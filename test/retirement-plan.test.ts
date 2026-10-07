import { describe, expect, it } from "vitest";
import { audit, planRetirement, ValidationError, type Action } from "../src/audit.js";
import { formatIp, parseCidr, parseIp, type Cidr } from "../src/ip.js";
import { runAudit } from "../src/runtime.js";

const rule = (id: string, action: Action, cidr: string) => ({ id, action, cidr });
const BASE = parseIp("10.13.0.0");
const PREFIX = 24;
const SIZE = 2 ** (32 - PREFIX);

interface GenRule {
  id: string;
  action: Action;
  cidr: Cidr;
}

function mulberry32(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function randomCidr(rand: () => number, prefix: number = PREFIX): Cidr {
  const hostBits = Math.floor(rand() * (32 - prefix + 1));
  const block = 2 ** hostBits;
  const offset = Math.floor(rand() * (SIZE / block)) * block;
  const lo = BASE + offset;
  return { base: lo, prefix: 32 - hostBits, lo, hi: lo + block - 1 };
}

function randomRules(rand: () => number): GenRule[] {
  const count = 1 + Math.floor(rand() * 8);
  return Array.from({ length: count }, (_, i) => ({
    id: `r${i}`,
    action: rand() < 0.5 ? "allow" : "deny",
    cidr: randomCidr(rand),
  }));
}

const ruleInput = (r: GenRule) => ({
  id: r.id,
  action: r.action,
  cidr: `${formatIp(r.cidr.base)}/${r.cidr.prefix}`,
});

function firstMatch(rules: GenRule[], ip: number): { rule: GenRule; index: number } | null {
  for (let i = 0; i < rules.length; i++) {
    const r = rules[i]!;
    if (ip >= r.cidr.lo && ip <= r.cidr.hi) return { rule: r, index: i };
  }
  return null;
}

function decision(rules: GenRule[], ip: number): Action {
  return firstMatch(rules, ip)?.rule.action ?? "deny";
}

/**
 * Independent minimum-CIDR partition oracle over the 256-address domain:
 * recursively split on dyadic boundaries and keep every fully-covered
 * aligned block. Canonical CIDR partitions of a set are unique, so the
 * production output must equal this exactly.
 */
function dyadicPack(mask: bigint, loOff: number, hostBits: number): string[] {
  const width = 1 << hostBits;
  const block = ((1n << BigInt(width)) - 1n) << BigInt(loOff);
  const covered = mask & block;
  if (covered === 0n) return [];
  if (covered === block) {
    return [`${formatIp(BASE + loOff)}/${32 - hostBits}`];
  }
  if (hostBits === 0) return [`${formatIp(BASE + loOff)}/32`];
  const half = width >> 1;
  return [
    ...dyadicPack(mask, loOff, hostBits - 1),
    ...dyadicPack(mask, loOff + half, hostBits - 1),
  ];
}

/** Full IPv4-space equivalence check using maximal constant runs. */
function expectDecisionsEqualEverywhere(
  oldRules: { id: string; action: Action; cidr: Cidr }[],
  newRules: { id: string; action: Action; cidr: Cidr }[],
): void {
  const boundaries = new Set<number>([0, 0xffffffff + 1]);
  for (const rs of [oldRules, newRules]) {
    for (const r of rs) {
      boundaries.add(r.cidr.lo);
      boundaries.add(r.cidr.hi + 1); // 2^32 for the universe end, no wrap
    }
  }
  const points = [...boundaries].sort((a, b) => a - b);
  const decide = (
    rs: { id: string; action: Action; cidr: Cidr }[],
    ip: number,
  ): Action => {
    for (const r of rs) {
      if (ip >= r.cidr.lo && ip <= r.cidr.hi) return r.action;
    }
    return "deny";
  };
  for (let i = 0; i + 1 < points.length; i++) {
    const ip = points[i]!;
    expect(decide(newRules, ip), `run at ${formatIp(ip)}`).toBe(decide(oldRules, ip));
  }
}

describe("read-only retirement rehearsal — hand-checked semantics", () => {
  it("replaces a sole rule with one same-action CIDR at its slot", () => {
    const plan = planRetirement({
      rules: [rule("only", "allow", "10.13.0.0/24")],
      retireRuleId: "only",
    });
    expect(plan).toMatchObject({
      retiredRuleId: "only",
      position: 0,
      decidedAddresses: 256,
      affectedAddresses: 256,
      replacementCount: 1,
      resultingRuleCount: 1,
      feasible: true,
      reason: null,
    });
    expect(plan.affectedIntervals).toEqual([
      { startAddress: "10.13.0.0", endAddress: "10.13.0.255" },
    ]);
    expect(plan.replacements).toEqual([
      {
        id: "only--replacement-1",
        action: "allow",
        cidr: "10.13.0.0/24",
        index: 0,
      },
    ]);
  });

  it("emits an empty replacement list for a fully shadowed rule", () => {
    const plan = planRetirement({
      rules: [
        rule("cover", "allow", "10.13.0.0/24"),
        rule("dead", "deny", "10.13.0.0/25"),
      ],
      retireRuleId: "dead",
    });
    expect(plan.decidedAddresses).toBe(0);
    expect(plan.affectedAddresses).toBe(0);
    expect(plan.replacements).toEqual([]);
    expect(plan.replacementCount).toBe(0);
    expect(plan.resultingRuleCount).toBe(1);
    expect(plan.feasible).toBe(true);
  });

  it("excludes addresses whose first match changes but the action stays equal", () => {
    // allow /24 retired; the lower half is re-allowed by a later rule and
    // must NOT be replaced; the upper half flips to default deny.
    const plan = planRetirement({
      rules: [
        rule("wide", "allow", "10.13.0.0/24"),
        rule("keep", "allow", "10.13.0.0/25"),
      ],
      retireRuleId: "wide",
    });
    expect(plan.decidedAddresses).toBe(256);
    expect(plan.affectedAddresses).toBe(128);
    expect(plan.affectedIntervals).toEqual([
      { startAddress: "10.13.0.128", endAddress: "10.13.0.255" },
    ]);
    expect(plan.replacements).toEqual([
      {
        id: "wide--replacement-1",
        action: "allow",
        cidr: "10.13.0.128/25",
        index: 0,
      },
    ]);
  });

  it("excludes addresses a later same-action rule keeps (even interleaved with denies)", () => {
    // wide allow /24; mid deny .64/26; tail allow .128/25.
    // After deleting wide: .0..63 -> default deny: FLIP
    //   .64..127 -> mid deny: FLIP as well (wide allowed there)
    //   .128..255 -> tail allow: first match changes but the action stays
    //   allow, so exactly that half is excluded from the replacement.
    const plan = planRetirement({
      rules: [
        rule("wide", "allow", "10.13.0.0/24"),
        rule("mid", "deny", "10.13.0.64/26"),
        rule("tail", "allow", "10.13.0.128/25"),
      ],
      retireRuleId: "wide",
    });
    expect(plan.affectedAddresses).toBe(128);
    expect(plan.affectedIntervals).toEqual([
      { startAddress: "10.13.0.0", endAddress: "10.13.0.127" },
    ]);
    expect(plan.replacements).toEqual([
      {
        id: "wide--replacement-1",
        action: "allow",
        cidr: "10.13.0.0/25",
        index: 0,
      },
    ]);
  });

  it("for a deny rule, replaces only addresses a later rule now allows", () => {
    // early allow .0/26; d deny /24; late allow .128/25.
    // d genuinely decides .64..255 (earlier took .0..63). After deleting d:
    // .64..127 -> default deny (unchanged); .128..255 -> late allow (flip).
    const plan = planRetirement({
      rules: [
        rule("early", "allow", "10.13.0.0/26"),
        rule("d", "deny", "10.13.0.0/24"),
        rule("late", "allow", "10.13.0.128/25"),
      ],
      retireRuleId: "d",
    });
    expect(plan.position).toBe(1);
    expect(plan.decidedAddresses).toBe(192);
    expect(plan.affectedAddresses).toBe(128);
    expect(plan.replacements).toEqual([
      {
        id: "d--replacement-1",
        action: "deny",
        cidr: "10.13.0.128/25",
        index: 1,
      },
    ]);
  });

  it("retiring an explicit default-deny with no later allow leaves an empty list", () => {
    // deny /0 plus an overlapping later deny /24: every address stays denied
    // after removal (later rule or default deny) -> no replacement.
    const plan = planRetirement({
      rules: [
        rule("block-all", "deny", "0.0.0.0/0"),
        rule("block-subnet", "deny", "10.13.0.0/24"),
      ],
      retireRuleId: "block-all",
    });
    expect(plan.affectedAddresses).toBe(0);
    expect(plan.replacements).toEqual([]);
    expect(plan.resultingRuleCount).toBe(1);
  });

  it("retiring an allow /0 keeps later allow holes and partitions the rest minimally", () => {
    const plan = planRetirement({
      rules: [
        rule("any", "allow", "0.0.0.0/0"),
        rule("dns", "allow", "8.8.8.8/32"),
      ],
      retireRuleId: "any",
    });
    expect(plan.decidedAddresses).toBe(2 ** 32);
    expect(plan.affectedAddresses).toBe(2 ** 32 - 1);
    expect(plan.replacementCount).toBe(32);
    expect(plan.replacements[0]).toMatchObject({ cidr: "0.0.0.0/5" });
    expect(plan.replacements.at(-1)).toMatchObject({ cidr: "128.0.0.0/1" });
    // The single excluded address is exactly the later allow hole.
    for (const repl of plan.replacements) {
      const c = parseCidr(repl.cidr);
      expect(parseIp("8.8.8.8") < c.lo || parseIp("8.8.8.8") > c.hi).toBe(true);
    }
  });

  it("splits a non-aligned affected fragment into the minimum canonical CIDRs", () => {
    // Only .4..255 was decided by the retired allow; .0..3 decided earlier.
    // Deleting it flips .4..255 to default deny; .4/30 packs into two blocks.
    const plan = planRetirement({
      rules: [
        rule("early", "allow", "10.13.0.0/30"),
        rule("target", "allow", "10.13.0.0/24"),
      ],
      retireRuleId: "target",
    });
    expect(plan.decidedAddresses).toBe(252);
    expect(plan.affectedAddresses).toBe(252);
    expect(plan.replacements.map((r) => r.cidr)).toEqual([
      "10.13.0.4/30",
      "10.13.0.8/29",
      "10.13.0.16/28",
      "10.13.0.32/27",
      "10.13.0.64/26",
      "10.13.0.128/25",
    ]);
  });

  it("produces multiple replacements across separated fragments with overlapping rules", () => {
    // mid deny .64/26 (index 0); target allow /24 (index 1).
    // target decides .0..63 and .128..255; on deletion both flip to default
    // deny (mid keeps .64..127 denied). Two clean CIDRs.
    const plan = planRetirement({
      rules: [
        rule("mid", "deny", "10.13.0.64/26"),
        rule("target", "allow", "10.13.0.0/24"),
      ],
      retireRuleId: "target",
    });
    expect(plan.replacements.map((r) => r.cidr)).toEqual([
      "10.13.0.0/26",
      "10.13.0.128/25",
    ]);
    expect(plan.replacements.every((r) => r.action === "allow")).toBe(true);
    expect(plan.replacements.every((r) => r.index === 1)).toBe(true);
  });

  it("never lets replacements touch addresses earlier rules already decided", () => {
    // early allow .0/25 stays the first match after replacements are put in
    // the retired slot (index 1), behind it.
    const plan = planRetirement({
      rules: [
        rule("early", "allow", "10.13.0.0/25"),
        rule("target", "allow", "10.13.0.0/24"),
      ],
      retireRuleId: "target",
    });
    expect(plan.decidedAddresses).toBe(128);
    for (const repl of plan.replacements) {
      const c = parseCidr(repl.cidr);
      expect(c.lo).toBeGreaterThanOrEqual(BASE + 128);
      expect(repl.index).toBe(1);
    }
  });

  it("uses deterministic, collision-free replacement ids", () => {
    const plan = planRetirement({
      rules: [
        rule("v", "allow", "10.13.0.0/30"),
        // Existing ids deliberately collide with the generated suffix.
        rule("v--replacement-1", "allow", "10.13.0.4/30"),
        rule("v--replacement-1-d1", "allow", "10.13.0.8/29"),
      ],
      retireRuleId: "v",
    });
    expect(plan.replacements[0]!.id).toBe("v--replacement-1-d2");
    expect(new Set(plan.replacements.map((r) => r.id)).size).toBe(
      plan.replacements.length,
    );
    // Re-running gives the identical plan.
    const again = planRetirement({
      rules: [
        rule("v", "allow", "10.13.0.0/30"),
        rule("v--replacement-1", "allow", "10.13.0.4/30"),
        rule("v--replacement-1-d1", "allow", "10.13.0.8/29"),
      ],
      retireRuleId: "v",
    });
    expect(again).toEqual(plan);
  });

  it("reports infeasible without truncating when replacements exceed the cap", () => {
    // allow /0 with 12 widely-spaced later allow /32 holes: the affected set
    // (whole space minus 12 addresses) packs into 315 canonical CIDRs, so the
    // post-application policy would hold 327 > 300 rules.
    const rules = [rule("any", "allow", "0.0.0.0/0")];
    for (let i = 0; i < 12; i++) {
      const ip = (i * 0x04000000 + 0x01020304) >>> 0;
      rules.push(rule(`h${i}`, "allow", `${formatIp(ip)}/32`));
    }
    const plan = planRetirement({ rules, retireRuleId: "any" });
    expect(plan.replacementCount).toBe(315);
    expect(plan.replacements).toHaveLength(315); // untruncated
    expect(plan.resultingRuleCount).toBe(327);
    expect(plan.feasible).toBe(false);
    expect(plan.reason).toMatch(/300 rule limit/);
    expect(plan.affectedAddresses).toBe(2 ** 32 - 12);

    // The full, untruncated list still preserves every decision when applied.
    const applied = [
      ...plan.replacements.map((repl) => ({
        id: repl.id,
        action: repl.action as Action,
        cidr: parseCidr(repl.cidr),
      })),
      ...rules.slice(1).map((rr) => ({ id: rr.id, action: rr.action, cidr: parseCidr(rr.cidr) })),
    ];
    const oldParsed = rules.map((rr) => ({
      id: rr.id,
      action: rr.action,
      cidr: parseCidr(rr.cidr),
    }));
    expectDecisionsEqualEverywhere(oldParsed, applied);
  });
});

describe("retirement rehearsal — address-by-address differential tests in 10.13.0.0/24", () => {
  for (let seed = 1; seed <= 300; seed++) {
    it(`random policy ${seed}: exact affected set, minimum packing, identical new decisions`, () => {
      const rand = mulberry32(seed * 104729 + 17);
      const oldRules = randomRules(rand);
      const retireIndex = Math.floor(rand() * oldRules.length);
      const retireId = oldRules[retireIndex]!.id;

      const input = {
        rules: oldRules.map(ruleInput),
        retireRuleId: retireId,
      };
      const plan = audit(input).retirementPlan!;

      // Oracle: walk every address.
      const affectedMask: boolean[] = new Array(SIZE).fill(false);
      let decidedCount = 0;
      let affectedCount = 0;
      for (let off = 0; off < SIZE; off++) {
        const ip = BASE + off;
        const before = firstMatch(oldRules, ip);
        if (before?.index !== retireIndex) continue;
        decidedCount++;
        const afterRules = [
          ...oldRules.slice(0, retireIndex),
          ...oldRules.slice(retireIndex + 1),
        ];
        if (decision(afterRules, ip) !== oldRules[retireIndex]!.action) {
          affectedMask[off] = true;
          affectedCount++;
        }
      }

      expect(plan.position).toBe(retireIndex);
      expect(plan.decidedAddresses).toBe(decidedCount);
      expect(plan.affectedAddresses).toBe(affectedCount);

      // Expected intervals from the oracle booleans.
      const expectedIntervals: Array<{ startAddress: string; endAddress: string }> = [];
      for (let off = 0; off < SIZE; off++) {
        if (!affectedMask[off]) continue;
        const last = expectedIntervals.at(-1);
        if (last && parseIp(last.endAddress) === BASE + off - 1) {
          last.endAddress = formatIp(BASE + off);
        } else {
          expectedIntervals.push({
            startAddress: formatIp(BASE + off),
            endAddress: formatIp(BASE + off),
          });
        }
      }
      expect(plan.affectedIntervals).toEqual(expectedIntervals);

      // Minimum, canonical CIDR partition per the independent dyadic oracle.
      let mask = 0n;
      for (let off = 0; off < SIZE; off++) {
        if (affectedMask[off]) mask |= 1n << BigInt(off);
      }
      const expectedCidrs =
        affectedCount === 0 ? [] : dyadicPack(mask, 0, 32 - PREFIX);
      const gotCidrs = plan.replacements.map((repl) => repl.cidr);
      expect(gotCidrs).toEqual(expectedCidrs);

      // Every replacement is canonical and parses back to its text.
      for (const repl of plan.replacements) {
        const c = parseCidr(repl.cidr);
        expect(repl.action).toBe(oldRules[retireIndex]!.action);
        expect(repl.index).toBe(retireIndex);
        expect(`${formatIp(c.base)}/${c.prefix}`).toBe(repl.cidr);
      }
      // Ids are unique against each other.
      expect(new Set(plan.replacements.map((r) => r.id)).size).toBe(
        plan.replacements.length,
      );

      // Apply the plan: delete the rule, insert replacements at its slot.
      const replacementsParsed = plan.replacements.map((repl) => ({
        id: repl.id,
        action: repl.action,
        cidr: parseCidr(repl.cidr),
      }));
      const applied = [
        ...oldRules.slice(0, retireIndex).map((g) => ({
          id: g.id,
          action: g.action,
          cidr: g.cidr,
        })),
        ...replacementsParsed.map((g) => ({
          id: g.id,
          action: g.action,
          cidr: g.cidr,
        })),
        ...oldRules.slice(retireIndex + 1).map((g) => ({
          id: g.id,
          action: g.action,
          cidr: g.cidr,
        })),
      ];

      // Every one of the 256 domain addresses keeps its exact conclusion.
      for (let off = 0; off < SIZE; off++) {
        const ip = BASE + off;
        expect(decision(applied, ip)).toBe(decision(oldRules, ip));
      }

      // Earlier rules still win every address they used to (their first-match
      // index is unchanged by construction).
      for (let off = 0; off < SIZE; off++) {
        const ip = BASE + off;
        const oldMatch = firstMatch(oldRules, ip);
        if (oldMatch && oldMatch.index < retireIndex) {
          expect(firstMatch(applied, ip)?.index).toBe(oldMatch.index);
        }
      }

      // Replacement CIDRs union exactly to the affected set.
      const coveredByReplacements = new Set<number>();
      for (const repl of replacementsParsed) {
        for (let ip = repl.cidr.lo; ip <= repl.cidr.hi; ip++) {
          coveredByReplacements.add(ip);
        }
      }
      for (let off = 0; off < SIZE; off++) {
        expect(coveredByReplacements.has(BASE + off)).toBe(affectedMask[off]!);
      }

      // Empty replacement cases: shadowed target or decision-preserving delete.
      if (affectedCount === 0) {
        expect(plan.replacements).toEqual([]);
        expect(plan.resultingRuleCount).toBe(oldRules.length - 1);
        expect(plan.feasible).toBe(true);
      }

      // Generated policies inside the tiny domain never exceed 300 rules.
      expect(plan.resultingRuleCount).toBe(
        oldRules.length - 1 + plan.replacements.length,
      );
      expect(plan.feasible).toBe(true);
    });
  }
});

describe("retirement rehearsal — full IPv4 space via maximal constant runs", () => {
  const cases: Array<{
    name: string;
    rules: { id: string; action: Action; cidr: string }[];
    retire: string;
  }> = [
    {
      name: "allow /0 over default deny",
      rules: [{ id: "any", action: "allow", cidr: "0.0.0.0/0" }],
      retire: "any",
    },
    {
      name: "deny /0 is a no-op replacement",
      rules: [{ id: "d", action: "deny", cidr: "0.0.0.0/0" }],
      retire: "d",
    },
    {
      name: "mixed /1 boundaries with /0",
      rules: [
        { id: "h1", action: "allow", cidr: "0.0.0.0/1" },
        { id: "rest", action: "deny", cidr: "0.0.0.0/0" },
        { id: "host", action: "allow", cidr: "8.8.8.8/32" },
        { id: "tail", action: "allow", cidr: "200.0.0.0/8" },
      ],
      retire: "rest",
    },
    {
      name: "allow /0 with scattered later allow holes (infeasible packing)",
      rules: [
        { id: "any", action: "allow", cidr: "0.0.0.0/0" },
        ...Array.from({ length: 12 }, (_, i) => ({
          id: `h${i}`,
          action: "allow" as Action,
          cidr: `${formatIp((i * 0x04000000 + 0x01020304) >>> 0)}/32`,
        })),
      ],
      retire: "any",
    },
  ];

  for (const c of cases) {
    it(`preserves every IPv4 decision: ${c.name}`, () => {
      const plan = planRetirement({ rules: c.rules, retireRuleId: c.retire });
      const k = c.rules.findIndex((r) => r.id === c.retire);
      const oldParsed = c.rules.map((rr) => ({
        id: rr.id,
        action: rr.action,
        cidr: parseCidr(rr.cidr),
      }));
      const applied = [
        ...oldParsed.slice(0, k),
        ...plan.replacements.map((repl) => ({
          id: repl.id,
          action: repl.action,
          cidr: parseCidr(repl.cidr),
        })),
        ...oldParsed.slice(k + 1),
      ];
      expectDecisionsEqualEverywhere(oldParsed, applied);
    });
  }
});

describe("retirement rehearsal — validation and shared runtime", () => {
  it("rejects missing, empty, non-string or unknown retireRuleId", () => {
    expect(() =>
      planRetirement({ rules: [rule("a", "allow", "10.13.0.0/24")] }),
    ).toThrow(/missing required field retireRuleId/);
    expect(() =>
      audit({ rules: [rule("a", "allow", "10.13.0.0/24")], retireRuleId: "" }),
    ).toThrow(/retireRuleId must be a non-empty string/);
    expect(() =>
      audit({ rules: [rule("a", "allow", "10.13.0.0/24")], retireRuleId: 7 }),
    ).toThrow(ValidationError);
    expect(() =>
      audit({
        rules: [rule("a", "allow", "10.13.0.0/24")],
        retireRuleId: "ghost",
      }),
    ).toThrow(/unknown rule id "ghost"/);
    expect(() =>
      audit({
        rules: [rule("a", "allow", "10.13.0.0/24")],
        retireRuleId: "a",
        bogus: 1,
      }),
    ).toThrow(/unknown field "bogus"/);
  });

  it("leaves the original rules, swaps, queries and insertion planning untouched", () => {
    const input = {
      rules: [
        rule("a", "deny", "10.13.0.0/25"),
        rule("b", "allow", "10.13.0.0/24"),
      ],
      queries: ["10.13.0.1", "10.13.0.200"],
      newRule: rule("c", "allow", "10.13.0.64/26"),
      probes: [{ address: "10.13.0.65", action: "allow" as const }],
      protectedAddresses: ["10.13.0.1"],
      retireRuleId: "b",
    };
    const withoutRetirement = audit({ ...input, retireRuleId: undefined });
    const withRetirement = audit(input);
    expect(withRetirement.rules).toEqual(withoutRetirement.rules);
    expect(withRetirement.swaps).toEqual(withoutRetirement.swaps);
    expect(withRetirement.queries).toEqual(withoutRetirement.queries);
    expect(withRetirement.insertionPlan).toEqual(withoutRetirement.insertionPlan);
    expect(withRetirement.retirementPlan).toBeDefined();

    // Input arrays are not mutated.
    const snapshot = JSON.parse(JSON.stringify(input));
    audit(input);
    expect(input).toEqual(snapshot);
  });

  it("omits the retirement plan when retireRuleId is absent", () => {
    const report = audit({ rules: [rule("a", "allow", "10.13.0.0/24")] });
    expect(report.retirementPlan).toBeUndefined();
  });

  it("keeps CLI and HTTP on the same JSON runtime result", () => {
    const input = {
      rules: [
        rule("early", "allow", "10.13.0.0/26"),
        rule("d", "deny", "10.13.0.0/24"),
        rule("late", "allow", "10.13.0.128/25"),
      ],
      retireRuleId: "d",
      queries: ["10.13.0.100", "10.13.0.200"],
    };
    const text = JSON.stringify(input);
    expect(runAudit(text)).toEqual(audit(input));
  });
});
