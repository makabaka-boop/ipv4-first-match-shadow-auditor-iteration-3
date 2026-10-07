import { describe, expect, it } from "vitest";
import {
  audit,
  planRetirement,
  ValidationError,
  type Action,
} from "../src/audit.js";
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

// Deterministic PRNG so the suite is reproducible.
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

function randomCidr(rand: () => number): Cidr {
  const hostBits = Math.floor(rand() * (32 - PREFIX + 1));
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

/** Merge a sorted address list into closed-interval runs. */
function runsOf(ips: number[]): Array<{ startAddress: string; endAddress: string }> {
  const out: Array<{ startAddress: string; endAddress: string }> = [];
  for (const ip of ips) {
    const last = out.at(-1);
    if (last && parseIp(last.endAddress) === ip - 1) {
      last.endAddress = formatIp(ip);
    } else {
      out.push({ startAddress: formatIp(ip), endAddress: formatIp(ip) });
    }
  }
  return out;
}

/**
 * Independent minimal-CIDR oracle: grow the block at each cursor by doubling
 * while alignment and fit allow (a different code shape from src/ip.ts; the
 * minimal decomposition of an interval is unique, so the two must agree).
 */
function oracleCidrs(lo: number, hi: number): Array<{ base: number; prefix: number }> {
  const out: Array<{ base: number; prefix: number }> = [];
  let cursor = lo;
  while (cursor <= hi) {
    let size = 1;
    while (cursor % (size * 2) === 0 && cursor + size * 2 - 1 <= hi) size *= 2;
    out.push({ base: cursor, prefix: 32 - Math.log2(size) });
    cursor += size;
  }
  return out;
}

/**
 * Maximal constant runs over the full 32-bit space: rule membership flips
 * only at CIDR edges, so sampling one address per run is equivalent to
 * walking all 2^32 addresses.
 */
function fullSpaceRuns(cidrs: Cidr[]): Array<[number, number]> {
  const boundaries = new Set<number>([0, 0xffffffff]);
  for (const c of cidrs) {
    boundaries.add(c.lo);
    boundaries.add(c.hi < 0xffffffff ? c.hi + 1 : c.hi);
  }
  const points = [...boundaries].sort((a, b) => a - b);
  const runs: Array<[number, number]> = [];
  for (let p = 0; p < points.length; p++) {
    const lo = points[p]!;
    const hi = p + 1 < points.length ? points[p + 1]! - 1 : 0xffffffff;
    runs.push([lo, Math.max(lo, hi)]);
  }
  return runs;
}

const planOf = (input: unknown) => audit(input).retirementPlan!;

describe("read-only retirement replacement rehearsal", () => {
  it("returns an empty replacement list for a fully shadowed rule", () => {
    const plan = planOf({
      rules: [rule("cover", "deny", "10.13.0.0/24"), rule("shadowed", "allow", "10.13.0.0/25")],
      retireRuleId: "shadowed",
    });

    expect(plan).toMatchObject({
      retireRuleId: "shadowed",
      retireIndex: 1,
      action: "allow",
      applicable: true,
      position: 1,
      changedAddresses: 0,
      changedIntervals: [],
      replacementRules: [],
      resultingRuleCount: 1,
      maxRuleCount: 300,
      reason: null,
    });
  });

  it("returns an empty replacement list when deletion falls through to the same default deny", () => {
    const plan = planOf({
      rules: [rule("d", "deny", "10.13.0.0/24")],
      retireRuleId: "d",
    });

    expect(plan.applicable).toBe(true);
    expect(plan.changedAddresses).toBe(0);
    expect(plan.changedIntervals).toEqual([]);
    expect(plan.replacementRules).toEqual([]);
    expect(plan.resultingRuleCount).toBe(0);
  });

  it("excludes addresses whose first match changes but whose action does not", () => {
    // Every address of "a" stays allowed via the allow /0 behind it.
    const empty = planOf({
      rules: [rule("a", "allow", "10.13.0.0/24"), rule("all", "allow", "0.0.0.0/0")],
      retireRuleId: "a",
    });
    expect(empty.changedAddresses).toBe(0);
    expect(empty.replacementRules).toEqual([]);

    // Only the lower half flips; .128..255 keeps allow via "b".
    const plan = planOf({
      rules: [rule("a", "allow", "10.13.0.0/24"), rule("b", "allow", "10.13.0.128/25")],
      retireRuleId: "a",
    });
    expect(plan.changedIntervals).toEqual([
      { startAddress: "10.13.0.0", endAddress: "10.13.0.127" },
    ]);
    expect(plan.replacementRules).toEqual([
      { id: "a-retire-0", action: "allow", cidr: "10.13.0.0/25" },
    ]);
    expect(plan.position).toBe(0);
  });

  it("replaces only the truly decided fragment among overlapping rules", () => {
    const plan = planOf({
      rules: [
        rule("early", "allow", "10.13.0.0/25"),
        rule("mid", "deny", "10.13.0.0/24"),
        rule("late", "allow", "10.13.0.192/26"),
      ],
      retireRuleId: "mid",
    });

    // "mid" truly decides .128..255; deleting it lets .192..255 fall to the
    // allow behind it (a real flip, deny -> allow), while .128..191 would
    // hit default deny — the same action as before, so no replacement there.
    expect(plan.changedIntervals).toEqual([
      { startAddress: "10.13.0.192", endAddress: "10.13.0.255" },
    ]);
    expect(plan.replacementRules).toEqual([
      { id: "mid-retire-0", action: "deny", cidr: "10.13.0.192/26" },
    ]);
    expect(plan.position).toBe(1);
    // The replacement must not touch addresses "early" already decides.
    expect(parseCidr(plan.replacementRules[0]!.cidr).lo).toBeGreaterThan(
      parseIp("10.13.0.127"),
    );
  });

  it("replaces a retired only-rule with an equivalent deterministic rule", () => {
    const plan = planOf({
      rules: [rule("solo", "allow", "10.13.0.0/24")],
      retireRuleId: "solo",
    });

    expect(plan.replacementRules).toEqual([
      { id: "solo-retire-0", action: "allow", cidr: "10.13.0.0/24" },
    ]);
    expect(plan.resultingRuleCount).toBe(1);
    expect(plan.applicable).toBe(true);
  });

  it("splits the changed set into the minimum number of canonical CIDRs", () => {
    const plan = planOf({
      rules: [
        rule("edge", "allow", "10.13.0.0/24"),
        rule("lo", "allow", "10.13.0.0/32"),
        rule("hi", "allow", "10.13.0.255/32"),
      ],
      retireRuleId: "edge",
    });

    expect(plan.changedIntervals).toEqual([
      { startAddress: "10.13.0.1", endAddress: "10.13.0.254" },
    ]);
    expect(plan.replacementRules).toEqual(
      [
        "10.13.0.1/32", "10.13.0.2/31", "10.13.0.4/30", "10.13.0.8/29",
        "10.13.0.16/28", "10.13.0.32/27", "10.13.0.64/26", "10.13.0.128/26",
        "10.13.0.192/27", "10.13.0.224/28", "10.13.0.240/29", "10.13.0.248/30",
        "10.13.0.252/31", "10.13.0.254/32",
      ].map((cidr, i) => ({ id: `edge-retire-${i}`, action: "allow", cidr })),
    );
    expect(plan.changedAddresses).toBe(254);
  });

  it("covers a whole /0 changed set with a single replacement CIDR", () => {
    const plan = planOf({
      rules: [rule("any", "allow", "0.0.0.0/0")],
      retireRuleId: "any",
    });

    expect(plan.changedAddresses).toBe(2 ** 32);
    expect(plan.changedIntervals).toEqual([
      { startAddress: "0.0.0.0", endAddress: "255.255.255.255" },
    ]);
    expect(plan.replacementRules).toEqual([
      { id: "any-retire-0", action: "allow", cidr: "0.0.0.0/0" },
    ]);
  });

  it("handles a /0 rule with a fragmented changed set over the full IPv4 space", () => {
    const genRules: GenRule[] = [
      { id: "local", action: "deny", cidr: parseCidr("10.13.0.0/24") },
      { id: "any", action: "allow", cidr: parseCidr("0.0.0.0/0") },
    ];
    const plan = planOf({ rules: genRules.map(ruleInput), retireRuleId: "any" });

    expect(plan.changedAddresses).toBe(2 ** 32 - 256);
    expect(plan.changedIntervals).toEqual([
      { startAddress: "0.0.0.0", endAddress: "10.12.255.255" },
      { startAddress: "10.13.1.0", endAddress: "255.255.255.255" },
    ]);

    // The replacement list is exactly the unique minimal CIDR decomposition.
    const expectedCidrs = plan.changedIntervals.flatMap((iv) =>
      oracleCidrs(parseIp(iv.startAddress), parseIp(iv.endAddress)),
    );
    expect(plan.replacementRules.map((r) => r.cidr)).toEqual(
      expectedCidrs.map((c) => `${formatIp(c.base)}/${c.prefix}`),
    );
    expect(plan.replacementRules.every((r) => r.action === "allow")).toBe(true);

    // Full-space equivalence: sample one address per maximal constant run.
    const replacements: GenRule[] = plan.replacementRules.map((r) => ({
      id: r.id,
      action: r.action,
      cidr: parseCidr(r.cidr),
    }));
    const applied: GenRule[] = [genRules[0]!, ...replacements];
    const without: GenRule[] = [genRules[0]!];
    const runs = fullSpaceRuns([...genRules, ...replacements].map((r) => r.cidr));
    for (const [lo] of runs) {
      expect(decision(applied, lo)).toBe(decision(genRules, lo));
      // Replacement coverage is exactly the set of addresses that would flip.
      const covered = firstMatch(replacements, lo) !== null;
      expect(covered).toBe(decision(genRules, lo) !== decision(without, lo));
    }
  });

  it("reports not applicable beyond the rule limit without truncating the list", () => {
    const dummyCidrs = [
      ...Array.from({ length: 256 }, (_, i) => `198.51.100.${i}/32`),
      ...Array.from({ length: 42 }, (_, i) => `203.0.113.${i}/32`),
    ];
    const rules = [
      rule("wide", "allow", "10.13.0.0/24"),
      rule("pin", "allow", "10.13.0.1/32"),
      ...dummyCidrs.map((cidr, i) => rule(`dummy-${i}`, "deny" as const, cidr)),
    ];
    expect(rules).toHaveLength(300);

    const plan = planOf({ rules, retireRuleId: "wide" });

    // changed = /24 minus 10.13.0.1 -> 8 minimal CIDRs -> 300 - 1 + 8 = 307.
    expect(plan.replacementRules.map((r) => r.cidr)).toEqual([
      "10.13.0.0/32", "10.13.0.2/31", "10.13.0.4/30", "10.13.0.8/29",
      "10.13.0.16/28", "10.13.0.32/27", "10.13.0.64/26", "10.13.0.128/25",
    ]);
    expect(plan.resultingRuleCount).toBe(307);
    expect(plan.applicable).toBe(false);
    expect(plan.reason).toMatch(/307 rules, exceeding the 300-rule limit/);
    // Untruncated: the full changed set and replacement list are reported.
    expect(plan.changedAddresses).toBe(255);
    expect(plan.changedIntervals).toEqual([
      { startAddress: "10.13.0.0", endAddress: "10.13.0.0" },
      { startAddress: "10.13.0.2", endAddress: "10.13.0.255" },
    ]);
  });

  it("accepts a plan landing exactly on the rule limit", () => {
    const dummyCidrs = [
      ...Array.from({ length: 256 }, (_, i) => `198.51.100.${i}/32`),
      ...Array.from({ length: 41 }, (_, i) => `203.0.113.${i}/32`),
    ];
    const rules = [
      rule("wide", "allow", "10.13.0.0/24"),
      rule("hole", "allow", "10.13.0.128/26"),
      ...dummyCidrs.map((cidr, i) => rule(`dummy-${i}`, "deny" as const, cidr)),
    ];
    expect(rules).toHaveLength(299);

    const plan = planOf({ rules, retireRuleId: "wide" });

    // changed = /24 minus .128/26 -> two CIDRs -> 299 - 1 + 2 = 300.
    expect(plan.replacementRules.map((r) => r.cidr)).toEqual([
      "10.13.0.0/25",
      "10.13.0.192/26",
    ]);
    expect(plan.resultingRuleCount).toBe(300);
    expect(plan.applicable).toBe(true);
    expect(plan.reason).toBeNull();
  });

  it("reports not applicable when a deterministic replacement id collides", () => {
    const plan = planOf({
      rules: [
        rule("a", "allow", "10.13.0.0/24"),
        rule("a-retire-0", "allow", "10.13.0.1/32"),
      ],
      retireRuleId: "a",
    });

    expect(plan.replacementRules).toHaveLength(8); // still untruncated
    expect(plan.applicable).toBe(false);
    expect(plan.reason).toMatch(/"a-retire-0" collides/);
  });

  it("validates retireRuleId and rejects the whole request on errors", () => {
    const rules = [rule("a", "allow", "10.13.0.0/24")];
    expect(() => audit({ rules, retireRuleId: "nope" })).toThrow(/unknown rule id "nope"/);
    expect(() => audit({ rules, retireRuleId: "" })).toThrow(/retireRuleId must be a non-empty string/);
    expect(() => audit({ rules, retireRuleId: 7 })).toThrow(ValidationError);
    expect(() => planRetirement({ rules })).toThrow(/missing required field retireRuleId/);
    expect(planRetirement({ rules, retireRuleId: "a" })).toEqual(
      audit({ rules, retireRuleId: "a" }).retirementPlan,
    );
  });

  it("leaves the base report and insertion planning untouched", () => {
    const base = {
      rules: [rule("a", "deny", "10.13.0.0/25"), rule("b", "allow", "10.13.0.0/24")],
      newRule: rule("c", "allow", "10.13.0.64/26"),
      probes: [{ address: "10.13.0.65", action: "allow" as const }],
      protectedAddresses: ["10.13.0.1"],
      queries: ["10.13.0.9"],
    };
    const without = audit(base);
    const withRetire = audit({ ...base, retireRuleId: "a" });

    expect(without.retirementPlan).toBeUndefined();
    expect(withRetire.retirementPlan).toBeDefined();
    expect(withRetire.rules).toEqual(without.rules);
    expect(withRetire.swaps).toEqual(without.swaps);
    expect(withRetire.queries).toEqual(without.queries);
    expect(withRetire.insertionPlan).toEqual(without.insertionPlan);
  });

  it("does not mutate the supplied policy input", () => {
    const input = {
      rules: [
        rule("a", "allow", "10.13.0.0/24"),
        rule("b", "deny", "10.13.0.128/25"),
      ],
      retireRuleId: "a",
    };
    const snapshot = JSON.parse(JSON.stringify(input));
    audit(input);
    expect(input).toEqual(snapshot);
  });

  it("keeps CLI and HTTP on the same JSON runtime result", () => {
    const input = {
      rules: [rule("a", "deny", "10.13.0.0/25"), rule("b", "allow", "10.13.0.0/24")],
      retireRuleId: "b",
    };
    expect(runAudit(JSON.stringify(input))).toEqual(audit(input));
  });

  for (let seed = 1; seed <= 300; seed++) {
    it(`preserves every per-address decision (random ${seed})`, () => {
      const rand = mulberry32(seed * 2246822519 + 3266489917);
      const rules = randomRules(rand);
      const retireIndex = Math.floor(rand() * rules.length);
      const retired = rules[retireIndex]!;
      const input = { rules: rules.map(ruleInput), retireRuleId: retired.id };
      const plan = audit(input).retirementPlan!;

      // Oracle: per-address changed set over the whole small domain.
      const without = rules.filter((_, i) => i !== retireIndex);
      const expectedChanged: number[] = [];
      for (let off = 0; off < SIZE; off++) {
        const ip = BASE + off;
        if (decision(rules, ip) !== decision(without, ip)) {
          // A flip is only possible where the retired rule truly decided.
          expect(firstMatch(rules, ip)?.index).toBe(retireIndex);
          expectedChanged.push(ip);
        }
      }
      const expectedIntervals = runsOf(expectedChanged);

      expect(plan.retireRuleId).toBe(retired.id);
      expect(plan.retireIndex).toBe(retireIndex);
      expect(plan.position).toBe(retireIndex);
      expect(plan.action).toBe(retired.action);
      expect(plan.changedAddresses).toBe(expectedChanged.length);
      expect(plan.changedIntervals).toEqual(expectedIntervals);

      // Replacements are the unique minimal CIDR decomposition of the
      // changed set, with deterministic ids and the original action.
      const expectedCidrs = expectedIntervals.flatMap((iv) =>
        oracleCidrs(parseIp(iv.startAddress), parseIp(iv.endAddress)),
      );
      expect(plan.replacementRules.map((r) => r.cidr)).toEqual(
        expectedCidrs.map((c) => `${formatIp(c.base)}/${c.prefix}`),
      );
      plan.replacementRules.forEach((r, i) => {
        expect(r.id).toBe(`${retired.id}-retire-${i}`);
        expect(r.action).toBe(retired.action);
        expect(() => parseCidr(r.cidr)).not.toThrow(); // canonical form
      });

      // Small policies never hit the rule limit or an id collision.
      expect(plan.resultingRuleCount).toBe(
        rules.length - 1 + plan.replacementRules.length,
      );
      expect(plan.applicable).toBe(true);
      expect(plan.reason).toBeNull();
      expect(plan.maxRuleCount).toBe(300);

      // Apply the plan: delete the rule, insert replacements at its slot.
      const replacements: GenRule[] = plan.replacementRules.map((r) => ({
        id: r.id,
        action: r.action,
        cidr: parseCidr(r.cidr),
      }));
      const applied: GenRule[] = [
        ...rules.slice(0, retireIndex),
        ...replacements,
        ...rules.slice(retireIndex + 1),
      ];

      for (let off = 0; off < SIZE; off++) {
        const ip = BASE + off;
        // New and old actions are exactly equal, address by address.
        expect(decision(applied, ip)).toBe(decision(rules, ip));

        // Replacement coverage is exactly the changed set — never addresses
        // whose first match moved without an action change.
        const covered = firstMatch(replacements, ip) !== null;
        expect(covered).toBe(decision(rules, ip) !== decision(without, ip));

        // Replacements never touch addresses earlier rules already decide.
        if (covered) {
          const match = firstMatch(rules, ip);
          expect(match === null || match.index >= retireIndex).toBe(true);
        }
      }

      // Addresses outside the generated domain keep the default deny.
      for (const ip of [parseIp("0.0.0.0"), parseIp("8.8.8.8"), parseIp("255.255.255.255")]) {
        expect(decision(applied, ip)).toBe(decision(rules, ip));
      }

      // Deterministic: re-running and the standalone entry point agree.
      expect(audit(input).retirementPlan).toEqual(plan);
      expect(planRetirement(input)).toEqual(plan);
    });
  }
});
