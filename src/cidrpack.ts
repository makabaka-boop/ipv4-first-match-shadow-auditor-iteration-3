/**
 * Exact decomposition of an IPv4 address set (sorted disjoint closed
 * intervals) into the minimum number of canonical CIDR blocks.
 *
 * The blocks covering any single address form a chain from /32 up to /0,
 * so taking the largest aligned block at the smallest uncovered address is
 * a matroid-style greedy choice: it never costs more than splitting that
 * address off, hence the block count is minimum. Repeated greedily also
 * makes the partition unique (any minimum canonical partition is unique).
 */

import type { IP } from "./ip.js";
import type { IntervalSet } from "./intervals.js";

export interface PackedCidr {
  base: IP; // canonical network address
  prefix: number; // 0..32
  lo: IP; // inclusive
  hi: IP; // inclusive
}

/** Largest aligned CIDR block starting at `lo` that does not pass `hi`. */
function largestBlock(lo: IP, hi: IP): PackedCidr {
  // Number of trailing zero bits of lo, capped at 32 for lo === 0.
  let alignment = 0;
  if (lo === 0) {
    alignment = 32;
  } else {
    let v = lo >>> 0;
    while ((v & 1) === 0) {
      alignment++;
      v >>>= 1;
    }
  }

  let hostBits = 0;
  while (hostBits < alignment) {
    const size = 2 ** (hostBits + 1);
    // Plain arithmetic: hi can be 2^32-1, so hi + 1 reaches 2^32 and the
    // comparison simply stays false without unsigned wrap.
    if (lo + size - 1 > hi) break;
    hostBits++;
  }

  const size = 2 ** hostBits;
  const hiAddr = lo + size - 1;
  return { base: lo, prefix: 32 - hostBits, lo, hi: hiAddr };
}

/** Split an interval set into the fewest canonical, disjoint CIDR blocks. */
export function minimumCidrs(set: IntervalSet): PackedCidr[] {
  const blocks: PackedCidr[] = [];
  for (const interval of set) {
    let cursor = interval.lo;
    while (cursor <= interval.hi) {
      const block = largestBlock(cursor, interval.hi);
      blocks.push(block);
      cursor = block.hi + 1; // exits at 2^32 after 255.255.255.255, no wrap
    }
  }
  return blocks;
}
