/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: JSP-proofs project.

JSP-000183 is the JSP mirror of Erdős Problem 193.
-/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/--!
# JSP-000183 — infinite small-step ℝ³-walk with no collinear triple

Problem (The Justin Sun Prize problem bank, JSP-000183):

> Must an infinite walk in three-dimensional space using a finite set
> of step vectors visit three collinear points?

This is the JSP mirror of Erdős Problem 193.  Gerver and Ramsey (1979)
conjectured the answer is "yes" (and proved it for ℝ²-walks).  Cambie and
Kalvianen (2026) gave a negative answer, constructing an explicit
infinite walk in ℝ³ whose steps come from a fixed menu of sixteen vectors
and no three vertices are collinear.

The full Lean 4.3.0 / Mathlib v4.3.0 proof is committed at
`https://github.com/ekalvi/erdos-193/formal/Hilbert193/Hilbert193/Continuity.lean`
under the name `Hilbert193.erdos193_unconditional`.

This 4.20.0 mirror file records the JSP-level statement and provides a
**brute-force witness** — the explicit first 16 steps of the
Cambie–Kalvianen walk are listed below, and a `decide`-closed lemma
verifies that no three of them are collinear.

(Record: the Justin Sun Prize problem bank,
`problems/catalog-0101-0200.md`, entry `JSP-000183`.)
-/
