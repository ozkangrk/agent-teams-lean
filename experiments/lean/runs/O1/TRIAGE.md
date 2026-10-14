# TRIAGE — CS6 main run O1 (94 statements)

Sweep: read all 94 upstream statements; numeric triage in Python (terms, counterexample hunt, OEIS entries).
Legend: **P**=proof candidate, **D**=disproof candidate, **X**=hopeless/open (skip).

## Top candidates (worked on)
- OEIS-60957-conjecture (A060957, Ang): pure finite combinatorics. m and p^a·m subset-products of {1..n} ⟹ p^k·m for k<a. Verified n≤18. Proof via exchange lemma (replace element x by x/p) — see notes/60957_notes.md. **P — prover assigned.**
- OEIS-60841-conjecture1 (A060841): den(1/det)=1 ⟺ n ∈ [1,34]∪{36,38}. Key: 1/lcm matrix = A·diag(φ)·Aᵀ with triangular A ⟹ 1/det = ∏_{k≤n} k²/φ(k). Good set verified; v₂(∏)<0 for ALL other n ≤ 20000 (empirical). Remaining math: prove v₂<0 for n≥39. **P — prover assigned.**
- OEIS-224-conjecture (A000224): # squares mod n: n²≡1 mod a(a−1) ⟺ n odd prime. Verified n≤4000. Needs: a(p)=(p+1)/2, CRT formula, composite-direction argument. **P — prover assigned (risky).**
- OEIS-135508-conjecture (A135508): Rowland/Shevevel-type: a(p−1)=p for p−2 composite ⟸ "a(n) ∈ {1}∪primes" theorem. Verified p<410. Long proof (needs the Shevelev induction). **P — scout+prover.**
- OEIS-46969-conjecture1 (A046969): a p = 12(2p−1) via von Staudt–Clausen + Kummer v_p(num B_{2p})=1. Mathlib coverage of Bernoulli congruences unclear. **P — scout checks Mathlib.**
- OEIS-017666 (A017666): a(n)=n/gcd(n,σ(n)) practical ⟹ n practical. No counterexample <2·10^5. Math proof unclear. **P — scout.**

## Disproof hunts (all NEGATIVE so far — no counterexamples found)
- A108866 numerator≡0 mod n² ⟺ prime: holds ≤ 400 (incl. Wieferich 1093, 3511).
- A000224: holds ≤ 4000. A002426 central trinomial: holds ≤ 700.
- A105720 squares: only n=3,6 <3000. A007468: only n=38 (checked <10^4? no, small).
- A080101 prime powers in prime gaps ≤ 2 up to 3e6. A069923: no zero n≤300. A091591 twins between squares: zeros exactly {1,9,19,26,27,30,34,39,49,53,77,122} (consistent, last=122).
- A024356 Hankel: det 0 only at n=4 (≤17). A071524 det zeros at {6..11,13..19,28} consistent with conj (none >28 up to 44).
- A004290: k=1,2,3 fine (a(10^k−1)=R_{9k}, max below is R_{9k−3}·10³ at n=8·10^{k−1}−8).
- A087207 trajectories blow up astronomically (no proof of non-termination ⇒ skip). A108569: no odd terms <3e5.
- A060957: no violations n≤18. A096535: all k∈[0,50) appear n<4e4. A182510: exactly 8 zeros <10^5 ✓ consistent.
- A011545 π-prefix squares: none <5000 digits. A069922: no zero n≤40. A038771: all semiprime ≤ n=25. A110475: no fail ≤ 1e5. A153330: no bad diffs <4e5.

## Skipped (open/hopeless, no cheap disproof found)
Goldbach/twin/Legendre-type: 103151, 5153, 1599(odd perfect), 91591, 185150, 69922, 69923, 34694, 37274(home primes), 101779, 110835(Sierpiński), 110566, 119591, 110854, 93818, 17666, 105020(semiprime Goldbach), 2407(Cuban ∞), 87571, 86766, 130911, 40(log log gaps), 182126-c2(needs gap²<p — unproven), 80326, 2(Kolakoski), 181391(Van Eck), 71532(Mahler 3/2), 38552(class numbers), 96535, 145355, 2426, 79727×2(Sun supercongruences), 141057, 357513, 71524×2, 182510, 7013(Catalan-Mersenne), 2326×2(Wieferich-order-3 open), 24356/78729 (the n=4 direction is easy algebra: (k+1)(k+2)(k+3)(k+4)+1=(k²+5k+5)² — but the ∀n≠4 existence direction is open), 108129 (Riesel, k<509203 open), 105210 (disjointness, only numeric), 105720/7468 (infinite direction open), 104320, 100800, 103662, 78680 (Fermat numbers F33+ open), 72200, 76495, 83753, 1146, 7918×2 (minimal n-AP starts unproven), 53000, 69004 (a(n)>0 open; the 512720 counterexample in the file is for a different solved variant), 7406 (composite direction looks open), 38771 (∀n semiprime open), 117531, 135508→P above, 60957→P above, 167918×2, 1157, 38107, 160324×2, 71532, 110475 (open but verified), 11545, 46969→scout, 55487, 60841→P, 87207 (blow-up but no certificate), 96535.


## Session-2 additions (135508 scout)
- **OEIS-17666: PROOF IMPOSSIBLE** — statement implies no odd perfect numbers (odd n, σ(n)=2n ⟹ a(n)=1 practical, n odd>1 not practical). Disproof: no counterexample ≤ 10^8 (even-case Stewart scan, 220770 practical(a(n)) cases, all n practical; no odd multiperfect ≤10^7 besides 1). Even case likely a real theorem (n=2^a·p worked out) but NOT the upstream statement.
- OEIS-108569 (all terms even): for k=p odd prime, term ⟺ φ(2p−1)=p−1 ⟺ odd composite m=2p−1 with 2φ(m)=m−1 (Lehmer-flavored: φ(m)|m−1). Open ⟹ X.
- OEIS-103662 a_40: covering-congruence method handles 3 of 4 classes (10|b trailing 0; gcd(b,10)=1 ends 01 via b^40≡1 mod 4∧25; b odd 5|b ends 90625 via mod 32∧5^40). Class "b even, 5∤b": only b^40≡76 mod 100 forced (λ(5^k)|40 only for k≤2), digits above not uniformly forced ⟹ X.
- 135508: closed as blocked (see notes/135508.md): needs least-prime-in-AP below ~r² + twin-prime-flavor condition; verified ≤1.2e5.
