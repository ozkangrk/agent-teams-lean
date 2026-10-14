# RESULT — CS6 pilot P1 (swarm)

Tarih: 2026-10-12, oturum 11:47–14:47 (bütçe 3 sa). Kok ajan + en fazla 6 alt ajan (glm-5.3).

## Kabul edilen kanıtlar (referee `accepted: true`)

| # | Problem | Kanıt özeti | Ajan | Dosya |
|---|---------|-------------|------|-------|
| 1 | Erdos138.monoAPNumber_two_one (W 1 = 1) | sInf üstünde sInf_le + sInf_ge: 0/1 noktalarında AP yok (bos domain, decide/omega), 3'te var (renk sabiti) | root | proofs/ErdosProblems-138-monoAPNumber_two_one.lean |
| 2 | Erdos138.monoAPNumber_two_two (W 2 = 3) | guvercin: {1,2,3}'ün 2-renklenmesinde mono 2-AP (3 çift); N=0,1,2'den yok (encard + omega/decide); le_antisymm | root | proofs/ErdosProblems-138-monoAPNumber_two_two.lean |
| 3 | OEIS-113250-conjecture | kapalı form a n = 4^n * q n, q 6-periyodik [-1,1,2,1,-1,4]; tek indislerde q ∈ {1,4} → kare | oeis113250 | proofs/OEIS-113250-conjecture.lean |

## Denenip reddedilen / yarım kalan

| 4 | Erdos1074.erdos_1074.variants.EHSNumbers_init | per-eleman üyelik (tanık p=61,71,83,23,59,61,661), genel üyeliksizlik (m!+1 çarpanları ≡1 mod m), Nat.count/nth zinciri | w1074 | proofs/ErdosProblems-1074-erdos_1074.variants.EHSNumbers_init.lean |
| 5 | Erdos1074.erdos_1074.variants.PillaiPrimes_init | tanık m=14,18,15,8,18,9; üyeliksizlik: p−1'e kadar decide + büyük-m çelişkisi | w1074 | proofs/ErdosProblems-1074-erdos_1074.variants.PillaiPrimes_init.lean |

## Reddedilen / yarım kalan

| Problem | Durum | Not |
|---------|-------|-----|
| 812 lower_bound | negatif | uniform süsleme +2n+1 sınırı; BEFS89 cihazı rekonstrükte edilemedi; scratch/ramsey812b/reduction.lean indirgeme derliyor (tek açık parca: Bad (R n + 4n − 9) boyaması) |
| 1050 borwein (2b) | negatif | altyapı (denom≠0, summable) derlendi; çekirdek irrasyonellik argümanı bulunamadı |
| 1050 borwein (3) | negatif | Lambert kuyruk indirgemesi + s-carpanli teleskop dogrulandi; yakinsaklik-rotasi oldugu kanit; tek canli yol Bo91 basamak argumani (cevrimdisi). Kalinti: Borwein3.irrational_of_approx (scratch/borwein3/lem.lean) |
| 1050 borwein (1050/b1) | negatif | 3. deneme: bolen duvari prod(q^j-1) ~ q^(J^2/2); CF kismi bolen max 417. Kalinti: scratch/borwein1/infra.lean (tail_two_term 2. mertebe Lambert kuyrugu + genel irrational_of_approx) |
| 650 erdos_selfridge | sürüyor (w650) | erdos650 sessizce kapandi (yapisal bulgular: q_i=d_ij(r_j-d_ij), v_j=kappa*u_j/(kappa-u_j-1)); kok CRT ile 6 aday (D-orani ~1.05); forall-m parametrik aile araniyor |
| 698 | sürüyor | p698rb: dosya tek sorry (bergman_core: 4^i*n < 16i^2(i-1)*g^2, yani g > 2^i*sqrt(n)/(4i*sqrt(i-1)) — Bergman [Be11]); vandermonde/es_bound/h_le_gcd derliyor; bergman698 + w1074 yarisiyor |
| 966, 1036, 206 | atlandı | Gallai/Hales–Jewett ve Shelah/Kovaç gereksinimleri; süre dışı |
