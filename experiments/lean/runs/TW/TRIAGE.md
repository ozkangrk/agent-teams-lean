# TRIAGE.md (orchestrator, 23:30)

Ref: statements in `scratch/problems_index.json`; upstream sources `scratch/all_sources.txt`.
Smoke test accepted: OEIS-112970-conjecture1 (5.3s referee).

## Tier A — assigned round 1
| worker | ids | teknik |
|---|---|---|
| w1-witness | OEIS-103425, OEIS-306477, OEIS-64169, OEIS-70823 | python ile tanık bul, Lean'da açık tanık / decide |
| w2-period | OEIS-113250, OEIS-113252, OEIS-113255 | a(n+6)=C·a(n) güçlü tümevarım + n%6 durum ayrımı |
| w3-twostep | OEIS-100434-c2/c3, OEIS-112970-c2/c1_value/c3 | iki-adımlı tümevarım (upstream a_even/a_odd kanıtlı, kullanılabilir) |
| w4-graphs | WOWII 59,194,200,291 | python graf taraması → açık graf + decide; answer(False) → ¬X |
| w5-numthy | OEIS-3625, OEIS-129365-c1, OEIS-48153 | QR/bölünebilirlik/padik değerlendirme |
| w6-misc | OEIS-287616, OEIS-108306, (sonra OEIS-176477 c1/c2) | kütüphane json'u oku, invert transform = matris kuvveti |

## Tier B — yedek (boşalan workera)
OEIS-71532 (mahler-parity tanık? büyük olabilir), OEIS-105801 (3-adik stabilizasyon), OEIS-22030 (Cassini),
OEIS-76141 (tails sayımı ≤1), OEIS-108081 (X-kelimeleri), OEIS-237271 obs_carmichael, OEIS-93456 (sonsuz şahit),
OEIS-211417 (Landau faktöriyel oranı ×2), OEIS-100474 (büyük hesap+sertifika), ErdosProblems-348 (tanım oku).

## Skip (araştırma seviyesi / çok büyük)
Sendov, Hindman-172, 53175, 49473, 105565, 109074, 102371, 100474-catalan?, Mathoverflow-1973 (S⁶ karmaşık),
0805.3777 (tensör rank), Borsuk, Komlos, Pompeiu, Sidorenko (dejenere W? bakılabilir), TuDeng, Erdos 181/371/547,
141057, 185895-c2/c3, 3162, 1818-c1/c2, 3189, 129365-c2-c4? (görelü).
