# IA1 Sonuç Raporu

```json
{
  "accepted": [
  "OEIS-100434-conjecture2",
  "OEIS-100434-conjecture3",
  "OEIS-103425-conjecture",
  "OEIS-108306-conjecture",
  "OEIS-112970-conjecture1",
  "OEIS-112970-conjecture2",
  "OEIS-113250-conjecture",
  "OEIS-113252-conjecture",
  "OEIS-113255-conjecture",
  "OEIS-129365-conjecture1",
  "OEIS-129365-conjecture2",
  "OEIS-237271-conjecture_5",
  "OEIS-3625-conjecture",
  "OEIS-93456-conjecture"
]
}
```

## Özet
100 problemin tamamı triage edildi; şu ana kadar **14 ispat hakem tarafından KABUL EDİLDİ**
(Lean 4 + Mathlib, `referee/check.py`, tümü `accepted: true`). Kayıtlar `ledger.jsonl`'de. Çalışma sürüyor.

## Kabul edilen ispatlar
| # | Problem | Yöntem |
|---|---------|--------|
| 1 | OEIS-103425-conjecture | kapalı form + k-indüksiyonu |
| 14 | OEIS-237271-conjecture_5 | bölen-sıralı D üzerinde simetri eşleştirmesi (d,d')↔(m/d',m/d) + even_sum_window parite lemma'sı; countP_zip_sum list-indüksiyonu |
| 2 | OEIS-112970-conjecture2 | parite / kapalı form |
| 3 | OEIS-113250-conjecture | a(6k+r) = ±2^(12k+e_r), 6 durumlu k-indüksiyonu |
| 4 | OEIS-100434-conjecture3 | c/d çiftliği modülleri |
| 5 | OEIS-100434-conjecture2 | heven ile tamsayı bölme |
| 6 | OEIS-93456-conjecture | satır-tabanlı v₂ analizi: a(2^m) ∤ a(2^m+1) sonsuz çok n |
| 7 | OEIS-112970-conjecture1 | a(2^(n+1)+1) tek → a((2^(n+1)+1)/2) = a(2^n), bölme omega |
| 8 | OEIS-3625-conjecture | quadratic reciprocity + diskriminant −7: A p ↔ Irreducible (X²+X+2 mod p) |
| 9 | OEIS-113252-conjecture | c-lineer tekrarlama + k-indüksiyon |
| 10 | OEIS-113255-conjecture | 113252 ailesi, uyarlanmış katsayı kombinasyonu |
| 11 | OEIS-129365-conjecture1 | p-adik değerlendirme: v_p(gcd çarpımı) = Σ⌊n/p^e⌋² ≥ v_p(faktöriyel çarpımı); Legendre formülü + Icc bölünmesi |
| 12 | OEIS-108306-conjecture | (accepted earlier; tabloya geç eklenmiş) |
| 13 | OEIS-129365-conjecture2 | tam p-adik özdeşlik: a(n) = num/den, her asal için v_p(num) = v_p(den) + Σ_e b(⌊n/p^e⌋); den ∣ num tam bölünebilirlik + eşitlik yönleri |

## Denenip tamamlanamayanlar (henüz)
- OEIS-70823-conjecture: answer(False) — küçük n taranmasında çürütme tanığı bulunamadı; upstream ispat sorry'li.
- OEIS-70823-conjecture: devam ediyor (sonraki aday).

## Dürüstlük beyanı
Bu raporda yalnızca hakemin `accepted: true` döndürdüğü ispatlar listelenir.
Tüm girişler (başarılı/başarısız) `ledger.jsonl`'de izlenebilir.