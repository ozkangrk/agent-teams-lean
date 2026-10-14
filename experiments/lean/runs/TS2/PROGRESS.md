# TS2 ilerleme notlari (Turkce)

- 07:11 basladi. 100 problem triage ediliyor. Odak: OEIS kisa nufuzlu ifadeler.
- Ilk iki kanit kabul edildi: OEIS-112970 conjecture1 ve conjecture2 (tek adim acilim + induksiyon, her iki taraf da 1).
- Siradaki: A113250/252/255 (kapali form 4^n * periyodik), A100434 conjecture2/3, sonra sonlu karsit ornekler (A306477, A71532, A70823, A64169).

## 2026-10-14 ~saat 2
- A113250, A113252, A113255 kabul edildi (tek-kare teoremleri; periyodik + t-kare sablonu).
- Toplam kabul: 5 (112970 x2 dahil). Sıradaki: A100434, sayisal karsi-ornek problemleri.

100434 c2+c3 kabul edildi (toplam 7). Sıradaki: 102371/237271/287616/70823.

2026-10-14 13:07:46.066279: 3625 kabul edildi (toplam 9). QR ile −7 nonresidue ⟺ p%7∈{3,5,6}. Sıradaki hedef: 141057/3162 değerlendirme.
2026-10-14 13:18:12.621477: Son durum: 9 ispat kabul edildi (112970x2, 113250/252/255, 100434x2, 108306, 3625). 3625: quadratic reciprocity ile -7 nonresidue ⟺ p%7∈{3,5,6}. 22030 (Somos-benzeri, invariant bulunamadi), 93456 (kanit kisa-aralik asall gerektiriyor), 287616 (T+P+H teoremi), 48153 (zemin-toplami), 64169 (karsi-ornek cok buyuk, n>4000), 306477 (karsi-ornek >300000) denendi/analiz edildi, hepsi cekirdek-uygun degil. Ledger yanlislikla silindi, oturum gecmisinden yeniden insa edildi (12 kayit). Sonuc: RESULT.md 9 ispat.
2026-10-14 13:26:28.891079: 103425 kabul edildi (10 toplam). Sabit x=4 tanikli varlik ispati, upstream variant kalibi.
2026-10-14 13:27:33.512474: Oturum sonlandi. TOPLAM 10 kabul: +103425 (varlik tanigi). Kalan butce bosa cikarildi; uygun hedef kalmadi (102371 ~3saat, digerleri arastirma-derece).
2026-10-14 13:53:55.741639: Son 35 dk: graf sanrileri (59/291: kapsamli arama, ihlal yok), 194/200 (Petersen tipi karsi-ornek, Hamilton-olmayanlik ispati cok uzun), 64169 (n>4000), 93456 (kisa-aralik asal) denendi; hepsi reddedildi. Kesin sonuc: 10 kabul.
2026-10-14 14:18:34.958570: Son bolumde 237271 observation_carmichael'e tam saldiri: k tekligi (b=k-1 Fermat), (1,minFac) ve (k/minFac,k) ardasil bolen ciftleriyle a>=3 ispati kuruldu; dosya %90 derleniyor (2 omega hilesi + 1 rcases detayi kaldi), butunene yetmedi. Reddedildi olarak loglandi. KESIN SONUC: 10 kabul.

11. kanıt KABUL EDİLDİ: OEIS-237271-observation_carmichael (Carmichael sayıları için 3 ≤ a k; liste-zip ardışıklık lemması + tekrarlı omega/rewriting onarımı).
