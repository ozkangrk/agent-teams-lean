import FormalConjectures.OEIS.«71532»
set_option exponentiation.threshold 1000000

open Finset

/-! Streaming evaluation: `S f k r` computes the partial sum of the OEIS A071532
terms from index `k` upward for `f` steps, carrying `r = 3 ^ k` incrementally. -/

private def S (f k r : ℕ) : ℤ :=
  match f with
  | 0 => 0
  | g + 1 => (if (r >>> k) % 2 = 1 then (-1 : ℤ) else 1) + S g (k + 1) (3 * r)

private def Q1 : ℕ := 3^1024 * 3
private def Q2 : ℕ := 3^1024 * Q1
private def Q3 : ℕ := 3^1024 * Q2
private def Q4 : ℕ := 3^1024 * Q3
private def Q5 : ℕ := 3^1024 * Q4
private def Q6 : ℕ := 3^1024 * Q5
private def Q7 : ℕ := 3^1024 * Q6
private def Q8 : ℕ := 3^1024 * Q7
private def Q9 : ℕ := 3^1024 * Q8
private def Q10 : ℕ := 3^1024 * Q9
private def Q11 : ℕ := 3^1024 * Q10
private def Q12 : ℕ := 3^1024 * Q11
private def Q13 : ℕ := 3^1024 * Q12
private def Q14 : ℕ := 3^1024 * Q13
private def Q15 : ℕ := 3^1024 * Q14
private def Q16 : ℕ := 3^1024 * Q15
private def Q17 : ℕ := 3^1024 * Q16
private def Q18 : ℕ := 3^1024 * Q17
private def Q19 : ℕ := 3^1024 * Q18
private def Q20 : ℕ := 3^1024 * Q19
private def Q21 : ℕ := 3^1024 * Q20
private def Q22 : ℕ := 3^1024 * Q21
private def Q23 : ℕ := 3^1024 * Q22
private def Q24 : ℕ := 3^1024 * Q23
private def Q25 : ℕ := 3^1024 * Q24
private def Q26 : ℕ := 3^1024 * Q25
private def Q27 : ℕ := 3^1024 * Q26
private def Q28 : ℕ := 3^1024 * Q27
private def Q29 : ℕ := 3^1024 * Q28
private def Q30 : ℕ := 3^1024 * Q29
private def Q31 : ℕ := 3^1024 * Q30
private def Q32 : ℕ := 3^1024 * Q31
private def Q33 : ℕ := 3^1024 * Q32
private def Q34 : ℕ := 3^1024 * Q33
private def Q35 : ℕ := 3^1024 * Q34
private def Q36 : ℕ := 3^1024 * Q35
private def Q37 : ℕ := 3^1024 * Q36
private def Q38 : ℕ := 3^1024 * Q37
private def Q39 : ℕ := 3^1024 * Q38
private def Q40 : ℕ := 3^1024 * Q39
private def Q41 : ℕ := 3^1024 * Q40
private def Q42 : ℕ := 3^1024 * Q41
private def Q43 : ℕ := 3^1024 * Q42
private def Q44 : ℕ := 3^1024 * Q43
private def Q45 : ℕ := 3^1024 * Q44
private def Q46 : ℕ := 3^1024 * Q45
private def Q47 : ℕ := 3^1024 * Q46
private def Q48 : ℕ := 3^1024 * Q47
private def Q49 : ℕ := 3^1024 * Q48
private def Q50 : ℕ := 3^1024 * Q49
private def Q51 : ℕ := 3^1024 * Q50
private def Q52 : ℕ := 3^1024 * Q51
private def Q53 : ℕ := 3^1024 * Q52
private def Q54 : ℕ := 3^1024 * Q53
private def Q55 : ℕ := 3^1024 * Q54
private def Q56 : ℕ := 3^1024 * Q55
private def Q57 : ℕ := 3^1024 * Q56
private def Q58 : ℕ := 3^1024 * Q57
private def Q59 : ℕ := 3^1024 * Q58
private def Q60 : ℕ := 3^1024 * Q59
private def Q61 : ℕ := 3^1024 * Q60
private def Q62 : ℕ := 3^1024 * Q61
private def Q63 : ℕ := 3^1024 * Q62
private def Q64 : ℕ := 3^1024 * Q63
private def Q65 : ℕ := 3^1024 * Q64
private def Q66 : ℕ := 3^1024 * Q65
private def Q67 : ℕ := 3^1024 * Q66
private def Q68 : ℕ := 3^1024 * Q67
private def Q69 : ℕ := 3^1024 * Q68
private def Q70 : ℕ := 3^1024 * Q69
private def Q71 : ℕ := 3^1024 * Q70
private def Q72 : ℕ := 3^1024 * Q71
private def Q73 : ℕ := 3^1024 * Q72
private def Q74 : ℕ := 3^1024 * Q73
private def Q75 : ℕ := 3^1024 * Q74
private def Q76 : ℕ := 3^1024 * Q75
private def Q77 : ℕ := 3^1024 * Q76
private def Q78 : ℕ := 3^1024 * Q77
private def Q79 : ℕ := 3^1024 * Q78
private def Q80 : ℕ := 3^1024 * Q79
private def Q81 : ℕ := 3^1024 * Q80
private def Q82 : ℕ := 3^1024 * Q81
private def Q83 : ℕ := 3^1024 * Q82
private def Q84 : ℕ := 3^1024 * Q83
private def Q85 : ℕ := 3^1024 * Q84
private def Q86 : ℕ := 3^1024 * Q85
private def Q87 : ℕ := 3^1024 * Q86
private def Q88 : ℕ := 3^1024 * Q87
private def Q89 : ℕ := 3^1024 * Q88
private def Q90 : ℕ := 3^1024 * Q89
private def Q91 : ℕ := 3^1024 * Q90
private def Q92 : ℕ := 3^1024 * Q91
private def Q93 : ℕ := 3^1024 * Q92
private def Q94 : ℕ := 3^1024 * Q93
private def Q95 : ℕ := 3^1024 * Q94
private def Q96 : ℕ := 3^1024 * Q95
private def Q97 : ℕ := 3^1024 * Q96
private def Q98 : ℕ := 3^1024 * Q97
private def Q99 : ℕ := 3^1024 * Q98
private def Q100 : ℕ := 3^1024 * Q99
private def Q101 : ℕ := 3^1024 * Q100
private def Q102 : ℕ := 3^1024 * Q101
private def Q103 : ℕ := 3^1024 * Q102
private def Q104 : ℕ := 3^1024 * Q103
private def Q105 : ℕ := 3^1024 * Q104
private def Q106 : ℕ := 3^1024 * Q105
private def Q107 : ℕ := 3^1024 * Q106
private def Q108 : ℕ := 3^1024 * Q107
private def Q109 : ℕ := 3^1024 * Q108
private def Q110 : ℕ := 3^1024 * Q109
private def Q111 : ℕ := 3^1024 * Q110
private def Q112 : ℕ := 3^1024 * Q111
private def Q113 : ℕ := 3^1024 * Q112
private def Q114 : ℕ := 3^1024 * Q113
private def Q115 : ℕ := 3^1024 * Q114
private def Q116 : ℕ := 3^1024 * Q115
private def Q117 : ℕ := 3^1024 * Q116
private def Q118 : ℕ := 3^1024 * Q117
private def Q119 : ℕ := 3^1024 * Q118
private def Q120 : ℕ := 3^1024 * Q119
private def Q121 : ℕ := 3^1024 * Q120
private def Q122 : ℕ := 3^1024 * Q121
private def Q123 : ℕ := 3^1024 * Q122
private def Q124 : ℕ := 3^1024 * Q123
private def Q125 : ℕ := 3^1024 * Q124
private def Q126 : ℕ := 3^1024 * Q125
private def Q127 : ℕ := 3^1024 * Q126
private def Q128 : ℕ := 3^1024 * Q127
private def Q129 : ℕ := 3^1024 * Q128
private def Q130 : ℕ := 3^1024 * Q129
private def Q131 : ℕ := 3^1024 * Q130
private def Q132 : ℕ := 3^1024 * Q131
private def Q133 : ℕ := 3^1024 * Q132
private def Q134 : ℕ := 3^1024 * Q133
private def Q135 : ℕ := 3^1024 * Q134
private def Q136 : ℕ := 3^1024 * Q135
private def Q137 : ℕ := 3^1024 * Q136
private def Q138 : ℕ := 3^1024 * Q137
private def Q139 : ℕ := 3^1024 * Q138
private def Q140 : ℕ := 3^1024 * Q139
private def Q141 : ℕ := 3^1024 * Q140
private def Q142 : ℕ := 3^1024 * Q141
private def Q143 : ℕ := 3^1024 * Q142
private def Q144 : ℕ := 3^1024 * Q143
private def Q145 : ℕ := 3^1024 * Q144
private def Q146 : ℕ := 3^1024 * Q145
private def Q147 : ℕ := 3^1024 * Q146
private def Q148 : ℕ := 3^1024 * Q147
private def Q149 : ℕ := 3^1024 * Q148
private def Q150 : ℕ := 3^1024 * Q149
private def Q151 : ℕ := 3^1024 * Q150
private def Q152 : ℕ := 3^1024 * Q151
private def Q153 : ℕ := 3^1024 * Q152
private def Q154 : ℕ := 3^1024 * Q153
private def Q155 : ℕ := 3^1024 * Q154
private def Q156 : ℕ := 3^1024 * Q155
private def Q157 : ℕ := 3^1024 * Q156
private def Q158 : ℕ := 3^1024 * Q157
private def Q159 : ℕ := 3^1024 * Q158
private def Q160 : ℕ := 3^1024 * Q159
private def Q161 : ℕ := 3^1024 * Q160
private def Q162 : ℕ := 3^1024 * Q161
private def Q163 : ℕ := 3^1024 * Q162
private def Q164 : ℕ := 3^1024 * Q163
private def Q165 : ℕ := 3^1024 * Q164
private def Q166 : ℕ := 3^1024 * Q165
private def Q167 : ℕ := 3^1024 * Q166
private def Q168 : ℕ := 3^1024 * Q167
private def Q169 : ℕ := 3^1024 * Q168
private def Q170 : ℕ := 3^1024 * Q169
private def Q171 : ℕ := 3^1024 * Q170
private def Q172 : ℕ := 3^1024 * Q171
private def Q173 : ℕ := 3^1024 * Q172
private def Q174 : ℕ := 3^1024 * Q173
private def Q175 : ℕ := 3^1024 * Q174
private def Q176 : ℕ := 3^1024 * Q175
private def Q177 : ℕ := 3^1024 * Q176
private def Q178 : ℕ := 3^1024 * Q177
private def Q179 : ℕ := 3^1024 * Q178
private def Q180 : ℕ := 3^1024 * Q179
private def Q181 : ℕ := 3^1024 * Q180
private def Q182 : ℕ := 3^1024 * Q181
private def Q183 : ℕ := 3^1024 * Q182
private def Q184 : ℕ := 3^1024 * Q183
private def Q185 : ℕ := 3^1024 * Q184
private def Q186 : ℕ := 3^1024 * Q185
private def Q187 : ℕ := 3^1024 * Q186
private def Q188 : ℕ := 3^1024 * Q187
private def Q189 : ℕ := 3^1024 * Q188
private def Q190 : ℕ := 3^1024 * Q189
private def Q191 : ℕ := 3^1024 * Q190
private def Q192 : ℕ := 3^1024 * Q191
private def Q193 : ℕ := 3^1024 * Q192
private def Q194 : ℕ := 3^1024 * Q193
private def Q195 : ℕ := 3^1024 * Q194
private def Q196 : ℕ := 3^1024 * Q195
private def Q197 : ℕ := 3^1024 * Q196
private def Q198 : ℕ := 3^1024 * Q197
private def Q199 : ℕ := 3^1024 * Q198
private def Q200 : ℕ := 3^1024 * Q199
private def Q201 : ℕ := 3^1024 * Q200
private def Q202 : ℕ := 3^1024 * Q201
private def Q203 : ℕ := 3^1024 * Q202
private def Q204 : ℕ := 3^1024 * Q203
private def Q205 : ℕ := 3^1024 * Q204
private def Q206 : ℕ := 3^1024 * Q205
private def Q207 : ℕ := 3^1024 * Q206
private def Q208 : ℕ := 3^1024 * Q207
private def Q209 : ℕ := 3^1024 * Q208
private def Q210 : ℕ := 3^1024 * Q209
private def Q211 : ℕ := 3^1024 * Q210
private def Q212 : ℕ := 3^1024 * Q211
private def Q213 : ℕ := 3^1024 * Q212
private def Q214 : ℕ := 3^1024 * Q213
private def Q215 : ℕ := 3^1024 * Q214
private def Q216 : ℕ := 3^1024 * Q215
private def Q217 : ℕ := 3^1024 * Q216
private def Q218 : ℕ := 3^1024 * Q217
private def Q219 : ℕ := 3^1024 * Q218
private def Q220 : ℕ := 3^1024 * Q219
private def Q221 : ℕ := 3^1024 * Q220
private def Q222 : ℕ := 3^1024 * Q221
private def Q223 : ℕ := 3^1024 * Q222
private def Q224 : ℕ := 3^1024 * Q223
private def Q225 : ℕ := 3^1024 * Q224
private def Q226 : ℕ := 3^1024 * Q225
private def Q227 : ℕ := 3^1024 * Q226
private def Q228 : ℕ := 3^1024 * Q227
private def Q229 : ℕ := 3^1024 * Q228
private def Q230 : ℕ := 3^1024 * Q229
private def Q231 : ℕ := 3^1024 * Q230
private def Q232 : ℕ := 3^1024 * Q231
private def Q233 : ℕ := 3^1024 * Q232
private def Q234 : ℕ := 3^1024 * Q233
private def Q235 : ℕ := 3^1024 * Q234
private def Q236 : ℕ := 3^1024 * Q235
private def Q237 : ℕ := 3^1024 * Q236
private def Q238 : ℕ := 3^1024 * Q237
private def Q239 : ℕ := 3^1024 * Q238
private def Q240 : ℕ := 3^1024 * Q239
private def Q241 : ℕ := 3^1024 * Q240
private def Q242 : ℕ := 3^1024 * Q241
private def Q243 : ℕ := 3^1024 * Q242
private def Q244 : ℕ := 3^1024 * Q243
private def Q245 : ℕ := 3^1024 * Q244
private def Q246 : ℕ := 3^1024 * Q245
private def Q247 : ℕ := 3^1024 * Q246
private def Q248 : ℕ := 3^1024 * Q247
private def Q249 : ℕ := 3^1024 * Q248
private def Q250 : ℕ := 3^1024 * Q249
private def Q251 : ℕ := 3^1024 * Q250
private def Q252 : ℕ := 3^1024 * Q251
private def Q253 : ℕ := 3^1024 * Q252
private def Q254 : ℕ := 3^1024 * Q253
private def Q255 : ℕ := 3^1024 * Q254
private def Q256 : ℕ := 3^1024 * Q255
private def Q257 : ℕ := 3^1024 * Q256
private def Q258 : ℕ := 3^1024 * Q257
private def Q259 : ℕ := 3^1024 * Q258
private def Q260 : ℕ := 3^1024 * Q259
private def Q261 : ℕ := 3^1024 * Q260
private def Q262 : ℕ := 3^1024 * Q261
private def Q263 : ℕ := 3^1024 * Q262
private def Q264 : ℕ := 3^1024 * Q263
private def Q265 : ℕ := 3^1024 * Q264
private def Q266 : ℕ := 3^1024 * Q265
private def Q267 : ℕ := 3^1024 * Q266
private def Q268 : ℕ := 3^1024 * Q267
private def Q269 : ℕ := 3^1024 * Q268
private def Q270 : ℕ := 3^1024 * Q269
private def Q271 : ℕ := 3^1024 * Q270
private def Q272 : ℕ := 3^1024 * Q271
private def Q273 : ℕ := 3^1024 * Q272
private def Q274 : ℕ := 3^1024 * Q273
private def Q275 : ℕ := 3^1024 * Q274
private def Q276 : ℕ := 3^1024 * Q275
private def Q277 : ℕ := 3^1024 * Q276
private def Q278 : ℕ := 3^1024 * Q277
private def Q279 : ℕ := 3^1024 * Q278
private def Q280 : ℕ := 3^1024 * Q279
private def Q281 : ℕ := 3^1024 * Q280
private def Q282 : ℕ := 3^1024 * Q281
private def Q283 : ℕ := 3^1024 * Q282
private def Q284 : ℕ := 3^1024 * Q283
private def Q285 : ℕ := 3^1024 * Q284
private def Q286 : ℕ := 3^1024 * Q285
private def Q287 : ℕ := 3^1024 * Q286
private def Q288 : ℕ := 3^1024 * Q287
private def Q289 : ℕ := 3^1024 * Q288
private def Q290 : ℕ := 3^1024 * Q289
private def Q291 : ℕ := 3^1024 * Q290
private def Q292 : ℕ := 3^1024 * Q291
private def Q293 : ℕ := 3^1024 * Q292
private def Q294 : ℕ := 3^1024 * Q293
private def Q295 : ℕ := 3^1024 * Q294
private def Q296 : ℕ := 3^1024 * Q295
private def Q297 : ℕ := 3^1024 * Q296
private def Q298 : ℕ := 3^1024 * Q297
private def Q299 : ℕ := 3^1024 * Q298
private def Q300 : ℕ := 3^1024 * Q299
private def Q301 : ℕ := 3^1024 * Q300
private def Q302 : ℕ := 3^1024 * Q301
private def Q303 : ℕ := 3^1024 * Q302
private def Q304 : ℕ := 3^1024 * Q303
private def Q305 : ℕ := 3^1024 * Q304
private def Q306 : ℕ := 3^1024 * Q305
private def Q307 : ℕ := 3^1024 * Q306
private def Q308 : ℕ := 3^1024 * Q307
private def Q309 : ℕ := 3^1024 * Q308
private def Q310 : ℕ := 3^1024 * Q309
private def Q311 : ℕ := 3^1024 * Q310
private def Q312 : ℕ := 3^1024 * Q311
private def Q313 : ℕ := 3^1024 * Q312
private def Q314 : ℕ := 3^1024 * Q313
private def Q315 : ℕ := 3^1024 * Q314
private def Q316 : ℕ := 3^1024 * Q315
private def Q317 : ℕ := 3^1024 * Q316
private def Q318 : ℕ := 3^1024 * Q317
private def Q319 : ℕ := 3^1024 * Q318
private def Q320 : ℕ := 3^1024 * Q319
private def Q321 : ℕ := 3^1024 * Q320
private def Q322 : ℕ := 3^1024 * Q321
private def Q323 : ℕ := 3^1024 * Q322

private lemma sum_Icc_succ_bot {f : ℕ → ℤ} {k m : ℕ} (h2 : k ≤ m) :
    ∑ j ∈ Finset.Icc k (m + 1), f j = f k + ∑ j ∈ Finset.Icc (k + 1) (m + 1), f j := by
  have he : (Finset.Icc k (m + 1)).erase k = Finset.Icc (k + 1) (m + 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_erase]
    omega
  have hstep : ∑ j ∈ Finset.Icc k (m + 1), f j = ∑ j ∈ (Finset.Icc k (m + 1)).erase k, f j + f k :=
    (Finset.sum_erase_add _ f (Finset.mem_Icc.mpr (by omega))).symm
  rw [hstep, he]
  omega

private lemma term_bit (k : ℕ) :
    (-1 : ℤ) ^ (3 ^ k / 2 ^ k) = if (3 ^ k >>> k) % 2 = 1 then -1 else 1 := by
  have hsh : 3 ^ k >>> k = 3 ^ k / 2 ^ k := by omega
  rw [neg_one_pow_eq_pow_mod_two, hsh]
  rcases Nat.mod_two_eq_zero_or_one (3 ^ k / 2 ^ k) with h | h <;> rw [h] <;> simp

private lemma S_eq (f k r : ℕ) (hr : r = 3 ^ k) (hk : 1 ≤ k) :
    S f k r = ∑ j ∈ Finset.Icc k (k + f - 1), (-1 : ℤ) ^ (3 ^ j / 2 ^ j) := by
  induction f generalizing k r with
  | zero =>
    have hE : ∑ j ∈ Finset.Icc k (k + 0 - 1), (-1 : ℤ) ^ (3 ^ j / 2 ^ j) = 0 := by
      rw [Finset.Icc_eq_empty_of_lt (by omega : k + 0 - 1 < k)]
      simp
    rw [hE]
    rfl
  | succ g ih =>
    have hr3 : 3 * r = 3 ^ (k + 1) := by rw [hr, Nat.pow_succ]; ring
    show (if (r >>> k) % 2 = 1 then (-1 : ℤ) else 1) + S g (k + 1) (3 * r) = _
    rw [ih (k + 1) (3 * r) hr3 (by omega)]
    have hb : (if (r >>> k) % 2 = 1 then (-1 : ℤ) else 1) = (-1 : ℤ) ^ (3 ^ k / 2 ^ k) := by
      rw [hr]
      exact (term_bit k).symm
    rw [hb]
    cases g with
    | zero =>
      have hE : ∑ j ∈ Finset.Icc (k + 1) (k + 1 + 0 - 1),
          (-1 : ℤ) ^ (3 ^ j / 2 ^ j) = 0 := by
        rw [Finset.Icc_eq_empty_of_lt (by omega : k + 1 + 0 - 1 < k + 1)]
        simp
      rw [hE]
      have e : k + (0 + 1) - 1 = k := by omega
      rw [e, Finset.Icc_self, Finset.sum_singleton]
      ring
    | succ g' =>
      have hbot := sum_Icc_succ_bot (f := fun j => (-1 : ℤ) ^ (3 ^ j / 2 ^ j))
        (k := k) (m := k + g') (by omega)
      have eL : k + 1 + (g' + 1) - 1 = k + g' + 1 := by omega
      have eR : k + (g' + 1 + 1) - 1 = k + g' + 1 := by omega
      rw [eL, eR, hbot]

private lemma S_add (a b k r : ℕ) :
    S (a + b) k r = S a k r + S b (k + a) (3^a * r) := by
  induction a generalizing k r with
  | zero =>
    rw [Nat.zero_add]
    show S b k r = 0 + S b (k + 0) (3^0 * r)
    simp
  | succ a' ih =>
    have e1 : a' + 1 + b = a' + b + 1 := by omega
    have e2 : k + (a' + 1) = k + 1 + a' := by omega
    rw [e1, e2]
    show (if (r >>> k) % 2 = 1 then (-1 : ℤ) else 1) + S (a' + b) (k + 1) (3 * r) =
      ((if (r >>> k) % 2 = 1 then (-1 : ℤ) else 1) + S a' (k + 1) (3 * r)) +
      S b (k + 1 + a') (3^(a'+1) * r)
    rw [ih (k + 1) (3 * r)]
    have hc : 3^a' * (3 * r) = 3^(a'+1) * r := by
      rw [Nat.pow_succ]
      ring
    rw [hc]
    omega

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem swarm_proof : answer(False) ↔ ∀ n : ℕ, 2 < n → 0 < OeisA71532.a n := by
  constructor
  · intro h
    exact h.elim
  · intro h
    have b0 : S 1024 1 3 = -96 := by decide
    have b1 : S 1024 1025 Q1 = 2 := by decide
    have b2 : S 1024 2049 Q2 = 52 := by decide
    have b3 : S 1024 3073 Q3 = -48 := by decide
    have b4 : S 1024 4097 Q4 = 2 := by decide
    have b5 : S 1024 5121 Q5 = -6 := by decide
    have b6 : S 1024 6145 Q6 = -30 := by decide
    have b7 : S 1024 7169 Q7 = -24 := by decide
    have b8 : S 1024 8193 Q8 = 8 := by decide
    have b9 : S 1024 9217 Q9 = -14 := by decide
    have b10 : S 1024 10241 Q10 = -20 := by decide
    have b11 : S 1024 11265 Q11 = -42 := by decide
    have b12 : S 1024 12289 Q12 = 36 := by decide
    have b13 : S 1024 13313 Q13 = -16 := by decide
    have b14 : S 1024 14337 Q14 = -4 := by decide
    have b15 : S 1024 15361 Q15 = -18 := by decide
    have b16 : S 1024 16385 Q16 = 60 := by decide
    have b17 : S 1024 17409 Q17 = 8 := by decide
    have b18 : S 1024 18433 Q18 = -44 := by decide
    have b19 : S 1024 19457 Q19 = 8 := by decide
    have b20 : S 1024 20481 Q20 = 26 := by decide
    have b21 : S 1024 21505 Q21 = 10 := by decide
    have b22 : S 1024 22529 Q22 = -48 := by decide
    have b23 : S 1024 23553 Q23 = -22 := by decide
    have b24 : S 1024 24577 Q24 = -58 := by decide
    have b25 : S 1024 25601 Q25 = -16 := by decide
    have b26 : S 1024 26625 Q26 = 38 := by decide
    have b27 : S 1024 27649 Q27 = 46 := by decide
    have b28 : S 1024 28673 Q28 = -20 := by decide
    have b29 : S 1024 29697 Q29 = 0 := by decide
    have b30 : S 1024 30721 Q30 = -30 := by decide
    have b31 : S 1024 31745 Q31 = -4 := by decide
    have b32 : S 1024 32769 Q32 = -26 := by decide
    have b33 : S 1024 33793 Q33 = 18 := by decide
    have b34 : S 1024 34817 Q34 = -10 := by decide
    have b35 : S 1024 35841 Q35 = 24 := by decide
    have b36 : S 1024 36865 Q36 = 40 := by decide
    have b37 : S 1024 37889 Q37 = -24 := by decide
    have b38 : S 1024 38913 Q38 = -42 := by decide
    have b39 : S 1024 39937 Q39 = -44 := by decide
    have b40 : S 1024 40961 Q40 = -14 := by decide
    have b41 : S 1024 41985 Q41 = 32 := by decide
    have b42 : S 1024 43009 Q42 = 42 := by decide
    have b43 : S 1024 44033 Q43 = -32 := by decide
    have b44 : S 1024 45057 Q44 = 40 := by decide
    have b45 : S 1024 46081 Q45 = 0 := by decide
    have b46 : S 1024 47105 Q46 = 34 := by decide
    have b47 : S 1024 48129 Q47 = 8 := by decide
    have b48 : S 1024 49153 Q48 = 44 := by decide
    have b49 : S 1024 50177 Q49 = -4 := by decide
    have b50 : S 1024 51201 Q50 = -2 := by decide
    have b51 : S 1024 52225 Q51 = 24 := by decide
    have b52 : S 1024 53249 Q52 = -20 := by decide
    have b53 : S 1024 54273 Q53 = -50 := by decide
    have b54 : S 1024 55297 Q54 = 0 := by decide
    have b55 : S 1024 56321 Q55 = -16 := by decide
    have b56 : S 1024 57345 Q56 = -2 := by decide
    have b57 : S 1024 58369 Q57 = -10 := by decide
    have b58 : S 1024 59393 Q58 = 14 := by decide
    have b59 : S 1024 60417 Q59 = -14 := by decide
    have b60 : S 1024 61441 Q60 = 20 := by decide
    have b61 : S 1024 62465 Q61 = 12 := by decide
    have b62 : S 1024 63489 Q62 = -8 := by decide
    have b63 : S 1024 64513 Q63 = -70 := by decide
    have b64 : S 1024 65537 Q64 = -46 := by decide
    have b65 : S 1024 66561 Q65 = 8 := by decide
    have b66 : S 1024 67585 Q66 = 50 := by decide
    have b67 : S 1024 68609 Q67 = 2 := by decide
    have b68 : S 1024 69633 Q68 = 26 := by decide
    have b69 : S 1024 70657 Q69 = -32 := by decide
    have b70 : S 1024 71681 Q70 = -32 := by decide
    have b71 : S 1024 72705 Q71 = -2 := by decide
    have b72 : S 1024 73729 Q72 = -82 := by decide
    have b73 : S 1024 74753 Q73 = -42 := by decide
    have b74 : S 1024 75777 Q74 = 16 := by decide
    have b75 : S 1024 76801 Q75 = -22 := by decide
    have b76 : S 1024 77825 Q76 = -22 := by decide
    have b77 : S 1024 78849 Q77 = 0 := by decide
    have b78 : S 1024 79873 Q78 = -12 := by decide
    have b79 : S 1024 80897 Q79 = 46 := by decide
    have b80 : S 1024 81921 Q80 = -14 := by decide
    have b81 : S 1024 82945 Q81 = -22 := by decide
    have b82 : S 1024 83969 Q82 = -10 := by decide
    have b83 : S 1024 84993 Q83 = 18 := by decide
    have b84 : S 1024 86017 Q84 = -76 := by decide
    have b85 : S 1024 87041 Q85 = 4 := by decide
    have b86 : S 1024 88065 Q86 = 8 := by decide
    have b87 : S 1024 89089 Q87 = -24 := by decide
    have b88 : S 1024 90113 Q88 = -70 := by decide
    have b89 : S 1024 91137 Q89 = -6 := by decide
    have b90 : S 1024 92161 Q90 = 20 := by decide
    have b91 : S 1024 93185 Q91 = -12 := by decide
    have b92 : S 1024 94209 Q92 = 20 := by decide
    have b93 : S 1024 95233 Q93 = 32 := by decide
    have b94 : S 1024 96257 Q94 = 22 := by decide
    have b95 : S 1024 97281 Q95 = -20 := by decide
    have b96 : S 1024 98305 Q96 = 0 := by decide
    have b97 : S 1024 99329 Q97 = 58 := by decide
    have b98 : S 1024 100353 Q98 = -30 := by decide
    have b99 : S 1024 101377 Q99 = -24 := by decide
    have b100 : S 1024 102401 Q100 = -32 := by decide
    have b101 : S 1024 103425 Q101 = 54 := by decide
    have b102 : S 1024 104449 Q102 = -10 := by decide
    have b103 : S 1024 105473 Q103 = -4 := by decide
    have b104 : S 1024 106497 Q104 = 8 := by decide
    have b105 : S 1024 107521 Q105 = -16 := by decide
    have b106 : S 1024 108545 Q106 = 44 := by decide
    have b107 : S 1024 109569 Q107 = 30 := by decide
    have b108 : S 1024 110593 Q108 = 24 := by decide
    have b109 : S 1024 111617 Q109 = -38 := by decide
    have b110 : S 1024 112641 Q110 = -16 := by decide
    have b111 : S 1024 113665 Q111 = 26 := by decide
    have b112 : S 1024 114689 Q112 = -2 := by decide
    have b113 : S 1024 115713 Q113 = 34 := by decide
    have b114 : S 1024 116737 Q114 = -18 := by decide
    have b115 : S 1024 117761 Q115 = -4 := by decide
    have b116 : S 1024 118785 Q116 = 28 := by decide
    have b117 : S 1024 119809 Q117 = 34 := by decide
    have b118 : S 1024 120833 Q118 = 26 := by decide
    have b119 : S 1024 121857 Q119 = 26 := by decide
    have b120 : S 1024 122881 Q120 = -26 := by decide
    have b121 : S 1024 123905 Q121 = 22 := by decide
    have b122 : S 1024 124929 Q122 = 14 := by decide
    have b123 : S 1024 125953 Q123 = 42 := by decide
    have b124 : S 1024 126977 Q124 = -16 := by decide
    have b125 : S 1024 128001 Q125 = -22 := by decide
    have b126 : S 1024 129025 Q126 = -2 := by decide
    have b127 : S 1024 130049 Q127 = 6 := by decide
    have b128 : S 1024 131073 Q128 = -24 := by decide
    have b129 : S 1024 132097 Q129 = -20 := by decide
    have b130 : S 1024 133121 Q130 = 4 := by decide
    have b131 : S 1024 134145 Q131 = 14 := by decide
    have b132 : S 1024 135169 Q132 = -10 := by decide
    have b133 : S 1024 136193 Q133 = -32 := by decide
    have b134 : S 1024 137217 Q134 = -46 := by decide
    have b135 : S 1024 138241 Q135 = -24 := by decide
    have b136 : S 1024 139265 Q136 = -62 := by decide
    have b137 : S 1024 140289 Q137 = 0 := by decide
    have b138 : S 1024 141313 Q138 = 22 := by decide
    have b139 : S 1024 142337 Q139 = -62 := by decide
    have b140 : S 1024 143361 Q140 = 44 := by decide
    have b141 : S 1024 144385 Q141 = -14 := by decide
    have b142 : S 1024 145409 Q142 = 12 := by decide
    have b143 : S 1024 146433 Q143 = 4 := by decide
    have b144 : S 1024 147457 Q144 = 14 := by decide
    have b145 : S 1024 148481 Q145 = 16 := by decide
    have b146 : S 1024 149505 Q146 = 14 := by decide
    have b147 : S 1024 150529 Q147 = 20 := by decide
    have b148 : S 1024 151553 Q148 = 6 := by decide
    have b149 : S 1024 152577 Q149 = -14 := by decide
    have b150 : S 1024 153601 Q150 = -30 := by decide
    have b151 : S 1024 154625 Q151 = 6 := by decide
    have b152 : S 1024 155649 Q152 = -28 := by decide
    have b153 : S 1024 156673 Q153 = 14 := by decide
    have b154 : S 1024 157697 Q154 = -40 := by decide
    have b155 : S 1024 158721 Q155 = -22 := by decide
    have b156 : S 1024 159745 Q156 = 38 := by decide
    have b157 : S 1024 160769 Q157 = -12 := by decide
    have b158 : S 1024 161793 Q158 = -30 := by decide
    have b159 : S 1024 162817 Q159 = 6 := by decide
    have b160 : S 1024 163841 Q160 = -30 := by decide
    have b161 : S 1024 164865 Q161 = -24 := by decide
    have b162 : S 1024 165889 Q162 = -28 := by decide
    have b163 : S 1024 166913 Q163 = 16 := by decide
    have b164 : S 1024 167937 Q164 = -16 := by decide
    have b165 : S 1024 168961 Q165 = 30 := by decide
    have b166 : S 1024 169985 Q166 = -8 := by decide
    have b167 : S 1024 171009 Q167 = 16 := by decide
    have b168 : S 1024 172033 Q168 = -36 := by decide
    have b169 : S 1024 173057 Q169 = 4 := by decide
    have b170 : S 1024 174081 Q170 = 20 := by decide
    have b171 : S 1024 175105 Q171 = 6 := by decide
    have b172 : S 1024 176129 Q172 = -12 := by decide
    have b173 : S 1024 177153 Q173 = 24 := by decide
    have b174 : S 1024 178177 Q174 = 18 := by decide
    have b175 : S 1024 179201 Q175 = -20 := by decide
    have b176 : S 1024 180225 Q176 = 24 := by decide
    have b177 : S 1024 181249 Q177 = 6 := by decide
    have b178 : S 1024 182273 Q178 = 12 := by decide
    have b179 : S 1024 183297 Q179 = 46 := by decide
    have b180 : S 1024 184321 Q180 = -26 := by decide
    have b181 : S 1024 185345 Q181 = 28 := by decide
    have b182 : S 1024 186369 Q182 = 36 := by decide
    have b183 : S 1024 187393 Q183 = 4 := by decide
    have b184 : S 1024 188417 Q184 = -8 := by decide
    have b185 : S 1024 189441 Q185 = 14 := by decide
    have b186 : S 1024 190465 Q186 = 54 := by decide
    have b187 : S 1024 191489 Q187 = 28 := by decide
    have b188 : S 1024 192513 Q188 = -64 := by decide
    have b189 : S 1024 193537 Q189 = 14 := by decide
    have b190 : S 1024 194561 Q190 = 10 := by decide
    have b191 : S 1024 195585 Q191 = -26 := by decide
    have b192 : S 1024 196609 Q192 = -10 := by decide
    have b193 : S 1024 197633 Q193 = -14 := by decide
    have b194 : S 1024 198657 Q194 = -46 := by decide
    have b195 : S 1024 199681 Q195 = 26 := by decide
    have b196 : S 1024 200705 Q196 = -22 := by decide
    have b197 : S 1024 201729 Q197 = 14 := by decide
    have b198 : S 1024 202753 Q198 = 2 := by decide
    have b199 : S 1024 203777 Q199 = 38 := by decide
    have b200 : S 1024 204801 Q200 = 10 := by decide
    have b201 : S 1024 205825 Q201 = 2 := by decide
    have b202 : S 1024 206849 Q202 = -14 := by decide
    have b203 : S 1024 207873 Q203 = 16 := by decide
    have b204 : S 1024 208897 Q204 = 82 := by decide
    have b205 : S 1024 209921 Q205 = 36 := by decide
    have b206 : S 1024 210945 Q206 = -34 := by decide
    have b207 : S 1024 211969 Q207 = 18 := by decide
    have b208 : S 1024 212993 Q208 = -4 := by decide
    have b209 : S 1024 214017 Q209 = -42 := by decide
    have b210 : S 1024 215041 Q210 = 62 := by decide
    have b211 : S 1024 216065 Q211 = 22 := by decide
    have b212 : S 1024 217089 Q212 = -26 := by decide
    have b213 : S 1024 218113 Q213 = 12 := by decide
    have b214 : S 1024 219137 Q214 = -84 := by decide
    have b215 : S 1024 220161 Q215 = 2 := by decide
    have b216 : S 1024 221185 Q216 = -42 := by decide
    have b217 : S 1024 222209 Q217 = -38 := by decide
    have b218 : S 1024 223233 Q218 = 18 := by decide
    have b219 : S 1024 224257 Q219 = -26 := by decide
    have b220 : S 1024 225281 Q220 = 12 := by decide
    have b221 : S 1024 226305 Q221 = -26 := by decide
    have b222 : S 1024 227329 Q222 = 10 := by decide
    have b223 : S 1024 228353 Q223 = -44 := by decide
    have b224 : S 1024 229377 Q224 = 46 := by decide
    have b225 : S 1024 230401 Q225 = -8 := by decide
    have b226 : S 1024 231425 Q226 = -54 := by decide
    have b227 : S 1024 232449 Q227 = -6 := by decide
    have b228 : S 1024 233473 Q228 = 44 := by decide
    have b229 : S 1024 234497 Q229 = -16 := by decide
    have b230 : S 1024 235521 Q230 = 26 := by decide
    have b231 : S 1024 236545 Q231 = 4 := by decide
    have b232 : S 1024 237569 Q232 = 28 := by decide
    have b233 : S 1024 238593 Q233 = -48 := by decide
    have b234 : S 1024 239617 Q234 = -32 := by decide
    have b235 : S 1024 240641 Q235 = -10 := by decide
    have b236 : S 1024 241665 Q236 = 8 := by decide
    have b237 : S 1024 242689 Q237 = 54 := by decide
    have b238 : S 1024 243713 Q238 = 22 := by decide
    have b239 : S 1024 244737 Q239 = -30 := by decide
    have b240 : S 1024 245761 Q240 = -8 := by decide
    have b241 : S 1024 246785 Q241 = -4 := by decide
    have b242 : S 1024 247809 Q242 = 4 := by decide
    have b243 : S 1024 248833 Q243 = 92 := by decide
    have b244 : S 1024 249857 Q244 = 18 := by decide
    have b245 : S 1024 250881 Q245 = -16 := by decide
    have b246 : S 1024 251905 Q246 = 40 := by decide
    have b247 : S 1024 252929 Q247 = -2 := by decide
    have b248 : S 1024 253953 Q248 = 52 := by decide
    have b249 : S 1024 254977 Q249 = 14 := by decide
    have b250 : S 1024 256001 Q250 = 26 := by decide
    have b251 : S 1024 257025 Q251 = 30 := by decide
    have b252 : S 1024 258049 Q252 = -16 := by decide
    have b253 : S 1024 259073 Q253 = 22 := by decide
    have b254 : S 1024 260097 Q254 = 36 := by decide
    have b255 : S 1024 261121 Q255 = 4 := by decide
    have b256 : S 1024 262145 Q256 = 14 := by decide
    have b257 : S 1024 263169 Q257 = 26 := by decide
    have b258 : S 1024 264193 Q258 = -62 := by decide
    have b259 : S 1024 265217 Q259 = 28 := by decide
    have b260 : S 1024 266241 Q260 = 10 := by decide
    have b261 : S 1024 267265 Q261 = 20 := by decide
    have b262 : S 1024 268289 Q262 = 106 := by decide
    have b263 : S 1024 269313 Q263 = 48 := by decide
    have b264 : S 1024 270337 Q264 = -6 := by decide
    have b265 : S 1024 271361 Q265 = 22 := by decide
    have b266 : S 1024 272385 Q266 = -52 := by decide
    have b267 : S 1024 273409 Q267 = -82 := by decide
    have b268 : S 1024 274433 Q268 = -88 := by decide
    have b269 : S 1024 275457 Q269 = 16 := by decide
    have b270 : S 1024 276481 Q270 = 24 := by decide
    have b271 : S 1024 277505 Q271 = -30 := by decide
    have b272 : S 1024 278529 Q272 = 22 := by decide
    have b273 : S 1024 279553 Q273 = -30 := by decide
    have b274 : S 1024 280577 Q274 = 10 := by decide
    have b275 : S 1024 281601 Q275 = -2 := by decide
    have b276 : S 1024 282625 Q276 = 62 := by decide
    have b277 : S 1024 283649 Q277 = -28 := by decide
    have b278 : S 1024 284673 Q278 = 40 := by decide
    have b279 : S 1024 285697 Q279 = -32 := by decide
    have b280 : S 1024 286721 Q280 = 6 := by decide
    have b281 : S 1024 287745 Q281 = 46 := by decide
    have b282 : S 1024 288769 Q282 = -42 := by decide
    have b283 : S 1024 289793 Q283 = 22 := by decide
    have b284 : S 1024 290817 Q284 = 18 := by decide
    have b285 : S 1024 291841 Q285 = 32 := by decide
    have b286 : S 1024 292865 Q286 = 14 := by decide
    have b287 : S 1024 293889 Q287 = -20 := by decide
    have b288 : S 1024 294913 Q288 = 36 := by decide
    have b289 : S 1024 295937 Q289 = 18 := by decide
    have b290 : S 1024 296961 Q290 = 42 := by decide
    have b291 : S 1024 297985 Q291 = -64 := by decide
    have b292 : S 1024 299009 Q292 = -20 := by decide
    have b293 : S 1024 300033 Q293 = 0 := by decide
    have b294 : S 1024 301057 Q294 = 2 := by decide
    have b295 : S 1024 302081 Q295 = -66 := by decide
    have b296 : S 1024 303105 Q296 = 4 := by decide
    have b297 : S 1024 304129 Q297 = 0 := by decide
    have b298 : S 1024 305153 Q298 = 2 := by decide
    have b299 : S 1024 306177 Q299 = -42 := by decide
    have b300 : S 1024 307201 Q300 = 22 := by decide
    have b301 : S 1024 308225 Q301 = 8 := by decide
    have b302 : S 1024 309249 Q302 = 36 := by decide
    have b303 : S 1024 310273 Q303 = 8 := by decide
    have b304 : S 1024 311297 Q304 = 20 := by decide
    have b305 : S 1024 312321 Q305 = -2 := by decide
    have b306 : S 1024 313345 Q306 = 4 := by decide
    have b307 : S 1024 314369 Q307 = -38 := by decide
    have b308 : S 1024 315393 Q308 = -18 := by decide
    have b309 : S 1024 316417 Q309 = 2 := by decide
    have b310 : S 1024 317441 Q310 = 28 := by decide
    have b311 : S 1024 318465 Q311 = 16 := by decide
    have b312 : S 1024 319489 Q312 = -20 := by decide
    have b313 : S 1024 320513 Q313 = 44 := by decide
    have b314 : S 1024 321537 Q314 = 22 := by decide
    have b315 : S 1024 322561 Q315 = 6 := by decide
    have b316 : S 1024 323585 Q316 = 32 := by decide
    have b317 : S 1024 324609 Q317 = 8 := by decide
    have b318 : S 1024 325633 Q318 = -32 := by decide
    have b319 : S 1024 326657 Q319 = -82 := by decide
    have b320 : S 1024 327681 Q320 = 28 := by decide
    have b321 : S 1024 328705 Q321 = 22 := by decide
    have b322 : S 1024 329729 Q322 = 64 := by decide
    have b323 : S 770 330753 Q323 = 50 := by decide
    have hQ1 : 3^1024 * 3 = Q1 := rfl
    have hQ2 : 3^1024 * Q1 = Q2 := rfl
    have hQ3 : 3^1024 * Q2 = Q3 := rfl
    have hQ4 : 3^1024 * Q3 = Q4 := rfl
    have hQ5 : 3^1024 * Q4 = Q5 := rfl
    have hQ6 : 3^1024 * Q5 = Q6 := rfl
    have hQ7 : 3^1024 * Q6 = Q7 := rfl
    have hQ8 : 3^1024 * Q7 = Q8 := rfl
    have hQ9 : 3^1024 * Q8 = Q9 := rfl
    have hQ10 : 3^1024 * Q9 = Q10 := rfl
    have hQ11 : 3^1024 * Q10 = Q11 := rfl
    have hQ12 : 3^1024 * Q11 = Q12 := rfl
    have hQ13 : 3^1024 * Q12 = Q13 := rfl
    have hQ14 : 3^1024 * Q13 = Q14 := rfl
    have hQ15 : 3^1024 * Q14 = Q15 := rfl
    have hQ16 : 3^1024 * Q15 = Q16 := rfl
    have hQ17 : 3^1024 * Q16 = Q17 := rfl
    have hQ18 : 3^1024 * Q17 = Q18 := rfl
    have hQ19 : 3^1024 * Q18 = Q19 := rfl
    have hQ20 : 3^1024 * Q19 = Q20 := rfl
    have hQ21 : 3^1024 * Q20 = Q21 := rfl
    have hQ22 : 3^1024 * Q21 = Q22 := rfl
    have hQ23 : 3^1024 * Q22 = Q23 := rfl
    have hQ24 : 3^1024 * Q23 = Q24 := rfl
    have hQ25 : 3^1024 * Q24 = Q25 := rfl
    have hQ26 : 3^1024 * Q25 = Q26 := rfl
    have hQ27 : 3^1024 * Q26 = Q27 := rfl
    have hQ28 : 3^1024 * Q27 = Q28 := rfl
    have hQ29 : 3^1024 * Q28 = Q29 := rfl
    have hQ30 : 3^1024 * Q29 = Q30 := rfl
    have hQ31 : 3^1024 * Q30 = Q31 := rfl
    have hQ32 : 3^1024 * Q31 = Q32 := rfl
    have hQ33 : 3^1024 * Q32 = Q33 := rfl
    have hQ34 : 3^1024 * Q33 = Q34 := rfl
    have hQ35 : 3^1024 * Q34 = Q35 := rfl
    have hQ36 : 3^1024 * Q35 = Q36 := rfl
    have hQ37 : 3^1024 * Q36 = Q37 := rfl
    have hQ38 : 3^1024 * Q37 = Q38 := rfl
    have hQ39 : 3^1024 * Q38 = Q39 := rfl
    have hQ40 : 3^1024 * Q39 = Q40 := rfl
    have hQ41 : 3^1024 * Q40 = Q41 := rfl
    have hQ42 : 3^1024 * Q41 = Q42 := rfl
    have hQ43 : 3^1024 * Q42 = Q43 := rfl
    have hQ44 : 3^1024 * Q43 = Q44 := rfl
    have hQ45 : 3^1024 * Q44 = Q45 := rfl
    have hQ46 : 3^1024 * Q45 = Q46 := rfl
    have hQ47 : 3^1024 * Q46 = Q47 := rfl
    have hQ48 : 3^1024 * Q47 = Q48 := rfl
    have hQ49 : 3^1024 * Q48 = Q49 := rfl
    have hQ50 : 3^1024 * Q49 = Q50 := rfl
    have hQ51 : 3^1024 * Q50 = Q51 := rfl
    have hQ52 : 3^1024 * Q51 = Q52 := rfl
    have hQ53 : 3^1024 * Q52 = Q53 := rfl
    have hQ54 : 3^1024 * Q53 = Q54 := rfl
    have hQ55 : 3^1024 * Q54 = Q55 := rfl
    have hQ56 : 3^1024 * Q55 = Q56 := rfl
    have hQ57 : 3^1024 * Q56 = Q57 := rfl
    have hQ58 : 3^1024 * Q57 = Q58 := rfl
    have hQ59 : 3^1024 * Q58 = Q59 := rfl
    have hQ60 : 3^1024 * Q59 = Q60 := rfl
    have hQ61 : 3^1024 * Q60 = Q61 := rfl
    have hQ62 : 3^1024 * Q61 = Q62 := rfl
    have hQ63 : 3^1024 * Q62 = Q63 := rfl
    have hQ64 : 3^1024 * Q63 = Q64 := rfl
    have hQ65 : 3^1024 * Q64 = Q65 := rfl
    have hQ66 : 3^1024 * Q65 = Q66 := rfl
    have hQ67 : 3^1024 * Q66 = Q67 := rfl
    have hQ68 : 3^1024 * Q67 = Q68 := rfl
    have hQ69 : 3^1024 * Q68 = Q69 := rfl
    have hQ70 : 3^1024 * Q69 = Q70 := rfl
    have hQ71 : 3^1024 * Q70 = Q71 := rfl
    have hQ72 : 3^1024 * Q71 = Q72 := rfl
    have hQ73 : 3^1024 * Q72 = Q73 := rfl
    have hQ74 : 3^1024 * Q73 = Q74 := rfl
    have hQ75 : 3^1024 * Q74 = Q75 := rfl
    have hQ76 : 3^1024 * Q75 = Q76 := rfl
    have hQ77 : 3^1024 * Q76 = Q77 := rfl
    have hQ78 : 3^1024 * Q77 = Q78 := rfl
    have hQ79 : 3^1024 * Q78 = Q79 := rfl
    have hQ80 : 3^1024 * Q79 = Q80 := rfl
    have hQ81 : 3^1024 * Q80 = Q81 := rfl
    have hQ82 : 3^1024 * Q81 = Q82 := rfl
    have hQ83 : 3^1024 * Q82 = Q83 := rfl
    have hQ84 : 3^1024 * Q83 = Q84 := rfl
    have hQ85 : 3^1024 * Q84 = Q85 := rfl
    have hQ86 : 3^1024 * Q85 = Q86 := rfl
    have hQ87 : 3^1024 * Q86 = Q87 := rfl
    have hQ88 : 3^1024 * Q87 = Q88 := rfl
    have hQ89 : 3^1024 * Q88 = Q89 := rfl
    have hQ90 : 3^1024 * Q89 = Q90 := rfl
    have hQ91 : 3^1024 * Q90 = Q91 := rfl
    have hQ92 : 3^1024 * Q91 = Q92 := rfl
    have hQ93 : 3^1024 * Q92 = Q93 := rfl
    have hQ94 : 3^1024 * Q93 = Q94 := rfl
    have hQ95 : 3^1024 * Q94 = Q95 := rfl
    have hQ96 : 3^1024 * Q95 = Q96 := rfl
    have hQ97 : 3^1024 * Q96 = Q97 := rfl
    have hQ98 : 3^1024 * Q97 = Q98 := rfl
    have hQ99 : 3^1024 * Q98 = Q99 := rfl
    have hQ100 : 3^1024 * Q99 = Q100 := rfl
    have hQ101 : 3^1024 * Q100 = Q101 := rfl
    have hQ102 : 3^1024 * Q101 = Q102 := rfl
    have hQ103 : 3^1024 * Q102 = Q103 := rfl
    have hQ104 : 3^1024 * Q103 = Q104 := rfl
    have hQ105 : 3^1024 * Q104 = Q105 := rfl
    have hQ106 : 3^1024 * Q105 = Q106 := rfl
    have hQ107 : 3^1024 * Q106 = Q107 := rfl
    have hQ108 : 3^1024 * Q107 = Q108 := rfl
    have hQ109 : 3^1024 * Q108 = Q109 := rfl
    have hQ110 : 3^1024 * Q109 = Q110 := rfl
    have hQ111 : 3^1024 * Q110 = Q111 := rfl
    have hQ112 : 3^1024 * Q111 = Q112 := rfl
    have hQ113 : 3^1024 * Q112 = Q113 := rfl
    have hQ114 : 3^1024 * Q113 = Q114 := rfl
    have hQ115 : 3^1024 * Q114 = Q115 := rfl
    have hQ116 : 3^1024 * Q115 = Q116 := rfl
    have hQ117 : 3^1024 * Q116 = Q117 := rfl
    have hQ118 : 3^1024 * Q117 = Q118 := rfl
    have hQ119 : 3^1024 * Q118 = Q119 := rfl
    have hQ120 : 3^1024 * Q119 = Q120 := rfl
    have hQ121 : 3^1024 * Q120 = Q121 := rfl
    have hQ122 : 3^1024 * Q121 = Q122 := rfl
    have hQ123 : 3^1024 * Q122 = Q123 := rfl
    have hQ124 : 3^1024 * Q123 = Q124 := rfl
    have hQ125 : 3^1024 * Q124 = Q125 := rfl
    have hQ126 : 3^1024 * Q125 = Q126 := rfl
    have hQ127 : 3^1024 * Q126 = Q127 := rfl
    have hQ128 : 3^1024 * Q127 = Q128 := rfl
    have hQ129 : 3^1024 * Q128 = Q129 := rfl
    have hQ130 : 3^1024 * Q129 = Q130 := rfl
    have hQ131 : 3^1024 * Q130 = Q131 := rfl
    have hQ132 : 3^1024 * Q131 = Q132 := rfl
    have hQ133 : 3^1024 * Q132 = Q133 := rfl
    have hQ134 : 3^1024 * Q133 = Q134 := rfl
    have hQ135 : 3^1024 * Q134 = Q135 := rfl
    have hQ136 : 3^1024 * Q135 = Q136 := rfl
    have hQ137 : 3^1024 * Q136 = Q137 := rfl
    have hQ138 : 3^1024 * Q137 = Q138 := rfl
    have hQ139 : 3^1024 * Q138 = Q139 := rfl
    have hQ140 : 3^1024 * Q139 = Q140 := rfl
    have hQ141 : 3^1024 * Q140 = Q141 := rfl
    have hQ142 : 3^1024 * Q141 = Q142 := rfl
    have hQ143 : 3^1024 * Q142 = Q143 := rfl
    have hQ144 : 3^1024 * Q143 = Q144 := rfl
    have hQ145 : 3^1024 * Q144 = Q145 := rfl
    have hQ146 : 3^1024 * Q145 = Q146 := rfl
    have hQ147 : 3^1024 * Q146 = Q147 := rfl
    have hQ148 : 3^1024 * Q147 = Q148 := rfl
    have hQ149 : 3^1024 * Q148 = Q149 := rfl
    have hQ150 : 3^1024 * Q149 = Q150 := rfl
    have hQ151 : 3^1024 * Q150 = Q151 := rfl
    have hQ152 : 3^1024 * Q151 = Q152 := rfl
    have hQ153 : 3^1024 * Q152 = Q153 := rfl
    have hQ154 : 3^1024 * Q153 = Q154 := rfl
    have hQ155 : 3^1024 * Q154 = Q155 := rfl
    have hQ156 : 3^1024 * Q155 = Q156 := rfl
    have hQ157 : 3^1024 * Q156 = Q157 := rfl
    have hQ158 : 3^1024 * Q157 = Q158 := rfl
    have hQ159 : 3^1024 * Q158 = Q159 := rfl
    have hQ160 : 3^1024 * Q159 = Q160 := rfl
    have hQ161 : 3^1024 * Q160 = Q161 := rfl
    have hQ162 : 3^1024 * Q161 = Q162 := rfl
    have hQ163 : 3^1024 * Q162 = Q163 := rfl
    have hQ164 : 3^1024 * Q163 = Q164 := rfl
    have hQ165 : 3^1024 * Q164 = Q165 := rfl
    have hQ166 : 3^1024 * Q165 = Q166 := rfl
    have hQ167 : 3^1024 * Q166 = Q167 := rfl
    have hQ168 : 3^1024 * Q167 = Q168 := rfl
    have hQ169 : 3^1024 * Q168 = Q169 := rfl
    have hQ170 : 3^1024 * Q169 = Q170 := rfl
    have hQ171 : 3^1024 * Q170 = Q171 := rfl
    have hQ172 : 3^1024 * Q171 = Q172 := rfl
    have hQ173 : 3^1024 * Q172 = Q173 := rfl
    have hQ174 : 3^1024 * Q173 = Q174 := rfl
    have hQ175 : 3^1024 * Q174 = Q175 := rfl
    have hQ176 : 3^1024 * Q175 = Q176 := rfl
    have hQ177 : 3^1024 * Q176 = Q177 := rfl
    have hQ178 : 3^1024 * Q177 = Q178 := rfl
    have hQ179 : 3^1024 * Q178 = Q179 := rfl
    have hQ180 : 3^1024 * Q179 = Q180 := rfl
    have hQ181 : 3^1024 * Q180 = Q181 := rfl
    have hQ182 : 3^1024 * Q181 = Q182 := rfl
    have hQ183 : 3^1024 * Q182 = Q183 := rfl
    have hQ184 : 3^1024 * Q183 = Q184 := rfl
    have hQ185 : 3^1024 * Q184 = Q185 := rfl
    have hQ186 : 3^1024 * Q185 = Q186 := rfl
    have hQ187 : 3^1024 * Q186 = Q187 := rfl
    have hQ188 : 3^1024 * Q187 = Q188 := rfl
    have hQ189 : 3^1024 * Q188 = Q189 := rfl
    have hQ190 : 3^1024 * Q189 = Q190 := rfl
    have hQ191 : 3^1024 * Q190 = Q191 := rfl
    have hQ192 : 3^1024 * Q191 = Q192 := rfl
    have hQ193 : 3^1024 * Q192 = Q193 := rfl
    have hQ194 : 3^1024 * Q193 = Q194 := rfl
    have hQ195 : 3^1024 * Q194 = Q195 := rfl
    have hQ196 : 3^1024 * Q195 = Q196 := rfl
    have hQ197 : 3^1024 * Q196 = Q197 := rfl
    have hQ198 : 3^1024 * Q197 = Q198 := rfl
    have hQ199 : 3^1024 * Q198 = Q199 := rfl
    have hQ200 : 3^1024 * Q199 = Q200 := rfl
    have hQ201 : 3^1024 * Q200 = Q201 := rfl
    have hQ202 : 3^1024 * Q201 = Q202 := rfl
    have hQ203 : 3^1024 * Q202 = Q203 := rfl
    have hQ204 : 3^1024 * Q203 = Q204 := rfl
    have hQ205 : 3^1024 * Q204 = Q205 := rfl
    have hQ206 : 3^1024 * Q205 = Q206 := rfl
    have hQ207 : 3^1024 * Q206 = Q207 := rfl
    have hQ208 : 3^1024 * Q207 = Q208 := rfl
    have hQ209 : 3^1024 * Q208 = Q209 := rfl
    have hQ210 : 3^1024 * Q209 = Q210 := rfl
    have hQ211 : 3^1024 * Q210 = Q211 := rfl
    have hQ212 : 3^1024 * Q211 = Q212 := rfl
    have hQ213 : 3^1024 * Q212 = Q213 := rfl
    have hQ214 : 3^1024 * Q213 = Q214 := rfl
    have hQ215 : 3^1024 * Q214 = Q215 := rfl
    have hQ216 : 3^1024 * Q215 = Q216 := rfl
    have hQ217 : 3^1024 * Q216 = Q217 := rfl
    have hQ218 : 3^1024 * Q217 = Q218 := rfl
    have hQ219 : 3^1024 * Q218 = Q219 := rfl
    have hQ220 : 3^1024 * Q219 = Q220 := rfl
    have hQ221 : 3^1024 * Q220 = Q221 := rfl
    have hQ222 : 3^1024 * Q221 = Q222 := rfl
    have hQ223 : 3^1024 * Q222 = Q223 := rfl
    have hQ224 : 3^1024 * Q223 = Q224 := rfl
    have hQ225 : 3^1024 * Q224 = Q225 := rfl
    have hQ226 : 3^1024 * Q225 = Q226 := rfl
    have hQ227 : 3^1024 * Q226 = Q227 := rfl
    have hQ228 : 3^1024 * Q227 = Q228 := rfl
    have hQ229 : 3^1024 * Q228 = Q229 := rfl
    have hQ230 : 3^1024 * Q229 = Q230 := rfl
    have hQ231 : 3^1024 * Q230 = Q231 := rfl
    have hQ232 : 3^1024 * Q231 = Q232 := rfl
    have hQ233 : 3^1024 * Q232 = Q233 := rfl
    have hQ234 : 3^1024 * Q233 = Q234 := rfl
    have hQ235 : 3^1024 * Q234 = Q235 := rfl
    have hQ236 : 3^1024 * Q235 = Q236 := rfl
    have hQ237 : 3^1024 * Q236 = Q237 := rfl
    have hQ238 : 3^1024 * Q237 = Q238 := rfl
    have hQ239 : 3^1024 * Q238 = Q239 := rfl
    have hQ240 : 3^1024 * Q239 = Q240 := rfl
    have hQ241 : 3^1024 * Q240 = Q241 := rfl
    have hQ242 : 3^1024 * Q241 = Q242 := rfl
    have hQ243 : 3^1024 * Q242 = Q243 := rfl
    have hQ244 : 3^1024 * Q243 = Q244 := rfl
    have hQ245 : 3^1024 * Q244 = Q245 := rfl
    have hQ246 : 3^1024 * Q245 = Q246 := rfl
    have hQ247 : 3^1024 * Q246 = Q247 := rfl
    have hQ248 : 3^1024 * Q247 = Q248 := rfl
    have hQ249 : 3^1024 * Q248 = Q249 := rfl
    have hQ250 : 3^1024 * Q249 = Q250 := rfl
    have hQ251 : 3^1024 * Q250 = Q251 := rfl
    have hQ252 : 3^1024 * Q251 = Q252 := rfl
    have hQ253 : 3^1024 * Q252 = Q253 := rfl
    have hQ254 : 3^1024 * Q253 = Q254 := rfl
    have hQ255 : 3^1024 * Q254 = Q255 := rfl
    have hQ256 : 3^1024 * Q255 = Q256 := rfl
    have hQ257 : 3^1024 * Q256 = Q257 := rfl
    have hQ258 : 3^1024 * Q257 = Q258 := rfl
    have hQ259 : 3^1024 * Q258 = Q259 := rfl
    have hQ260 : 3^1024 * Q259 = Q260 := rfl
    have hQ261 : 3^1024 * Q260 = Q261 := rfl
    have hQ262 : 3^1024 * Q261 = Q262 := rfl
    have hQ263 : 3^1024 * Q262 = Q263 := rfl
    have hQ264 : 3^1024 * Q263 = Q264 := rfl
    have hQ265 : 3^1024 * Q264 = Q265 := rfl
    have hQ266 : 3^1024 * Q265 = Q266 := rfl
    have hQ267 : 3^1024 * Q266 = Q267 := rfl
    have hQ268 : 3^1024 * Q267 = Q268 := rfl
    have hQ269 : 3^1024 * Q268 = Q269 := rfl
    have hQ270 : 3^1024 * Q269 = Q270 := rfl
    have hQ271 : 3^1024 * Q270 = Q271 := rfl
    have hQ272 : 3^1024 * Q271 = Q272 := rfl
    have hQ273 : 3^1024 * Q272 = Q273 := rfl
    have hQ274 : 3^1024 * Q273 = Q274 := rfl
    have hQ275 : 3^1024 * Q274 = Q275 := rfl
    have hQ276 : 3^1024 * Q275 = Q276 := rfl
    have hQ277 : 3^1024 * Q276 = Q277 := rfl
    have hQ278 : 3^1024 * Q277 = Q278 := rfl
    have hQ279 : 3^1024 * Q278 = Q279 := rfl
    have hQ280 : 3^1024 * Q279 = Q280 := rfl
    have hQ281 : 3^1024 * Q280 = Q281 := rfl
    have hQ282 : 3^1024 * Q281 = Q282 := rfl
    have hQ283 : 3^1024 * Q282 = Q283 := rfl
    have hQ284 : 3^1024 * Q283 = Q284 := rfl
    have hQ285 : 3^1024 * Q284 = Q285 := rfl
    have hQ286 : 3^1024 * Q285 = Q286 := rfl
    have hQ287 : 3^1024 * Q286 = Q287 := rfl
    have hQ288 : 3^1024 * Q287 = Q288 := rfl
    have hQ289 : 3^1024 * Q288 = Q289 := rfl
    have hQ290 : 3^1024 * Q289 = Q290 := rfl
    have hQ291 : 3^1024 * Q290 = Q291 := rfl
    have hQ292 : 3^1024 * Q291 = Q292 := rfl
    have hQ293 : 3^1024 * Q292 = Q293 := rfl
    have hQ294 : 3^1024 * Q293 = Q294 := rfl
    have hQ295 : 3^1024 * Q294 = Q295 := rfl
    have hQ296 : 3^1024 * Q295 = Q296 := rfl
    have hQ297 : 3^1024 * Q296 = Q297 := rfl
    have hQ298 : 3^1024 * Q297 = Q298 := rfl
    have hQ299 : 3^1024 * Q298 = Q299 := rfl
    have hQ300 : 3^1024 * Q299 = Q300 := rfl
    have hQ301 : 3^1024 * Q300 = Q301 := rfl
    have hQ302 : 3^1024 * Q301 = Q302 := rfl
    have hQ303 : 3^1024 * Q302 = Q303 := rfl
    have hQ304 : 3^1024 * Q303 = Q304 := rfl
    have hQ305 : 3^1024 * Q304 = Q305 := rfl
    have hQ306 : 3^1024 * Q305 = Q306 := rfl
    have hQ307 : 3^1024 * Q306 = Q307 := rfl
    have hQ308 : 3^1024 * Q307 = Q308 := rfl
    have hQ309 : 3^1024 * Q308 = Q309 := rfl
    have hQ310 : 3^1024 * Q309 = Q310 := rfl
    have hQ311 : 3^1024 * Q310 = Q311 := rfl
    have hQ312 : 3^1024 * Q311 = Q312 := rfl
    have hQ313 : 3^1024 * Q312 = Q313 := rfl
    have hQ314 : 3^1024 * Q313 = Q314 := rfl
    have hQ315 : 3^1024 * Q314 = Q315 := rfl
    have hQ316 : 3^1024 * Q315 = Q316 := rfl
    have hQ317 : 3^1024 * Q316 = Q317 := rfl
    have hQ318 : 3^1024 * Q317 = Q318 := rfl
    have hQ319 : 3^1024 * Q318 = Q319 := rfl
    have hQ320 : 3^1024 * Q319 = Q320 := rfl
    have hQ321 : 3^1024 * Q320 = Q321 := rfl
    have hQ322 : 3^1024 * Q321 = Q322 := rfl
    have hQ323 : 3^1024 * Q322 = Q323 := rfl
    have key : S 331522 1 3 = 0 := by
      rw [show 331522 = 1024 + 330498 from by norm_num, S_add, hQ1, b0, show 330498 = 1024 + 329474 from by norm_num, S_add, hQ2, b1, show 329474 = 1024 + 328450 from by norm_num, S_add, hQ3, b2, show 328450 = 1024 + 327426 from by norm_num, S_add, hQ4, b3, show 327426 = 1024 + 326402 from by norm_num, S_add, hQ5, b4, show 326402 = 1024 + 325378 from by norm_num, S_add, hQ6, b5, show 325378 = 1024 + 324354 from by norm_num, S_add, hQ7, b6, show 324354 = 1024 + 323330 from by norm_num, S_add, hQ8, b7, show 323330 = 1024 + 322306 from by norm_num, S_add, hQ9, b8, show 322306 = 1024 + 321282 from by norm_num, S_add, hQ10, b9, show 321282 = 1024 + 320258 from by norm_num, S_add, hQ11, b10, show 320258 = 1024 + 319234 from by norm_num, S_add, hQ12, b11, show 319234 = 1024 + 318210 from by norm_num, S_add, hQ13, b12, show 318210 = 1024 + 317186 from by norm_num, S_add, hQ14, b13, show 317186 = 1024 + 316162 from by norm_num, S_add, hQ15, b14, show 316162 = 1024 + 315138 from by norm_num, S_add, hQ16, b15, show 315138 = 1024 + 314114 from by norm_num, S_add, hQ17, b16, show 314114 = 1024 + 313090 from by norm_num, S_add, hQ18, b17, show 313090 = 1024 + 312066 from by norm_num, S_add, hQ19, b18, show 312066 = 1024 + 311042 from by norm_num, S_add, hQ20, b19, show 311042 = 1024 + 310018 from by norm_num, S_add, hQ21, b20, show 310018 = 1024 + 308994 from by norm_num, S_add, hQ22, b21, show 308994 = 1024 + 307970 from by norm_num, S_add, hQ23, b22, show 307970 = 1024 + 306946 from by norm_num, S_add, hQ24, b23, show 306946 = 1024 + 305922 from by norm_num, S_add, hQ25, b24, show 305922 = 1024 + 304898 from by norm_num, S_add, hQ26, b25, show 304898 = 1024 + 303874 from by norm_num, S_add, hQ27, b26, show 303874 = 1024 + 302850 from by norm_num, S_add, hQ28, b27, show 302850 = 1024 + 301826 from by norm_num, S_add, hQ29, b28, show 301826 = 1024 + 300802 from by norm_num, S_add, hQ30, b29, show 300802 = 1024 + 299778 from by norm_num, S_add, hQ31, b30, show 299778 = 1024 + 298754 from by norm_num, S_add, hQ32, b31, show 298754 = 1024 + 297730 from by norm_num, S_add, hQ33, b32, show 297730 = 1024 + 296706 from by norm_num, S_add, hQ34, b33, show 296706 = 1024 + 295682 from by norm_num, S_add, hQ35, b34, show 295682 = 1024 + 294658 from by norm_num, S_add, hQ36, b35, show 294658 = 1024 + 293634 from by norm_num, S_add, hQ37, b36, show 293634 = 1024 + 292610 from by norm_num, S_add, hQ38, b37, show 292610 = 1024 + 291586 from by norm_num, S_add, hQ39, b38, show 291586 = 1024 + 290562 from by norm_num, S_add, hQ40, b39, show 290562 = 1024 + 289538 from by norm_num, S_add, hQ41, b40, show 289538 = 1024 + 288514 from by norm_num, S_add, hQ42, b41, show 288514 = 1024 + 287490 from by norm_num, S_add, hQ43, b42, show 287490 = 1024 + 286466 from by norm_num, S_add, hQ44, b43, show 286466 = 1024 + 285442 from by norm_num, S_add, hQ45, b44, show 285442 = 1024 + 284418 from by norm_num, S_add, hQ46, b45, show 284418 = 1024 + 283394 from by norm_num, S_add, hQ47, b46, show 283394 = 1024 + 282370 from by norm_num, S_add, hQ48, b47, show 282370 = 1024 + 281346 from by norm_num, S_add, hQ49, b48, show 281346 = 1024 + 280322 from by norm_num, S_add, hQ50, b49, show 280322 = 1024 + 279298 from by norm_num, S_add, hQ51, b50, show 279298 = 1024 + 278274 from by norm_num, S_add, hQ52, b51, show 278274 = 1024 + 277250 from by norm_num, S_add, hQ53, b52, show 277250 = 1024 + 276226 from by norm_num, S_add, hQ54, b53, show 276226 = 1024 + 275202 from by norm_num, S_add, hQ55, b54, show 275202 = 1024 + 274178 from by norm_num, S_add, hQ56, b55, show 274178 = 1024 + 273154 from by norm_num, S_add, hQ57, b56, show 273154 = 1024 + 272130 from by norm_num, S_add, hQ58, b57, show 272130 = 1024 + 271106 from by norm_num, S_add, hQ59, b58, show 271106 = 1024 + 270082 from by norm_num, S_add, hQ60, b59, show 270082 = 1024 + 269058 from by norm_num, S_add, hQ61, b60, show 269058 = 1024 + 268034 from by norm_num, S_add, hQ62, b61, show 268034 = 1024 + 267010 from by norm_num, S_add, hQ63, b62, show 267010 = 1024 + 265986 from by norm_num, S_add, hQ64, b63, show 265986 = 1024 + 264962 from by norm_num, S_add, hQ65, b64, show 264962 = 1024 + 263938 from by norm_num, S_add, hQ66, b65, show 263938 = 1024 + 262914 from by norm_num, S_add, hQ67, b66, show 262914 = 1024 + 261890 from by norm_num, S_add, hQ68, b67, show 261890 = 1024 + 260866 from by norm_num, S_add, hQ69, b68, show 260866 = 1024 + 259842 from by norm_num, S_add, hQ70, b69, show 259842 = 1024 + 258818 from by norm_num, S_add, hQ71, b70, show 258818 = 1024 + 257794 from by norm_num, S_add, hQ72, b71, show 257794 = 1024 + 256770 from by norm_num, S_add, hQ73, b72, show 256770 = 1024 + 255746 from by norm_num, S_add, hQ74, b73, show 255746 = 1024 + 254722 from by norm_num, S_add, hQ75, b74, show 254722 = 1024 + 253698 from by norm_num, S_add, hQ76, b75, show 253698 = 1024 + 252674 from by norm_num, S_add, hQ77, b76, show 252674 = 1024 + 251650 from by norm_num, S_add, hQ78, b77, show 251650 = 1024 + 250626 from by norm_num, S_add, hQ79, b78, show 250626 = 1024 + 249602 from by norm_num, S_add, hQ80, b79, show 249602 = 1024 + 248578 from by norm_num, S_add, hQ81, b80, show 248578 = 1024 + 247554 from by norm_num, S_add, hQ82, b81, show 247554 = 1024 + 246530 from by norm_num, S_add, hQ83, b82, show 246530 = 1024 + 245506 from by norm_num, S_add, hQ84, b83, show 245506 = 1024 + 244482 from by norm_num, S_add, hQ85, b84, show 244482 = 1024 + 243458 from by norm_num, S_add, hQ86, b85, show 243458 = 1024 + 242434 from by norm_num, S_add, hQ87, b86, show 242434 = 1024 + 241410 from by norm_num, S_add, hQ88, b87, show 241410 = 1024 + 240386 from by norm_num, S_add, hQ89, b88, show 240386 = 1024 + 239362 from by norm_num, S_add, hQ90, b89, show 239362 = 1024 + 238338 from by norm_num, S_add, hQ91, b90, show 238338 = 1024 + 237314 from by norm_num, S_add, hQ92, b91, show 237314 = 1024 + 236290 from by norm_num, S_add, hQ93, b92, show 236290 = 1024 + 235266 from by norm_num, S_add, hQ94, b93, show 235266 = 1024 + 234242 from by norm_num, S_add, hQ95, b94, show 234242 = 1024 + 233218 from by norm_num, S_add, hQ96, b95, show 233218 = 1024 + 232194 from by norm_num, S_add, hQ97, b96, show 232194 = 1024 + 231170 from by norm_num, S_add, hQ98, b97, show 231170 = 1024 + 230146 from by norm_num, S_add, hQ99, b98, show 230146 = 1024 + 229122 from by norm_num, S_add, hQ100, b99, show 229122 = 1024 + 228098 from by norm_num, S_add, hQ101, b100, show 228098 = 1024 + 227074 from by norm_num, S_add, hQ102, b101, show 227074 = 1024 + 226050 from by norm_num, S_add, hQ103, b102, show 226050 = 1024 + 225026 from by norm_num, S_add, hQ104, b103, show 225026 = 1024 + 224002 from by norm_num, S_add, hQ105, b104, show 224002 = 1024 + 222978 from by norm_num, S_add, hQ106, b105, show 222978 = 1024 + 221954 from by norm_num, S_add, hQ107, b106, show 221954 = 1024 + 220930 from by norm_num, S_add, hQ108, b107, show 220930 = 1024 + 219906 from by norm_num, S_add, hQ109, b108, show 219906 = 1024 + 218882 from by norm_num, S_add, hQ110, b109, show 218882 = 1024 + 217858 from by norm_num, S_add, hQ111, b110, show 217858 = 1024 + 216834 from by norm_num, S_add, hQ112, b111, show 216834 = 1024 + 215810 from by norm_num, S_add, hQ113, b112, show 215810 = 1024 + 214786 from by norm_num, S_add, hQ114, b113, show 214786 = 1024 + 213762 from by norm_num, S_add, hQ115, b114, show 213762 = 1024 + 212738 from by norm_num, S_add, hQ116, b115, show 212738 = 1024 + 211714 from by norm_num, S_add, hQ117, b116, show 211714 = 1024 + 210690 from by norm_num, S_add, hQ118, b117, show 210690 = 1024 + 209666 from by norm_num, S_add, hQ119, b118, show 209666 = 1024 + 208642 from by norm_num, S_add, hQ120, b119, show 208642 = 1024 + 207618 from by norm_num, S_add, hQ121, b120, show 207618 = 1024 + 206594 from by norm_num, S_add, hQ122, b121, show 206594 = 1024 + 205570 from by norm_num, S_add, hQ123, b122, show 205570 = 1024 + 204546 from by norm_num, S_add, hQ124, b123, show 204546 = 1024 + 203522 from by norm_num, S_add, hQ125, b124, show 203522 = 1024 + 202498 from by norm_num, S_add, hQ126, b125, show 202498 = 1024 + 201474 from by norm_num, S_add, hQ127, b126, show 201474 = 1024 + 200450 from by norm_num, S_add, hQ128, b127, show 200450 = 1024 + 199426 from by norm_num, S_add, hQ129, b128, show 199426 = 1024 + 198402 from by norm_num, S_add, hQ130, b129, show 198402 = 1024 + 197378 from by norm_num, S_add, hQ131, b130, show 197378 = 1024 + 196354 from by norm_num, S_add, hQ132, b131, show 196354 = 1024 + 195330 from by norm_num, S_add, hQ133, b132, show 195330 = 1024 + 194306 from by norm_num, S_add, hQ134, b133, show 194306 = 1024 + 193282 from by norm_num, S_add, hQ135, b134, show 193282 = 1024 + 192258 from by norm_num, S_add, hQ136, b135, show 192258 = 1024 + 191234 from by norm_num, S_add, hQ137, b136, show 191234 = 1024 + 190210 from by norm_num, S_add, hQ138, b137, show 190210 = 1024 + 189186 from by norm_num, S_add, hQ139, b138, show 189186 = 1024 + 188162 from by norm_num, S_add, hQ140, b139, show 188162 = 1024 + 187138 from by norm_num, S_add, hQ141, b140, show 187138 = 1024 + 186114 from by norm_num, S_add, hQ142, b141, show 186114 = 1024 + 185090 from by norm_num, S_add, hQ143, b142, show 185090 = 1024 + 184066 from by norm_num, S_add, hQ144, b143, show 184066 = 1024 + 183042 from by norm_num, S_add, hQ145, b144, show 183042 = 1024 + 182018 from by norm_num, S_add, hQ146, b145, show 182018 = 1024 + 180994 from by norm_num, S_add, hQ147, b146, show 180994 = 1024 + 179970 from by norm_num, S_add, hQ148, b147, show 179970 = 1024 + 178946 from by norm_num, S_add, hQ149, b148, show 178946 = 1024 + 177922 from by norm_num, S_add, hQ150, b149, show 177922 = 1024 + 176898 from by norm_num, S_add, hQ151, b150, show 176898 = 1024 + 175874 from by norm_num, S_add, hQ152, b151, show 175874 = 1024 + 174850 from by norm_num, S_add, hQ153, b152, show 174850 = 1024 + 173826 from by norm_num, S_add, hQ154, b153, show 173826 = 1024 + 172802 from by norm_num, S_add, hQ155, b154, show 172802 = 1024 + 171778 from by norm_num, S_add, hQ156, b155, show 171778 = 1024 + 170754 from by norm_num, S_add, hQ157, b156, show 170754 = 1024 + 169730 from by norm_num, S_add, hQ158, b157, show 169730 = 1024 + 168706 from by norm_num, S_add, hQ159, b158, show 168706 = 1024 + 167682 from by norm_num, S_add, hQ160, b159, show 167682 = 1024 + 166658 from by norm_num, S_add, hQ161, b160, show 166658 = 1024 + 165634 from by norm_num, S_add, hQ162, b161, show 165634 = 1024 + 164610 from by norm_num, S_add, hQ163, b162, show 164610 = 1024 + 163586 from by norm_num, S_add, hQ164, b163, show 163586 = 1024 + 162562 from by norm_num, S_add, hQ165, b164, show 162562 = 1024 + 161538 from by norm_num, S_add, hQ166, b165, show 161538 = 1024 + 160514 from by norm_num, S_add, hQ167, b166, show 160514 = 1024 + 159490 from by norm_num, S_add, hQ168, b167, show 159490 = 1024 + 158466 from by norm_num, S_add, hQ169, b168, show 158466 = 1024 + 157442 from by norm_num, S_add, hQ170, b169, show 157442 = 1024 + 156418 from by norm_num, S_add, hQ171, b170, show 156418 = 1024 + 155394 from by norm_num, S_add, hQ172, b171, show 155394 = 1024 + 154370 from by norm_num, S_add, hQ173, b172, show 154370 = 1024 + 153346 from by norm_num, S_add, hQ174, b173, show 153346 = 1024 + 152322 from by norm_num, S_add, hQ175, b174, show 152322 = 1024 + 151298 from by norm_num, S_add, hQ176, b175, show 151298 = 1024 + 150274 from by norm_num, S_add, hQ177, b176, show 150274 = 1024 + 149250 from by norm_num, S_add, hQ178, b177, show 149250 = 1024 + 148226 from by norm_num, S_add, hQ179, b178, show 148226 = 1024 + 147202 from by norm_num, S_add, hQ180, b179, show 147202 = 1024 + 146178 from by norm_num, S_add, hQ181, b180, show 146178 = 1024 + 145154 from by norm_num, S_add, hQ182, b181, show 145154 = 1024 + 144130 from by norm_num, S_add, hQ183, b182, show 144130 = 1024 + 143106 from by norm_num, S_add, hQ184, b183, show 143106 = 1024 + 142082 from by norm_num, S_add, hQ185, b184, show 142082 = 1024 + 141058 from by norm_num, S_add, hQ186, b185, show 141058 = 1024 + 140034 from by norm_num, S_add, hQ187, b186, show 140034 = 1024 + 139010 from by norm_num, S_add, hQ188, b187, show 139010 = 1024 + 137986 from by norm_num, S_add, hQ189, b188, show 137986 = 1024 + 136962 from by norm_num, S_add, hQ190, b189, show 136962 = 1024 + 135938 from by norm_num, S_add, hQ191, b190, show 135938 = 1024 + 134914 from by norm_num, S_add, hQ192, b191, show 134914 = 1024 + 133890 from by norm_num, S_add, hQ193, b192, show 133890 = 1024 + 132866 from by norm_num, S_add, hQ194, b193, show 132866 = 1024 + 131842 from by norm_num, S_add, hQ195, b194, show 131842 = 1024 + 130818 from by norm_num, S_add, hQ196, b195, show 130818 = 1024 + 129794 from by norm_num, S_add, hQ197, b196, show 129794 = 1024 + 128770 from by norm_num, S_add, hQ198, b197, show 128770 = 1024 + 127746 from by norm_num, S_add, hQ199, b198, show 127746 = 1024 + 126722 from by norm_num, S_add, hQ200, b199, show 126722 = 1024 + 125698 from by norm_num, S_add, hQ201, b200, show 125698 = 1024 + 124674 from by norm_num, S_add, hQ202, b201, show 124674 = 1024 + 123650 from by norm_num, S_add, hQ203, b202, show 123650 = 1024 + 122626 from by norm_num, S_add, hQ204, b203, show 122626 = 1024 + 121602 from by norm_num, S_add, hQ205, b204, show 121602 = 1024 + 120578 from by norm_num, S_add, hQ206, b205, show 120578 = 1024 + 119554 from by norm_num, S_add, hQ207, b206, show 119554 = 1024 + 118530 from by norm_num, S_add, hQ208, b207, show 118530 = 1024 + 117506 from by norm_num, S_add, hQ209, b208, show 117506 = 1024 + 116482 from by norm_num, S_add, hQ210, b209, show 116482 = 1024 + 115458 from by norm_num, S_add, hQ211, b210, show 115458 = 1024 + 114434 from by norm_num, S_add, hQ212, b211, show 114434 = 1024 + 113410 from by norm_num, S_add, hQ213, b212, show 113410 = 1024 + 112386 from by norm_num, S_add, hQ214, b213, show 112386 = 1024 + 111362 from by norm_num, S_add, hQ215, b214, show 111362 = 1024 + 110338 from by norm_num, S_add, hQ216, b215, show 110338 = 1024 + 109314 from by norm_num, S_add, hQ217, b216, show 109314 = 1024 + 108290 from by norm_num, S_add, hQ218, b217, show 108290 = 1024 + 107266 from by norm_num, S_add, hQ219, b218, show 107266 = 1024 + 106242 from by norm_num, S_add, hQ220, b219, show 106242 = 1024 + 105218 from by norm_num, S_add, hQ221, b220, show 105218 = 1024 + 104194 from by norm_num, S_add, hQ222, b221, show 104194 = 1024 + 103170 from by norm_num, S_add, hQ223, b222, show 103170 = 1024 + 102146 from by norm_num, S_add, hQ224, b223, show 102146 = 1024 + 101122 from by norm_num, S_add, hQ225, b224, show 101122 = 1024 + 100098 from by norm_num, S_add, hQ226, b225, show 100098 = 1024 + 99074 from by norm_num, S_add, hQ227, b226, show 99074 = 1024 + 98050 from by norm_num, S_add, hQ228, b227, show 98050 = 1024 + 97026 from by norm_num, S_add, hQ229, b228, show 97026 = 1024 + 96002 from by norm_num, S_add, hQ230, b229, show 96002 = 1024 + 94978 from by norm_num, S_add, hQ231, b230, show 94978 = 1024 + 93954 from by norm_num, S_add, hQ232, b231, show 93954 = 1024 + 92930 from by norm_num, S_add, hQ233, b232, show 92930 = 1024 + 91906 from by norm_num, S_add, hQ234, b233, show 91906 = 1024 + 90882 from by norm_num, S_add, hQ235, b234, show 90882 = 1024 + 89858 from by norm_num, S_add, hQ236, b235, show 89858 = 1024 + 88834 from by norm_num, S_add, hQ237, b236, show 88834 = 1024 + 87810 from by norm_num, S_add, hQ238, b237, show 87810 = 1024 + 86786 from by norm_num, S_add, hQ239, b238, show 86786 = 1024 + 85762 from by norm_num, S_add, hQ240, b239, show 85762 = 1024 + 84738 from by norm_num, S_add, hQ241, b240, show 84738 = 1024 + 83714 from by norm_num, S_add, hQ242, b241, show 83714 = 1024 + 82690 from by norm_num, S_add, hQ243, b242, show 82690 = 1024 + 81666 from by norm_num, S_add, hQ244, b243, show 81666 = 1024 + 80642 from by norm_num, S_add, hQ245, b244, show 80642 = 1024 + 79618 from by norm_num, S_add, hQ246, b245, show 79618 = 1024 + 78594 from by norm_num, S_add, hQ247, b246, show 78594 = 1024 + 77570 from by norm_num, S_add, hQ248, b247, show 77570 = 1024 + 76546 from by norm_num, S_add, hQ249, b248, show 76546 = 1024 + 75522 from by norm_num, S_add, hQ250, b249, show 75522 = 1024 + 74498 from by norm_num, S_add, hQ251, b250, show 74498 = 1024 + 73474 from by norm_num, S_add, hQ252, b251, show 73474 = 1024 + 72450 from by norm_num, S_add, hQ253, b252, show 72450 = 1024 + 71426 from by norm_num, S_add, hQ254, b253, show 71426 = 1024 + 70402 from by norm_num, S_add, hQ255, b254, show 70402 = 1024 + 69378 from by norm_num, S_add, hQ256, b255, show 69378 = 1024 + 68354 from by norm_num, S_add, hQ257, b256, show 68354 = 1024 + 67330 from by norm_num, S_add, hQ258, b257, show 67330 = 1024 + 66306 from by norm_num, S_add, hQ259, b258, show 66306 = 1024 + 65282 from by norm_num, S_add, hQ260, b259, show 65282 = 1024 + 64258 from by norm_num, S_add, hQ261, b260, show 64258 = 1024 + 63234 from by norm_num, S_add, hQ262, b261, show 63234 = 1024 + 62210 from by norm_num, S_add, hQ263, b262, show 62210 = 1024 + 61186 from by norm_num, S_add, hQ264, b263, show 61186 = 1024 + 60162 from by norm_num, S_add, hQ265, b264, show 60162 = 1024 + 59138 from by norm_num, S_add, hQ266, b265, show 59138 = 1024 + 58114 from by norm_num, S_add, hQ267, b266, show 58114 = 1024 + 57090 from by norm_num, S_add, hQ268, b267, show 57090 = 1024 + 56066 from by norm_num, S_add, hQ269, b268, show 56066 = 1024 + 55042 from by norm_num, S_add, hQ270, b269, show 55042 = 1024 + 54018 from by norm_num, S_add, hQ271, b270, show 54018 = 1024 + 52994 from by norm_num, S_add, hQ272, b271, show 52994 = 1024 + 51970 from by norm_num, S_add, hQ273, b272, show 51970 = 1024 + 50946 from by norm_num, S_add, hQ274, b273, show 50946 = 1024 + 49922 from by norm_num, S_add, hQ275, b274, show 49922 = 1024 + 48898 from by norm_num, S_add, hQ276, b275, show 48898 = 1024 + 47874 from by norm_num, S_add, hQ277, b276, show 47874 = 1024 + 46850 from by norm_num, S_add, hQ278, b277, show 46850 = 1024 + 45826 from by norm_num, S_add, hQ279, b278, show 45826 = 1024 + 44802 from by norm_num, S_add, hQ280, b279, show 44802 = 1024 + 43778 from by norm_num, S_add, hQ281, b280, show 43778 = 1024 + 42754 from by norm_num, S_add, hQ282, b281, show 42754 = 1024 + 41730 from by norm_num, S_add, hQ283, b282, show 41730 = 1024 + 40706 from by norm_num, S_add, hQ284, b283, show 40706 = 1024 + 39682 from by norm_num, S_add, hQ285, b284, show 39682 = 1024 + 38658 from by norm_num, S_add, hQ286, b285, show 38658 = 1024 + 37634 from by norm_num, S_add, hQ287, b286, show 37634 = 1024 + 36610 from by norm_num, S_add, hQ288, b287, show 36610 = 1024 + 35586 from by norm_num, S_add, hQ289, b288, show 35586 = 1024 + 34562 from by norm_num, S_add, hQ290, b289, show 34562 = 1024 + 33538 from by norm_num, S_add, hQ291, b290, show 33538 = 1024 + 32514 from by norm_num, S_add, hQ292, b291, show 32514 = 1024 + 31490 from by norm_num, S_add, hQ293, b292, show 31490 = 1024 + 30466 from by norm_num, S_add, hQ294, b293, show 30466 = 1024 + 29442 from by norm_num, S_add, hQ295, b294, show 29442 = 1024 + 28418 from by norm_num, S_add, hQ296, b295, show 28418 = 1024 + 27394 from by norm_num, S_add, hQ297, b296, show 27394 = 1024 + 26370 from by norm_num, S_add, hQ298, b297, show 26370 = 1024 + 25346 from by norm_num, S_add, hQ299, b298, show 25346 = 1024 + 24322 from by norm_num, S_add, hQ300, b299, show 24322 = 1024 + 23298 from by norm_num, S_add, hQ301, b300, show 23298 = 1024 + 22274 from by norm_num, S_add, hQ302, b301, show 22274 = 1024 + 21250 from by norm_num, S_add, hQ303, b302, show 21250 = 1024 + 20226 from by norm_num, S_add, hQ304, b303, show 20226 = 1024 + 19202 from by norm_num, S_add, hQ305, b304, show 19202 = 1024 + 18178 from by norm_num, S_add, hQ306, b305, show 18178 = 1024 + 17154 from by norm_num, S_add, hQ307, b306, show 17154 = 1024 + 16130 from by norm_num, S_add, hQ308, b307, show 16130 = 1024 + 15106 from by norm_num, S_add, hQ309, b308, show 15106 = 1024 + 14082 from by norm_num, S_add, hQ310, b309, show 14082 = 1024 + 13058 from by norm_num, S_add, hQ311, b310, show 13058 = 1024 + 12034 from by norm_num, S_add, hQ312, b311, show 12034 = 1024 + 11010 from by norm_num, S_add, hQ313, b312, show 11010 = 1024 + 9986 from by norm_num, S_add, hQ314, b313, show 9986 = 1024 + 8962 from by norm_num, S_add, hQ315, b314, show 8962 = 1024 + 7938 from by norm_num, S_add, hQ316, b315, show 7938 = 1024 + 6914 from by norm_num, S_add, hQ317, b316, show 6914 = 1024 + 5890 from by norm_num, S_add, hQ318, b317, show 5890 = 1024 + 4866 from by norm_num, S_add, hQ319, b318, show 4866 = 1024 + 3842 from by norm_num, S_add, hQ320, b319, show 3842 = 1024 + 2818 from by norm_num, S_add, hQ321, b320, show 2818 = 1024 + 1794 from by norm_num, S_add, hQ322, b321, show 1794 = 1024 + 770 from by norm_num, S_add, hQ323, b322, b323]
      norm_num
    have hS := S_eq 331522 1 3 rfl (by omega)
    have h0 : OeisA71532.a 331522 = 0 := by
      rw [OeisA71532.a, ← hS, key]
      simp
    have hn := h 331522 (by norm_num)
    rw [h0] at hn
    exact absurd hn (by norm_num)
