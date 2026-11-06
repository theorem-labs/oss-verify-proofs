| YD1k.v donor line(s) | out line(s) | old | new | role | AD2j / source |
|---|---|---|---|---|---|
| 170 | 171 | `img_rd m 0x10568 0x1cccb /\ img_rd m 0x1cce0 0x20b40` | `img_rd m 0x10588 0x1cd70 /\ img_rd m 0x1cd85 0x20d00` | img_facts: the A1 regions before / after the owned cell "memory at address %p" (donor R_A1h / R_A1i; here R_A1j / R_A1k) [lo, hi) | AD2j R_A1j, R_A1k (one CImg chunk each) |
| 170 | 171 | `img_rd m 650920 650928 /\ img_rd m 665504 666336` | `img_rd m 660792 660800 /\ img_rd m 675360 676192` | img_facts: canary .got chunk [a, a+8), R_A3 [lo, hi) | AD2j R_A2h chunk (CImg 8), R_A3 |
| 173 | 174 | `IMG_REGIONS R_A1h 66920 51043 HM)` | `IMG_REGIONS R_A1j 66952 51176 HM)` | img_facts: img_rd_of_mem_ok on donor R_A1h (here R_A1j) lo len | AD2j R_A1j chunk |
| 174 | 175 | `IMG_REGIONS R_A1i 117984 15968 HM)` | `IMG_REGIONS R_A1k 118149 16251 HM)` | img_facts: img_rd_of_mem_ok on donor R_A1i (here R_A1k) lo len | AD2j R_A1k chunk |
| 176 | 177 | `IMG_REGIONS R_A3 665504 832 HM)` | `IMG_REGIONS R_A3 675360 832 HM)` | img_facts: img_rd_of_mem_ok on donor R_A3 (here R_A3) lo len | AD2j R_A3 chunk |
| 175 | 176 | `IMG_REGIONS R_A2e 650920 8 HM)` | `IMG_REGIONS R_A2h 660792 8 HM)` | img_facts: img_rd_of_mem_ok on the canary .got chunk (region name follows the table) | AD2j R_A2h chunk 660792 (CImg 8) |
| 178 | 179 | `mkChunk 6263376 (CVal 8 (SOff 41 0))` | `mkChunk 6276176 (CVal 8 (SOff 41 0))` | img_facts: the canary cell chunk of R_A7b | AD2j R_A7b chunk |
| 179 | 180 | `change A_canary with (0 + 6263376)` | `change A_canary with (0 + 6276176)` | img_facts: A_canary = that chunk's offset | AD2j R_A7b chunk |
| 180 | 181 | `E m 0 6263376 8 (SOff 41 0)` | `E m 0 6276176 8 (SOff 41 0)` | img_facts: val_of_chunk_ok at that chunk | AD2j R_A7b chunk |
| 268 | 314 | `IMG_REGIONS R_A1d 66352 104 HM` | `IMG_REGIONS R_A1e 66392 72 HM` | mconsts_of_IMG: the A1 region holding mconsts_view's 32 constant bytes (donor R_A1d; here R_A1e); MC_LO..MC_HI here 0x10368..0x10388 (must equal the relocated AE39 mc_bounds) | AD2j R_A1e chunk; the bytes of donor [0x10350, 0x10370) found once, at 0x10368 |
| 291,325 | 337,371 | `file_is_img _ 665504 666336)` | `file_is_img _ 675360 676192)` | fwrite/refused sites: R_A3 [lo, hi) | AD2j R_A3 |
| 248,249,250..262 | 249,250,251..308 | `15 CH alternatives (R_A1a .. R_A1o)` | `60 CH alternatives (R_A1a .. R_A1bh)` | ro_img_of_IMG: CH r lo len for every R_A1* region | AD2j R_A1* (one CImg chunk each) |
| 206,230 | 207,231 | `0x10000 (0x20dc8 - 0x10000)` | `0x10000 (0x20f98 - 0x10000)` | rodata_zero_shadow / rodata_shadow_facts: zero-shadow range | owned-static file Tfib_zero_shadow, first range |
| 209 | 210 | `(0x10000, 0x20dc8 - 0x10000)` | `(0x10000, 0x20f98 - 0x10000)` | rodata_zero_shadow: al_zshadow range | owned-static file Tfib_zero_shadow, first range |
| 212,226 | 213,227 | `0x10568 <= p -> p + n <= 0x20dc0` | `0x10588 <= p -> p + n <= 0x20f80` | rodata_hull_zero / rodata_shadow_facts: [lo of donor R_A1h (here R_A1j), first asan global beg) | AD2j R_A1j lo; asan_globals descriptor with the lowest beg |
| 217 | 218 | `assert (L1 : 0x10568 / 8` | `assert (L1 : 0x10588 / 8` | rodata_hull_zero: lo of donor R_A1h (here R_A1j) | AD2j R_A1j lo |
| 218 | 219 | `(0x20dc0 - 1) / 8) by` | `(0x20f80 - 1) / 8) by` | rodata_hull_zero: hull bound | first asan global beg |
| 219 | 220 | `change (0x10568 / 8) with 8365 in L1. change ((0x20dc0 - 1) / 8) with 16823 in L2.` | `change (0x10588 / 8) with 8369 in L1. change ((0x20f80 - 1) / 8) with 16879 in L2.` | rodata_hull_zero: the quotients | R_A1j lo / 8; (first global beg - 1) / 8 |
| 224 | 225 | `change ((134600 - 65536) / 8) with 8633.` | `change ((135064 - 65536) / 8) with 8691.` | rodata_hull_zero: zero-shadow range end and its granule count | Tfib_zero_shadow first range end |
| 134 | 135 | `STDOUT_BUFA = 6265120) by reflexivity` | `STDOUT_BUFA = 6277920) by reflexivity` | tfib_xst_frame: STDOUT_BUFA (restates AD1x/AE*; must equal the relocated value) | image word at __stdout_FILE+88 (FILE.buf) = buf+8 (0x5fcb18, 1032 bytes) |
| 134 | 135 | `F_STDOUT = 665816) by reflexivity` | `F_STDOUT = 675672) by reflexivity` | tfib_xst_frame: F_STDOUT (restates AD1x/AE*; must equal the relocated value) | twin __stdout_FILE = 0xa4f58 (232 bytes) |
| 278,319 | 324,365 | `F_STDERR = 0xa27e8) by reflexivity` | `F_STDERR = 0xa4e68) by reflexivity` | fwrite/refused sites: F_STDERR (restates AD1x/AE*; must equal the relocated value) | twin __stderr_FILE = 0xa4e68 (232 bytes) |

CH alternatives (ro_img_of_IMG), one per R_A1* region of the generated table, `CH name lo len` = its single CImg chunk:

| out line | region | chunk lo | chunk len |
|---|---|---|---|
| 249 | R_A1a | 65536 | 744 |
| 250 | R_A1b | 66288 | 24 |
| 251 | R_A1c | 66320 | 40 |
| 252 | R_A1d | 66368 | 16 |
| 253 | R_A1e | 66392 | 72 |
| 254 | R_A1f | 66472 | 8 |
| 255 | R_A1g | 66496 | 16 |
| 256 | R_A1h | 66520 | 112 |
| 257 | R_A1i | 66696 | 192 |
| 258 | R_A1j | 66952 | 51176 |
| 259 | R_A1k | 118149 | 16251 |
| 260 | R_A1l | 134404 | 666 |
| 261 | R_A1m | 135104 | 8 |
| 262 | R_A1n | 135136 | 6 |
| 263 | R_A1o | 135168 | 5 |
| 264 | R_A1p | 135200 | 6 |
| 265 | R_A1q | 135232 | 5 |
| 266 | R_A1r | 135264 | 4 |
| 267 | R_A1s | 135296 | 5 |
| 268 | R_A1t | 135328 | 6 |
| 269 | R_A1u | 135360 | 6 |
| 270 | R_A1v | 135392 | 6 |
| 271 | R_A1w | 135424 | 7 |
| 272 | R_A1x | 135456 | 10 |
| 273 | R_A1y | 135488 | 5 |
| 274 | R_A1z | 135520 | 4 |
| 275 | R_A1aa | 135552 | 7 |
| 276 | R_A1ab | 135584 | 39 |
| 277 | R_A1ac | 135648 | 7 |
| 278 | R_A1ad | 135680 | 8 |
| 279 | R_A1ae | 135712 | 5 |
| 280 | R_A1af | 135744 | 3 |
| 281 | R_A1ag | 135776 | 7 |
| 282 | R_A1ah | 135808 | 6 |
| 283 | R_A1ai | 135840 | 68 |
| 284 | R_A1aj | 135936 | 7 |
| 285 | R_A1ak | 135968 | 8 |
| 286 | R_A1al | 136000 | 2 |
| 287 | R_A1am | 136032 | 41 |
| 288 | R_A1an | 136128 | 2 |
| 289 | R_A1ao | 136160 | 1 |
| 290 | R_A1ap | 136192 | 13 |
| 291 | R_A1aq | 136224 | 14 |
| 292 | R_A1ar | 136256 | 17 |
| 293 | R_A1as | 136320 | 19 |
| 294 | R_A1at | 136384 | 15 |
| 295 | R_A1au | 136416 | 12 |
| 296 | R_A1av | 136448 | 5 |
| 297 | R_A1aw | 136480 | 6 |
| 298 | R_A1ax | 136512 | 16 |
| 299 | R_A1ay | 136544 | 2 |
| 300 | R_A1az | 136576 | 39 |
| 301 | R_A1ba | 136640 | 39 |
| 302 | R_A1bb | 136704 | 6 |
| 303 | R_A1bc | 136736 | 8 |
| 304 | R_A1bd | 136768 | 8 |
| 305 | R_A1be | 136800 | 44 |
| 306 | R_A1bf | 136864 | 1416 |
| 307 | R_A1bg | 138284 | 96 |
| 308 | R_A1bh | 138382 | 516978 |
