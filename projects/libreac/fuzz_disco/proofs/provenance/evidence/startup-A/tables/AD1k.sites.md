| A/AD1k.v donor line(s) | out line(s) | old | new | role | AD2j / source |
|---|---|---|---|---|---|
| 171 | 172 | `img_rd m 0x10568 0x1cd09 /\ img_rd m 0x1cd1e 0x20b7c` | `img_rd m 0x10588 0x1cd68 /\ img_rd m 0x1cd7d 0x20cf8` | img_facts: R_A1h [lo, hi), R_A1i [lo, hi) | AD2j R_A1h, R_A1i (one CImg chunk each) |
| 171 | 172 | `img_rd m 650296 650304 /\ img_rd m 664880 665712` | `img_rd m 659864 659872 /\ img_rd m 674432 675264` | img_facts: canary .got chunk [a, a+8), R_A3 [lo, hi) | AD2j R_A2h chunk (CImg 8), R_A3 |
| 174 | 175 | `IMG_REGIONS R_A1h 66920 51105 HM)` | `IMG_REGIONS R_A1i 66952 51168 HM)` | img_facts: img_rd_of_mem_ok R_A1h lo len | AD2j R_A1h chunk |
| 175 | 176 | `IMG_REGIONS R_A1i 118046 15966 HM)` | `IMG_REGIONS R_A1j 118141 16251 HM)` | img_facts: img_rd_of_mem_ok R_A1i lo len | AD2j R_A1i chunk |
| 177 | 178 | `IMG_REGIONS R_A3 664880 832 HM)` | `IMG_REGIONS R_A3 674432 832 HM)` | img_facts: img_rd_of_mem_ok R_A3 lo len | AD2j R_A3 chunk |
| 176 | 177 | `IMG_REGIONS R_A2e 650296 8 HM)` | `IMG_REGIONS R_A2h 659864 8 HM)` | img_facts: img_rd_of_mem_ok on the canary .got chunk (region name follows the table) | AD2j R_A2h chunk 659864 (CImg 8) |
| 179 | 180 | `mkChunk 6262736 (CVal 8 (SOff 41 0))` | `mkChunk 6275216 (CVal 8 (SOff 41 0))` | img_facts: the canary cell chunk of R_A7b | AD2j R_A7b chunk |
| 180 | 181 | `change A_canary with (0 + 6262736)` | `change A_canary with (0 + 6275216)` | img_facts: A_canary = that chunk's offset | AD2j R_A7b chunk |
| 181 | 182 | `E m 0 6262736 8 (SOff 41 0)` | `E m 0 6275216 8 (SOff 41 0)` | img_facts: val_of_chunk_ok at that chunk | AD2j R_A7b chunk |
| 269 | 314 | `IMG_REGIONS R_A1d 66352 104 HM` | `IMG_REGIONS R_A1e 66392 88 HM` | mconsts_of_IMG: R_A1d lo len (the region holding the mconsts band, found by its bytes at 0x10368) | AD2j R_A1d chunk |
| 292,326 | 337,371 | `file_is_img _ 664880 665712)` | `file_is_img _ 674432 675264)` | fwrite/refused sites: R_A3 [lo, hi) | AD2j R_A3 |
| 249,250,251..263 | 250,251,252..308 | `15 CH alternatives (R_A1a .. R_A1o)` | `59 CH alternatives (R_A1a .. R_A1bg)` | ro_img_of_IMG: CH r lo len for every CImg chunk of every R_A1* region | AD2j R_A1* chunks |
| 207,231 | 208,232 | `0x10000 (0x20e08 - 0x10000)` | `0x10000 (0x20f98 - 0x10000)` | rodata_zero_shadow / rodata_shadow_facts: zero-shadow range | owned-static file Tfib_zero_shadow, first range |
| 210 | 211 | `(0x10000, 0x20e08 - 0x10000)` | `(0x10000, 0x20f98 - 0x10000)` | rodata_zero_shadow: al_zshadow range | owned-static file Tfib_zero_shadow, first range |
| 213,227 | 214,228 | `0x10568 <= p -> p + n <= 0x20e00` | `0x10588 <= p -> p + n <= 0x20f80` | rodata_hull_zero / rodata_shadow_facts: [R_A1h lo, first asan global beg) | AD2j R_A1h lo; asan_globals descriptor with the lowest beg |
| 218 | 219 | `assert (L1 : 0x10568 / 8` | `assert (L1 : 0x10588 / 8` | rodata_hull_zero: R_A1h lo | AD2j R_A1h lo |
| 219 | 220 | `(0x20e00 - 1) / 8) by` | `(0x20f80 - 1) / 8) by` | rodata_hull_zero: hull bound | first asan global beg |
| 220 | 221 | `change (0x10568 / 8) with 8365 in L1. change ((0x20e00 - 1) / 8) with 16831 in L2.` | `change (0x10588 / 8) with 8369 in L1. change ((0x20f80 - 1) / 8) with 16879 in L2.` | rodata_hull_zero: the quotients | R_A1h lo / 8; (first global beg - 1) / 8 |
| 225 | 226 | `change ((134664 - 65536) / 8) with 8641.` | `change ((135064 - 65536) / 8) with 8691.` | rodata_hull_zero: zero-shadow range end and its granule count | Tfib_zero_shadow first range end |
| 135 | 136 | `STDOUT_BUFA = 6264480) by reflexivity` | `STDOUT_BUFA = 6276960) by reflexivity` | tfib_xst_frame: STDOUT_BUFA (restates AD1x/AE*; must equal gra-3's relocated value) | image word at __stdout_FILE+88 (FILE.buf) = buf+8 (0x5fc758, 1032 bytes) |
| 135 | 136 | `F_STDOUT = 665192) by reflexivity` | `F_STDOUT = 674744) by reflexivity` | tfib_xst_frame: F_STDOUT (restates AD1x/AE*; must equal gra-3's relocated value) | twin __stdout_FILE = 0xa4bb8 (232 bytes) |
| 279,320 | 324,365 | `F_STDERR = 0xa2578) by reflexivity` | `F_STDERR = 0xa4ac8) by reflexivity` | fwrite/refused sites: F_STDERR (restates AD1x/AE*; must equal gra-3's relocated value) | twin __stderr_FILE = 0xa4ac8 (232 bytes) |

CH alternatives (ro_img_of_IMG), one per CImg chunk of every R_A1* region of the generated table, `CH name lo len`:

| out line | region | chunk lo | chunk len |
|---|---|---|---|
| 250 | R_A1a | 65536 | 744 |
| 251 | R_A1b | 66288 | 24 |
| 252 | R_A1c | 66320 | 40 |
| 253 | R_A1d | 66368 | 16 |
| 254 | R_A1e | 66392 | 88 |
| 255 | R_A1f | 66496 | 16 |
| 256 | R_A1g | 66520 | 112 |
| 257 | R_A1h | 66696 | 192 |
| 258 | R_A1i | 66952 | 51168 |
| 259 | R_A1j | 118141 | 16251 |
| 260 | R_A1k | 134396 | 674 |
| 261 | R_A1l | 135104 | 8 |
| 262 | R_A1m | 135136 | 6 |
| 263 | R_A1n | 135168 | 5 |
| 264 | R_A1o | 135200 | 6 |
| 265 | R_A1p | 135232 | 5 |
| 266 | R_A1q | 135264 | 4 |
| 267 | R_A1r | 135296 | 5 |
| 268 | R_A1s | 135328 | 6 |
| 269 | R_A1t | 135360 | 6 |
| 270 | R_A1u | 135392 | 6 |
| 271 | R_A1v | 135424 | 7 |
| 272 | R_A1w | 135456 | 10 |
| 273 | R_A1x | 135488 | 5 |
| 274 | R_A1y | 135520 | 4 |
| 275 | R_A1z | 135552 | 7 |
| 276 | R_A1aa | 135584 | 39 |
| 277 | R_A1ab | 135648 | 7 |
| 278 | R_A1ac | 135680 | 8 |
| 279 | R_A1ad | 135712 | 5 |
| 280 | R_A1ae | 135744 | 3 |
| 281 | R_A1af | 135776 | 7 |
| 282 | R_A1ag | 135808 | 6 |
| 283 | R_A1ah | 135840 | 68 |
| 284 | R_A1ai | 135936 | 7 |
| 285 | R_A1aj | 135968 | 8 |
| 286 | R_A1ak | 136000 | 2 |
| 287 | R_A1al | 136032 | 41 |
| 288 | R_A1am | 136128 | 2 |
| 289 | R_A1an | 136160 | 1 |
| 290 | R_A1ao | 136192 | 13 |
| 291 | R_A1ap | 136224 | 14 |
| 292 | R_A1aq | 136256 | 17 |
| 293 | R_A1ar | 136320 | 19 |
| 294 | R_A1as | 136384 | 15 |
| 295 | R_A1at | 136416 | 12 |
| 296 | R_A1au | 136448 | 5 |
| 297 | R_A1av | 136480 | 6 |
| 298 | R_A1aw | 136512 | 16 |
| 299 | R_A1ax | 136544 | 2 |
| 300 | R_A1ay | 136576 | 39 |
| 301 | R_A1az | 136640 | 39 |
| 302 | R_A1ba | 136704 | 6 |
| 303 | R_A1bb | 136736 | 8 |
| 304 | R_A1bc | 136768 | 8 |
| 305 | R_A1bd | 136800 | 44 |
| 306 | R_A1be | 136864 | 1416 |
| 307 | R_A1bf | 138284 | 96 |
| 308 | R_A1bg | 138382 | 512882 |
