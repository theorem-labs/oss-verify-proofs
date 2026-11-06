| A/AD1k.v donor line(s) | out line(s) | old | new | role | AD2j / source |
|---|---|---|---|---|---|
| 171 | 172 | `img_rd m 0x10568 0x1cd09 /\ img_rd m 0x1cd1e 0x20b7c` | `img_rd m 0x10578 0x1ce78 /\ img_rd m 0x1ce8d 0x20cfc` | img_facts: R_A1h [lo, hi), R_A1i [lo, hi) | AD2j R_A1h, R_A1i (one CImg chunk each) |
| 171 | 172 | `img_rd m 650296 650304 /\ img_rd m 664880 665712` | `img_rd m 665176 665184 /\ img_rd m 679768 680608` | img_facts: canary .got chunk [a, a+8), R_A3 [lo, hi) | AD2j R_A2g chunk (CImg 8), R_A3 |
| 174 | 175 | `IMG_REGIONS R_A1h 66920 51105 HM)` | `IMG_REGIONS R_A1h 66936 51456 HM)` | img_facts: img_rd_of_mem_ok R_A1h lo len | AD2j R_A1h chunk |
| 175 | 176 | `IMG_REGIONS R_A1i 118046 15966 HM)` | `IMG_REGIONS R_A1i 118413 15983 HM)` | img_facts: img_rd_of_mem_ok R_A1i lo len | AD2j R_A1i chunk |
| 177 | 178 | `IMG_REGIONS R_A3 664880 832 HM)` | `IMG_REGIONS R_A3 679768 840 HM)` | img_facts: img_rd_of_mem_ok R_A3 lo len | AD2j R_A3 chunk |
| 176 | 177 | `IMG_REGIONS R_A2e 650296 8 HM)` | `IMG_REGIONS R_A2g 665176 8 HM)` | img_facts: img_rd_of_mem_ok on the canary .got chunk (region name follows the table) | AD2j R_A2g chunk 665176 (CImg 8) |
| 179 | 180 | `mkChunk 6262736 (CVal 8 (SOff 41 0))` | `mkChunk 6626384 (CVal 8 (SOff 41 0))` | img_facts: the canary cell chunk of R_A7b | AD2j R_A7b chunk |
| 180 | 181 | `change A_canary with (0 + 6262736)` | `change A_canary with (0 + 6626384)` | img_facts: A_canary = that chunk's offset | AD2j R_A7b chunk |
| 181 | 182 | `E m 0 6262736 8 (SOff 41 0)` | `E m 0 6626384 8 (SOff 41 0)` | img_facts: val_of_chunk_ok at that chunk | AD2j R_A7b chunk |
| 269 | 302 | `IMG_REGIONS R_A1d 66352 104 HM` | `IMG_REGIONS R_A1d 66368 112 HM` | mconsts_of_IMG: R_A1d lo len (the region holding the mconsts band, found by its bytes at 0x10360) | AD2j R_A1d chunk |
| 292,326 | 325,359 | `file_is_img _ 664880 665712)` | `file_is_img _ 679768 680608)` | fwrite/refused sites: R_A3 [lo, hi) | AD2j R_A3 |
| 249,250,251..263 | 250,251,252..296 | `15 CH alternatives (R_A1a .. R_A1o)` | `47 CH alternatives (R_A1a .. R_A1au)` | ro_img_of_IMG: CH r lo len for every CImg chunk of every R_A1* region | AD2j R_A1* chunks |
| 207,231 | 208,232 | `0x10000 (0x20e08 - 0x10000)` | `0x10000 (0x20fa0 - 0x10000)` | rodata_zero_shadow / rodata_shadow_facts: zero-shadow range | owned-static file Tfib_zero_shadow, first range |
| 210 | 211 | `(0x10000, 0x20e08 - 0x10000)` | `(0x10000, 0x20fa0 - 0x10000)` | rodata_zero_shadow: al_zshadow range | owned-static file Tfib_zero_shadow, first range |
| 213,227 | 214,228 | `0x10568 <= p -> p + n <= 0x20e00` | `0x10578 <= p -> p + n <= 0x20f80` | rodata_hull_zero / rodata_shadow_facts: [R_A1h lo, first asan global beg) | AD2j R_A1h lo; asan_globals descriptor with the lowest beg |
| 218 | 219 | `assert (L1 : 0x10568 / 8` | `assert (L1 : 0x10578 / 8` | rodata_hull_zero: R_A1h lo | AD2j R_A1h lo |
| 219 | 220 | `(0x20e00 - 1) / 8) by` | `(0x20f80 - 1) / 8) by` | rodata_hull_zero: hull bound | first asan global beg |
| 220 | 221 | `change (0x10568 / 8) with 8365 in L1. change ((0x20e00 - 1) / 8) with 16831 in L2.` | `change (0x10578 / 8) with 8367 in L1. change ((0x20f80 - 1) / 8) with 16879 in L2.` | rodata_hull_zero: the quotients | R_A1h lo / 8; (first global beg - 1) / 8 |
| 225 | 226 | `change ((134664 - 65536) / 8) with 8641.` | `change ((135072 - 65536) / 8) with 8692.` | rodata_hull_zero: zero-shadow range end and its granule count | Tfib_zero_shadow first range end |
| 135 | 136 | `STDOUT_BUFA = 6264480) by reflexivity` | `STDOUT_BUFA = 6628128) by reflexivity` | tfib_xst_frame: STDOUT_BUFA (restates AD1x/AE*; must equal gra-3's relocated value) | image word at __stdout_FILE+88 (FILE.buf) = buf+8 (0x652318, 1032 bytes) |
| 135 | 136 | `F_STDOUT = 665192) by reflexivity` | `F_STDOUT = 680080) by reflexivity` | tfib_xst_frame: F_STDOUT (restates AD1x/AE*; must equal gra-3's relocated value) | twin __stdout_FILE = 0xa6090 (232 bytes) |
| 279,320 | 312,353 | `F_STDERR = 0xa2578) by reflexivity` | `F_STDERR = 0xa5fa0) by reflexivity` | fwrite/refused sites: F_STDERR (restates AD1x/AE*; must equal gra-3's relocated value) | twin __stderr_FILE = 0xa5fa0 (232 bytes) |
| 164,187,189 | 165,188,190 | `TfibSyms` | `PcapSyms` | --rename (whole word, 3 occurrence(s) on 3 line(s)) | the unit's record / instance name |

CH alternatives (ro_img_of_IMG), one per CImg chunk of every R_A1* region of the generated table, `CH name lo len`:

| out line | region | chunk lo | chunk len |
|---|---|---|---|
| 250 | R_A1a | 65536 | 744 |
| 251 | R_A1b | 66288 | 24 |
| 252 | R_A1c | 66320 | 40 |
| 253 | R_A1d | 66368 | 112 |
| 254 | R_A1e | 66496 | 8 |
| 255 | R_A1f | 66512 | 104 |
| 256 | R_A1g | 66680 | 192 |
| 257 | R_A1h | 66936 | 51456 |
| 258 | R_A1i | 118413 | 15983 |
| 259 | R_A1j | 134400 | 677 |
| 260 | R_A1k | 135104 | 1 |
| 261 | R_A1l | 135136 | 12 |
| 262 | R_A1m | 135168 | 5 |
| 263 | R_A1n | 135200 | 6 |
| 264 | R_A1o | 135232 | 9 |
| 265 | R_A1p | 135264 | 6 |
| 266 | R_A1q | 135296 | 24 |
| 267 | R_A1r | 135360 | 2 |
| 268 | R_A1s | 135392 | 16 |
| 269 | R_A1t | 135424 | 15 |
| 270 | R_A1u | 135456 | 15 |
| 271 | R_A1v | 135488 | 11 |
| 272 | R_A1w | 135520 | 9 |
| 273 | R_A1x | 135552 | 16 |
| 274 | R_A1y | 135584 | 8 |
| 275 | R_A1z | 135616 | 5 |
| 276 | R_A1aa | 135648 | 5 |
| 277 | R_A1ab | 135680 | 6 |
| 278 | R_A1ac | 135712 | 4 |
| 279 | R_A1ad | 135744 | 3 |
| 280 | R_A1ae | 135776 | 2 |
| 281 | R_A1af | 135808 | 41 |
| 282 | R_A1ag | 135872 | 5 |
| 283 | R_A1ah | 135904 | 8 |
| 284 | R_A1ai | 135936 | 148 |
| 285 | R_A1aj | 136128 | 15 |
| 286 | R_A1ak | 136160 | 103 |
| 287 | R_A1al | 136320 | 35 |
| 288 | R_A1am | 136416 | 1 |
| 289 | R_A1an | 136448 | 118 |
| 290 | R_A1ao | 136608 | 122 |
| 291 | R_A1ap | 136768 | 8 |
| 292 | R_A1aq | 136800 | 13 |
| 293 | R_A1ar | 136832 | 3 |
| 294 | R_A1as | 136864 | 1416 |
| 295 | R_A1at | 138284 | 96 |
| 296 | R_A1au | 138382 | 521074 |
