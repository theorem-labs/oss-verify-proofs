(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From Ltac2 Require Import Ltac2.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExec2 SymExecFP.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Set Default Proof Mode "Classic".
Unset Lia Cache.

(* [comment removed for export] *)
Definition idn (n : nat) : nat := n.

(* [comment removed for export] *)
Definition vn0 : nat := 0.
Definition vn1 : nat := 1.
Definition vn2 : nat := 2.
Definition vn3 : nat := 3.
Definition vn4 : nat := 4.
Definition vn5 : nat := 5.
Definition vn6 : nat := 6.
Definition vn7 : nat := 7.
Definition vn8 : nat := 8.
Definition vn9 : nat := 9.
Definition vn10 : nat := 10.
Definition vn11 : nat := 11.
Definition vn12 : nat := 12.
Definition vn13 : nat := 13.
Definition vn14 : nat := 14.
Definition vn15 : nat := 15.
Definition vn16 : nat := 16.
Definition vn17 : nat := 17.
Definition vn18 : nat := 18.
Definition vn19 : nat := 19.
Definition vn20 : nat := 20.
Definition vn21 : nat := 21.
Definition vn22 : nat := 22.
Definition vn23 : nat := 23.
Definition vn24 : nat := 24.
Definition vn25 : nat := 25.
Definition vn26 : nat := 26.
Definition vn27 : nat := 27.
Definition vn28 : nat := 28.
Definition vn29 : nat := 29.
Definition vn30 : nat := 30.
Definition vn31 : nat := 31.
Definition vn32 : nat := 32.
Definition vn33 : nat := 33.
Definition vn34 : nat := 34.
Definition vn35 : nat := 35.
Definition vn36 : nat := 36.
Definition vn37 : nat := 37.
Definition vn38 : nat := 38.
Definition vn39 : nat := 39.
Definition vn40 : nat := 40.
Definition vn41 : nat := 41.
Definition vn42 : nat := 42.
Definition vn43 : nat := 43.
Definition vn44 : nat := 44.
Definition vn45 : nat := 45.
Definition vn46 : nat := 46.
Definition vn47 : nat := 47.
Definition vn48 : nat := 48.
Definition vn49 : nat := 49.
Definition vn50 : nat := 50.
Definition vn51 : nat := 51.
Definition vn52 : nat := 52.
Definition vn53 : nat := 53.
Definition vn54 : nat := 54.
Definition vn55 : nat := 55.
Definition vn56 : nat := 56.
Definition vn57 : nat := 57.
Definition vn58 : nat := 58.
Definition vn59 : nat := 59.
Definition vn60 : nat := 60.
Definition vn61 : nat := 61.
Definition vn62 : nat := 62.
Definition vn63 : nat := 63.
Definition vn64 : nat := 64.
Definition vn65 : nat := 65.
Definition vn66 : nat := 66.
Definition vn67 : nat := 67.
Definition vn68 : nat := 68.
Definition vn69 : nat := 69.
Definition vn70 : nat := 70.
Definition vn71 : nat := 71.
Definition vn72 : nat := 72.
Definition vn73 : nat := 73.
Definition vn74 : nat := 74.
Definition vn75 : nat := 75.
Definition vn76 : nat := 76.
Definition vn77 : nat := 77.
Definition vn78 : nat := 78.
Definition vn79 : nat := 79.
Definition vn80 : nat := 80.
Definition vn81 : nat := 81.
Definition vn82 : nat := 82.
Definition vn83 : nat := 83.
Definition vn84 : nat := 84.
Definition vn85 : nat := 85.
Definition vn86 : nat := 86.
Definition vn87 : nat := 87.
Definition vn88 : nat := 88.
Definition vn89 : nat := 89.
Definition vn90 : nat := 90.
Definition vn91 : nat := 91.
Definition vn92 : nat := 92.
Definition vn93 : nat := 93.
Definition vn94 : nat := 94.
Definition vn95 : nat := 95.
Definition vn96 : nat := 96.
Definition vn97 : nat := 97.
Definition vn98 : nat := 98.
Definition vn99 : nat := 99.
Definition vn100 : nat := 100.
Definition vn101 : nat := 101.
Definition vn102 : nat := 102.
Definition vn103 : nat := 103.
Definition vn104 : nat := 104.
Definition vn105 : nat := 105.
Definition vn106 : nat := 106.
Definition vn107 : nat := 107.
Definition vn108 : nat := 108.
Definition vn109 : nat := 109.
Definition vn110 : nat := 110.
Definition vn111 : nat := 111.
Definition vn112 : nat := 112.
Definition vn113 : nat := 113.
Definition vn114 : nat := 114.
Definition vn115 : nat := 115.
Definition vn116 : nat := 116.
Definition vn117 : nat := 117.
Definition vn118 : nat := 118.
Definition vn119 : nat := 119.
Definition vn120 : nat := 120.
Definition vn121 : nat := 121.
Definition vn122 : nat := 122.
Definition vn123 : nat := 123.
Definition vn124 : nat := 124.
Definition vn125 : nat := 125.
Definition vn126 : nat := 126.
Definition vn127 : nat := 127.
Definition vn128 : nat := 128.
Definition vn129 : nat := 129.
Definition vn130 : nat := 130.
Definition vn131 : nat := 131.
Definition vn132 : nat := 132.
Definition vn133 : nat := 133.
Definition vn134 : nat := 134.
Definition vn135 : nat := 135.
Definition vn136 : nat := 136.
Definition vn137 : nat := 137.
Definition vn138 : nat := 138.
Definition vn139 : nat := 139.
Definition vn140 : nat := 140.
Definition vn141 : nat := 141.
Definition vn142 : nat := 142.
Definition vn143 : nat := 143.
Definition vn144 : nat := 144.
Definition vn145 : nat := 145.
Definition vn146 : nat := 146.
Definition vn147 : nat := 147.
Definition vn148 : nat := 148.
Definition vn149 : nat := 149.
Definition vn150 : nat := 150.
Definition vn151 : nat := 151.
Definition vn152 : nat := 152.
Definition vn153 : nat := 153.
Definition vn154 : nat := 154.
Definition vn155 : nat := 155.
Definition vn156 : nat := 156.
Definition vn157 : nat := 157.
Definition vn158 : nat := 158.
Definition vn159 : nat := 159.
Definition vn160 : nat := 160.
Definition vn161 : nat := 161.
Definition vn162 : nat := 162.
Definition vn163 : nat := 163.
Definition vn164 : nat := 164.
Definition vn165 : nat := 165.
Definition vn166 : nat := 166.
Definition vn167 : nat := 167.
Definition vn168 : nat := 168.
Definition vn169 : nat := 169.
Definition vn170 : nat := 170.
Definition vn171 : nat := 171.
Definition vn172 : nat := 172.
Definition vn173 : nat := 173.
Definition vn174 : nat := 174.
Definition vn175 : nat := 175.
Definition vn176 : nat := 176.
Definition vn177 : nat := 177.
Definition vn178 : nat := 178.
Definition vn179 : nat := 179.
Definition vn180 : nat := 180.
Definition vn181 : nat := 181.
Definition vn182 : nat := 182.
Definition vn183 : nat := 183.
Definition vn184 : nat := 184.
Definition vn185 : nat := 185.
Definition vn186 : nat := 186.
Definition vn187 : nat := 187.
Definition vn188 : nat := 188.
Definition vn189 : nat := 189.
Definition vn190 : nat := 190.
Definition vn191 : nat := 191.
Definition vn192 : nat := 192.
Definition vn193 : nat := 193.
Definition vn194 : nat := 194.
Definition vn195 : nat := 195.
Definition vn196 : nat := 196.
Definition vn197 : nat := 197.
Definition vn198 : nat := 198.
Definition vn199 : nat := 199.
Definition vn200 : nat := 200.
Definition vn201 : nat := 201.
Definition vn202 : nat := 202.
Definition vn203 : nat := 203.
Definition vn204 : nat := 204.
Definition vn205 : nat := 205.
Definition vn206 : nat := 206.
Definition vn207 : nat := 207.
Definition vn208 : nat := 208.
Definition vn209 : nat := 209.
Definition vn210 : nat := 210.
Definition vn211 : nat := 211.
Definition vn212 : nat := 212.
Definition vn213 : nat := 213.
Definition vn214 : nat := 214.
Definition vn215 : nat := 215.
Definition vn216 : nat := 216.
Definition vn217 : nat := 217.
Definition vn218 : nat := 218.
Definition vn219 : nat := 219.
Definition vn220 : nat := 220.
Definition vn221 : nat := 221.
Definition vn222 : nat := 222.
Definition vn223 : nat := 223.
Definition vn224 : nat := 224.
Definition vn225 : nat := 225.
Definition vn226 : nat := 226.
Definition vn227 : nat := 227.
Definition vn228 : nat := 228.
Definition vn229 : nat := 229.
Definition vn230 : nat := 230.
Definition vn231 : nat := 231.
Definition vn232 : nat := 232.
Definition vn233 : nat := 233.
Definition vn234 : nat := 234.
Definition vn235 : nat := 235.
Definition vn236 : nat := 236.
Definition vn237 : nat := 237.
Definition vn238 : nat := 238.
Definition vn239 : nat := 239.
Definition vn240 : nat := 240.
Definition vn241 : nat := 241.
Definition vn242 : nat := 242.
Definition vn243 : nat := 243.
Definition vn244 : nat := 244.
Definition vn245 : nat := 245.
Definition vn246 : nat := 246.
Definition vn247 : nat := 247.
Definition vn248 : nat := 248.
Definition vn249 : nat := 249.
Definition vn250 : nat := 250.
Definition vn251 : nat := 251.
Definition vn252 : nat := 252.
Definition vn253 : nat := 253.
Definition vn254 : nat := 254.
Definition vn255 : nat := 255.
Definition vn256 : nat := 256.
Definition vn257 : nat := 257.
Definition vn258 : nat := 258.
Definition vn259 : nat := 259.
Definition vn260 : nat := 260.
Definition vn261 : nat := 261.
Definition vn262 : nat := 262.
Definition vn263 : nat := 263.
Definition vn264 : nat := 264.
Definition vn265 : nat := 265.
Definition vn266 : nat := 266.
Definition vn267 : nat := 267.
Definition vn268 : nat := 268.
Definition vn269 : nat := 269.
Definition vn270 : nat := 270.
Definition vn271 : nat := 271.
Definition vn272 : nat := 272.
Definition vn273 : nat := 273.
Definition vn274 : nat := 274.
Definition vn275 : nat := 275.
Definition vn276 : nat := 276.
Definition vn277 : nat := 277.
Definition vn278 : nat := 278.
Definition vn279 : nat := 279.
Definition vn280 : nat := 280.
Definition vn281 : nat := 281.
Definition vn282 : nat := 282.
Definition vn283 : nat := 283.
Definition vn284 : nat := 284.
Definition vn285 : nat := 285.
Definition vn286 : nat := 286.
Definition vn287 : nat := 287.
Definition vn288 : nat := 288.
Definition vn289 : nat := 289.
Definition vn290 : nat := 290.
Definition vn291 : nat := 291.
Definition vn292 : nat := 292.
Definition vn293 : nat := 293.
Definition vn294 : nat := 294.
Definition vn295 : nat := 295.
Definition vn296 : nat := 296.
Definition vn297 : nat := 297.
Definition vn298 : nat := 298.
Definition vn299 : nat := 299.
Definition vn300 : nat := 300.
Definition vn301 : nat := 301.
Definition vn302 : nat := 302.
Definition vn303 : nat := 303.
Definition vn304 : nat := 304.
Definition vn305 : nat := 305.
Definition vn306 : nat := 306.
Definition vn307 : nat := 307.
Definition vn308 : nat := 308.
Definition vn309 : nat := 309.
Definition vn310 : nat := 310.
Definition vn311 : nat := 311.
Definition vn312 : nat := 312.
Definition vn313 : nat := 313.
Definition vn314 : nat := 314.
Definition vn315 : nat := 315.
Definition vn316 : nat := 316.
Definition vn317 : nat := 317.
Definition vn318 : nat := 318.
Definition vn319 : nat := 319.
Definition vn320 : nat := 320.
Definition vn321 : nat := 321.
Definition vn322 : nat := 322.
Definition vn323 : nat := 323.
Definition vn324 : nat := 324.
Definition vn325 : nat := 325.
Definition vn326 : nat := 326.
Definition vn327 : nat := 327.
Definition vn328 : nat := 328.
Definition vn329 : nat := 329.
Definition vn330 : nat := 330.
Definition vn331 : nat := 331.
Definition vn332 : nat := 332.
Definition vn333 : nat := 333.
Definition vn334 : nat := 334.
Definition vn335 : nat := 335.
Definition vn336 : nat := 336.
Definition vn337 : nat := 337.
Definition vn338 : nat := 338.
Definition vn339 : nat := 339.
Definition vn340 : nat := 340.
Definition vn341 : nat := 341.
Definition vn342 : nat := 342.
Definition vn343 : nat := 343.
Definition vn344 : nat := 344.
Definition vn345 : nat := 345.
Definition vn346 : nat := 346.
Definition vn347 : nat := 347.
Definition vn348 : nat := 348.
Definition vn349 : nat := 349.
Definition vn350 : nat := 350.
Definition vn351 : nat := 351.
Definition vn352 : nat := 352.
Definition vn353 : nat := 353.
Definition vn354 : nat := 354.
Definition vn355 : nat := 355.
Definition vn356 : nat := 356.
Definition vn357 : nat := 357.
Definition vn358 : nat := 358.
Definition vn359 : nat := 359.
Definition vn360 : nat := 360.
Definition vn361 : nat := 361.
Definition vn362 : nat := 362.
Definition vn363 : nat := 363.
Definition vn364 : nat := 364.
Definition vn365 : nat := 365.
Definition vn366 : nat := 366.
Definition vn367 : nat := 367.
Definition vn368 : nat := 368.
Definition vn369 : nat := 369.
Definition vn370 : nat := 370.
Definition vn371 : nat := 371.
Definition vn372 : nat := 372.
Definition vn373 : nat := 373.
Definition vn374 : nat := 374.
Definition vn375 : nat := 375.
Definition vn376 : nat := 376.
Definition vn377 : nat := 377.
Definition vn378 : nat := 378.
Definition vn379 : nat := 379.
Definition vn380 : nat := 380.
Definition vn381 : nat := 381.
Definition vn382 : nat := 382.
Definition vn383 : nat := 383.
Definition vn384 : nat := 384.
Definition vn385 : nat := 385.
Definition vn386 : nat := 386.
Definition vn387 : nat := 387.
Definition vn388 : nat := 388.
Definition vn389 : nat := 389.
Definition vn390 : nat := 390.
Definition vn391 : nat := 391.
Definition vn392 : nat := 392.
Definition vn393 : nat := 393.
Definition vn394 : nat := 394.
Definition vn395 : nat := 395.
Definition vn396 : nat := 396.
Definition vn397 : nat := 397.
Definition vn398 : nat := 398.
Definition vn399 : nat := 399.
Definition vn400 : nat := 400.
Definition vn401 : nat := 401.
Definition vn402 : nat := 402.
Definition vn403 : nat := 403.
Definition vn404 : nat := 404.
Definition vn405 : nat := 405.
Definition vn406 : nat := 406.
Definition vn407 : nat := 407.
Definition vn408 : nat := 408.
Definition vn409 : nat := 409.
Definition vn410 : nat := 410.
Definition vn411 : nat := 411.
Definition vn412 : nat := 412.
Definition vn413 : nat := 413.
Definition vn414 : nat := 414.
Definition vn415 : nat := 415.
Definition vn416 : nat := 416.
Definition vn417 : nat := 417.
Definition vn418 : nat := 418.
Definition vn419 : nat := 419.
Definition vn420 : nat := 420.
Definition vn421 : nat := 421.
Definition vn422 : nat := 422.
Definition vn423 : nat := 423.
Definition vn424 : nat := 424.
Definition vn425 : nat := 425.
Definition vn426 : nat := 426.
Definition vn427 : nat := 427.
Definition vn428 : nat := 428.
Definition vn429 : nat := 429.
Definition vn430 : nat := 430.
Definition vn431 : nat := 431.
Definition vn432 : nat := 432.
Definition vn433 : nat := 433.
Definition vn434 : nat := 434.
Definition vn435 : nat := 435.
Definition vn436 : nat := 436.
Definition vn437 : nat := 437.
Definition vn438 : nat := 438.
Definition vn439 : nat := 439.
Definition vn440 : nat := 440.
Definition vn441 : nat := 441.
Definition vn442 : nat := 442.
Definition vn443 : nat := 443.
Definition vn444 : nat := 444.
Definition vn445 : nat := 445.
Definition vn446 : nat := 446.
Definition vn447 : nat := 447.
Definition vn448 : nat := 448.
Definition vn449 : nat := 449.
Definition vn450 : nat := 450.
Definition vn451 : nat := 451.
Definition vn452 : nat := 452.
Definition vn453 : nat := 453.
Definition vn454 : nat := 454.
Definition vn455 : nat := 455.
Definition vn456 : nat := 456.
Definition vn457 : nat := 457.
Definition vn458 : nat := 458.
Definition vn459 : nat := 459.
Definition vn460 : nat := 460.
Definition vn461 : nat := 461.
Definition vn462 : nat := 462.
Definition vn463 : nat := 463.
Definition vn464 : nat := 464.
Definition vn465 : nat := 465.
Definition vn466 : nat := 466.
Definition vn467 : nat := 467.
Definition vn468 : nat := 468.
Definition vn469 : nat := 469.
Definition vn470 : nat := 470.
Definition vn471 : nat := 471.
Definition vn472 : nat := 472.
Definition vn473 : nat := 473.
Definition vn474 : nat := 474.
Definition vn475 : nat := 475.
Definition vn476 : nat := 476.
Definition vn477 : nat := 477.
Definition vn478 : nat := 478.
Definition vn479 : nat := 479.
Definition vn480 : nat := 480.
Definition vn481 : nat := 481.
Definition vn482 : nat := 482.
Definition vn483 : nat := 483.
Definition vn484 : nat := 484.
Definition vn485 : nat := 485.
Definition vn486 : nat := 486.
Definition vn487 : nat := 487.
Definition vn488 : nat := 488.
Definition vn489 : nat := 489.
Definition vn490 : nat := 490.
Definition vn491 : nat := 491.
Definition vn492 : nat := 492.
Definition vn493 : nat := 493.
Definition vn494 : nat := 494.
Definition vn495 : nat := 495.
Definition vn496 : nat := 496.
Definition vn497 : nat := 497.
Definition vn498 : nat := 498.
Definition vn499 : nat := 499.
Definition vn500 : nat := 500.
Definition vn501 : nat := 501.
Definition vn502 : nat := 502.
Definition vn503 : nat := 503.
Definition vn504 : nat := 504.
Definition vn505 : nat := 505.
Definition vn506 : nat := 506.
Definition vn507 : nat := 507.
Definition vn508 : nat := 508.
Definition vn509 : nat := 509.
Definition vn510 : nat := 510.
Definition vn511 : nat := 511.

(* [comment removed for export] *)
Ltac2 vn_of (k : int) : constr :=
  if Int.lt k 256 then
    if Int.lt k 128 then
      if Int.lt k 64 then
        if Int.lt k 32 then
          if Int.lt k 16 then
            if Int.lt k 8 then
              if Int.equal k 0 then constr:(vn0) else
              if Int.equal k 1 then constr:(vn1) else
              if Int.equal k 2 then constr:(vn2) else
              if Int.equal k 3 then constr:(vn3) else
              if Int.equal k 4 then constr:(vn4) else
              if Int.equal k 5 then constr:(vn5) else
              if Int.equal k 6 then constr:(vn6) else
              if Int.equal k 7 then constr:(vn7) else
              constr:(O)
            else
              if Int.equal k 8 then constr:(vn8) else
              if Int.equal k 9 then constr:(vn9) else
              if Int.equal k 10 then constr:(vn10) else
              if Int.equal k 11 then constr:(vn11) else
              if Int.equal k 12 then constr:(vn12) else
              if Int.equal k 13 then constr:(vn13) else
              if Int.equal k 14 then constr:(vn14) else
              if Int.equal k 15 then constr:(vn15) else
              constr:(O)
          else
            if Int.lt k 24 then
              if Int.equal k 16 then constr:(vn16) else
              if Int.equal k 17 then constr:(vn17) else
              if Int.equal k 18 then constr:(vn18) else
              if Int.equal k 19 then constr:(vn19) else
              if Int.equal k 20 then constr:(vn20) else
              if Int.equal k 21 then constr:(vn21) else
              if Int.equal k 22 then constr:(vn22) else
              if Int.equal k 23 then constr:(vn23) else
              constr:(O)
            else
              if Int.equal k 24 then constr:(vn24) else
              if Int.equal k 25 then constr:(vn25) else
              if Int.equal k 26 then constr:(vn26) else
              if Int.equal k 27 then constr:(vn27) else
              if Int.equal k 28 then constr:(vn28) else
              if Int.equal k 29 then constr:(vn29) else
              if Int.equal k 30 then constr:(vn30) else
              if Int.equal k 31 then constr:(vn31) else
              constr:(O)
        else
          if Int.lt k 48 then
            if Int.lt k 40 then
              if Int.equal k 32 then constr:(vn32) else
              if Int.equal k 33 then constr:(vn33) else
              if Int.equal k 34 then constr:(vn34) else
              if Int.equal k 35 then constr:(vn35) else
              if Int.equal k 36 then constr:(vn36) else
              if Int.equal k 37 then constr:(vn37) else
              if Int.equal k 38 then constr:(vn38) else
              if Int.equal k 39 then constr:(vn39) else
              constr:(O)
            else
              if Int.equal k 40 then constr:(vn40) else
              if Int.equal k 41 then constr:(vn41) else
              if Int.equal k 42 then constr:(vn42) else
              if Int.equal k 43 then constr:(vn43) else
              if Int.equal k 44 then constr:(vn44) else
              if Int.equal k 45 then constr:(vn45) else
              if Int.equal k 46 then constr:(vn46) else
              if Int.equal k 47 then constr:(vn47) else
              constr:(O)
          else
            if Int.lt k 56 then
              if Int.equal k 48 then constr:(vn48) else
              if Int.equal k 49 then constr:(vn49) else
              if Int.equal k 50 then constr:(vn50) else
              if Int.equal k 51 then constr:(vn51) else
              if Int.equal k 52 then constr:(vn52) else
              if Int.equal k 53 then constr:(vn53) else
              if Int.equal k 54 then constr:(vn54) else
              if Int.equal k 55 then constr:(vn55) else
              constr:(O)
            else
              if Int.equal k 56 then constr:(vn56) else
              if Int.equal k 57 then constr:(vn57) else
              if Int.equal k 58 then constr:(vn58) else
              if Int.equal k 59 then constr:(vn59) else
              if Int.equal k 60 then constr:(vn60) else
              if Int.equal k 61 then constr:(vn61) else
              if Int.equal k 62 then constr:(vn62) else
              if Int.equal k 63 then constr:(vn63) else
              constr:(O)
      else
        if Int.lt k 96 then
          if Int.lt k 80 then
            if Int.lt k 72 then
              if Int.equal k 64 then constr:(vn64) else
              if Int.equal k 65 then constr:(vn65) else
              if Int.equal k 66 then constr:(vn66) else
              if Int.equal k 67 then constr:(vn67) else
              if Int.equal k 68 then constr:(vn68) else
              if Int.equal k 69 then constr:(vn69) else
              if Int.equal k 70 then constr:(vn70) else
              if Int.equal k 71 then constr:(vn71) else
              constr:(O)
            else
              if Int.equal k 72 then constr:(vn72) else
              if Int.equal k 73 then constr:(vn73) else
              if Int.equal k 74 then constr:(vn74) else
              if Int.equal k 75 then constr:(vn75) else
              if Int.equal k 76 then constr:(vn76) else
              if Int.equal k 77 then constr:(vn77) else
              if Int.equal k 78 then constr:(vn78) else
              if Int.equal k 79 then constr:(vn79) else
              constr:(O)
          else
            if Int.lt k 88 then
              if Int.equal k 80 then constr:(vn80) else
              if Int.equal k 81 then constr:(vn81) else
              if Int.equal k 82 then constr:(vn82) else
              if Int.equal k 83 then constr:(vn83) else
              if Int.equal k 84 then constr:(vn84) else
              if Int.equal k 85 then constr:(vn85) else
              if Int.equal k 86 then constr:(vn86) else
              if Int.equal k 87 then constr:(vn87) else
              constr:(O)
            else
              if Int.equal k 88 then constr:(vn88) else
              if Int.equal k 89 then constr:(vn89) else
              if Int.equal k 90 then constr:(vn90) else
              if Int.equal k 91 then constr:(vn91) else
              if Int.equal k 92 then constr:(vn92) else
              if Int.equal k 93 then constr:(vn93) else
              if Int.equal k 94 then constr:(vn94) else
              if Int.equal k 95 then constr:(vn95) else
              constr:(O)
        else
          if Int.lt k 112 then
            if Int.lt k 104 then
              if Int.equal k 96 then constr:(vn96) else
              if Int.equal k 97 then constr:(vn97) else
              if Int.equal k 98 then constr:(vn98) else
              if Int.equal k 99 then constr:(vn99) else
              if Int.equal k 100 then constr:(vn100) else
              if Int.equal k 101 then constr:(vn101) else
              if Int.equal k 102 then constr:(vn102) else
              if Int.equal k 103 then constr:(vn103) else
              constr:(O)
            else
              if Int.equal k 104 then constr:(vn104) else
              if Int.equal k 105 then constr:(vn105) else
              if Int.equal k 106 then constr:(vn106) else
              if Int.equal k 107 then constr:(vn107) else
              if Int.equal k 108 then constr:(vn108) else
              if Int.equal k 109 then constr:(vn109) else
              if Int.equal k 110 then constr:(vn110) else
              if Int.equal k 111 then constr:(vn111) else
              constr:(O)
          else
            if Int.lt k 120 then
              if Int.equal k 112 then constr:(vn112) else
              if Int.equal k 113 then constr:(vn113) else
              if Int.equal k 114 then constr:(vn114) else
              if Int.equal k 115 then constr:(vn115) else
              if Int.equal k 116 then constr:(vn116) else
              if Int.equal k 117 then constr:(vn117) else
              if Int.equal k 118 then constr:(vn118) else
              if Int.equal k 119 then constr:(vn119) else
              constr:(O)
            else
              if Int.equal k 120 then constr:(vn120) else
              if Int.equal k 121 then constr:(vn121) else
              if Int.equal k 122 then constr:(vn122) else
              if Int.equal k 123 then constr:(vn123) else
              if Int.equal k 124 then constr:(vn124) else
              if Int.equal k 125 then constr:(vn125) else
              if Int.equal k 126 then constr:(vn126) else
              if Int.equal k 127 then constr:(vn127) else
              constr:(O)
    else
      if Int.lt k 192 then
        if Int.lt k 160 then
          if Int.lt k 144 then
            if Int.lt k 136 then
              if Int.equal k 128 then constr:(vn128) else
              if Int.equal k 129 then constr:(vn129) else
              if Int.equal k 130 then constr:(vn130) else
              if Int.equal k 131 then constr:(vn131) else
              if Int.equal k 132 then constr:(vn132) else
              if Int.equal k 133 then constr:(vn133) else
              if Int.equal k 134 then constr:(vn134) else
              if Int.equal k 135 then constr:(vn135) else
              constr:(O)
            else
              if Int.equal k 136 then constr:(vn136) else
              if Int.equal k 137 then constr:(vn137) else
              if Int.equal k 138 then constr:(vn138) else
              if Int.equal k 139 then constr:(vn139) else
              if Int.equal k 140 then constr:(vn140) else
              if Int.equal k 141 then constr:(vn141) else
              if Int.equal k 142 then constr:(vn142) else
              if Int.equal k 143 then constr:(vn143) else
              constr:(O)
          else
            if Int.lt k 152 then
              if Int.equal k 144 then constr:(vn144) else
              if Int.equal k 145 then constr:(vn145) else
              if Int.equal k 146 then constr:(vn146) else
              if Int.equal k 147 then constr:(vn147) else
              if Int.equal k 148 then constr:(vn148) else
              if Int.equal k 149 then constr:(vn149) else
              if Int.equal k 150 then constr:(vn150) else
              if Int.equal k 151 then constr:(vn151) else
              constr:(O)
            else
              if Int.equal k 152 then constr:(vn152) else
              if Int.equal k 153 then constr:(vn153) else
              if Int.equal k 154 then constr:(vn154) else
              if Int.equal k 155 then constr:(vn155) else
              if Int.equal k 156 then constr:(vn156) else
              if Int.equal k 157 then constr:(vn157) else
              if Int.equal k 158 then constr:(vn158) else
              if Int.equal k 159 then constr:(vn159) else
              constr:(O)
        else
          if Int.lt k 176 then
            if Int.lt k 168 then
              if Int.equal k 160 then constr:(vn160) else
              if Int.equal k 161 then constr:(vn161) else
              if Int.equal k 162 then constr:(vn162) else
              if Int.equal k 163 then constr:(vn163) else
              if Int.equal k 164 then constr:(vn164) else
              if Int.equal k 165 then constr:(vn165) else
              if Int.equal k 166 then constr:(vn166) else
              if Int.equal k 167 then constr:(vn167) else
              constr:(O)
            else
              if Int.equal k 168 then constr:(vn168) else
              if Int.equal k 169 then constr:(vn169) else
              if Int.equal k 170 then constr:(vn170) else
              if Int.equal k 171 then constr:(vn171) else
              if Int.equal k 172 then constr:(vn172) else
              if Int.equal k 173 then constr:(vn173) else
              if Int.equal k 174 then constr:(vn174) else
              if Int.equal k 175 then constr:(vn175) else
              constr:(O)
          else
            if Int.lt k 184 then
              if Int.equal k 176 then constr:(vn176) else
              if Int.equal k 177 then constr:(vn177) else
              if Int.equal k 178 then constr:(vn178) else
              if Int.equal k 179 then constr:(vn179) else
              if Int.equal k 180 then constr:(vn180) else
              if Int.equal k 181 then constr:(vn181) else
              if Int.equal k 182 then constr:(vn182) else
              if Int.equal k 183 then constr:(vn183) else
              constr:(O)
            else
              if Int.equal k 184 then constr:(vn184) else
              if Int.equal k 185 then constr:(vn185) else
              if Int.equal k 186 then constr:(vn186) else
              if Int.equal k 187 then constr:(vn187) else
              if Int.equal k 188 then constr:(vn188) else
              if Int.equal k 189 then constr:(vn189) else
              if Int.equal k 190 then constr:(vn190) else
              if Int.equal k 191 then constr:(vn191) else
              constr:(O)
      else
        if Int.lt k 224 then
          if Int.lt k 208 then
            if Int.lt k 200 then
              if Int.equal k 192 then constr:(vn192) else
              if Int.equal k 193 then constr:(vn193) else
              if Int.equal k 194 then constr:(vn194) else
              if Int.equal k 195 then constr:(vn195) else
              if Int.equal k 196 then constr:(vn196) else
              if Int.equal k 197 then constr:(vn197) else
              if Int.equal k 198 then constr:(vn198) else
              if Int.equal k 199 then constr:(vn199) else
              constr:(O)
            else
              if Int.equal k 200 then constr:(vn200) else
              if Int.equal k 201 then constr:(vn201) else
              if Int.equal k 202 then constr:(vn202) else
              if Int.equal k 203 then constr:(vn203) else
              if Int.equal k 204 then constr:(vn204) else
              if Int.equal k 205 then constr:(vn205) else
              if Int.equal k 206 then constr:(vn206) else
              if Int.equal k 207 then constr:(vn207) else
              constr:(O)
          else
            if Int.lt k 216 then
              if Int.equal k 208 then constr:(vn208) else
              if Int.equal k 209 then constr:(vn209) else
              if Int.equal k 210 then constr:(vn210) else
              if Int.equal k 211 then constr:(vn211) else
              if Int.equal k 212 then constr:(vn212) else
              if Int.equal k 213 then constr:(vn213) else
              if Int.equal k 214 then constr:(vn214) else
              if Int.equal k 215 then constr:(vn215) else
              constr:(O)
            else
              if Int.equal k 216 then constr:(vn216) else
              if Int.equal k 217 then constr:(vn217) else
              if Int.equal k 218 then constr:(vn218) else
              if Int.equal k 219 then constr:(vn219) else
              if Int.equal k 220 then constr:(vn220) else
              if Int.equal k 221 then constr:(vn221) else
              if Int.equal k 222 then constr:(vn222) else
              if Int.equal k 223 then constr:(vn223) else
              constr:(O)
        else
          if Int.lt k 240 then
            if Int.lt k 232 then
              if Int.equal k 224 then constr:(vn224) else
              if Int.equal k 225 then constr:(vn225) else
              if Int.equal k 226 then constr:(vn226) else
              if Int.equal k 227 then constr:(vn227) else
              if Int.equal k 228 then constr:(vn228) else
              if Int.equal k 229 then constr:(vn229) else
              if Int.equal k 230 then constr:(vn230) else
              if Int.equal k 231 then constr:(vn231) else
              constr:(O)
            else
              if Int.equal k 232 then constr:(vn232) else
              if Int.equal k 233 then constr:(vn233) else
              if Int.equal k 234 then constr:(vn234) else
              if Int.equal k 235 then constr:(vn235) else
              if Int.equal k 236 then constr:(vn236) else
              if Int.equal k 237 then constr:(vn237) else
              if Int.equal k 238 then constr:(vn238) else
              if Int.equal k 239 then constr:(vn239) else
              constr:(O)
          else
            if Int.lt k 248 then
              if Int.equal k 240 then constr:(vn240) else
              if Int.equal k 241 then constr:(vn241) else
              if Int.equal k 242 then constr:(vn242) else
              if Int.equal k 243 then constr:(vn243) else
              if Int.equal k 244 then constr:(vn244) else
              if Int.equal k 245 then constr:(vn245) else
              if Int.equal k 246 then constr:(vn246) else
              if Int.equal k 247 then constr:(vn247) else
              constr:(O)
            else
              if Int.equal k 248 then constr:(vn248) else
              if Int.equal k 249 then constr:(vn249) else
              if Int.equal k 250 then constr:(vn250) else
              if Int.equal k 251 then constr:(vn251) else
              if Int.equal k 252 then constr:(vn252) else
              if Int.equal k 253 then constr:(vn253) else
              if Int.equal k 254 then constr:(vn254) else
              if Int.equal k 255 then constr:(vn255) else
              constr:(O)
  else
    if Int.lt k 384 then
      if Int.lt k 320 then
        if Int.lt k 288 then
          if Int.lt k 272 then
            if Int.lt k 264 then
              if Int.equal k 256 then constr:(vn256) else
              if Int.equal k 257 then constr:(vn257) else
              if Int.equal k 258 then constr:(vn258) else
              if Int.equal k 259 then constr:(vn259) else
              if Int.equal k 260 then constr:(vn260) else
              if Int.equal k 261 then constr:(vn261) else
              if Int.equal k 262 then constr:(vn262) else
              if Int.equal k 263 then constr:(vn263) else
              constr:(O)
            else
              if Int.equal k 264 then constr:(vn264) else
              if Int.equal k 265 then constr:(vn265) else
              if Int.equal k 266 then constr:(vn266) else
              if Int.equal k 267 then constr:(vn267) else
              if Int.equal k 268 then constr:(vn268) else
              if Int.equal k 269 then constr:(vn269) else
              if Int.equal k 270 then constr:(vn270) else
              if Int.equal k 271 then constr:(vn271) else
              constr:(O)
          else
            if Int.lt k 280 then
              if Int.equal k 272 then constr:(vn272) else
              if Int.equal k 273 then constr:(vn273) else
              if Int.equal k 274 then constr:(vn274) else
              if Int.equal k 275 then constr:(vn275) else
              if Int.equal k 276 then constr:(vn276) else
              if Int.equal k 277 then constr:(vn277) else
              if Int.equal k 278 then constr:(vn278) else
              if Int.equal k 279 then constr:(vn279) else
              constr:(O)
            else
              if Int.equal k 280 then constr:(vn280) else
              if Int.equal k 281 then constr:(vn281) else
              if Int.equal k 282 then constr:(vn282) else
              if Int.equal k 283 then constr:(vn283) else
              if Int.equal k 284 then constr:(vn284) else
              if Int.equal k 285 then constr:(vn285) else
              if Int.equal k 286 then constr:(vn286) else
              if Int.equal k 287 then constr:(vn287) else
              constr:(O)
        else
          if Int.lt k 304 then
            if Int.lt k 296 then
              if Int.equal k 288 then constr:(vn288) else
              if Int.equal k 289 then constr:(vn289) else
              if Int.equal k 290 then constr:(vn290) else
              if Int.equal k 291 then constr:(vn291) else
              if Int.equal k 292 then constr:(vn292) else
              if Int.equal k 293 then constr:(vn293) else
              if Int.equal k 294 then constr:(vn294) else
              if Int.equal k 295 then constr:(vn295) else
              constr:(O)
            else
              if Int.equal k 296 then constr:(vn296) else
              if Int.equal k 297 then constr:(vn297) else
              if Int.equal k 298 then constr:(vn298) else
              if Int.equal k 299 then constr:(vn299) else
              if Int.equal k 300 then constr:(vn300) else
              if Int.equal k 301 then constr:(vn301) else
              if Int.equal k 302 then constr:(vn302) else
              if Int.equal k 303 then constr:(vn303) else
              constr:(O)
          else
            if Int.lt k 312 then
              if Int.equal k 304 then constr:(vn304) else
              if Int.equal k 305 then constr:(vn305) else
              if Int.equal k 306 then constr:(vn306) else
              if Int.equal k 307 then constr:(vn307) else
              if Int.equal k 308 then constr:(vn308) else
              if Int.equal k 309 then constr:(vn309) else
              if Int.equal k 310 then constr:(vn310) else
              if Int.equal k 311 then constr:(vn311) else
              constr:(O)
            else
              if Int.equal k 312 then constr:(vn312) else
              if Int.equal k 313 then constr:(vn313) else
              if Int.equal k 314 then constr:(vn314) else
              if Int.equal k 315 then constr:(vn315) else
              if Int.equal k 316 then constr:(vn316) else
              if Int.equal k 317 then constr:(vn317) else
              if Int.equal k 318 then constr:(vn318) else
              if Int.equal k 319 then constr:(vn319) else
              constr:(O)
      else
        if Int.lt k 352 then
          if Int.lt k 336 then
            if Int.lt k 328 then
              if Int.equal k 320 then constr:(vn320) else
              if Int.equal k 321 then constr:(vn321) else
              if Int.equal k 322 then constr:(vn322) else
              if Int.equal k 323 then constr:(vn323) else
              if Int.equal k 324 then constr:(vn324) else
              if Int.equal k 325 then constr:(vn325) else
              if Int.equal k 326 then constr:(vn326) else
              if Int.equal k 327 then constr:(vn327) else
              constr:(O)
            else
              if Int.equal k 328 then constr:(vn328) else
              if Int.equal k 329 then constr:(vn329) else
              if Int.equal k 330 then constr:(vn330) else
              if Int.equal k 331 then constr:(vn331) else
              if Int.equal k 332 then constr:(vn332) else
              if Int.equal k 333 then constr:(vn333) else
              if Int.equal k 334 then constr:(vn334) else
              if Int.equal k 335 then constr:(vn335) else
              constr:(O)
          else
            if Int.lt k 344 then
              if Int.equal k 336 then constr:(vn336) else
              if Int.equal k 337 then constr:(vn337) else
              if Int.equal k 338 then constr:(vn338) else
              if Int.equal k 339 then constr:(vn339) else
              if Int.equal k 340 then constr:(vn340) else
              if Int.equal k 341 then constr:(vn341) else
              if Int.equal k 342 then constr:(vn342) else
              if Int.equal k 343 then constr:(vn343) else
              constr:(O)
            else
              if Int.equal k 344 then constr:(vn344) else
              if Int.equal k 345 then constr:(vn345) else
              if Int.equal k 346 then constr:(vn346) else
              if Int.equal k 347 then constr:(vn347) else
              if Int.equal k 348 then constr:(vn348) else
              if Int.equal k 349 then constr:(vn349) else
              if Int.equal k 350 then constr:(vn350) else
              if Int.equal k 351 then constr:(vn351) else
              constr:(O)
        else
          if Int.lt k 368 then
            if Int.lt k 360 then
              if Int.equal k 352 then constr:(vn352) else
              if Int.equal k 353 then constr:(vn353) else
              if Int.equal k 354 then constr:(vn354) else
              if Int.equal k 355 then constr:(vn355) else
              if Int.equal k 356 then constr:(vn356) else
              if Int.equal k 357 then constr:(vn357) else
              if Int.equal k 358 then constr:(vn358) else
              if Int.equal k 359 then constr:(vn359) else
              constr:(O)
            else
              if Int.equal k 360 then constr:(vn360) else
              if Int.equal k 361 then constr:(vn361) else
              if Int.equal k 362 then constr:(vn362) else
              if Int.equal k 363 then constr:(vn363) else
              if Int.equal k 364 then constr:(vn364) else
              if Int.equal k 365 then constr:(vn365) else
              if Int.equal k 366 then constr:(vn366) else
              if Int.equal k 367 then constr:(vn367) else
              constr:(O)
          else
            if Int.lt k 376 then
              if Int.equal k 368 then constr:(vn368) else
              if Int.equal k 369 then constr:(vn369) else
              if Int.equal k 370 then constr:(vn370) else
              if Int.equal k 371 then constr:(vn371) else
              if Int.equal k 372 then constr:(vn372) else
              if Int.equal k 373 then constr:(vn373) else
              if Int.equal k 374 then constr:(vn374) else
              if Int.equal k 375 then constr:(vn375) else
              constr:(O)
            else
              if Int.equal k 376 then constr:(vn376) else
              if Int.equal k 377 then constr:(vn377) else
              if Int.equal k 378 then constr:(vn378) else
              if Int.equal k 379 then constr:(vn379) else
              if Int.equal k 380 then constr:(vn380) else
              if Int.equal k 381 then constr:(vn381) else
              if Int.equal k 382 then constr:(vn382) else
              if Int.equal k 383 then constr:(vn383) else
              constr:(O)
    else
      if Int.lt k 448 then
        if Int.lt k 416 then
          if Int.lt k 400 then
            if Int.lt k 392 then
              if Int.equal k 384 then constr:(vn384) else
              if Int.equal k 385 then constr:(vn385) else
              if Int.equal k 386 then constr:(vn386) else
              if Int.equal k 387 then constr:(vn387) else
              if Int.equal k 388 then constr:(vn388) else
              if Int.equal k 389 then constr:(vn389) else
              if Int.equal k 390 then constr:(vn390) else
              if Int.equal k 391 then constr:(vn391) else
              constr:(O)
            else
              if Int.equal k 392 then constr:(vn392) else
              if Int.equal k 393 then constr:(vn393) else
              if Int.equal k 394 then constr:(vn394) else
              if Int.equal k 395 then constr:(vn395) else
              if Int.equal k 396 then constr:(vn396) else
              if Int.equal k 397 then constr:(vn397) else
              if Int.equal k 398 then constr:(vn398) else
              if Int.equal k 399 then constr:(vn399) else
              constr:(O)
          else
            if Int.lt k 408 then
              if Int.equal k 400 then constr:(vn400) else
              if Int.equal k 401 then constr:(vn401) else
              if Int.equal k 402 then constr:(vn402) else
              if Int.equal k 403 then constr:(vn403) else
              if Int.equal k 404 then constr:(vn404) else
              if Int.equal k 405 then constr:(vn405) else
              if Int.equal k 406 then constr:(vn406) else
              if Int.equal k 407 then constr:(vn407) else
              constr:(O)
            else
              if Int.equal k 408 then constr:(vn408) else
              if Int.equal k 409 then constr:(vn409) else
              if Int.equal k 410 then constr:(vn410) else
              if Int.equal k 411 then constr:(vn411) else
              if Int.equal k 412 then constr:(vn412) else
              if Int.equal k 413 then constr:(vn413) else
              if Int.equal k 414 then constr:(vn414) else
              if Int.equal k 415 then constr:(vn415) else
              constr:(O)
        else
          if Int.lt k 432 then
            if Int.lt k 424 then
              if Int.equal k 416 then constr:(vn416) else
              if Int.equal k 417 then constr:(vn417) else
              if Int.equal k 418 then constr:(vn418) else
              if Int.equal k 419 then constr:(vn419) else
              if Int.equal k 420 then constr:(vn420) else
              if Int.equal k 421 then constr:(vn421) else
              if Int.equal k 422 then constr:(vn422) else
              if Int.equal k 423 then constr:(vn423) else
              constr:(O)
            else
              if Int.equal k 424 then constr:(vn424) else
              if Int.equal k 425 then constr:(vn425) else
              if Int.equal k 426 then constr:(vn426) else
              if Int.equal k 427 then constr:(vn427) else
              if Int.equal k 428 then constr:(vn428) else
              if Int.equal k 429 then constr:(vn429) else
              if Int.equal k 430 then constr:(vn430) else
              if Int.equal k 431 then constr:(vn431) else
              constr:(O)
          else
            if Int.lt k 440 then
              if Int.equal k 432 then constr:(vn432) else
              if Int.equal k 433 then constr:(vn433) else
              if Int.equal k 434 then constr:(vn434) else
              if Int.equal k 435 then constr:(vn435) else
              if Int.equal k 436 then constr:(vn436) else
              if Int.equal k 437 then constr:(vn437) else
              if Int.equal k 438 then constr:(vn438) else
              if Int.equal k 439 then constr:(vn439) else
              constr:(O)
            else
              if Int.equal k 440 then constr:(vn440) else
              if Int.equal k 441 then constr:(vn441) else
              if Int.equal k 442 then constr:(vn442) else
              if Int.equal k 443 then constr:(vn443) else
              if Int.equal k 444 then constr:(vn444) else
              if Int.equal k 445 then constr:(vn445) else
              if Int.equal k 446 then constr:(vn446) else
              if Int.equal k 447 then constr:(vn447) else
              constr:(O)
      else
        if Int.lt k 480 then
          if Int.lt k 464 then
            if Int.lt k 456 then
              if Int.equal k 448 then constr:(vn448) else
              if Int.equal k 449 then constr:(vn449) else
              if Int.equal k 450 then constr:(vn450) else
              if Int.equal k 451 then constr:(vn451) else
              if Int.equal k 452 then constr:(vn452) else
              if Int.equal k 453 then constr:(vn453) else
              if Int.equal k 454 then constr:(vn454) else
              if Int.equal k 455 then constr:(vn455) else
              constr:(O)
            else
              if Int.equal k 456 then constr:(vn456) else
              if Int.equal k 457 then constr:(vn457) else
              if Int.equal k 458 then constr:(vn458) else
              if Int.equal k 459 then constr:(vn459) else
              if Int.equal k 460 then constr:(vn460) else
              if Int.equal k 461 then constr:(vn461) else
              if Int.equal k 462 then constr:(vn462) else
              if Int.equal k 463 then constr:(vn463) else
              constr:(O)
          else
            if Int.lt k 472 then
              if Int.equal k 464 then constr:(vn464) else
              if Int.equal k 465 then constr:(vn465) else
              if Int.equal k 466 then constr:(vn466) else
              if Int.equal k 467 then constr:(vn467) else
              if Int.equal k 468 then constr:(vn468) else
              if Int.equal k 469 then constr:(vn469) else
              if Int.equal k 470 then constr:(vn470) else
              if Int.equal k 471 then constr:(vn471) else
              constr:(O)
            else
              if Int.equal k 472 then constr:(vn472) else
              if Int.equal k 473 then constr:(vn473) else
              if Int.equal k 474 then constr:(vn474) else
              if Int.equal k 475 then constr:(vn475) else
              if Int.equal k 476 then constr:(vn476) else
              if Int.equal k 477 then constr:(vn477) else
              if Int.equal k 478 then constr:(vn478) else
              if Int.equal k 479 then constr:(vn479) else
              constr:(O)
        else
          if Int.lt k 496 then
            if Int.lt k 488 then
              if Int.equal k 480 then constr:(vn480) else
              if Int.equal k 481 then constr:(vn481) else
              if Int.equal k 482 then constr:(vn482) else
              if Int.equal k 483 then constr:(vn483) else
              if Int.equal k 484 then constr:(vn484) else
              if Int.equal k 485 then constr:(vn485) else
              if Int.equal k 486 then constr:(vn486) else
              if Int.equal k 487 then constr:(vn487) else
              constr:(O)
            else
              if Int.equal k 488 then constr:(vn488) else
              if Int.equal k 489 then constr:(vn489) else
              if Int.equal k 490 then constr:(vn490) else
              if Int.equal k 491 then constr:(vn491) else
              if Int.equal k 492 then constr:(vn492) else
              if Int.equal k 493 then constr:(vn493) else
              if Int.equal k 494 then constr:(vn494) else
              if Int.equal k 495 then constr:(vn495) else
              constr:(O)
          else
            if Int.lt k 504 then
              if Int.equal k 496 then constr:(vn496) else
              if Int.equal k 497 then constr:(vn497) else
              if Int.equal k 498 then constr:(vn498) else
              if Int.equal k 499 then constr:(vn499) else
              if Int.equal k 500 then constr:(vn500) else
              if Int.equal k 501 then constr:(vn501) else
              if Int.equal k 502 then constr:(vn502) else
              if Int.equal k 503 then constr:(vn503) else
              constr:(O)
            else
              if Int.equal k 504 then constr:(vn504) else
              if Int.equal k 505 then constr:(vn505) else
              if Int.equal k 506 then constr:(vn506) else
              if Int.equal k 507 then constr:(vn507) else
              if Int.equal k 508 then constr:(vn508) else
              if Int.equal k 509 then constr:(vn509) else
              if Int.equal k 510 then constr:(vn510) else
              if Int.equal k 511 then constr:(vn511) else
              constr:(O).

(* [comment removed for export] *)
Ltac2 Type heads := { hS : constr; hO : constr; hEF : constr; hE2 : constr; hLF : constr; hL2 : constr;
                      hZp : constr; hZn : constr; hIdn : constr }.
Ltac2 mk_heads () : heads :=
  { hS := constr:(S); hO := constr:(O); hEF := constr:(SXF.EVar); hE2 := constr:(SX2.EVar);
    hLF := constr:(SXF.ELit); hL2 := constr:(SX2.ELit); hZp := constr:(Zpos); hZn := constr:(Zneg); hIdn := constr:(idn) }.

(* [comment removed for export] *)
Ltac2 rec nat_walk (c : constr) (acc : int) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => Some acc
  | Constr.Unsafe.App _ args => nat_walk (Array.get args 0) (Int.add acc 1)
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 nat_lit (h : heads) (c : constr) (acc : int) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => if Constr.equal c (h.(hO)) then Some acc else None
  | Constr.Unsafe.App f args => if Constr.equal f (h.(hS)) then nat_walk (Array.get args 0) (Int.add acc 1) else None
  | _ => None
  end.

Ltac2 leaf (h : heads) (m : (constr * constr) list) (n : constr) : constr * (constr * constr) list :=
  let v := match nat_lit h n 0 with
           | Some k => if Int.lt k 512 then vn_of k else Constr.Unsafe.make (Constr.Unsafe.App (h.(hIdn)) [| n |])
           | None => Constr.Unsafe.make (Constr.Unsafe.App (h.(hIdn)) [| n |])
           end in
  (v, m).

Ltac2 rec binzm (h : heads) (c : constr) (m : (constr * constr) list) : constr * (constr * constr) list :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Constr.equal f (h.(hEF)) then
        let (v, m') := leaf h m (Array.get args 0) in (Constr.Unsafe.make (Constr.Unsafe.App f [| v |]), m')
      else if Constr.equal f (h.(hE2)) then
        let (v, m') := leaf h m (Array.get args 0) in (Constr.Unsafe.make (Constr.Unsafe.App f [| v |]), m')
      else if Constr.equal f (h.(hLF)) then (c, m)
      else if Constr.equal f (h.(hL2)) then (c, m)
      else if Constr.equal f (h.(hZp)) then (c, m)
      else if Constr.equal f (h.(hZn)) then (c, m)
      else
        let n := Array.length args in
        let res := Array.make n c in
        let rec go i m :=
          if Int.equal i n then m
          else let (a, m2) := binzm h (Array.get args i) m in (Array.set res i a; go (Int.add i 1) m2) in
        let m' := go 0 m in
        (Constr.Unsafe.make (Constr.Unsafe.App f res), m')
  | _ => (c, m)
  end.

Ltac2 binz (c : constr) : constr := let h := mk_heads () in let (t, _) := binzm h c [] in t.

(* [comment removed for export] *)
Ltac binarize_k c k := let f := ltac2:(c k |- let t := binz (Option.get (Ltac1.to_constr c)) in Ltac1.apply k [Ltac1.of_constr t] Ltac1.run) in f c k.


Goal True.
  binarize_k constr:([SXF.EVar 64; SXF.EAlu ALU_ADD (SXF.EVar 3) (SXF.ELit 5); SXF.EVar 64; SXF.EVar 600]) ltac:(fun t =>
    lazymatch t with [SXF.EVar vn64; SXF.EAlu ALU_ADD (SXF.EVar vn3) (SXF.ELit 5); SXF.EVar vn64; SXF.EVar (idn 600)] => idtac | _ => fail end).
  binarize_k constr:([SX2.EVar 200; SX2.ELit 7]) ltac:(fun t =>
    lazymatch t with [SX2.EVar vn200; SX2.ELit 7] => idtac | _ => fail end).
  exact I.
Qed.
