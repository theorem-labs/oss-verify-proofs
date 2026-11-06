(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import Reloc.

(* [comment removed for export] *)
Abbreviation B_OL_23720 := 200%positive (only parsing).
Abbreviation dOL_23720 := (rl_delta 200%positive).
(* [comment removed for export] *)
Abbreviation B_OL_237ac := 210%positive (only parsing).
Abbreviation dOL_237ac := (rl_delta 210%positive).
(* [comment removed for export] *)
Abbreviation B_OL_238e8 := 211%positive (only parsing).
Abbreviation dOL_238e8 := (rl_delta 211%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23be4 := 212%positive (only parsing).
Abbreviation dOL_23be4 := (rl_delta 212%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23c24 := 213%positive (only parsing).
Abbreviation dOL_23c24 := (rl_delta 213%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23cf0 := 201%positive (only parsing).
Abbreviation dOL_23cf0 := (rl_delta 201%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23d70 := 202%positive (only parsing).
Abbreviation dOL_23d70 := (rl_delta 202%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23e54 := 203%positive (only parsing).
Abbreviation dOL_23e54 := (rl_delta 203%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23e94 := 204%positive (only parsing).
Abbreviation dOL_23e94 := (rl_delta 204%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23ed4 := 214%positive (only parsing).
Abbreviation dOL_23ed4 := (rl_delta 214%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23f14 := 205%positive (only parsing).
Abbreviation dOL_23f14 := (rl_delta 205%positive).
(* [comment removed for export] *)
Abbreviation B_OL_23f9c := 206%positive (only parsing).
Abbreviation dOL_23f9c := (rl_delta 206%positive).
(* [comment removed for export] *)
Abbreviation B_OL_24118 := 207%positive (only parsing).
Abbreviation dOL_24118 := (rl_delta 207%positive).
(* [comment removed for export] *)
Abbreviation B_OL_24414 := 215%positive (only parsing).
Abbreviation dOL_24414 := (rl_delta 215%positive).
(* [comment removed for export] *)
Abbreviation B_OL_24498 := 208%positive (only parsing).
Abbreviation dOL_24498 := (rl_delta 208%positive).
(* [comment removed for export] *)
Abbreviation B_OL_246d4 := 216%positive (only parsing).
Abbreviation dOL_246d4 := (rl_delta 216%positive).
(* [comment removed for export] *)
Abbreviation B_OL_2499c := 217%positive (only parsing).
Abbreviation dOL_2499c := (rl_delta 217%positive).
(* [comment removed for export] *)
Abbreviation B_OL_24b94 := 209%positive (only parsing).
Abbreviation dOL_24b94 := (rl_delta 209%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10298 := (rl_delta 300%positive).
(* [comment removed for export] *)
Abbreviation dOLS_102aa := (rl_delta 301%positive).
(* [comment removed for export] *)
Abbreviation dOLS_102b6 := (rl_delta 302%positive).
(* [comment removed for export] *)
Abbreviation dOLS_102c7 := (rl_delta 303%positive).
(* [comment removed for export] *)
Abbreviation dOLS_102d6 := (rl_delta 304%positive).
(* [comment removed for export] *)
Abbreviation dOLS_102f1 := (rl_delta 305%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10316 := (rl_delta 306%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10325 := (rl_delta 307%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10335 := (rl_delta 308%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10340 := (rl_delta 309%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1034f := (rl_delta 310%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1037f := (rl_delta 311%positive).
(* [comment removed for export] *)
Abbreviation dOLS_103b7 := (rl_delta 312%positive).
(* [comment removed for export] *)
Abbreviation dOLS_103c5 := (rl_delta 313%positive).
(* [comment removed for export] *)
Abbreviation dOLS_103d4 := (rl_delta 314%positive).
(* [comment removed for export] *)
Abbreviation dOLS_103e3 := (rl_delta 315%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1040f := (rl_delta 316%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10436 := (rl_delta 317%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10460 := (rl_delta 318%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10470 := (rl_delta 319%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1047c := (rl_delta 320%positive).
(* [comment removed for export] *)
Abbreviation dOLS_104c3 := (rl_delta 321%positive).
(* [comment removed for export] *)
Abbreviation dOLS_104cd := (rl_delta 322%positive).
(* [comment removed for export] *)
Abbreviation dOLS_104e0 := (rl_delta 323%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10534 := (rl_delta 324%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10544 := (rl_delta 325%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10567 := (rl_delta 326%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10572 := (rl_delta 327%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1058d := (rl_delta 328%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10598 := (rl_delta 329%positive).
(* [comment removed for export] *)
Abbreviation dOLS_105a6 := (rl_delta 330%positive).
(* [comment removed for export] *)
Abbreviation dOLS_105cb := (rl_delta 331%positive).
(* [comment removed for export] *)
Abbreviation dOLS_105e4 := (rl_delta 332%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10612 := (rl_delta 333%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10645 := (rl_delta 334%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10654 := (rl_delta 335%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10667 := (rl_delta 336%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10675 := (rl_delta 337%positive).
(* [comment removed for export] *)
Abbreviation dOLS_106e7 := (rl_delta 338%positive).
(* [comment removed for export] *)
Abbreviation dOLS_106fa := (rl_delta 339%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1071d := (rl_delta 340%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1072f := (rl_delta 341%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10764 := (rl_delta 342%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10774 := (rl_delta 343%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10781 := (rl_delta 344%positive).
(* [comment removed for export] *)
Abbreviation dOLS_107bb := (rl_delta 345%positive).
(* [comment removed for export] *)
Abbreviation dOLS_107cc := (rl_delta 346%positive).
(* [comment removed for export] *)
Abbreviation dOLS_107ee := (rl_delta 347%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10806 := (rl_delta 348%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10810 := (rl_delta 349%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10826 := (rl_delta 350%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1083d := (rl_delta 351%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1086c := (rl_delta 352%positive).
(* [comment removed for export] *)
Abbreviation dOLS_108aa := (rl_delta 353%positive).
(* [comment removed for export] *)
Abbreviation dOLS_108c7 := (rl_delta 354%positive).
(* [comment removed for export] *)
Abbreviation dOLS_108d3 := (rl_delta 355%positive).
(* [comment removed for export] *)
Abbreviation dOLS_108e9 := (rl_delta 356%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10906 := (rl_delta 357%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10935 := (rl_delta 358%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10947 := (rl_delta 359%positive).
(* [comment removed for export] *)
Abbreviation dOLS_1097f := (rl_delta 360%positive).
(* [comment removed for export] *)
Abbreviation dOLS_109d2 := (rl_delta 361%positive).
(* [comment removed for export] *)
Abbreviation dOLS_109eb := (rl_delta 362%positive).
(* [comment removed for export] *)
Abbreviation dOLS_109fc := (rl_delta 363%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10a12 := (rl_delta 364%positive).
(* [comment removed for export] *)
Abbreviation dOLS_10a26 := (rl_delta 365%positive).
