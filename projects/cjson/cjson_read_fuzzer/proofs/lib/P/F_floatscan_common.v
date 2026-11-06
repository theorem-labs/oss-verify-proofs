(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_f128_mul.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sf_helpers3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_divtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_divtf3_wide.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmodl.
Module F_divtf3_round.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_wide OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3_wide.F_divtf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3_wide.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
Definition saved12 (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (j : list byte) : list cell :=
  [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition DRr (signHi absHi absLo r3Hi r3Lo bHi bLo gt1 : Z) : Z :=
  let abs1Lo := add64 absLo gt1 in
  let b2Hi := shl64 bHi 1 in
  let ca := b2z (Z.ltb abs1Lo absLo) in
  let b3Hi0 := mulhu bLo 3 in
  let abs1Hi := add64 absHi ca in
  let b3Hi1 := add64 b3Hi0 bHi in
  let b3Hi := add64 b3Hi1 b2Hi in
  let ltInf1 := b2z (Z.ltb abs1Hi INF_HI) in
  let gt3 := b2z (if Z.eqb r3Hi b3Hi then Z.ltb (add64 (shl64 bLo 1) bLo) r3Lo else Z.ltb b3Hi r3Hi) in
  let inc2 := Z.land ltInf1 gt3 in
  let b5Hi0 := mulhu bLo 5 in
  let b5Hi1 := add64 b5Hi0 bHi in
  let b4Hi := shl64 bHi 2 in
  let abs2Lo := add64 abs1Lo inc2 in
  let cb := b2z (Z.ltb abs2Lo abs1Lo) in
  let abs2Hi := add64 abs1Hi cb in
  let b5Hi := add64 b5Hi1 b4Hi in
  let ltInf2 := b2z (Z.ltb abs2Hi INF_HI) in
  let gt5 := b2z (if Z.eqb r3Hi b5Hi then Z.ltb (add64 (shl64 bLo 2) bLo) r3Lo else Z.ltb b5Hi r3Hi) in
  let inc3 := Z.land ltInf2 gt5 in
  let resLo := add64 abs2Lo inc3 in
  let cc := b2z (Z.ltb resLo abs2Lo) in
  let resHi := Z.lor (add64 abs2Hi cc) signHi in
  mk128 resHi resLo.

(* [comment removed for export] *)
Section IfLemmas.
  Context {T : Type}.
  Lemma if_ltb_t x y (A B : T) : x < y -> (if x <? y then A else B) = A.   Proof. intro; now rewrite (proj2 (Z.ltb_lt x y)). Qed.
  Lemma if_ltb_f x y (A B : T) : y <= x -> (if x <? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.ltb_ge x y)). Qed.
  Lemma if_leb_t x y (A B : T) : x <= y -> (if x <=? y then A else B) = A. Proof. intro; now rewrite (proj2 (Z.leb_le x y)). Qed.
  Lemma if_leb_f x y (A B : T) : y < x -> (if x <=? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.leb_gt x y)). Qed.
  Lemma if_eqb_t x y (A B : T) : x = y -> (if x =? y then A else B) = A.   Proof. intro; now rewrite (proj2 (Z.eqb_eq x y)). Qed.
  Lemma if_eqb_f x y (A B : T) : x <> y -> (if x =? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.eqb_neq x y)). Qed.
  Lemma if_nltb_t x y (A B : T) : x < y -> (if negb (x <? y) then A else B) = B.   Proof. intro; now rewrite (proj2 (Z.ltb_lt x y)). Qed.
  Lemma if_nltb_f x y (A B : T) : y <= x -> (if negb (x <? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.ltb_ge x y)). Qed.
  Lemma if_nleb_t x y (A B : T) : x <= y -> (if negb (x <=? y) then A else B) = B. Proof. intro; now rewrite (proj2 (Z.leb_le x y)). Qed.
  Lemma if_nleb_f x y (A B : T) : y < x -> (if negb (x <=? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.leb_gt x y)). Qed.
  Lemma if_neqb_t x y (A B : T) : x = y -> (if negb (x =? y) then A else B) = B.   Proof. intro; now rewrite (proj2 (Z.eqb_eq x y)). Qed.
  Lemma if_neqb_f x y (A B : T) : x <> y -> (if negb (x =? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.eqb_neq x y)). Qed.
End IfLemmas.
Ltac decide_ifs ::=
  repeat (match goal with
  | |- context [if (?x <? ?y) then ?A else ?B] => first [rewrite (if_ltb_t x y A B) by lia | rewrite (if_ltb_f x y A B) by lia]
  | |- context [if negb (?x <? ?y) then ?A else ?B] => first [rewrite (if_nltb_t x y A B) by lia | rewrite (if_nltb_f x y A B) by lia]
  | |- context [if (?x <=? ?y) then ?A else ?B] => first [rewrite (if_leb_t x y A B) by lia | rewrite (if_leb_f x y A B) by lia]
  | |- context [if negb (?x <=? ?y) then ?A else ?B] => first [rewrite (if_nleb_t x y A B) by lia | rewrite (if_nleb_f x y A B) by lia]
  | |- context [if (?x =? ?y) then ?A else ?B] => first [rewrite (if_eqb_t x y A B) by lia | rewrite (if_eqb_f x y A B) by lia]
  | |- context [if negb (?x =? ?y) then ?A else ?B] => first [rewrite (if_neqb_t x y A B) by lia | rewrite (if_neqb_f x y A B) by lia]
  end).
End F_divtf3_round.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module F_divtf3_tail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_wide OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3_wide.F_divtf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3_wide F_divtf3_round.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)
Local Ltac simp_amounts ::=
  try (lazymatch goal with |- context [Z.land (_ - Z.land _ 18446744073709551615) 18446744073709551615] => rewrite !F_f128_mul.land_sub_neg by lia end);
  try (lazymatch goal with |- context [Z.land (Z.lxor (Z.land _ 4294967295) 2147483648 - 2147483648) 18446744073709551615] => rewrite !sext32_id by lia end);
  try (lazymatch goal with |- context [Z.land (Z.land _ 18446744073709551615 + _) 18446744073709551615] => rewrite !land_add_neg by lia end);
  try (lazymatch goal with |- context [Z.land _ 4294967295] => rewrite !landM32_id by lia end);
  try (lazymatch goal with |- context [negb (Z.shiftr (Z.land _ 18446744073709551615) 63 =? 0)] => rewrite !isneg_land by lia end);
  try (lazymatch goal with |- context [Z.shiftr (Z.land _ 18446744073709551615) 63 =? 0] => rewrite !isneg_land2 by lia end);
  decide_ifs;
  try (lazymatch goal with |- context [Z.land 18446744073709551615 _] => rewrite !F_sf_helpers2.land_ones_l by F_f128_mul.zrange2 end);
  try (lazymatch goal with |- context [Z.land 0 _] => rewrite ?Z.land_0_l end).
End F_divtf3_tail.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sf_helpers2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_f128_mul_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module F_divtf3_main.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul_top OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_wide OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_top.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_norm OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3_wide.F_divtf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3_wide F_divtf3_round F_divtf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_divtf3_norm.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
Theorem divtf3_spec : divtf3_stmt.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.divtf3_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.divtf3_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.divtf3_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.divtf3_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.divtf3_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.
#[export] Instance P_divtf3_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.divtf3_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.G_divtf3_main.divtf3_spec_c_ok.
End F_divtf3_main.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_letf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_floatsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fpclassifyl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StepFast.
Module F_fmodl.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_divtf3 F_divtf3_main OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fpclassifyl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.


(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
(* [comment removed for export] *)

#[local] Ltac2 Set OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StepFast.SF.sf_mode := 0.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fpclassifyl.P_fpclassifyl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)

Definition FMODL : Z := 0x1f914.
Definition RFMODL_DEPTH : Z := 192.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lit_loads :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?c)] =>
      lazymatch isZcst c with true => idtac end;
      let c' := eval vm_compute in (bv_swrap 32 (c mod 2^64))%Z in
      let c'' := eval vm_compute in (c' mod 2^64)%Z in
      replace (sx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c'') by (unfold sx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
  | |- context [zx32 (Z_to_bv 64 ?c)] =>
      lazymatch isZcst c with true => idtac end;
      let c' := eval vm_compute in ((c mod 2^64) mod 2^32)%Z in
      replace (zx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c') by (unfold zx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
  end.

Definition extsf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom psegs)
    /\ munch [] m m /\ wmono psegs m m /\ mem_inv psegs m.

Definition rfmodl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - RFMODL_DEPTH, q)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (q - RFMODL_DEPTH) q
    /\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k).

Definition rfmodl_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X Y r : Z),
  stk psegs m (q - RFMODL_DEPTH) q -> mem_inv psegs m ->
  (4096 <= q - RFMODL_DEPTH)%Z -> (q < 2^63)%Z ->
  m_fmodl X Y = Some r ->
  evt psegs (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FMODL) fc None m (seg_rom psegs)).
#[export] Instance P_rfmodl_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.rfmodl_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmodl.rfmodl_spec_c_ok.
End F_fmodl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan_split2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3 F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_strnlen.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3_tail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_divtf3.
Import F_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_subtf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_subtf3 F_letf2 F_getf2 F_floatsitf F_floatunsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scalbn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scalbnl.
Import F_fmodl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
From Ltac2 Require Import Ltac2 Constr.
Set Default Proof Mode "Classic".
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_floatscan_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_subtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_strnlen.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_multf3.P_multf3_contract F_divtf3_main.P_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.F_addtf3_E.P_addtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_subtf3.P_subtf3_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_letf2.P_letf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_getf2.P_getf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatsitf.P_floatsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_floatunsitf.P_floatunsitf_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.F_extenddftf2.P_extenddftf2_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbn.P_scalbn_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_shlim_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_A.P_toread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc_B.P_sread_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_uflow_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_shgetc.P_shgetc_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_rfile.P_shgetc_callJ_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_scalbnl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_fabsl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scalbnl.P_copysignl_spec_c F_fmodl.P_rfmodl_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Scan_iface.F_scanexp.P_scanexp_rspec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Ltac2 rec zt_plain_arith' (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
          else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
          else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
          else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
          else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
          else false
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@and then (if zt_plain_arith' (Array.get args 0) then zt_plain_arith' (Array.get args 1) else false)
          else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
          else false
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
  | _ => false
  end.
Ltac2 rec zt_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => zt_codomain b
  | Constr.Unsafe.LetIn _ _ b => zt_codomain b
  | Constr.Unsafe.Cast c _ _ => zt_codomain c
  | _ => t
  end.
Ltac2 rec zt_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => zt_head f
  | Constr.Unsafe.Cast c _ _ => zt_head c
  | _ => t
  end.
Ltac2 zt_sort_is_prop (ty : constr) : bool :=
  lazy_match! zt_codomain ty with Prop => true | _ => false end.
Ltac2 zt_is_prop_fast (ty : constr) : bool :=
  let h := zt_head (zt_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
  | _ => false
  end.
Ltac2 zt_is_local' (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.
Ltac2 zt_prune_fast () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_arith' ty then None
                          else if Bool.and (zt_is_local' id) (zt_is_prop_fast ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
(* [comment removed for export] *)

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
  idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
(* [comment removed for export] *)
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

(* [comment removed for export] *)
Ltac fix_idx := repeat match goal with
  | |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
    replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
  | |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
    replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

(* [comment removed for export] *)
Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
  let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.

(* [comment removed for export] *)
Definition RATP : Z := 0x33890.
Definition RERRNO : Z := 0x337ec.
Definition ERRNO_LOC : Z := 0x151c8.

Definition FS_DEPTH : Z := 8656.    (* [comment removed for export] *)
Definition FLOATSCAN : Z := 0x1d780.
