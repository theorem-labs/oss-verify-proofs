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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_divtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_divtf3_wide.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require ProgAt3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Module G_divtf3_round.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_wide OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3_wide.G_divtf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3_wide.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_divtf3.   Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt. 
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_divtf3_round : CodeAtT img_segs (sym 0x1c6b0) (divtf3_prog_at IMG)}.
  Context {RB_divtf3_round : RelCode (sym 0x1c6b0) 2308}.
  Collection ImgHyps := IMG CODE_divtf3_round RB_divtf3_round.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
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

Lemma div_round_DRr : forall s aH aL rH rL bH bL,
  div_round s aH aL rH rL bH bL =
  let odd := Z.land aL 1 in
  let r3Lo := add64 odd rL in
  let rc := b2z (Z.ltb r3Lo odd) in
  let r3Hi := add64 rH rc in
  DRr s aH aL r3Hi r3Lo bH bL (b2z (if Z.eqb r3Hi bH then Z.ltb bL r3Lo else Z.ltb bH r3Hi)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma subw_amt : forall wE, -2^30 < wE < 2^30 ->
  bv_swrap 32 (1 - Z.land wE 18446744073709551615) = 1 - wE.
Proof.
  intros. rewrite land_W64. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 `div` 2) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

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

Section Walk.
  Variables (sp sgw w6 : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation sgn := (bv_unsigned sgw).
  Notation bLo := (bv_unsigned w6).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
    | |- (_ <= _ <= _)%Z => lia
    | |- (0 <= _ < _)%Z => first [zrange2 | lia]
    end.
  Ltac join L := eapply L; try hyp.
  Ltac exact_HR :=
    lazymatch goal with |- ?g =>
      match goal with
      | HR : ?t |- _ => constr_eq t g; exact HR
      | HR : @eq Z ?r ?t |- _ => fail 0 "exact_HR: goal" g "but HR:" r "=" t
      end
    end.

  (* [comment removed for export] *)
  Lemma Lepi : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1
      y1 y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    Z_to_bv 64 (lo64 R) = w0 -> Z_to_bv 64 (hi64 R) = w1 ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 w0 w1 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1912)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO H0 H1. unfold saved12 in FR.
    pose_word_ranges.
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- H0, <- H1. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma Lzero : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w1
      y1 y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = mk128 (bv_unsigned w1) 0 ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 y10 w1 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1344)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    do 2 zstep. join Lepi; subst R; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; [reflexivity | apply Z_to_bv_bv_unsigned].
  Qed.

  (* [comment removed for export] *)
  Lemma Linf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = mk128 (Z.lor sgn INF_HI) 0 ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 y10 sgw y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1152)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    do 5 zstep. join Lepi; subst R; unfold INF_HI; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; reflexivity.
  Qed.

  Ltac flag_join n G body K :=
    set (G := body);
    let w := getreg n in
    lazymatch w with Z_to_bv 64 ?e =>
      replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
        by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
    end;
    let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

  (* [comment removed for export] *)
  Lemma Lround : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (absHi absLo r3Hi r3Lo bHi : Z) (g1 : bool)
      y1 y5 y6 y7 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= absHi < 2^64)%Z -> (0 <= absLo < 2^64)%Z -> (0 <= r3Hi < 2^64)%Z -> (0 <= r3Lo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
    R = DRr sgn absHi absLo r3Hi r3Lo bHi bLo (Z.b2z g1) ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 absLo) sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 r3Lo) (Z_to_bv 64 absHi) (Z_to_bv 64 r3Hi) (Z_to_bv 64 (Z.b2z g1))
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1760)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 HR.
    pose_word_ranges.
    name_as gt1 (Z.b2z g1).
    zstep. model_reg 17 abs1Lo (Z.land (absLo + gt1) 18446744073709551615).
    do 3 zstep. model_reg 7 b2Hi (Z.land (Z.shiftl bHi 1) 18446744073709551615).
    zstep. model_reg 28 ca (Z.b2z (abs1Lo <? absLo)).
    zstep. zstep. model_reg 5 b3Hi0 (Z.shiftr (bLo * 3) 64). mulhu_rng b3Hi0.
    zstep. model_reg 15 abs1Hi (Z.land (absHi + ca) 18446744073709551615).
    zstep. model_reg 5 b3Hi1 (Z.land (b3Hi0 + bHi) 18446744073709551615).
    zstep. model_reg 6 b3Hi (Z.land (b3Hi1 + b2Hi) 18446744073709551615).
    zstep. model_reg 5 ltInf1 (Z.b2z (abs1Hi <? 9223090561878065152)).
    zstep. if_cases K2; zify_cond K2; [ do 3 zstep | do 2 zstep ];
      flag_join 6%Z gt3 (Z.b2z (if r3Hi =? b3Hi then Z.land (Z.land (Z.shiftl bLo 1) 18446744073709551615 + bLo) 18446744073709551615 <? r3Lo else b3Hi <? r3Hi)) K2;
      ( zstep; model_reg 5 inc2 (Z.land ltInf1 gt3);
        do 2 zstep; model_reg 6 b5Hi0 (Z.shiftr (bLo * 5) 64); mulhu_rng b5Hi0;
        zstep; model_reg 6 b5Hi1 (Z.land (b5Hi0 + bHi) 18446744073709551615);
        zstep; model_reg 7 b4Hi (Z.land (Z.shiftl bHi 2) 18446744073709551615);
        zstep; model_reg 13 abs2Lo (Z.land (abs1Lo + inc2) 18446744073709551615);
        zstep; model_reg 17 cb (Z.b2z (abs2Lo <? abs1Lo));
        zstep; model_reg 15 abs2Hi (Z.land (abs1Hi + cb) 18446744073709551615);
        zstep; model_reg 17 b5Hi (Z.land (b5Hi1 + b4Hi) 18446744073709551615);
        zstep; model_reg 10 ltInf2 (Z.b2z (abs2Hi <? 9223090561878065152));
        zstep; if_cases K3; zify_cond K3; [ do 3 zstep | do 2 zstep ] );
      flag_join 12%Z gt5 (Z.b2z (if r3Hi =? b5Hi then Z.land (Z.land (Z.shiftl bLo 2) 18446744073709551615 + bLo) 18446744073709551615 <? r3Lo else b5Hi <? r3Hi)) K3;
      ( zstep; model_reg 10 inc3 (Z.land ltInf2 gt5);
        zstep; model_reg 10 resLo (Z.land (abs2Lo + inc3) 18446744073709551615);
        zstep; model_reg 12 cc (Z.b2z (resLo <? abs2Lo));
        do 2 zstep; model_reg 11 resHi (Z.lor (Z.land (abs2Hi + cc) 18446744073709551615) sgn);
        assert (E : R = mk128 resHi resLo);
        [ rewrite HR; change (Z.b2z g1) with gt1; cbv beta delta [DRr]; sf_vocab;
          fold_model_lets2;
          repeat (first [ progress fold_model_lets2
                        | match goal with |- (let x := ?b in _) = _ =>
                            first [ change b with gt3 | change b with gt5 ] end ]);
          reflexivity
        | join Lepi; rewrite E; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; reflexivity ] ).
  Time Qed.

End Walk.

End Img.
(* [comment removed for export] *)
Ltac decide_ifs ::=
  repeat (match goal with
  | |- context [if (?x <? ?y) then ?A else ?B] => first [rewrite (if_ltb_t x y A B) by lia | rewrite (if_ltb_f x y A B) by lia]
  | |- context [if negb (?x <? ?y) then ?A else ?B] => first [rewrite (if_nltb_t x y A B) by lia | rewrite (if_nltb_f x y A B) by lia]
  | |- context [if (?x <=? ?y) then ?A else ?B] => first [rewrite (if_leb_t x y A B) by lia | rewrite (if_leb_f x y A B) by lia]
  | |- context [if negb (?x <=? ?y) then ?A else ?B] => first [rewrite (if_nleb_t x y A B) by lia | rewrite (if_nleb_f x y A B) by lia]
  | |- context [if (?x =? ?y) then ?A else ?B] => first [rewrite (if_eqb_t x y A B) by lia | rewrite (if_eqb_f x y A B) by lia]
  | |- context [if negb (?x =? ?y) then ?A else ?B] => first [rewrite (if_neqb_t x y A B) by lia | rewrite (if_neqb_f x y A B) by lia]
  end).
End G_divtf3_round.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module G_divtf3_tail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_wide OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3_wide.G_divtf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3_wide G_divtf3_round.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_divtf3. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.   Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt. 
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_divtf3_tail : CodeAtT img_segs (sym 0x1c6b0) (divtf3_prog_at IMG)}.
  Context {RB_divtf3_tail : RelCode (sym 0x1c6b0) 2308}.
  Collection ImgHyps := IMG CODE_divtf3_tail RB_divtf3_tail.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
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

Section Walk.
  Variables (sp sgw w6 : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation sgn := (bv_unsigned sgw).
  Notation bLo := (bv_unsigned w6).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
    | |- (_ <= _ <= _)%Z => lia
    | |- (0 <= _ < _)%Z => first [zrange2 | lia]
    end.
  Ltac join L := eapply L; try hyp.
  Ltac exact_HR :=
    lazymatch goal with |- ?g =>
      match goal with
      | HR : ?t |- _ => constr_eq t g; exact HR
      | HR : @eq Z ?r ?t |- _ => fail 0 "exact_HR: goal" g "but HR:" r "=" t
      end
    end.

  Ltac flag_join n G body K :=
    set (G := body);
    let w := getreg n in
    lazymatch w with Z_to_bv 64 ?e =>
      replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
        by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
    end;
    let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

  (* [comment removed for export] *)
  Lemma L6r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wE q1Hi q1Lo resHi resLo aDHi aDLo bHi : Z)
      y1 y5 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= q1Hi < 2^64)%Z -> (0 <= q1Lo < 2^64)%Z -> (0 <= resHi < 2^64)%Z -> (0 <= resLo < 2^64)%Z ->
    (0 <= aDHi < 2^64)%Z -> (0 <= aDLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
    (-100000 <= wE <= 32766)%Z ->
    R = DC6 sgn wE q1Hi q1Lo resHi resLo aDHi aDLo bHi bLo ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 (Z_to_bv 64 resLo) (Z_to_bv 64 resHi) y8 y9 y10 sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 aDLo)
               (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aDHi)
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q1Hi) (Z_to_bv 64 wE) (Z_to_bv 64 q1Lo) y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1172)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 RwE HR.
    pose_word_ranges.
    zstep. if_cases K; zify_cond K; sgn_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
      + join Lzero. rewrite HR. apply DC6_tiny. lia.
      + do 6 zstep. rewrite !subw_amt by lia. unland. rewrite !landM32_id by lia.
        zstep. if_cases K3; zify_cond K3; sgn_cond K3.
        * (* [comment removed for export] *)
          do 5 zstep. unland.
          model_reg 10 absLo (Z.lor (Z.shiftr q1Lo (Z.land (1 - wE) 63))
                                   (Z.land (Z.shiftl (Z.land (Z.shiftl q1Hi 1) 18446744073709551615) (Z.land (Z.lxor (1 - wE) 18446744073709551615) 63)) 18446744073709551615)).
          rng absLo.
          zstep. unland. model_reg 15 absHi0 (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absHi0.
          zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
          zstep. rewrite (srai63_mask (1 - wE + -64)) by lia. decide_ifs. rewrite land_ones_l by zrange2.
          zstep. if_cases K4; zify_cond K4; sgn_cond K4.
          -- (* [comment removed for export] *)
             do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
                                   (Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
              zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
              zstep.
              zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
              zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
              zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
              zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
              zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
              zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
              zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
              zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
              zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
              zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
              do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
              zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
              zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
              zstep. model_reg 17 odd (Z.land absLo 1).
              zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
              zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
              zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
              zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
              all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
              all: join Lround.
              all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                   rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
          -- (* [comment removed for export] *)
             do 2 zstep. unland. model_reg 17 aSHi (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615). rng aSHi.
              zstep. change (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615) with aSHi.
              zstep.
              zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
              zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
              zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
              zstep. rewrite !signed_of_Z by lia. rewrite (shr63_nonneg (wE + 48)), ?Z.land_0_l by lia.
              zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
              zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
              zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
              zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
              zstep. model_reg 6 bor (Z.b2z (0 <? qb2Lo)).
              zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
              do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
              zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
              zstep. model_reg 14 r2Lo (Z.land (0 - qb2Lo) 18446744073709551615).
              zstep. model_reg 17 odd (Z.land absLo 1).
              zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
              zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
              zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
              zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
              all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
              all: join Lround.
              all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                   rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
        * (* [comment removed for export] *)
          do 2 zstep. unland. model_reg 10 absLo (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absLo.
          zstep. unland.
          zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
          zstep. rewrite (shr63_nonneg (1 - wE + -64)), ?Z.land_0_l by lia.
          zstep. if_cases K4; zify_cond K4; sgn_cond K4; [ | exfalso; lia ].
          do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
                                   (Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
           zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
           zstep.
           zstep. model_reg 5 pb1 (Z.land (bLo * 0) 18446744073709551615).
           zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
           zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
           zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
           zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
           zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
           zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
           zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
           zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
           zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
           do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
           zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
           zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
           zstep. model_reg 17 odd (Z.land absLo 1).
           zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
           zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
           zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
           zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
           all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
           all: join Lround.
           all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
    - (* [comment removed for export] *)
      assert (K' : 0 < wE) by (rewrite land_W64 in K0, K1; Z.div_mod_to_equations; lia). clear K0 K1.
      do 2 zstep. unland.
      model_reg 14 fracHi (Z.land q1Hi 281474976710655).
      do 4 zstep. unland. model_reg 15 absHi (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi). rng absHi.
      zstep. model_reg 16 r2Hi (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)). rng r2Hi.
      zstep. model_reg 14 r2Lo (Z.land (Z.shiftl resLo 1) 18446744073709551615).
      zstep. model_reg 17 odd (Z.land q1Lo 1).
      zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
      zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
      zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
      zstep. if_cases K1; zify_cond K1; [ zstep | do 2 zstep ];
        flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1;
        (join Lround;
         rewrite HR, DC6_normal, div_round_DRr by lia; unland;
         change (Z.land q1Hi 281474976710655) with fracHi;
         change (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi) with absHi;
         change (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)) with r2Hi;
         change (Z.land (Z.shiftl resLo 1) 18446744073709551615) with r2Lo;
         fold_model_lets2; reflexivity).
  Time Qed.

  (* [comment removed for export] *)
  Lemma L5r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (w4 : word) (expM1 q_hi q_lo aSigHiI bSigHiI aHi2 aLoTop a2Lo : Z)
      y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= q_hi < 2^64)%Z -> (0 <= q_lo < 2^64)%Z -> (0 <= aSigHiI < 2^64)%Z -> (0 <= bSigHiI < 2^64)%Z ->
    (0 <= aHi2 < 2^64)%Z -> (0 <= aLoTop < 2^64)%Z -> (0 <= a2Lo < 2^64)%Z ->
    (-20000 <= expM1 <= 60000)%Z ->
    R = divc_tail sgn expM1 q_hi q_lo (bv_unsigned w4) aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 expM1) (Z_to_bv 64 aLoTop) (Z_to_bv 64 aHi2) y8 y9 w4 sgw w6
               (Z_to_bv 64 bSigHiI) (Z_to_bv 64 a2Lo) (Z_to_bv 64 (Z.shiftr q_hi 49)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aSigHiI)
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q_hi) (Z_to_bv 64 (expM1 + 1)) (Z_to_bv 64 q_lo) y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 856)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 Rexp HR.
    pose_word_ranges.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 3 zstep. model_reg 28 q1Hi (Z.shiftr q_hi 1). rng q1Hi.
      zstep. model_reg 5 aTop (Z.land (Z.shiftl (bv_unsigned w4) 48) 18446744073709551615).
      zstep. model_reg 30 q1Lo (Z.lor (Z.shiftr q_lo 1) (Z.land (Z.shiftl q_hi 63) 18446744073709551615)). rng q1Lo.
      zstep. model_reg 14 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
      zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
      zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
      zstep. model_reg 14 d1 (Z.land (aTop - pq1) 18446744073709551615).
      zstep. model_reg 5 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
      zstep. model_reg 15 sh (Z.land (pq3 + pq2) 18446744073709551615).
      zstep. model_reg 6 bor (Z.b2z (negb (qbLo =? 0))).
      zstep. model_reg 14 d2 (Z.land (d1 - sh) 18446744073709551615).
      zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
      zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
      do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
      + rewrite <- (Z_to_bv_bv_unsigned w4). join L6r. all: try lia.
        rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
      + join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
    - (* [comment removed for export] *)
      assert (Rbit : 0 <= Z.shiftr q_hi 48 <= 1).
      { rewrite !Z.shiftr_div_pow2 in * by lia. Z.div_mod_to_equations. lia. }
      zstep. name_as bit112 (Z.shiftr q_hi 48).
      zstep. zstep. rewrite (ltb1_eqb0 bit112) by lia. model_reg 31 sh (Z.b2z (bit112 =? 0)).
      assert (Rsh' : 0 <= sh <= 1) by (cbv delta [sh]; destruct (bit112 =? 0); cbn; lia).
      zstep. rewrite (land63_id sh) by lia.
      zstep. zstep.
      assert (Hamt : Z.land (Z.lxor sh 63) 63 = Z.lxor sh 63) by (cbv delta [sh]; destruct (bit112 =? 0); reflexivity).
      rewrite Hamt.
      zstep. unland. model_reg 28 q1Hi (Z.lor (Z.land (Z.shiftl q_hi sh) 18446744073709551615) (Z.shiftr (Z.shiftr q_lo 1) (Z.lxor sh 63))). rng q1Hi.
      zstep. rewrite (land63_id sh) by lia. model_reg 30 q1Lo (Z.land (Z.shiftl q_lo sh) 18446744073709551615).
      zstep. if_cases Kb; zify_cond Kb.
      * (* [comment removed for export] *)
        zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
        zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
        zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
        zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
        zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
        zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
        zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
        zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
        zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
        zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
        zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
        zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
        do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
        + (* [comment removed for export] *) join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
        + zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
      * (* [comment removed for export] *)
        zstep.
        zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
        zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
        zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
        zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
        zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
        zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
        zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
        zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
        zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
        zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
        zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
        zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
        do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
        + (* [comment removed for export] *) join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
        + zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
  Time Qed.

  (* [comment removed for export] *)
  Lemma divtf3_core : forall ra gp tp (w3 w4 w5 : word) (scale ea eb : Z) s0 s1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 y1
      y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    R = div_core sgn ea eb (bv_unsigned w3) (bv_unsigned w4) (bv_unsigned w5) bLo scale ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) y8 y9 w4 sgw w6 a3 a4 a5 (Z_to_bv 64 281474976710655) w3
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 scale) t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1c6b0 + 136)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Ra Rb Rsc HR.
    pose_word_ranges.
    eapply evt_cut. { eapply (divtf3_core12 w3 w4 w5 w6 ea eb scale); eauto. }
    intros ms' P.
    (nelim P 20%nat; intros q_hi q_lo z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z31 EQ Rqh Rql ->).
    rewrite EQ in HR.
    eapply L5r; try eassumption; try exact HR.
    all: try (cbv beta delta [E_aSigHiI E_bSigHiI E_aHi2 E_aLoTop E_a2Lo]; zrange).
    cbv beta delta [E_expM1]. lia.
  Qed.
End Walk.

End Img.
End G_divtf3_tail.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sf_helpers2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_f128_mul_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module G_divtf3_main.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_f128_mul_top OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_wide OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_core2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_f128_div_top.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_norm OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3_wide.G_divtf3_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_divtf3_wide G_divtf3_round G_divtf3_tail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_divtf3_norm.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.Prog_divtf3.   Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.ProgAt3.ProgAt. 
Import ListNotations.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_divtf3_main : CodeAtT img_segs (sym 0x1c6b0) (divtf3_prog_at IMG)}.
  Context {RB_divtf3_main : RelCode (sym 0x1c6b0) 2308}.
  Collection ImgHyps := IMG CODE_divtf3_main RB_divtf3_main.


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

Section Walk.
  Variables (sp a0 a1 a2 a3 : word).
  Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
  Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation E_sgn := (Z.land (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63) 18446744073709551615).
  Notation E_aExp := (Z.shiftr (Z.land (Z.shiftl a_hi 1) 18446744073709551615) 49).
  Notation E_bExp := (Z.shiftr (Z.land (Z.shiftl b_hi 1) 18446744073709551615) 49).
  Notation E_aSig := (Z.land a_hi 281474976710655).
  Notation E_bSig := (Z.land b_hi 281474976710655).
  Notation E_aAbs := (Z.land a_hi 9223372036854775807).
  Notation E_bAbs := (Z.land b_hi 9223372036854775807).
  Notation MONE := (Z_to_bv 64 (-1)).
  Notation M48 := (Z_to_bv 64 281474976710655).
  Notation EXPK := (Z_to_bv 64 (-32767)).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : bv_unsigned ?w = _ |- bv_unsigned ?w = _ => exact H
    | H : ?x = ?y |- ?x = ?y => exact H
    | H : ?x <> ?y |- ?x <> ?y => exact H
    | H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
    | |- (_ <= _ <= _)%Z => lia
    | |- (0 <= _ < _)%Z => first [zrange2 | lia]
    end.
  Ltac join L := eapply L; try hyp.
  (* [comment removed for export] *)
  Ltac model_in H := sf_model_in H.
  Ltac eblia := rewrite ?Z.shiftl_mul_pow2 in * by lia; blia.
  Ltac decide_in_cond H c :=
    match c with
    | context [Z.eqb ?x ?y] =>
        first [ rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia) ]
    | context [Z.ltb ?x ?y] =>
        first [ rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia) ]
    | context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia) ]
    end.
  Ltac decide_head H :=
    cbn_bool_in H;   (* [comment removed for export] *)
    lazymatch type of H with
    | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond H c end
    end;
    cbn_bool_in H.
  (* [comment removed for export] *)
  Ltac decide_in_cond_t H c :=
    match c with
    | context [Z.eqb ?x ?y] => rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia)
    | context [Z.ltb ?x ?y] => rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia)
    | context [Z.leb ?x ?y] => rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia)
    end.
  Ltac decide_in_cond_f H c :=
    match c with
    | context [Z.eqb ?x ?y] => rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia)
    | context [Z.ltb ?x ?y] => rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia)
    | context [Z.leb ?x ?y] => rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia)
    end.
  Ltac decide_head_t H := cbn_bool_in H;
    lazymatch type of H with | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond_t H c end end; cbn_bool_in H.
  Ltac decide_head_f H := cbn_bool_in H;
    lazymatch type of H with | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond_f H c end end; cbn_bool_in H.
  Ltac res_words := rewrite ?lo64_mk128, ?hi64_mk128 by zrange; first [ apply Z_to_bv_lit_self | weq ].
  Ltac exact_HR0 :=
    lazymatch goal with |- ?g =>
      match goal with
      | HR : ?t |- _ => constr_eq t g; exact HR
      | HR : @eq Z ?r ?t |- _ => fail 0 "exact_HR: goal" g "but HR:" r "=" t
      end
    end.
  Ltac exact_HR := rewrite ?unsigned_lit by zrange; cbv delta [INF_HI QNAN_HI QUIET_HI]; exact_HR0.

  (* [comment removed for export] *)
  Lemma Lbchk : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (sc1 : Z) w3 w4
      y1 y8 y9 y13 y28' y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    y28' = Z_to_bv 64 sc1 ->
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (-600 <= sc1 <= 16)%Z ->
    R = FD_p2b a_hi b_lo b_hi (bv_unsigned w3) (bv_unsigned w4) sc1 ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               w4 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 w3
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28' y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 2040)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros -> MI MU WM ST FR SPLO Rsc HR.
    pose_word_ranges.
    assert (Ra : 0 <= E_aExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    assert (Rb : 0 <= E_bExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    unfold FD_p2b in HR. model_in HR.
    zstep. zstep. if_cases K; zify_cond K; [ decide_head_f HR | decide_head_t HR ].
    - (* [comment removed for export] *)
      join divtf3_core; exact_HR.
    - rewrite norm_denormal_eta in HR. cbn_bool_in HR.
      eapply LnormB; [zrange | lia |]. intros.
      pose proof (nd_clz_range E_bSig b_lo).
      pose proof (nd_hi_range E_bSig b_lo ltac:(zrange)). pose proof (nd_lo_range E_bSig b_lo).
      join divtf3_core; rewrite ?unsigned_lit by first [assumption | zrange]; exact_HR.
  Qed.

  (* [comment removed for export] *)
  Lemma Lp2r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y8 y9 y13 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FD_p2 a_lo a_hi b_lo b_hi ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 (Z_to_bv 64 E_aSig)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1368)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FD_p2 in HR. model_in HR.
    zstep. zstep. if_cases K; zify_cond K; [ decide_head_f HR | decide_head_t HR ].
    - (* [comment removed for export] *)
      do 2 zstep. join Lbchk; [reflexivity | lia | exact_HR].
    - rewrite norm_denormal_eta in HR. cbn_bool_in HR.
      eapply LnormA; [zrange |]. intros.
      pose proof (nd_clz_range E_aSig a_lo).
      pose proof (nd_hi_range E_aSig a_lo ltac:(zrange)). pose proof (nd_lo_range E_aSig a_lo).
      join Lbchk; [reflexivity | lia | rewrite ?unsigned_lit by first [assumption | zrange]; exact_HR].
  Qed.

  (* [comment removed for export] *)
  Lemma Linfr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y8 y9 y13 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FD_inf a_lo a_hi b_lo b_hi ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 (Z_to_bv 64 E_aSig)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1024)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FD_inf in HR. model_in HR.
    do 4 zstep. zstep. if_cases K7; zify_cond K7; [ decide_head_f HR | decide_head_t HR ].
    - (* [comment removed for export] *)
      do 2 zstep. zstep. if_cases K9; zify_cond K9; [ decide_head_f HR | decide_head_t HR ].
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K11; zify_cond K11; [ decide_head_t HR | decide_head_f HR ].
        * (* [comment removed for export] *) zstep. zstep. if_cases K12; zify_cond K12; [ decide_head_f HR | decide_head_t HR ].
          -- join Lzero; exact_HR.
          -- do 3 zstep. join Lzero. all: zsimp; exact_HR.
        * zstep. zstep. if_cases K12; zify_cond K12; [ decide_head_t HR | decide_head_f HR ].
          -- (* [comment removed for export] *) join Linf; exact_HR.
          -- join Lp2r; exact_HR.
      + (* [comment removed for export] *) join Lzero; exact_HR.
    - (* [comment removed for export] *)
      do 2 zstep. zstep. if_cases K8; zify_cond K8; [ decide_head_f HR | decide_head_t HR ].
      + join Linf; exact_HR.
      + subst R. do 4 zstep. join Lepi; res_words.
  Qed.

  (* [comment removed for export] *)
  Lemma Lbr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y8 y9 y14 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FD_b a_lo a_hi b_lo b_hi ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 a3 y14 MONE M48 (Z_to_bv 64 E_aSig)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) (Z_to_bv 64 9223372036854775807) y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 1000)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FD_b in HR. model_in HR.
    do 3 zstep. zstep. if_cases K5; zify_cond K5; [ decide_head_t HR | decide_head_f HR ].
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K6; zify_cond K6; [ decide_head_t HR | decide_head_f HR ].
      + (* [comment removed for export] *) join Linfr; exact_HR.
      + subst R. do 5 zstep. join Lepi; res_words.
    - zstep. zstep. if_cases K6; zify_cond K6; [ decide_head_f HR | decide_head_t HR ].
      + (* [comment removed for export] *) subst R. do 5 zstep. join Lepi; res_words.
      + join Linfr; exact_HR.
  Qed.

  (* [comment removed for export] *)
  Lemma Lspec : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y8 y9 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv img_segs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells img_segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FD_a a_lo a_hi b_lo b_hi ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 a3 a1 MONE M48 (Z_to_bv 64 E_aSig)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 (sym 0x1c6b0 + 972)) fc None m1 (seg_rom img_segs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FD_a in HR. model_in HR.
    do 4 zstep. zstep. if_cases K3; zify_cond K3; [ decide_head_t HR | decide_head_f HR ].
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K4; zify_cond K4; [ decide_head_t HR | decide_head_f HR ].
      + join Lbr; exact_HR.
      + subst R. do 4 zstep. join Lepi; res_words.
    - zstep. zstep. if_cases K4; zify_cond K4; [ decide_head_f HR | decide_head_t HR ].
      + subst R. do 4 zstep. join Lepi; res_words.
      + join Lbr; exact_HR.
  Qed.

  (* [comment removed for export] *)
  Lemma divtf3_walk : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte),
    stk img_segs m (bv_unsigned sp - 112) (bv_unsigned sp) ->
    mem_inv img_segs m ->
    (4096 <= bv_unsigned sp)%Z ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (f128_div_w a_lo a_hi b_lo b_hi) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1c6b0)) fc None m (seg_rom img_segs)).
  Proof.
    intros until m. intros ST MI SPLO.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl img_segs m) as WM.
    pose_word_ranges.
    carve_frame 112%nat ST.
    remember (f128_div_w a_lo a_hi b_lo b_hi) as R eqn:HR.
    unfold f128_div_w in HR. model_in HR.
    do 14 zstep. do 16 zstep.
    rewrite <- (Z_to_bv_land64 (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63)).
    assert (Ra : 0 <= E_aExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    assert (Rb : 0 <= E_bExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
   
    zstep. if_cases K1; zify_cond K1; [ decide_head_t HR | decide_head_f HR ].
    - (* [comment removed for export] *) join Lspec; exact_HR.
    - unfold FD_0b in HR. model_in HR.
      zstep. zstep. if_cases K2; zify_cond K2; [ decide_head_t HR | decide_head_f HR ].
      + join Lspec; exact_HR.
      + zstep. join divtf3_core; exact_HR.
  Qed.
End Walk.

(* [comment removed for export] *)
Theorem divtf3_spec : divtf3_stmt.
Proof.
  unfold divtf3_stmt. intros.
  rewrite f128_div_words by (pose_word_ranges; assumption).
  apply divtf3_walk; assumption.
Qed.

(* [comment removed for export] *)
Definition divtf3_spec_c : Prop := divtf3_stmt.
Lemma divtf3_spec_c_ok : divtf3_spec_c.
Proof. exact divtf3_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class divtf3_spec_c.
End G_divtf3_main.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FmtFp FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3_tail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_multf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_divtf3.
Import G_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_letf2 G_floatsitf G_fpclassifyl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pop_arg.G_extenddftf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
Definition fmodl_prog (B B_floatsitf B_letf2 B_multf3 B_divtf3 B_fpclassifyl B_200dc : Z) : RStep.ptree :=
  PNode 364%Z
  (PNode 180%Z
    (PNode 88%Z
      (PNode 44%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 0 2 2 4016 4
            (PJ_Store_SZ8_nnn 4 2 1 72 4
            (PJ_Store_SZ8_nnn 8 2 8 64 4
            (PJ_Store_SZ8_nnn 12 2 9 56 4
            (PJ_Store_SZ8_nnn 16 2 18 48 4
            (PJ_Store_SZ8_nnn 20 2 19 40 4
            (PJ_Store_SZ8_nnn 24 2 20 32 4
            (PJ_Store_SZ8_nnn 28 2 21 24 4
            (PJ_Store_SZ8_nnn 32 2 22 16 4
            (PJ_Store_SZ8_nnn 36 2 23 8 4
            (PJ_Store_SZ8_nnn 40 2 24 0 4 nil))))))))))))
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 44 19 13 0 4
            (PJ_OpImm_ALU_ADD_nnn 48 18 12 0 4
            (PJ_OpImm_ALU_ADD_nnn 52 8 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 56 9 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 60 10 0 0 4
            (PJ_Jal_nt 64 1 (jimm21 (B_floatsitf - (B + 64))) 4
            (PJ_OpImm_ALU_ADD_nnn 68 12 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 72 13 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 76 10 18 0 4
            (PJ_OpImm_ALU_ADD_nnn 80 11 19 0 4
            (PJ_Jal_nt 84 1 (jimm21 (B_letf2 - (B + 84))) 4 nil)))))))))))))
      (PNode 132%Z
        (PLeaf
            (PJ_Branch_BC_NE_nnn 88 10 0 84 4
            (PJ_OpImm_ALU_ADD_nnn 92 10 9 0 4
            (PJ_OpImm_ALU_ADD_nnn 96 11 8 0 4
            (PJ_OpImm_ALU_ADD_nnn 100 12 18 0 4
            (PJ_OpImm_ALU_ADD_nnn 104 13 19 0 4
            (PJ_Jal_nt 108 1 (jimm21 (B_multf3 - (B + 108))) 4
            (PJ_OpImm_ALU_ADD_nnn 112 12 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 116 13 11 0 4
            (PJ_Jal_nt 120 1 (jimm21 (B_divtf3 - (B + 120))) 4
            (PJ_Load_SZ8_true_nnn 124 1 2 72 4
            (PJ_Load_SZ8_true_nnn 128 8 2 64 4 nil))))))))))))
        (PLeaf
            (PJ_Load_SZ8_true_nnn 132 9 2 56 4
            (PJ_Load_SZ8_true_nnn 136 18 2 48 4
            (PJ_Load_SZ8_true_nnn 140 19 2 40 4
            (PJ_Load_SZ8_true_nnn 144 20 2 32 4
            (PJ_Load_SZ8_true_nnn 148 21 2 24 4
            (PJ_Load_SZ8_true_nnn 152 22 2 16 4
            (PJ_Load_SZ8_true_nnn 156 23 2 8 4
            (PJ_Load_SZ8_true_nnn 160 24 2 0 4
            (PJ_OpImm_ALU_ADD_nnn 164 2 2 80 4
            (PJ_Jalr_nnn 168 0 1 0 4
            (PJ_OpImm_ALU_ADD_nnn 172 10 18 0 4
            (PJ_OpImm_ALU_ADD_nnn 176 11 19 0 4 nil)))))))))))))))
    (PNode 272%Z
      (PNode 224%Z
        (PLeaf
            (PJ_Jal_nt 180 1 (jimm21 (B_fpclassifyl - (B + 180))) 4
            (PJ_Branch_BC_EQ_nnn 184 10 0 8100 4
            (PJ_ShiftImm_ALU_SRL_nnn 188 22 8 48 4
            (PJ_Lui_nn 192 10 8 4
            (PJ_ShiftImm_ALU_SLL_nnn 196 11 22 49 4
            (PJ_ShiftImm_ALU_SRL_nnn 200 23 11 49 4
            (PJ_OpImm32_nnn 204 10 10 4095 4
            (PJ_Branch_BC_EQ_nnn 208 23 10 8076 4
            (PJ_OpImm_ALU_ADD_nnn 212 10 0 4095 4
            (PJ_ShiftImm_ALU_SRL_nnn 216 10 10 1 4
            (PJ_Op_ALU_AND_nnn 220 21 8 10 4 nil))))))))))))
        (PLeaf
            (PJ_Op_ALU_AND_nnn 224 20 19 10 4
            (PJ_OpImm_ALU_ADD_nnn 228 10 9 0 4
            (PJ_OpImm_ALU_ADD_nnn 232 11 21 0 4
            (PJ_OpImm_ALU_ADD_nnn 236 12 18 0 4
            (PJ_OpImm_ALU_ADD_nnn 240 13 20 0 4
            (PJ_Jal_nt 244 1 (jimm21 (B_letf2 - (B + 244))) 4
            (PJ_Branch_BC_LT_nnn 248 0 10 32 4
            (PJ_OpImm_ALU_ADD_nnn 252 10 9 0 4
            (PJ_OpImm_ALU_ADD_nnn 256 11 21 0 4
            (PJ_OpImm_ALU_ADD_nnn 260 12 18 0 4
            (PJ_OpImm_ALU_ADD_nnn 264 13 20 0 4
            (PJ_Jal_nt 268 1 (jimm21 (B_letf2 - (B + 268))) 4 nil))))))))))))))
      (PNode 316%Z
        (PLeaf
            (PJ_Branch_BC_EQ_nnn 272 10 0 272 4
            (PJ_Jal_nn 276 0 380 4
            (PJ_ShiftImm_ALU_SLL_nnn 280 19 19 1 4
            (PJ_ShiftImm_ALU_SRL_nnn 284 24 19 49 4
            (PJ_Branch_BC_EQ_nnn 288 23 0 164 4
            (PJ_OpImm_ALU_ADD_nnn 292 19 9 0 4
            (PJ_Branch_BC_NE_nnn 296 24 0 52 4
            (PJ_Lui_nn 300 10 505856 4
            (PJ_Fmv_FMV_F_X_FMT_S_nn 304 10 10 4
            (PJ_Jal_nt 308 1 (jimm21 (B_200dc - (B + 308))) 4
            (PJ_OpImm_ALU_ADD_nnn 312 12 10 0 4 nil))))))))))))
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 316 13 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 320 10 18 0 4
            (PJ_OpImm_ALU_ADD_nnn 324 11 20 0 4
            (PJ_Jal_nt 328 1 (jimm21 (B_multf3 - (B + 328))) 4
            (PJ_OpImm_ALU_ADD_nnn 332 18 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 336 20 11 0 4
            (PJ_ShiftImm_ALU_SRL_nnn 340 10 11 48 4
            (PJ_OpImm_ALU_ADD_nnn 344 24 10 3976 4
            (PJ_OpImm_ALU_ADD_nnn 348 10 0 4095 4
            (PJ_ShiftImm_ALU_SRL_nnn 352 10 10 16 4
            (PJ_Op_ALU_AND_nnn 356 11 21 10 4
            (PJ_OpImm_ALU_ADD_nnn 360 12 10 1 4 nil))))))))))))))))
  (PNode 548%Z
    (PNode 456%Z
      (PNode 408%Z
        (PLeaf
            (PJ_Op_ALU_AND_nnn 364 10 20 10 4
            (PJ_Op_ALU_OR_nnn 368 11 11 12 4
            (PJ_Op_ALU_OR_nnn 372 10 10 12 4
            (PJ_Branch_BC_LT_nnn 376 24 23 32 4
            (PJ_Jal_nn 380 0 132 4
            (PJ_ShiftImm_ALU_SRL_nnn 384 12 19 63 4
            (PJ_ShiftImm_ALU_SLL_nnn 388 11 11 1 4
            (PJ_Op_ALU_OR_nnn 392 11 11 12 4
            (PJ_OpImm32_nnn 396 23 23 4095 4
            (PJ_ShiftImm_ALU_SLL_nnn 400 19 19 1 4
            (PJ_Branch_BC_GE_nnn 404 24 23 104 4 nil))))))))))))
        (PLeaf
            (PJ_Op_ALU_SUB_nnn 408 12 11 10 4
            (PJ_Op_ALU_SLTU_nnn 412 13 19 18 4
            (PJ_Op_ALU_SUB_nnn 416 12 12 13 4
            (PJ_Branch_BC_LT_nnn 420 12 0 8156 4
            (PJ_Op_ALU_SUB_nnn 424 19 19 18 4
            (PJ_Op_ALU_OR_nnn 428 11 12 19 4
            (PJ_Branch_BC_EQ_nnn 432 11 0 108 4
            (PJ_ShiftImm_ALU_SRL_nnn 436 11 19 63 4
            (PJ_ShiftImm_ALU_SLL_nnn 440 12 12 1 4
            (PJ_Op_ALU_OR_nnn 444 11 12 11 4
            (PJ_Jal_nn 448 0 2097100 4
            (PJ_Lui_nn 452 10 505856 4 nil))))))))))))))
      (PNode 500%Z
        (PLeaf
            (PJ_Fmv_FMV_F_X_FMT_S_nn 456 10 10 4
            (PJ_Jal_nt 460 1 (jimm21 (B_200dc - (B + 460))) 4
            (PJ_OpImm_ALU_ADD_nnn 464 12 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 468 13 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 472 10 9 0 4
            (PJ_OpImm_ALU_ADD_nnn 476 11 21 0 4
            (PJ_Jal_nt 480 1 (jimm21 (B_multf3 - (B + 480))) 4
            (PJ_OpImm_ALU_ADD_nnn 484 19 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 488 21 11 0 4
            (PJ_ShiftImm_ALU_SRL_nnn 492 10 11 48 4
            (PJ_OpImm_ALU_ADD_nnn 496 23 10 3976 4 nil))))))))))))
        (PLeaf
            (PJ_Branch_BC_NE_nnn 500 24 0 8040 4
            (PJ_Jal_nn 504 0 2096948 4
            (PJ_OpImm_ALU_ADD_nnn 508 23 24 0 4
            (PJ_Op_ALU_SUB_nnn 512 10 11 10 4
            (PJ_Op_ALU_SLTU_nnn 516 12 19 18 4
            (PJ_Op_ALU_SUB_nnn 520 10 10 12 4
            (PJ_Branch_BC_LT_nnn 524 10 0 40 4
            (PJ_Op_ALU_SUB_nnn 528 19 19 18 4
            (PJ_Op_ALU_OR_nnn 532 11 10 19 4
            (PJ_Branch_BC_NE_nnn 536 11 0 32 4
            (PJ_OpImm_ALU_ADD_nnn 540 10 0 0 4
            (PJ_Jal_nt 544 1 (jimm21 (B_floatsitf - (B + 544))) 4 nil)))))))))))))))
    (PNode 640%Z
      (PNode 592%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 548 12 9 0 4
            (PJ_OpImm_ALU_ADD_nnn 552 13 8 0 4
            (PJ_Jal_nt 556 1 (jimm21 (B_multf3 - (B + 556))) 4
            (PJ_Jal_nn 560 0 2096716 4
            (PJ_OpImm_ALU_ADD_nnn 564 10 11 0 4
            (PJ_ShiftImm_ALU_SRL_nnn 568 12 10 48 4
            (PJ_Lui_nn 572 11 8 4
            (PJ_Branch_BC_NE_nnn 576 12 0 32 4
            (PJ_ShiftImm_ALU_SRL_nnn 580 12 19 63 4
            (PJ_ShiftImm_ALU_SLL_nnn 584 13 10 1 4
            (PJ_ShiftImm_ALU_SLL_nnn 588 19 19 1 4 nil))))))))))))
        (PLeaf
            (PJ_Op_ALU_OR_nnn 592 10 13 12 4
            (PJ_ShiftImm_ALU_SRL_nnn 596 13 13 48 4
            (PJ_OpImm32_nnn 600 23 23 4095 4
            (PJ_Branch_BC_EQ_nnn 604 13 0 8168 4
            (PJ_Op_ALU_AND_nnn 608 11 22 11 4
            (PJ_OpImm_ALU_ADD_nnn 612 13 0 4095 4
            (PJ_Lui_nn 616 14 16 4
            (PJ_ShiftImm_ALU_SRL_nnn 620 12 13 16 4
            (PJ_OpImm_ALU_ADD_nnn 624 14 14 4095 4
            (PJ_Branch_BC_GE_nnn 628 0 23 40 4
            (PJ_Op_ALU_AND_nnn 632 14 23 14 4
            (PJ_Op_ALU_AND_nnn 636 9 19 13 4 nil))))))))))))))
      (PNode 684%Z
        (PLeaf
            (PJ_Op_ALU_OR_nnn 640 11 14 11 4
            (PJ_ShiftImm_ALU_SLL_nnn 644 11 11 48 4
            (PJ_Op_ALU_AND_nnn 648 10 10 12 4
            (PJ_Op_ALU_OR_nnn 652 8 10 11 4
            (PJ_OpImm_ALU_ADD_nnn 656 10 9 0 4
            (PJ_OpImm_ALU_ADD_nnn 660 11 8 0 4
            (PJ_Jal_nn 664 0 2096612 4
            (PJ_OpImm_ALU_ADD_nnn 668 15 23 120 4
            (PJ_Op_ALU_AND_nnn 672 8 19 13 4
            (PJ_Op_ALU_AND_nnn 676 14 15 14 4
            (PJ_Op_ALU_OR_nnn 680 11 14 11 4 nil))))))))))))
        (PLeaf
            (PJ_ShiftImm_ALU_SLL_nnn 684 11 11 48 4
            (PJ_Op_ALU_AND_nnn 688 10 10 12 4
            (PJ_Op_ALU_OR_nnn 692 9 10 11 4
            (PJ_Lui_nn 696 10 14336 4
            (PJ_Fmv_FMV_F_X_FMT_S_nn 700 10 10 4
            (PJ_Jal_nt 704 1 (jimm21 (B_200dc - (B + 704))) 4
            (PJ_OpImm_ALU_ADD_nnn 708 12 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 712 13 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 716 10 8 0 4
            (PJ_OpImm_ALU_ADD_nnn 720 11 9 0 4
            (PJ_Jal_nt 724 1 (jimm21 (B_multf3 - (B + 724))) 4
            (PJ_Jal_nn 728 0 2096548 4 nil)))))))))))))))).

(* [comment removed for export] *)
Definition fmodl_prog_r1 (B : Z) : RStep.ptree :=
  PNode 172%Z
  (PNode 84%Z
    (PNode 40%Z
      (PLeaf
          (PJ_Fmv_FMV_X_F_FMT_S_nn 0 11 10 4
          (PJ_ShiftImm32_ALU_SRL_nnn 4 10 11 23 4
          (PJ_ShiftImm_ALU_SLL_nnn 8 12 11 41 4
          (PJ_OpImm_ALU_AND_nnn 12 13 10 255 4
          (PJ_ShiftImm_ALU_SRL_nnn 16 12 12 41 4
          (PJ_Branch_BC_EQ_nnn 20 13 0 52 4
          (PJ_OpImm_ALU_ADD_nnn 24 10 0 255 4
          (PJ_Branch_BC_NE_nnn 28 13 10 252 4
          (PJ_OpImm_ALU_ADD_nnn 32 10 0 0 4
          (PJ_ShiftImm_ALU_SLL_nnn 36 12 12 25 4 nil)))))))))))
      (PLeaf
          (PJ_Lui_nn 40 13 8 4
          (PJ_OpImm_ALU_ADD_nnn 44 13 13 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 48 11 11 31 4
          (PJ_ShiftImm_ALU_SLL_nnn 52 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 56 13 13 48 4
          (PJ_Op_ALU_OR_nnn 60 11 13 11 4
          (PJ_Op_ALU_OR_nnn 64 11 11 12 4
          (PJ_Jalr_nnn 68 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 72 10 0 0 4
          (PJ_Branch_BC_EQ_nnn 76 12 0 248 4
          (PJ_ShiftImm_ALU_SRL_nnn 80 13 12 1 4 nil)))))))))))))
    (PNode 128%Z
      (PLeaf
          (PJ_Op_ALU_OR_nnn 84 13 12 13 4
          (PJ_ShiftImm_ALU_SRL_nnn 88 14 13 2 4
          (PJ_Op_ALU_OR_nnn 92 13 13 14 4
          (PJ_ShiftImm_ALU_SRL_nnn 96 14 13 4 4
          (PJ_Op_ALU_OR_nnn 100 13 13 14 4
          (PJ_ShiftImm_ALU_SLL_nnn 104 14 13 41 4
          (PJ_ShiftImm_ALU_SRL_nnn 108 15 14 49 4
          (PJ_Op_ALU_OR_nnn 112 13 13 15 4
          (PJ_Lui_nn 116 15 349525 4
          (PJ_OpImm32_nnn 120 15 15 1365 4
          (PJ_ShiftImm_ALU_SRL_nnn 124 14 14 57 4 nil))))))))))))
      (PLeaf
          (PJ_Op_ALU_OR_nnn 128 13 13 14 4
          (PJ_OpImm_ALU_XOR_nnn 132 13 13 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 136 14 13 1 4
          (PJ_Op_ALU_AND_nnn 140 14 14 15 4
          (PJ_Lui_nn 144 15 209715 4
          (PJ_OpImm32_nnn 148 15 15 819 4
          (PJ_Op_ALU_SUB_nnn 152 13 13 14 4
          (PJ_Op_ALU_AND_nnn 156 14 13 15 4
          (PJ_ShiftImm_ALU_SRL_nnn 160 13 13 2 4
          (PJ_Op_ALU_AND_nnn 164 13 13 15 4
          (PJ_Op_ALU_ADD_nnn 168 13 14 13 4 nil))))))))))))))
  (PNode 260%Z
    (PNode 216%Z
      (PLeaf
          (PJ_ShiftImm_ALU_SRL_nnn 172 14 13 4 4
          (PJ_Op_ALU_ADD_nnn 176 13 13 14 4
          (PJ_Lui_nn 180 14 61681 4
          (PJ_OpImm_ALU_ADD_nnn 184 14 14 3855 4
          (PJ_Op_ALU_AND_nnn 188 13 13 14 4
          (PJ_Lui_nn 192 14 4112 4
          (PJ_OpImm_ALU_ADD_nnn 196 14 14 257 4
          (PJ_Mul_M_MUL_nnn 200 13 13 14 4
          (PJ_Lui_nn 204 14 4 4
          (PJ_OpImm_ALU_ADD_nnn 208 14 14 3968 4
          (PJ_ShiftImm32_ALU_SRL_nnn 212 13 13 24 4 nil))))))))))))
      (PLeaf
          (PJ_Op_ALU_SUB_nnn 216 14 14 13 4
          (PJ_OpImm_ALU_ADD_nnn 220 13 13 17 4
          (PJ_Op_ALU_SLL_nnn 224 12 12 13 4
          (PJ_OpImm_ALU_SLT_nnn 228 13 13 0 4
          (PJ_OpImm_ALU_ADD_nnn 232 13 13 4095 4
          (PJ_Op_ALU_AND_nnn 236 12 13 12 4
          (PJ_OpImm_ALU_ADD_nnn 240 15 0 1 4
          (PJ_OpImm_ALU_ADD_nnn 244 13 14 9 4
          (PJ_ShiftImm_ALU_SLL_nnn 248 15 15 48 4
          (PJ_Op_ALU_XOR_nnn 252 12 12 15 4
          (PJ_ShiftImm_ALU_SRL_nnn 256 11 11 31 4 nil)))))))))))))
    (PNode 304%Z
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 260 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 264 13 13 48 4
          (PJ_Op_ALU_OR_nnn 268 11 13 11 4
          (PJ_Op_ALU_OR_nnn 272 11 11 12 4
          (PJ_Jalr_nnn 276 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 280 10 0 0 4
          (PJ_Lui_nn 284 14 4 4
          (PJ_OpImm_ALU_ADD_nnn 288 14 14 3968 4
          (PJ_Op_ALU_ADD_nnn 292 13 13 14 4
          (PJ_ShiftImm_ALU_SLL_nnn 296 12 12 25 4
          (PJ_ShiftImm_ALU_SRL_nnn 300 11 11 31 4 nil))))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 304 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 308 13 13 48 4
          (PJ_Op_ALU_OR_nnn 312 11 13 11 4
          (PJ_Op_ALU_OR_nnn 316 11 11 12 4
          (PJ_Jalr_nnn 320 0 1 0 4
          (PJ_ShiftImm_ALU_SRL_nnn 324 11 11 31 4
          (PJ_ShiftImm_ALU_SLL_nnn 328 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 332 13 0 48 4
          (PJ_Op_ALU_OR_nnn 336 11 13 11 4
          (PJ_Op_ALU_OR_nnn 340 11 11 12 4
          (PJ_Jalr_nnn 344 0 1 0 4 nil)))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m. (* [comment removed for export] *) Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_fmodl (IMG : RImg) := fmodl_prog (sym 0x20260) (sym 0x1bad0) (sym 0x1b24c) (sym 0x1b3d0) (sym 0x1c6b0) (sym 0x1b130) (sym 0x200dc).
Definition PROGAT_CODE_fmodl_1 (IMG : RImg) := fmodl_prog_r1 (sym 0x200dc).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_fmodl : CodeAtT img_segs (sym 0x20260) (PROGAT_CODE_fmodl IMG)}.
  Context {RB_fmodl : RelCode (sym 0x20260) 732}.
  Context {CODE_fmodl_1 : CodeAtT img_segs (sym 0x200dc) (PROGAT_CODE_fmodl_1 IMG)}.
  Context {RB_fmodl_1 : RelCode (sym 0x200dc) 348}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_floatsitf_20260 : GLRN 0x20260 0x1bad0}.
  Context {RN_B_letf2_20260 : GLRN 0x20260 0x1b24c}.
  Context {RN_B_multf3_20260 : GLRN 0x20260 0x1b3d0}.
  Context {RN_B_divtf3_20260 : GLRN 0x20260 0x1c6b0}.
  Context {RN_B_fpclassifyl_20260 : GLRN 0x20260 0x1b130}.
  Context {RN_B_200dc_20260 : GLRN 0x20260 0x200dc}.
  Context {SPEC_fpclassifyl : fpclassifyl_contract}.
  Context {SPEC_multf3_callq : multf3_callq_c}.
  Context {SPEC_letf2_callv : letf2_callv_c}.
  Context {SPEC_floatsitf_callv : floatsitf_callv_c}.
  Context {SPEC_divtf3_callq : divtf3_callq_c}.
  Context {SPEC_divtf3_spec : divtf3_spec_c}.
  Collection ImgHyps := IMG CODE_fmodl RB_fmodl CODE_fmodl_1 RB_fmodl_1 RN_B_floatsitf_20260 RN_B_letf2_20260 RN_B_multf3_20260 RN_B_divtf3_20260 RN_B_fpclassifyl_20260 RN_B_200dc_20260 SPEC_fpclassifyl SPEC_multf3_callq SPEC_letf2_callv SPEC_floatsitf_callv SPEC_divtf3_callq SPEC_divtf3_spec.


(* [comment removed for export] *)

Definition FMODL : Z := (sym 0x20260).
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
             F (ret_pc ra) fc None m (seg_rom img_segs)
    /\ munch [] m m /\ wmono img_segs m m /\ mem_inv img_segs m.

Lemma extendsftf2_2p120 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (extsf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 18446744071486570496) F) fc C_2P120 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        (bvmap_set 10 (Z_to_bv 64 18446744071486570496) F) (Z_to_bv 64 (sym 0x200dc)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI.
  zs. lit_loads. zs. zs. zs. zs. zs.
  br K1; try (exfalso; clear -K1; cbv in K1; lia).
  zs. zs. br K2; try (exfalso; clear -K2; cbv in K2; lia).
  do 11 zs.
  apply evt_done. unfold extsf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma extendsftf2_2pm120 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (extsf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 18446744069473304576) F) fc C_2PM120 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        (bvmap_set 10 (Z_to_bv 64 18446744069473304576) F) (Z_to_bv 64 (sym 0x200dc)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI.
  zs. lit_loads. zs. zs. zs. zs. zs.
  br K1; try (exfalso; clear -K1; cbv in K1; lia).
  zs. zs. br K2; try (exfalso; clear -K2; cbv in K2; lia).
  do 11 zs.
  apply evt_done. unfold extsf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma m_fpclassifyl_canon : forall y, fpclassifyl (lo64 y + 2^64 * hi64 y) = m_fpclassifyl y.
Proof.
  intros y. unfold fpclassifyl, m_fpclassifyl. change (lo64 y + 2^64 * hi64 y)%Z with (canon y).
  rewrite lo64_canon, hi64_canon. unfold nz. reflexivity.
Qed.

Definition rfmodl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - RFMODL_DEPTH, q)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - RFMODL_DEPTH) q
    /\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k).

Definition rfmodl_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X Y r : Z),
  stk img_segs m (q - RFMODL_DEPTH) q -> mem_inv img_segs m ->
  (4096 <= q - RFMODL_DEPTH)%Z -> (q < 2^63)%Z ->
  m_fmodl X Y = Some r ->
  evt img_segs (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FMODL) fc None m (seg_rom img_segs)).

Section Fmodl.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (X Y r : Z).
  Hypothesis SPLO : (4096 <= q - RFMODL_DEPTH)%Z.
  Hypothesis SPHI : (q < 2^63)%Z.
  Hypothesis HM : m_fmodl X Y = Some r.

  Notation POST := (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m0).
  Notation SPv := (Z_to_bv 64 (q + -80)).
  Definition frame : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) : Prop :=
    mem_inv img_segs m /\ munch [(q - RFMODL_DEPTH, q)]%Z m0 m /\ wmono img_segs m0 m
    /\ rw_cells img_segs m (q + -80) frame /\ stk img_segs m (q - RFMODL_DEPTH) (q + -80).
  Ltac dest_finv H := (nelim H 5%nat; intros MI MU WM FR ST); unfold frame in FR; unfold RFMODL_DEPTH in MU, ST.
  Ltac mk_finv := unfold finv, frame, RFMODL_DEPTH; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|hyp].
  (* [comment removed for export] *)
  Definition Fok (F' : bvmap 5 word) : Prop := forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k.
  Lemma Fok_refl : Fok F. Proof. intros k _. reflexivity. Qed.
  Lemma Fok_set10 : forall F' v, Fok F' -> Fok (bvmap_set 10 v F').
  Proof. intros F' v H k Hk. rewrite reg_get_set_other by (intros E; apply Hk; rewrite <- E; reflexivity). apply H. exact Hk. Qed.

  Definition exv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x7fff.
  Definition eyv : Z := Z.land (Z.shiftr (hi64 Y) 48) 0x7fff.
  Definition sxv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x8000.

  (* [comment removed for export] *)
  Lemma L_ret : forall m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
    finv m -> Fok F' ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 124)) fc None m (seg_rom img_segs)).
  Proof.
    intros until x1. intros FI FOK. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
    do 12 zs.
    release_frame FR ST q.
    apply evt_done. unfold rfmodl_post, RFMODL_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST | exact FOK].
  Qed.

  Definition DS : divtf3_stmt := SPEC_divtf3_spec.
  Lemma stk_lower : forall m lo lo' hi, stk img_segs m lo hi -> (lo <= lo' <= hi)%Z -> stk img_segs m lo' hi.
  Proof. intros m lo lo' hi ST H. exact (proj2 (stk_split _ _ _ _ _ ST H)). Qed.
  (* [comment removed for export] *)
  Tactic Notation "call_split" constr(K) tactic3(tac) :=
    lazymatch goal with ST : stk _ ?m (q - 192)%Z (q + -80)%Z |- _ =>
      let ST1 := fresh "ST1" in let ST2 := fresh "ST2" in
      destruct (stk_split _ _ _ (q + -80 - K)%Z _ ST ltac:(lia)) as [ST1 ST2]; clear ST;
      callw tac;
      lazymatch goal with STn : stk _ ?m' (q + -80 - K)%Z (q + -80)%Z |- _ =>
        pose proof (stk_merge _ _ _ _ _ ST1 STn ltac:(lia)) as ST; clear ST1 STn end
    end.

  (* [comment removed for export] *)
  Lemma L_nan : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
    finv m -> Fok F' -> r = f128_div (f128_mul X Y) (f128_mul X Y) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 92)) fc None m (seg_rom img_segs)).
  Proof.
    intros until x1. intros FI FOK Hr. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
    zs. zs. zs. zs.
    zs. call_split 80%Z (eapply SPEC_multf3_callq; [hyp | hyp | lia]).
    zs. zs.
    zs. call_split 112%Z (eapply (SPEC_divtf3_callq DS); [hyp | hyp | lia]).
    rewrite <- Hr. apply L_ret; [mk_finv | exact FOK].
  Qed.

  (* [comment removed for export] *)
  Lemma L_zero : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
    finv m -> Fok F' -> r = f128_mul (f128_of_i32 0) X ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 544)) fc None m (seg_rom img_segs)).
  Proof.
    intros until x1. intros FI FOK Hr. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
    zs. callw (eapply SPEC_floatsitf_callv with (v := 0%Z) (i := 0%Z); [hyp | lia | reflexivity]).
    zs. zs.
    zs. call_split 80%Z (eapply SPEC_multf3_callq; [hyp | hyp | lia]).
    zs. rewrite <- Hr. apply L_ret; [mk_finv | exact FOK].
  Qed.

  (* [comment removed for export] *)
  Lemma L_retx : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1 lo hi,
    finv m -> Fok F' -> Z_to_bv 64 lo = Z_to_bv 64 (lo64 r) -> Z_to_bv 64 hi = Z_to_bv 64 (hi64 r) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 656)) fc None m (seg_rom img_segs)).
  Proof.
    intros until hi. intros FI FOK Hlo Hhi. pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
    zs. zs. zs. rewrite Hlo, Hhi. apply L_ret; [exact FI | exact FOK].
  Qed.

  Lemma sxv_cases : sxv = 0%Z \/ sxv = 32768%Z.
  Proof. unfold sxv. change 32768%Z with (2^15)%Z. rewrite land_pow2_bit by lia. destruct (Z.testbit _ _); [right|left]; reflexivity. Qed.
  Lemma sext_field : forall e, Z.land (Z.lor (Z.land e 65535) sxv) 65535 = Z.land (Z.lor e sxv) 65535.
  Proof.
    intros e. rewrite !zb_land_lor_distr_l, <- Z.land_assoc, Z.land_diag. reflexivity.
  Qed.
  Lemma exv_range : (0 <= exv < 32768)%Z.
  Proof. unfold exv. rewrite Z.land_comm. change 32768%Z with (2^15)%Z. apply Bytes.land_lt_pow2; [cbn; lia|]. apply Z.shiftr_nonneg. pose proof (hi64_range X). lia. Qed.
  Lemma eyv_range : (0 <= eyv < 32768)%Z.
  Proof. unfold eyv. rewrite Z.land_comm. change 32768%Z with (2^15)%Z. apply Bytes.land_lt_pow2; [cbn; lia|]. apply Z.shiftr_nonneg. pose proof (hi64_range Y). lia. Qed.
  Lemma shr48X : Z.shiftr (hi64 X) 48 = (hi64 X / 2^48)%Z. Proof. apply Z.shiftr_div_pow2. lia. Qed.

  Lemma land_M_16 : forall e, Z.land (Z.land e 18446744073709551615) 65535 = Z.land e 65535.
  Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma pack_bridge : forall xhi xlo E, (0 <= xlo < 2^64)%Z ->
    Z_to_bv 64 (Z.lor (Z.land xhi 281474976710655) (Z.land (Z.shiftl (Z.lor (Z.land E 65535) sxv) 48) 18446744073709551615))
    = Z_to_bv 64 (hi64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land (Z.lor E sxv) 65535) 48)) xlo)).
  Proof.
    intros xhi xlo E Hxlo. rewrite Z.lor_comm. rewrite (proj1 (pack_eq xhi xlo _ Hxlo)). rewrite sext_field. reflexivity.
  Qed.
  Lemma pack_bridge_lo : forall xhi xlo E, (0 <= xlo < 2^64)%Z ->
    Z_to_bv 64 xlo = Z_to_bv 64 (lo64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land (Z.lor E sxv) 65535) 48)) xlo)).
  Proof. intros xhi xlo E Hxlo. exact (proj2 (pack_eq xhi xlo _ Hxlo)). Qed.

  (* [comment removed for export] *)
  Lemma L_scale : forall m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
      (xhi xlo ex : Z),
    finv m -> Fok F' ->
    (0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (-2^20 <= ex < 2^20)%Z ->
    fmodl_scale sxv (xhi, xlo, ex) = r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) (Z_to_bv 64 32768) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 608)) fc None m (seg_rom img_segs)).
  Proof.
    intros until ex. intros FI FOK Rh Rl Re HS.
    pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
    pose proof sxv_cases as SX. unfold sxv in SX.
    unfold fmodl_scale in HS.
    zs. zs. zs. zs. zs. zs. brs K1.
    - (* [comment removed for export] *)
      replace (ex <=? 0) with true in HS by (symmetry; apply Z.leb_le; lia).
      do 7 zs. rewrite ?land_M_16. change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv. rewrite (pack_bridge xhi xlo (ex + 120)) by lia.
      rewrite (land_W64 xlo), (Z.mod_small xlo) by lia.
      zs. zs. zs. callw (eapply extendsftf2_2pm120; hyp).
      zs. zs. zs. zs. rewrite (pack_bridge_lo xhi xlo (ex + 120)) by lia.
      zs. call_split 80%Z (eapply SPEC_multf3_callq; [hyp | hyp | lia]).
      zs. rewrite HS. apply L_ret; [mk_finv | apply Fok_set10; exact FOK].
    - replace (ex <=? 0) with false in HS by (symmetry; apply Z.leb_gt; lia).
      do 6 zs. rewrite ?land_M_16. change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv. rewrite (pack_bridge xhi xlo ex) by lia.
      rewrite (land_W64 xlo), (Z.mod_small xlo) by lia.
      eapply L_retx; [exact FI | exact FOK | rewrite <- HS; apply pack_bridge_lo; lia | rewrite <- HS; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma L_L2 : forall (n : nat) m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
      (xhi xlo ex : Z) st',
    finv m -> Fok F' ->
    (0 <= xhi < 2^48)%Z -> (0 <= xlo < 2^64)%Z -> (-2^20 + Z.of_nat n <= ex < 2^20)%Z ->
    fmodl_norm_loop n (fmodl_norm_body (xhi, xlo, ex)) = Some st' -> fmodl_scale sxv st' = r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) (Z_to_bv 64 32768) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 580)) fc None m (seg_rom img_segs)).
  Proof.
    induction n as [|n IH]; intros until st'; intros FI FOK Rh Rl Re HL HS; [discriminate HL|].
    pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
    unfold fmodl_norm_body in HL. rewrite fmodl_norm_loop_step in HL.
    zs. zs. zs. zs. zs. zs. fixw. zs.
    (* [comment removed for export] *)
    set (b := Z.shiftr xlo 63) in *. assert (Rb : (0 <= b <= 1)%Z) by (subst b; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (E1 : Z.land (Z.shiftl xhi 1) 18446744073709551615 = (xhi * 2)%Z) by (rewrite land_W64, Z.shiftl_mul_pow2 by lia; apply Z.mod_small; lia).
    rewrite !E1 in *.
    assert (E2 : Z.lor (xhi * 2) b = (b + xhi * 2)%Z) by (rewrite Z.lor_comm; change (xhi * 2)%Z with (xhi * 2^1)%Z; apply lor_low_high; lia).
    rewrite !E2 in *.
    assert (E3 : u64 (2 * xhi + b) = (b + xhi * 2)%Z) by (unfold u64; rewrite Z.mod_small by lia; lia).
    rewrite !E3 in HL.
    assert (E4 : Z.shiftr (b + xhi * 2) 48 = Z.shiftr (xhi * 2) 48) by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    rewrite E4 in HL.
    assert (R5 : (0 <= Z.shiftr (xhi * 2) 48 < 2^16)%Z) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    assert (E6 : Z.land (Z.shiftl xlo 1) 18446744073709551615 = u64 (2 * xlo)) by (unfold u64; rewrite land_W64, Z.shiftl_mul_pow2 by lia; f_equal; lia).
    rewrite ?E6 in *. pose proof (Z.mod_pos_bound (2 * xlo) (2^64) ltac:(lia)) as R6. unfold u64 in *.
    replace (Z_to_bv 64 (Z.shiftl xlo 1)) with (Z_to_bv 64 ((2 * xlo) mod 2^64)%Z) by (apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2, Z.mod_mod by lia; f_equal; lia).
    replace (ex + -1)%Z with (ex - 1)%Z by lia.
    br K2; rewrite ?Z.shiftr_div_pow2 in K2 by lia.
    - (* [comment removed for export] *)
      replace (Z.shiftr (xhi * 2) 48 =? 0) with true in HL by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; lia).
      eapply (IH m); [exact FI | exact FOK | | | | exact HL | exact HS]; lia.
    - replace (Z.shiftr (xhi * 2) 48 =? 0) with false in HL by (symmetry; apply Z.eqb_neq; rewrite Z.shiftr_div_pow2 by lia; lia).
      injection HL as <-.
      eapply L_scale; [exact FI | exact FOK | lia | lia | lia | exact HS].
  Qed.

  (* [comment removed for export] *)
  Lemma L_K2 : forall m (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
      (xhi xlo ex : Z),
    finv m -> Fok F' ->
    (0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (-2^19 <= ex < 2^19)%Z ->
    fmodl_K2 sxv (xhi, xlo, ex) = Some r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 568)) fc None m (seg_rom img_segs)).
  Proof.
    intros until ex. intros FI FOK Rh Rl Re HK.
    pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
    unfold fmodl_K2 in HK. change 130%nat with (S 129) in HK. rewrite fmodl_norm_loop_step in HK.
    pose proof (shr48_range xhi Rh) as R48.
    rewrite Z.shiftr_div_pow2 in R48 by lia.
    zs. zs. zs. br K1; rewrite ?Z.shiftr_div_pow2 in K1 by lia.
    - replace (Z.shiftr xhi 48 =? 0) with false in HK by (symmetry; apply Z.eqb_neq; rewrite Z.shiftr_div_pow2 by lia; lia). injection HK as HS.
      eapply L_scale; [exact FI | exact FOK | lia | lia | lia | exact HS].
    - replace (Z.shiftr xhi 48 =? 0) with true in HK by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; lia).
      destruct (fmodl_norm_loop 129 _) as [st'|] eqn:HL; [|discriminate HK]. injection HK as HS.
      eapply L_L2; [exact FI | exact FOK | | exact Rl | | exact HL | exact HS].
      + Z.div_mod_to_equations. lia.
      + lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_fin : forall m (x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
      (xhi xlo yhi ylo ex : Z),
    finv m -> Fok F' ->
    (0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z -> (-2^19 <= ex < 2^19)%Z ->
    fmodl_K1 X yhi ylo sxv (inl (xhi, xlo, ex)) = Some r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ylo) (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 512)) fc None m (seg_rom img_segs)).
  Proof.
    intros until ex. intros FI FOK Rxh Rxl Ryh Ryl Re HK.
    pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
    unfold fmodl_K1, fmodl_fin in HK.
    (nelim (sbb_bridge xhi xlo yhi ylo Rxh Rxl Ryh Ryl) 4%nat; intros B1 B2 B3 B4). cbv zeta in B1, B2, B3.
    set (hi' := if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi)) in *.
    zs. zs. zs. rewrite B2.
    rewrite (shr63_eqb hi') in HK by lia.
    zs. br K1.
    - (* [comment removed for export] *)
      replace (hi' <? 2^63) with false in HK by (symmetry; apply Z.ltb_ge; lia).
      zs. eapply L_K2; [exact FI | exact FOK | lia | lia | lia | exact HK].
    - replace (hi' <? 2^63) with true in HK by (symmetry; apply Z.ltb_lt; lia).
      zs. zs. rewrite <- B4. pose proof (Z.mod_pos_bound (xlo - ylo) (2^64) ltac:(lia)) as Rlo. unfold u64 in HK, Rlo |- *.
      assert (RL : (0 <= Z.lor hi' ((xlo - ylo) mod 2^64) < 2^64)%Z) by (apply Bytes.lor_lt_pow2; lia).
      change 18446744073709551616%Z with (2^64)%Z in *.
      zs. br K2; rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
      + replace (Z.lor hi' ((xlo - ylo) mod 2 ^ 64) =? 0) with false in HK by (symmetry; apply Z.eqb_neq; exact K2).
        rewrite <- (Z_to_bv_mod64 (xlo - ylo)).
        eapply L_K2; [exact FI | exact FOK | lia | lia | lia | exact HK].
      + replace (Z.lor hi' ((xlo - ylo) mod 2 ^ 64) =? 0) with true in HK by (symmetry; apply Z.eqb_eq; exact K2).
        injection HK as Hr. zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
  Qed.

  Lemma dbl_bridge : forall h b, (0 <= h < 2^64)%Z -> (0 <= b <= 1)%Z ->
    Z.lor (Z.land (Z.shiftl h 1) 18446744073709551615) b = u64 (2 * h + b).
  Proof.
    intros h b Hh Hb. rewrite land_W64, Z.shiftl_mul_pow2 by lia. unfold u64.
    replace ((h * 2^1) mod 2^64)%Z with ((h mod 2^63) * 2^1)%Z by (Z.div_mod_to_equations; lia).
    rewrite Z.lor_comm, lor_low_high by (try lia; Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations; lia.
  Qed.
  Lemma shr63_b : forall l, (0 <= l < 2^64)%Z -> (0 <= Z.shiftr l 63 <= 1)%Z.
  Proof. intros l Hl. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations; lia. Qed.
  Lemma u64_range : forall v, (0 <= u64 v < 2^64)%Z.
  Proof. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.
  Lemma zbv_shl1 : forall v, Z_to_bv 64 (Z.shiftl v 1) = Z_to_bv 64 (u64 (2 * v)).
  Proof. intros. rewrite zbv_u64, Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

  (* [comment removed for export] *)
  Lemma L_L1 : forall (yhi ylo ey : Z) (n : nat) m (x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) F' x1
      (xhi xlo ex : Z) res,
    finv m -> Fok F' ->
    (0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z ->
    (-2^18 <= ey)%Z -> (ey < ex < 2^18)%Z ->
    fmodl_sub_loop (S n) X yhi ylo ey (xhi, xlo, ex) = Some res -> fmodl_K1 X yhi ylo sxv res = Some r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ylo) (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 408)) fc None m (seg_rom img_segs)).
  Proof.
    intros yhi ylo ey. induction n as [|n IH]; intros until res; intros FI FOK Rxh Rxl Ryh Ryl Rey Rex HL HK.
    all: pose proof FI as FI'; dest_finv FI'; unfold RFMODL_DEPTH in SPLO; pose proof (hi64_range X) as RHX.
    all: rewrite fmodl_sub_loop_step in HL; replace (ey <? ex) with true in HL by (symmetry; apply Z.ltb_lt; lia).
    all: unfold fmodl_sub_body in HL.
    all: (nelim (sbb_bridge xhi xlo yhi ylo Rxh Rxl Ryh Ryl) 4%nat; intros B1 B2 B3 B4); cbv zeta in B1, B2, B3.
    all: set (hi' := if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi)) in *.
    all: rewrite (shr63_eqb hi') in HL by lia.
    all: pose proof (shr63_b xlo Rxl) as Rb; pose proof (u64_range (xlo - ylo)) as Rlo; pose proof (shr63_b (u64 (xlo - ylo)) Rlo) as Rb2.
    all: zs; zs; zs; rewrite B2; zs; br K1.
    (* [comment removed for export] *)
    - replace (hi' <? 2^63) with false in HL by (symmetry; apply Z.ltb_ge; lia). cbn [fmodl_sub_loop] in HL. discriminate HL.
    - replace (hi' <? 2^63) with true in HL by (symmetry; apply Z.ltb_lt; lia).
      zs. rewrite <- (Z_to_bv_mod64 (xlo - ylo)). change ((xlo - ylo) mod 2^64)%Z with (u64 (xlo - ylo)).
      assert (RL : (0 <= Z.lor hi' (u64 (xlo - ylo)) < 2^64)%Z) by (apply Bytes.lor_lt_pow2; lia).
      zs. zs. br K2; rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
      + replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with true in HL by (symmetry; apply Z.eqb_eq; exact K2).
        injection HL as <-. cbn [fmodl_K1] in HK. injection HK as Hr.
        zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
      + replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with false in HL by (symmetry; apply Z.eqb_neq; exact K2).
        cbn [fmodl_sub_loop] in HL. discriminate HL.
    - (* [comment removed for export] *)
      replace (hi' <? 2^63) with false in HL by (symmetry; apply Z.ltb_ge; lia).
      zs. zs. zs. rewrite (dbl_bridge xhi (Z.shiftr xlo 63)) by lia.
      zs. fixw. zs. rewrite zbv_shl1. zs. brs K3.
      * (* [comment removed for export] *)
        rewrite fmodl_sub_loop_step in HL. replace (ey <? ex - 1) with false in HL by (symmetry; apply Z.ltb_ge; lia).
        injection HL as <-. zs. replace (ex - 1)%Z with ey in HK by lia.
        eapply L_fin; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | exact HK].
      * eapply IH; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | lia | exact HL | exact HK].
    - replace (hi' <? 2^63) with true in HL by (symmetry; apply Z.ltb_lt; lia).
      zs. rewrite <- (Z_to_bv_mod64 (xlo - ylo)). change ((xlo - ylo) mod 2^64)%Z with (u64 (xlo - ylo)).
      assert (RL : (0 <= Z.lor hi' (u64 (xlo - ylo)) < 2^64)%Z) by (apply Bytes.lor_lt_pow2; lia).
      zs. zs. br K2; rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
      + replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with true in HL by (symmetry; apply Z.eqb_eq; exact K2).
        injection HL as <-. cbn [fmodl_K1] in HK. injection HK as Hr.
        zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
      + replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with false in HL by (symmetry; apply Z.eqb_neq; exact K2).
        zs. zs. zs. rewrite (dbl_bridge hi' (Z.shiftr (u64 (xlo - ylo)) 63)) by lia. zs.
        zs. fixw. zs. rewrite zbv_shl1. zs. brs K3.
        * (* [comment removed for export] *)
          rewrite fmodl_sub_loop_step in HL. replace (ey <? ex - 1) with false in HL by (symmetry; apply Z.ltb_ge; lia).
          injection HL as <-. zs. replace (ex - 1)%Z with ey in HK by lia.
          eapply L_fin; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | exact HK].
        * eapply IH; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | lia | exact HL | exact HK].
  Qed.

  Lemma ex_field : forall v, (0 <= v < 2^16)%Z -> Z.shiftr (Z.land (Z.shiftl v 49) 18446744073709551615) 49 = Z.land v 32767.
  Proof.
    intros v Hv. apply Z.bits_inj'. intros i Hi.
    rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
    change 18446744073709551615%Z with (Z.ones 64). change 32767%Z with (Z.ones 15).
    destruct (Z.lt_ge_cases i 15).
    - rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
    - rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 15) by lia. now rewrite !Bool.andb_false_r.
  Qed.
  Lemma mant_or_range : forall h, (0 <= Z.lor (Z.land h 281474976710655) 281474976710656 < 2^64)%Z.
  Proof.
    intros h. pose proof (land48_range h) as R. change 0x0000ffffffffffff%Z with 281474976710655%Z in R.
    change 281474976710656%Z with (1 * 2^48)%Z. rewrite lor_low_high by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_setup : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' x1
      (uxh uxl uyh uyl ex ey : Z),
    finv m -> Fok F' ->
    (0 <= uxh < 2^64)%Z -> (0 <= uxl < 2^64)%Z -> (0 <= uyh < 2^64)%Z -> (0 <= uyl < 2^64)%Z ->
    (-2^18 <= ey < 2^18)%Z -> (-2^18 <= ex < 2^18)%Z ->
    match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X (Z.lor (Z.land uyh 0x0000ffffffffffff) (2^48)) uyl ey
            (Z.lor (Z.land uxh 0x0000ffffffffffff) (2^48), uxl, ex) with
    | Some res => fmodl_K1 X (Z.lor (Z.land uyh 0x0000ffffffffffff) (2^48)) uyl sxv res
    | None => None end = Some r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 uyl) (Z_to_bv 64 uxl) (Z_to_bv 64 uyh) (Z_to_bv 64 uxh) (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 348)) fc None m (seg_rom img_segs)).
  Proof.
    intros until ey. intros FI FOK R1 R2 R3 R4 R5 R6 HK.
    pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
    pose proof (mant_or_range uxh) as Q1. pose proof (mant_or_range uyh) as Q2.
    change (2^48)%Z with 281474976710656%Z in HK. change 0x0000ffffffffffff%Z with 281474976710655%Z in HK.
    do 7 zs. rewrite ?land_W64, ?(Z.mod_small (Z.lor _ _) (2^64)) by lia.
    zs. brs K1.
    - (* [comment removed for export] *)
      destruct (fmodl_sub_loop _ _ _ _ _ _) as [res|] eqn:HL; [|discriminate HK].
      eapply L_L1; [exact FI | exact FOK | lia | lia | lia | lia | lia | lia | exact HL | exact HK].
    - zs. rewrite fmodl_sub_loop_step in HK. replace (ey <? ex) with false in HK by (symmetry; apply Z.ltb_ge; lia).
      eapply L_fin; [exact FI | exact FOK | lia | lia | lia | lia | lia | exact HK].
  Qed.

  Definition UX : Z := mk128 (Z.land (hi64 X) 0x7fffffffffffffff) (lo64 X).
  Definition UY : Z := mk128 (Z.land (hi64 Y) 0x7fffffffffffffff) (lo64 Y).
  Lemma UX_words : lo64 UX = lo64 X /\ hi64 UX = Z.land (hi64 X) 0x7fffffffffffffff.
  Proof. unfold UX. pose proof (lo64_range X). pose proof (land63_range (hi64 X) (hi64_range X)). rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.
  Lemma UY_words : lo64 UY = lo64 Y /\ hi64 UY = Z.land (hi64 Y) 0x7fffffffffffffff.
  Proof. unfold UY. pose proof (lo64_range Y). pose proof (land63_range (hi64 Y) (hi64_range Y)). rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition K_normy (ux ex uy ey : Z) : option Z :=
    (let xhi := Z.lor (Z.land (hi64 ux) 0x0000ffffffffffff) (2^48) in
     let yhi := Z.lor (Z.land (hi64 uy) 0x0000ffffffffffff) (2^48) in
     match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X yhi (lo64 uy) ey (xhi, lo64 ux, ex) with
     | Some res => fmodl_K1 X yhi (lo64 uy) sxv res
     | None => None end)%Z.

  (* [comment removed for export] *)
  Lemma L_normy : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' x1 (ux ex : Z) (wl wh : word),
    finv m -> Fok F' -> (-2^18 <= ex < 2^18)%Z ->
    K_normy ux ex (f128_mul UY C_2P120) (Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120)%Z = Some r ->
    wl = Z_to_bv 64 (lo64 ux) -> wh = Z_to_bv 64 (hi64 ux) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (lo64 UY)) wl (Z_to_bv 64 (hi64 UY)) wh (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 0) s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 300)) fc None m (seg_rom img_segs)).
  Proof.
    intros until wh. intros FI FOK Re HK -> ->.
    pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
    pose proof (lo64_range UY) as R1. pose proof (hi64_range UY) as R2. pose proof (lo64_range ux) as R3. pose proof (hi64_range ux) as R4.
    zs. zs. zs. callw (eapply extendsftf2_2p120; hyp).
    zs. zs. zs. zs.
    zs. call_split 80%Z (eapply SPEC_multf3_callq; [hyp | hyp | lia]).
    set (uy' := f128_mul UY C_2P120) in *. pose proof (lo64_range uy') as R5. pose proof (hi64_range uy') as R6.
    pose proof (shr48_range (hi64 uy') R6) as R7.
    zs. zs. zs. zs.
    unfold K_normy in HK.
    eapply L_setup; [mk_finv | apply Fok_set10; exact FOK | lia | lia | lia | lia | | lia | exact HK].
    rewrite Z.shiftr_div_pow2 in R7 |- * by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_norm : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F' x1,
    finv m -> Fok F' ->
    (let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
     let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
     K_normy ux ex uy ey) = Some r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 (Z.land (hi64 Y) 0x7fffffffffffffff)) (Z_to_bv 64 (Z.land (hi64 X) 0x7fffffffffffffff))
               (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 exv) x24 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 (sym 0x20260 + 280)) fc None m (seg_rom img_segs)).
  Proof.
    intros until x1. intros FI FOK HK.
    pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
    pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
    pose proof exv_range as REX. pose proof eyv_range as REY.
    pose proof (land63_range (hi64 X) RHX) as R63X. pose proof (land63_range (hi64 Y) RHY) as R63Y.
    destruct UX_words as [EUXl EUXh]. destruct UY_words as [EUYl EUYh].
    zs. zs. rewrite (fpc_exp_field (hi64 Y)) by lia. change (Z.land (Z.shiftr (hi64 Y) 48) 32767) with eyv.
    zs. br K1.
    - (* [comment removed for export] *)
      replace (exv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia).
      zs. zs. zs. callw (eapply extendsftf2_2p120; hyp).
      zs. zs. rewrite <- EUXl, <- EUXh. zs. zs.
      zs. call_split 80%Z (eapply SPEC_multf3_callq; [hyp | hyp | lia]).
      rewrite EUXl.
      set (ux' := f128_mul UX C_2P120) in *. pose proof (lo64_range ux') as R5. pose proof (hi64_range ux') as R6.
      pose proof (shr48_range (hi64 ux') R6) as R7. rewrite Z.shiftr_div_pow2 in R7 by lia.
      zs. zs. zs. zs. zs. br K2.
      + (* [comment removed for export] *)
        replace (eyv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK. unfold K_normy in HK.
        rewrite EUYl, EUYh in HK.
        eapply L_setup; [mk_finv | apply Fok_set10; exact FOK | lia | lia | lia | lia | lia | | exact HK].
        rewrite Z.shiftr_div_pow2 by lia. lia.
      + replace (eyv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
        zs. rewrite <- EUYl, <- EUYh, K2. eapply L_normy; [mk_finv | apply Fok_set10; exact FOK | | exact HK | reflexivity | reflexivity].
        rewrite Z.shiftr_div_pow2 by lia. lia.
    - replace (exv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK.
      zs. zs. br K2.
      + replace (eyv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK. unfold K_normy in HK.
        rewrite EUXl, EUXh, EUYl, EUYh in HK.
        eapply L_setup; [exact FI | exact FOK | lia | lia | lia | lia | lia | lia | exact HK].
      + replace (eyv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
        rewrite <- EUYl, <- EUYh, K2. eapply L_normy; [exact FI | exact FOK | lia | exact HK | rewrite EUXl; reflexivity | rewrite EUXh; reflexivity].
  Qed.

  Definition K_norm : option Z :=
    (let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
     let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
     K_normy ux ex uy ey).
  Definition K_cmp : option Z :=
    if f128_le UX UY <=? 0 then (if f128_le UX UY =? 0 then Some (f128_mul (f128_of_i32 0) X) else Some X) else K_norm.

  (* [comment removed for export] *)
  Lemma L_cmp : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) x1,
    finv m ->
    (if exv =? 32767 then Some (f128_div (f128_mul X Y) (f128_mul X Y)) else K_cmp) = Some r ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x20260 + 188)) fc None m (seg_rom img_segs)).
  Proof.
    intros until x1. intros FI HK.
    pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
    pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
    pose proof (shr48_range (hi64 X) RHX) as R48.
    pose proof (land63_range (hi64 X) RHX) as R63X. pose proof (land63_range (hi64 Y) RHY) as R63Y.
    destruct UX_words as [EUXl EUXh]. destruct UY_words as [EUYl EUYh].
    pose proof exv_range as REX.
    zs. zs. zs. zs. try rewrite (ex_field (Z.shiftr (hi64 X) 48)) by lia. change (Z.land (Z.shiftr (hi64 X) 48) 32767) with exv.
    zs. fixw. zs. br K1.
    - replace (exv =? 32767) with true in HK by (symmetry; apply Z.eqb_eq; lia). injection HK as Hr.
      eapply L_nan; [exact FI | apply Fok_refl | symmetry; exact Hr].
    - replace (exv =? 32767) with false in HK by (symmetry; apply Z.eqb_neq; lia). unfold K_cmp in HK.
      pose proof (f128_le_range UX UY) as RLE.
      zs. zs. zs. zs. zs. zs. zs. zs.
      rewrite <- EUXl, <- EUXh, <- EUYl, <- EUYh.
      zs. callw (eapply SPEC_letf2_callv; hyp).
      zs. brs K2.
      + replace (f128_le UX UY <=? 0) with false in HK by (symmetry; apply Z.leb_gt; lia).
        rewrite EUXl, EUXh, EUYl, EUYh. eapply L_norm; [mk_finv | apply Fok_refl | exact HK].
      + replace (f128_le UX UY <=? 0) with true in HK by (symmetry; apply Z.leb_le; lia).
        zs. zs. zs. zs. zs. callw (eapply SPEC_letf2_callv; hyp).
        zs. br K3.
        * replace (f128_le UX UY =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K3 RLE; mlia2). injection HK as Hr.
          rewrite EUXl. replace (Z_to_bv 64 (f128_le UX UY)) with (Z_to_bv 64 0) by (f_equal; clear -K3 RLE; mlia2).
          eapply L_zero; [mk_finv | apply Fok_refl | symmetry; exact Hr].
        * replace (f128_le UX UY =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K3 RLE; mlia2). injection HK as Hr.
          zs. rewrite EUXl. eapply L_retx; [mk_finv | apply Fok_refl | rewrite Hr; reflexivity | rewrite Hr; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma L_entry : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk img_segs m0 (q - RFMODL_DEPTH) q -> mem_inv img_segs m0 ->
    evt img_segs POST
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FMODL) fc None m0 (seg_rom img_segs)).
  Proof.
    intros until t6. intros ST MI.
    pose proof (munch_refl [(q - RFMODL_DEPTH, q)]%Z m0) as MU. pose proof (wmono_refl img_segs m0) as WM.
    unfold RFMODL_DEPTH in ST, MU, SPLO. unfold FMODL.
    pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
    pose proof HM as HK. rewrite m_fmodl_split in HK. cbv zeta in HK.
    change (Z.land (Z.shiftr (hi64 X) 48) 32767) with exv in HK. change (Z.land (Z.shiftr (hi64 Y) 48) 32767) with eyv in HK.
    change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv in HK.
    fold UX UY in HK.
    zs. carve_frame 80%nat ST.
    do 15 zs.
    zs. callw (eapply SPEC_floatsitf_callv with (v := 0%Z) (i := 0%Z); [hyp | lia | reflexivity]).
    set (t00 := f128_of_i32 0) in *. pose proof (lo64_range t00) as RT1. pose proof (hi64_range t00) as RT2.
    pose proof (f128_le_range Y t00) as RLE.
    zs. zs. zs. zs. zs. callw (eapply SPEC_letf2_callv; hyp).
    zs. br K1.
    - (* [comment removed for export] *)
      replace (f128_le Y t00 =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K1 RLE; mlia2). cbn [orb] in HK.
      zs. zs. zs. callw (eapply SPEC_fpclassifyl; eassumption). norm_rsegs.
      rewrite !ulit_lo64, !ulit_hi64, m_fpclassifyl_canon.
      assert (RC : (0 <= m_fpclassifyl Y <= 4)%Z) by (unfold m_fpclassifyl; repeat (destruct (_ : bool)); lia).
      zs. br K2.
      + replace (m_fpclassifyl Y =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K2 RC; mlia2). cbn [orb] in HK. injection HK as Hr.
        eapply L_nan; [mk_finv | apply Fok_refl | symmetry; exact Hr].
      + replace (m_fpclassifyl Y =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K2 RC; mlia2). cbn [orb] in HK.
        eapply L_cmp; [mk_finv | exact HK].
    - replace (f128_le Y t00 =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K1 RLE; mlia2). cbn [orb] in HK. injection HK as Hr.
      eapply L_nan; [mk_finv | apply Fok_refl | symmetry; exact Hr].
  Qed.
End Fmodl.

Lemma rfmodl_spec : rfmodl_stmt.
Proof.
  unfold rfmodl_stmt. intros. eapply L_entry; eassumption.
Qed.

(* [comment removed for export] *)
Definition rfmodl_spec_c : Prop := rfmodl_stmt.
Lemma rfmodl_spec_c_ok : rfmodl_spec_c.
Proof. exact rfmodl_spec. Qed.


End Img.
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

(* [comment removed for export] *)
Existing Class rfmodl_spec_c.
