(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP StoreFast SysStep SFModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Layout Str_tac Sj_num_kit Pj_num_defs Pj_sf_c Pj_tochars_a Pj_tochars_b Pj_tochars_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section TC.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q lo NB : Z) (m0 : word -> option byte).
  Hypothesis ROOM : (lo <= q - TC_STACK)%Z.
  Hypothesis GTOP : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QNB : (q <= NB)%Z.
  Hypothesis NBHI : (NB + 40 < 2^63)%Z.

  Notation POST := (tochars_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo NB m0).
  Notation INV := (TCINV ra s0 s1 s2 s3 q lo NB m0).
  Notation TCS pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m :=
    (MS (mkR xra (Z_to_bv 64 (q + -80)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).
  Notation ZERO := (tc_zero ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q lo NB m0 ROOM GTOP QNB NBHI).
  Notation DIGITS := (tc_digits ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q lo NB m0 ROOM GTOP QNB NBHI
                        (tc_copy_proof ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q lo NB m0 ROOM GTOP QNB NBHI)).

  Lemma tc_nonzero : forall sg xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (0 <= sg <= 1)%Z ->
    evt psegs POST (TCS 0x3f840 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HS. pose proof I as I0. tc_open I.
    do 5 zstep. zstep.
    set (E := (Z.land (bv_unsigned (reg_get F 10) ≪ 1) 18446744073709551615 ≫ 53)%Z).
    assert (HE : (0 <= E <= 2047)%Z).
    { unfold E. rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 53)%Z with 9007199254740992%Z.
      generalize (bv_unsigned (reg_get F 10) ≪ 1)%Z. intros z. Z.div_mod_to_equations. lia. }
    clearbody E.
    eapply evt_cut; [eapply sf_proof; [exact MI | exact HE] |].
    cbv beta. intros ms' PO. unfold sf_post in PO.
    destruct PO as (y0 & y1 & y2 & w & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & e & -> & HR).
    replace (ret_pc (Z_to_bv 64 260184)) with (Z_to_bv 64 260184) by (apply bv_eq; vm_compute; reflexivity).
    eapply evt_eq; [| eapply (DIGITS e sg F fc FRM HR HS); exact I0].
    num_st_eq.
  Qed.

  Lemma tochars_body : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (junk : list byte),
    stk psegs m0 lo q -> mem_inv psegs m0 -> frm0 fc -> rw_cells psegs m0 NB [CB 40 junk] ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3f7d8) fc None m0 (seg_rom psegs)).
  Proof using ROOM GTOP QNB NBHI.
    intros until junk. intros ST MI FRM NBC.
    pose proof ZERO as KZERO. pose proof tc_nonzero as KNZ.
    pose proof ROOM as ROOM'. pose proof GTOP as GTOP'. unfold TC_STACK, GLOBALS_TOP in ROOM', GTOP'.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    pose proof (munch_refl [(q + -80, q); (NB, NB + 40)]%Z m0) as MU. pose proof (wmono_refl psegs m0) as WM.
    zstep. carve_frame 80%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 80 junk0 [] [40;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 zstep.
    zstep. zstep. zstep.
    apply (proj1 (num_rw_cells_app psegs _ _ [CB 40 (firstn 40 junk0)] _)) in FR. destruct FR as [TMP FRS].
    cbn [cells_size csize Nat.add] in FRS. change (Z.of_nat 40) with 40%Z in FRS.
    replace (q + -80 + 40)%Z with (q + -40)%Z in FRS by lia.
    pose proof (u8arr_of_rw_cells psegs _ _ _ _ TMP) as TA.
    assert (TL : length (firstn 40 junk0) = 40%nat) by (destruct TMP as [[Hwf _] _]; cbn in Hwf; tauto).
    clear TMP. set (tmp := firstn 40 junk0) in *. clearbody tmp.
    pose proof (u8arr_of_rw_cells psegs _ _ _ _ NBC) as NA.
    assert (NL : length junk = 40%nat) by (destruct NBC as [[Hwf _] _]; cbn in Hwf; tauto).
    clear NBC.
    if_cases K.
    -
      zstep.
      arr_store NA NL 0%Z 1%nat.
      zstep. zstep. zstep. zstep.
      zstep. if_cases KZ.
      + eapply evt_eq; [| eapply (KZERO 1%Z); [tc_close | exact FRM | lia]]. num_st_eq.
      + eapply evt_eq; [| eapply (KNZ 1%Z); [tc_close | exact FRM | lia]]. num_st_eq.
    - zstep. zstep.
      zstep. if_cases KZ.
      + eapply evt_eq; [| eapply (KNZ 0%Z); [tc_close | exact FRM | lia]]. num_st_eq.
      +
        eapply evt_eq; [| eapply (KZERO 0%Z); [tc_close | exact FRM | lia]]. num_st_eq.
  Qed.
End TC.

Theorem tochars_proof : tochars_stmt.
Proof.
  unfold tochars_stmt. intros until junk. intros ST ROOM GTOP MI FRM QNB NBHI NBC. unfold TC_ENTRY.
  eapply tochars_body; eassumption.
Qed.
