(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import ItB_base ItB_ldefs ItB_count ItB_max ItB_min ItB_left ItB_offs ItB_sort ItB_switch ItB_here ItB_fill ItB_cnt2 ItB_sub ItB_loop ItB_tail.
(* [U14B] A2 2026-11-12: the CODES bound of zlib 1.4's table loop (NEW text, the U2B twin of G's U1A/ItA_safe20) *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import ItB_safe20.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top : Z) (m1 : amem).
  Variables (ty : codetype) (lf wf cf : Z -> Z) (lo codes nx bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis C : itc ty lf lo codes nx bits cf wf.

  Notation LP := (S + 168 + 2 * lo).
  Notation ST := (bst SP SPA S F PB LP (cty ty) gp tp FR fc).
  Notation cntAr := (cntA lf lo codes).
  Notation cA := (arr_get (cntA lf lo codes)).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation work1Ar := (work1A lf lo codes wf).
  Notation w1 := (arr_get (work1A lf lo codes wf)).
  Notation X := (itm_ctx ty (lensA lf) lo nx rt mx).
  Notation st0 := (itm_st0 mn nx rt cntAr (tblA cf) (work1A lf lo codes wf)).
  Notation RES := (resA ty lf lo codes nx bits cf wf).
  Notation RET r wfx cfx nxt bts := (ret_pre SP SPA S F PB LP (cty ty) gp tp FR fc m1 r lf wfx cfx nxt bts).

  Definition body_post : machine_state -> Prop :=
    RET (it_ret RES) (arr_get (it_work RES)) (arr_get (it_tbl RES)) (Z_to_bv 64 (S + 1384 + 4 * it_table RES)) (Z_to_bv 64 (it_bits RES)).

  Lemma ret_pre_ext : forall r (wf1 wf2 cf1 cf2 : Z -> Z) nxt bts ms',
    RET r wf1 cf1 nxt bts ms' ->
    (forall j, 0 <= j < 288 -> wf1 j = wf2 j) -> (forall j, 0 <= j < 1444 -> cf1 j = cf2 j) ->
    RET r wf2 cf2 nxt bts ms'.
  Proof.
    intros r wf1 wf2 cf1 cf2 nxt bts ms' HR EW EC. unfold ret_pre in *.
    destruct HR as (m & x1 & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x25 & x28 & x29 & x30 & x31 &
                    v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & v96 & v104 & v112 & v120 & v128 & v136 & v144 & cnt & of & E & INV).
    exists m, x1, x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x25, x28, x29, x30, x31,
           v0, v8, v16, v24, v32, v40, v48, v56, v64, v72, v80, v88, v96, v104, v112, v120, v128, v136, v144, cnt, of.
    split; [exact E|]. destruct INV as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
    split; [eapply f16arr_ext; [exact A8| exact EW]|]. split; [eapply f32arr_ext; [exact A9| exact EC]| exact A10].
  Qed.

  Lemma safe_sort : mx <> 0 -> itm_reject ty mx (it_left_check cntAr) = false ->
    it_sort_ok (lensA lf) lo codes (offsA lf lo codes) 288 = true /\
    (it_not_enough ty (itm_used rt) = false -> it_loop_ok (Z.to_nat (codes + 1)) X 288 320 1444 st0 = true).
  Proof.
    intros Hmx Hrj.
    pose proof (it_safe_sort ty (lensA lf) lo codes (tblA cf) nx bits (workA wf) (it_safe_ok _ _ _ _ _ _ _ _ C)) as SS.
    cbv zeta in SS. unfold mxA, cntA, rootA, mnA, mxA, cntA, offsA, work1A, offsA, cntA in *.
    specialize (SS Hmx Hrj). destruct SS as [S1 S2].
    unfold workA, lensA, tblA in S1, S2 |- *. rewrite !arr_len_init in S1, S2. cbv [IDefs.N_WORK IDefs.N_LENS IDefs.N_CODES] in S1, S2 |- *.
    split; [exact S1 | intros Hne; exact (proj2 (proj2 (S2 Hne)))].
  Qed.

  (* [U14B] A2 2026-11-12: the loop's CODES bound (U2B/ItB_safe20), as safe_sort gives it_loop_ok (G's U1A safe20) *)
  Lemma safe20 : mx <> 0 -> itm_reject ty mx (it_left_check cntAr) = false ->
    it_not_enough ty (itm_used rt) = false -> it_loop20 (Z.to_nat (codes + 1)) X st0 = true.
  Proof.
    intros Hmx Hrj Hne.
    pose proof (it_safe20_loop ty (lensA lf) lo codes (tblA cf) nx bits (workA wf) (it_safe20_ok _ _ _ _ _ _ _ _ C)) as SS.
    cbv zeta in SS. unfold mxA, cntA, rootA, mnA, mxA, cntA, offsA, work1A, offsA, cntA in *.
    exact (SS Hmx Hrj Hne).
  Qed.

  Lemma it_body : forall (m : amem) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v128 v136 : word) (of : Z -> Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 (Z_to_bv 64 (S + 160)) v128 v136 (Z_to_bv 64 F)
            (fun _ => 0) of lf wf cf (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    evtF bsegs RNG body_post
      (ST x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 codes) x28 x29 x30 x31 0x96e30 m).
  Proof using All.
    intros until x31. intros INV.
    pose proof C as C'. open_itc C'.
    assert (Hl15' : forall s, 0 <= s < codes -> lf (lo + s) <= 15) by exact Hlens15.
    eapply evtF_cut; [eapply (it_count RNG FR fc gp tp SP SPA S F PB top (cty ty) m1 lf wf cf lo codes CX); [exact Hlf | lia | lia | lia | exact Hl15' | exact INV]|].
    cbv beta. intros ms1 (ma & q5 & q6 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & -> & INVa).
    assert (KLEFT : forall ms (y1 y5 y6 y7 y17 y28 y29 y30 y31 : word),
              left_pre FR fc gp tp SP SPA S F PB (cty ty) lf lo codes bits ma y1 y5 y6 y7 y17 (Z_to_bv 64 codes) y28 y29 y30 y31 ms ->
              evtF bsegs RNG body_post ms).
    { intros ms y1 y5 y6 y7 y17 y28 y29 y30 y31 (t10 & t16 & -> & Hmx1).
      assert (Hmx0 : mx <> 0) by lia.
      eapply evtF_cut; [eapply (it_left RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes bits CX); [lia | lia | exact Hmx1 | exact INVa]|].
      cbv beta. intros ms3 [(u10 & u11 & u16 & u17 & -> & Hrj) | (u11 & u16 & u17 & -> & Hrj)].
      -
        destruct (safe_sort Hmx0 Hrj) as [SOK LOOPOK].
        eapply evtF_cut; [eapply (it_offs RNG FR fc gp tp SP SPA S F PB top (cty ty) m1 lf wf cf lo codes CX); [lia | exact INVa]|].
        cbv beta. intros ms4 (mb & w10 & w11 & ofb & -> & INVb & HOFb).
        eapply evtF_cut; [eapply (it_sort RNG FR fc gp tp SP SPA S F PB top (cty ty) m1 lf wf cf lo codes CX); [exact Hlf | lia | lia | lia | exact Hl15' | exact SOK | exact HOFb | exact INVb]|].
        cbv beta. intros ms5 (mc & z5 & z6 & z7 & z10 & z11 & z17 & z25 & z28 & z29 & z30 & z31 & ofc & -> & INVc).
        eapply evtF_cut; [eapply (it_switch RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C); [exact Hmx1 | exact INVc]|].
        cbv beta. intros ms6 [[HH Hne] | [HR Hne]].
        +
          destruct HH as (md & h5 & h6 & h7 & h11 & h16 & h29 & h30 & h31 & u56 & -> & INVd).
          specialize (LOOPOK Hne).
          assert (SP0 : spure work1Ar rt nx st0).
          { unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl itm_st0].
            split; [reflexivity|]. split; [unfold BOX; left; reflexivity|]. split; [unfold BOX; left; reflexivity|]. split; [lia|]. split; [lia|].
            split; [intros j Hj; pose proof (cntK_le lf lo codes j ltac:(lia) ltac:(lia)) as CK; rewrite <- cntA_eq in CK; lia|].
            split; [intros j Hj; rewrite tblA_get; apply Hcf; exact Hj|].
            split; [rewrite cntA_eq; apply cntK_len | unfold tblA; apply arr_len_init]. }
          eapply evtF_cut; [eapply (it_main_loop RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C (Z.to_nat (codes + 1)) st0);
                             [exact LOOPOK | exact Hmx1 | exact (safe20 Hmx0 Hrj Hne) | exact INVd | exact SP0]|].
          cbv beta. intros ms7 [(st' & HL & HB & Hfit) | (st' & HL & HRf & HW)].
          *
            destruct HB as (me & b5 & b6 & b7 & b10 & b11 & b12 & b16 & b17 & b25 & b29 & b30 & b31 & -> & INVe & SPe & B1 & B2 & B3).
            eapply evtF_mono; [eapply (it_tail RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st'); [exact INVe | exact SPe | exact B1 | exact B2 | exact B3 | exact Hfit]|].
            cbv beta. intros ms8 HR8. unfold body_post. rewrite (res_phases ty lf lo codes nx bits cf wf).
            replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmx0). rewrite Hrj, Hne.
            rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL.
            cbn [it_ret it_work it_tbl it_table it_bits fst snd].
            destruct SPe as (WKe & _). rewrite WKe. exact HR8.
          *
            apply evtF_done. unfold body_post. rewrite (res_phases ty lf lo codes nx bits cf wf).
            replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmx0). rewrite Hrj, Hne.
            rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL.
            cbn [it_ret it_work it_tbl it_table it_bits fst snd]. rewrite HW. exact HRf.
        +
          apply evtF_done. unfold body_post. rewrite (res_phases ty lf lo codes nx bits cf wf).
          replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmx0). rewrite Hrj, Hne.
          cbn [it_ret it_work it_tbl it_table it_bits fst snd].
          eapply ret_pre_ext; [exact HR | intros; reflexivity | intros j Hj; symmetry; apply tblA_get].
      -
        apply evtF_done. unfold body_post. rewrite (res_phases ty lf lo codes nx bits cf wf).
        replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmx0). rewrite Hrj.
        cbn [it_ret it_work it_tbl it_table it_bits fst snd].
        unfold ret_pre. exists ma. do 16 eexists. do 19 eexists. exists cA, of. split; [reflexivity|].
        destruct INVa as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
        split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
        split; [eapply f16arr_ext; [exact A8| intros j Hj; symmetry; apply workA_get]|].
        split; [eapply f32arr_ext; [exact A9| intros j Hj; symmetry; apply tblA_get]| exact A10]. }
    eapply evtF_cut; [eapply (it_max RNG FR fc gp tp SP SPA S F PB top (cty ty) m1 lf wf cf lo codes bits CX); [lia | lia | exact INVa]|].
    cbv beta. intros ms2 (r10 & r14 & [[-> Hmx2] | [-> HZ]]).
    all: cycle 1.
    -
      eapply evtF_cut; [eapply (it_low RNG FR fc gp tp SP SPA S F PB top (cty ty) m1 lf wf cf lo codes bits CX); [lia | lia | exact HZ | exact INVa]|].
      cbv beta. intros ms3 [HL | (s10 & -> & Hmx0)].
      + eapply KLEFT. exact HL.
      +
        eapply evtF_mono; [eapply (it_max0 RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C); exact INVa|].
        cbv beta. intros ms4 HR. unfold body_post. rewrite (res_phases ty lf lo codes nx bits cf wf).
        replace (mx =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hmx0). cbn [it_ret it_work it_tbl it_table it_bits fst snd].
        eapply ret_pre_ext; [exact HR | intros j Hj; symmetry; apply workA_get | intros; reflexivity].
    - eapply evtF_cut; [eapply (it_rootmin RNG FR fc gp tp SP SPA S F PB top (cty ty) m1 lf wf cf lo codes bits CX); [lia | lia | exact Hmx2 | exact INVa]|].
      cbv beta. intros ms3 HL. eapply KLEFT. exact HL.
  Qed.
End P.
End CANSEC1.
