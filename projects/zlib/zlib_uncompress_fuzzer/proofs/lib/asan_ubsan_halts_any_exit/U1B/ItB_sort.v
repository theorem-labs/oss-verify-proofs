(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import ItB_base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top TY : Z) (m1 : amem).
  Variables (lf wf cf : Z -> Z) (lo codes : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis Hlf : forall i, 0 <= i < 320 -> 0 <= lf i < 65536.
  Hypothesis Hlo : 0 <= lo.
  Hypothesis Hlc : lo + codes <= 320.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hl15 : forall s, 0 <= s < codes -> lf (lo + s) <= 15.
  Hypothesis SOK : it_sort_ok (lensA lf) lo codes (offsA lf lo codes) 288 = true.

  Notation LP := (S + 168 + 2 * lo).
  Notation ST := (bst SP SPA S F PB LP TY gp tp FR fc).
  Notation cA := (arr_get (cntA lf lo codes)).
  Notation SKo i := (fst (itm_sort_k (lensA lf) lo i (offsA lf lo codes) (workA wf))).
  Notation SKw i := (snd (itm_sort_k (lensA lf) lo i (offsA lf lo codes) (workA wf))).

  Definition sort_post (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (next bitsw : word)
      (x1 x12 x13 x14 x15 : word) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q5 q6 q7 q10 q11 q17 q25 q28 q29 q30 q31 : word) (of : Z -> Z),
      ms' = ST x1 q5 q6 q7 q10 q11 x12 x13 x14 x15 (Z_to_bv 64 (F + 96)) q17 q25 q28 q29 q30 q31 0x9702c m
      /\ itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 cA of lf
                 (arr_get (work1A lf lo codes wf)) cf next bitsw.

  Lemma it_sort_loop : forall (k : nat) (i : Z) (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (of wfi : Z -> Z) (next bitsw : word)
      (x1 x10 x11 x12 x13 x14 x15 x31 : word),
    Z.of_nat k = codes - i -> 0 <= i < codes ->
    (forall j, 1 <= j <= 15 -> of j = arr_get (SKo i) j) ->
    (forall j, 0 <= j < 288 -> wfi j = arr_get (SKw i) j) ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 cA of lf wfi cf next bitsw ->
    evtF bsegs RNG (sort_post v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 next bitsw x1 x12 x13 x14 x15)
      (ST x1 (Z_to_bv 64 (Z.lxor (F + 96) 18446744073709551615)) (Z_to_bv 64 (Z.land LP 1)) (Z_to_bv 64 (Z.lxor LP 18446744073709551615))
          x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (F + 96)) (Z_to_bv 64 i)
          (Z_to_bv 64 (Z.shiftl codes 32)) (Z_to_bv 64 16) (Z_to_bv 64 codes) (Z_to_bv 64 1) x31 0x96f70 m).
  Proof using All.
    induction k as [|k IH]; intros i m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 of wfi next bitsw
      x1 x10 x11 x12 x13 x14 x15 x31 Hk Hi HOF HWF INV; [lia|].
    open_ctx CX. open_inv INV. unfold bst.
    pose proof (Hlf (lo + i) ltac:(lia)) as L0. pose proof (Hl15 i Hi) as L15.
    assert (HOr : forall j, 0 <= arr_get (SKo i) j < 65536) by (intros j; unfold offsA; apply itm_sort_k_offs_range).
    assert (J : forall (mj : amem) (ofj wfj : Z -> Z) (y10 y11 y31 : word),
      (forall j, 1 <= j <= 15 -> ofj j = arr_get (SKo (i + 1)) j) ->
      (forall j, 0 <= j < 288 -> wfj j = arr_get (SKw (i + 1)) j) ->
      itb_inv SPA S F PB m1 mj v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 cA ofj lf wfj cf next bitsw ->
      evtF bsegs RNG (sort_post v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 next bitsw x1 x12 x13 x14 x15)
        (ST x1 (Z_to_bv 64 (Z.lxor (F + 96) 18446744073709551615)) (Z_to_bv 64 (Z.land LP 1)) (Z_to_bv 64 (Z.lxor LP 18446744073709551615))
            y10 y11 x12 x13 x14 x15 (Z_to_bv 64 (F + 96)) (Z_to_bv 64 i)
            (Z_to_bv 64 (Z.shiftl codes 32)) (Z_to_bv 64 16) (Z_to_bv 64 codes) (Z_to_bv 64 1) y31 0x96f68 mj)).
    { intros mj ofj wfj y10 y11 y31 HOFj HWFj INVj. unfold bst.
      zs. zs. zbr0 KJ.
      -
        apply evtF_done. unfold sort_post. exists mj. do 11 eexists. exists ofj. split; [reflexivity|].
        destruct INVj as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
        split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [| exact A9].
        eapply f16arr_ext; [exact A8|]. intros j Hj. rewrite (HWFj j) by lia.
        unfold work1A. rewrite itm_work_eq. replace codes with (i + 1) by lia. reflexivity.
      - eapply (IH (i + 1)); [lia | lia | exact HOFj | exact HWFj | exact INVj]. }
    zs. setreg 10 (Z_to_bv 64 (2 * i)) ltac:(rewrite shl1_2x; reflexivity).
    zs. ubg. zs. ubg.
    zs. replace (S + 168 + 2 * lo + 2 * i) with (S + 168 + 2 * (lo + i)) by lia.
    do 4 zs.
    pose proof (f16arr_read bsegs m (S + 168) 320 lf (lo + i) _ LENS ltac:(lia) eq_refl) as RD.
    zs. rewrite (zx16_small (lf (lo + i))) by lia. clear RD.
    zs. zbr0 KZ.
    -
      eapply (J m of wfi); [| | close_inv].
      + intros j Hj. rewrite sort_k_skip; [apply HOF; exact Hj | lia | rewrite lensA_get; exact KZ].
      + intros j Hj. rewrite sort_k_skip; [apply HWF; exact Hj | lia | rewrite lensA_get; exact KZ].
    - pose proof (sort_ok_at (lensA lf) lo codes (offsA lf lo codes) (workA wf) 288 i SOK ltac:(lia) ltac:(rewrite lensA_get; exact KZ)) as HO.
      rewrite lensA_get in HO.
      assert (EO : of (lf (lo + i)) = arr_get (SKo i) (lf (lo + i))) by (apply HOF; lia).
      zs. ubg.
      zs. setreg 10 (Z_to_bv 64 (2 * lf (lo + i))) ltac:(rewrite shl1_2x; reflexivity).
      zs. ubg.
      zs.
      do 4 zs.
      f16_open_at OFFS (lf (lo + i)) C EC CH CC. rewrite EO in CC.
      zs. rewrite (zx16_small (arr_get (SKo i) (lf (lo + i)))) by lia.
      zs. zs. setreg 10 (Z_to_bv 64 (2 * arr_get (SKo i) (lf (lo + i)))) ltac:(rewrite shl1_2x; reflexivity).
      zs. zs.
      f16_close_at CH CC EC (arr_get (SKo i) (lf (lo + i)) + 1) OFFS; [reflexivity|]. subst C.
      zs. ubg.
      zs. setreg 11 (Z_to_bv 64 0) ltac:(replace (S + 808 + 2 * arr_get (SKo i) (lf (lo + i)) <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      zs. zs.
      zs. ubg.
      zs. zs. ubg.
      do 4 zs.
      f16_open_at WORK (arr_get (SKo i) (lf (lo + i))) D ED WH WC.
      zs.
      f16_close_at WH WC ED i WORK; [reflexivity|]. subst D.
      eapply (J _ (fupd of (lf (lo + i)) (arr_get (SKo i) (lf (lo + i)) + 1)) (fupd wfi (arr_get (SKo i) (lf (lo + i))) i)); [| | close_inv].
      + intros j Hj. rewrite sort_k_take by (try lia; rewrite lensA_get; exact KZ). cbv zeta. rewrite lensA_get. cbn [fst].
        rewrite arr_get_set. unfold arr_inb. rewrite (proj1 (sort_k_len _ _ _ _ _)), offsA_len.
        rewrite wrap16_small by lia. unfold fupd.
        destruct (Z.eqb_spec j (lf (lo + i))) as [->|NE].
        * rewrite Z.eqb_refl. replace ((0 <=? lf (lo + i)) && (lf (lo + i) <? 16)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          reflexivity.
        * replace (lf (lo + i) =? j) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. apply HOF. exact Hj.
      + intros j Hj. rewrite sort_k_take by (try lia; rewrite lensA_get; exact KZ). cbv zeta. rewrite lensA_get. cbn [snd].
        rewrite (wrap16_small i) by lia. rewrite <- fupd_arr_set by (rewrite (proj2 (sort_k_len _ _ _ _ _)), workA_len; lia).
        unfold fupd. destruct (j =? arr_get (SKo i) (lf (lo + i))); [reflexivity | apply HWF; exact Hj].
  Qed.
  Lemma it_sort : forall (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (of : Z -> Z) (next bitsw : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
    (forall k, 1 <= k <= 15 -> of k = arr_get (offsA lf lo codes) k) ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 cA of lf wf cf next bitsw ->
    evtF bsegs RNG (sort_post v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 next bitsw x1 x12 x13 x14 x15)
      (ST x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (F + 96)) x17 (Z_to_bv 64 codes) x28 x29 x30 x31 0x96f38 m).
  Proof using All.
    intros until x31. intros HOF INV. open_ctx CX. unfold bst. zs. zbr0 K.
    -
      apply evtF_done. unfold sort_post. exists m. do 11 eexists. exists of. split; [reflexivity|].
      destruct INV as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [| exact A9].
      eapply f16arr_ext; [exact A8|]. intros j Hj. unfold work1A. rewrite itm_work_eq, itm_sort_k_0 by lia. cbn [snd].
      symmetry. apply workA_get.
    - zs. ubg. zs. zs. zs. zs. zs. zs. zs.
      setreg 29 (Z_to_bv 64 codes) ltac:(rewrite Z.mod_small by lia; reflexivity).
      zs. setreg 30 (Z_to_bv 64 1) ltac:(replace (0 <? S + 808) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      zs.
      pose proof (it_sort_loop (Z.to_nat codes) 0 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 of wf next bitsw
                    x1 x10 x11 x12 x13 x14 x15 x31 ltac:(lia) ltac:(lia)) as HL.
      apply HL; [| | exact INV].
      + intros j Hj. rewrite itm_sort_k_0 by lia. cbn [fst]. apply HOF. exact Hj.
      + intros j Hj. rewrite itm_sort_k_0 by lia. cbn [snd]. symmetry. apply workA_get.
  Qed.
End P.
End CANSEC1.
