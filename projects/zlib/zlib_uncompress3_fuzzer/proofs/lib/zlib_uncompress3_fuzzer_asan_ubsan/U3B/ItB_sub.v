(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure UbFit2 ItBGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import ItBTac ItB_base ItB_ldefs ItB_switch ItB_here ItB_fill ItB_cnt2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

Ltac b2z_true := match goal with |- context [Z.b2z (?a <? ?b)] => replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) end; change (Z.b2z true) with 1.
Ltac b2z_false := match goal with |- context [Z.b2z (?a <? ?b)] => replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) end; change (Z.b2z false) with 0.

Ltac lit_reg r := let v := reg_val r in lazymatch v with Z_to_bv 64 ?e => let e' := eval vm_compute in e in change v with (Z_to_bv 64 e') end.
Ltac dec_lt a b H := destruct (Z.ltb_spec a b) as [H|H]; [change (Z.b2z true) with 1 | change (Z.b2z false) with 0].
Ltac close_inv_e := unfold itb_inv, itb_W, frm19; do 10 (split; [eassumption|]); eassumption.

Definition stC (s : ItSt) (c : Z) : ItSt :=
  mkItSt (t_huff s) (t_sym s) (t_len s) (t_next s) c (t_drop s) (t_low s) (t_used s) (t_min s) (t_count s) (t_tbl s) (t_work s).

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top : Z) (m1 : amem).
  Variables (ty : codetype) (lf wf cf : Z -> Z) (lo codes nx bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis C : itc ty lf lo codes nx bits cf wf.

  Notation LP := (S + 168 + 2 * lo).
  Notation cntAr := (cntA lf lo codes).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation work1Ar := (work1A lf lo codes wf).
  Notation w1 := (arr_get (work1A lf lo codes wf)).
  Notation X := (itm_ctx ty (lensA lf) lo nx rt mx).
  Notation BST := (bst SP SPA S F PB LP (cty ty) gp tp FR fc).
  Notation MST := (mst SP SPA S F PB LP (cty ty) gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).
  Notation HEAD := (head_post FR fc gp tp SP SPA S F PB m1 ty lf wf lo codes nx bits).
  Notation RET1 cfx := (ret_pre SP SPA S F PB LP (cty ty) gp tp FR fc m1 1 lf w1 cfx (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits)).
  Notation UST st x5 x6 x7 x10 x11 x12 x16 x17 x30 x31 pc m :=
    (* [U14B] A2 2026-11-12: the 1.4 homes: len in t1 (1.3.1 s9), huff in t4 (t3), (sym + 1) << 32 in t5 (t4); the
       binders x6 / x7 / x30 / x31 (1.3.1 t1 / t2 / t5 / t6) are t2 / t3 / t6 / s9.  x5 / x17 stay t0 / a7: the sub-table
       code uses them as at 1.3.1 (0x9781c sllw a7; 0x9782c ld t0,112(s1); 0x978a0 ld t0,40(s1)); the four entry states
       that still hold the loop's drop (t0 at 1.4) and 2 ^ curr (a7 at 1.4) pass them in the other order. *)
    (BST (Z_to_bv 64 (S + 1384 + 4 * t_next st)) x5 (Z_to_bv 64 (tr_len X st)) x6 x10 x11 x12 SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) x16 x17
         x31 x7 (Z_to_bv 64 (tr_huff st)) (Z_to_bv 64 (Z.shiftl (t_sym st + 1) 32)) x30 pc m).

  Definition currsz_post (st : ItSt) (cv : Z) (m : amem) (x6 x7 x12 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (q5 q10 q11 q17 : word),
      ms' = UST st q5 x6 x7 q10 q11 x12 (Z_to_bv 64 rt) q17 (Z_to_bv 64 cv) x31 0x97848 m.

  Lemma it_curr_loop : forall (k : nat) (curr lft n cr : Z) (cnt : arr) (st : ItSt) (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v120 v128 v136 v144 : word) (of wfx cfx : Z -> Z) (next bitsw : word)
      (x5 x6 x7 x10 x12 x31 : word),
    cr = curr + rt ->
    mx - (curr + rt) <= Z.of_nat k -> Z.of_nat k < n -> 1 <= mx <= 15 -> 1 <= rt <= 15 ->
    1 <= curr -> curr + rt < mx -> 0 < lft <= 2 ^ curr ->
    (forall j, 0 <= j < 16 -> 0 <= arr_get cnt j < 65536) ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 (Z_to_bv 64 (Z.lxor (F + 32) 18446744073709551615))
            v120 v128 v136 v144 (arr_get cnt) of lf wfx cfx next bitsw ->
    evtF bsegs RNG (currsz_post st (fst (loopZ n (curr_body cnt rt mx) (curr, lft))) m x6 x7 x12 x31)
      (UST st x5 x6 x7 x10 (Z_to_bv 64 cr) x12 (Z_to_bv 64 rt) (Z_to_bv 64 lft) (Z_to_bv 64 (mx - rt)) x31 0x977f0 m).
  Proof using All.
    induction k as [|k IH]; intros curr lft n cr cnt st m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v120 v128 v136 v144
      of wfx cfx next bitsw x5 x6 x7 x10 x12 x31 Ecr Hk Hn Hmx RT Hc1 Hcm Hl HCR INV; [exfalso; lia|].
    pose proof INV as INV0. open_ctx CX. open_inv INV. unfold bst.
    assert (P14 : 2 ^ curr <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P14.
    pose proof (HCR (curr + rt) ltac:(lia)) as HCc.
    zs. setreg 10 (Z_to_bv 64 (2 * cr)) ltac:(rewrite shl1_2x; reflexivity).
    zs. zs. ubg.
    zs. do 4 zs.
    pose proof (f16arr_read bsegs m (F + 32) 16 _ cr _ CNT ltac:(lia) eq_refl) as RD.
    zs. rewrite (zx16_small (arr_get cnt cr)) by (rewrite Ecr; lia). clear RD.
    zs. setreg 17 (Z_to_bv 64 (lft - arr_get cnt (curr + rt))) ltac:(rewrite Ecr, (Z.mod_small (arr_get cnt (curr + rt))) by lia; rewrite swrap32_small by lia; reflexivity).
    zs. zbr KL.
    -
      zs. setreg 31 (Z_to_bv 64 curr) ltac:(rewrite swrap32_small by lia; f_equal; lia).
      apply evtF_done. unfold currsz_post. do 4 eexists.
      rewrite curr_stop_le by lia. cbn [fst]. reflexivity.
    - zs. setreg 10 (Z_to_bv 64 0) ltac:(rewrite srliw30_small by lia; reflexivity).
      zs.
      zs. setreg 11 (Z_to_bv 64 (cr + 1)) ltac:(rewrite swrap32_small by lia; reflexivity).
      zs. setreg 17 (Z_to_bv 64 (2 * (lft - arr_get cnt (curr + rt)))) ltac:(rewrite shl1_2x; reflexivity).
      zs. zbr KM.
      +
        rewrite curr_more by lia. rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
        replace ((lft - arr_get cnt (curr + rt)) * 2) with (2 * (lft - arr_get cnt (curr + rt))) by lia.
        eapply (IH (curr + 1) (2 * (lft - arr_get cnt (curr + rt))) (n - 1) (cr + 1) cnt st); try eassumption; try lia.
        rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
      + zs.
        apply evtF_done. unfold currsz_post. do 4 eexists.
        rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. replace (curr + 1) with (mx - rt) by lia. reflexivity.
  Qed.

  Definition currsz_post2 (st : ItSt) (v0 v8 v16 v56 v128 v136 : word) (of : Z -> Z) (x6 x7 x12 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q5 q10 q11 q17 q30 : word),
      ms' = UST st q5 x6 x7 q10 q11 x12 (Z_to_bv 64 rt) q17 q30 x31 0x97854 m
      /\ MINV m (stC (tr_st1 X st) (tr_curr X st)) v0 v8 v16 v56 v128 v136 of.

  Lemma it_currsz : forall (st : ItSt) (m : amem) (v0 v8 v16 v56 v128 v136 : word) (of : Z -> Z)
      (x5 x6 x7 x10 x11 x12 x17 x30 x31 : word),
    1 <= mx <= 15 -> 1 <= rt <= 15 -> 1 <= tr_len X st <= 15 -> rt < tr_len X st -> tr_drop X st = rt ->
    (forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536) ->
    MINV m (tr_st1 X st) v0 v8 v16 v56 v128 v136 of ->
    evtF bsegs RNG (currsz_post2 st v0 v8 v16 v56 v128 v136 of x6 x7 x12 x31)
      (UST st x5 x6 x7 x10 x11 x12 (Z_to_bv 64 rt) x17 x30 x31 0x977c8 m).
  Proof using All.
    intros until x31. intros Hmx RT TLR RTL HDR HCr1 INV.
    set (c0 := tr_len X st - rt). assert (Ec0 : c0 = tr_len X st - rt) by reflexivity.
    pose proof (pow2_le15 c0 ltac:(lia)) as PC0.
    assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
    { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
      fold c0. rewrite Z.shiftl_1_l, swrap32_id by lia. reflexivity. }
    pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (CR1 & CR2 & CR3).
    rewrite <- ETC in CR1, CR2, CR3.
    open_ctx CX. unfold minv in INV. open_inv INV. cbn [t_used t_low t_curr t_count t_tbl t_sym tr_st1] in *.
    unfold bst.
    zs. setreg 11 (Z_to_bv 64 c0) ltac:(rewrite swrap32_small by lia; f_equal; lia).
    zs. zs. zs. ubg.
    zs. zbr KG.
    -
      assert (ETC0 : tr_curr X st = c0) by (apply CR3; lia).
      apply evtF_done. unfold currsz_post2. eexists. do 5 eexists. split; [reflexivity|].
      unfold minv, stC. cbn [t_used t_low t_curr t_count t_tbl t_sym tr_st1]. rewrite ETC0. close_inv.
    - zs. zs. zs. setreg 17 (Z_to_bv 64 (2 ^ c0)) ltac:(rewrite sllw_1 by lia; reflexivity).
      zs. setreg 31 (Z_to_bv 64 (mx - rt)) ltac:(rewrite swrap32_small by lia; f_equal; lia).
      zs.
      eapply evtF_cut.
      { eapply (it_curr_loop 15%nat c0 (2 ^ c0) 16 (tr_len X st) (tr_count st) st);
          [lia | lia | lia | exact Hmx | exact RT | lia | lia | lia | exact HCr1
          | unfold itb_inv, itb_W, frm19; do 10 (split; [eassumption|]); eassumption]. }
      cbv beta. intros ms1 (q5 & q10 & q11 & q17 & ->). rewrite <- ETC.
      assert (HCU : 0 <= tr_curr X st <= 15) by lia.
      unfold bst.
      zs. zs. zs. ubg.
      apply evtF_done. unfold currsz_post2. eexists. do 5 eexists. split; [reflexivity|].
      unfold minv, stC. cbn [t_used t_low t_curr t_count t_tbl t_sym tr_st1]. close_inv.
  Qed.

  Lemma it_reenter : forall (st' : ItSt) (m : amem) (v0 v8 v16 v56 v88 v128 v136 : word) (of : Z -> Z)
      (x5 x7 x10 x11 x12 x17 x30 x31 : word),
    0 <= t_sym st' < 2147483648 -> (t_low st' = 4294967295 \/ 0 <= t_low st' < 32768) ->
    1 <= t_len st' <= 15 -> 0 <= t_drop st' <= 15 ->
    (* [U14B] A2 2026-11-12: the 1.4 combined frame (see minv in ItB_ldefs) *)
    itb_inv SPA S F PB m1 m v0 v8 (Z_to_bv 64 (EXA ty S)) (Z_to_bv 64 (Z.shiftr (S + 160) 3 + 2147450880))
            (Z_to_bv 64 (2 ^ rt - 1)) (Z_to_bv 64 (t_used st')) (Z_to_bv 64 (BSA ty S)) (Z_to_bv 64 (XFL ty)) v56 (Z_to_bv 64 (it_match ty))
            (Z_to_bv 64 (Z.lxor (S + 808) 18446744073709551615)) v88 (Z_to_bv 64 (t_curr st')) (Z_to_bv 64 (t_sym st'))
            (Z_to_bv 64 (Z.lxor (F + 32) 18446744073709551615)) (Z_to_bv 64 (S + 160)) v128 v136 (Z_to_bv 64 F)
            (arr_get (t_count st')) of lf w1 (arr_get (t_tbl st'))
            (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    evtF bsegs RNG (HEAD st' v0 v8 v16 v128 v136 of)
      (* [U14B] A2 2026-11-12: 0x97528 at the 1.4 loop allocation: low in t2 (0x97524 mv t2,a1), len t1, huff t4,
         sym << 32 in t5; x17 / x5 / x7 / x30 / x31 are t0 / a7 / t3 / t6 / s9 *)
      (BST (Z_to_bv 64 (S + 1384 + 4 * t_next st')) x17 (Z_to_bv 64 (t_len st')) (Z_to_bv 64 (lowS (t_low st'))) x10 x11 x12 SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx)
           (Z_to_bv 64 (t_drop st')) x5 x31 x7 (Z_to_bv 64 (t_huff st')) (Z_to_bv 64 (Z.shiftl (t_sym st') 32)) x30 0x974f0 m).
  Proof using All.
    intros until x31. intros HS HL HLN HD INV. open_ctx CX. open_inv INV. unfold bst.
    zs. setreg 12 (Z_to_bv 64 (t_len st' - t_drop st')) ltac:(rewrite swrap32_small by lia; f_equal; lia).
    zs. setreg 11 (Z_to_bv 64 (2 * t_sym st')) ltac:(rewrite zext32_shift31 by lia; reflexivity).
    zs. zs. zs. zs. zs. ubg.
    apply evtF_done. unfold head_post. eexists. do 9 eexists. split; [unfold mst, bst; reflexivity|]. unfold minv. close_inv_e.
  Qed.
  Lemma ne_facts : (isL ty = 0 \/ isL ty = 1) /\ (isD ty = 0 \/ isD ty = 1) /\ isL ty + isD ty <= 1 /\
    (forall u, it_not_enough ty u = (if isL ty =? 1 then 852 <? u else if isD ty =? 1 then 592 <? u else false)).
  Proof. destruct ty; cbn; repeat split; try lia; intros; reflexivity. Qed.
  Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
  Proof. destruct b; reflexivity. Qed.
  Lemma land1_b2z : forall b, Z.land 1 (Z.b2z b) = Z.b2z b.
  Proof. destruct b; reflexivity. Qed.

  Notation SPU := (spure work1Ar rt nx).
  Lemma spure_st1 : forall st, SPU st -> SPU (tr_st1 X st).
  Proof.
    intros st HP. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st1].
    split; [exact WK|]. split; [exact LOWR|]. split; [exact DROPR|]. split; [exact NX0|]. split; [exact NX1|].
    split; [apply tr_count_range0; exact HCr|]. split; [apply tr_tbl1_range; exact HTr|].
    split; [unfold tr_count; rewrite arr_len_set; exact CL | rewrite it_fill_len_tr; exact TL].
  Qed.
  Lemma spure_st3 : forall st, SPU st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st -> SPU (tr_st3 X st).
  Proof.
    intros st HP HL HD HN. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st3].
    split; [exact WK|]. split; [unfold BOX; right; exact HL|]. split; [unfold BOX; right; exact HD|]. split; [lia|]. split; [lia|].
    split; [apply tr_count_range0; exact HCr|]. split; [apply tr_tbl2_range; exact HTr|].
    split; [unfold tr_count; rewrite arr_len_set; exact CL | unfold tr_tbl2; rewrite arr_len_set, it_fill_len_tr; exact TL].
  Qed.
  Lemma tr_huff_range : forall st, 1 <= t_len st <= 15 -> 0 <= t_huff st < 65536 -> 0 <= tr_huff st < 65536 + 16384.
  Proof.
    intros st Flen Fhuff. unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
    pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
    rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
    assert (2 ^ (t_len st - 1) <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
    destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
    assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1) <= t_huff st) by (split; [apply Z.land_nonneg; lia | apply land_le_l; lia]). lia.
  Qed.


  Lemma ne_cases : forall u, (ty = CODES -> it_not_enough ty u = false) /\ (ty = LENS -> it_not_enough ty u = (852 <? u))
                             /\ (ty = DISTS -> it_not_enough ty u = (592 <? u)).
  Proof. intros u. repeat split; intros E; rewrite E; reflexivity. Qed.

  Definition link_post (st : ItSt) (v0 v8 v16 v128 v136 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (HEAD (tr_st3 X st) v0 v8 v16 v128 v136 of ms' /\ it_not_enough ty (tr_used X st) = false /\ SPU (tr_st3 X st))
               \/ (RET1 (arr_get (tr_tbl1 X st)) ms' /\ it_not_enough ty (tr_used X st) = true).

  Lemma it_link : forall (st : ItSt) (m : amem) (v0 v8 v16 v56 v128 v136 : word) (of : Z -> Z)
      (x5 x7 x10 x11 x17 x30 x31 : word),
    MINV m (stC (tr_st1 X st) (tr_curr X st)) v0 v8 v16 v56 v128 v136 of -> SPU st ->
    1 <= rt <= 15 -> 1 <= tr_curr X st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_curr st <= 15 ->
    0 <= tr_low X st < 32768 -> (it_not_enough ty (tr_used X st) = false -> 0 <= nx + tr_low X st < 1444) -> tr_drop X st = rt ->
    0 <= nx -> nx <= t_next st -> t_next st < 1444 -> arr_len (tr_tbl1 X st) = 1444 ->
    0 <= t_sym st < 288 -> 1 <= tr_len X st <= 15 -> rt < tr_len X st ->
    evtF bsegs RNG (link_post st v0 v8 v16 v128 v136 of)
      (UST st x5 (Z_to_bv 64 (tr_low X st)) x7 x10 x11 (Z_to_bv 64 (S + 1384 + 4 * tr_next st)) (Z_to_bv 64 rt) x17 x30 x31 0x97854 m).
  Proof using All.
    intros until x31. intros INV HSPU RT HCU Fused Fcurr HLOW Flow3 HDR Hnx NX1 Hroom TL1 Fsym TLR RTL.
    pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC.
    assert (EU : tr_used X st = t_used st + 2 ^ tr_curr X st).
    { unfold tr_used. rewrite Z.shiftl_1_l. apply wrap32_small. lia. }
    assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
    assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
    pose proof (ne_cases (tr_used X st)) as (NEC & NEL & NED).
    pose proof INV as INV0. open_ctx CX. unfold minv in INV. open_inv INV. cbn [t_used t_low t_curr t_count t_tbl t_sym tr_st1 stC] in *. rewrite ESY in FRM.
    assert (FAIL : forall (mm : amem) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31 : word)
                          (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 : word) (cnt ofx : Z -> Z),
              itb_inv SPA S F PB m1 mm u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u136 u144 cnt ofx lf w1 (arr_get (tr_tbl1 X st))
                      (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
              it_not_enough ty (tr_used X st) = true ->
              link_post st v0 v8 v16 v128 v136 of
                (BST y1 y5 y6 y7 (Z_to_bv 64 1) y11 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31 0x97a80 mm)).
    { intros. right. split; [|assumption]. unfold ret_pre. exists mm. do 16 eexists. do 19 eexists. exists cnt, ofx. split; [reflexivity | eassumption]. }
    assert (LINK : it_not_enough ty (tr_used X st) = false ->
              forall (z11 z17 : word), evtF bsegs RNG (link_post st v0 v8 v16 v128 v136 of)
                (UST st (Z_to_bv 64 (tr_used X st)) (Z_to_bv 64 (tr_low X st)) x7 (Z_to_bv 64 1) z11 (Z_to_bv 64 (S + 1384 + 4 * tr_next st))
                     (Z_to_bv 64 rt) z17 x30 x31 0x97894 m)).
    { intros HNE z11 z17. specialize (Flow3 HNE). unfold bst.
      zs.
      zs. zs. zs.
      zs. zs.
      zs. zs. setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (nx + tr_low X st))) ltac:(rewrite shl2_4x; f_equal; lia).
      zs. ubg.
      zs. snez1 11. zs. seqz0 17. zs. zs.    (* [U14B] A2: 0x978f0 snez a1,t0; 0x978f4 seqz a7,a0 (1.3.1 seqz t0) *)
      zs. ubg.
      zs. zs. ubg.
      f32_open_at CDS (nx + tr_low X st) D ED CH CC.
      do 4 zs.
      zs. zs.
      zs. ubg.
      zs. do 4 zs. zs.
      zs. do 4 zs.
      zs. zs. setreg 11 (Z_to_bv 64 (tr_next st - nx))
                ltac:(replace (S + 1384 + 4 * tr_next st - (S + 1384 + 4 * nx)) with ((tr_next st - nx) * 2 ^ 2) by lia;
                      rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_mul by lia; reflexivity).
      zs.
      f32_close_at CH CC ED (code_pack (wrap8 (tr_curr X st)) rt (tr_next st - nx)) CDS; [apply entry_bytes; lia|]. subst D.
      assert (HIDX : 0 <= nx + tr_low X st < arr_len (tr_tbl1 X st)) by (rewrite TL1; lia).
      assert (W8 : wrap8 (tr_curr X st) = tr_curr X st) by (rewrite wrap8_mod; apply Z.mod_small; lia).
      rewrite W8 in CDS.
      apply (fun H => f32arr_ext bsegs _ _ _ _ (arr_get (tr_tbl2 X st)) H
                        (fun j _ => fupd_arr_set (tr_tbl1 X st) (nx + tr_low X st) (code_pack (tr_curr X st) rt (tr_next st - nx)) j HIDX)) in CDS.
      zs. zs.
      pose proof (fun mm u0 u8 u16 u56 u88 u128 u136 ofx y5 y7 y10 y11 y12 y17 y30 y31 =>
                    it_reenter (tr_st3 X st) mm u0 u8 u16 u56 u88 u128 u136 ofx y5 y7 y10 y11 y12 y17 y30 y31) as HR.
      cbn [t_drop t_len t_huff t_next t_sym t_curr t_low t_used t_count t_tbl tr_st3] in HR.
      rewrite HDR, (lowS_small (tr_low X st)), ESY in HR by lia.
      eapply evtF_mono; [eapply HR|].
      - lia.
      - right. lia.
      - lia.
      - lia.
      - unfold itb_inv, itb_W, frm19; do 10 (split; [first [eassumption | match goal with |- ?g => idtac "FAILCONJ" g end]|]); eassumption.
      - intros ms' HP. left. split; [exact HP|]. split; [exact HNE|]. apply spure_st3; [exact HSPU | exact HLOW | exact HDR | lia]. }
    Local Ltac enough_head EU PC3 :=
      zs; zs; zs; zs; zs;
      lazymatch goal with |- context [Z.shiftl 1 (?c mod 32)] =>
        setreg 17 (Z_to_bv 64 (2 ^ c)) ltac:(rewrite sllw_1 by lia; reflexivity) end;
      zs; zs;
      lazymatch goal with |- context [bv_swrap 32 (2 ^ ?c + ?u)] =>
        setreg 5 (Z_to_bv 64 (u + 2 ^ c)) ltac:(rewrite swrap32_small by lia; f_equal; lia) end;
      rewrite <- EU.
    unfold bst.
    destruct (ty_cases ty S) as [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | (ET & ECT & EM & EEX & EBS & ENE & EL & ED)]];
      rewrite ECT; unfold bst in LINK, FAIL; rewrite ECT in LINK, FAIL.
    -
      enough_head EU PC3. lit_reg 11.
      zs. dec_lt (tr_used X st) 853 U8; (zs; lit_reg 11; zs; zs; zs; dec_lt (tr_used X st) 593 U5;
        (zs; lit_reg 11; zs; lit_reg 17; zs; lit_reg 11; zs; eapply LINK; apply NEC; exact ET)).
    -
      enough_head EU PC3. lit_reg 11.
      zs. dec_lt (tr_used X st) 853 U8; (zs; lit_reg 11; zs).
      + zs. zs. dec_lt (tr_used X st) 593 U5;
          (zs; lit_reg 11; zs; lit_reg 17; zs; lit_reg 11; zs; eapply LINK; rewrite (NEL ET); apply Z.ltb_ge; lia).
      + apply evtF_done. eapply FAIL; [close_inv_e|]. rewrite (NEL ET). apply Z.ltb_lt. lia.
    -
      enough_head EU PC3. lit_reg 11.
      zs. dec_lt (tr_used X st) 853 U8; (zs; lit_reg 11; zs; zs; zs; dec_lt (tr_used X st) 593 U5;
        (zs; lit_reg 11; zs; lit_reg 17; zs; lit_reg 11; zs)).
      1, 3: (eapply LINK; rewrite (NED ET); apply Z.ltb_ge; lia).
      all: (apply evtF_done; eapply FAIL; [close_inv_e|]; rewrite (NED ET); apply Z.ltb_lt; lia).
  Qed.

  Definition sub_post (st : ItSt) (v0 v8 v16 v128 v136 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (HEAD (tr_st1 X st) v0 v8 v16 v128 v136 of ms' /\ tr_sub X st = false)
               \/ (link_post st v0 v8 v16 v128 v136 of ms' /\ tr_sub X st = true).

  Lemma zext32_shift30 : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = 4 * x.
  Proof.
    intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
    change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
  Qed.

  Lemma it_sub : forall (st : ItSt) (m : amem) (v0 v8 v16 v56 v128 v136 : word) (of : Z -> Z)
      (x6 x7 x10 x11 x12 x16 x30 x31 : word),
    MINV m (tr_st1 X st) v0 v8 v16 v56 v128 v136 of -> spure work1Ar rt nx st -> it_trip_ok X 288 320 1444 st = true ->
    tr_brk X st = false -> 1 <= mx ->
    evtF bsegs RNG (sub_post st v0 v8 v16 v128 v136 of)
      (UST st (Z_to_bv 64 (t_drop st)) x6 x7 x10 x11 x12 x16 (Z_to_bv 64 (2 ^ t_curr st)) x30 x31 0x9778c m).
  Proof using All.
    intros until x31. intros INV HP TOK Hbrk Hmx.
    pose proof C as C'. open_itc C'. open_spure HP. clear HtyC HtyD Hcf Hwf Hlens15.
    pose proof (mx_range cntAr) as MXR. fold mx in MXR. pose proof (rt_facts lf lo codes bits Hmx) as (RT1 & RT2 & RT3).
    trip_facts TOK. clear Fwm.
    pose proof (pow2_le15 rt ltac:(lia)) as PRT. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC.
    assert (TLR : 1 <= tr_len X st <= 15).
    { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx].
      destruct (Z.eqb_spec (tr_c st) 0) as [E0|NE0]; [|cbn [andb]; lia].
      destruct (Z.eqb_spec (t_len st) mx) as [EM|NEM]; cbn [andb negb]; [lia|].
      unbox Flook. destruct (Flook E0 NEM) as (W1 & W2 & W3 & W4).
      replace (tr_sym st) with (t_sym st + 1) by (unfold tr_sym; symmetry; apply wrap32_small; lia). rewrite lensA_get in W4 |- *. exact W4. }
    clear Flook.
    pose proof (tr_huff_range st Flen Fhuff) as HHF.
    assert (HLOW : 0 <= tr_low X st < 32768).
    { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia.
      split; [apply Z.land_nonneg; lia|]. eapply Z.le_lt_trans; [apply land_le_r; lia | lia]. }
    assert (ELOW : Z.land (tr_huff st) (2 ^ rt - 1) = tr_low X st).
    { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia. reflexivity. }
    assert (HDR : tr_drop X st = rt).
    { unfold tr_drop. cbn [x_root itm_ctx]. unbox DROPR. destruct DROPR as [D0|D1]; rewrite D0 || rewrite D1; [reflexivity|].
      destruct (Z.eqb_spec rt 0); lia. }
    assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
    assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
    assert (NXB : t_next st < 1444).
    { pose proof (pow2_le15 (t_len st - t_drop st) ltac:(lia)).
      assert (2 ^ (t_len st - t_drop st) <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
      assert (0 <= Z.shiftr (t_huff st) (t_drop st)) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]). lia. }
    pose proof INV as INV0. open_ctx CX. unfold minv in INV. open_inv INV. cbn [t_used t_low t_curr t_count t_tbl t_sym tr_st1] in *.
    assert (SAME : tr_sub X st = false -> forall (y5 y6 y7 y10 y12 y16 y30 y31 : word),
              evtF bsegs RNG (sub_post st v0 v8 v16 v128 v136 of)
                (UST st (Z_to_bv 64 (t_drop st)) y6 y7 y10 (Z_to_bv 64 (lowS (t_low st))) y12 y16 y5 y30 y31 0x974e8 m)).
    { intros Hsub y5 y6 y7 y10 y12 y16 y30 y31. unfold bst. zs. zs.
      pose proof (fun mm u0 u8 u16 u56 u88 u128 u136 ofx z5 z7 z10 z11 z12 z17 z30 z31 =>
                    it_reenter (tr_st1 X st) mm u0 u8 u16 u56 u88 u128 u136 ofx z5 z7 z10 z11 z12 z17 z30 z31) as HR.
      cbn [t_drop t_len t_huff t_next t_sym t_curr t_low t_used t_count t_tbl tr_st1] in HR. rewrite ESY in HR.
      eapply evtF_mono; [eapply HR|].
      - lia.
      - unbox LOWR. exact LOWR.
      - lia.
      - unbox DROPR. lia.
      - rewrite <- ESY. exact INV0.
      - intros ms' HP'. left. split; [exact HP' | exact Hsub]. }
    unfold bst.
    zs. zs. zbr KR.
    -
      eapply SAME.
      unfold tr_sub. cbn [x_root itm_ctx]. replace (rt <? tr_len X st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - zs. zs. setreg 7 (Z_to_bv 64 (tr_low X st)) ltac:(rewrite ELOW; reflexivity).
      assert (J68 : tr_sub X st = true -> forall (y10 y11 : word),
                evtF bsegs RNG (sub_post st v0 v8 v16 v128 v136 of)
                  (UST st (Z_to_bv 64 (t_drop st)) (Z_to_bv 64 (tr_low X st)) x7 y10 y11 x12 x16 (Z_to_bv 64 (2 ^ t_curr st)) x30 x31 0x977a4 m)).
      { intros Hsub y10 y11.
        assert (RTL : rt < tr_len X st).
        { unfold tr_sub in Hsub. apply andb_prop in Hsub as [H1 _]. cbn [x_root itm_ctx] in H1. apply Z.ltb_lt in H1. exact H1. }
        assert (HCr1 : forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536) by (apply tr_count_range0; exact HCr).
        assert (AT4 : forall (y17 : word), evtF bsegs RNG (sub_post st v0 v8 v16 v128 v136 of)
                  (UST st y17 (Z_to_bv 64 (tr_low X st)) x7 y10 y11 x12 (Z_to_bv 64 rt) (Z_to_bv 64 (2 ^ t_curr st)) x30 x31 0x977b0 m)).
        { intros y17. unfold bst.
          zs. ubg.
          zs. zs. setreg 12 (Z_to_bv 64 (4 * 2 ^ t_curr st)) ltac:(rewrite zext32_shift30 by lia; reflexivity).
          zs. setreg 12 (Z_to_bv 64 (S + 1384 + 4 * tr_next st)) ltac:(rewrite ENX; f_equal; lia).
          zs. ubg. zs. ubg.
          eapply evtF_cut; [eapply (it_currsz st m v0 v8 v16 v56 v128 v136 of); [lia | lia | exact TLR | exact RTL | exact HDR | exact HCr1 | exact INV0]|].
          cbv beta. intros ms1 (m2 & q5 & q10 & q11 & q17 & q30 & -> & INV2).
          set (c0 := tr_len X st - rt).
          assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
          { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
            fold c0. rewrite Z.shiftl_1_l, swrap32_id by (pose proof (pow2_le15 c0 ltac:(unfold c0; lia)); lia). reflexivity. }
          pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(unfold c0; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold c0; lia)) as (CR1 & CR2 & CR3).
          rewrite <- ETC in CR1, CR2, CR3.
          assert (HCU : 1 <= tr_curr X st <= 15).
          { destruct (Z_le_gt_dec (c0 + rt) mx) as [LE|GT]; [specialize (CR2 LE); unfold c0 in *; lia | rewrite (CR3 ltac:(lia)); unfold c0; lia]. }
          eapply evtF_mono; [eapply (it_link st m2 v0 v8 v16 v56 v128 v136 of);
                               [exact INV2 | exact HP | lia | exact HCU | lia | lia | exact HLOW | | exact HDR | lia | exact NX1 | | | lia | exact TLR | exact RTL] |].
          -
            intros HNE.
            assert (HST3 : it_step X st = ItCont (tr_st3 X st)).
            { rewrite it_step_eq. rewrite Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite HNE. reflexivity. }
            unbox Fcont. destruct (Fcont (tr_st3 X st) HST3) as (Flow3 & Fcurr3 & Fnext3).
            { right. cbn [t_next tr_st3]. unfold tr_next, tr_fill. rewrite shl32_1 by lia. lia. }
            cbn [t_low tr_st3] in Flow3. exact Flow3.
          - exact NXB.
          - rewrite it_fill_len_tr. exact TL.
          - intros ms' HP'. right. split; [exact HP' | exact Hsub]. }
        unfold bst. zs.
        unbox DROPR. destruct DROPR as [D0|D1].
        - rewrite D0. zs. eapply AT4.
        - zs. zbr KD0. zs. rewrite D1. eapply AT4. }
      unbox LOWR. destruct LOWR as [LM|LSM].
      +
        rewrite LM. change (lowS 4294967295) with (-1).
        zs. zs. zbr KQ. eapply J68.
        unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, LM.
        replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Z.eqb_spec (tr_low X st) 4294967295); [lia | reflexivity].
      + zs. rewrite (sextw_lowS (t_low st)) by (right; exact LSM).
        zs. rewrite (lowS_small (t_low st)) by lia. zbr KQ.
        *
          rewrite <- (lowS_small (t_low st)) by lia. eapply SAME.
          unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, KQ, Z.eqb_refl. cbn [negb]. apply Bool.andb_false_r.
        * eapply J68.
          unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW.
          replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
          destruct (Z.eqb_spec (tr_low X st) (t_low st)); [lia | reflexivity].
  Qed.
End P.
End CANSEC1.
