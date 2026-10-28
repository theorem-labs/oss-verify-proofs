(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseRdKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AF_fse_rd_base AF_fse_rd_cnt1.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= rdA_acc_hint.

Section CANSEC1. Context {rc : runConstT}.
Section Count.
  Variable C : rdctxA.
  Variable RNG : footprint.
  Hypothesis OK : rd_okA C.
  Hypothesis SH : rd_shA C.
  Hypothesis RNGS : rd_rngA C RNG.
  Variable tl : Z.
  Hypothesis Htl : 5 <= tl <= 15.
  Variable POST : machine_state -> Prop.

  Notation buf := (a_buf C).
  Notation msv1 := (a_msv0 C + 1).
  Notation BUF := (a_BUF C).
  Notation NC := (a_NC C).

  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
  Ltac zify_lts K :=
    unfold bv_lts in K; rewrite ?land7_mod in K;
    rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
    zify_bool K.
  Let cnt_hbA := cnt_hbA C RNG OK RNGS POST.
  Let cnt_finA := cnt_finA C RNG OK SH RNGS POST.

  (* [comment removed for export] *)
  Lemma cnt_tailA : forall s m1 msvw tlw count0 addb fl (x11 x14 x15 x30 : word),
    rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
    x14 = Z_to_bv 64 (if 0 <? count0 then 1 - count0 else -1) ->
    rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
    (forall s' m2 y6 y11 y14 y15 y17 y19 y23 y30, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
        evtF bsegs RNG POST (rd_exitA C s' m2 y6 y11 y14 y15 y17 y19 y23 y30)) ->
    (forall s' m2 y12 y14 y15 y19 y30, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
        evtF bsegs RNG POST (rd_headA C s' m2 y12 y14 y15 y19 y30)) ->
    evtF bsegs RNG POST (rd_lstA C 0xaaf34 m1 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (BUF + r_ip s)) x11 (Z_to_bv 64 addb)
                           (Z_to_bv 64 (r_charnum s)) x14 x15
                           (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (count0 + -1))
                           (Z_to_bv 64 (r_nbBits s)) x30).
  Proof.
    intros s m1 msvw tlw count0 addb fl x11 x14 x15 x30 INV HC HP HB32 Hc0 Haddb -> RR KB KC.
    destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
    pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
    pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA1 & SPA2 & NC1 & NC2 & N8 & _).
    pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
    destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
    set (DR := if 0 <? count0 then 1 - count0 else -1) in *.
    assert (RDR : - 2^31 <= DR <= 0 /\ 1 <= rem + DR) by (subst DR; destruct (Z.ltb_spec 0 count0); lia).
    assert (UN : unpoisoned m1 NC (NC + 2 * zlen (a_rt0 C))) by (destruct INV as (_ & _ & _ & _ & _ & _ & _ & MU & _); apply (inv_shadowA C m1 OK SH MU)).
    assert (LWS : length (map (Z_to_bv 64) nc) = length (a_rt0 C)) by (rewrite length_map; destruct INV as (_ & LNC & _); exact LNC).
    (* [comment removed for export] *)
    destruct (chk1A m1 NC (NC + 2 * zlen (a_rt0 C)) (NC + 2 * cn) 2 UN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia))
      as (b & RDB & CK & SR).
    clear UN.
    unfold rd_lstA.
    zstep. zstep. rewrite (shl32_shr31 cn) by lia.                          (* [comment removed for export] *)
    zstep.                                                                   (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite sxb_sval.                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (JOIN : forall (y15 y30 : word),
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 16843009) (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C) (Z_to_bv 64 18446744071562067968) (Z_to_bv 64 bc) (Z_to_bv 64 23)
                 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) (Z_to_bv 64 (BUF + ip)) (Z_to_bv 64 (NC + 2 * cn)) (Z_to_bv 64 addb) (Z_to_bv 64 cn)
                 (Z_to_bv 64 DR) y15 (Z_to_bv 64 rem) (Z_to_bv 64 thr)
                 (Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (count0 + -1)) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 252645135) (Z_to_bv 64 nb)
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) (Z_to_bv 64 (a_msv0 C + 1))
                 (Z_to_bv 64 (BUF + zlen buf + -7)) (Z_to_bv 64 125613361) y30 (Z_to_bv 64 858993459))
             (a_F C) (Z_to_bv 64 0xaaf50) (a_fc C) None m1 (seg_rom bsegs))).
    { intros y15 y30. clear RDB CK SR.
      zstep. rewrite (FseWalkKit.swrap32_small (addb + bc)) by lia. replace (addb + bc) with (bc + addb) by lia.   (* [comment removed for export] *)
      zstep. rewrite (addw_neg DR rem) by lia.                                                         (* [comment removed for export] *)
      zstep. rewrite (FseWalkKit.swrap32_small (cn + 1)) by lia.                                                  (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof (u16arr_store_ok bsegs _ NC _ cn (wa (NC + 2 * cn)) (proj1 INV) ltac:(rewrite LWS; lia) eq_refl) as SOK.
      zstep. clear SOK.
      pose proof (rd_invA_store2 C m1 nc msvw tlw cn (count0 + -1) OK INV ltac:(lia)) as INV2.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        change mm with (write_to_mem m1 (wa (NC + 2 * cn)) (le2 (Z_to_bv 64 (count0 + -1)))) end.
      remember (write_to_mem m1 (wa (NC + 2 * cn)) (le2 (Z_to_bv 64 (count0 + -1)))) as m eqn:Hm. clear Hm INV.
      (* [comment removed for export] *)
      unfold rcount_rest in RR. cbnR.
      replace (count0 - 1) with (count0 + -1) in RR by lia.
      rewrite (zstore_ok nc cn) in RR by (unfold FseNCount.Zlength; lia). cbn [bind] in RR.
      replace (if 0 <=? count0 + -1 then rem - (count0 + -1) else rem + (count0 + -1)) with (rem + DR) in RR
        by (subst DR; destruct (Z.ltb_spec 0 count0); destruct (Z.leb_spec 0 (count0 + -1)); lia).
      set (nc' := Zupd cn (to_short (count0 + -1)) nc) in *.
      zstep.                                                                                           (* [comment removed for export] *)
      if_cases B1; zify_cond B1; rewrite !signed_lit in B1 by lia.
      - (* [comment removed for export] *)
        replace (rem + DR <? thr) with false in RR by (symmetry; apply Z.ltb_ge; lia). cbn [bind] in RR.
        eapply (cnt_finA (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m msvw tlw (count0 + -1) fl);
          cbnR; try eassumption; try lia; try reflexivity.
      - replace (rem + DR <? thr) with true in RR by (symmetry; apply Z.ltb_lt; lia).
        zstep. zstep.                                                                                  (* [comment removed for export] *)
        if_cases B2; zify_cond B2; rewrite ?signed_lit in B2 by lia.
        + (* [comment removed for export] *)
          replace (rem + DR <=? 1) with true in RR by (symmetry; apply Z.leb_le; lia). cbn [bind] in RR. injection RR as <-.
          pose proof (KB (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m) as KB'.
          unfold rd_exitA, rd_lstA in KB'. cbnR.
          eapply KB'; [reflexivity| exact INV2|]. unfold rd_brk_okA. cbnR. change (2^31) with 2147483648. lia.
        + replace (rem + DR <=? 1) with false in RR by (symmetry; apply Z.leb_gt; lia).
          unfold highbit32, assert in RR.
          replace ((0 <? rem + DR) && (rem + DR <? 2 ^ 32)) with true in RR
            by (symmetry; apply andb_true_iff; split; [apply Z.ltb_lt| apply Z.ltb_lt]; lia).
          cbn [bind] in RR.
          assert (L2 : 1 <= Z.log2 (rem + DR) < 15).
          { split; [apply Z.log2_le_pow2; lia| apply Z.log2_lt_pow2; lia]. }
          replace (Z.log2 (rem + DR) + 1 - 1) with (Z.log2 (rem + DR)) in RR by lia.
          replace ((0 <=? Z.log2 (rem + DR)) && (Z.log2 (rem + DR) <? 31)) with true in RR
            by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
          cbn [bind] in RR.
          pose proof (cnt_hbA (rem + DR) m nc' msvw tlw) as HBK. unfold rd_lstA in HBK.
          eapply HBK; [exact INV2| lia|]. intros y11 y14 y15' y17 y23 -> ->.
          eapply (cnt_finA (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) (2 ^ Z.log2 (rem + DR)) (Z.log2 (rem + DR) + 1) (count0 + -1 =? 0))
                    m msvw tlw (count0 + -1) fl);
            cbnR; try eassumption; try lia; try reflexivity. }
    zstep. if_cases G; zify_cond G.                                          (* [comment removed for export] *)
    - zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply JOIN.
    - apply JOIN.
  Qed.

  (* [comment removed for export] *)
  Lemma count_runA : forall s m1 msvw tlw fl (x12 x14 x15 x19 x30 : word),
    rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    rcount_block buf msv1 s = Ok fl ->
    (forall s' m2 y6 y11 y14 y15 y17 y19 y23 y30, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
        evtF bsegs RNG POST (rd_exitA C s' m2 y6 y11 y14 y15 y17 y19 y23 y30)) ->
    (forall s' m2 y12 y14 y15 y19 y30, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
        evtF bsegs RNG POST (rd_headA C s' m2 y12 y14 y15 y19 y30)) ->
    evtF bsegs RNG POST (rd_cntA C s m1 x12 x14 x15 x19 x30).
  Proof.
    intros s m1 msvw tlw fl x12 x14 x15 x19 x30 INV HC HP HB32 RR KB KC.
    rewrite rcount_block_split in RR.
    pose proof (fun c0 ab => cnt_tailA s m1 msvw tlw c0 ab fl) as TAIL.
    destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
    unfold rcount_decode in RR. unfold rd_cntA.
    destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
    unfold rd_lstA in TAIL |- *.
    assert (RL : 0 <= Z.land bs (thr + -1) < thr).
    { rewrite Ethr. replace (2 ^ (nb - 1) + -1) with (2 ^ (nb - 1) - 1) by lia. rewrite land_ones_mod by lia. apply Z.mod_pos_bound. lia. }
    assert (P2 : 2 ^ (nb - 1 + 1) = 2 * 2 ^ (nb - 1)) by (apply pow2_S; lia). replace (nb - 1 + 1) with nb in P2 by lia.
    assert (RC : 0 <= Z.land bs (thr * 2 + -1) < 2 * thr).
    { rewrite Ethr. replace (2 ^ (nb - 1) * 2 + -1) with (2 ^ nb - 1) by lia.
      rewrite land_ones_mod by lia. rewrite <- P2. apply Z.mod_pos_bound. lia. }
    replace (thr - 1) with (thr + -1) in RR by lia. replace (2 * thr - 1) with (thr * 2 + -1) in RR by lia.
    rewrite (u32_id (thr * 2 + -1 - rem)) in RR by lia.
    zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.                   (* [comment removed for export] *)
    zstep. zstep.                                                                     (* [comment removed for export] *)
    zstep. rewrite ?(land_swrap32 bs (thr + -1)) by lia.                               (* [comment removed for export] *)
    zstep. rewrite ?(FseWalkKit.swrap32_small (thr * 2 + -1 - rem)) by lia.   (* [comment removed for export] *)
    zstep. rewrite ?Z.add_0_r. rewrite ?(FseWalkKit.swrap32_small (Z.land bs (thr + -1))) by lia.                    (* [comment removed for export] *)
    zstep.                                                                            (* [comment removed for export] *)
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with false in RR by (symmetry; apply Z.ltb_ge; lia).
      cbn [fst snd] in RR.
      zstep. rewrite ?(land_swrap32 bs (thr * 2 + -1)) by lia.                       (* [comment removed for export] *)
      zstep. rewrite ?Z.add_0_r. rewrite ?(FseWalkKit.swrap32_small (Z.land bs (thr * 2 + -1))) by lia.             (* [comment removed for export] *)
      set (c := Z.land bs (thr * 2 + -1)) in *. set (mx := thr * 2 + -1 - rem) in *.
      zstep. rewrite (slt_small c thr) by lia.                                        (* [comment removed for export] *)
      zstep. zstep. rewrite (mask_sel (c <? thr) mx) by (subst mx; lia).              (* [comment removed for export] *)
      set (count0 := if thr <=? c then c - mx else c) in *.
      assert (EC0 : c - (if c <? thr then 0 else mx) = count0).
      { subst count0. destruct (Z.ltb_spec c thr); destruct (Z.leb_spec thr c); lia. }
      assert (RC0 : 0 <= count0 <= rem) by (subst count0 mx; destruct (Z.leb_spec thr c); lia).
      zstep. rewrite EC0. rewrite ?(FseWalkKit.swrap32_small count0) by lia.                     (* [comment removed for export] *)
      zstep.                                                                          (* [comment removed for export] *)
      zstep. rewrite ?Z.add_0_r. rewrite ?(FseWalkKit.swrap32_small count0) by lia.                                   (* [comment removed for export] *)
      zstep. rewrite ?(FseWalkKit.swrap32_small (count0 + -1)) by lia.                            (* [comment removed for export] *)
      zstep.                                                                          (* [comment removed for export] *)
      if_cases K2; zify_lts K2.
      + (* [comment removed for export] *)
        zstep. zstep. zstep.                                                          (* [comment removed for export] *)
        eapply (TAIL count0 nb); try eassumption; try lia.
        f_equal. destruct (Z.ltb_spec 0 count0); lia.
      + zstep.                                                                        (* [comment removed for export] *)
        eapply (TAIL count0 nb); try eassumption; try lia.
        f_equal. destruct (Z.ltb_spec 0 count0); lia.
    - (* [comment removed for export] *)
      replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with true in RR by (symmetry; apply Z.ltb_lt; lia).
      cbn [fst snd] in RR.
      set (count0 := Z.land bs (thr + -1)) in *.
      zstep.                                                                          (* [comment removed for export] *)
      zstep. rewrite ?Z.add_0_r. rewrite ?(FseWalkKit.swrap32_small count0) by lia.                                   (* [comment removed for export] *)
      zstep. rewrite ?(FseWalkKit.swrap32_small (count0 + -1)) by lia.                            (* [comment removed for export] *)
      zstep.                                                                          (* [comment removed for export] *)
      if_cases K2; zify_lts K2.
      + zstep.                                                                        (* [comment removed for export] *)
        eapply (TAIL count0 (nb + -1)); try eassumption; try lia.
        f_equal. destruct (Z.ltb_spec 0 count0); lia.
      + zstep. zstep. zstep.                                                          (* [comment removed for export] *)
        eapply (TAIL count0 (nb + -1)); try eassumption; try lia.
        f_equal. destruct (Z.ltb_spec 0 count0); lia.
  Qed.
End Count.
End CANSEC1.
