(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseRdKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RF_fse_iface RF_fse_rd_base RF_fse_rd_cnt1.
Import ListNotations.
Open Scope Z_scope.

Section Count.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.
  Variable tl : Z.
  Hypothesis Htl : 5 <= tl <= 15.
  Variable POST : machine_state -> Prop.

  Notation buf := (c_buf C).
  Notation msv1 := (c_msv0 C + 1).
  Notation BUF := (c_BUF C).
  Notation NC := (c_NC C).

  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
  Ltac zify_lts H :=
    unfold bv_lts in H; rewrite !signed_lit in H by lia;
    first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H
          | apply negb_true_iff in H; apply Z.ltb_ge in H | apply negb_false_iff in H; apply Z.ltb_lt in H ].
  Let cnt_hb := cnt_hb C POST.
  Let cnt_fin := cnt_fin C OK POST.

  (* [comment removed for export] *)
  Lemma cnt_tail : forall s m1 msvw tlw count0 addb fl (x1 x26 x27 : word),
    rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
    x26 = Z_to_bv 64 (if 0 <? count0 then 1 - count0 else -1) ->
    rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
    (forall s' m2 y1 y20 y23 y24 y26 y27 y30, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
        evt psegs POST (rd_exit C s' m2 y1 y20 y23 y24 y26 y27 y30)) ->
    (forall s' m2 y1 y25 y26 y27, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
        evt psegs POST (rd_head C s' m2 y1 y25 y26 y27)) ->
    evt psegs POST (rd_lst C 0x24b60 m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (r_threshold s))
                      (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 addb) (Z_to_bv 64 (count0 + -1)) (Z_to_bv 64 (r_charnum s))
                      x26 x27 (Z_to_bv 64 (r_nbBits s))).
  Proof.
    intros s m1 msvw tlw count0 addb fl x1 x26 x27 INV HC HP HB32 Hc0 Haddb -> RR KB KC.
    destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
    pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB).
    unfold RD_STACK in *.
    destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
    set (DR := if 0 <? count0 then 1 - count0 else -1) in *.
    assert (RDR : - 2^31 <= DR <= 0 /\ 1 <= rem + DR) by (subst DR; destruct (Z.ltb_spec 0 count0); lia).
    unfold rd_lst.
    zstep. rewrite (swrap32_small (addb + bc)) by lia. replace (addb + bc) with (bc + addb) by lia.
    zstep. rewrite (addw_neg DR rem) by lia.
    zstep. rewrite (swrap32_small (cn + 1)) by lia.
    zstep. zstep. rewrite (shl32_shr31 cn) by lia.
    zstep.
    (* [comment removed for export] *)
    destruct INV as (ARR & LNC & HBUF & HMSV & HTL & (junk8 & FR) & ST & MU & WM & MI). unfold rd_W, RD_STACK in MU.
    assert (LWS : length (map (Z_to_bv 64) nc) = length (c_rt0 C)) by (rewrite length_map; exact LNC).
    assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
    pose proof (u16arr_store_ok psegs _ NC _ cn (wa (NC + 2 * cn)) ARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
    zstep.
    pose proof (u16arr_write psegs _ NC _ cn (Z_to_bv 64 (count0 + -1)) ARR ltac:(rewrite LWS; lia)) as ARR2.
    clear ARR. store_done.
    rewrite u16s_upd_short in ARR2.
    (* [comment removed for export] *)
    unfold rcount_rest in RR. cbnR.
    replace (count0 - 1) with (count0 + -1) in RR by lia.
    rewrite (zstore_ok nc cn) in RR by (unfold FseNCount.Zlength; lia). cbn [bind] in RR.
    replace (if 0 <=? count0 + -1 then rem - (count0 + -1) else rem + (count0 + -1)) with (rem + DR) in RR
      by (subst DR; destruct (Z.ltb_spec 0 count0); destruct (Z.leb_spec 0 (count0 + -1)); lia).
    set (nc' := Zupd cn (to_short (count0 + -1)) nc) in *.
    assert (INV2 : rd_inv C m (nc') msvw tlw).
    { unfold rd_inv, rd_W, RD_STACK. split; [exact ARR2|]. split; [subst nc'; rewrite Zupd_length; exact LNC|].
      split; [exact HBUF|]. split; [exact HMSV|]. split; [exact HTL|]. split; [exists junk8; exact FR|].
      split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
    clear ARR2 HBUF HMSV HTL FR ST MU WM MI.
    zstep.
    if_cases B1; zify_cond B1; rewrite !signed_lit in B1 by lia.
    - (* [comment removed for export] *)
      replace (rem + DR <? thr) with false in RR by (symmetry; apply Z.ltb_ge; lia). cbn [bind] in RR.
      eapply (cnt_fin (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m msvw tlw (count0 + -1) fl);
        cbnR; try eassumption; try lia; try reflexivity.
    - replace (rem + DR <? thr) with true in RR by (symmetry; apply Z.ltb_lt; lia).
      zstep.
      if_cases B2; zify_cond B2; rewrite ?signed_lit in B2 by lia.
      + (* [comment removed for export] *)
        replace (rem + DR <=? 1) with true in RR by (symmetry; apply Z.leb_le; lia). cbn [bind] in RR. injection RR as <-.
        pose proof (KB (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m) as KB'.
        unfold rd_exit, rd_lst in KB'. cbnR.
        zstep.
        eapply KB'; [reflexivity| exact INV2|]. unfold rd_brk_ok. cbnR. change (2^31) with 2147483648. lia.
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
        pose proof (cnt_hb (rem + DR) m) as HBK. unfold rd_lst in HBK.
        eapply HBK; [lia|]. intros y20 y30 -> ->.
        eapply (cnt_fin (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) (2 ^ Z.log2 (rem + DR)) (Z.log2 (rem + DR) + 1) (count0 + -1 =? 0)) m msvw tlw (count0 + -1) fl);
          cbnR; try eassumption; try lia; try reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma count_run : forall s m1 msvw tlw fl (x1 x23 x26 x27 : word),
    rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    rcount_block buf msv1 s = Ok fl ->
    (forall s' m2 y1 y20 y23 y24 y26 y27 y30, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
        evt psegs POST (rd_exit C s' m2 y1 y20 y23 y24 y26 y27 y30)) ->
    (forall s' m2 y1 y25 y26 y27, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
        evt psegs POST (rd_head C s' m2 y1 y25 y26 y27)) ->
    evt psegs POST (rd_cnt C s m1 x1 x23 x26 x27).
  Proof.
    intros s m1 msvw tlw fl x1 x23 x26 x27 INV HC HP HB32 RR KB KC.
    rewrite rcount_block_split in RR.
    pose proof (fun c0 ab => cnt_tail s m1 msvw tlw c0 ab fl) as TAIL.
    destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
    unfold rcount_decode in RR. unfold rd_cnt.
    destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
    unfold rd_lst in TAIL |- *.
    assert (RL : 0 <= Z.land bs (thr + -1) < thr).
    { rewrite Ethr. replace (2 ^ (nb - 1) + -1) with (2 ^ (nb - 1) - 1) by lia. rewrite land_ones_mod by lia. apply Z.mod_pos_bound. lia. }
    assert (P2 : 2 ^ (nb - 1 + 1) = 2 * 2 ^ (nb - 1)) by (apply pow2_S; lia). replace (nb - 1 + 1) with nb in P2 by lia.
    assert (RC : 0 <= Z.land bs (thr * 2 + -1) < 2 * thr).
    { rewrite Ethr. replace (2 ^ (nb - 1) * 2 + -1) with (2 ^ nb - 1) by lia.
      rewrite land_ones_mod by lia. rewrite <- P2. apply Z.mod_pos_bound. lia. }
    replace (thr - 1) with (thr + -1) in RR by lia. replace (2 * thr - 1) with (thr * 2 + -1) in RR by lia.
    rewrite (u32_id (thr * 2 + -1 - rem)) in RR by lia.
    zstep. zstep. zstep. zstep.
    rewrite (land_swrap32 bs (thr + -1)) by lia.
    zstep.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
    rewrite (Z.mod_small (thr * 2 + -1)) by lia. rewrite (swrap32_small (thr * 2 + -1 - rem)) by lia.
    zstep.
    rewrite Z.add_0_r. rewrite (swrap32_small (Z.land bs (thr + -1))) by lia.
    zstep.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with false in RR by (symmetry; apply Z.ltb_ge; lia).
      cbn [fst snd] in RR.
      zstep. rewrite (land_swrap32 bs (thr * 2 + -1)) by lia.
      zstep. rewrite Z.add_0_r. rewrite (swrap32_small (Z.land bs (thr * 2 + -1))) by lia.
      set (c := Z.land bs (thr * 2 + -1)) in *. set (mx := thr * 2 + -1 - rem) in *.
      zstep. rewrite (slt_small c thr) by lia.
      zstep. zstep. rewrite (mask_sel (c <? thr) mx) by (subst mx; lia).
      set (count0 := if thr <=? c then c - mx else c) in *.
      assert (EC0 : c - (if c <? thr then 0 else mx) = count0).
      { subst count0. destruct (Z.ltb_spec c thr); destruct (Z.leb_spec thr c); lia. }
      assert (RC0 : 0 <= count0 <= rem) by (subst count0 mx; destruct (Z.leb_spec thr c); lia).
      zstep. rewrite EC0. rewrite (swrap32_small count0) by lia.
      zstep. zstep. rewrite Z.add_0_r. rewrite (swrap32_small count0) by lia.
      zstep. rewrite (swrap32_small (count0 + -1)) by lia.
      zstep.
      if_cases K2; zify_lts K2.
      + (* [comment removed for export] *)
        zstep. zstep.
        eapply (TAIL count0 nb); try eassumption; try lia.
        f_equal. destruct (Z.ltb_spec 0 count0); lia.
      + zstep.
        eapply (TAIL count0 nb); try eassumption; try lia.
        f_equal. destruct (Z.ltb_spec 0 count0); lia.
    - (* [comment removed for export] *)
      replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with true in RR by (symmetry; apply Z.ltb_lt; lia).
      cbn [fst snd] in RR.
      set (count0 := Z.land bs (thr + -1)) in *.
      zstep. zstep. rewrite Z.add_0_r. rewrite (swrap32_small count0) by lia.
      zstep. rewrite (swrap32_small (count0 + -1)) by lia.
      zstep.
      if_cases K2; zify_lts K2.
      + zstep.
        eapply (TAIL count0 (nb + -1)); try eassumption; try lia.
        f_equal. destruct (Z.ltb_spec 0 count0); lia.
      + zstep. zstep.
        eapply (TAIL count0 (nb + -1)); try eassumption; try lia.
        f_equal. destruct (Z.ltb_spec 0 count0); lia.
  Qed.

End Count.
