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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= rdA_acc_hint.

Section CANSEC1. Context {rc : runConstT}.
Section Count1.
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

  (* [comment removed for export] *)
  Lemma cnt_loadA : forall s2 m1 msvw tlw count ip' (x6 x10 x11 x12 x14 x15 x30 : word),
    rd_invA C m1 (r_nc s2) msvw tlw ->
    0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s2 < 32 ->
    r_ip s2 = ip' -> r_bitStream s2 = le32 buf ip' / 2 ^ r_bitCount s2 -> r_previous0 s2 = (count =? 0) ->
    -1 <= count < 2^31 ->
    x10 = Z_to_bv 64 (BUF + ip') -> x6 = Z_to_bv 64 (r_bitCount s2) ->
    (forall y12 y14 y15 y19 y30, evtF bsegs RNG POST (rd_headA C s2 m1 y12 y14 y15 y19 y30)) ->
    evtF bsegs RNG POST (rd_lstA C 0xab018 m1 x6 x10 x11 x12 (Z_to_bv 64 (r_charnum s2)) x14 x15 (Z_to_bv 64 (r_remaining s2))
                           (Z_to_bv 64 (r_threshold s2)) (Z_to_bv 64 count) (Z_to_bv 64 (r_nbBits s2)) x30).
  Proof.
    intros s2 m1 msvw tlw count ip' x6 x10 x11 x12 x14 x15 x30 INV Hip0 Hip4 Hbc Eip Ebs Ep0 Hcount -> -> K.
    destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
    destruct INV as (_ & _ & HBUF & _).
    destruct (buf_rdA C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
    destruct (buf_rdA C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
    destruct (buf_rdA C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
    destruct (buf_rdA C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
    rewrite !Z.add_assoc in RD1, RD2, RD3.
    destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip p0.
    unfold rd_lstA.
    zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
    fold (le32 buf ip'). rewrite <- Ebs.
    pose proof K as K'. unfold rd_headA, rd_lstA in K'. cbnR.
    zstep. zstep.
    if_cases B; zify_cond B.
    - (* [comment removed for export] *)
      assert (count = 0).
      { destruct (Z.ltb_spec 0 (count mod 18446744073709551616)) as [L|L]; cbn [Z.b2z] in B; [discriminate B|].
        destruct (Z.eq_dec count (-1)) as [->|N]; [cbn in L; lia|]. rewrite Z.mod_small in L by lia. lia. }
      subst count. change (0 =? 0) with true in K'. apply K'.
    - assert (count <> 0).
      { intros ->. apply B. reflexivity. }
      replace (count =? 0) with false in K' by (symmetry; apply Z.eqb_neq; assumption).
      zstep. apply K'.
  Qed.
  (* [comment removed for export] *)
  Lemma rl_chk2 : forall m1 ip' (x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
    unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
    (forall y11 y12 y14, evtF bsegs RNG POST (rd_lstA C 0xab018 m1 x6 (Z_to_bv 64 (BUF + ip')) y11 y12 x13 y14 x15 x16 x17 x19 x23 x30)) ->
    evtF bsegs RNG POST (rd_lstA C 0xab004 m1 x6 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x14 x15 x16 x17 x19 x23 x30).
  Proof.
    intros m1 ip' x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB P0 P4 K.
    destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
    pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
    pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
    destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip' + 3) UB ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2).
    unfold rd_lstA in K |- *.
    zstep. zstep. zstep. zstep. rewrite sxb_sval.
    zstep. if_cases G; zify_cond G.
    - zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
    - apply K.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_chk1 : forall m1 ip' (x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
    unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
    (forall y11 y12, evtF bsegs RNG POST (rd_lstA C 0xab004 m1 x6 (Z_to_bv 64 (BUF + ip')) y11 y12 x13 x14 x15 x16 x17 x19 x23 x30)) ->
    evtF bsegs RNG POST (rd_lstA C 0xaaff4 m1 x6 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x14 x15 x16 x17 x19 x23 x30).
  Proof.
    intros m1 ip' x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB P0 P4 K.
    destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
    pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
    pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
    destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip') UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
    unfold rd_lstA in K |- *.
    zstep. zstep. zstep. rewrite sxb_sval.
    zstep. if_cases G; zify_cond G.
    - zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
    - apply K.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_chk1c : forall m1 (x6 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
    unpoisoned m1 BUF (BUF + zlen buf) ->
    (forall y11 y12, evtF bsegs RNG POST (rd_lstA C 0xab004 m1 x6 (Z_to_bv 64 (BUF + zlen buf + -4)) y11 y12 x13 x14 x15 x16 x17 x19 x23 x30)) ->
    evtF bsegs RNG POST (rd_lstA C 0xab078 m1 x6 (Z_to_bv 64 (BUF + zlen buf + -4)) (Z_to_bv 64 (BUF + zlen buf + -4)) x12 x13 x14 x15 x16 x17 x19 x23 x30).
  Proof.
    intros m1 x6 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB K.
    destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
    pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
    pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
    destruct (chkB m1 BUF (BUF + zlen buf) (BUF + zlen buf + -4) UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
    unfold rd_lstA in K |- *.
    zstep. zstep. zstep. rewrite sxb_sval.
    zstep. if_cases G; zify_cond G.
    - apply K.
    - zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
  Qed.

  (* [comment removed for export] *)
  Lemma cnt_reloadA : forall s1 s2 m1 msvw tlw count (x6 x11 x14 x15 x30 : word),
    rd_invA C m1 (r_nc s1) msvw tlw -> reload buf s1 = Ok s2 ->
    0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 ->
    r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
    (forall y12 y14 y15 y19 y30, evtF bsegs RNG POST (rd_headA C s2 m1 y12 y14 y15 y19 y30)) ->
    evtF bsegs RNG POST (rd_lstA C 0xaafe4 m1 x6 (Z_to_bv 64 (BUF + r_ip s1)) x11 (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_charnum s1))
                           x14 x15 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1)) (Z_to_bv 64 count) (Z_to_bv 64 (r_nbBits s1)) x30).
  Proof.
    intros s1 s2 m1 msvw tlw count x6 x11 x14 x15 x30 INV RL Hip0 Hip4 Hbc Ep0 Hcount K.
    pose proof (reload_inv buf s1 s2 (buf_all_bytesA C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
    destruct RI as (I1 & I2 & I3 & ->).
    pose proof RNGS as RNGS'. destruct RNGS' as (RIM & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
    pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & SP16 & SPK & LOS & LOA & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
    pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3].
    pose proof (ablk_lin _ _ BB) as LBB. pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
    pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j16 & FRM) & _ & MU & _). unfold FRA_main in FRM.
    destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & _ & UB).
    destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst p0.
    unfold reload_pos in *. unfold FseNCount.Zlength in *.
    rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
    assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    (* [comment removed for export] *)
    assert (LOAD : forall ip' bc' (y11 y12 y14 y15 y30 : word),
       fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
       snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
       evtF bsegs RNG POST (rd_lstA C 0xab004 m1 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip')) y11 y12 (Z_to_bv 64 cn) y14 y15
                              (Z_to_bv 64 rem) (Z_to_bv 64 thr) (Z_to_bv 64 count) (Z_to_bv 64 nb) y30)).
    { intros ip' bc' y11 y12 y14 y15 y30 E1 E2. rewrite E1, E2 in *.
      eapply (rl_chk2 m1 ip'); [exact UB| lia| lia|]. intros z11 z12 z14.
      eapply (cnt_loadA (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb (count =? 0)) m1 msvw tlw count ip');
        try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
    clear K. unfold rd_lstA in LOAD |- *.
    zstep. rewrite signed_lit by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.   (* [comment removed for export] *)
    zstep.                                                                                       (* [comment removed for export] *)
    if_cases B1; zify_cond B1.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.                                                                       (* [comment removed for export] *)
      if_cases B2; zify_cond B2.
      + (* [comment removed for export] *)
        replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD, I2
          by (symmetry; apply orb_true_iff; right; apply Z.leb_le; lia). cbn [fst] in I2.
        zstep. zstep. rewrite land_7.                                                            (* [comment removed for export] *)
        pose proof (rl_chk1 m1 (ip + bc / 8)) as CK1. unfold rd_lstA in CK1.
        replace (BUF + ip + bc / 8) with (BUF + (ip + bc / 8)) by lia.
        eapply CK1; [exact UB| lia| lia|]. intros y11 y12.
        eapply (LOAD (ip + bc / 8) (bc mod 8)); reflexivity.
      + replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with false in LOAD
          by (symmetry; apply orb_false_iff; split; apply Z.leb_gt; lia).
        zstep. zstep.                                                                            (* [comment removed for export] *)
        replace (BUF + ip - (BUF + zlen buf + -4)) with (ip - zlen buf + 4) by lia.
        rewrite (FseWalkKit.swrap32_small (ip - zlen buf + 4)) by lia.
        zstep. zstep. zstep.                                                                     (* [comment removed for export] *)
        rewrite (clamp_bc bc (ip - zlen buf + 4)) by lia.
        replace (bc + 8 * (ip - zlen buf + 4)) with (bc - 8 * (zlen buf - 4 - ip)) by lia.
        zstep.                                                                                   (* [comment removed for export] *)
        pose proof (rl_chk1c m1) as CK1. unfold rd_lstA in CK1.
        eapply CK1; [exact UB|]. intros y11 y12.
        replace (BUF + zlen buf + -4) with (BUF + (zlen buf - 4)) by lia.
        eapply (LOAD (zlen buf - 4) ((bc - 8 * (zlen buf - 4 - ip)) mod 32)); reflexivity.
    - replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD, I2
        by (symmetry; apply orb_true_iff; left; apply Z.leb_le; lia). cbn [fst] in I2.
      zstep. zstep. rewrite land_7.                                                              (* [comment removed for export] *)
      pose proof (rl_chk1 m1 (ip + bc / 8)) as CK1. unfold rd_lstA in CK1.
      replace (BUF + ip + bc / 8) with (BUF + (ip + bc / 8)) by lia.
      eapply CK1; [exact UB| lia| lia|]. intros y11 y12.
      eapply (LOAD (ip + bc / 8) (bc mod 8)); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cnt_hbA : forall r m1 nc msvw tlw (x6 x10 x11 x12 x13 x14 x15 x17 x19 x23 x30 : word),
    rd_invA C m1 nc msvw tlw -> 2 <= r < 32768 ->
    (forall y11 y14 y15 y17 y23, y23 = Z_to_bv 64 (Z.log2 r + 1) -> y17 = Z_to_bv 64 (2 ^ Z.log2 r) ->
        evtF bsegs RNG POST (rd_lstA C 0xaafe0 m1 x6 x10 y11 x12 x13 y14 y15 (Z_to_bv 64 r) y17 x19 y23 x30)) ->
    evtF bsegs RNG POST (rd_lstA C 0xaaf6c m1 x6 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 r) x17 x19 x23 x30).
  Proof.
    intros r m1 nc msvw tlw x6 x10 x11 x12 x13 x14 x15 x17 x19 x23 x30 INV Hr K.
    pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j16 & FRM) & _). unfold FRA_main in FRM.
    pose proof RNGS as RNGS'. destruct RNGS' as (RIM & RSTK & _).
    pose proof OK as OK'. destruct OK' as (_ & _ & _ & _ & _ & SP16 & SPK & LOS & LOA & _).
    pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3]. pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, KEND in *.
    unfold rd_lstA in *.
    zstep. zstep. brute_regF 11 r 2 32766 sm1.
    zstep. zstep. brute_regF 11 r 2 32766 sm2.
    zstep. zstep. brute_regF 11 r 2 32766 sm3.
    zstep. zstep. brute_regF 11 r 2 32766 sm4.
    zstep. zstep. brute_regF 11 r 2 32766 sm5.
    do 14 zstep.                            (* [comment removed for export] *)
    brute_regF 11 r 2 32766 (fun r0 => 31 - Z.log2 r0).
    zstep. zstep. zstep.
    brute_regF 23 r 2 32766 (fun r0 => Z.log2 r0 + 1).
    zstep. zstep.
    brute_regF 17 r 2 32766 (fun r0 => 2 ^ Z.log2 r0).
    eapply K; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cnt_finA : forall s1 m1 msvw tlw count fl (x6 x11 x14 x15 x30 : word),
    rd_invA C m1 (r_nc s1) msvw tlw ->
    0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 -> 1 <= r_charnum s1 <= msv1 -> 1 <= r_remaining s1 < 2^31 ->
    r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
    (if msv1 <=? r_charnum s1 then Ok (Brk s1) else let! s2 := reload buf s1 in Ok (Cont s2)) = Ok fl ->
    (forall s' m2 y6 y11 y14 y15 y17 y19 y23 y30, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
        evtF bsegs RNG POST (rd_exitA C s' m2 y6 y11 y14 y15 y17 y19 y23 y30)) ->
    (forall s' m2 y12 y14 y15 y19 y30, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
        evtF bsegs RNG POST (rd_headA C s' m2 y12 y14 y15 y19 y30)) ->
    evtF bsegs RNG POST (rd_lstA C 0xaafe0 m1 x6 (Z_to_bv 64 (BUF + r_ip s1)) x11 (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_charnum s1))
                           x14 x15 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1)) (Z_to_bv 64 count) (Z_to_bv 64 (r_nbBits s1)) x30).
  Proof.
    intros s1 m1 msvw tlw count fl x6 x11 x14 x15 x30 INV Hip0 Hip4 Hbc Hcn Hrem Ep0 Hcount RR KB KC.
    pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
    destruct (Z.leb_spec msv1 (r_charnum s1)) as [GE|LT].
    - (* [comment removed for export] *)
      injection RR as <-.
      pose proof (KB s1 m1) as KB'. unfold rd_exitA, rd_lstA in KB'.
      destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
      unfold rd_lstA.
      zstep. if_cases B; zify_cond B; [| exfalso; lia].
      eapply KB'; [reflexivity| exact INV|]. unfold rd_brk_okA. cbnR. change (2^31) with 2147483648 in *. lia.
    - destruct (reload buf s1) as [s2| | |] eqn:RL; cbn [bind] in RR; try discriminate RR. injection RR as <-.
      pose proof (fun y12 y14 y15 y19 y30 => KC s2 m1 y12 y14 y15 y19 y30 eq_refl) as KC'.
      assert (INV2 : rd_invA C m1 (r_nc s2) msvw tlw).
      { pose proof (reload_inv buf s1 s2 (buf_all_bytesA C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
        destruct RI as (_ & _ & _ & ->). cbnR. exact INV. }
      specialize (fun y12 y14 y15 y19 y30 => KC' y12 y14 y15 y19 y30 INV2).
      pose proof (cnt_reloadA s1 s2 m1 msvw tlw count) as CR. unfold rd_lstA in CR.
      destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
      unfold rd_lstA.
      zstep. if_cases B; zify_cond B; [exfalso; lia|].
      eapply CR; try eassumption; cbnR; try lia.
  Qed.
End Count1.
End CANSEC1.
