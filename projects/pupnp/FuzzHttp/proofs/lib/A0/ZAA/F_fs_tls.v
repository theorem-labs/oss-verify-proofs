(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim APrimLem ATacA ACells LJ LJU PEnv ATacFix F_gct F_alloc_B AFsEnv.
Import ListNotations.
Open Scope Z_scope.

Section M2S.
  Context {HC : HasCeiling}.
  Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (A : Z) (m : mem).

  Definition m2s_post : machine_state -> Prop :=
    fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (sh A)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m (seg_rom asegs).

  #[using="Type"] Lemma m2s_spec : forall (t0 a1 a2 a3 a4 a5 a6 a7 : word),
    env_shadow asegs m -> env_layout asegs m ->
    (0 <= A <= 0x7fff7fff \/ 0x10007fff8000 <= A < 2^47) ->
    evt asegs m2s_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3f400) fc None m (seg_rom asegs)).
  Proof.
    intros t0 a1 a2 a3 a4 a5 a6 a7 (ES1 & ES2) (EL1 & EL2) AR.
    assert (SHA : 2147450880 + Z.shiftr A 3 = sh A) by (rewrite Z.shiftr_div_pow2 by lia; unfold sh, SHADOW_OFF; change (2^3) with 8; clear; lia).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
    assert (ARG : 0 <= A < 2^64) by (clear - AR; lia).
    zstep. if_cases KL; zify_cond KL.
    -
      zstep. zstep. rewrite SHA. zstep.
      apply evt_done. unfold m2s_post. eexists _, _, _, _, _, _, _, _. reflexivity.
    - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases KX; zify_cond KX. 2: { exfalso. clear - KX ARG. change ((-1) mod 18446744073709551616) with 18446744073709551615 in KX. lia. } clear KX.
      zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KH; zify_cond KH. { exfalso. clear - KH KL AR. lia. } clear KH.
      zstep. if_cases KG; zify_cond KG. { exfalso. clear - KG KL AR. lia. } clear KG.
      zstep. zstep. rewrite SHA. zstep.
      apply evt_done. unfold m2s_post. eexists _, _, _, _, _, _, _, _. reflexivity.
  Qed.
End M2S.

Section TLSA.
  Context {HC : HasCeiling}.
  Variables (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z) (m : mem).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis QH : q < 2^64.

  Definition tryinit_post : machine_state -> Prop :=
    fun ms' => exists a1 m', ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 16, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

  #[using="HC CLO QH"] Lemma tryinit_spec : forall a0 a1,
    stk asegs m lo q -> lo <= q - 16 -> mem_inv asegs m -> env_inited asegs m ->
    evt asegs tryinit_post
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x5f634) fc None m (seg_rom asegs)).
  Proof.
    intros a0 a1 ST LO MI EI. unfold env_inited in EI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 16, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- EQ in ST. carve_frame 16%nat ST. rewrite !EQ in *.
    zstep. do 2 sstep.
    do 2 zstep. zstep. do 2 zstep.
    zstep. lit_branch.
    do 2 zstep. zstep.
    replace (q + -16 + 16) with q by lia.
    zstep.
    release_frame FR ST q.
    apply evt_done. unfold tryinit_post. eexists _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; assumption.
  Qed.

  Variables (DTV TLSB : Z).
  Definition tlsget_post : machine_state -> Prop :=
    fun ms' => exists a1' a2', ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (TLSB - 2048)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F_ (ret_pc ra) fc None m (seg_rom asegs).

  #[using="Type"] Lemma tlsget_spec : forall a1 a2',
    rw_cells asegs m 0xaadc0 [C8 (wz 1); C8 (wz 18446744073709549568); C8 (wz 8)] ->
    rw_cells asegs m (A0_TP - 8) [C8 (wz DTV)] -> rw_cells asegs m (DTV + 8) [C8 (wz TLSB)] -> 2048 <= TLSB < 2^63 ->
    evt asegs tlsget_post
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0xaadc0) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0xa3130) fc None m (seg_rom asegs)).
  Proof.
    intros a1 a2' DESC DTVC DTV1 TR.
    change (A0_TP - 8) with 6187368 in DTVC.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep.
    rewrite (Z_to_bv_eqm (18446744073709549568 + TLSB) (TLSB - 2048))
      by (replace (18446744073709549568 + TLSB) with (TLSB - 2048 + 1 * 2^64) by (clear; lia); apply Z_mod_plus_full).
    zstep.
    apply evt_done. unfold tlsget_post. eexists _, _. reflexivity.
  Qed.

  Variable L : athread.
  #[using="CLO QH"] Lemma gct_spec_q : forall a0 a1,
    stk asegs m lo q -> lo <= q - 16 -> thread_env L m -> thread_layout_ok L -> mem_inv asegs m ->
    evt asegs (gct_post L ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc q m lo)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz gct_entry) fc None m (seg_rom asegs)).
  Proof.
    intros a0 a1 ST LO TE TL MI. unfold gct_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. unfold thread_layout_ok in TL.
    pose proof (munch_refl [(q - 16, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    te_split TE.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- EQ in ST. carve_frame 16%nat ST. rewrite !EQ in *.
    zstep. sstep.
    zstep. zstep. zstep. zstep.
    zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. clear. intros KT. lia. }
    zstep. zstep.
    zstep. zstep.
    change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    zstep. zstep. zstep.
    zstep. zstep.
    zstep. if_cases KC; zify_cond KC. { exfalso; lia. }
    zstep. zstep. zstep.
    replace (q + -16 + 16) with q by lia.
    zstep.
    release_frame FR ST q.
    apply evt_done. unfold gct_post. eexists _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    unfold thread_env. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End TLSA.

Section DTLS.
  Context {HC : HasCeiling}.
  Variables (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo BLK : Z) (m : mem).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis QH : q < 2^64.

  Definition dtls_post : machine_state -> Prop :=
    fun ms' => exists a1 a2 a3 a4 a5 a6 a7 m', ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 144, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

  #[using="HC CLO QH"] Lemma dtls_spec : forall (a1 a2 a3 a4 a5 a6 a7 : word) (e : Z),
    stk asegs m lo q -> lo <= q - 144 -> mem_inv asegs m -> env_cf asegs m ->
    rw_cells asegs m 0xaadc0 [C8 (wz 1); C8 (wz 18446744073709549568); C8 (wz 8)] ->
    rw_cells asegs m 0x1454b1 [C1 (Z_to_bv 8 1)] ->
    rw_cells asegs m 0xaa120 [C8 (wz 0x143398)] -> rw_cells asegs m 0x143398 [C4 (wz 0)] ->
    rw_cells asegs m (A0_TP + 8) [C8 (wz BLK)] -> rw_cells asegs m (BLK + 24) [C8 (wz e)] -> 0 < e < 2^64 -> 0 < BLK -> BLK + 32 <= lo ->
    evt asegs dtls_post
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0xaadc0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x6f584) fc None m (seg_rom asegs)).
  Proof.
    intros a1 a2 a3 a4 a5 a6 a7 e ST LO MI ECF DESC ITG GVB VB BLKC ENT ER BR0 BRL. assert (BR : 0 < BLK < 2^64 - 1) by (clear - BR0 BRL ST QH LO; lia). unfold env_cf in ECF.
    change (A0_TP + 8) with 6187384 in BLKC.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 144, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    hideB ENT.
    rewrite <- EQ in ST. carve_frame 144%nat ST. rewrite !EQ in *.
    zstep. do 13 sstep.
    zstep. zstep. zstep. zstep.
    cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1.
    zstep. if_false.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    zstep. if_false.
    zstep. zstep. zstep.
    zstep. if_cases KM; zify_cond KM. { exfalso. clear - KM BR. change ((-1) mod 18446744073709551616) with 18446744073709551615 in KM. lia. } clear KM.
    zstep. if_cases KN; zify_cond KN. 2: { exfalso. clear - KN BR. lia. } clear KN.
    zstep. if_cases KO; zify_cond KO. { exfalso. clear - KO BR. lia. } clear KO.
    sstep. sstep.
    zstep. zstep. if_true.
    zstep. zstep. zstep.
    unhideB ENT. eapply (rw_cells_transport asegs _ m m0) in ENT; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - BRL LO; lia].
    zstep.
    zstep. if_cases KE; zify_cond KE. { exfalso. clear - KE ER. lia. } clear KE.
    zstep. do 13 zstep. zstep.
    replace (q + -144 + 144) with q by lia.
    zstep.
    release_frame FR ST q.
    apply evt_done. unfold dtls_post. eexists _, _, _, _, _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; assumption.
  Qed.
End DTLS.

Section TGA.
  Context {HC : HasCeiling}.
  Variable L : athread.
  Variables (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo DTV TLSB BLK FSB0 : Z) (m : mem).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis QH : q < 2^64.
  Hypothesis LOQ : lo <= q - 176.

  Definition tga_post : machine_state -> Prop :=
    fun ms' => exists a1 a2 a3 a4 a5 a6 a7 m', ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (TLSB - 2048)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 176, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

  #[using="CLO QH LOQ"] Lemma tga_spec : forall (a1 a2 a3 a4 a5 a6 a7 : word),
    stk asegs m lo q -> mem_inv asegs m -> env_inited asegs m -> env_cf asegs m ->
    thread_env L m -> thread_layout_ok L -> fs_tls_env (at_thr L) DTV TLSB BLK FSB0 m ->
    evt asegs tga_post
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0xaadc0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x4aeac) fc None m (seg_rom asegs)).
  Proof.
    intros a1 a2 a3 a4 a5 a6 a7 ST MI EI ECF TE TL (RTG & DESC & DTVC & DTV1 & FSTLS & ITG & GVB & VB & BLKC & (e & ENT & ER) & (tb & te & THRC) & D0 & DHI & TLR & B0 & BHI).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof TL as (_ & _ & T3 & T4 & _).
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; pose proof ST as (S0 & _); lia).
    assert (DJS : forall A k, A + k <= alloc_ceiling -> disjoint_from [(q - 176, q)] A k) by (intros A k HA; cbn [disjoint_from]; clear - HA CLO LOQ; lia).
    unfold env_inited in EI. unfold env_cf in ECF.
    change (A0_TP - 8) with 6187368 in DTVC. change (A0_TP + 8) with 6187384 in BLKC.
    hideB EI. hideB ECF. hideB TE. hideB RTG. hideB DESC. hideB DTVC. hideB DTV1. hideB ITG. hideB GVB. hideB VB. hideB BLKC. hideB ENT. hideB THRC. clear FSTLS.
    pose proof (munch_refl [(q - 176, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (TRC : forall (mx : mem) A cs, munch [(q - 176, q)] m mx -> wmono asegs m mx -> rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= alloc_ceiling -> rw_cells asegs mx A cs).
    { intros mx A cs MUx WMx HC0 HA. eapply (rw_cells_transport asegs _ m mx); [exact HC0| exact MUx| exact WMx| apply DJS; exact HA]. }
    rewrite <- EQ in ST. carve_frame 32%nat ST. rewrite !EQ in *.
    zstep. do 4 sstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unhideB EI. pose proof (TRC m1 _ _ MU WM EI ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as EI1. hideB EI.
    call (tryinit_spec _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q + -32) lo m1 CLO ltac:(clear - QH; lia) _ _);
      [ exact ST | clear - LOQ; lia | assumption | exact EI1 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    rename POST into ST2. clear EI1.
    unhideB RTG. pose proof (TRC m2 _ _ MU WM RTG ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as RTG2. hideB RTG.
    zstep. zstep. clear RTG2. zstep. zstep. zstep.
    unhideB DESC. pose proof (TRC m2 _ _ MU WM DESC ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as DESC2. hideB DESC.
    unhideB DTVC. pose proof (TRC m2 _ _ MU WM DTVC ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as DTVC2. hideB DTVC.
    unhideB DTV1. pose proof (TRC m2 _ _ MU WM DTV1 ltac:(cbn [cells_size csize Nat.add]; clear - DHI; lia)) as DTV12. hideB DTV1.
    eapply evt_cut.
    { eapply (tlsget_spec) with (DTV := DTV) (TLSB := TLSB); [exact DESC2| exact DTVC2| exact DTV12| clear - TLR ACR; lia]. }
    cbv beta. intros msT PT. unfold tlsget_post in PT. destruct PT as (v1 & v2 & ->).
    clear DESC2 DTVC2 DTV12.
    replace (ret_pc (Z_to_bv 64 306908)) with (Z_to_bv 64 306908) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. zstep. if_false.
    zstep.
    assert (TE2 : thread_env L m2).
    { unhideB TE. pose proof TL as (_ & TC2 & _ & TT2 & _). unfold thread_env in *.
      destruct TE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
      repeat match goal with |- _ /\ _ => split end;
        (eapply (TRC m2); [exact MU| exact WM| eassumption| cbn [cells_size csize Nat.add]; clear - ACR TC2 TT2; lia]). }
    call (gct_spec_q _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q + -32) lo m2 CLO ltac:(clear - QH; lia) L _ _);
      [ exact ST2 | clear - LOQ; lia | exact TE2 | exact TL | assumption | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    rename PC into ST3. clear TE2 POST.
    unhideB THRC. pose proof (TRC m3 _ _ MU WM THRC ltac:(cbn [cells_size csize Nat.add]; clear - T4; lia)) as THRC3. hideB THRC.
    zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT T3 T4 ACR. lia. } clear KT.
    zstep. zstep. zstep. zstep. zstep. zstep.
    clear THRC3.
    unhideB ECF. pose proof (TRC m3 _ _ MU WM ECF ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as ECF3. hideB ECF.
    unhideB DESC. pose proof (TRC m3 _ _ MU WM DESC ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as DESC3. hideB DESC.
    unhideB ITG. pose proof (TRC m3 _ _ MU WM ITG ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as ITG3. hideB ITG.
    unhideB GVB. pose proof (TRC m3 _ _ MU WM GVB ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as GVB3. hideB GVB.
    unhideB VB. pose proof (TRC m3 _ _ MU WM VB ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as VB3. hideB VB.
    unhideB BLKC. pose proof (TRC m3 _ _ MU WM BLKC ltac:(cbn [cells_size csize Nat.add]; clear - ACR; lia)) as BLKC3. hideB BLKC.
    unhideB ENT. pose proof (TRC m3 _ _ MU WM ENT ltac:(cbn [cells_size csize Nat.add]; clear - BHI; lia)) as ENT3. hideB ENT.
    eapply evt_cut.
    { eapply (dtls_spec) with (BLK := BLK) (lo := lo) (e := e);
        [ exact CLO | clear - QH; lia | exact ST3 | clear - LOQ; lia | exact MI | exact ECF3 | exact DESC3 | exact ITG3 | exact GVB3 | exact VB3 | exact BLKC3 | exact ENT3 | exact ER | exact B0 | clear - BHI CLO; lia ]. }
    cbv beta. intros msD PD. unfold dtls_post in PD. destruct PD as (d1 & d2 & d3 & d4 & d5 & d6 & d7 & m4 & -> & MU4 & WM4 & MI4 & ST4).
    clear ECF3 DESC3 ITG3 GVB3 VB3 BLKC3 ENT3.
    eapply (rw_cells_transport asegs _ m3 m4) in FR; [| exact MU4| exact WM4| cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
    apply (munch_trans _ m m3 m4) in MU; [| eapply (munch_weaken [(q + -32 - 144, q + -32)] _ m3 m4); [unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; lia| exact MU4]].
    apply (wmono_trans asegs m m3 m4) in WM; [| exact WM4].
    replace (ret_pc (Z_to_bv 64 306956)) with (Z_to_bv 64 306956) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (q + -32 + 32) with q by (clear; lia).
    zstep.
    release_frame FR ST4 q.
    apply evt_done. unfold tga_post. eexists _, _, _, _, _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; assumption.
  Qed.
End TGA.
