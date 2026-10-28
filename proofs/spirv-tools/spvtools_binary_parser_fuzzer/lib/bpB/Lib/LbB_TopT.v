(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH2 LbB_TopT1.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopT.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition hpost (e : hent H) : config -> Prop :=
    fuzz_post H FZP_A (e_ra e) (e_sp e) (e_gp e) (e_tp e) (e_s0 e) (e_s1 e) (e_s2 e) (e_s3 e) (e_s4 e) (e_s5 e) (e_s6 e)
      (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (e_s11 e) (e_F e) (e_fc e) (e_s e) (e_LB e) (e_LF e) (e_N e) (e_lo e) (e_B e)
      (e_shi e) (e_m e) (e_mo e).

  Definition cut_T (e : hent H) (c : config) : Prop :=
    exists (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (F' : bvmap 5 word) (fc' : bv 32)
           (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m' : mem),
      as_VIS H sk (cfg_ms c) = MS (mkR x1 (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e)) x9 x10 x11 x12 x13 x14
                                       x15 x16 x17 (Z_to_bv 64 ff) x19 (Z_to_bv 64 ff) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                  F' (Z_to_bv 64 TOP_RET6) fc' None m' (seg_rom asegs)
      /\ as_AKREL H sk c /\ as_MPRES H (e_mo e) (cfg_model c)
      /\ FPSteps.frm_zero fc'
      /\ hinv H e ff fp XSc sk LBk m'
      /\ Permutation LBk (e_LB e)
      /\ as_AL H sk >= as_AL H (e_s e) - top_cost (e_N e).

  Lemma seg_T : forall (e : hent H) (c : config), hpre H e -> cut_T e c -> as_SR H (hpost e) c.
  Proof.
    intros e [msF mo] HP CT.
    destruct CT as (ff & fp & XSc & sk & LBk & F' & fc' & x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x19
                    & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & VIS & KR & MP & FZ & HI & PERM & AL).
    cbn [cfg_ms cfg_model] in VIS, MP.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (rt_bp_ext H HH) as (_ & _ & _ & _ & _ & _ & _ & SF6 & _ & _ & _).
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *.

    set (WT := [(ff, ff + 8); (S1 - AFS_STACK, S1); (fp, fp + 1); (sh ff, sh ff + fshn 6)]).
    assert (WOK : Forall (fun iv => (forall LB0, aclient_write_ok H LB0 iv) /\ aconst_ok iv /\ stack0_ok iv
                           /\ ((aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XH H ff fp ++ XSc) a))
                           /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= SP - 104 \/ SP <= fst iv)) WT).
    { unfold WT, AFS_STACK. change (fshn 6) with 512.
      assert (FSBb : as_FSB H + AFS_SIZE <= aceil) by lia.
      repeat apply Forall_cons; try apply Forall_nil.
      - destruct (hwin_ok H e ff fp XSc (ff, ff + 8) FFR CE ltac:(fold lo SP; lia) ltac:(unfold AAPP_HI; fold SP; lia) ltac:(right; left; cbn; lia))
          as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        repeat split; try assumption.
      - destruct (hwin_ok H e ff fp XSc (S1 - 1024, S1) FFR CE ltac:(fold lo SP; lia) ltac:(unfold AAPP_HI; fold SP; lia) ltac:(left; cbn; fold lo SP; lia))
          as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        repeat split; try assumption.
      - cbn [fst snd]. split; [intros LB0; right; right; right; right; left; cbn; unfold AFS_SIZE; lia|].
        split; [eapply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; unfold AFS_SIZE; lia]|].
        split; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | unfold AFS_SIZE; lia]|].
        split; [right; intros a Ha; apply rin_ivs_app; left; cbn; right; left; lia|].
        split; [right; unfold ATP; lia | left; lia].
      - destruct (hwin_ok H e ff fp XSc (sh ff, sh ff + 512) FFR CE ltac:(fold lo SP; lia) ltac:(unfold AAPP_HI; fold SP; lia) ltac:(right; right; cbn; lia))
          as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        repeat split; try assumption. }
    assert (DJ : forall A n, (forall iv, In iv WT -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from WT A n).
    { intros A n K. clear - K. induction WT as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }

    eapply (ahh_evt_then H HB (fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
              ms = MS (mkR (e_ra e) (Z_to_bv 64 SP) (e_gp e) (e_tp e) t0 t1 t2 (e_s0 e) (e_s1 e) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                           (e_s2 e) (e_s3 e) (e_s4 e) (e_s5 e) (e_s6 e) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (e_s11 e) t3 t4 t5 t6)
                      F' (ret_pc (e_ra e)) fc' None m2 (seg_rom asegs)
              /\ munch WT m' m2 /\ wmono asegs m' m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo SP /\ as_RFS H (e_LF e) m2 /\ ACONST m2));
      [exact KR | exact VIS | |].
    { eapply evt_cut.
      { eapply (hT1 x1 (e_gp e) (e_tp e) x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                    F' fc' m' SP S1 ff lo); [lia | lia | exact (hinv_wf H _ _ _ _ _ _ _ HI) | exact (hinv_stk H _ _ _ _ _ _ _ HI) | exact (hinv_mi H _ _ _ _ _ _ _ HI)]. }
      intros ms1 (m1 & EQ1 & MU1 & WM1 & MI1 & ST1). subst ms1.
      assert (W1 : Forall (afs_write_ok H ((6, ff, fp) :: e_LF e)) [(ff, ff + 8)]).
      { apply Forall_cons; [| apply Forall_nil]. right. exists (6, ff, fp). split; [left; reflexivity | cbn; change (fsz 6) with 4096; lia]. }
      assert (RF1 : as_RFS H ((6, ff, fp) :: e_LF e) m1) by (eapply (ah_RFS_frame H HB); [exact (hinv_rf H _ _ _ _ _ _ _ HI) | exact MU1 | exact WM1 | exact W1]).
      assert (AC1 : ACONST m1).
      { eapply ACONST_frame; [exact (hinv_ac H _ _ _ _ _ _ _ HI) | exact MU1 | exact WM1 |].
        apply Forall_cons; [| apply Forall_nil]. eapply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; lia]. }
      assert (SF1 : rw_cells asegs m1 (ff + 4088) [C8 (Z_to_bv 64 fp)])
        by (eapply rw_cells_transport; [exact (hinv_sf H _ _ _ _ _ _ _ HI) | exact MU1 | exact WM1 | cbn; lia]).
      assert (SV1 : rw_cells asegs m1 (SP - 104) (esaved e))
        by (eapply rw_cells_transport; [exact (hinv_sv H _ _ _ _ _ _ _ HI) | exact MU1 | exact WM1 | cbn; lia]).
      eapply evt_cut.
      { eapply (SF6 (Z_to_bv 64 TOP_SF_RA) (Z_to_bv 64 S1)) with (LF := (6, ff, fp) :: e_LF e) (ff := ff) (fp := fp) (lo := lo);
          [exact RF1 | left; reflexivity | reflexivity | replace (ff + fsz 6 - 8) with (ff + 4088) by (change (fsz 6) with 4096; lia); exact SF1 | rewrite HLib.u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)))
          | exact CE | rewrite HLib.u64_of_Z by lia; unfold AFS_STACK; lia | exact MI1 | exact AC1]. }
      intros ms2 P2. destruct P2 as (u0 & u1 & u2 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2
                                     & EQ2 & MU2 & WM2 & MI2 & ST2 & RF2 & SH2 & AC2).
      subst ms2. rewrite HLib.u64_of_Z in MU2, ST2 by lia. rewrite lf_remove_head in RF2.
      rewrite (ret_pc_even TOP_SF_RA ltac:(unfold TOP_SF_RA; lia) eq_refl).
      assert (SV2 : rw_cells asegs m2 (SP - 104) (esaved e))
        by (eapply rw_cells_transport; [exact SV1 | exact MU2 | exact WM2 | cbn; change (fshn 6) with 512; unfold AFS_STACK; lia]).
      eapply evt_cut.
      { eapply (hT2 (Z_to_bv 64 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (e_ra e) (e_s0 e) (e_s1 e) (e_s2 e) (e_s3 e) (e_s4 e) (e_s5 e) (e_s6 e) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (e_s11 e) F' fc' m2 SP);
          [reflexivity | lia | exact SV2]. }
      intros ms3 EQ3. hnf in EQ3. subst ms3. apply evt_done.
      do 14 eexists. exists m2. split; [reflexivity|].
      split.
      { assert (MU12 := munch_app _ _ _ _ _ MU1 MU2). eapply munch_eqW; [exact MU12|]. unfold WT, AFS_STACK. reflexivity. }
      split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|]. split; [exact MI2|].
      split.
      { destruct (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)) as [_ STu].
        assert (STu2 : stk asegs m2 S1 SP) by (eapply stk_transport_disjoint; [exact STu | exact MU2 | exact WM2 | cbn; change (fshn 6) with 512; unfold AFS_STACK; lia]).
        exact (stk_merge asegs m2 lo S1 SP ST2 STu2 ltac:(lia)). }
      split; [exact RF2 | exact AC2]. }

    intros msF2 mo2 KR2 MP2 P2. destruct P2 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & VIS2 & MU & WM & MI2 & ST2 & RF2 & AC2).
    apply (ah_done H HB). unfold hpost, fuzz_post.
    destruct HI as (_ & _ & RH & _ & _ & S0 & RA & (errv & ER) & _ & _ & _ & _ & XP & FS & LVI).
    rewrite (errno_ATP H e TP) in ER.
    hnf. exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m2, errv, sk, LBk, (XH H ff fp ++ XSc), F', fc'.
    cbn [cfg_ms cfg_model]. rewrite VIS2.
    assert (ESP : Z_to_bv 64 SP = e_sp e) by (unfold SP, eSP; apply Z_to_bv_bv_unsigned).
    rewrite ESP.
    split; [reflexivity|]. split; [exact FZ|]. split; [exact KR2|].
    split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP MP2)|].
    split; [exact MI2|]. split; [exact ST2|].
    split; [rewrite (errno_ATP H e TP); eapply rw_cells_transport; [exact ER | exact MU | exact WM |];
            cbn [cells_size csize]; apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & X & _); lia|].
    assert (A1 : Forall (aclient_write_ok H LBk) WT) by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    split; [eapply (ah_rauxv_frame H HB); [exact RA | exact MU | exact WM | exact A1]|].
    split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU | exact WM | exact A1]|].
    split; [exact PERM|].
    split; [apply Forall_app; split; [exact (fs_scratch_of_fresh H (e_LF e) 6 ff fp FFR) | exact FS]|].
    split.
    { eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch H (e_s e) (e_LB e) SP _ WT (e_m e)); [exact HB | exact (hpre_RH0 H e HP) | exact MU | exact WM |].
      eapply Forall_impl; [| exact WOK]. intros iv (_ & _ & _ & [K|K] & _); [left; exact K | right; intros a Ha; right; exact (K a Ha)]. }
    split; [exact RF2|]. split; [exact AC2|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM |]; eapply Forall_impl; [| exact WOK]; intros iv X; apply X|].
    split; [cbn [fz_cost FZP_A]; exact AL|].

    cbn [fz_inv FZP_A]. eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |].
    unfold WT, AFS_STACK. change (fshn 6) with 512. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP, AFS_FLAGS in *; lia.
  Qed.

  Definition cut_E (e : hent H) (c : config) : Prop :=
    exists (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (F' : bvmap 5 word) (fc' : bv 32)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m' : mem) (A : Z),
      as_VIS H sk (cfg_ms c) = MS (mkR x1 (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e)) (Z_to_bv 64 (eS1 e))
                                       x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                  F' (Z_to_bv 64 0xe8c28) fc' None m' (seg_rom asegs)
      /\ as_AKREL H sk c /\ as_MPRES H (e_mo e) (cfg_model c)
      /\ FPSteps.frm_zero fc'
      /\ hinv H e ff fp XSc sk LBk m'
      /\ Permutation LBk (e_LB e)
      /\ as_AL H sk >= as_AL H (e_s e) - top_cost (e_N e)
      /\ wr_at asegs m' (sh ff + 334) 3 /\ (exists j, rw_cells asegs m' (sh ff + 4) [CB 313 j])
      /\ rw_cells asegs m' (eS1 e + 24) (top_fr A ff).

  Lemma seg_E : forall (e : hent H) (c : config), hpre H e -> cut_E e c -> as_SR H (hpost e) c.
  Proof.
    intros e [msF mo] HP CT.
    destruct CT as (ff & fp & XSc & sk & LBk & F' & fc' & x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19
                    & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & A & VIS & KR & MP & FZ & HI & PERM & AL
                    & W334 & (j & CJ) & CF).
    cbn [cfg_ms cfg_model] in VIS, MP.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (rt_bp_ext H HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SSF8).
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *.
    unfold top_fr in CF.
    change [C8 (wz A); C8 (wz (sh ff + 4)); C8 (wz ff); C8 (wz (sh ff)); C8 (wz ff)]
      with ([C8 (wz A)] ++ [C8 (wz (sh ff + 4)); C8 (wz ff); C8 (wz (sh ff)); C8 (wz ff)]) in CF.
    apply rw_cells_app in CF as [_ CF32].
    replace (S1 + 24 + Z.of_nat (cells_size [C8 (wz A)])) with (S1 + 32) in CF32 by (cbn; lia).
    eapply (ahh_evt_then H HB (fun ms => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
              ms = MS (mkR (Z_to_bv 64 TOP_RET6) (Z_to_bv 64 S1) (e_gp e) (e_tp e) t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                      F' (Z_to_bv 64 TOP_RET6) fc' None m2 (seg_rom asegs)
              /\ hinv H e ff fp XSc sk LBk m2));
      [exact KR | exact VIS | |].
    { eapply evt_cut.
      { eapply (hE1 x1 (e_gp e) (e_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                    F' fc' m' SP S1 ff lo);
          [lia | lia | exact F3 | lia | lia | exact CF32 | exact W334 | exact (hinv_stk H _ _ _ _ _ _ _ HI) | exact (hinv_mi H _ _ _ _ _ _ _ HI)]. }
      intros ms1 (m1 & EQ1 & MU1 & WM1 & MI1 & ST1). subst ms1.
      assert (HI1 : hinv H e ff fp XSc sk LBk m1).
      { eapply (hinv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 |].
        unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; right. lia. }
      assert (CJ1 : rw_cells asegs m1 (sh ff + 4) [CB 313 j]) by (eapply rw_cells_transport; [exact CJ | exact MU1 | exact WM1 | cbn; lia]).
      eapply evt_cut.
      { eapply (SSF8 (Z_to_bv 64 TOP_RET6) (Z_to_bv 64 S1)) with (sa := sh ff + 4) (n := 313) (junk := j);
          [reflexivity | reflexivity | lia | exact CJ1 | exact MI1 | exact (hinv_ac H _ _ _ _ _ _ _ HI1)]. }
      intros ms2 P2. destruct P2 as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m2 & EQ2 & MU2 & WM2 & MI2 & CB2).
      subst ms2. rewrite (ret_pc_even TOP_RET6 ltac:(unfold TOP_RET6; lia) eq_refl).
      apply evt_done. exists w0, w1, w2, w10, w11, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m2. split; [reflexivity|].
      eapply (hinv_munch H HB); [exact HP | exact HI1 | exact MU2 | exact WM2 | exact MI2 | |].
      - eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn; lia].
      - unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; right. lia. }
    intros msF2 mo2 KR2 MP2 P2. destruct P2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & VIS2 & HI2).
    apply seg_T; [exact HP|].
    exists ff, fp, XSc, sk, LBk, F', fc', (Z_to_bv 64 TOP_RET6), t0, t1, t2, (Z_to_bv 64 S1), a0, a1, a2, a3, a4, a5, a6, a7,
      (Z_to_bv 64 (sh ff + 4)), (Z_to_bv 64 (sh ff)), x22, x23, x24, x25, x26, x27, t3, t4, t5, t6, m2.
    cbn [cfg_ms cfg_model]. split; [exact VIS2|]. split; [exact KR2|]. split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP MP2)|].
    split; [exact FZ|]. split; [exact HI2|]. split; [exact PERM | exact AL].
  Qed.

End TopT.
