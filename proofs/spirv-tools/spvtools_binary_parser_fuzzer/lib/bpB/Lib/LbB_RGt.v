(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_RGl.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition MT_FA : Z := 6364136223846793005.
Definition CS_RET_RA : Z := 0x1006d8.
Definition RG_RET : Z := 0x10071c.

Section RGt.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition rgt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (ff fp sph : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(ff, ff + 8); (sh ff, sh ff + 16); (fp, fp + 1); (sph - 2520, sph - 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ as_RFS H LF m'.

  Lemma rgt_evt : forall (x1 x3 x4 x5 x6 x7 x11 x12 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (ra s0 s1 s2 s3 s4 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe) (ff fp sph lo : Z),

    rw_cells asegs m (sph - 2576) [C8 s4; C8 s3; C8 s2; C8 s1; C8 (wz MT_FA); C8 (wz CS_RET_RA)] ->
    rw_cells asegs m (sph - 16) [C8 s0; C8 ra] ->
    rw_cells asegs m (ff + 120) [C8 (wz fp)] -> wr_at asegs m ff 8 -> wr_at asegs m (sh ff) 16 -> wr_at asegs m fp 1 ->
    as_RFS H ((1, ff, fp) :: LF) m ->
    stk asegs m lo sph -> aceil <= lo -> lo <= sph - 2592 -> sph mod 32 = 0 -> sph <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (rgt_post ra (Z_to_bv 64 sph) x3 x4 s0 s1 s2 s3 s4 x21 x22 x23 x24 x25 x26 x27 F fc LF ff fp sph m)
      (MS (mkR x1 (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592)) (Z_to_bv 64 ff) x11
               x12 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) x15 x16 x17 x18 x19 (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31)
          F (Z_to_bv 64 LH_EXIT) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros CSF CTF CFP WFF WSH WFP RF ST CE LO SP32 SP47 MI.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4).
    pose proof (FR (1, ff, fp) (or_introl eq_refl)) as AFR. unfold ff_class, ff_addr, ff_flag in AFR. cbn [fst snd] in AFR.
    destruct AFR as (AK & AF1 & AF2 & (AF3 & AF4) & AF5 & AF6). unfold fsz in AF2. cbn in AF2.
    unfold AFS_HDR, AFS_SIZE, AFS_FLAGS in *. unfold AIMG_TOP in FS1.
    assert (SHF : 0x7fff7000 < sh ff) by (unfold sh; rewrite ASHADOW_BASE_val; unfold AIMG_TOP in FS1; Z.div_mod_to_equations; lia).
    assert (SHF2 : sh ff + 16 <= sh aceil) by (unfold sh; acb; Z.div_mod_to_equations; lia).
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    assert (FSB_BAND : (as_FSB H + 0xb09000 <= 0x7fff7000) \/ (0x10007fff8000 <= as_FSB H)).
    { unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AFS_SIZE in FS4. destruct FS4; [left | right]; lia. }
    remember (mkR x1 (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592)) (Z_to_bv 64 ff) x11 x12 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) x15 x16 x17 x18 x19 (Z_to_bv 64 0x7fff8000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 (sph - 2592); Z_to_bv 64 (sph - 2528); Z_to_bv 64 (sh ff);
                        s4; s3; s2; s1]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (8%bv, EVar 35); (9%bv, EVar 34); (10%bv, EVar 32); (13%bv, EVar 36); (14%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 120) 8 (EVar 33);
         KWord (SA (EVar 35) (-48)) 8 (EVar 37); KWord (SA (EVar 35) (-40)) 8 (EVar 38); KWord (SA (EVar 35) (-32)) 8 (EVar 39);
         KWord (SA (EVar 35) (-24)) 8 (EVar 40); KWord (SA (EVar 35) (-16)) 8 (ELit MT_FA); KWord (SA (EVar 35) (-8)) 8 (ELit CS_RET_RA);
         KWr (SA (EVar 32) 0) (ELit 8); KWr (SA (EVar 36) 0) (ELit 16); KWr (SA (EVar 33) 0) (ELit 1);
         KRange (EVar 34) (2 ^ 45) (2 ^ 47); KRange (EVar 35) (2 ^ 45) (2 ^ 47);
         KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 33) 0x6e8000 (2 ^ 47); KRange (EVar 36) 0x7fff7000 (2 ^ 47);
         KDisj (SA (EVar 32) 120) (ELit 8) (SA (EVar 36) 0) (ELit 16);
         KDisj (SA (EVar 35) (-48)) (ELit 48) (SA (EVar 32) 0) (ELit 8);
         KDisj (SA (EVar 35) (-48)) (ELit 48) (SA (EVar 36) 0) (ELit 16);
         KDisj (SA (EVar 35) (-48)) (ELit 48) (SA (EVar 33) 0) (ELit 1);
         KWr (SA (EVar 35) 8) (ELit 8) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CFP 0%nat (C8 (wz fp)). }
      apply Forall_cons. { kword_cell CSF 0%nat (C8 s4). }
      apply Forall_cons. { kword_cell CSF 8%nat (C8 s3). }
      apply Forall_cons. { kword_cell CSF 16%nat (C8 s2). }
      apply Forall_cons. { kword_cell CSF 24%nat (C8 s1). }
      apply Forall_cons. { kword_cell CSF 32%nat (C8 (wz MT_FA)). }
      apply Forall_cons. { kword_cell CSF 40%nat (C8 (wz CS_RET_RA)). }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WFF | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WSH | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WFP | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 5 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      do 4 (apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia|]).
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
          | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R LH_EXIT m (seg_rom asegs) HR HK 80%nat [L2_HEAD] (SCR [] [] []) 41%N.
    { first [apply Forall_nil | split_scs]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M := mem_denot E m lg) in Hms end end.
    assert (MU : munch [(ff, ff + 8); (sh ff, sh ff + 16); (fp, fp + 1); (sph - 2520, sph - 2512)] m M).
    { subst M. clear - Hlf AF1 AF2 AF5 AF6 FS1 FS2 ACF1 ACF2 SHF SHF2 SHB FSB_BAND CE LO SP47. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM : wmono asegs m M) by (subst M; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (WSK : forall a n, sph - 2592 <= a -> a + n <= sph -> 0 <= n -> wr_at asegs m a n).
    { intros a n Ha1 Ha2 Hn. eapply wr_at_sub; [exact (wr_at_of_stk asegs m lo sph ST) | lia | lia | lia]. }
    assert (CW0 : rw_cells asegs M (sph - 2520 + 8 * 1 - 8) [C8 x11]).
    { subst M. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | apply WSK; lia | reflexivity | exact I
        | evs; rewrite HR0; reflexivity]. }
    assert (W2 : wr_at asegs M (sph - 2520 + 8 * 1) (8 * (312 - 1))) by (eapply wr_at_wm; [apply WSK; lia | exact WM]).
    assert (FLAG : rw_cells asegs M fp [C1 (b8 0)]).
    { subst M. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
        | apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite !u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply Forall_nil]
        | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | exact WFP | reflexivity | exact I | reflexivity]. }
    assert (FLAGr : mrd asegs M (wa fp) = Some (b8 0)).
    { destruct FLAG as [[_ (_ & _ & B)] _]. specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B. exact B. }
    assert (RF1 : as_RFS H LF M).
    { pose proof (ah_release H HH ((1, ff, fp) :: LF) m M [(ff, ff + 8); (sh ff, sh ff + 16); (fp, fp + 1); (sph - 2520, sph - 2512)] 1 ff fp RF (or_introl eq_refl) MU WM) as K.
      rewrite lf_remove_head in K. apply K; [| exact FLAGr].
      apply Forall_cons; [left; right; exists (1, ff, fp); split; [left; reflexivity | unfold ff_class, ff_addr; cbn; unfold fsz; cbn; lia]|].
      apply Forall_cons; [left; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ATLS_PRIV_SZ, AFS_SIZE; split; [destruct FSB_BAND; lia | lia]|].
      apply Forall_cons; [right; split; reflexivity|].
      apply Forall_cons; [left; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ATLS_PRIV_SZ, AFS_SIZE; split; lia | apply Forall_nil]. }
    assert (CTF1 : rw_cells asegs M (sph - 16) [C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact CTF | exact MU | exact WM | cbn; destruct FSB_BAND; lia]).

    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20.
    assert (L11' : getr R' 11 = Z_to_bv 64 (sph - 2520 + 8 * 1)) by (rewrite L11, w_add by lia; f_equal; lia).
    destruct (l2_loop 310%nat R' F fc M (seg_rom asegs) 1 (sph - 2520) x11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) L10 L11' L12 CW0 W2)
      as (R2 & M2 & RUN2 & GK2 & MU2 & WM2).
    assert (CTF2 : rw_cells asegs M2 (sph - 16) [C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact CTF1 | exact MU2 | exact WM2 | cbn; lia]).
    assert (MI2 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ RUN2 MI1).
    assert (RF2 : as_RFS H LF M2).
    { apply (ah_RFS_frame H HH LF M M2 [(sph - 2520 + 8 * 1, sph - 2520 + 8 * 312)] RF1 MU2 WM2).
      apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ATLS_PRIV_SZ, AFS_SIZE; split; lia | apply Forall_nil]. }

    assert (HF2 : rfull R2) by exact (msteps_full asegs _ _ RUN2 HF1).
    pose proof (rfull_eq R2 HF2) as HRe2.
    pose (E2 := Eseed R2 [Z_to_bv 64 (sph - 2528); ra; s0]).
    assert (K2 : getr R2 2 = Z_to_bv 64 (sph - 2528)) by (rewrite (GK2 2%bv ltac:(inb)), L2; reflexivity).
    assert (HRb : regs_ok E2 (srs sr_id [(2%bv, EVar 32)]) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact K2. }
    assert (HKb : know_ok asegs E2 M2 [KWord (SA (EVar 32) 2520) 8 (EVar 33); KWord (SA (EVar 32) 2512) 8 (EVar 34); KRange (EVar 32) (2 ^ 45) (2 ^ 47)]).
    { unfold know_ok. apply Forall_cons. { kword_cell CTF2 8%nat (C8 ra). } apply Forall_cons. { kword_cell CTF2 0%nat (C8 s0). }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R2 L2_EXIT M2 (seg_rom asegs) HRb HKb 20%nat [RG_RET] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    pose proof (msteps_full asegs _ _ Hms0 HF2) as HF3. cbn [ms_regs] in HF3.
    readback HR'0 HF3 HRe2 HRe3.
    rreg HR'0 1%bv N1. rreg HR'0 2%bv N2. rreg HR'0 8%bv N8.
    assert (N2' : getr R'0 2 = Z_to_bv 64 sph) by (rewrite N2, w_add by lia; f_equal; lia).
    rewrite N1, N2', N8 in HRe3.
    assert (Q3 : getr R2 3 = x3) by (rewrite (GK2 3%bv ltac:(inb)), HRe; reflexivity).
    assert (Q4 : getr R2 4 = x4) by (rewrite (GK2 4%bv ltac:(inb)), HRe; reflexivity).
    assert (Q21 : getr R2 21 = x21) by (rewrite (GK2 21%bv ltac:(inb)), HRe; reflexivity).
    assert (Q22 : getr R2 22 = x22) by (rewrite (GK2 22%bv ltac:(inb)), HRe; reflexivity).
    assert (Q23 : getr R2 23 = x23) by (rewrite (GK2 23%bv ltac:(inb)), HRe; reflexivity).
    assert (Q24 : getr R2 24 = x24) by (rewrite (GK2 24%bv ltac:(inb)), HRe; reflexivity).
    assert (Q25 : getr R2 25 = x25) by (rewrite (GK2 25%bv ltac:(inb)), HRe; reflexivity).
    assert (Q26 : getr R2 26 = x26) by (rewrite (GK2 26%bv ltac:(inb)), HRe; reflexivity).
    assert (Q27 : getr R2 27 = x27) by (rewrite (GK2 27%bv ltac:(inb)), HRe; reflexivity).
    assert (Q9 : getr R2 9 = s1) by (rewrite (GK2 9%bv ltac:(inb)), L9; reflexivity).
    assert (Q18 : getr R2 18 = s2) by (rewrite (GK2 18%bv ltac:(inb)), L18; reflexivity).
    assert (Q19 : getr R2 19 = s3) by (rewrite (GK2 19%bv ltac:(inb)), L19; reflexivity).
    assert (Q20 : getr R2 20 = s4) by (rewrite (GK2 20%bv ltac:(inb)), L20; reflexivity).
    rewrite Q3, Q4, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27 in HRe3.
    eapply evt_of_msteps; [exact Hms|]. eapply evt_of_msteps; [exact RUN2|]. eapply evt_of_msteps; [exact Hms0|].
    change (PropExec.mkst R'0 (Z_to_bv 64 1050396) M2 (seg_rom asegs)) with (MS R'0 F (Z_to_bv 64 1050396) fc None M2 (seg_rom asegs)).
    rewrite HRe3. step. apply evt_done.
    exists (getr R2 5), (getr R2 6), (getr R2 7), (getr R2 10), (getr R2 11), (getr R2 12), (getr R2 13), (getr R2 14), (getr R2 15),
      (getr R2 16), (getr R2 17), (getr R2 28), (getr R2 29), (getr R2 30), (getr R2 31), M2.
    split; [reflexivity|].
    split.
    { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU MU2)].
      intros x Hx; cbn [app outside] in Hx |- *.
      repeat match type of Hx with _ /\ _ => let N := fresh "N" in destruct Hx as [N Hx] end.
      repeat split; let K := fresh "K" in intro K;
      match goal with N : ~ _ |- _ => apply N; clear - K; lia end. }
    split; [exact (wmono_trans asegs _ _ _ WM WM2)|]. split; [exact MI2 | exact RF2].
  Qed.
End RGt.
