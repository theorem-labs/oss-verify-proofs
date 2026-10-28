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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require B5_smkit LbB_WoGen.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition VRESIZE : Z := 0xe8d58.
Definition VAPP_NEW_RET : Z := 0xe952c.

Definition VRESIZE_STACK : Z := 128 + AOPNEW_STACK.

Definition VR0_RET : Z := 0xe8dfc.
Definition vr0_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (11%bv, ELit 0)].
Definition vr0_kn : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
    KWord (SA (EVar 32) 0) 8 (ELit 0); KWord (SA (EVar 32) 8) 8 (ELit 0); KWord (SA (EVar 32) 16) 8 (ELit 0);
    KWr (SA (EVar 33) (-16)) (ELit 16);
    KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) AIMG_TOP (2 ^ 47); KAlign (EVar 32) 8 ].
Definition vr0_knF : list kentry := Eval vm_compute in kn_fix 30 [VR0_RET] (SCR [] [] []) VRESIZE vr0_sr vr0_kn 40.
Definition vrA_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (11%bv, EVar 34)].
Definition vrA_kn : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
    KWord (SA (EVar 32) 0) 8 (ELit 0); KWord (SA (EVar 32) 8) 8 (ELit 0); KWord (SA (EVar 32) 16) 8 (ELit 0);
    KWr (SA (EVar 33) (-144)) (ELit 144);
    KRange (EVar 33) (2 ^ 45) (2 ^ 47); KAlign (EVar 33) 16; KRange (EVar 32) AIMG_TOP (2 ^ 47); KAlign (EVar 32) 8;
    KRange (EVar 34) 1 (2 ^ 24) ].
Definition vrA_knF : list kentry := Eval vm_compute in kn_fix 30 [AOPNEW] (SCR [] [] []) VRESIZE vrA_sr vrA_kn 40.

Definition vrB_sr : list expr := srs sr_id [(1%bv, ELit VAPP_NEW_RET); (2%bv, EAlu ALU_ADD (EVar 33) (ELit (-128)));
  (8%bv, EAlu ALU_ADD (EVar 33) (ELit (-40))); (9%bv, EVar 34); (10%bv, EVar 35);
  (18%bv, EAlu ALU_ADD (EVar 33) (ELit (-64))); (19%bv, ELit 0);
  (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-40))) (ELit 3)) (ELit SHBASE)); (21%bv, ELit SHBASE)].
Definition vrB_kn : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
    KWord (SA (EVar 33) (-120)) 8 (EVar 41); KWord (SA (EVar 33) (-112)) 8 (EVar 40); KWord (SA (EVar 33) (-104)) 8 (EVar 39);
    KWord (SA (EVar 33) (-96)) 8 (EVar 38); KWord (SA (EVar 33) (-88)) 8 (EVar 34); KWord (SA (EVar 33) (-80)) 8 (EVar 32);
    KWord (SA (EVar 33) (-72)) 8 (ELit 0xe92f8); KWord (SA (EVar 33) (-40)) 8 (ELit 0); KWord (SA (EVar 33) (-32)) 8 (EVar 32);
    KWr (SA (EVar 33) (-128)) (ELit 128);
    KRange (EVar 33) (2 ^ 45) (2 ^ 47); KAlign (EVar 33) 16; KRange (EVar 32) AIMG_TOP (2 ^ 47); KAlign (EVar 32) 8;
    KRange (EVar 34) 1 (2 ^ 24); KRange (EVar 35) AIMG_TOP (2 ^ 47); KAlign (EVar 35) 16 ].
Definition vrB_knF : list kentry := Eval vm_compute in kn_fix 30 [VFILL] (SCR [false] [] []) VAPP_NEW_RET vrB_sr vrB_kn 50.

Lemma vr_wr_stk : forall segs m lo hi a n, stk segs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at segs m a n.
Proof.
  intros segs m lo hi a n (S1 & S2 & S) H1 H2 H3. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (S (a + i) ltac:(lia))).
Qed.

Section Vec.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Hypothesis HANN : annotate_gen_stmt.

  Definition vresize_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (V n lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (p : Z) (pid : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) [(V, V + 24)] m m'
      /\ ablock_range H p (4 * n) /\ as_RHEAP H s' ((pid, p, 4 * n) :: LB) m'
      /\ rw_cells asegs m' V [C8 (wz p); C8 (wz (p + 4 * n)); C8 (wz (p + 4 * n))]
      /\ rw_cells asegs m' p [CB (Z.to_nat (4 * n)) (repeat (b8 0) (Z.to_nat (4 * n)))]
      /\ addressable m' p (4 * n)
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - as_Cm H (4 * n).

  Lemma vresize_sr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe)
      (V n lo B : Z) (errv : word) (mo : Model),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 VRESIZE) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 n -> 1 <= n <= 2 ^ 24 ->
    rw_cells asegs m V [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> SHAD m V (repeat (b8 0) 3) ->
    V mod 8 = 0 -> ((0x6e8000 <= V /\ V + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= V /\ V + 24 <= 2 ^ 47)) ->
    aclient_range H LB (bv_unsigned sp) V 24 -> aclient_range H LB (bv_unsigned sp) (sh V) 3 ->
    aclient_write_ok H LB (V, V + 24) -> afs_write_ok H LF (V, V + 24) -> aconst_ok (V, V + 24) ->
    (V + 24 <= bv_unsigned sp - VRESIZE_STACK \/ bv_unsigned sp <= V) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_alloc_ok H s LB (4 * n) -> as_Cm H (4 * n) <= as_AL H s ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - VRESIZE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 -> ACONST m -> as_RFS H LF m ->
    forall shi, stack0 m lo shi -> bv_unsigned sp <= shi ->
    as_SR H (vresize_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF V n lo B shi m mo) (mkCfg msF mo).
  Proof.
    intros until mo. intros VIS Ha0 Ha1 NB CV SV V8 VB CR1 CR2 CW FW CO VAP RH KR AOK CM RA SPB ST CE LO ERR MI TPV SP16 SPH AC RF shi S0 SHI.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold VRESIZE_STACK, AOPNEW_STACK, AMALLOC_STACK in LO, VAP.
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 V; Z_to_bv 64 spz; Z_to_bv 64 n]).
    assert (HR : regs_ok E vrA_sr R).
    { unfold vrA_sr. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp | exact Ha1]. }
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (GZV : gz m V 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (SD1 : sh0 m (spz + -40)) by (eapply sh0_of_stack0; [exact S0 | lia]).
    assert (SD2 : sh0 m (spz + -32)) by (eapply sh0_of_stack0; [exact S0 | lia]).
    assert (HK : know_ok asegs E m vrA_knF).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz SHBASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz 0)). }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 5 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; unfold AIMG_TOP; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R VRESIZE m (seg_rom asegs) HR HK 400%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VB VAP LO CE ACF1 ACF2 SPH SB0 SHI.
      all: first [ sc_dj | sc_shdj | sc_br ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 10%bv G10. rreg HR' 18%bv G18.
    rewrite w_addm in G2, G8, G18 by lia.
    rewrite G2 in HRe.
    assert (MU1 : munch [(spz - 144, spz)] m M1).
    { subst M1. clear - Hlf VB VAP LO CE ACF1 ACF2 SPH SB0. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (W1 : Forall (aclient_write_ok H LB) [(spz - 144, spz)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
    assert (RH1 : as_RHEAP H s LB M1) by exact (ah_RHEAP_frame H HH s LB m M1 _ RH MU1 WM1 W1).
    assert (RA1 : as_rauxv_ok H M1 B) by exact (ah_rauxv_frame H HH LB m M1 B _ RA MU1 WM1 W1).
    assert (SHT : sh AIMG_TOP < 2 ^ 32) by reflexivity.
    assert (AC1 : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [apply aconst_ok_high; [cbn; lia | right; left; cbn; lia] | apply Forall_nil]. }
    assert (EA : errno_addr tp = errno_addr (Z_to_bv 64 ATP)) by (rewrite TPV; reflexivity).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |].
      rewrite EA. unfold errno_addr. rewrite u64_of_Z by (unfold ATP; lia). cbn. unfold ATP. lia. }
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact HF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 4 * n) (LB := LB) (lo := lo) (B := B) (errv := errv);
        [ exact VIS1 | exact RH1 | exact KR1 | exact AOK | exact CM | exact RA1
        | rewrite u64_of_Z by lia; lia
        | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs M1 lo (spz - 128) spz ST1 ltac:(lia)))
        | exact CE | rewrite u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | exact ERR1 | exact MI1 | exact TPV | rewrite u64_of_Z by lia; Z.div_mod_to_equations; lia
        | exact AC1 | rewrite G10; apply w_mul; lia | lia ]. }
    intros [msF2 mo2] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & A & junk & pid & s'
                      & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1, (ret_pc_even 0xe952c ltac:(lia) eq_refl) in VIS2.
    rewrite u64_of_Z in AP2, ST2 by lia.
    rename R' into Rr1, HR' into HRA, Hlf into HlfA, Hms into HmsA.
    pose proof ABR as (A0 & A16 & AN0 & AIT & AAC & AFS & AAP). clear AFS.
    pose proof AIT as AIT'. unfold AIMG_TOP in AIT'.
    assert (NI : ~ In pid (map blk_id LB)).
    { pose proof (ah_nodup H HH _ _ _ RH2) as ND. cbn [map blk_id Datatypes.fst] in ND.
      apply NoDup_cons_iff in ND. exact (proj1 ND). }

    assert (WF : forall k, 8 <= k <= 144 -> wr_at asegs m (spz - k) 8) by (intros k Hk; eapply vr_wr_stk; [exact ST | lia | lia | lia]).
    pose proof (WF 120 ltac:(lia)) as W120. pose proof (WF 112 ltac:(lia)) as W112. pose proof (WF 104 ltac:(lia)) as W104.
    pose proof (WF 96 ltac:(lia)) as W96. pose proof (WF 88 ltac:(lia)) as W88. pose proof (WF 80 ltac:(lia)) as W80.
    pose proof (WF 72 ltac:(lia)) as W72. pose proof (WF 40 ltac:(lia)) as W40. pose proof (WF 32 ltac:(lia)) as W32.
    pose proof (WF 24 ltac:(lia)) as W24. pose proof (WF 16 ltac:(lia)) as W16. pose proof (WF 8 ltac:(lia)) as W8.
    assert (FA120 : rw_cells asegs M1 (spz - 120) [C8 s5]) by (subst M1; lgcell HlfA W120 3%nat).
    assert (FA112 : rw_cells asegs M1 (spz - 112) [C8 s4]) by (subst M1; lgcell HlfA W112 4%nat).
    assert (FA104 : rw_cells asegs M1 (spz - 104) [C8 s3]) by (subst M1; lgcell HlfA W104 5%nat).
    assert (FA96 : rw_cells asegs M1 (spz - 96) [C8 s2]) by (subst M1; lgcell HlfA W96 6%nat).
    assert (FA88 : rw_cells asegs M1 (spz - 88) [C8 (wz n)]) by (subst M1; lgcell HlfA W88 7%nat).
    assert (FA80 : rw_cells asegs M1 (spz - 80) [C8 (wz V)]) by (subst M1; lgcell HlfA W80 8%nat).
    assert (FA72 : rw_cells asegs M1 (spz - 72) [C8 (wz 0xe92f8)]) by (subst M1; lgcell HlfA W72 9%nat).
    assert (FA40 : rw_cells asegs M1 (spz - 40) [C8 (wz 0)]) by (subst M1; lgcell HlfA W40 2%nat).
    assert (FA32 : rw_cells asegs M1 (spz - 32) [C8 (wz V)]) by (subst M1; lgcell HlfA W32 1%nat).
    assert (FA24 : rw_cells asegs M1 (spz - 24) [C8 s1]) by (subst M1; lgcell HlfA W24 10%nat).
    assert (FA16 : rw_cells asegs M1 (spz - 16) [C8 s0]) by (subst M1; lgcell HlfA W16 11%nat).
    assert (FA8 : rw_cells asegs M1 (spz - 8) [C8 ra]) by (subst M1; lgcell HlfA W8 12%nat).
    assert (FR2 : forall a w, rw_cells asegs M1 a [C8 w] -> spz - 128 <= a -> rw_cells asegs m2 a [C8 w]).
    { intros a w Cw Ha. eapply (apres_rw_cells H); [exact AP2 | exact Cw | left; lia]. }
    pose proof (FR2 _ _ FA120 ltac:(lia)) as FB120. pose proof (FR2 _ _ FA112 ltac:(lia)) as FB112.
    pose proof (FR2 _ _ FA104 ltac:(lia)) as FB104. pose proof (FR2 _ _ FA96 ltac:(lia)) as FB96.
    pose proof (FR2 _ _ FA88 ltac:(lia)) as FB88. pose proof (FR2 _ _ FA80 ltac:(lia)) as FB80.
    pose proof (FR2 _ _ FA72 ltac:(lia)) as FB72. pose proof (FR2 _ _ FA40 ltac:(lia)) as FB40.
    pose proof (FR2 _ _ FA32 ltac:(lia)) as FB32. pose proof (FR2 _ _ FA24 ltac:(lia)) as FB24.
    pose proof (FR2 _ _ FA16 ltac:(lia)) as FB16. pose proof (FR2 _ _ FA8 ltac:(lia)) as FB8.

    pose proof (stk_split asegs M1 lo (spz - 128) spz ST1 ltac:(lia)) as [_ STU1].
    assert (STU2 : stk asegs m2 (spz - 128) spz) by (eapply (apres_stk H); [exact AP2 | exact STU1 | lia]).
    assert (STm2 : stk asegs m2 lo spz).
    { apply (stk_merge asegs m2 lo (spz - 128) spz); [| exact STU2 | lia]. replace (spz - 128) with (spz + -128) by lia. exact ST2. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]).
    assert (AP01 : apres H LB spz m M1).
    { eapply (apres_fresh H HH s' LB pid A (4 * n) spz m2 m M1); [exact RH2 | exact NI | exact MU1 | exact WM1 | | lia].
      repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil. }
    assert (RF1 : as_RFS H LF M1) by exact (RFS_via_apres H HH LF LB spz m M1 RF AP01).
    assert (RF2 : as_RFS H LF m2) by exact (RFS_via_apres H HH LF LB _ M1 m2 RF1 AP2).
    assert (CR1' : aclient_range H LB (spz + -128) V 24) by (destruct CR1 as [K|K]; [left; lia | right; exact K]).
    assert (CR2' : aclient_range H LB (spz + -128) (sh V) 3) by (destruct CR2 as [K|K]; [left; lia | right; exact K]).
    assert (CV1 : rw_cells asegs M1 V [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by (eapply (apres_rw_cells H); [exact AP01 | exact CV | exact CR1]).
    assert (CV2 : rw_cells asegs m2 V [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by (eapply (apres_rw_cells H); [exact AP2 | exact CV1 | exact CR1']).
    assert (SV1 : SHAD M1 V (repeat (b8 0) 3)) by (eapply (apres_SHAD H); [exact AP01 | exact SV | exact CR2]).
    assert (SV2 : SHAD m2 V (repeat (b8 0) 3)) by (eapply (apres_SHAD H); [exact AP2 | exact SV1 | exact CR2']).
    assert (GZ2 : gz m2 (spz - 64) 32) by (intros i Hi; eapply sh0_of_stack0; [exact S02 | lia]).
    pose proof (ACONST_shbase m2 AC2) as [CG2 CS2].

    rreg HRA 9%bv G9. rreg HRA 19%bv G19. rreg HRA 20%bv G20. rreg HRA 21%bv G21.
    lazymatch type of VIS2 with as_VIS _ _ _ = MS ?RR _ _ _ _ _ _ => remember RR as R2 eqn:HR20 end.
    pose (E2 := Eseed R2 [Z_to_bv 64 V; Z_to_bv 64 spz; Z_to_bv 64 n; Z_to_bv 64 A; Z_to_bv 64 0; Z_to_bv 64 0; s2; s3; s4; s5]).
    assert (HRB : regs_ok E2 vrB_sr R2).
    { unfold vrB_sr. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs; try reflexivity.
      all: rewrite ?G8, ?G9, ?G18, ?G19, ?G20, ?G21; rewrite ?w_addm by lia; reflexivity. }
    assert (HKB : know_ok asegs E2 m2 vrB_knF).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E2 m2 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG2 | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E2 m2 0x191038 _ 0%nat (C8 (wz SHBASE))); [exact CS2 | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell FB120 0%nat (C8 s5). }
      apply Forall_cons. { kword_cell FB112 0%nat (C8 s4). }
      apply Forall_cons. { kword_cell FB104 0%nat (C8 s3). }
      apply Forall_cons. { kword_cell FB96 0%nat (C8 s2). }
      apply Forall_cons. { kword_cell FB88 0%nat (C8 (wz n)). }
      apply Forall_cons. { kword_cell FB80 0%nat (C8 (wz V)). }
      apply Forall_cons. { kword_cell FB72 0%nat (C8 (wz 0xe92f8)). }
      apply Forall_cons. { kword_cell FB40 0%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell FB32 0%nat (C8 (wz V)). }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact STm2 | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 7 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; unfold AIMG_TOP; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R2 VAPP_NEW_RET m2 (seg_rom asegs) HRB HKB 400%nat [VFILL] (SCR [false] [] []) 50%N.
    { split_scs.
      all: clear - A0 AAC ACF2 NB.
      all: cbn [sc_denot]; evs; rewrite ?w_mul, ?w_add by lia; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia. }
    clear HKB.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E2 m2 lg) in Hms; set (M2 := mem_denot E2 m2 lg) in Hms end end.
    assert (HF2 : rfull R2) by (rewrite HR20; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
    readback HR' HF3 HR20 HReB.
    rreg HR' 1%bv GB1. rreg HR' 2%bv GB2. rreg HR' 8%bv GB8. rreg HR' 9%bv GB9. rreg HR' 10%bv GB10. rreg HR' 11%bv GB11.
    rreg HR' 18%bv GB18. rreg HR' 19%bv GB19. rreg HR' 20%bv GB20. rreg HR' 21%bv GB21.
    rewrite w_addm in GB2, GB10 by lia.
    rewrite GB1, GB2, GB8, GB9, GB10, GB11, GB18, GB19, GB20, GB21 in HReB.

    assert (MU2 : munch [(spz - 64, spz - 32)] m2 M2).
    { subst M2. clear - Hlf SPH SB0 ACF1 LO. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM2 : wmono asegs m2 M2) by (subst M2; apply wmono_mem_denot).
    assert (MI3 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms MI2).
    assert (STm3 : stk asegs M2 lo spz) by (subst M2; apply stk_mem_denot; exact STm2).
    assert (WFB : forall k, 32 <= k <= 128 -> wr_at asegs m2 (spz - k) 8) by (intros k Hk; eapply vr_wr_stk; [exact STm2 | lia | lia | lia]).
    pose proof (WFB 64 ltac:(lia)) as WB64. pose proof (WFB 56 ltac:(lia)) as WB56.
    pose proof (WFB 48 ltac:(lia)) as WB48. pose proof (WFB 40 ltac:(lia)) as WB40.
    assert (FC64 : rw_cells asegs M2 (spz - 64) [C8 (wz A)]) by (subst M2; lgcell Hlf WB64 3%nat).
    assert (FC56 : rw_cells asegs M2 (spz - 56) [C8 (wz A)]) by (subst M2; lgcell Hlf WB56 1%nat).
    assert (FC48 : rw_cells asegs M2 (spz - 48) [C8 (wz A)]) by (subst M2; lgcell Hlf WB48 2%nat).
    assert (FC40 : rw_cells asegs M2 (spz - 40) [C8 (wz (A + 4 * n))]).
    { subst M2. eapply (rw_cells_log_nth _ _ _ 0%nat);
        [ exact Hlf | reflexivity | apply Forall_nil | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
        | exact WB40 | reflexivity | exact I | ].
      evs. rewrite w_mul, w_add by lia. replace (4 * n + A) with (A + 4 * n) by lia. reflexivity. }
    assert (FT2 : forall a w, rw_cells asegs m2 a [C8 w] -> spz - 32 <= a -> rw_cells asegs M2 a [C8 w]).
    { intros a w Cw Ha. eapply rw_cells_transport; [exact Cw | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; lia]. }
    pose proof (FT2 _ _ FB32 ltac:(lia)) as FC32. pose proof (FT2 _ _ FB24 ltac:(lia)) as FC24.
    pose proof (FT2 _ _ FB16 ltac:(lia)) as FC16. pose proof (FT2 _ _ FB8 ltac:(lia)) as FC8.
    assert (WB2 : Forall (aclient_write_ok H ((pid, A, 4 * n) :: LB)) [(spz - 64, spz - 32)])
      by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
    assert (RH3 : as_RHEAP H s' ((pid, A, 4 * n) :: LB) M2) by exact (ah_RHEAP_frame H HH s' _ m2 M2 _ RH2 MU2 WM2 WB2).
    assert (RA3 : as_rauxv_ok H M2 B) by exact (ah_rauxv_frame H HH _ m2 M2 B _ RA2 MU2 WM2 WB2).
    assert (AC3 : ACONST M2).
    { eapply ACONST_frame; [exact AC2 | exact MU2 | exact WM2 |].
      apply Forall_cons; [apply aconst_ok_high; [cbn; lia | right; left; cbn; lia] | apply Forall_nil]. }
    assert (AP23 : apres H LB spz m2 M2).
    { eapply (apres_fresh H HH s' LB pid A (4 * n) spz m2 m2 M2); [exact RH2 | exact NI | exact MU2 | exact WM2 | | lia].
      repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil. }
    assert (RF3 : as_RFS H LF M2) by exact (RFS_via_apres H HH LF LB spz m2 M2 RF2 AP23).
    assert (S03 : stack0 M2 lo shi).
    { eapply stack0_transport; [exact S02 | exact MU2 | exact WM2 |].
      apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (ERR3 : rw_cells asegs M2 (bv_unsigned tp + -164) [C4 errv2]).
    { eapply rw_cells_transport; [exact ERR2 | exact MU2 | exact WM2 |].
      rewrite EA. rewrite u64_of_Z by (unfold ATP; lia). cbn [disjoint_from cells_size csize]. unfold ATP. lia. }
    assert (CV3 : rw_cells asegs M2 V [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by (eapply (apres_rw_cells H); [exact AP23 | exact CV2 | exact CR1]).
    assert (SV3 : SHAD M2 V (repeat (b8 0) 3)) by (eapply (apres_SHAD H); [exact AP23 | exact SV2 | exact CR2]).
    assert (ADDR3 : addressable M2 A (4 * n)).
    { eapply addressable_transport_hi; [exact ADDR | exact MU2 | exact WM2 | unfold AAPP_HI; lia |].
      apply Forall_cons; [right; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (SHV3 : shvis M2 A (A + 4 * n)).
    { eapply shvis_transport_hi; [exact (ah_blk_shvis H HH s' _ m2 pid A (4 * n) RH2 (or_introl eq_refl)) | exact MU2 | exact WM2 | lia | unfold AAPP_HI; lia |].
      apply Forall_cons; [right; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (CB3 : rw_cells asegs M2 A [CB (Z.to_nat (4 * n)) junk]).
    { eapply rw_cells_transport; [exact CB2 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize]. lia. }

    eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms | exact HReB |].
    intros msF3 mo3 KR3 MP3 VIS3.
    eapply (ahh_evt_then H HH); [exact KR3 | exact VIS3 | |].
    { eapply vfill_evt with (sb := spz - 64) (e := A) (al := V) (n := n) (lo := lo) (junk := junk).
      - first [reflexivity | f_equal; lia].
      - reflexivity.
      - lia.
      - rewrite u64_of_Z by lia. lia.
      - lia.
      - replace (spz - 64 + 16) with (spz - 48) by lia. exact FC48.
      - replace (spz - 64 + 32) with (spz - 32) by lia. exact FC32.
      - lia.
      - eapply sh0_of_stack0; [exact S03 | lia].
      - eapply sh0_of_stack0; [exact S03 | lia].
      - lia.
      - clear - A16. Z.div_mod_to_equations. lia.
      - unfold in_app_mem. destruct AAP as [[K1 K2]|[K1 K2]]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI, ALOWSH_LO, AIMG_TOP in *; lia.
      - exact CB3.
      - eapply addressable_accessible; [exact ADDR3 | lia | lia | unfold AAPP_HI; lia].
      - rewrite u64_of_Z by lia. exact (proj1 (stk_split asegs M2 lo (spz + -64) spz STm3 ltac:(lia))).
      - exact CE.
      - rewrite u64_of_Z by lia. lia.
      - rewrite u64_of_Z by lia. lia.
      - exact MI3.
      - exact AC3.
      - exact (B5_smkit.aconst_ok_aapp5 A (4 * n) A (A + 4 * n) AAP ltac:(lia) ltac:(lia)).
      - apply aconst_ok_high; [cbn; lia | right; left; cbn; lia].
      - left. lia.
      - left. lia. }
    intros msF4 mo4 KR4 MP4 POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & VIS4 & MU3 & WM3 & MI4 & ST4 & CB4 & FD48 & AC4).
    lazymatch type of VIS4 with context [ret_pc (Z_to_bv 64 ?z)] => rewrite (ret_pc_even z ltac:(lia) eq_refl) in VIS4 end.
    replace (spz + -64) with (spz - 64) in VIS4 by lia.
    rewrite u64_of_Z in MU3, ST4 by lia.
    replace (spz - 64 + 16) with (spz - 48) in FD48 by lia.

    assert (WB3 : Forall (aclient_write_ok H ((pid, A, 4 * n) :: LB)) [(A, A + 4 * n); (spz - 64 + 16, spz - 64 + 24); (spz - 64 - 16, spz - 64)]).
    { repeat (apply Forall_cons; [first [left; cbn [fst]; lia | right; right; left; exists (pid, A, 4 * n); split; [left; reflexivity | cbn; lia]] |]).
      apply Forall_nil. }
    assert (WH3 : wins_hi [(A, A + 4 * n); (spz - 64 + 16, spz - 64 + 24); (spz - 64 - 16, spz - 64)]).
    { repeat (apply Forall_cons; [first [right; cbn [fst]; unfold AHI_LO; lia | cbn [fst snd]; destruct AAP as [[K1 K2]|[K1 K2]]; [left | right]; lia] |]).
      apply Forall_nil. }
    assert (SO3 : Forall stack0_ok [(A, A + 4 * n); (spz - 64 + 16, spz - 64 + 24); (spz - 64 - 16, spz - 64)]).
    { repeat (apply Forall_cons; [first [apply stack0_ok_app; unfold AHI_LO; lia | apply (stack0_ok_aapp A (4 * n)); [exact AAP | lia | lia]] |]).
      apply Forall_nil. }
    replace (spz + -64) with (spz - 64) in MU3, ST4 by lia.
    assert (AP34 : apres H LB spz M2 m3).
    { eapply (apres_fresh H HH s' LB pid A (4 * n) spz m2 M2 m3); [exact RH2 | exact NI | exact MU3 | exact WM3 | | lia].
      repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil. }
    assert (FT3 : forall a w, rw_cells asegs M2 a [C8 w] -> spz - 64 <= a -> a + 8 <= spz - 48 \/ spz - 40 <= a -> rw_cells asegs m3 a [C8 w]).
    { intros a w Cw Ha Hb. eapply rw_cells_transport; [exact Cw | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; lia]. }
    pose proof (FT3 _ _ FC64 ltac:(lia) ltac:(lia)) as FD64. pose proof (FT3 _ _ FC56 ltac:(lia) ltac:(lia)) as FD56.
    pose proof (FT3 _ _ FC40 ltac:(lia) ltac:(lia)) as FD40. pose proof (FT3 _ _ FC32 ltac:(lia) ltac:(lia)) as FD32.
    pose proof (FT3 _ _ FC24 ltac:(lia) ltac:(lia)) as FD24. pose proof (FT3 _ _ FC16 ltac:(lia) ltac:(lia)) as FD16.
    pose proof (FT3 _ _ FC8 ltac:(lia) ltac:(lia)) as FD8.
    assert (FR8 : rw_cells asegs m3 (spz - 64)
                    [C8 (wz A); C8 (wz A); C8 (wz (A + 4 * n)); C8 (wz (A + 4 * n)); C8 (wz V); C8 s1; C8 s0; C8 ra]).
    { apply rw_cells_cons8; [exact FD64|]. replace (spz - 64 + 8) with (spz - 56) by lia.
      apply rw_cells_cons8; [exact FD56|]. replace (spz - 56 + 8) with (spz - 48) by lia.
      apply rw_cells_cons8; [exact FD48|]. replace (spz - 48 + 8) with (spz - 40) by lia.
      apply rw_cells_cons8; [exact FD40|]. replace (spz - 40 + 8) with (spz - 32) by lia.
      apply rw_cells_cons8; [exact FD32|]. replace (spz - 32 + 8) with (spz - 24) by lia.
      apply rw_cells_cons8; [exact FD24|]. replace (spz - 24 + 8) with (spz - 16) by lia.
      apply rw_cells_cons8; [exact FD16|]. replace (spz - 16 + 8) with (spz - 8) by lia.
      exact FD8. }
    assert (CV4 : rw_cells asegs m3 V [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by (eapply (apres_rw_cells H); [exact AP34 | exact CV3 | exact CR1]).
    assert (SV4 : SHAD m3 V (repeat (b8 0) 3)) by (eapply (apres_SHAD H); [exact AP34 | exact SV3 | exact CR2]).
    assert (ADDR4 : addressable m3 A (4 * n)) by (eapply addressable_transport_hi; [exact ADDR3 | exact MU3 | exact WM3 | unfold AAPP_HI; lia | exact WH3]).
    assert (SHV4 : shvis m3 A (A + 4 * n)) by (eapply shvis_transport_hi; [exact SHV3 | exact MU3 | exact WM3 | lia | unfold AAPP_HI; lia | exact WH3]).
    assert (RH4 : as_RHEAP H s' ((pid, A, 4 * n) :: LB) m3) by exact (ah_RHEAP_frame H HH s' _ M2 m3 _ RH3 MU3 WM3 WB3).
    assert (RA4 : as_rauxv_ok H m3 B) by exact (ah_rauxv_frame H HH _ M2 m3 B _ RA3 MU3 WM3 WB3).
    assert (RF4 : as_RFS H LF m3) by exact (RFS_via_apres H HH LF LB spz M2 m3 RF3 AP34).
    assert (S04 : stack0 m3 lo shi) by (eapply stack0_transport; [exact S03 | exact MU3 | exact WM3 | exact SO3]).
    assert (ST5 : stk asegs m3 lo spz) by (eapply LbB_WoGen.stk_wmono; [exact STm3 | exact WM3 | lia]).
    assert (ERR4 : rw_cells asegs m3 (bv_unsigned tp + -164) [C4 errv2]).
    { eapply rw_cells_transport; [exact ERR3 | exact MU3 | exact WM3 |].
      rewrite EA. rewrite u64_of_Z by (unfold ATP; lia). cbn [disjoint_from cells_size csize]. unfold ATP. lia. }
    assert (XP03 : xpres H LB spz [(V, V + 24)] m m3).
    { eapply xpres_trans; [exact (xpres_of_apres H _ _ _ _ _ AP01)|].
      eapply xpres_trans; [|exact (xpres_of_apres H _ _ _ _ _ AP34)].
      eapply xpres_trans; [|exact (xpres_of_apres H _ _ _ _ _ AP23)].
      eapply (xpres_weaken H); [exact (xpres_of_apres H _ _ [(V, V + 24)] _ _ AP2) | lia | intros b Hb; exact Hb | intros a Ha; exact Ha]. }

    eapply (ah_mono H HH).
    { eapply (vtail_sr' H HH HANN) with (P := A) (pid := pid) (LB := LB) (LF := LF) (B := B) (lo := lo) (shi := shi)
        (errv := errv2) (ra := ra) (s0 := s0) (s1 := s1) (V := V) (n := n) (spz := spz);
        [ exact VIS4 | lia | exact FR8 | exact CV4 | exact SV4 | exact V8 | lia | lia
        | apply Forall_cons; [cbn [fst snd]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO; lia | apply Forall_nil]
        | unfold stack0_ok, sh, ASHADOW_BASE, AHI_LO; cbn [fst snd]; Z.div_mod_to_equations; lia
        | exact CR1 | exact CR2 | exact CW | exact FW | exact CO | unfold vdisj; lia
        | exact CB4 | exact ADDR4 | exact SHV4 | exact RH4 | exact NI | exact ABR | exact KR4
        | exact RA4 | exact SPB | exact ST5 | exact CE | lia | exact ERR4 | exact MI4 | exact TPV
        | exact SP16 | exact SPH | exact AC4 | exact RF4 | exact S04 | exact SHI ]. }
    intros c' HQ.
    destruct HQ as (q0 & q1 & q2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & q3 & q4 & q5 & q6 & mf & ef
                    & VF & KF & MF & MIF & STF & ERF & RAF & XF & RHF & CVF & CBF & ADF & RFF & ACX & S0F).
    unfold vresize_post.
    exists q0, q1, q2, c0, c1, c2, c3, c4, c5, c6, c7, q3, q4, q5, q6, mf, ef, A, pid, s'.
    split; [rewrite Hsp; exact VF|].
    split; [exact KF|].
    split.
    { eapply (ah_mpres_trans H HH); [exact MP1|]. eapply (ah_mpres_trans H HH); [exact MP2|].
      eapply (ah_mpres_trans H HH); [exact MP3|]. eapply (ah_mpres_trans H HH); [exact MP4 | exact MF]. }
    split; [exact MIF|]. split; [exact STF|]. split; [exact ERF|]. split; [exact RAF|].
    split; [eapply xpres_trans; [exact XP03 | exact XF]|].
    split; [exact ABR|]. split; [exact RHF|]. split; [exact CVF|]. split; [exact CBF|]. split; [exact ADF|].
    split; [exact RFF|]. split; [exact ACX|]. split; [exact S0F|]. exact AL2.
  Qed.

  Definition vresize0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      as_VIS H s (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s c /\ as_MPRES H mo (cfg_model c)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

  Lemma vresize0_sr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (V lo : Z) (mo : Model),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 VRESIZE) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 0 ->
    rw_cells asegs m V [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> SHAD m V (repeat (b8 0) 3) ->
    V mod 8 = 0 -> 0x6e8000 <= V -> V + 24 <= 2 ^ 47 ->
    (V + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= V) ->
    as_AKREL H s (mkCfg msF mo) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
    bv_unsigned sp <= 2 ^ 47 -> ACONST m ->
    as_SR H (vresize0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s m mo) (mkCfg msF mo).
  Proof.
    intros until mo. intros VIS Ha0 Ha1 CV SV V8 VLO VHI VAP KR ST CE LO MI SPH AC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 V; Z_to_bv 64 spz]).
    assert (HR : regs_ok E vr0_sr R).
    { unfold vr0_sr. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp | exact Ha1]. }
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (GZV : gz m V 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (HK : know_ok asegs E m vr0_knF).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz SHBASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz 0)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz 0)). }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; unfold AIMG_TOP; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R VRESIZE m (seg_rom asegs) HR HK 60%nat [VR0_RET] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VLO VHI VAP LO CE ACF1 ACF2 SPH.
      all: first [ sc_dj | sc_shdj | sc_br ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 2%bv G2.
    assert (G2' : getr R' 2 = Z_to_bv 64 spz) by (rewrite G2; rewrite ?w_addm, ?w_add, ?v_addi_Z by lia; try reflexivity; f_equal; lia).
    rewrite G2' in HRe.
    assert (MU1 : munch [(spz - 16, spz)] m M1).
    { subst M1. clear - Hlf VLO VHI VAP LO CE ACF1 ACF2 SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    eapply (sr_evt H HH) with
      (P := fun ms => exists u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6,
              ms = MS (mkR ra (Z_to_bv 64 spz) gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc ra) fc None M1 (seg_rom asegs));
      [exact KR | exact VIS | |].
    { eapply evt_of_msteps; [exact Hms|].
      rewrite mkst_MS, HRe. step. apply evt_done. do 15 eexists. reflexivity. }
    intros msF' mo' KR' MP' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & HP).
    unfold vresize0_post.
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, M1.
    rewrite <- Hsp in HP.
    split; [exact HP|]. split; [exact KR'|]. split; [exact MP'|].
    split; [exact MU1|]. split; [exact WM1 | exact MI1].
  Qed.
End Vec.
