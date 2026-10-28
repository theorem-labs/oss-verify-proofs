(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Spec04.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ModelAmb.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Spec ShapeLaws StartupRnd U.S0Startup U.S0MainEntry U.S0Usage U.S0OpenFail.

From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX Spec U.S0Startup U.S0MainEntry U.S0OpenFail_defs U.S0OpenFail. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module S0OpenFailBranch.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0OpenFail_defs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0OpenFail OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM.
Import ListNotations.
Local Open Scope bv_scope.
Import SX2. Import SX2S.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Section Branch.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rnd tid regs0 mem0.

  Theorem open_err_branch_cannot_open :
    OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM.open_err_branch sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P1 P2 P5 HR HK Habove.
    apply (S0OpenFail.ref_open_fail_errno sp0 a0s path envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp ME Hfits
             e vals R M (openat_errnos_range e He) HL P0 P38 P2 HR HK Habove).
  Qed.
End Branch.

(* [comment removed for export] *)
Corollary cannot_open_branch : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (uid hw : word) (rnd : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
  main_entry sp0 [a0s; dot_path] envv uid hw rnd tid regs0 mem0 ->
  open_err_branch sp0 a0s dot_path envv hw rnd tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open dot_path) fs0).
Proof.
  intros sp0 a0s envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME.
  exact (open_err_branch_cannot_open sp0 a0s dot_path envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME).
Qed.

End ACeilS1.
End S0OpenFailBranch.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ReadBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ReadChunk.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0World U.S0TargetPre.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require StepTac Hoare WalkTac Frame MemSplit LibMaskBits SumWalkTac RefMemcpyLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require LibKnowFrame LibKnowXfer RefNodes RefReadLib U.S0ReadBase. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ReadChunk. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ReadChunk.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0_code_1337c_1378c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHideSum.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0Read0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibMaskBits OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibKnowFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibKnowXfer OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefReadLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadChunk.S0ReadStage OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadChunk.S7ReadChunkW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadChunk.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0_code_1337c_1378c.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
(* [comment removed for export] *)

Import WalkHideSum.OptIn.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Local Open Scope bv_scope.
Import SX2. Import SX2S.


#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma front_walk : forall regs mem rom (buf cap : Z),
  getr regs 10 = Z_to_bv 64 buf -> getr regs 21 = Z_to_bv 64 cap -> (0 < buf < 2 ^ 64)%Z -> (0 < cap < 2 ^ 64)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x135d4 : word) mem rom) (mkst regs' (0x1364c : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 READ_STAGE
    /\ (forall r, In r [2; 3; 4; 8; 18; 20; 21; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf cap Ha0 Hs5 Hbuf Hcap. eexists. split.
  - stepb_ft F_1351c D_1351c ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_13520 D_13520. rewrite Ha0.
    stepn F_13524 D_13524.
    stepn F_13528 D_13528.
    stepn F_1352c D_1352c.
    stepb_tk F_13530 D_13530 ltac:(rewrite Hs5; rewrite ?getr_zero; first [rewrite c_eq_Z by lia; apply Z.eqb_neq; lia | cond_compute | match goal with |- ?g => idtac "COND"; idtac g; fail end]).
    stepn F_13554 D_13554.
    stepn F_13558 D_13558.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity).
    intros r Hr; cbv [In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

Section R0.
  Variables (sp0 p1 mb gm : word) (path content : list byte).
  Variables (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  Let MPRE := model_pre path VM stdin0 fs0 tid.
  Let MPOST := model_post VM stdin0 fs0 tid.

  (* [comment removed for export] *)
  Lemma loop_entry : forall R M K,
    read_pre sp0 p1 mb gm R M ->
    (forall R1, getr R1 9 = Z_to_bv 64 (bv_unsigned gm + 32) -> getr R1 23 = Z_to_bv 64 (bv_unsigned gm + 32) ->
       getr R1 19 = Z_to_bv 64 0 -> getr R1 22 = Z_to_bv 64 READ_STAGE ->
       (forall r, In r [2; 3; 4; 8; 18; 20; 21; 24; 25; 26; 27]%bv -> getr R1 r = getr R r) ->
       realizes RSEGS (mkCfg (mkst R1 (Z_to_bv 64 0x1364c) M (seg_rom RSEGS)) MPRE) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x135d4) M (seg_rom RSEGS)) MPRE) K.
  Proof.
    intros R M K RP HK. pose proof (rp_gm _ _ _ _ _ _ RP) as Hgm. pose proof alloc_ceiling_range as ACR.
    cps_destruct (front_walk R M (seg_rom RSEGS) (bv_unsigned gm + 32) 65536 (rp_a0 _ _ _ _ _ _ RP) (rp_s5 _ _ _ _ _ _ RP) ltac:(lia) ltac:(lia))
      as (R1 & RUN & A9 & A23 & A19 & A22 & AK).
    replace (Z_to_bv 64 0x135d4) with (0x135d4 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN |].
    replace (0x1364c : word) with (Z_to_bv 64 0x1364c) by (apply bv_eq; reflexivity).
    apply HK; assumption.
  Qed.

  (* [comment removed for export] *)
  Theorem read_k0 : forall R M K,
    read_pre sp0 p1 mb gm R M -> (L < 65536)%Z ->
    (forall R' M', read_post0 sp0 p1 gm content R M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x1367c) M' (seg_rom RSEGS)) MPOST) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x135d4) M (seg_rom RSEGS)) MPRE) K.
  Proof.
    intros R M K RP HL Hk.
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hceil Hb Hbi Hgm Hgb Hst Hgr Hmw Her Hkm]. rewrite Hceil in Hb, Hgm.
    apply (loop_entry R M K RP). intros R1 A9 A23 A19 A22 AK.
    change MPRE with (modelG path stdin0 fs0 tid 0 VM).
    apply (chunk_loop_mid path content stdin0 fs0 tid VM Hfile (Z.to_nat 65536) R1 M (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [exact A9 | split; [exact A19 | split; [|split; [|exact A22]]]]].
      + rewrite (AK 2%bv) by (cbn; noncert_qtauto). exact Rsp.
      + rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
      + rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - subst L. lia.
    - replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia.
    - replace (bv_unsigned gm + 32 + 0)%Z with (bv_unsigned gm + 32)%Z by lia. apply Hgr; lia.
    - intros HcL. exfalso. subst L. lia.
    - (intros HLc R' M'; cps_intros (P2 & P9 & P23 & P19 & PK); intros PM). apply Hk.
      pose proof PM as [[EQ GR] RD].
      constructor.
      + exact P2.
      + rewrite (PK 3%bv) by (cbn; noncert_qtauto). rewrite (AK 3%bv) by (cbn; noncert_qtauto). exact Rgp.
      + rewrite (PK 4%bv) by (cbn; noncert_qtauto). rewrite (AK 4%bv) by (cbn; noncert_qtauto). exact Rtp.
      + rewrite (PK 8%bv) by (cbn; noncert_qtauto). rewrite (AK 8%bv) by (cbn; noncert_qtauto). exact Rs0.
      + exact P9.
      + rewrite (PK 18%bv) by (cbn; noncert_qtauto). rewrite (AK 18%bv) by (cbn; noncert_qtauto). exact Rs2.
      + rewrite P19. subst L. reflexivity.
      + rewrite (PK 20%bv) by (cbn; noncert_qtauto). rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
      + rewrite (PK 21%bv) by (cbn; noncert_qtauto). rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
      + rewrite (PK 22%bv) by (cbn; noncert_qtauto). exact A22.
      + exact P23.
      + intros r Hr. cbv [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
          (rewrite PK by (cbn; noncert_qtauto); rewrite AK by (cbn; noncert_qtauto); reflexivity).
      + (* [comment removed for export] *)
        intros a [O1 [O2 [O3 _]]]. apply EQ. cbn [outside loop_regions]. unfold in_rng, READ_STAGE in *. rewrite !u_small in * by lia.
        subst L. repeat split; lia.
      + exact GR.
      + (* [comment removed for export] *)
        subst L. eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned gm + 32) 0); try lia; [|exact PM].
        rewrite pref_0. reflexivity.
      + eapply stack_writable_grows; [exact GR | exact Hst].
      + eapply group_writable_grows; [exact GR | exact Hgr].
  Qed.
End R0.
End ACeilS2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Read0.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0SymPlanSoundA.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeLaws OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Usage OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0OpenFail OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Main.S0OpenFailBranch OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadChunk.S0ReadStage OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Main.S0Read0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0SymPlanSoundA.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x.
Module S0LeafWorld.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.S0WorldVM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope bv_scope.

Section LeafWorld.
  Context {ACEIL__ : ACeil} {RUNW__ : RunW}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rnd tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
  Hypothesis Hguard : run_guard = bv_unsigned (canary_w rnd).         (* [comment removed for export] *)
  Hypothesis Hsec : run_secret = bv_unsigned (secret_word rnd).
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : openat_plain_name path = true.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.

  (* [comment removed for export] *)
  Definition vm_small (VM : VmMaps) (gm : word) : Prop :=
    vm_reserved VM = segments_reserved RSEGS /\ vm_limit VM = LIM   (* [comment removed for export] *)
    /\ (length (vm_maps VM) <= 4)%nat
    /\ In (gm, Z_to_bv 64 69632) (vm_maps VM)
    /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 69632)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
    /\ seps (vm_maps VM).                                   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition after_malloc (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->                    (* [comment removed for export] *)
      read_pre sp0 (p1 sp0 a0s path envv) mb gm R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned hw) M ->   (* [comment removed for export] *)
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM mb gm -> vm_small VM gm ->
      target_vmx (bv_unsigned sp0) (bv_unsigned gm) area brkv mas VM -> auxv0 (bv_unsigned sp0) M ->   (* [comment removed for export] *)
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x135d4) M (seg_rom RSEGS))
                              (model_pre path VM stdin0 fs0 tid)) K.

  (* [comment removed for export] *)
  Lemma brk_ok_sem : forall K, after_malloc K ->
    brk_ok_branch sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 K.
  Proof using Hva Hve Hvsp Htid ME Hbrk Hceil Hguard Hsec Hfile Hpne Hpnd Hplen.
    intros K AM. exact (S0W65x.brk_ok_sem sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hceil Hguard Hsec Hplen K AM).
  Qed.

  (* [comment removed for export] *)
  Lemma mmap_ok_sem : forall K, after_malloc K ->
    mmap_ok_branch sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 K.
  Proof using Hva Hve Hvsp Htid ME Hbrk Hceil Hguard Hsec Hfile Hpne Hpnd Hplen.
    intros K AM. exact (S0W65x.mmap_ok_sem sp0 a0s path envv hw rnd tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hceil Hguard Hsec Hplen K AM).
  Qed.
End LeafWorld.
End S0LeafWorld.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0LibStdioCall.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymFold.
Module S0Header_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0LibStdioCall.
   (* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPSh : list Z :=
  [0x306ac; 0x30ab0; 0x30ba8; 0x30bec; 0x13208; 0x2aaa8; 0x291c0; 0x13850; 0x2b114]%Z.
Definition FUELh : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition runh (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELh true STOPSh scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENVh (content : list byte) (vals : list word) : env := Env (vals_ev vals) (blobs_ev [content]).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition ax (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).
Definition gmx (k : Z) : expr := EAlu ALU_ADD (EVar 3) (ELit k).
Definition J (i : nat) : expr := EVar (9 + i).

(* [comment removed for export] *)
Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x441e0; J 5; J 6; J 7;
   ELit 2; gmx 32; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; EVar 5; ELit 3; ELit 65536; ELit 0x340d9; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

(* [comment removed for export] *)
Definition kn_Hstack : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x28c48);
   KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x13580); KWord (SA (EVar 0) (-88)) 8 (spx 32);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-120)) 8 (ELit 0)].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition area_x : expr := EAlu ALU_AND (ax 24) (ELit 18446744073709547520).

(* [comment removed for export] *)
Definition kn_Hheap : list kentry :=
  [KAlign (EVar 2) 4096; KRange (EVar 2) 0x2000 0x7fffff7ff000;
   KAlign (EVar 3) 4096; KRange (EVar 3) 0x66000 0x7fffff7ef000;
   KWr (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 2) 0) 4096;
   KDisj (SA (EVar 2) 0) 4096 (SA (EVar 3) 0) 69632;
   (* [comment removed for export] *)
   KDisj (SA (ELit 0) 0x10000) 0x56000 (SA (EVar 2) 0) 4096;
   KWr (SA (EVar 2) 0) 4096;
   KWord (SA (EVar 2) 0) 8 (EVar 42);
   KWord (SA area_x 0) 8 (EVar 42); KRange area_x 0x2000 0x7fffff7ff000;
   KDisj (SA (ELit 0) 0x10000) 0x56000 (SA area_x 0) 4096;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA area_x 0) 4096;
   KWord (SA (EVar 2) 24) 8 (ax 24); KWord (SA (EVar 2) 32) 8 (ax 24);
   KWord (SA (EVar 2) 40) 8 (EVar 3);
   KWord (SA (EVar 2) 48) 4 (ELit 0); KWord (SA (EVar 2) 52) 4 (ELit 0);
   KWord (SA (EVar 2) 56) 8 (ELit 0x11b20);
   KWord (SA (EVar 3) 0) 8 (ax 24);
   KWord (SA (EVar 3) 28) 1 (ELit 0); KWord (SA (EVar 3) 29) 1 (ELit 160); KWord (SA (EVar 3) 30) 2 (ELit 1);
   KWord (SA (EVar 3) 65568) 1 (ELit 0);
   KWord (SA (EVar 3) 69623) 1 (ELit 0); KWord (SA (EVar 3) 69624) 4 (ELit 0xfdc);
   KZero (SA (EVar 3) 69628) (ELit 4)].

(* [comment removed for export] *)
Definition kn_Himage : list kentry :=
  [KWr (SA (ELit 0) 0x33000) 0x33000;
   KImg 0x10000 0x34090; KImg 0x34091 0x340d9; KImg 0x440d9 0x44110;
   KWord (SA (ELit 0) 0x44138) 4 (EVar 4); KWord (SA (ELit 0) 0x4413c) 4 (EVar 8);
   KImg 0x441f8 0x641e8; KImg 0x64220 0x64450; KWord (SA (ELit 0) 0x64450) 8 (EVar 41);
   KImg 0x64471 0x64478; KImg 0x644e0 0x644e8;
   KWord (SA (ELit 0) 0x644e8) 8 (EVar 42);
   KWord (SA (ELit 0) 0x644f8) 8 (ELit 0);
   KWord (SA (ELit 0) 0x64698) 8 (ax 24);
   KWord (SA (ELit 0) 0x64818) 8 (ELit 1);
   KWord (SA (ELit 0) 0x64878) 1 (ELit 1);
   KImg 0x64890 0x66000;
   KRange (EVar 4) 1 4194303].

Definition kn_H : list kentry := kn_Hstack ++ kn_Hheap ++ kn_Himage.
(* [comment removed for export] *)
Definition kn_short : list kentry := kn_H ++ [KRange (EVar 5) 0 5].
(* [comment removed for export] *)
Definition kn_long : list kentry :=
  kn_H ++ [KRange (EVar 5) 6 65535;
           KWord (SA (EVar 3) 32) 1 (EVar 6); KWord (SA (EVar 3) 33) 1 (EVar 7);
           KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

Definition NXh : nat := 43.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hsA__t := runh scr0 (SS 0x1367c sr_H [] kn_short NXh).
Definition srSA : list expr := Eval vm_compute in s_regs (fst (fst hsA__t)).
Definition hsA := ltac:(SymFold.sf_def hsA__t (srSA, (kn_short, tt))).
Definition knSA : list kentry := Eval vm_compute in kn_after hsA kn_short.
(* [comment removed for export] *)
Definition scS : stdio_res := Eval vm_compute in
  match stdio_call NXh srSA knSA with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition NXh2 : nat := 75.
Definition srSB0 : list expr := Eval vm_compute in sc_sr scS.
Definition knSB0 : list kentry := Eval vm_compute in sc_kn scS.
Definition hsB := Eval vm_compute in runh scr0 (SS (sc_ret scS) srSB0 [] knSB0 NXh2).
Definition srSB : list expr := Eval vm_compute in s_regs (fst (fst hsB)).
Definition knSB : list kentry := Eval vm_compute in kn_after hsB knSB0.
(* [comment removed for export] *)
Definition knSB2 : list kentry := Eval vm_compute in kn_unfill knSB (EVar 3) 0 69632.
Definition srSC0 : list expr := sr_upd srSB (ridx 10) (ELit 0).
Definition hsC__t := runh scr0 (SS 0x2aed4 srSC0 [] knSB2 NXh2).
Definition srSC : list expr := Eval vm_compute in s_regs (fst (fst hsC__t)).
Definition hsC := ltac:(SymFold.sf_def hsC__t (srSC, (knSB2, tt))).
Definition knSC : list kentry := Eval vm_compute in kn_after hsC knSB2.

(* [comment removed for export] *)
Definition scr_taken : scripts := SCR [true] [] [].
Definition hoA__t := runh scr_taken (SS 0x1367c sr_H [] kn_long NXh).
Definition srOA : list expr := Eval vm_compute in s_regs (fst (fst hoA__t)).
Definition hoA := ltac:(SymFold.sf_def hoA__t (srOA, (kn_long, tt))).
Definition knOA : list kentry := Eval vm_compute in kn_after hoA kn_long.
Definition scO__t : stdio_res := match stdio_call NXh srOA knOA with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srOB0 : list expr := Eval vm_compute in sc_sr scO__t.
Definition knOB0 : list kentry := Eval vm_compute in sc_kn scO__t.
Definition scO : stdio_res := ltac:(SymFold.sf_def scO__t (srOB0, (knOB0, tt))).
Definition hoB := Eval vm_compute in runh scr0 (SS (sc_ret scO) srOB0 [] knOB0 NXh2).
Definition srOB : list expr := Eval vm_compute in s_regs (fst (fst hoB)).
Definition knOB : list kentry := Eval vm_compute in kn_after hoB knOB0.
Definition knOB2 : list kentry := Eval vm_compute in kn_unfill knOB (EVar 3) 0 69632.
Definition srOC0 : list expr := sr_upd srOB (ridx 10) (ELit 0).
Definition hoC__t := runh scr0 (SS 0x2aed4 srOC0 [] knOB2 NXh2).
Definition srOC : list expr := Eval vm_compute in s_regs (fst (fst hoC__t)).
Definition hoC := ltac:(SymFold.sf_def hoC__t (srOC, (knOB2, tt))).
Definition knOC : list kentry := Eval vm_compute in kn_after hoC knOB2.

(* [comment removed for export] *)
Definition scr_fall : scripts := SCR [false] [] [].
Definition hkA__t := runh scr_fall (SS 0x1367c sr_H [] kn_long NXh).
Definition srK : list expr := Eval vm_compute in s_regs (fst (fst hkA__t)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cfglen_x : expr := Eval vm_compute in nth 11 srK (ELit 0).
(* [comment removed for export] *)
Definition cfglen_v : expr := EVar 47.
Definition srT : list expr := Eval vm_compute in map (esub cfglen_x cfglen_v) srK.
Definition knT : list kentry := kn_long.

(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.micromega.Lia.

(* [comment removed for export] *)
Definition cfgF (v6 v7 : word) : word :=
  edenot (Env (fun n => match n with 6%nat => v6 | 7%nat => v7 | _ => Z_to_bv 64 0 end) (blobs_ev []))
         cfglen_x.

Lemma cfglen_x_cfgF : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_x = cfgF (vals_ev vals 6) (vals_ev vals 7).
Proof. intros. reflexivity. Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - cps_intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_shift8_byte : forall k b, (0 <= k)%Z -> (0 <= b < 256)%Z ->
  Z.lor (k * 256) b = (k * 256 + b)%Z.
Proof.
  intros k b Hk Hb.
  assert (Hand : Z.land (k * 256) b = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    - change 256%Z with (2 ^ 8)%Z. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|Hb0].
      + rewrite Z.bits_0. apply andb_false_r.
      + rewrite (Z.bits_above_log2 b i); [apply andb_false_r|lia|].
        apply Z.lt_le_trans with 8%Z; [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 8)%Z with 256%Z. lia. }
  rewrite <- Z.lxor_lor by exact Hand. symmetry. apply Z.add_nocarry_lxor. exact Hand.
Qed.

(* [comment removed for export] *)
Local Ltac cfgF_val_symbolic b0 b1 :=
  unfold cfgF, cfglen_x; cbn [edenot ev eb];
  unfold Sem.alu64, Sem.alu, Sem.mul_div, ext_val, ext_Z;
  rewrite bv_or_unsigned, bv_shiftr_unsigned, bv_and_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned;
  change (Z.land (bv_wrap 64 49) (bv_wrap 64 63)) with 49%Z;
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z; change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z;
  change (8 * N.of_nat 1)%N with 8%N;
  rewrite !Z.div_1_r;
  rewrite (bv_wrap_small 64 b0) by (unfold bv_modulus; lia);
  rewrite (bv_wrap_small 64 b1) by (unfold bv_modulus; lia);
  rewrite (Z.mod_small b0 256) by lia; rewrite (Z.mod_small b1 256) by lia;
  change (bv_wrap 64 144115188075855872) with (2 ^ 57)%Z;
  rewrite Z.shiftr_div_pow2 by lia;
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
  change (2 ^ Z.of_N 8)%Z with 256%Z; change (256 `div` 2)%Z with 128%Z; change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z;
  rewrite (Z.mod_small b0 (2 ^ 64)) by lia;
  let Hs := fresh "Hs" in
  destruct (Z.lt_ge_cases b1 128) as [Hs|Hs];
  [ rewrite (Z.mod_small (b1 + 128) 256) by lia;
    replace (b1 + 128 - 128)%Z with b1 by lia;
    rewrite (Z.mod_small b1 (2 ^ 64)) by lia;
    rewrite (Z.mod_small (2 ^ 57 * b1) (2 ^ 64)) by lia;
    replace (2 ^ 57 * b1)%Z with (b1 * 256 * 2 ^ 49)%Z by lia; rewrite Z.div_mul by lia;
    rewrite (Z.mod_small (b0 + 256 * b1) 32768) by lia;
    rewrite lor_shift8_byte by lia; lia
  | replace ((b1 + 128) mod 256)%Z with (b1 + 128 - 256)%Z
      by (apply Z.mod_unique with 1%Z; [left; lia | lia]);
    replace ((b1 + 128 - 256 - 128) mod 2 ^ 64)%Z with (2 ^ 64 + (b1 - 256))%Z
      by (apply Z.mod_unique with (-1)%Z; [left; lia | lia]);
    replace ((2 ^ 57 * (2 ^ 64 + (b1 - 256))) mod 2 ^ 64)%Z with (2 ^ 57 * (b1 - 128))%Z
      by (apply Z.mod_unique with (2 ^ 57 - 1)%Z; [left; lia | lia]);
    replace (2 ^ 57 * (b1 - 128))%Z with ((b1 - 128) * 256 * 2 ^ 49)%Z by lia; rewrite Z.div_mul by lia;
    replace ((b0 + 256 * b1) mod 32768)%Z with (b0 + 256 * b1 - 32768)%Z
      by (apply Z.mod_unique with 1%Z; [left; lia | lia]);
    rewrite lor_shift8_byte by lia; lia ].

Lemma cfgF_val : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  pose proof (Z.mod_pos_bound (b0 + 256 * b1) 32768 ltac:(lia)) as HM.
  apply bv_eq. rewrite (u_small ((b0 + 256 * b1) mod 32768)) by lia.
  first
    [ solve [ cfgF_val_symbolic b0 b1 ]
    | (* [comment removed for export] *)
      idtac "S0Header_defs.cfgF_val: symbolic proof failed, falling back to the 65536-entry VM table";
      assert (T : forallb (fun b1 => forallb (fun b0 =>
                Z.eqb (bv_unsigned (cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1))) ((b0 + 256 * b1) mod 32768))
                (zseq 256)) (zseq 256) = true) by (vm_cast_no_check (@eq_refl bool true));
      rewrite forallb_forall in T;
      specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))); rewrite forallb_forall in T;
      specialize (T b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))); apply Z.eqb_eq in T; exact T ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.
Lemma cfglen_val : forall content vals,
  vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content) -> vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content) ->
  edenot (ENVh content vals) cfglen_x = Z_to_bv 64 (hdr_cfglen content).
Proof.
  intros content vals P6 P7. unfold ENVh. rewrite cfglen_x_cfgF, P6, P7.
  pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
  change (bv_modulus 8) with 256%Z in B0, B1.
  unfold hdr_cfglen, hdr_cfg. apply cfgF_val; unfold hdr_b0, hdr_b1; lia.
Qed.

Lemma hdr_cfglen_range : forall content, (0 <= hdr_cfglen content < 32768)%Z.
Proof. intros. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition sx8F (v7 : word) : word := ext_val true 0 1 v7.
Lemma sx8F_tab :
  forallb (fun b1 => Z.eqb (bv_unsigned (sx8F (Z_to_bv 64 b1)))
                           (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)%Z) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sx8F_val : forall b1, (0 <= b1 < 256)%Z ->
  sx8F (Z_to_bv 64 b1) = Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)%Z.
Proof.
  intros b1 H1. pose proof sx8F_tab as T. rewrite forallb_forall in T.
  specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in T.
  apply bv_eq. rewrite T. symmetry. apply u_small. destruct (b1 <? 128)%Z eqn:Eb; [apply Z.ltb_lt in Eb|apply Z.ltb_ge in Eb]; lia.
Qed.

(* [comment removed for export] *)
Lemma mod_eq_shift : forall a b k m, (0 < m)%Z -> (a = b + k * m)%Z -> (a mod m = b mod m)%Z.
Proof. intros a b k m Hm ->. apply Z_mod_plus_full. Qed.
End S0Header_defs.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Nodes. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ModelAmb. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require FileSim AgentLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require LibWritev U.S0ExitBase U.S0StdioDefs U.S0Exit StreamSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymHide.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Module S0LeafHeader.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.





Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.



Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
(* [comment removed for export] *)

Import SymHide.OptIn.
(* [comment removed for export] *)
Local Ltac SymHide.sc_cands ::= constr:((S0Header_defs.sr_H, (S0Header_defs.kn_Hstack, (S0Header_defs.kn_Hheap, (S0Header_defs.kn_Himage, (S0Header_defs.kn_H, (S0Header_defs.kn_short, (S0Header_defs.kn_long, (S0Header_defs.srSA, (S0Header_defs.knSA, (S0Header_defs.srSB0, (S0Header_defs.knSB0, (S0Header_defs.srSB, (S0Header_defs.knSB, (S0Header_defs.knSB2, (S0Header_defs.srSC0, (S0Header_defs.srSC, (S0Header_defs.knSC, (S0Header_defs.srOA, (S0Header_defs.knOA, (S0Header_defs.srOB0, (S0Header_defs.knOB0, (S0Header_defs.srOB, (S0Header_defs.knOB, (S0Header_defs.knOB2, (S0Header_defs.srOC0, (S0Header_defs.srOC, (S0Header_defs.knOC, (S0Header_defs.srK, (S0Header_defs.srT, (S0Header_defs.knT, tt))))))))))))))))))))))))))))))).

Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Module S7Header.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeLaws OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.SpecConsts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.FileSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ExitBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StdioDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Exit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0LibStdioCall OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibMaskBits OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Main.S0Header_defs.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)


#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUELh STOPSh scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUELh STOPSh scr NX true.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hdr_img_ranges : list (Z * Z) :=
  [(0x10000, 0x34090); (0x34091, 0x340d9); (0x440d9, 0x44110); (0x441f8, 0x641e8); (0x64220, 0x64450);
   (0x64471, 0x64478); (0x644e0, 0x644e8); (0x64890, 0x66000)]%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Record header_pre (sp0 p1 gm tid : word) (area : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := HDR_PRE {
  (* [comment removed for export] *)
  hp_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  hp_gp : getr R 3 = Z_to_bv 64 0x10800;
  hp_tp : getr R 4 = Z_to_bv 64 0x441e0;
  hp_s0 : getr R 8 = Z_to_bv 64 2;
  hp_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned gm + 32);
  hp_s2 : getr R 18 = p1;
  hp_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));
  hp_s4 : getr R 20 = Z_to_bv 64 3;
  hp_s5 : getr R 21 = Z_to_bv 64 65536;
  hp_s6 : getr R 22 = Z_to_bv 64 0x340d9;                      (* [comment removed for export] *)
  hp_s7 : getr R 23 = Z_to_bv 64 0;                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  hp_sp0 : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z;
  hp_ceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z;    (* [comment removed for export] *)
  hp_gm  : (0x66000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= alloc_ceiling)%Z
           /\ (bv_unsigned gm mod 4096 = 0)%Z;
  hp_area : (0x2000 <= area)%Z /\ (area + 4096 <= alloc_ceiling)%Z /\ (area mod 4096 = 0)%Z;
  hp_area_img : (area + 4096 <= 0x10000 \/ 0x67000 <= area)%Z;   (* [comment removed for export] *)
  hp_disj : (area + 4096 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= area)%Z;
  hp_tid : (0 < bv_unsigned tid < 2 ^ 22)%Z;
  hp_L   : (Z.of_nat (length content) < 65536)%Z;
  (* [comment removed for export] *)
  hp_stack : stack_writable M sp0;
  hp_ra   : cell M (bv_unsigned sp0 - 56) 8 0x28c48;
  hp_f64  : cell M (bv_unsigned sp0 - 64) 8 (bv_unsigned sp0 + 8);
  hp_f72  : cell M (bv_unsigned sp0 - 72) 8 2;
  hp_f80  : cell M (bv_unsigned sp0 - 80) 8 0x13580;
  hp_f88  : cell M (bv_unsigned sp0 - 88) 8 (bv_unsigned sp0 + 32);
  hp_f96  : cell M (bv_unsigned sp0 - 96) 8 0;
  hp_f104 : cell M (bv_unsigned sp0 - 104) 8 0;
  hp_f112 : cell M (bv_unsigned sp0 - 112) 8 0;                (* [comment removed for export] *)
  hp_f120 : cell M (bv_unsigned sp0 - 120) 8 0;                (* [comment removed for export] *)
  (* [comment removed for export] *)
  hp_group : group_writable M gm;
  hp_gmeta : cell M (bv_unsigned gm) 8 (area + 24);
  hp_pm4   : M (Z_to_bv 64 (bv_unsigned gm + 28)) = Some (Z_to_bv 8 0);
  hp_pm3   : M (Z_to_bv 64 (bv_unsigned gm + 29)) = Some (Z_to_bv 8 160);
  hp_pm2   : cell M (bv_unsigned gm + 30) 2 1;
  hp_gzr   : M (Z_to_bv 64 (bv_unsigned gm + 65568)) = Some (Z_to_bv 8 0);
  hp_ge5   : M (Z_to_bv 64 (bv_unsigned gm + 69623)) = Some (Z_to_bv 8 0);
  hp_ge4   : cell M (bv_unsigned gm + 69624) 4 0xfdc;
  hp_gend  : zero_bytes M (bv_unsigned gm + 69628) 4;
  hp_content : rdn RSEGS M (Z_to_bv 64 (bv_unsigned gm + 32)) (length content) = Some content;
  (* [comment removed for export] *)
  hp_marea : forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 4096)%Z ->
               store_ok RSEGS M (Z_to_bv 64 (area + d)) m = true;
  hp_check : cell M area 8 run_secret;                        (* [comment removed for export] *)
  hp_gprev : cell M (area + 24) 8 (area + 24);
  hp_gnext : cell M (area + 32) 8 (area + 24);
  hp_gmem  : cell M (area + 40) 8 (bv_unsigned gm);
  hp_gavail : cell M (area + 48) 4 0;
  hp_gfreed : cell M (area + 52) 4 0;
  hp_gW    : cell M (area + 56) 8 0x11b20;
  (* [comment removed for export] *)
  hp_secret : cell M 0x644e8 8 run_secret;                    (* [comment removed for export] *)
  hp_fmh    : cell M 0x644f8 8 0;
  hp_active : cell M 0x64698 8 (area + 24);
  hp_usage  : cell M 0x64818 8 1;
  hp_seq    : cell M 0x64878 1 1;
  hp_tidc   : cell M 0x44138 4 (bv_unsigned tid);
  hp_errno  : exists e, (0 <= e < 2 ^ 32)%Z /\ cell M 0x4413c 4 e;
  hp_guard  : cell M 0x64450 8 run_guard;                     (* [comment removed for export] *)
  hp_img    : forall lo hi i, In (lo, hi) hdr_img_ranges -> (lo <= i < hi)%Z -> M (Z_to_bv 64 i) = None
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma data_wseg : wseg_ok RSEGS (Z_to_bv 64 0x33000) 208896 = true.
Proof. exact ref_wseg_1c. Qed.  (* [comment removed for export] *)

Lemma data_store_ok : forall M d m, (0 <= d)%Z -> (d + Z.of_nat m <= 208896)%Z ->   (* [comment removed for export] *)
  store_ok RSEGS M (Z_to_bv 64 (0x33000 + d)) m = true.
Proof.
  intros M d m Hd Hm.
  eapply (store_ok_window RSEGS M (Z_to_bv 64 0x33000) _ 208896 m 0x33000 0x66000);
    [reflexivity | vm_cast_no_check (@eq_refl Z 0x66000%Z) | cbn; lia | apply data_wseg | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Header.
  Variables (sp0 p1 gm tid : word) (area : Z) (content : list byte).
  Variables (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs).
  Variables (R0 : bvmap 5 word) (M0 : word -> option byte).
  Hypothesis HP : header_pre sp0 p1 gm tid area content R0 M0.
  Hypothesis Hmap : map_has (vm_maps VM) gm (Z_to_bv 64 69632) = true.

  Let L : Z := Z.of_nat (length content).
  Definition modelh : Model := model_post VM stdin0 fs0 tid.
  #[local] Notation ENVv := (ENVh content) (only parsing).

  (* [comment removed for export] *)
  Definition valsh (e : Z) : list word :=
    [sp0; p1; Z_to_bv 64 area; gm; tid; Z_to_bv 64 L; Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content);
     Z_to_bv 64 e] ++ junk_vals R0 ++ [Z_to_bv 64 run_guard; Z_to_bv 64 run_secret].   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma w2le1_byte : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
  Proof.
    intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
    unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
    rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_sym : exists e, (0 <= e < 2 ^ 32)%Z /\
    regs_ok (ENVh content (valsh e)) sr_H R0 /\ know_ok RSEGS (ENVh content (valsh e)) M0 kn_H.
  Proof.
    destruct HP as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Hsp Hceil Hgm Har Hai Hdj Htid HL Hst
                    Hra Hf64 Hf72 Hf80 Hf88 Hf96 Hf104 Hf112 Hf120
                    Hgr Hgmeta Hpm4 Hpm3 Hpm2 Hgzr Hge5 Hge4 Hgend Hcont Hma Hck Hgp Hgn Hgmm Hgav Hgfr HgW
                    Hsec Hfmh Hact Hus Hseq Htc (e & He & Herr') Hgd Himg].
    pose proof alloc_ceiling_range as ACR. pose proof run_guard_range as RGR. pose proof run_secret_range as RSR.
    exists e. split; [exact He|].
    set (vals := valsh e). set (E := ENVh content vals).
    assert (E0 : ev E 0 = sp0) by reflexivity.
    assert (E1 : ev E 1 = p1) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 area) by reflexivity.
    assert (E3 : ev E 3 = gm) by reflexivity.
    assert (E4 : ev E 4 = tid) by reflexivity.
    assert (E5 : ev E 5 = Z_to_bv 64 L) by reflexivity.
    assert (E8 : ev E 8 = Z_to_bv 64 e) by reflexivity.
    assert (E41 : ev E 41 = Z_to_bv 64 run_guard) by reflexivity.
    assert (E42 : ev E 42 = Z_to_bv 64 run_secret) by reflexivity.
    assert (EJ : forall i, (i < 32)%nat -> ev E (9 + i) = getr R0 (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold E, ENVh, vals, valsh. cbn [ev]. unfold vals_ev.
      change (9 + i)%nat with (length [sp0; p1; Z_to_bv 64 area; gm; tid; Z_to_bv 64 L; Z_to_bv 64 (hdr_b0 content);
                                        Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 e] + i)%nat.
      rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
      unfold junk_vals. rewrite (nth_map_seq (fun i => getr R0 (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
      reflexivity. }
    split.
    - (* [comment removed for export] *)
      apply S0ReadBase.regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_H S0ReadBase.all_regs].
      all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                  unfold J; change (edenot E (EVar (9 + n))) with (ev E (9 + n)%nat); rewrite EJ by lia; reflexivity end).
      all: try (lazymatch goal with |- _ = edenot _ (spx ?k) =>
                  unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0;
                  rewrite Rsp; f_equal; lia end).
      all: try (lazymatch goal with |- _ = edenot _ (gmx ?k) =>
                  unfold gmx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E3;
                  assumption end).
      all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite E1; assumption).
      all: try (change (edenot E (EVar 5)) with (ev E 5); rewrite E5; assumption).
      all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
    - (* [comment removed for export] *)
      pose proof (proj1 Hsp) as Hspr. pose proof (proj2 Hsp) as Hspa.
      cps_destruct Hgm as (Hgm1 & Hgm2 & Hgmal). cps_destruct Har as (Har1 & Har2 & Haral).
      pose proof (u64_range gm) as Ugm. pose proof (u64_range sp0) as Usp. pose proof (u64_range tid) as Utid.
      assert (AX : forall k, (0 <= k <= 4096)%Z -> edenot E (ax k) = Z_to_bv 64 (area + k)).
      { intros k Hk. unfold ax. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite E2.
        rewrite u_small by lia. reflexivity. }
      assert (SPX : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k)).
      { intros k. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite E0. reflexivity. }
      assert (AREA : edenot E area_x = Z_to_bv 64 area).
      { unfold area_x. cbn [edenot]. rewrite AX by lia. rewrite alu_and. unfold v_and.
        rewrite !u_small by lia. rewrite land_pagemask by lia.
        rewrite <- Zplus_mod_idemp_l, Haral. change ((0 + 24) mod 4096)%Z with 24%Z. f_equal. lia. }
      unfold kn_H, kn_Hstack, kn_Hheap, kn_Himage, know_ok. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil.
      all: cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off];
           rewrite ?AREA; rewrite ?AX by lia; rewrite ?SPX; cbn [edenot]; rewrite ?E0, ?E1, ?E2, ?E3, ?E4, ?E5, ?E8, ?E41, ?E42;
           rewrite ?(u_small area) by lia; rewrite ?Z.add_0_r;
           change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite ?Z.add_0_l.
      (* [comment removed for export] *)
      all: try (split; [lia | first [exact Hspa | exact Haral | exact Hgmal]]; fail).
      all: lazymatch goal with
           (* [comment removed for export] *)
           | |- (_ <= _ <= _)%Z => lia
           | |- (_ <= _)%Z \/ (_ <= _)%Z => lia
           (* [comment removed for export] *)
           | |- (0 <= _)%Z /\ (_ <= 2 ^ 64)%Z /\ (forall i, _ -> M0 (Z_to_bv 64 i) = None) =>
               split; [lia|]; split; [lia|]; intros i Hi; (eapply Himg; [ | exact Hi]);
               cbn; repeat (first [left; reflexivity | right])
           | |- _ => idtac
           end.
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ (forall d m, _ -> _ -> store_ok _ _ (Z_to_bv 64 (?B + d)) m = true) =>
                    split; [lia|]; intros d m Hd Hm;
                    first [ replace (B + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia; apply Hst; lia
                          | replace (B + d)%Z with (bv_unsigned gm + d)%Z by lia; apply Hgr; lia
                          | apply Hma; lia
                          | replace (B + d)%Z with (0x33000 + d)%Z by lia; apply data_store_ok; lia ]
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ (forall i, _ -> M0 _ = Some (Z_to_bv 8 0)) =>
                    split; [rewrite ?u_small by lia; lia|]; intros i Hi; rewrite ?u_small in Hi by lia;
                    apply Hgend; lia
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ _ /\ rdn _ _ _ 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 _)) =>
                    split; [lia|]; split; [lia|]; cbn [rdn];
                    first [rewrite Hgzr | rewrite Hge5 | rewrite Hpm4 | rewrite Hpm3]; reflexivity
                end).
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- _ /\ _ /\ rdn _ _ (Z_to_bv 64 ?A) _ = _ =>
                    split; [lia|]; split; [lia|]; unfold cell in *; rewrite ?Z_to_bv_bv_unsigned in *;
                    let try1 H := (lazymatch type of H with rdn _ _ (Z_to_bv 64 ?A2) _ = _ =>
                                     replace A with A2 by lia; exact H end) in
                    first [ exact Hgmeta | try1 Hpm2 | try1 Hra | try1 Hf64 | try1 Hf72 | try1 Hf80 | try1 Hf88 | try1 Hf96 | try1 Hf104 | try1 Hf112 | try1 Hf120
                          | try1 Hgmeta | try1 Hghdr | try1 Hge4 | try1 Hck | try1 Hgp | try1 Hgn | try1 Hgmm
                          | try1 Hgav | try1 Hgfr | try1 HgW | try1 Hsec | try1 Hfmh | try1 Hact | try1 Hus | try1 Hseq
                          | try1 Htc | try1 Herr' | try1 Hgd ]
                end).
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_know_short : forall e, know_ok RSEGS (ENVh content (valsh e)) M0 kn_H ->
    (length content < 6)%nat -> know_ok RSEGS (ENVh content (valsh e)) M0 kn_short.
  Proof.
    intros e HK Hlt. unfold kn_short. apply know_ok_app. split; [exact HK|].
    apply know_ok_cons; [|constructor]. apply krange_intro.
    change (edenot (ENVh content (valsh e)) (EVar 5)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
  Qed.

  Lemma content_byte : forall j, (j < length content)%nat ->
    rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned gm + 32 + Z.of_nat j)) 1%nat
    = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j content (Z_to_bv 8 0))))).
  Proof.
    intros j Hj. pose proof (hp_gm _ _ _ _ _ _ _ _ HP) as Hgm. pose proof (hp_L _ _ _ _ _ _ _ _ HP) as HL. pose proof alloc_ceiling_range as ACR.
    pose proof (hp_content _ _ _ _ _ _ _ _ HP) as Hcont.
    pose proof (rdn_nth RSEGS M0 (length content) _ content j Hcont Hj) as H.
    rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte. exact H.
  Qed.

  Lemma hdr_know_long : forall e, know_ok RSEGS (ENVh content (valsh e)) M0 kn_H ->
    (6 <= length content)%nat -> know_ok RSEGS (ENVh content (valsh e)) M0 kn_long.
  Proof.
    intros e HK Hge. pose proof (hp_gm _ _ _ _ _ _ _ _ HP) as Hgm. pose proof (hp_L _ _ _ _ _ _ _ _ HP) as HL. pose proof alloc_ceiling_range as ACR.
    pose proof (hp_content _ _ _ _ _ _ _ _ HP) as Hcont.
    pose proof (u64_range gm) as Ugm.
    pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
    change (bv_modulus 8) with 256%Z in B0, B1.
    unfold kn_long. apply know_ok_app. split; [exact HK|].
    apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|constructor]]]]].
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 5)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot ev ENVh valsh vals_ev nth app]; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content (valsh e)) 3) with gm.
      change (ev (ENVh content (valsh e)) 6) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0.
      replace (bv_unsigned gm + 32)%Z with (bv_unsigned gm + 32 + Z.of_nat 0)%Z by lia. apply content_byte. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot ev ENVh valsh vals_ev nth app]; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content (valsh e)) 3) with gm.
      change (ev (ENVh content (valsh e)) 7) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1.
      replace (bv_unsigned gm + 33)%Z with (bv_unsigned gm + 32 + Z.of_nat 1)%Z by lia. apply content_byte. lia.
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 6)) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0.
      rewrite u_small by lia. lia.
    - apply krange_intro. change (edenot (ENVh content (valsh e)) (EVar 7)) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1.
      rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fds_std_2 : fd_lookup fds_std (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.

  Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10c71) 31 = Some msg_short.
  Proof. vm_compute. reflexivity. Qed.
  Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x105dd) 31 = Some msg_overrun.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hp_facts :
    ((0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z)
    /\ ((0x66000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= 0x7fffff800000)%Z /\ (bv_unsigned gm mod 4096 = 0)%Z)
    /\ (0 < bv_unsigned tid < 2 ^ 22)%Z /\ (Z.of_nat (length content) < 65536)%Z.
  Proof.
    pose proof alloc_ceiling_range as ACR.
    split; [exact (hp_sp0 _ _ _ _ _ _ _ _ HP)|]. split; [pose proof (hp_gm _ _ _ _ _ _ _ _ HP); lia|].
    split; [exact (hp_tid _ _ _ _ _ _ _ _ HP) | exact (hp_L _ _ _ _ _ _ _ _ HP)].
  Qed.

  (* [comment removed for export] *)
  Definition err_tail_stmt (sr : list expr) (kn : list kentry) : Prop :=
    forall vals R M,
      length vals = 75%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 3 = gm -> vals_ev vals 4 = tid ->
      regs_ok (ENVh content vals) sr R -> know_ok RSEGS (ENVh content vals) M kn ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2bbac) M (seg_rom RSEGS)) modelh)
                 (t_exit (exit_code 2) fs0).

  Ltac err_tail_1 HL P0 P3 P4 HR HK :=
    let GMA := ident:(GMA) in cps_pose hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL);
    pose proof (u64_range gm) as Ugm;
    (* [comment removed for export] *)
    run_block scr0 75%nat;
    (* [comment removed for export] *)
    eapply (rz_munmap RSEGS _ _ _ modelh ECALLW gm 69632);
    [ vm_compute; reflexivity
    | apply is_ecall_ECALLW
    | reflexivity
    | reflexivity
    | regv HR (17 : reg); reflexivity
    | regv HR (10 : reg); cbn [edenot ev ENVh]; exact P3
    | exact GMA
    | regv HR (11 : reg); reflexivity
    | lia
    | change (page_round_up_Z 69632) with 69632%Z; unfold TASK_SIZE; lia   (* [comment removed for export] *)
    | change (page_round_up_Z 69632) with 69632%Z; cbv [m_vmmaps modelh model_post mkModelA m_vm vmst_maps]; exact Hmap
    | ];
    rewrite v_addi_pc4 by lia; change (0x2aed0 + 4)%Z with 0x2aed4%Z;
    change (page_round_up_Z 69632) with 69632%Z.

  Ltac err_tail_2 HL P0 P3 P4 HR HK :=
    let HK2 := fresh "HK2" in let HR2 := fresh "HR2" in
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
      pose proof (know_ok_unfill RSEGS E Mc kn (EVar 3) 0 69632 HK
                    ltac:(apply flat_intro; cbn [edenot ev ENVh]; rewrite ?P3; lia) ltac:(lia)) as HK2;
      let kn' := eval vm_compute in (kn_unfill kn (EVar 3) 0 69632) in
      change (kn_unfill kn (EVar 3) 0 69632) with kn' in HK2
    end;
    unfold adenot, v_addi in HK2; cbn [a_base a_off edenot ev ENVh] in HK2;
    rewrite P3, Z.add_0_r, Z_to_bv_bv_unsigned in HK2;
    clear HK; rename HK2 into HK;
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_set_a0 E sr Rc (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end;
    clear HR; rename HR2 into HR;
    (* [comment removed for export] *)
    run_block scr0 75%nat.

  Ltac err_tail_3 HL P0 P3 P4 HR HK :=
    let Hst := fresh "Hst" in let Ktid := fresh "Ktid" in
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255))
                                                  (m_fs (munmap_model gm (Z_to_bv 64 69632) modelh)))));
    [ | replace (m_fs (munmap_model gm (Z_to_bv 64 69632) modelh)) with fs0 by reflexivity;
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 4)) in exact i) _ HK eq_refl)
        as Ktid; cbn [kentry_ok edenot ev ENVh] in Ktid; rewrite P4 in Ktid
    end;
    exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x441e0), (bv_unsigned tid),
           (Z_to_bv 64 0x648a8), (Z_to_bv 64 0);
    split; [|split; [reflexivity|split; [reflexivity|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        lazymatch type of HK with know_ok _ ?E _ ?kn =>
          pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-192) 144) in exact i)
                        _ _ _ (-192) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVh] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + -192)%Z by lia; exact Hst
      | lit_u; lia
      | lit_u; lia
      | lia
      | lit_u; change (279008 - 168)%Z with 0x44138%Z;
        let Htc := fresh in krd HK 0x44138%Z 4%nat Htc; rewrite Htc; cbn [ev ENVh]; rewrite P4;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK | krd_solve HK | left; repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ].

  Ltac err_tail_tac :=
    intros vals R M HL P0 P3 P4 HR HK;
    err_tail_1 HL P0 P3 P4 HR HK;
    match goal with HR' : regs_ok _ _ _, HK' : know_ok _ _ _ _ |- _ => err_tail_2 HL P0 P3 P4 HR' HK' end;
    match goal with HR' : regs_ok _ _ _, HK' : know_ok _ _ _ _ |- _ => err_tail_3 HL P0 P3 P4 HR' HK' end.

  Lemma err_tail_short : err_tail_stmt srSB0 knSB0.
  Proof. err_tail_tac. Qed.

  Lemma err_tail_overrun : err_tail_stmt srOB0 knOB0.
  Proof. err_tail_tac. Qed.

  (* [comment removed for export] *)
  Ltac usmall_off := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 (bv_unsigned ?x + ?k))] => rewrite (u_small (bv_unsigned x + k)) by lia end.

  (* [comment removed for export] *)
  Ltac stdio_then_tail vals res msg msg_img msg_addr TAIL HL P0 P3 P4 HR HK :=
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
    unfold t_die, W;
    apply (stdio_call_sound vals (blobs_ev [content]) sr kn Rc Mc modelh res [] msg
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) ltac:(vm_compute; reflexivity)));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res];
      try (replace (Z.of_nat (@length byte msg)) with 31%Z by reflexivity); cbn [length Z.of_nat];
    [ cbn [edenot]; lia
    | cbn [edenot]; lit_u; lia   (* [comment removed for export] *)
    | cbn [edenot]; lia
    | cbn [edenot]; lit_u; reflexivity
    | pose proof rw_bytes_max_ge17; lia
    | lia
    | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
      usmall_off; rewrite ?u_small by lia; lia
    | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
      usmall_off; rewrite ?u_small by lia; lia
    | cbn [edenot]; rewrite ?u_small by lia; lia
    | reflexivity
    | cbn [edenot]; replace (@length byte msg) with 31%nat by reflexivity;
      rewrite (kimg_rdn RSEGS (ENVh content vals) _ kn ltac:(let i := kidx kn (is_kimg_cov msg_addr 31) in exact i)
                 _ _ msg_addr 31 HK eq_refl) by (cbn; lia);
      apply msg_img
    | apply fds_std_2
    | reflexivity
    | reflexivity
    | apply t_exit_has_nil
    | clear HR HK;
      let R' := fresh "R" in let M' := fresh "M" in let HR' := fresh "HR" in let HK' := fresh "HK" in
      intros R' M' HR' HK';
      apply (TAIL (vals ++ junk_vals R') R' M');
      [ rewrite length_app, junk_vals_length, HL; reflexivity
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P3
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P4
      | exact HR' | exact HK' ] ]
    end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_short : (length content < 6)%nat ->
    realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x1367c) M0 (seg_rom RSEGS)) modelh) (t_die msg_short fs0).
  Proof.
    intros Hlt. cps_destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_know_short e HK0 Hlt) as HK. clear HK0.
    cps_pose hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    set (vals := valsh e) in *.
    assert (HL : length vals = 43%nat) by (subst vals; unfold valsh; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = tid) by reflexivity.
    clearbody vals.
    (* [comment removed for export] *)
    run_block scr0 43%nat.
    (* [comment removed for export] *)
    stdio_then_tail vals scS msg_short msg_short_img 0x10c71%Z err_tail_short HL P0 P3 P4 HR HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_overrun :
    (6 <= length content)%nat -> (Z.of_nat (length content) < 6 + hdr_cfglen content)%Z ->
    realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x1367c) M0 (seg_rom RSEGS)) modelh) (t_die msg_overrun fs0).
  Proof.
    intros Hge Hov. cps_destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_know_long e HK0 Hge) as HK. clear HK0.
    cps_pose hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    pose proof (hdr_cfglen_range content) as CR. assert (LB : (0 <= L < 65536)%Z) by (unfold L; lia).
    set (vals := valsh e) in *.
    assert (HL : length vals = 43%nat) by (subst vals; unfold valsh; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = tid) by reflexivity.
    assert (P5 : vals_ev vals 5 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    clearbody vals.
    (* [comment removed for export] *)
    run_block scr_taken 43%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. fold cfglen_x. cbn [edenot].
      rewrite (cfglen_val content vals P6 P7). change (ev (ENVh content vals) 5) with (vals_ev vals 5). rewrite P5.
      rewrite alu_add. unfold v_add. cbn [branch_taken]. unfold bv_ltu.
      rewrite (u_small (hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6%Z.
      rewrite !u_small by lia. apply Z.ltb_lt. lia. }
    (* [comment removed for export] *)
    stdio_then_tail vals scO msg_overrun msg_overrun_img 0x105dd%Z err_tail_overrun HL P0 P3 P4 HR HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem header_ok : forall brkv mas (hw : word) K,
    world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned hw) M0 ->
    (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
    (forall R' M', target_pre (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned hw) content R' M' -> M' = M0 ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13850) M' (seg_rom RSEGS)) modelh) K) ->
    realizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x1367c) M0 (seg_rom RSEGS)) modelh) K.
  Proof.
    intros brkv mas hw K W0 Hok HK_T. cps_destruct hdr_sym as (e & He & HR & HK0).
    pose proof (hdr_cfglen_range content) as CR.
    pose proof (hdr_know_long e HK0 ltac:(lia)) as HK. clear HK0.
    cps_pose hp_facts as ((SP & SPA) & (GM1 & GM2 & GMA) & TID & LL).
    pose proof (u64_range gm) as Ugm. assert (LB : (0 <= L < 65536)%Z) by (unfold L; lia).
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
    (* [comment removed for export] *)
    set (cb := fun i : nat => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)))).
    assert (HL : length (valsh e) = 43%nat) by (unfold valsh; rewrite !length_app, junk_vals_length; reflexivity).
    (* [comment removed for export] *)
    pose proof (env_app_regs (valsh e) [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) sr_H R0
                  ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know RSEGS (valsh e) [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) M0 kn_long
                  ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
    clear HR HK.
    set (vals := valsh e ++ [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat]) in *.
    change (Env (vals_ev vals) (blobs_ev [content])) with (ENVh content vals) in HR1, HK1.
    rename HR1 into HR. rename HK1 into HK.
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P5 : vals_ev vals 5 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (PJ23 : vals_ev vals (9 + 23)%nat = getr R0 23) by reflexivity.
    assert (PB41 : vals_ev vals 43 = cb 1%nat).
    { unfold vals. replace 43%nat with (length (valsh e) + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB42 : vals_ev vals 44 = cb 0%nat).
    { unfold vals. replace 44%nat with (length (valsh e) + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB43 : vals_ev vals 45 = cb 2%nat).
    { unfold vals. replace 45%nat with (length (valsh e) + 2)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB44 : vals_ev vals 46 = cb 3%nat).
    { unfold vals. replace 46%nat with (length (valsh e) + 3)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals.
    pose proof (cfglen_val content vals P6 P7) as CV.
    (* [comment removed for export] *)
    assert (CB : forall i, (i < 4)%nat ->
      rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)) 1%nat
      = Some [nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)]).
    { intros i Hi.
      replace (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)%Z
        with (bv_unsigned gm + 32 + Z.of_nat (Z.to_nat (hdr_cfglen content) + 2 + i))%Z by lia.
      rewrite content_byte by lia. rewrite w2le1_byte. reflexivity. }
    (* [comment removed for export] *)
    run_block_keep scr_fall 43%nat.
    all: try (unfold sc_denot; fold cfglen_x).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
              | |- branch_taken _ _ _ = false =>
                  cbn [edenot]; rewrite CV; change (ev (ENVh content vals) 5) with (vals_ev vals 5); rewrite P5;
                  rewrite alu_add; unfold v_add; cbn [branch_taken]; unfold bv_ltu;
                  rewrite (u_small (hdr_cfglen content)) by lia; change (bv_unsigned (Z_to_bv 64 6)) with 6%Z;
                  rewrite !u_small by lia; apply Z.ltb_ge; lia
              end).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
              | |- exists bs, rdn _ _ (adenot _ (SA _ ?k)) 1 = Some bs /\ _ =>
                  let i := eval vm_compute in (Z.to_nat (k - 34)) in
                  eexists; split;
                  [ unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite CV;
                    change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                    rewrite alu_add; unfold v_add;
                    rewrite (u_small (hdr_cfglen content)) by lia; rewrite !u_small by lia;
                    replace (bv_unsigned gm + hdr_cfglen content + k)%Z
                      with (bv_unsigned gm + hdr_cfglen content + 34 + Z.of_nat i)%Z by lia;
                    apply (CB i); lia
                  | lazymatch goal with |- _ = edenot _ (EVar ?n) => change (edenot (ENVh content vals) (EVar n)) with (vals_ev vals n) end;
                    first [rewrite PB41 | rewrite PB42 | rewrite PB43 | rewrite PB44];
                    unfold cb, extz; cbn [lez bytes_le_to_Z Z.shiftl]; rewrite Z.lor_0_r; reflexivity ]
              | |- flat _ (SA _ ?k) _ =>
                  unfold flat, estart, elenZ; cbn [a_base a_off]; fold cfglen_x; cbn [edenot]; rewrite CV;
                  change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                  rewrite alu_add; unfold v_add; rewrite (u_small (hdr_cfglen content)) by lia; rewrite !u_small by lia; lia
              end).
    all: let n := numgoals in idtac "after-block goals:" n.
    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
      lazymatch goal with EQ : Mx = _ |- _ => cbn [mem_denot] in EQ; subst Mx end end.
    apply HK_T; [ | reflexivity ].
    destruct HP as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Hsp Hceil Hgm Har Hai Hdj Htid HLL Hst
                    Hra Hf64 Hf72 Hf80 Hf88 Hf96 Hf104 Hf112 Hf120
                    Hgr Hgmeta Hpm4 Hpm3 Hpm2 Hgzr Hge5 Hge4 Hgend Hcont Hma Hck Hgp Hgn Hgmm Hgav Hgfr HgW
                    Hsec Hfmh Hact Hus Hseq Htc Herr Hgd Himg].
    assert (A38 : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 3) cfglen_x) (ELit 38))
                  = Z_to_bv 64 (bv_unsigned gm + 38 + hdr_cfglen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3.
      rewrite !alu_add. unfold v_add. rewrite (alu_add gm). unfold v_add. rewrite (u_small (hdr_cfglen content)) by lia.
      rewrite (u_small (bv_unsigned gm + hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 38)) with 38%Z. f_equal. lia. }
    assert (APL : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 5) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6)))
                  = Z_to_bv 64 (hdr_paylen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 5) with (vals_ev vals 5); rewrite P5.
      rewrite !alu_add, m_mul. unfold v_add, v_mul. rewrite ?alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
      rewrite (Z.mod_small L), (Z.mod_small (hdr_cfglen content)) by lia.
      change ((-1) mod 2 ^ 64)%Z with 18446744073709551615%Z. change ((-6) mod 2 ^ 64)%Z with 18446744073709551610%Z.
      rewrite Zplus_mod_idemp_l.
      replace (L + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64 + 18446744073709551610)%Z
        with (L + 18446744073709551610 + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64)%Z by lia.
      rewrite Zplus_mod_idemp_r.
      apply (mod_eq_shift _ _ (hdr_cfglen content + 1)); [lia|]. unfold hdr_paylen, L. lia. }
    constructor.
    all: try (regv HR (1 : reg); reflexivity).
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P0. f_equal; lia.
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - regv HR (10 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. reflexivity.
    - regv HR (11 : reg). exact CV.
    - regv HR (12 : reg). exact A38.
    - regv HR (13 : reg). exact APL.
    - regv HR (8 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. reflexivity.
    - regv HR (9 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3. reflexivity.
    - regv HR (18 : reg). exact CV.
    - regv HR (19 : reg). exact A38.
    - regv HR (20 : reg). exact APL.
    - regv HR (21 : reg). change (edenot (ENVh content vals) (EExt true 0 1 (EVar 7))) with (sx8F (vals_ev vals 7)).
      rewrite P7. apply sx8F_val. unfold hdr_b1. lia.
    - regv HR (22 : reg). reflexivity.                                         (* [comment removed for export] *)
    - regv HR (23 : reg). etransitivity; [| exact Rs7]. exact PJ23.                (* [comment removed for export] *)
    - exact Hsp.
    - exact Hceil.
    - unfold L in *. lia.
    - exact Hst.
    - constructor; assumption.
    - exact W0.
    - exact Hcont.
  Qed.

End Header.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_of_defined : forall M (a : Z) (m : nat),
  (0 <= a)%Z -> (a + Z.of_nat m <= 2 ^ 64)%Z ->
  (forall i, (a <= i < a + Z.of_nat m)%Z -> M (Z_to_bv 64 i) <> None) ->
  store_ok RSEGS M (Z_to_bv 64 a) m = true.
Proof.
  intros M a m Ha Hm Hdef. destruct m as [|m]; [reflexivity|].
  apply store_ok_of_all; [rewrite u_small by lia; lia|].
  intros x Hx. rewrite u_small in Hx by lia. unfold wview.
  specialize (Hdef (bv_unsigned x) Hx). rewrite Z_to_bv_bv_unsigned in Hdef.
  destruct (M x); [discriminate | exfalso; apply Hdef; reflexivity].
Qed.

Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof.
  induction l as [|[b k] l IH]; intros a n Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - injection E as -> ->. apply map_has_head.
  - apply map_has_cons. apply IH. exact Hin.
Qed.

(* [comment removed for export] *)

Section Intro.
  Variables (sp0 p1 gm tid : word) (area brkv mas : Z) (hw : word) (content : list byte).
  Variables (Rr : bvmap 5 word) (Mr : word -> option byte) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
  Hypothesis RP : read_post0 sp0 p1 gm content Rr Mr R M.
  Hypothesis W0 : world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned hw) M.
  Hypothesis MF : main_frame (bv_unsigned sp0) M.
  Hypothesis HL : (Z.of_nat (length content) < 65536)%Z.

  Lemma header_pre_intro : header_pre sp0 p1 gm tid area content R M.
  Proof.
    destruct RP as [Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs6 Qs7 Qkeep Qframe Qgrows Qcontent Qstack Qgroup].
    pose proof W0 as W.
    destruct W as [Wsecret Winit Wctr Wfmh Wam Wamc Wamac Wmas Wmah Wmat Wamas Wactive44 Wusage44 Wseq Wbrk
                   Wachk Wanext Wans Wsprev Wsnext Wsmem Wsmsk WsW Warest Wadef Wgmeta Wgaidx Wgpad Wenf Wgtail Wgdef
                   Waal Wgmal Warng Waimg Wgmrng Wdisj Wbrkv Wmasv Wghs Wtid Wtidr Werrno Wself Wcanary Wpagesz Wlock80 Wimg].
    destruct MF as [F1 F2 F3 F4 F5 F6 F7 F8 F9].
    pose proof (u64_range gm) as Ugm. pose proof (u64_range sp0) as Usp.
    cps_destruct Hvsp as (SPlo & SPhi & SPal). unfold sp_window_lo, sp_window_hi in *.
    rewrite ctx_active_44 in Wactive44. rewrite ctx_usage_44 in Wusage44. rewrite W64K_val in WsW.
    unfold ctx_secret, ctx_free_meta_head, ctx_seq, CTX in Wsecret, Wfmh, Wseq.
    (* [comment removed for export] *)
    destruct Wenf as [Pp Pe Pr_ Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. subst Pp Pe Pr_ Pq.
    constructor.
    - exact Qsp. - exact Qgp. - exact Qtp. - exact Qs0. - exact Qs1. - exact Qs2. - exact Qs3. - exact Qs4. - exact Qs5. - exact Qs6. - exact Qs7.
    - split; [lia | exact SPal].
    - exact Hceil.
    - repeat split; first [lia | exact Wgmal].
    - repeat split; first [lia | exact Waal].
    - exact Waimg.
    - exact Wdisj.
    - exact Wtidr.
    - exact HL.
    - exact Qstack.
    - exact F1. - exact F2. - exact F3. - exact F4. - exact F5. - exact F6. - exact F7. - exact F8. - exact F9.
    - exact Qgroup.
    - exact Wgmeta.
    - (* [comment removed for export] *)
      replace (bv_unsigned gm + 28)%Z with (bv_unsigned gm + 16 + 16 * 1 - 4)%Z by lia. exact Pm4.
    - (* [comment removed for export] *)
      replace (bv_unsigned gm + 29)%Z with (bv_unsigned gm + 16 + 16 * 1 - 3)%Z by lia. rewrite Pm3. reflexivity.
    - (* [comment removed for export] *)
      unfold cell. replace (bv_unsigned gm + 30)%Z with (bv_unsigned gm + 16 + 16 * 1 - 2)%Z by lia. rewrite Pm2. reflexivity.
    - (* [comment removed for export] *) replace (bv_unsigned gm + 65568)%Z with (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z by lia. apply Pzr. lia.
    - replace (bv_unsigned gm + 69623)%Z with (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z by lia. apply Pe5. lia.
    - unfold cell. replace (bv_unsigned gm + 69624)%Z with (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z by lia.
      rewrite (Pe4 ltac:(lia)). reflexivity.
    - exact Wgtail.
    - exact Qcontent.
    - (* [comment removed for export] *)
      intros d m Hd Hm. apply store_ok_of_defined; [lia | lia |]. intros i Hi.
      replace i with (area + (i - area))%Z by lia. apply Wadef. lia.
    - exact Wachk.
    - exact Wsprev.
    - exact Wsnext.
    - exact Wsmem.
    - (* [comment removed for export] *)
      unfold cell in *. exact (rdn_firstn RSEGS M 8 _ _ 4 Wsmsk ltac:(lia)).
    - unfold cell in *.
      pose proof (rdn_skipn RSEGS M 8 (Z_to_bv 64 (area + 48)) _ 4 Wsmsk ltac:(lia)) as H4.
      rewrite w_add_nat, u_small in H4 by lia.
      replace (area + 52)%Z with (area + 48 + Z.of_nat 4)%Z by lia. exact H4.
    - exact WsW.
    - exact Wsecret.
    - exact Wfmh.
    - exact Wactive44.
    - exact Wusage44.
    - exact Wseq.
    - exact Wtid.
    - exact Werrno.
    - exact Wcanary.
    - (* [comment removed for export] *)
      intros lo hi i Hin Hi.
      assert (Hc : img_clear M lo hi).
      { apply (proj1 (Forall_forall _ _) Wimg (lo, hi)). clear -Hin.
        unfold hdr_img_ranges in Hin. unfold img_clear_ivs.
        repeat (destruct Hin as [Hin|Hin]; [rewrite <- Hin; cbn; tauto|]). destruct Hin. }
      apply Hc. exact Hi.
  Qed.
End Intro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem header_phase : forall (sp0 p1 gm tid : word) (area brkv mas : Z) (hw : word) (content : list byte)
    (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs)
    (Rr : bvmap 5 word) (Mr : word -> option byte) (R : bvmap 5 word) (M : word -> option byte),
  valid_sp sp0 -> alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z ->
  read_post0 sp0 p1 gm content Rr Mr R M ->
  world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned hw) M ->
  main_frame (bv_unsigned sp0) M ->
  (Z.of_nat (length content) < 65536)%Z ->
  In (gm, Z_to_bv 64 69632) (vm_maps VM) ->
  (forall R' M', target_pre (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned hw) content R' M' -> M' = M ->
      realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13850) M' (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))
                (t_target content fs0)) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1367c) M (seg_rom RSEGS)) (model_post VM stdin0 fs0 tid))
             (t_body04 content fs0).
Proof.
  intros sp0 p1 gm tid area brkv mas hw content VM stdin0 fs0 Rr Mr R M Hvsp Hceil RP W0 MF HL Hin HT.
  pose proof (header_pre_intro sp0 p1 gm tid area brkv mas hw content Rr Mr R M Hvsp Hceil RP W0 MF HL) as HP.
  pose proof (map_has_In _ _ _ Hin) as Hmap.
  pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)) as CR.
  unfold t_body04.
  destruct (MAX_INPUT <=? Z.of_nat (length content))%Z eqn:E1; [apply Z.leb_le in E1; unfold MAX_INPUT in E1; lia|].
  destruct (length content <? 6)%nat eqn:E2.
  - apply Nat.ltb_lt in E2. apply (header_short sp0 p1 gm tid area content VM stdin0 fs0 R M HP Hmap E2).
  - apply Nat.ltb_ge in E2.
    destruct (length content <? 6 + Z.to_nat ((bv_unsigned (nth 0 content (Z_to_bv 8 0)) +
               256 * bv_unsigned (nth 1 content (Z_to_bv 8 0))) mod 32768))%nat eqn:E3.
    + apply Nat.ltb_lt in E3.
      apply (header_overrun sp0 p1 gm tid area content VM stdin0 fs0 R M HP Hmap E2).
      unfold hdr_cfglen, hdr_cfg, hdr_b0, hdr_b1 in *. lia.
    + apply Nat.ltb_ge in E3.
      pose proof (t_body_target content fs0 ltac:(unfold MAX_INPUT; lia) ltac:(unfold hdr_cfg, hdr_b0, hdr_b1; lia)) as TB.
      unfold t_body04 in TB. rewrite E1 in TB.
      replace (length content <? 6)%nat with false in TB by (symmetry; apply Nat.ltb_ge; lia).
      replace (length content <? 6 + Z.to_nat ((bv_unsigned (nth 0 content (Z_to_bv 8 0)) +
               256 * bv_unsigned (nth 1 content (Z_to_bv 8 0))) mod 32768))%nat with false in TB
        by (symmetry; apply Nat.ltb_ge; lia).
      rewrite TB.
      apply (header_ok sp0 p1 gm tid area content VM stdin0 fs0 R M HP brkv mas hw _ W0); [|exact HT].
      unfold hdr_cfglen, hdr_cfg, hdr_b0, hdr_b1 in *. lia.
Qed.
End ACeilS2.

End S7Header.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre S7Header.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Local Open Scope bv_scope.
#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section ACeilS3. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Theorem header_phase : forall (sp0 p1 gm tid : word) (area brkv mas : Z) (hw : word) (content : list byte)
    (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs)
    (Rr : bvmap 5 word) (Mr : word -> option byte) (R : bvmap 5 word) (M : word -> option byte),
  valid_sp sp0 -> alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z ->
  read_post0 sp0 p1 gm content Rr Mr R M ->
  world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned hw) M ->
  main_frame (bv_unsigned sp0) M ->
  (Z.of_nat (length content) < 65536)%Z ->
  In (gm, Z_to_bv 64 69632) (vm_maps VM) ->
  (forall R' M', target_pre (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned hw) content R' M' -> M' = M ->
      realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13850) M' (seg_rom RSEGS))
                             (model_post VM stdin0 fs0 tid)) (t_target content fs0)) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1367c) M (seg_rom RSEGS))
                          (model_post VM stdin0 fs0 tid)) (t_body04 content fs0).
Proof. exact S7Header.header_phase. Qed.

End ACeilS3.
End S0LeafHeader.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0MemcpyBase U.S0Memcpy. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x.
From Stdlib Require String.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0MainEntryN U.S0ReadErr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require RefNodesDir RefLayout MallocDefs U.S0EnframeBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymXfer SymAbove. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0W65x.
Module S0LeafDir.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.





Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.






Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd.   (* [comment removed for export] *)

(* [comment removed for export] *)

Import SymHide.OptIn.
(* [comment removed for export] *)
Local Ltac SymHide.sc_cands ::= constr:((OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.kn_exec, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srA, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knA, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srB0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srB, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knB, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knB2, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srC0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srC, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knC, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knD0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srD0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srD, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knD, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srD2, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knD2, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srE0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srE, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knE, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srF0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srF, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knF, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srG0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knG0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srG, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knG, (S0W65x.S7W65_defs.knW0, (S0W65x.S7W65_defs.srW0, (S0W65x.S7W65_defs.srW1, (S0W65x.S7W65_defs.knW1, (S0W65x.S7W65_defs.srK0, (S0W65x.S7W65_defs.srK1, (S0W65x.S7W65_defs.knK1, (S0W65x.S7W65_defs.knU, (S0W65x.S7W65_defs.srO0, (S0W65x.S7W65_defs.srO1, (S0W65x.S7W65_defs.knO1, (S0W65x.S7W65_defs.srDd1, (S0W65x.S7W65_defs.knDd1, (S0W65x.S7W65_defs.srM, (S0W65x.S7W65_defs.knM, (S0W65x.S7W65_defs.srW2, (S0W65x.S7W65_defs.knW2, (S0W65x.S7W65_defs.srN0, (S0W65x.S7W65_defs.srN, (S0W65x.S7W65_defs.knN, (S0W65x.S7W65_defs.srX0, (S0W65x.S7W65_defs.knX0, (S0W65x.S7W65_defs.srX, (S0W65x.S7W65_defs.knX, (S0W65x.S7W65_defs.knG00, (S0W65x.S7W65_defs.knG0, (S0W65x.S7W65_defs.srG0, (S0W65x.S7W65_defs.srG, (S0W65x.S7W65_defs.knG, (S0W65x.S7W65_defs.knP00, (S0W65x.S7W65_defs.knP0, (S0W65x.S7W65_defs.srP0, (S0W65x.S7W65_defs.srP, (S0W65x.S7W65_defs.knP, (S0W65x.S7W65_defs.srQ0, (S0W65x.S7W65_defs.srQ, (S0W65x.S7W65_defs.knQ, (S0W65x.S7W65_defs.srQX0, (S0W65x.S7W65_defs.knQX0, (S0W65x.S7W65_defs.srQX, (S0W65x.S7W65_defs.knQX, (S0W65x.S7W65_defs.knR0, (S0W65x.S7W65_defs.srR0, (S0W65x.S7W65_defs.srR, (S0W65x.S7W65_defs.knR, (S0W65x.S7W65_defs.srS0, (S0W65x.S7W65_defs.srS, (S0W65x.S7W65_defs.knS, (S0W65x.S7W65_defs.srSX0, (S0W65x.S7W65_defs.knSX0, (S0W65x.S7W65_defs.srSX, (S0W65x.S7W65_defs.knSX, (S0W65x.S7W65_defs.knT00, (S0W65x.S7W65_defs.knT0, (S0W65x.S7W65_defs.srT0, (S0W65x.S7W65_defs.srT, (S0W65x.S7W65_defs.knT, (S0W65x.S7W65_defs.knZ, (S0W65x.S7W65_defs.srZ, (S0W65x.S7W65_defs.knZm, (S0W65x.S7W65_defs.srZm, tt)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Module S7DirFront.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.FileSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ExitBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Exit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MemcpyBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Memcpy OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section DirFront.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv uid hw rnd tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition modelD1 : Model := model1g sp0 tid brk mbase fs0 stdin0 FdDir.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dir_seg2_kont (T : TSet) : Prop :=
    forall vals R M,
      length vals = 38%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 sp0 a0s dot_path envv -> vals_ev vals 2 = p1 sp0 a0s dot_path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV a0s dot_path hw rnd vals) srB0 R -> know_ok RSEGS (ENV a0s dot_path hw rnd vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x30fd4) M (seg_rom RSEGS)) modelD1) T.

  Lemma dot_nonul : ~ In (Z_to_bv 8 0) dot_path.
  Proof. cbn. intros [E|[]]. apply (f_equal bv_unsigned) in E. vm_compute in E. lia. Qed.

  Lemma dir_seg1 : forall KA T,
    open_err_branch sp0 a0s dot_path envv hw rnd tid mem0 brk mbase fs0 stdin0 KA -> dir_seg2_kont T ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x13580) mem0 (seg_rom RSEGS))
                            (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0))
               (t_alt2 KA T).
  Proof.
    intros KA T HKA HT.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s dot_path envv uid hw rnd tid regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s dot_path envv uid hw rnd tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s dot_path envv hw rnd tid regs0) with (ENV a0s dot_path hw rnd (vals0 sp0 a0s dot_path envv tid regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s dot_path envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s dot_path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s dot_path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    cps_destruct (main_str sp0 a0s dot_path envv uid hw rnd tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    assert (ABOVE : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV a0s dot_path hw rnd vals) mem0 _ 0%nat 0x66000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s dot_path envv) (length dot_path + 1) = Some (dot_path ++ [Z_to_bv 8 0])).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply ABOVE.
      pose proof (u64_range (p1 sp0 a0s dot_path envv)). unfold p1 in *. rewrite u_small by lia. lia. }
    (* [comment removed for export] *)
    eapply (rz_openat_dot RSEGS _ _ _ (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0) ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [cbn; lia|]. split; [apply dot_nonul|].
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x30fd0 + 4)%Z with 0x30fd4%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s dot_path hw rnd)))
        with (ENV a0s dot_path hw rnd (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x30fd0 + 4)%Z with 0x30fd4%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0)) with modelD1.
      pose proof (regs_set_a0 (ENV a0s dot_path hw rnd vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      eapply (HT vals); try eassumption.
  Qed.
End DirFront.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7DirFront.

(* [comment removed for export] *)
Module S7DirTail.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntryN OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadErr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Record dir_tail_pre (sp0 p1 : word) (tid g hw : Z) (mem0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := DIR_TAIL_PRE {
  dt_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  dt_gp : getr R 3 = Z_to_bv 64 0x10800;
  dt_tp : getr R 4 = Z_to_bv 64 0x441e0;
  dt_s2 : getr R 18 = p1;                                  (* [comment removed for export] *)
  dt_stack : stack_writable M sp0;
  dt_img : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs;
  dt_tid : cell M 0x44138 4 tid;
  dt_tidr : (0 < tid < 2 ^ 22)%Z;
  dt_self : cell M 0x44118 8 0x44118;
  dt_g : (0 <= g < 2 ^ 64)%Z;
  dt_hw : (0 <= hw < 2 ^ 64)%Z;
  dt_canary : cell M 0x64450 8 g;
  dt_pagesz : cell M 0x644a0 8 4096;
  dt_hwcap : cell M 0x644d8 8 hw;
  dt_above : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a
}.

Section DirTail.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv uid hw rnd tid regs0 mem0.

  Theorem dir_tail : forall (g hwv : Z) (R : bvmap 5 word) (M : word -> option byte) (model : Model),
    m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) g hwv mem0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x137ac) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
  Proof.
    intros g hwv R M model Hh Hlazy Hfd2 P.
    destruct P as [Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself Hg Hhw Mcanary Mpagesz Mhwcap Habove].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    edestruct (main_strN sp0 [a0s; dot_path] envv uid hw rnd tid regs0 mem0 Hva Hve Hvsp ME 1%nat) as (Sr & Slo & Shi & Slen & t8 & Ht8);
      [cbn; lia|].
    cbn [nth length Nat.add dot_path app] in Sr, Slo, Shi, Ht8.
    set (pp := p1 sp0 a0s dot_path envv) in *.
    change (cat_argv_ptr sp0 [a0s; dot_path] envv 1) with pp in Sr, Slo, Shi, Ht8.
    change (Z.of_nat 1) with 1%Z in Ht8.
    pose proof (u64_range pp) as Hppr.
    assert (Hstr : rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0]).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia. }
    assert (Ht8' : rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8).
    { rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove.
      rewrite (u_small (bv_unsigned pp + 1)) by lia. rewrite u_small by lia. lia. }
    apply (ref_read_error_dot sp0 [] model Hvsp Hh Hlazy Hfd2 pp (bv_unsigned tid) R M
             Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself g hwv Hg Hhw Mcanary
             Mpagesz Mhwcap Slo t8 ltac:(lia) Hstr Ht8').
  Qed.
End DirTail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7DirTail.

(* [comment removed for export] *)
Module S7DirMid.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.MiniExec.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.FileSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodesDir OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MallocDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0EnframeBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadErr S7DirTail.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymXfer OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymAbove OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S7W65_defs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S7W65 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S7W65m OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.S0WorldVM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition DFUEL : nat := 5000.
Definition DSTOPS : list Z := [0x137ac; 0x306ac; 0x13828; 0x29508; 0x291c0]%Z.
Definition dscr0 : scripts := SCR [] [] [].
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen DFUEL DSTOPS scr NX true.

(* [comment removed for export] *)
Definition kn_cells : list kentry :=
  [KWr (SA (ELit 0) 0x33000) 0x33000;
   KWord (SA (ELit 0) 0x44138) 4 (EVar 4);          (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x44118) 8 (ELit 0x44118);     (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x64450) 8 (EVar 40);         (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x644a0) 8 (ELit 4096);        (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x644d8) 8 (EVar 41)].         (* [comment removed for export] *)
Definition kn_img : list kentry := map (fun iv => KImg (fst iv) (snd iv)) re_ivs.
Definition kn_D0 : list kentry := Eval vm_compute in (kn_RE 1 4194303 ++ kn_cells ++ kn_img).
(* [comment removed for export] *)
Local Ltac SymHide.sc_cands ::= constr:((OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.kn_exec, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srA, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knA, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srB0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srB, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knB, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knB2, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srC0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srC, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knC, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knD0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srD0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srD, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knD, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srD2, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knD2, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srE0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srE, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knE, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srF0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srF, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knF, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srG0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knG0, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.srG, (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs.knG, (S0W65x.S7W65_defs.knW0, (S0W65x.S7W65_defs.srW0, (S0W65x.S7W65_defs.srW1, (S0W65x.S7W65_defs.knW1, (S0W65x.S7W65_defs.srK0, (S0W65x.S7W65_defs.srK1, (S0W65x.S7W65_defs.knK1, (S0W65x.S7W65_defs.knU, (S0W65x.S7W65_defs.srO0, (S0W65x.S7W65_defs.srO1, (S0W65x.S7W65_defs.knO1, (S0W65x.S7W65_defs.srDd1, (S0W65x.S7W65_defs.knDd1, (S0W65x.S7W65_defs.srM, (S0W65x.S7W65_defs.knM, (S0W65x.S7W65_defs.srW2, (S0W65x.S7W65_defs.knW2, (S0W65x.S7W65_defs.srN0, (S0W65x.S7W65_defs.srN, (S0W65x.S7W65_defs.knN, (S0W65x.S7W65_defs.srX0, (S0W65x.S7W65_defs.knX0, (S0W65x.S7W65_defs.srX, (S0W65x.S7W65_defs.knX, (S0W65x.S7W65_defs.knG00, (S0W65x.S7W65_defs.knG0, (S0W65x.S7W65_defs.srG0, (S0W65x.S7W65_defs.srG, (S0W65x.S7W65_defs.knG, (S0W65x.S7W65_defs.knP00, (S0W65x.S7W65_defs.knP0, (S0W65x.S7W65_defs.srP0, (S0W65x.S7W65_defs.srP, (S0W65x.S7W65_defs.knP, (S0W65x.S7W65_defs.srQ0, (S0W65x.S7W65_defs.srQ, (S0W65x.S7W65_defs.knQ, (S0W65x.S7W65_defs.srQX0, (S0W65x.S7W65_defs.knQX0, (S0W65x.S7W65_defs.srQX, (S0W65x.S7W65_defs.knQX, (S0W65x.S7W65_defs.knR0, (S0W65x.S7W65_defs.srR0, (S0W65x.S7W65_defs.srR, (S0W65x.S7W65_defs.knR, (S0W65x.S7W65_defs.srS0, (S0W65x.S7W65_defs.srS, (S0W65x.S7W65_defs.knS, (S0W65x.S7W65_defs.srSX0, (S0W65x.S7W65_defs.knSX0, (S0W65x.S7W65_defs.srSX, (S0W65x.S7W65_defs.knSX, (S0W65x.S7W65_defs.knT00, (S0W65x.S7W65_defs.knT0, (S0W65x.S7W65_defs.srT0, (S0W65x.S7W65_defs.srT, (S0W65x.S7W65_defs.knT, (S0W65x.S7W65_defs.knZ, (S0W65x.S7W65_defs.srZ, (S0W65x.S7W65_defs.knZm, (S0W65x.S7W65_defs.srZm, (kn_cells, (kn_img, (kn_D0, tt))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Lemma kn_D0_eq : kn_D0 = kn_RE 1 4194303 ++ kn_cells ++ kn_img.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_26e58 : fetch_word RSEGS (Z_to_bv 64 0x30fd0) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

Lemma know_of_img_clear : forall E M ivs,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) ivs ->
  forallb (fun iv => Z.leb 0 (fst iv) && Z.leb (snd iv) (2 ^ 64)) ivs = true ->
  know_ok RSEGS E M (map (fun iv => KImg (fst iv) (snd iv)) ivs).
Proof.
  intros E M ivs H Hb. unfold know_ok. rewrite Forall_map. rewrite forallb_forall in Hb.
  apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as Hc.
  specialize (Hb _ Hin). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [kentry_ok fst snd] in *. split; [exact H1|]. split; [exact H2|]. exact Hc.
Qed.

Lemma kword_of_cell : forall E M a n v,
  cell M a n v -> (n <= 8)%nat -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  kentry_ok RSEGS E M (KWord (SA (ELit 0) a) n (ELit v)).
Proof.
  intros E M a n v Hc Hn H0 H64. cbn [kentry_ok edenot]. split; [exact Hn|].
  split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
  rewrite adenot_lit0. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma kword_of_cell_var : forall E M a n v i,
  cell M a n v -> ev E i = Z_to_bv 64 v -> (n <= 8)%nat -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  kentry_ok RSEGS E M (KWord (SA (ELit 0) a) n (EVar i)).
Proof.
  intros E M a n v i Hc Hi Hn H0 H64. cbn [kentry_ok edenot]. split; [exact Hn|].
  split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
  rewrite adenot_lit0, Hi. exact Hc.
Qed.

Section DirMid.
  Context {ACEIL__ : ACeil} {RUNW__ : RunW}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv uid hw rnd tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
  Hypothesis Hguard : run_guard = bv_unsigned (canary_w rnd).         (* [comment removed for export] *)
  Hypothesis Hsec : run_secret = bv_unsigned (secret_word rnd).

  Lemma dot_len : (length dot_path <= 4095)%nat.
  Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition modelDir (VM : VmMaps) : Model :=
    mkModelA (fd_insert fds0 (Z_to_bv 64 3) FdDir) VM stdin0 fs0 None (Some tid) None.

  (* [comment removed for export] *)
  Definition after_malloc_dir (K : TSet) : Prop :=
    forall (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (mb gm : word) (area brkv mas : Z),
      area = (bv_unsigned mb + 4096)%Z ->
      read_pre sp0 (p1 sp0 a0s dot_path envv) mb gm R M ->
      world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned hw) M ->   (* [comment removed for export] *)
      main_frame (bv_unsigned sp0) M ->
      vm_pre VM mb gm -> vm_small VM gm ->
      target_vmx (bv_unsigned sp0) (bv_unsigned gm) area brkv mas VM -> auxv0 (bv_unsigned sp0) M ->   (* [comment removed for export] *)
      above_sp0 sp0 mem0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x135d4) M (seg_rom RSEGS)) (modelDir VM)) K.

  Theorem dir_brk : forall K, after_malloc_dir K ->
    brk_ok_branch_g sp0 a0s dot_path envv hw rnd tid mem0 brk mbase fs0 stdin0 FdDir K.
  Proof.
    intros K AM. exact (brk_ok_sem_g sp0 a0s dot_path envv hw rnd tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hceil Hguard Hsec dot_len FdDir K AM).
  Qed.

  Theorem dir_mmap : forall K, after_malloc_dir K ->
    mmap_ok_branch_g sp0 a0s dot_path envv hw rnd tid mem0 brk mbase fs0 stdin0 FdDir
                     K.
  Proof.
    intros K AM. exact (mmap_ok_sem_g sp0 a0s dot_path envv hw rnd tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hceil Hguard Hsec dot_len FdDir K AM).
  Qed.

  (* [comment removed for export] *)
  Theorem dir_read : forall K,
    (forall R' M' VM', dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) run_guard (bv_unsigned hw) mem0 R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x137ac) M' (seg_rom RSEGS)) (modelDir VM')) K) ->
    after_malloc_dir K.
  Proof.
    intros K TAIL R M VM mb gm area brkv mas EA RP W MF VP VS VX AX HA.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    pose proof (rp_gm _ _ _ _ _ _ RP) as Hgm. pose proof (rp_p1 _ _ _ _ _ _ RP) as Hp1.
    set (p1v := p1 sp0 a0s dot_path envv) in *.
    (* [comment removed for export] *)
    set (vals := valsr sp0 p1v mb gm (bv_unsigned tid) R ++ [Z_to_bv 64 run_guard; hw]).
    set (E := ENVr vals []).
    assert (HL : length vals = 42%nat) by (subst vals; unfold valsr; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1v) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = tid) by (cbn; apply Z_to_bv_bv_unsigned).
    assert (P40 : vals_ev vals 40 = Z_to_bv 64 run_guard).
    { subst vals. change 40%nat with (length (valsr sp0 p1v mb gm (bv_unsigned tid) R) + 0)%nat. rewrite vals_ev_app_r. reflexivity. }
    assert (P41 : vals_ev vals 41 = hw).
    { subst vals. change 41%nat with (length (valsr sp0 p1v mb gm (bv_unsigned tid) R) + 1)%nat. rewrite vals_ev_app_r. reflexivity. }
    pose proof (env_app_regs (valsr sp0 p1v mb gm (bv_unsigned tid) R) [Z_to_bv 64 run_guard; hw] (blobs_ev [[]]) sr_RE R
                  ltac:(vm_compute; reflexivity)
                  (read_pre_regs sp0 p1v mb gm (bv_unsigned tid) R M [] RP) : regs_ok E sr_RE R) as HR.
    assert (HK : know_ok RSEGS E M kn_D0).
    { rewrite kn_D0_eq. apply know_ok_app. split; [|apply know_ok_app; split].
      - apply (env_app_know RSEGS (valsr sp0 p1v mb gm (bv_unsigned tid) R) [Z_to_bv 64 run_guard; hw] (blobs_ev [[]]) M (kn_RE 1 4194303)
                 ltac:(vm_compute; reflexivity)).
        apply (read_pre_know sp0 p1v mb gm (bv_unsigned tid) R M [] RP); lia.
      - destruct W. unfold kn_cells.
        repeat apply know_ok_cons; try apply Forall_nil.
        + split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite u0, Z.add_0_l.
          eapply (store_ok_window RSEGS M (Z_to_bv 64 0x33000) (Z_to_bv 64 (0x33000 + d)) 208896 m 0x33000 0x66000);
            [reflexivity | vm_cast_no_check (@eq_refl Z 0x66000%Z) | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
        + cbn [kentry_ok edenot]. split; [lia|]. split; [apply flat_intro; cbn [edenot]; rewrite ?u0; lia|].
          rewrite adenot_lit0. change (ev E 4) with (vals_ev vals 4). rewrite P4, <- (Z_to_bv_bv_unsigned 64 tid). exact w_tid.
        + apply kword_of_cell; [exact w_self | lia | lia | cbn; lia].
        + apply (kword_of_cell_var E M _ _ _ 40%nat w_canary); [exact P40 | lia | lia | cbn; lia].
        + apply kword_of_cell; [exact w_pagesz | lia | lia | cbn; lia].
        + apply (kword_of_cell_var E M _ _ _ 41%nat w_lock80); [change (ev E 41) with (vals_ev vals 41); rewrite P41; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | cbn; lia].
      - apply know_of_img_clear; [apply re_ivs_of_world; exact (w_img _ _ _ _ _ _ _ W) | vm_compute; reflexivity]. }
    clearbody vals. subst E.
    (* [comment removed for export] *)
    run_block_keep dscr0 42%nat.
    assert (HA1 : above_sp0 sp0 mem0 M0).
    { lazymatch goal with EQM : M0 = mem_denot ?E ?Mo ?log |- _ =>
        lazymatch type of HK with know_ok _ _ _ ?kn =>
        intros xa Hxa; rewrite EQM, (mem_denot_above_kb RSEGS E M0 Mo kn log 0%nat 0x66000 0x7fff7f800000 xa HK);
          [apply HA, Hxa | vm_compute; reflexivity | lia | cbn [ev ENVr]; pins; lia | cbn [ev ENVr]; pins; lia | lia | lia] end end. }
    clear EQM HA. rename HA1 into HA.
    (* [comment removed for export] *)
    eapply (rz_read_dir_mapped RSEGS R0 (Z_to_bv 64 0x30fd0) M0 (modelDir VM) ECALLW (Z_to_bv 64 3) 65536 K fetch_26e58 is_ecall_ECALLW eq_refl eq_refl).
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
    - reflexivity.
    - regv HR (12 : reg). reflexivity.
    - lia.
    - lia.
    - (* [comment removed for export] *)
      regv HR (11 : reg). cbn [edenot].
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        apply (kwr_store_ok_lit RSEGS E Mc kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x340d9%Z 65536%Z) in exact i) _ _ 0x340d9%Z (Z.to_nat 65536) HK eq_refl);
        [lia | rewrite Z2Nat.id by lia; lia | lia] end.
    - (* [comment removed for export] *)
      regv HR (11 : reg). regv HR (12 : reg). cbn [edenot]. apply access_okb_intro_num. rewrite !u_small by lia. lia.
    - rewrite v_addi_pc4 by lia. change (0x30fd0 + 4)%Z with 0x30fd4%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret EISDIR) (ELit (2 ^ 64 - 21)) HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      clear HR. rename HR2 into HR.
      (* [comment removed for export] *)
      run_block_keep dscr0 42%nat.
      assert (HA2 : above_sp0 sp0 mem0 M1).
      { lazymatch goal with EQM : M1 = mem_denot ?E ?Mo ?log |- _ =>
          lazymatch type of HK with know_ok _ _ _ ?kn =>
          intros xa Hxa; rewrite EQM, (mem_denot_above_kb RSEGS E M1 Mo kn log 0%nat 0x66000 0x7fff7f800000 xa HK);
            [apply HA, Hxa | vm_compute; reflexivity | lia | cbn [ev ENVr]; pins; lia | cbn [ev ENVr]; pins; lia | lia | lia] end end. }
      clear EQM HA.
      change 79788%Z with 0x137ac%Z.
      apply (TAIL R1 M1 VM). constructor.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + kreg HR.
      + unfold stack_writable. lazymatch type of HK with know_ok _ ?E _ ?kn =>
          apply (kwr_window E M1 kn (EVar 0) (-8388608) 8388608 _ HK); [vm_compute; reflexivity | cbn [edenot ev ENVr]; pins; lia] end.
      + lazymatch type of HK with know_ok _ ?E _ ?kn =>
          apply (img_clear_of_know E); apply (kderive_all_sound RSEGS _ M1 kn); [exact HK | vm_compute; reflexivity] end.
      + kcell HK.
      + exact Htid.
      + kcell HK.
      + (* [comment removed for export] *) apply run_guard_range.
      + (* [comment removed for export] *) apply u64_range.
      + kcell HK.
      + kcell HK.
      + kcell HK.
      + exact HA2.
  Qed.
End DirMid.
End S7DirMid.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0World OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM_defs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0W65x.S0PilotOOM S7DirTail S7DirFront S7DirMid.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Open Scope bv_scope.

(* [comment removed for export] *)
Lemma teq_pilot_dir : forall A K : TSet,
  t_eq (t_alt2 A (t_alt2 K K)) (t_alt2 A K).
Proof. intros A K tr. unfold t_alt2. tauto. Qed.

Section LeafDir.
  (* [comment removed for export] *)
  Hypothesis cannot_open_branch : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (uid hw : word) (rnd : EntryDraw) (tid : word)
      (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
    main_entry sp0 [a0s; dot_path] envv uid hw rnd tid regs0 mem0 ->
    open_err_branch sp0 a0s dot_path envv hw rnd tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open dot_path) fs0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ref_dir_path {ACEIL__ : ACeil} {RUNW__ : RunW} : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (uid hw : word) (rnd : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
  (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry sp0 [a0s; dot_path] envv uid hw rnd tid regs0 mem0 -> valid_brk RSEGS brk ->
  alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z ->
  run_guard = bv_unsigned (canary_w rnd) -> run_secret = bv_unsigned (secret_word rnd) ->
  realizes RSEGS (mkCfg (mkst regs0 (0x13580 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; dot_path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir04 dot_path fs0)).
Proof.
  intros sp0 a0s envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits Htid ME Hbrk Hceil Hguard Hsec.
  set (K := t_die (msg_read_error dot_path) fs0).
  assert (AM : after_malloc_dir sp0 a0s envv hw tid mem0 fs0 stdin0 K).
  { apply (dir_read sp0 a0s envv hw rnd tid mem0 fs0 stdin0 Hvsp Htid Hguard). intros R' M' VM' P. subst K.
    change fs0 with (m_fs (modelDir tid fs0 stdin0 VM')).
    apply (dir_tail sp0 a0s envv uid hw rnd tid regs0 mem0 Hva Hve Hvsp ME _ _ R' M' (modelDir tid fs0 stdin0 VM') eq_refl eq_refl eq_refl P). }
  eapply rz_conseq; [ | apply teq_pilot_dir ].
  replace (0x13580 : word) with (Z_to_bv 64 0x13580) by (apply bv_eq; reflexivity).
  change (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; dot_path] envv fs0 stdin0)))
    with (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0).
  apply (dir_seg1 sp0 a0s envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME).
  - apply (cannot_open_branch sp0 a0s envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME).
  - unfold dir_seg2_kont. intros vals R M HL P0 P1 P2 P5 HR HK HA.
    change (modelD1 sp0 tid brk mbase fs0 stdin0) with (model1g sp0 tid brk mbase fs0 stdin0 FdDir).
    apply (oom_seg2 sp0 a0s dot_path envv hw rnd tid mem0 brk mbase fs0 stdin0 Hvsp Hbrk Hceil ltac:(cbn; lia) FdDir
             K
             K
             vals R M
             (dir_brk sp0 a0s envv hw rnd tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hceil Hguard Hsec K AM)
             (dir_mmap sp0 a0s envv hw rnd tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk Hceil Hguard Hsec K AM)
             (fun tr Htr => Htr)
             HL P0 P1 P2 P5 HR HK HA).
Qed.
End LeafDir.
End S0LeafDir.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0GrowStmt U.S0TargetPhase.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Main.S0LeafWorld OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Main.S0LeafHeader OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Main.S0LeafDir OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.S0WorldVM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0GrowStmt OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPhase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Import ListNotations.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit.   (* [comment removed for export] *)
Open Scope bv_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Definition rsegs := Ubsan.M.loaded_segments.
Definition rpc := Ubsan.M.init_pc.
Definition rph := Ubsan.M.phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq.
  split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma teq_pilot : forall A K : TSet,
  t_eq (t_alt2 A (t_alt2 K K)) (t_alt2 A K).
Proof. intros A K tr. unfold t_alt2. tauto. Qed.

(* [comment removed for export] *)

Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_rng_lit : forall (i base : Z) (len : Z),
  (0 <= base < 2 ^ 64)%Z -> (0 <= i < 2 ^ 64)%Z ->
  in_rng (Z_to_bv 64 i) (Z_to_bv 64 base) len <-> (base <= i < base + len)%Z.
Proof.
  intros i base len Hb Hi. unfold in_rng. rewrite !u64_lit by lia. tauto.
Qed.

(* [comment removed for export] *)
Lemma read0_outside : forall (sp0 gm : word) (L i : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  (0x66000 <= bv_unsigned gm)%Z -> (bv_unsigned gm + 69632 <= 0x7fffff800000)%Z ->
  (0 <= L)%Z -> (0 <= i < 2 ^ 64)%Z ->
  ~ (bv_unsigned sp0 - 8388608 <= i < bv_unsigned sp0 - 128)%Z ->
  ~ (bv_unsigned gm + 32 <= i < bv_unsigned gm + 32 + L)%Z ->
  ~ (READ_STAGE <= i < READ_STAGE + 65536)%Z ->
  outside (Z_to_bv 64 i) (read_regions0 sp0 gm L).
Proof.
  intros sp0 gm L i Hsp Hg1 Hg2 HL Hi N1 N2 N3. unfold read_regions0. cbn [outside]. unfold READ_STAGE in *.
  rewrite !in_rng_lit by lia. repeat split; lia.
Qed.

Lemma world0_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid hw : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z -> (alloc_ceiling <= bv_unsigned sp0 - 8388608)%Z ->
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 area (bv_unsigned gm) brkv mas tid hw M0 ->
  world0 area (bv_unsigned gm) brkv mas tid hw M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid hw Hsp Hcl RQ HL W. pose proof alloc_ceiling_range as ACR.
  pose proof (w_area_rng _ _ _ _ _ _ _ W) as Har. pose proof (w_gm_rng _ _ _ _ _ _ _ W) as Hgr. pose proof (w_area_img _ _ _ _ _ _ _ W) as Hai.
  pose proof (w_disj _ _ _ _ _ _ _ W) as Hdj. pose proof (w_grp_def _ _ _ _ _ _ _ W) as Hdef.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr. pose proof (rq_grows _ _ _ _ _ _ _ _ RQ) as Hgw.
  eapply world0_frame; [exact W | |].
  - intros i Hi. apply Hfr. unfold world0_fp in Hi. unfold READ_STAGE in *.
    apply read0_outside; unfold READ_STAGE; lia.
  - intros i Hi. apply Hgw. apply Hdef. exact Hi.
Qed.

Lemma main_frame_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid hw : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z -> (alloc_ceiling <= bv_unsigned sp0 - 8388608)%Z ->
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 area (bv_unsigned gm) brkv mas tid hw M0 ->
  main_frame (bv_unsigned sp0) M0 -> main_frame (bv_unsigned sp0) M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid hw Hsp Hcl RQ HL W MF. pose proof alloc_ceiling_range as ACR.
  pose proof (w_gm_rng _ _ _ _ _ _ _ W) as Hgr.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr.
  eapply main_frame_frame; [lia | lia | | exact MF].
  intros i Hi. apply Hfr. apply read0_outside; unfold READ_STAGE; lia.
Qed.

Lemma auxv0_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid hw : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z -> (alloc_ceiling <= bv_unsigned sp0 - 8388608)%Z ->
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 area (bv_unsigned gm) brkv mas tid hw M0 ->
  auxv0 (bv_unsigned sp0) M0 -> auxv0 (bv_unsigned sp0) M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid hw Hsp Hcl RQ HL W AX. pose proof alloc_ceiling_range as ACR.
  pose proof (w_gm_rng _ _ _ _ _ _ _ W) as Hgr.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr.
  eapply auxv0_agree; [exact AX | | | lia].
  - intros i Hi. apply Hfr. apply read0_outside; unfold READ_STAGE; lia.
  - intros i Hi. apply Hfr. apply read0_outside; unfold READ_STAGE; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition K1351c (data : list byte) (fs0 : Fs) : TSet := t_body04 data fs0.   (* [comment removed for export] *)

Lemma teq_opened : forall path data fs0,
  t_eq (t_alt2 (t_die (msg_cannot_open path) fs0) (t_alt2 (K1351c data fs0) (K1351c data fs0)))
       (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened04 data fs0)).
Proof. intros path data fs0. unfold t_opened04, K1351c. apply teq_pilot. Qed.

(* [comment removed for export] *)

Section FileExists.
  Hypothesis TPH : target_phase_stmt.
  Hypothesis TPKH : big_file_stmt.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rnd tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.          (* [comment removed for export] *)
  Hypothesis Hceil : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
  Hypothesis Hguard : run_guard = bv_unsigned (canary_w rnd).         (* [comment removed for export] *)
  Hypothesis Hsecret : run_secret = bv_unsigned (secret_word rnd).
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : openat_plain_name path = true.   (* [comment removed for export] *)
  Hypothesis Hplen : (length path <= 4095)%nat.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma target_vm_of_small : forall (VM : VmMaps) (mb gm : word) (area : Z),
    area = (bv_unsigned mb + 4096)%Z -> vm_pre VM mb gm -> vm_small VM gm ->
    target_vm (bv_unsigned gm) area VM.
  Proof.
    (intros VM mb gm area Harea; cps_intros (Pr & Pl & Ph & Pf & Pn & Plive & (p & Pin & Pne & Plo & Phi) & Pseps); cps_intros (Vr & Vl & Vn & Vin & Vf & Vs)).
    constructor.
    - exact Vr.
    - rewrite Z_to_bv_bv_unsigned. exact Vin.
    - exists (fst p), (snd p). destruct p as [lo sz]. cbn [fst snd] in *. split; [exact Pin|]. lia.
    - exact Vn.
    - exact Vf.
    - exact Vs.
    - exact Vl.
  Qed.

  Lemma after_malloc_main :
    after_malloc sp0 a0s path envv hw tid fs0 stdin0 (K1351c fdata fs0).
  Proof.
    unfold after_malloc. intros R M VM mb gm area brkv mas Harea RP W MF VP VS VX AX.
    pose proof Hvsp as Hvsp'. cps_destruct Hvsp' as (SPlo & SPhi & SPal).
    unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    unfold K1351c. destruct (Z.ltb_spec0 (Z.of_nat (length fdata)) 65536) as [Hlt|Hge].
    - (* [comment removed for export] *)
      apply (read_k0 sp0 (p1 sp0 a0s path envv) mb gm path fdata VM stdin0 fs0 tid Hfile R M _ RP Hlt).
      intros R' M' RQ.
      pose proof VS as VS'. cps_destruct VS' as (VSr & VSl & VSn & VSin & VSsm & VSsep).
      apply (header_phase sp0 (p1 sp0 a0s path envv) gm tid area brkv mas hw fdata VM stdin0 fs0 R M R' M' Hvsp Hceil RQ).
      + eapply world0_after_read0; [ | | exact RQ | exact Hlt | exact W]; lia.
      + eapply main_frame_after_read0; [ | | exact RQ | exact Hlt | exact W | exact MF]; lia.
      + exact Hlt.
      + exact VSin.
      + intros R'' M'' TP EM. subst M''.
        pose proof (TPH (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned hw)
                      fdata R'' M' VM (model_post VM stdin0 fs0 tid) TP
                      (target_vm_of_small VM mb gm area Harea VP VS) VX
                      (auxv0_after_read0 sp0 (p1 sp0 a0s path envv) gm fdata R M R' M' area brkv mas (bv_unsigned tid) (bv_unsigned hw) ltac:(lia) ltac:(lia) RQ Hlt W AX)
                      (SPSA.std_model_mk VM stdin0 fs0 (Some tid) None)) as X.
        exact X.
    - (* [comment removed for export] *)
      apply (TPKH sp0 (p1 sp0 a0s path envv) mb gm R M area brkv mas (bv_unsigned hw) VM path fdata stdin0 fs0 tid Hfile ltac:(lia) Harea RP W MF VP VS VX AX Hceil).
  Qed.

  Theorem ref_file_exists :
    realizes RSEGS (mkCfg (mkst regs0 (0x13580 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened04 fdata fs0)).
  Proof.
    eapply rz_conseq; [ | apply teq_opened ].
    replace (0x13580 : word) with (Z_to_bv 64 0x13580) by (apply bv_eq; reflexivity).
    apply (oom_pilot sp0 a0s path envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 fdata
             Hva Hve Hvsp Htid ME Hbrk Hceil Hfile Hpne Hpnd Hplen).
    - apply (open_err_branch_cannot_open sp0 a0s path envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME).
    - apply (brk_ok_sem sp0 a0s path envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 fdata
               Hva Hve Hvsp Htid ME Hbrk Hceil Hguard Hsecret Hfile Hpne Hpnd Hplen).
      apply after_malloc_main.
    - apply (mmap_ok_sem sp0 a0s path envv uid hw rnd tid regs0 mem0 brk mbase fs0 stdin0 fdata
               Hva Hve Hvsp Htid ME Hbrk Hceil Hguard Hsecret Hfile Hpne Hpnd Hplen).
      apply after_malloc_main.
    - intros tr Htr. exact Htr.
  Qed.
End FileExists.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem ref_realizes_spec :
  target_phase_stmt -> big_file_stmt ->
  forall sp brk mbase (rnd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    alloc_ceiling = (bv_unsigned sp - 8388608)%Z ->
    run_guard = bv_unsigned (canary_w rnd) -> run_secret = bv_unsigned (secret_word rnd) ->
    realizes rsegs
      (init_config rsegs rpc rph sp brk mbase rnd target_alloc_limit inp)
      (spec04 (in_argv inp) (in_fs inp)).   (* [comment removed for export] *)
Proof.
  intros TPH TPKH sp brk mbase rnd [argv envp ifs0 sin uid0 gid groups net nofile sigmask hwc abt vsz urnd0 tmp0] Hsp Hbrk Hfits Hva Hve Hfs Hceil Hguard Hsecret.
  (* [comment removed for export] *)
  cbn [in_argv in_envp] in *.
  change (in_fs (mkProcInput_full argv envp ifs0 sin uid0 gid groups net nofile sigmask hwc abt vsz urnd0 tmp0)) with (fs_seed_tmp ifs0 tmp0) in *.
  set (stdin0 := mkAmbIn sin uid0 gid groups net nofile sigmask hwc abt vsz urnd0).
  lazymatch goal with
  | |- realizes ?sg (init_config ?a ?b ?c ?d ?e ?f ?g ?h _) ?T =>
      change (realizes sg (init_config a b c d e f g h (mkProcInputA argv envp (fs_seed_tmp ifs0 tmp0) stdin0)) T)
  end.
  set (fs0 := fs_seed_tmp ifs0 tmp0) in *. clearbody fs0. clear ifs0 tmp0.
  change target_alloc_limit with LIM.
  apply ref_startup; rewrite ?in_argv_A, ?in_envp_A, ?in_fs_A; try assumption.
  intros tid regs mem Htid ME. rewrite ?in_argv_A, ?in_envp_A, ?in_uid_A, ?in_hwcap_A in ME.
  cbn [in_argv in_envp in_uid in_hwcap mkProcInputA] in ME.
  set (uid := ia_uid stdin0) in ME. set (hw := ia_hwcap stdin0) in ME.
  destruct argv as [|a0s [|path [|x l]]].
  - apply (ref_usage_w sp [] envp uid hw rnd tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfits). cbn; lia.
  - apply (ref_usage_w sp [a0s] envp uid hw rnd tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfits). cbn; lia.
  - cbn [spec04].
    destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
    + apply (ref_open_fail_toolong_w sp a0s path envp uid hw rnd tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfits Hlong).
    + destruct (list_byte_eqb path []) eqn:Hemp.
      * apply ref_list_byte_eqb_eq in Hemp.
        apply (ref_open_fail_empty_w sp a0s path envp uid hw rnd tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfits Hemp).
      * assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
        destruct (list_byte_eqb path dot_path) eqn:Hdot.
        -- apply ref_list_byte_eqb_eq in Hdot. rewrite Hdot in *.
           apply (ref_dir_path cannot_open_branch sp a0s envp uid hw rnd tid regs mem brk mbase fs0 stdin0 Hva Hve Hsp Hfits Htid ME Hbrk Hceil Hguard Hsecret).
        -- assert (Hnd : path <> dot_path)
             by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
           assert (Hpl : openat_plain_name path = true).
           { apply (valid_argv_str_plain [a0s; path] 0%nat Hva); [cbn; lia|].
             cbn [nth]. lazymatch goal with |- ?x = false => destruct x eqn:Epd; [|reflexivity] end.
             exfalso. apply Hnd. exact (proj1 (path_eqb_eq _ _) Epd). }
           destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
           ++ apply (ref_file_exists TPH TPKH sp a0s path envp uid hw rnd tid regs mem brk mbase fs0 stdin0 data
                       Hva Hve Hsp Htid ME Hbrk Hfits Hceil Hguard Hsecret Hlk Hne Hpl ltac:(lia)).
           ++ apply (ref_open_fail_absent_w sp a0s path envp uid hw rnd tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfits
                       ltac:(lia) Hne Hpl Hlk).
  - apply (ref_usage_w sp (a0s :: path :: x :: l) envp uid hw rnd tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hfits). cbn; lia.
Qed.

End ACeilS1.
