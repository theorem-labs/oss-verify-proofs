(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics; the argv pointer p1 without the stack pointer; the channel-reader premise of ref_read_error_dot). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail SymCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2ExitBase O2Startup O2StartupDefs O2StartupFacts O2MainEntry O2LibStdioCall O2OpenFail_defs O2OpenFail_tail2 O2Open_defs O2Open O2Oom_defs O2MemPreds O2ReadErr O2Malloc65536 O2DirRead_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS3 scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS3 scr NX true.

(* [comment removed for export] *)
Lemma kimg_clear : forall E M kn lo hi,
  know_ok RSEGS E M kn -> existsb (is_kimg_cov lo (hi - lo)) kn = true -> img_clear M lo hi.
Proof.
  intros E M kn lo hi HK Hex. apply existsb_exists in Hex as (K & Hin & Hc).
  destruct K; try discriminate Hc. cbn [is_kimg_cov] in Hc. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hn).
  intros i Hi. apply Hn. lia.
Qed.

Definition is_kblob_at (a : Z) (K : kentry) : bool :=
  match K with KBlob (SA (ELit 0) k) _ _ => (k =? a)%Z | _ => false end.

Section DirRead.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let ENV := O2Open.ENV a0s path.
  Let model1g := O2Open.model1g sp0 tid brk mbase fs0 stdin0 lim.

  (* [comment removed for export] *)
  Theorem dir_read_error :
    path = dot_path ->
    O2Malloc65536.at_buf sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim FdDir (t_die (msg_read_error path) fs0).
Proof.
    intros Hdot A1 vm1 vals R M HL P0 P1 P2 P5 HI Hlive Hlq Hroom Hvl Htop Hisp Hres HR HK HE.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. destruct HE as [HA HEl].
    unfold model1g, O2Open.model1g. rewrite with_vmmaps_C.
    set (model := mkModelC (O2Open.fds1g FdDir) vm1 stdin0 fs0 None (Some tid) None).
    assert (Hh : m_halted model = None) by reflexivity.
    change (O2Malloc65536.ok_sr) with ok_sr in HR. change (O2Malloc65536.ok_kn) with ok_kn in HK.
    (* [comment removed for export] *)
    run_blk_keep d_scrR0 70%nat.
    assert (HA1 : O2Open.above_sp0 sp0 mem0 M0).
    { intros x Hx. rewrite EQM. rewrite (mem_denot_above (ENV vals) M _ 0%nat 0x6b000);
        [apply HA; exact Hx | vm_compute; reflexivity | cbn [ev ENV O2Open.ENV]; rewrite P0; lia | cbn [ev ENV O2Open.ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x37340) = Some ECALLW) by (vm_compute; reflexivity).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
      assert (A17 : bv_unsigned (getr Rc 17) = 63%Z) by (regv HR (17 : reg); reflexivity);
      assert (A10 : getr Rc 10 = Z_to_bv 64 3) by (regv HR (10 : reg); reflexivity);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x39739) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 65536) by (regv HR (12 : reg); reflexivity)
    end.
    eapply (rz_read_dir_at RSEGS _ _ _ _ model ECALLW (Z_to_bv 64 3));
      [ constructor; reflexivity | exact HF | apply is_ecall_ECALLW | exact A17 | exact A10
      | vm_compute; split; discriminate | reflexivity | rewrite A11, A12; vm_compute; reflexivity | ].
    rewrite v_addi_pc4 by lia. change (0x37340 + 4)%Z with 0x37344%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (regs_set_a0 (ENV vals) sr Rc (errno_ret EISDIR) (ELit (2 ^ 64 - 21)) HR ltac:(apply bv_eq; reflexivity)) as HR1 end.
    clear HR. rename HR1 into HR. change (sr_upd d_srR0 (ridx 10) (ELit (2 ^ 64 - 21))) with d_srR10 in HR.
    (* [comment removed for export] *)
    run_blk_keep scr0 70%nat.
    assert (HA2 : O2Open.above_sp0 sp0 mem0 M1).
    { intros x Hx. rewrite EQM. rewrite (mem_denot_above (ENV vals) M0 _ 0%nat 0x6b000);
        [apply HA1; exact Hx | vm_compute; reflexivity | cbn [ev ENV O2Open.ENV]; rewrite P0; lia | cbn [ev ENV O2Open.ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    subst path.
    destruct (main_str sp0 a0s dot_path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi. pose proof (u64_range (cat_argv_ptr (ed_top a_draw) [a0s; dot_path] envv a_execfn 1)) as Hpr.
    destruct (me_word_after sp0 [a0s; dot_path] envv tid regs0 mem0 ME Hva Hve Hvsp RSEGS 1 ltac:(cbn; lia))
      as (t8 & Hr8).
    cbn [nth] in Hr8. change (Z.of_nat (length dot_path)) with 1%Z in Hr8.
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    eapply (ref_read_error_dot sp0 (blobs0 a0s dot_path) model Hvsp Hh eq_refl eq_refl a_reader
             (p1 a0s dot_path envv) (bv_unsigned tid) Rc Mc) with (t8 := t8) end end.
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV O2Open.ENV].
      rewrite P0. first [reflexivity | f_equal; lia].
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - regv HR (18 : reg). cbn [edenot ev ENV O2Open.ENV]. exact P2.
    - (* [comment removed for export] *)
      intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS (ENV vals) _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-6144513) 6144513) in exact i)
                      _ _ _ (-6144513 + d) m HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst end.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV O2Open.ENV] in Hst. rewrite P0 in Hst.
      replace (bv_unsigned sp0 + (-6144513 + d))%Z with (bv_unsigned sp0 - 6144513 + d)%Z in Hst by lia. exact Hst.
    - (* [comment removed for export] *)
      unfold re_ivs. repeat (apply Forall_cons; [eapply kimg_clear; [exact HK | vm_compute; reflexivity] |]). apply Forall_nil.
    - (* [comment removed for export] *) unfold cell. krd HK 0x49798%Z 4%nat Htc. rewrite Htc. cbn [edenot ev ENV O2Open.ENV]. rewrite P5.
      rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact Htid.
    - unfold cell. krd HK 0x49778%Z 8%nat Hsf. rewrite Hsf. reflexivity.
    - unfold cell. krd HK 0x69af8%Z 8%nat Hpg. rewrite Hpg. reflexivity.
    - cbn. apply (length_guard_bytes a_draw).
    - (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kblob_at 0x69aa8) in exact i) _ HK eq_refl) as KB end.
      cbn [kentry_ok] in KB. destruct KB as (_ & _ & KB). unfold elenZ, estart in KB. cbn [a_base a_off edenot eb ENV O2Open.ENV blobs_ev blobs0 nth] in KB.
      rewrite (u_small 8), (u_small 0) in KB by lia.
      intros i Hi. change (nth 2 (blobs0 a0s dot_path) []) with (guard_bytes a_draw) in Hi |- *.
      rewrite Z.add_0_l in KB. apply KB. rewrite length_guard_bytes in Hi. exact Hi.
    - unfold p1. exact Slo.
    - unfold p1. lia.
    - unfold p1. change (length dot_path + 1)%nat with 2%nat in Sr.
      change ([Z_to_bv 8 46; Z_to_bv 8 0]) with (dot_path ++ [Z_to_bv 8 0]).
      rewrite <- Sr. apply rdn_agree. intros j Hj. cbn in Hj. apply HA2. rewrite u_small by lia. lia.
    - unfold p1. transitivity (rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top a_draw) [a0s; dot_path] envv a_execfn 1) + 1)) 8).
      { apply rdn_agree. intros j Hj. apply HA2. unorm. lia. }
      exact Hr8.
  Qed.
End DirRead.
