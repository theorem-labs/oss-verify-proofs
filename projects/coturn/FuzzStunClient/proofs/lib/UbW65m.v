(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes MmapSim AllocSim FileSim AgentLib SpecConsts SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame UbLibStdioCall Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LibWritev RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbExitBase UbStdioDefs UbExit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbStartup UbMainEntry.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MallocDefs RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbEnframeBase UbEnframe UbReadBase.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbPilotOOM_defs UbPilotOOM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymXfer SymAbove UbW65_defs UbW65.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefNodesX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymAboveX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require AsanCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymDriveLet SymDriveLetUb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveX.run_block_with ::= run_block_with_let_img.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require UbW65m_lits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_sr ::= constr:(UbW65m_lits.LITS_SR).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_lg ::= constr:(UbW65m_lits.LITS_LG).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_kn ::= constr:(UbW65m_lits.LITS_KN).
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_nobignat.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blockW" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX false.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mprotect_len_val : forall (a : word),
  (bv_unsigned a mod 4096 = 0)%Z -> (bv_unsigned a + 12288 < 2 ^ 64)%Z ->
  alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) a)
                   (alu64 ALU_AND (alu64 ALU_ADD a (Z_to_bv 64 12287)) (Z_to_bv 64 18446744073709547520)))
        (Z_to_bv 64 (-4096)) = Z_to_bv 64 4096.
Proof.
  intros a Hal Hb. pose proof (u64_range a) as Ha.
  apply bv_eq. cbn [alu64 alu mul_div].
  rewrite ?bv_add_unsigned, ?bv_and_unsigned, ?bv_mul_unsigned, ?bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z.
  change (18446744073709547520 mod 2 ^ 64)%Z with (2 ^ 64 - 4096)%Z.
  change (12287 mod 2 ^ 64)%Z with 12287%Z. change (4096 mod 2 ^ 64)%Z with 4096%Z.
  rewrite (Z.mod_small (bv_unsigned a + 12287)) by lia.
  rewrite fld_hi by lia.
  destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq].
  replace ((bv_unsigned a + 12287) / 4096)%Z with (q + 2)%Z by (rewrite Hq; lia).
  nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma grant_ok_na_unpack : forall (hint : word) m a n,
  grant_ok_na_pin m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_na_pin in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Section World.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Variable fd3 : FdEntry.
  Variable SI : (word -> option byte) -> Prop.
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path).
  (* [comment removed for export] *)
  #[local] Notation RES := (segments_reserved RSEGS).

  #[local] Notation modelV := (modelV tid fs0 stdin0 fd3).
  #[local] Notation model1V := (model1V sp0 tid brk mbase fs0 stdin0 fd3).

  (* [comment removed for export] *)
  Ltac si_block HSI Rn Mn :=
    lazymatch goal with
    | EQM : ?M' = mem_denot ?E ?Mo ?log, HK : know_ok ?segs ?E ?M' ?kn, HR : regs_ok ?E _ ?R' |- _ =>
        let H := fresh "HSI" in
        assert (H : SI M');
        [ apply (SI_step Mo M'); [| exact HSI]; intros xa Hxa; rewrite EQM;
          apply (mem_denot_above_kbx segs E M' Mo kn log 0%nat 0x58000 0x7fff7f800000 xa HK);
          [ vm_compute; reflexivity | lia | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia | lia ]
        | clear HSI EQM; try clear Mn; rename H into HSI; try rename M' into Mn; try clear Rn; try rename R' into Rn ]
    end.
  Ltac si_fill HSI :=
    lazymatch goal with
    | |- SI (zfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply zfill_out; rewrite ?u64_lit by lia; lia
    | |- SI (unfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply unfill_outside; rewrite ?u64_lit by lia; lia
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma w65_oomQ : forall vals R M VM,
    length vals = 72%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENVv vals) srQ0 R -> know_ok RSEGS (ENVv vals) M knP ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1dc04) M (seg_rom RSEGS)) (modelV VM)) (t_die msg_oom fs0).
  Proof using Hvsp Hplen.
    intros vals R M VM HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block scr0 72%nat.
    oom_stdio_exit HL P0 resQX_eq (mV_fd2 tid fs0 stdin0 fd3 VM) (mV_fs tid fs0 stdin0 fd3 VM).
  Qed.

  (* [comment removed for export] *)
  Lemma w65_oomS : forall vals R M VM,
    length vals = 72%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENVv vals) srS0 R -> know_ok RSEGS (ENVv vals) M knR ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1dbac) M (seg_rom RSEGS)) (modelV VM)) (t_die msg_oom fs0).
  Proof using Hvsp Hplen.
    intros vals R M VM HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block scr0 72%nat.
    oom_stdio_exit HL P0 resSX_eq (mV_fd2 tid fs0 stdin0 fd3 VM) (mV_fs tid fs0 stdin0 fd3 VM).
  Qed.
  Variable K : TSet.

  (* [comment removed for export] *)
  Definition exitT_branch : Prop :=
    forall vals R M VM,
      length vals = 105%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srZm R -> know_ok RSEGS (ENVv vals) M knZm ->
      vm_pre VM sp0 (vals_ev vals 71) (vals_ev vals 72) -> w65_vm VM (vals_ev vals 71) (vals_ev vals 72) -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b14) M (seg_rom RSEGS)) (modelV VM)) K.

  Lemma w65_T : forall vals R M VM,
    exitT_branch ->
    length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srT0 R -> know_ok RSEGS (ENVv vals) M knT0 ->
    vm_pre VM sp0 (vals_ev vals 71) (vals_ev vals 72) -> w65_vm VM (vals_ev vals 71) (vals_ev vals 72) -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1dbac) M (seg_rom RSEGS)) (modelV VM)) K.
  Proof using Hvsp Hbrk Hplen SI_step.
    intros vals R M VM EXIT HL P0 P2 P70 P5 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV] in Kgm.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV] in Kga.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_krange ax) in exact i) _ HK eq_refl)
      as Kar; cbn [kentry_ok edenot ev ENV] in Kar.
    pose proof (know_nth RSEGS _ _ knT0 ltac:(let i := kidx knT0 (is_kdisj ax gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ax gx ev ENV] in Kgd.
    set (gm := vals_ev vals 72) in *. set (av := vals_ev vals 71) in *.
    (* [comment removed for export] *)
    run_block_keep scrG 73%nat.
    { unfold sc_denot. cbn [edenot ev ENV]. apply bt_ne_not. subst gm. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      krdv HK 71%nat 4136%Z 8%nat Hmem; [apply flat_intro; cbn [edenot ev ENV]; fold av; lia|];
      krdv HK 71%nat 4152%Z 8%nat Hmw; [apply flat_intro; cbn [edenot ev ENV]; fold av; lia|];
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kzero_cov gx 9 8) in exact i) _ HK eq_refl) as Kz;
      cbn [kentry_ok] in Kz; unfold elenZ, estart in Kz; cbn [a_base a_off edenot ev ENV] in Kz;
      pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov gx 13 69615) in exact i)
                    _ _ _ 13 (Z.to_nat 69615) HK eq_refl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as Hok;
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 69824 96) in exact i) _ HK eq_refl) as Kimg;
      cbn [kentry_ok] in Kimg
    end.
    fold gm in Kz, Hmem, Hmw, Hok.
    unfold adenot, v_addi in Hmem, Hmw, Hok. cbn [a_base a_off edenot ev ENV] in Hmem, Hmw, Hok.
    fold av in Hmem, Hmw. fold gm in Hok.
    change (bv_unsigned (Z_to_bv 64 69623)) with 69623%Z in Kz.
    assert (EF : efH M (Z_to_bv 64 1) (bv_unsigned av + 4120) (bv_unsigned gm) 72480 0 65536 0 0 69616
                     (bv_unsigned gm + 16) 1).
    { constructor.
      - vm_compute. reflexivity.
      - unfold slot_start, UNIT. lia.
      - vm_compute. reflexivity.
      - pose proof (u64_range av). lia.
      - pose proof (u64_range gm). lia.
      - lia.
      - lia.
      - lia.
      - intros _. vm_compute. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - replace (bv_unsigned av + 4120 + 16)%Z with (bv_unsigned av + 4136)%Z by lia.
        rewrite Hmem. subst gm. rewrite Z_to_bv_bv_unsigned. reflexivity.
      - replace (bv_unsigned av + 4120 + 32)%Z with (bv_unsigned av + 4152)%Z by lia. exact Hmw.
      - replace (bv_unsigned gm + 16 - 4)%Z with (bv_unsigned gm + 9 + 3)%Z by lia. apply (proj2 Kz). lia.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 9 + 4)%Z by lia. apply (proj2 Kz). lia.
      - intros C. exfalso. apply C. reflexivity.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (Z.to_nat (69616 - 1)) with (Z.to_nat 69615) by reflexivity. exact Hok.
      - intros j Hj. unfold SCT. apply (proj2 (proj2 Kimg)). lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x13b14)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x13b14) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned av + 4120)).
    { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      reflexivity. }
    assert (G11 : getr R 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
    assert (G12 : getr R 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity).
    assert (G13 : getr R 13 = Z_to_bv 64 1) by (regv HR (13:reg); reflexivity).
    destruct (enframe_run M (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ EF R (seg_rom RSEGS) (Z_to_bv 64 0x13b14)
                G1 RT G10 G11 G12 G13) as (R2 & Hms & Hkeep & HA0).
    clear RT G1 G10 G11 G12 G13.
    replace (Z_to_bv 64 120860) with (0x1d81c : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    replace (memF M 0 65536 69616 (bv_unsigned gm + 16) 1) with (mem_denot (ENVv vals) M LOGE).
    2:{ unfold memF. cbv delta [mF mE mE1 mD] beta zeta.
        replace (69616 - 4 - 65536 - 16 * 1)%Z with 4060%Z by reflexivity.
        replace (69616 * 0 / 16 + 1)%Z with 1%Z by reflexivity.
        change (1 =? 0)%Z with false. change (4060 =? 0)%Z with false. change (4060 <? 5)%Z with false.
        cbv iota.
        replace (0 + 32 * res_code 4060)%Z with 160%Z by reflexivity.
        replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (bv_unsigned gm + 16 - 2)%Z with (bv_unsigned gm + 14)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 4)%Z with (bv_unsigned gm + 28)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 3)%Z with (bv_unsigned gm + 29)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 2)%Z with (bv_unsigned gm + 30)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z with (bv_unsigned gm + 65568)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z with (bv_unsigned gm + 69623)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z with (bv_unsigned gm + 69624)%Z by lia.
        unfold LOGE. cbn [mem_denot]. unfold adenot. cbn [a_base a_off edenot gx ev ENV]. fold gm. unfold v_addi.
        change (word_to_le_bytes 1 (Z_to_bv 64 160)) with [Z_to_bv 8 160].
        change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
        change (word_to_le_bytes 1 (Z_to_bv 64 224)) with [Z_to_bv 8 224].
        reflexivity. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      pose proof (carry_after RSEGS E MG LOGE kn [] knZm [] _ ltac:(vm_compute; reflexivity)
                    ltac:(cbn [log_flat LOGE]; unfold flat, estart; cbn [a_base a_off edenot gx ev ENV]; fold gm;
                          repeat split; lia)
                    HK ltac:(constructor)) as HK2
    end.
    assert (HSI2 : SI (mem_denot (ENVv vals) M LOGE)).
    { apply (SI_step M); [|exact HSI]. intros xa Hxa.
      apply (mem_denot_above_kbx RSEGS (ENVv vals) _ M knZm LOGE 0%nat 0x58000 0x7fff7f800000 xa HK2);
        [vm_compute; reflexivity | lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia | lia]. }
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr R R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity)
                    HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR.
    set (vals2 := vals ++ junk_vals R2) in *.
    assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q71 : vals_ev vals2 71 = av) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    assert (Q72 : vals_ev vals2 72 = gm) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2.
    pose proof (regs_ok_set_have (ENVv vals2) _ R2 10 _ (EAlu ALU_ADD gx (ELit 32)) HR2 HA0
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot gx ev ENV];
                        rewrite Q72; f_equal; lia) ltac:(discriminate)) as HR3.
    clear HR2.
    lazymatch type of HR3 with regs_ok _ ?sr _ => replace sr with srZm in HR3 by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
    clear HK2 HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HK3.
    change (mem_denot (Env (vals_ev vals) (blobs_ev (blobs0 a0s path))) M LOGE) with (mem_denot (ENVv vals) M LOGE) in HSI2.
    apply (EXIT vals2 R2 _ VM HL2 Q0 Q2 Q70 Q5 HR3 HK3);
      [rewrite Q71, Q72; exact HVM | rewrite Q71, Q72; exact HVS | exact HSI2].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition VMn (a : word) : VmMaps :=
    mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 8192)] brk brk LIM mbase sp0.
  Definition VMp (a : word) : VmMaps :=
    mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0.
  Definition VMt (a gm : word) : VmMaps :=
    mkVmMapsFull RES [(gm, Z_to_bv 64 69632); (a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0.

  Lemma RES_eq' : RES = [(Z_to_bv 64 65536, Z_to_bv 64 12288); (Z_to_bv 64 77824, Z_to_bv 64 73728);
                         (Z_to_bv 64 151552, Z_to_bv 64 4096); (Z_to_bv 64 155648, Z_to_bv 64 204800)].
  Proof using Type. vm_compute. reflexivity. Qed.

  Lemma VMp_grant_exists : forall hint a, exists g, grant_ok hint (modelV (VMp a)) g (page_round_up_Z 69632) = true.
  Proof using path Hvsp Hplen.
    intros hint a. change (page_round_up_Z 69632) with 69632%Z.
    apply grant_exists.
    - rewrite mV_vmmaps. unfold AsanCeil.init_sp_ok. cbn [VMp vm_init_sp]. exact (proj1 Hvsp).
    - lia.
    - rewrite mV_vmmaps. cbn [VMp vm_reserved vm_limit vm_maps]. rewrite ?RES_eq'.
      repeat constructor; cbn [snd]; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps. cbn [VMp vm_reserved vm_limit vm_maps]. rewrite ?RES_eq'.
      cbn [length app Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - apply grant_budget_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. cbn [VMp vm_maps vm_limit live_bytes]. rewrite ?u64_lit by lia. pose proof LIM_ge. lia.
  Qed.

  Lemma VMp_grant : forall hint a g, grant_ok hint (modelV (VMp a)) g 69632 = true ->
    (bv_unsigned g mod 4096 = 0 /\ 0x58000 <= bv_unsigned g /\ bv_unsigned g + 69632 <= bv_unsigned sp0 - 8388608
     /\ (bv_unsigned a + 8192 <= bv_unsigned g \/ bv_unsigned g + 69632 <= bv_unsigned a))%Z.
  Proof using path Htid Hplen.
    intros hint a g Hg.
    destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hce & Hrf & Hlive).
    rewrite mV_vmmaps in Hrf. cbn [VMp vm_reserved vm_maps] in Hrf. rewrite RES_eq' in Hrf.
    rewrite mV_vmmaps in Hce. unfold alloc_top in Hce. cbn [VMp vm_init_sp] in Hce. rewrite stack_max_size_val in Hce.
    unfold page_size in Hal. pose proof (u64_range g) as Hgr. pose proof (u64_range a) as Har.
    assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 12288) Hrf ltac:(cbn [In app]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 155648) (Z_to_bv 64 204800) Hrf ltac:(cbn [In app]; tauto)) as D4.
    pose proof (region_free_In _ _ _ a (Z_to_bv 64 8192) Hrf ltac:(cbn [In app]; tauto)) as D5.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 77824) (Z_to_bv 64 73728) Hrf ltac:(cbn [In app]; tauto)) as D2.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 151552) (Z_to_bv 64 4096) Hrf ltac:(cbn [In app]; tauto)) as D3.
    rewrite Hn in D2, D3. rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D3 by lia.
    rewrite Hn in D1, D4, D5. rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D4 by lia. rewrite !u64_lit in D5 by lia.
    assert (Hg4096 : (4096 <= bv_unsigned g)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned g) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    repeat split; lia.
  Qed.

  Lemma w65_R : forall vals R M,
    exitT_branch ->
    length vals = 72%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    (0x1000 <= bv_unsigned (vals_ev vals 71))%Z -> (bv_unsigned (vals_ev vals 71) + 8192 <= bv_unsigned sp0 - 8388608)%Z ->
    regs_ok (ENVv vals) srR0 R -> know_ok RSEGS (ENVv vals) M knR0 -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1dc04) M (seg_rom RSEGS)) (modelV (VMp (vals_ev vals 71))))
               (t_alt2 (t_die msg_oom fs0) K).
  Proof using Hvsp Htid Hbrk Hplen SI_step.
    intros vals R M EXIT HL P0 P2 P70 P5 Alo Ahi HR HK HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    set (av := vals_ev vals 71) in *.
    (* [comment removed for export] *)
    run_block_keep scr0 72%nat. si_block HSI R M.
    eapply (rz_mmap_anon RSEGS _ _ _ (modelV (VMp av)) ECALLW 69632).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - apply VMp_grant_exists.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x1dba8 + 4)%Z with 0x1dbac%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (w65_oomS vals); [exact HL | exact P0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      intros g Hg. rewrite v_addi_pc4 by lia. change (0x1dba8 + 4)%Z with 0x1dbac%Z.
      change (page_round_up_Z 69632) with 69632%Z in Hg |- *.
      destruct (VMp_grant _ av g Hg) as (Gal & Glo & Ghi & Gdj).
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [g] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [g] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals ++ [g]) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q71 : vals_ev vals2 71 = av) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
      assert (Q72 : vals_ev vals2 72 = g).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      clearbody vals2. clearbody av. clear HL P0 P2 P70 P5 vals. rename HL2 into HL.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENVv vals2) _ _ g gx HR2 ltac:(cbn [edenot gx ev ENV]; exact Q72)) as HR. clear HR2.
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knT00) end.
      { unfold knT00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]].
        - apply kalign_intro; [lia|]. cbn [edenot gx ev ENV]. rewrite Q72. exact Gal.
        - apply krange_intro. cbn [edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax gx ev ENV]. rewrite Q71, Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax gx ev ENV]. rewrite Q0, Q72. lia. }
      clear HK2.
      pose proof (xfer_zfill RSEGS (ENVv vals2) _ knT00 gx 0 g 69632 HK3
                    ltac:(unfold estart; cbn [a_base a_off edenot gx ev ENV]; rewrite Q72; lia)
                    ltac:(lia) ltac:(lia)) as HK.
      clear HK3.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knT0 in HK by (vm_compute; reflexivity) end.
      apply (w65_T vals2 _ _ (VMt av g) EXIT HL Q0 Q2 Q70 Q5 HR HK).
      3:{ si_fill HSI. }
      2:{ rewrite Q71, Q72. unfold w65_vm. cbn [vm_reserved vm_limit vm_maps VMt].
          split; [reflexivity|]. split; [reflexivity|]. left. split; [reflexivity | lia]. }
      rewrite Q71, Q72. pose proof (u64_range av).
      unfold vm_pre, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [VMt VMp vm_reserved vm_limit vm_maps vm_noaccess vm_start_brk vm_brk vm_init_sp].
      assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
      assert (H8 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by (apply u64_lit; lia).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply map_has_head|].
      split.
      { constructor; [cbn [fst snd]; rewrite ?Hn; lia|]. constructor; [|constructor]. cbn [fst snd]. rewrite ?H8. lia. }
      split; [cbn; lia|].
      split; [cbn [live_bytes]; rewrite Hn, H8; lia|].
      split.
      { exists (av, Z_to_bv 64 8192). split; [cbn [In]; tauto|]. cbn [fst snd]. rewrite H8.
        split; [intros Eav; apply (f_equal bv_unsigned) in Eav; lia | lia]. }
      (* [comment removed for export] *)
      constructor; [|constructor; [constructor | constructor]].
      constructor; [|constructor]. unfold UbTargetPre.iv_disjoint. cbn [fst snd]. rewrite Hn, H8. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem mmap_ok_worldV : exitT_branch ->
    mmap_ok_entry sp0 a0s path envv tid brk mbase fs0 stdin0 fd3 SI (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
  Proof using Hvsp Htid Hbrk Hplen SI_step.
    intros EXIT vals R M hint a HL P0 P70 P1 P2 P5 HR HK HSI0 Hg.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    destruct (grant_ok_na_unpack (Z_to_bv 64 0) _ _ _ Hg) as (Hal & Hpos & Hce & Hrf).
    unfold UbW65.model1V in Hrf. rewrite m_vmmaps_C in Hrf. cbn [vm_reserved vm_maps] in Hrf.
    rewrite app_nil_r, RES_eq' in Hrf.
    unfold UbW65.model1V in Hce. rewrite m_vmmaps_C in Hce. unfold alloc_top in Hce. cbn [vm_init_sp] in Hce.
    rewrite stack_max_size_val in Hce. unfold page_size in Hal. pose proof (u64_range a) as Har.
    change (page_round_up_Z 8192) with 8192%Z in Hce, Hrf.
    assert (H8 : bv_unsigned (Z_to_bv 64 8192) = 8192%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 12288) Hrf ltac:(cbn [In app]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 77824) (Z_to_bv 64 73728) Hrf ltac:(cbn [In app]; tauto)) as D2.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 151552) (Z_to_bv 64 4096) Hrf ltac:(cbn [In app]; tauto)) as D3.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 155648) (Z_to_bv 64 204800) Hrf ltac:(cbn [In app]; tauto)) as D4.
    rewrite H8 in D1, D2, D3, D4.
    rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D3 by lia. rewrite !u64_lit in D4 by lia.
    assert (Ha4096 : (4096 <= bv_unsigned a)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    assert (Aimg : (bv_unsigned a + 8192 <= 0x10000 \/ 0x58000 <= bv_unsigned a)%Z) by lia.
    clear D1 D2 D3 D4 Hrf.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [a] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals [a] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
    clear HR HK.
    set (vals2 := vals ++ [a]) in *.
    assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q71 : vals_ev vals2 71 = a).
    { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals2. clear HL P0 P2 P70 P1 P5 vals. rename HL2 into HL.
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2.
    pose proof (regs_set_a0 (ENVv vals2) _ _ a ax HR2 ltac:(cbn [edenot ax ev ENV]; exact Q71)) as HR. clear HR2.
    lazymatch type of HR with regs_ok _ ?sr _ => replace sr with srP0 in HR by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
      assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knP00) end.
    { unfold knP00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]].
      - apply kalign_intro; [lia|]. cbn [edenot ax ev ENV]. rewrite Q71. exact Hal.
      - apply krange_intro. cbn [edenot ax ev ENV]. rewrite Q71. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax ev ENV]. rewrite Q71.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ax ev ENV]. rewrite Q0, Q71. lia. }
    clear HK2.
    pose proof (xfer_unfill RSEGS (ENVv vals2) _ knP00 ax 0 a 8192 HK3
                  ltac:(unfold estart; cbn [a_base a_off edenot ax ev ENV]; rewrite Q71; lia) ltac:(lia) ltac:(lia)) as HK.
    clear HK3.
    lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knP0 in HK by (vm_compute; reflexivity) end.
    change (page_round_up_Z 8192) with 8192%Z.
    change (noaccess_model a (Z_to_bv 64 8192) model1V) with (modelV (VMn a)).
    assert (HSI : SI (unfill a (Z_to_bv 64 8192) M)) by si_fill HSI0. clear HSI0.
    (* [comment removed for export] *)
    run_block_keep scrP 72%nat.
    { unfold sc_denot. cbn [edenot ax ev ENV]. rewrite Q71. apply bt_ne_not. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    eapply (rz_mprotect RSEGS _ _ _ (modelV (VMn a)) ECALLW (Z_to_bv 64 (bv_unsigned a + 4096)) 4096).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ax ev ENV].
      rewrite Q71. reflexivity.
    - unfold page_size. rewrite u64_lit by lia.
      replace (bv_unsigned a + 4096)%Z with (bv_unsigned a + 1 * 4096)%Z by lia. rewrite Z.mod_add by lia. exact Hal.
    - regv HR (11 : reg). cbn [edenot ax ev ENV]. rewrite Q71. apply mprotect_len_val; lia.
    - lia.
    - change (page_round_up_Z 4096) with 4096%Z. unfold two_pow_64. rewrite u64_lit by lia. lia.
    - regv HR (12 : reg). reflexivity.
    - rewrite mV_vmmaps. cbn [VMn vm_noaccess]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps. cbn [VMn vm_maps]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - (* [comment removed for export] *)
      apply mprotect_budget_ok_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. cbn [VMn vm_maps vm_limit live_bytes]. rewrite H8. pose proof LIM_ge. lia.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x1dc00 + 4)%Z with 0x1dc04%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (w65_oomQ vals2); [exact HL | exact Q0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x1dc00 + 4)%Z with 0x1dc04%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
      clear HR. rename HR2 into HR.
      lazymatch type of HR with regs_ok _ ?sr _ => replace sr with srR0 in HR by (vm_compute; reflexivity) end.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_zfill RSEGS E Mc kn ax 4096 (Z_to_bv 64 (bv_unsigned a + 4096)) 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot ax ev ENV]; rewrite Q71, u64_lit by lia; lia)
                      ltac:(lia) ltac:(rewrite u64_lit by lia; lia)) as HK2 end.
      clear HK. rename HK2 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knR0 in HK by (vm_compute; reflexivity) end.
      (* [comment removed for export] *)
      unfold mprotect_model. rewrite mV_vmmaps.
      cbn [VMn vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit].
      rewrite maps_subtract_cons, maps_subtract_nil, app_nil_r.
      rewrite !u64_lit by lia.
      rewrite iv_subtract_suffix by (rewrite ?u64_lit, ?H8 by lia; lia).
      replace (bv_unsigned a + 4096 - bv_unsigned a)%Z with 4096%Z by lia.
      change (with_vmmaps (mkVmMapsFull RES [(a, Z_to_bv 64 8192)] [(a, Z_to_bv 64 4096)] brk brk LIM mbase sp0) (modelV (VMn a)))
        with (modelV (VMp a)).
      rewrite <- Q71.
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      apply (w65_R vals2 _ _ EXIT HL Q0 Q2 Q70 Q5); rewrite ?Q71; [lia | lia | exact HR | exact HK | exact HSI2].
  Qed.
End World.

(* [comment removed for export] *)
Theorem mmap_ok_world_g {AMB : Amb} sp0 a0s path envv tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  exitT_branch sp0 a0s path envv tid brk fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  mmap_ok_branch_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 fd3 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
Proof.
  intros EXIT. exact (mmap_ok_worldV sp0 a0s path envv tid brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen fd3
                        (above_eq sp0 mem0) (above_eq_step sp0 mem0) K EXIT).
Qed.

Theorem mmap_ok_world {AMB : Amb} sp0 a0s path envv tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  exitT_branch sp0 a0s path envv tid brk fs0 stdin0 (FdFile path (Z_to_bv 64 0)) (above_eq sp0 mem0) K ->
  mmap_ok_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K)).
Proof. exact (mmap_ok_world_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen (FdFile path (Z_to_bv 64 0)) K). Qed.
