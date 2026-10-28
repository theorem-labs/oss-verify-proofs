(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Import Amb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim ShapeAlg Nodes Hoare ShapeLaws AllocIface PureModel VmLedger.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Kit.
Import V10Kit.V10MallocLayout. Import V10Kit.V10Startup. Import V10Kit.V10StartupDefs. Import V10Kit.V10StartupFacts.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Drv1.
Import V10Drv1.V10MainEntry. Import V10Drv1.V10Open. Import V10Drv1.V10Malloc65536. Import V10Drv1.V10Usage. Import V10Drv1.V10OpenFail. Import V10Drv1.V10OpenFailBranch. Import V10Drv1.V10MainDir. Import V10Drv1.V10FuzzIface. Import V10Drv1.V10MainFile.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import RefLayout ArgvEnv.
Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fx0.

Abbreviation rsegs := Ubsan.M.loaded_segments.
Abbreviation rpc := Ubsan.M.init_pc.
Abbreviation rph := Ubsan.M.phdrs.

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq.
  split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

Section Main.
  Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.

  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = rsegs.
  Hypothesis AL_rom : al_rom = seg_rom rsegs.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2b348.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0x2b208.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x45480.
  Hypothesis AL_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x66000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall (AMB : Amb) sp0 a0s path envv tid regs0 mem0,
      valid_sp sp0 -> valid_argv [a0s; path] -> valid_envp envv ->
      @main_entry AMB sp0 [a0s; path] envv tid regs0 mem0 ->
      forall M, V10Drv1.V10Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  (* [comment removed for export] *)
  Hypothesis FZ : fuzz_call_contract.

  Theorem ref_realizes_spec :
    forall sp brk mbase draw lim (inp : ProcInput),
      valid_sp sp -> valid_brk rsegs brk -> (2 ^ 34 <= lim)%Z ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase draw lim inp Hsp Hbrk Hlim Hva Hve Hfits.
    apply ref_startup; [exact Hsp | exact Hva | exact Hve |].
    intros tid regs mem Htid ME.
    rewrite <- (init_model_C_of (segments_reserved rsegs) brk mbase sp lim inp draw).
    set (AMB := amb_of inp draw) in *.
    remember (in_argv inp) as argv eqn:Eargv. remember (in_envp inp) as envp eqn:Eenvp.
    remember (in_fs inp) as fs0 eqn:Efs0. remember (in_stdin inp) as stdin0 eqn:Estdin0.
    clear Eargv Eenvp Efs0 Estdin0.
    destruct argv as [|a0s [|path [|x l]]].
    - apply (ref_usage_w sp [] envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits). cbn; lia.
    - apply (ref_usage_w sp [a0s] envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits). cbn; lia.
    - cbn [spec].
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      + apply (ref_open_fail_toolong_w sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hlong).
      + destruct (list_byte_eqb path []) eqn:Hemp.
        * apply list_byte_eqb_eq in Hemp.
          apply (ref_open_fail_empty_w sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hemp).
        * assert (Hne : path <> []) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
          destruct (list_byte_eqb path dot_path) eqn:Hdot.
          -- apply list_byte_eqb_eq in Hdot.
             replace (0x1520c : word) with (Z_to_bv 64 0x1520c) by (apply bv_eq; reflexivity).
             apply (ref_dir_path sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hbrk Hlim
                      AL_segs AL_rom AL_malloc AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi); [| | exact Hdot].
             ++ intros z Hz. apply AL_ret. apply ret_ok_even. destruct Hz as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
             ++ apply (AL_env AMB sp a0s path envp tid regs mem Hsp Hva Hve ME).
          -- assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
             destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
             ++ replace (0x1520c : word) with (Z_to_bv 64 0x1520c) by (apply bv_eq; reflexivity).
                apply (ref_file_path sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hbrk Hlim
                         AL_segs AL_rom AL_malloc AL_free AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_ret
                         (AL_env AMB sp a0s path envp tid regs mem Hsp Hva Hve ME) FZ data Hlk Hne Hnd ltac:(lia)).
             ++ apply (ref_open_fail_absent_w sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits
                         ltac:(lia) Hne Hnd Hlk).
    - apply (ref_usage_w sp (a0s :: path :: x :: l) envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits). cbn; lia.
  Qed.
End Main.

(* [comment removed for export] *)
Record pins {AL : AllocLayout} : Prop := Pins {
  p_segs : al_segs = rsegs;
  p_rom : al_rom = seg_rom rsegs;
  p_malloc : al_malloc_pc = Z_to_bv 64 0x2b348;
  p_free : al_free_pc = Z_to_bv 64 0x2b208;
  p_tp : al_gp = Z_to_bv 64 0x45480;
  p_glob : forall a, al_globals a -> (0x65778 <= bv_unsigned a < 0x65b28)%Z;
  p_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x66000)%Z;
  p_errno : forall a, al_errno_slot a -> (0x453dc <= bv_unsigned a < 0x453e0)%Z;
  p_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x66000)%Z;
  p_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x66000)%Z;
  p_hi : (al_image_hi <= 0x66000)%Z;
  p_ret : forall k, ret_ok k -> al_ret_ok k;
  p_thr : (al_mmap_threshold <= 131072)%Z;
  p_env : forall (AMB : Amb) sp0 a0s path envv tid regs0 mem0,
      valid_sp sp0 -> valid_argv [a0s; path] -> valid_envp envv ->
      @main_entry AMB sp0 [a0s; path] envv tid regs0 mem0 ->
      forall M, V10Drv1.V10Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M }.

Theorem ref_realizes_spec_pins {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure} :
  pins -> fuzz_call_contract ->
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) (spec (in_argv inp) (in_fs inp)).
Proof.
  intros [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14] FZ.
  exact (ref_realizes_spec P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P14 FZ).   (* [comment removed for export] *)
Qed.
