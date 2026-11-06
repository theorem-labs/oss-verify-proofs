(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec ArgvEnv RefLayout ShapeAlg SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay U1BootCode U1BootDefs U1Boot U1StartInit_defs U1StartInit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma u1b_ok_img : u1b_ok SEGS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rph_img : Ubsan.M.phdrs = RPH.
Proof. reflexivity. Qed.

Definition D_main1 (sp0 : word) (av ev : list (list byte)) (hw tid : word) (rdraw : EntryDraw) : word -> option byte :=
  apply_runs init_runs (D8 sp0 av ev hw tid rdraw).

Record main_entry (sp0 : word) (rdraw : EntryDraw) (av ev : list (list byte)) (uid hw tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0xd1808;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x102418;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argc_w av;
  me_a0  : getr regs 10 = argc_w av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x6583c;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte),
             wfJ sp0 J /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw) J (D_main1 sp0 av ev hw tid rdraw);

  me_fits : entry_stack_fits sp0 av ev
}.

Theorem u1_start : forall (P : machine_state -> Model -> Prop),
  (forall model, m_halted model = None -> m_vm_lazy model = [] -> bwd SEGS (fun st => P st model)) ->
  (forall regs (pc : word) mem model w,
    fetch_word SEGS pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 96 -> m_tid model = None ->
    (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       P (mkst (regupd regs 10 tid) (v_addi pc 4) mem (seg_rom SEGS)) (with_tid tid model)) ->
    P (mkst regs pc mem (seg_rom SEGS)) model) ->
  forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) tid regs mem ->
     P (mkst regs (0x6583c : word) mem (seg_rom SEGS))
       (with_tid tid (init_model (segments_reserved SEGS) brk mbase sp lim inp))) ->
  P (cfg_ms (init_config SEGS Ubsan.M.init_pc
                         Ubsan.M.phdrs sp brk mbase rnd lim inp))
    (cfg_model (init_config SEGS Ubsan.M.init_pc
                         Ubsan.M.phdrs sp brk mbase rnd lim inp)).
Proof.
  intros P P_bwd P_set_tid sp brk mbase rnd lim inp Hsp Hva Hve Hfit HK.
  rewrite rph_img. change Ubsan.M.init_pc with 0x656f0%N.
  apply (u1_boot SEGS u1b_ok_img P P_bwd P_set_tid sp brk mbase rnd lim inp Hsp Hva Hve).
  intros tid regs mem Htid CE.
  set (model := with_tid tid (init_model (segments_reserved SEGS) brk mbase sp lim inp)).
  assert (Hh : m_halted model = None) by (unfold model; rewrite with_tid_halted; reflexivity).
  assert (Hlazy : m_vm_lazy model = []) by (unfold model; rewrite with_tid_lazy; reflexivity).
  destruct (ce_mem _ _ _ _ _ _ _ _ _ CE) as (Jb & s1v & HJb & ->).
  destruct Hsp as (Hlo & Hhi & Hal).
  eapply (start_init_run sp rnd Jb (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hva Hlo Hhi Hal
            (fun st => P st model) (P_bwd model Hh Hlazy) regs (seg_rom SEGS) s1v tid HJb);
    [ exact (ce_ra _ _ _ _ _ _ _ _ _ CE) | exact (ce_sp _ _ _ _ _ _ _ _ _ CE) | exact (ce_gp _ _ _ _ _ _ _ _ _ CE)
    | exact (ce_tp _ _ _ _ _ _ _ _ _ CE) | exact (ce_s0 _ _ _ _ _ _ _ _ _ CE) | exact (ce_s1 _ _ _ _ _ _ _ _ _ CE)
    | exact (ce_s2 _ _ _ _ _ _ _ _ _ CE) | exact (ce_s3 _ _ _ _ _ _ _ _ _ CE)
    | apply (ce_szero _ _ _ _ _ _ _ _ _ CE); cbn; tauto .. | ].
  intros regs' J' HJ' M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 Mz.
  apply (HK tid regs'); [exact Htid|].
  split; try assumption.
  exists J'. split; [exact HJ'|]. reflexivity.
Qed.

Theorem u1_startup : forall sp brk mbase rnd lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) tid regs mem ->
     srealizes SEGS (mkCfg (mkst regs (0x6583c : word) mem (seg_rom SEGS))
                           (with_tid tid (init_model (segments_reserved SEGS) brk mbase sp lim inp))) K) ->
  srealizes SEGS (init_config SEGS Ubsan.M.init_pc
                              Ubsan.M.phdrs sp brk mbase rnd lim inp) K.
Proof.
  intros sp brk mbase rnd lim inp K Hsp Hva Hve Hfit HK.
  change (init_config SEGS Ubsan.M.init_pc
            Ubsan.M.phdrs sp brk mbase rnd lim inp)
    with (mkCfg (cfg_ms (init_config SEGS Ubsan.M.init_pc
                           Ubsan.M.phdrs sp brk mbase rnd lim inp))
                (cfg_model (init_config SEGS Ubsan.M.init_pc
                           Ubsan.M.phdrs sp brk mbase rnd lim inp))).
  apply (u1_start (fun st model => srealizes SEGS (mkCfg st model) K)); try assumption.
  - intros model Hh Hlazy st st' Hms Hst'. eapply srz_msteps; eassumption.
  - intros regs pc mem model w HF HE Hh Hlazy H17 Ht Hk.
    eapply srz_set_tid; eassumption.
Qed.

Lemma total_firstn_succ : forall k (l : list (list byte)), (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros [|x l] H; cbn [length] in H; try lia.
  - cbn [firstn nth total_arg_bytes_nat fold_right]. lia.
  - cbn [firstn nth]. change (total_arg_bytes_nat (x :: firstn k l)) with (length x + 1 + total_arg_bytes_nat (firstn k l))%nat.
    change (total_arg_bytes_nat (x :: l)) with (length x + 1 + total_arg_bytes_nat l)%nat.
    pose proof (IH l ltac:(lia)). lia.
Qed.

Lemma argv_str_fits : forall (sp : word) av ev k, valid_sp sp -> valid_argv av -> valid_envp ev ->
  entry_stack_fits sp av ev -> (k < length av)%nat ->
  (bv_unsigned (cat_argv_ptr sp av ev k) + Z.of_nat (length (nth k av [])) + 1 <= sp_window_hi)%Z.
Proof.
  intros sp av ev k (Hlo & Hhi & _) Hva Hve Hfit Hk.
  rewrite (u_cat_argv_ptr RPH sp (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)) av ev (Z_to_bv 64 0) (Z_to_bv 64 0) Hva Hve Hlo Hhi k Hk).
  unfold entry_stack_fits, entry_stack_span in Hfit. pose proof (total_firstn_succ k av Hk).
  rewrite !total_arg_bytes_Z in Hfit. unfold cat_struct_size, auxv_size in *. lia.
Qed.

Section Consumers.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Variables av ev : list (list byte).
  Variables uid hw tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 rdraw av ev uid hw tid regs mem.

  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev uid hw rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main1 sp0 av ev hw tid rdraw a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main1 sp0 av ev hw tid rdraw) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
