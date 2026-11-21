(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Drv/S1Start.v for the budget-premise witness: the same proofs over BudgetWit.SRealizes.srealizes, the released srealizes with a no-allocation-call check at each node; only module paths change. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; the revised stack window). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec ArgvEnv RefLayout ShapeAlg.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit Require Import SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay S1BootCode S1BootDefs S1Boot S1StartInit_defs S1StartInit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Lemma s1b_ok_img : s1b_ok SEGS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rph_img : Plain.M.phdrs = RPH.
Proof. reflexivity. Qed.

(* 08b1429: the stack image ([PropExec.wrap_mem]) and the libc data ([S1Boot.D8]) read the
   launch's whole input, the mmap base and the entry point, so the hand-off record names the
   input [inp] and the mmap base; argv/envp/uid/hwcap are its fields.  The entry point is the
   image's ELF entry 0x6549c ([Plain.M.init_pc]). *)
Definition D_main1 (inp : ProcInput) (sp0 tid : word) (rdraw : EntryDraw) : word -> option byte :=
  apply_runs init_runs (D8 inp sp0 tid rdraw).

Record main_entry (sp0 : word) (rdraw : EntryDraw) (inp : ProcInput) (mbase tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0xcfab0;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x1006b8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argc_w inp;
  me_a0  : getr regs 10 = argc_w inp;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_s2  : getr regs 18 = Z_to_bv 64 0x655e8;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_fits : entry_stack_fits sp0 (in_argv inp) (in_envp inp);
  me_vl  : valid_launch inp;
  me_lau : exists brk, entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp;
  me_mem : exists (J : word -> option byte),
             wfJ sp0 J /\ mem = cmem sp0 (wrap_mem inp mbase RPH (0x6549c : word) sp0 rdraw) J (D_main1 inp sp0 tid rdraw)
}.

Theorem s1_start : forall (P : machine_state -> Model -> Prop),
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
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp rnd inp mbase tid regs mem ->
     P (mkst regs (0x655e8 : word) mem (seg_rom SEGS))
       (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                        (init_model (segments_reserved SEGS) brk mbase sp lim inp)))) ->
  P (cfg_ms (init_config SEGS Plain.M.init_pc
                         Plain.M.phdrs sp brk mbase rnd lim inp))
    (cfg_model (init_config SEGS Plain.M.init_pc
                         Plain.M.phdrs sp brk mbase rnd lim inp)).
Proof.
  intros P P_bwd P_set_tid sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau Hfit HK.
  rewrite rph_img. change Plain.M.init_pc with 0x6549c%N.
  apply (s1_boot SEGS s1b_ok_img P P_bwd P_set_tid sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau).
  intros tid regs mem Htid CE.
  set (model := with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                                (init_model (segments_reserved SEGS) brk mbase sp lim inp))).
  assert (Hh : m_halted model = None) by (unfold model; rewrite with_tid_halted; reflexivity).
  assert (Hlazy : m_vm_lazy model = []) by (unfold model; rewrite with_tid_lazy; reflexivity).
  destruct (ce_mem _ _ _ _ _ _ _ _ CE) as (Jb & s1v & HJb & ->).
  destruct Hsp as (Hlo & Hhi & Hal).
  eapply (start_init_run inp mbase (0x6549c : word) sp rnd Jb Hva Hlo Hhi Hal
            (fun st => P st model) (P_bwd model Hh Hlazy) regs (seg_rom SEGS) s1v tid HJb);
    [ exact (ce_ra _ _ _ _ _ _ _ _ CE) | exact (ce_sp _ _ _ _ _ _ _ _ CE) | exact (ce_gp _ _ _ _ _ _ _ _ CE)
    | exact (ce_tp _ _ _ _ _ _ _ _ CE) | exact (ce_s0 _ _ _ _ _ _ _ _ CE) | exact (ce_s1 _ _ _ _ _ _ _ _ CE)
    | exact (ce_s2 _ _ _ _ _ _ _ _ CE) | exact (ce_s3 _ _ _ _ _ _ _ _ CE)
    | apply (ce_szero _ _ _ _ _ _ _ _ CE); cbn; tauto .. | ].
  intros regs' J' HJ' M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 Mz.
  apply (HK tid regs'); [exact Htid|].
  split; try assumption.
  - exists brk. exact Hlau.
  - exists J'. split; [exact HJ'|]. reflexivity.
Qed.

Theorem s1_startup : forall sp brk mbase rnd lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp rnd inp mbase tid regs mem ->
     srealizes SEGS (mkCfg (mkst regs (0x655e8 : word) mem (seg_rom SEGS))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                              (init_model (segments_reserved SEGS) brk mbase sp lim inp)))) K) ->
  srealizes SEGS (init_config SEGS Plain.M.init_pc
                              Plain.M.phdrs sp brk mbase rnd lim inp) K.
Proof.
  intros sp brk mbase rnd lim inp K Hsp Hva Hve Hvl Hlau Hfit HK.
  change (init_config SEGS Plain.M.init_pc
            Plain.M.phdrs sp brk mbase rnd lim inp)
    with (mkCfg (cfg_ms (init_config SEGS Plain.M.init_pc
                           Plain.M.phdrs sp brk mbase rnd lim inp))
                (cfg_model (init_config SEGS Plain.M.init_pc
                           Plain.M.phdrs sp brk mbase rnd lim inp))).
  apply (s1_start (fun st model => srealizes SEGS (mkCfg st model) K)); try assumption.
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

(* LPS #38: [cat_argv_ptr] is now [top av ev execfn k] -- it is addressed from the
   stack VMA's end, not from [sp] -- and [RefLayout]'s Section discharges the launch
   facts rather than [entry_stack_fits].  So this lemma takes the launch, and the
   bound is derived rather than re-stated: the string area sits inside the block
   ([struct_av_bound]) and the block ends inside the window ([lay_usp_fit], which is
   [entry_launch_ok_va]'s own first conjunct).  [entry_stack_fits] can no longer carry
   it on its own: its 160-byte auxv term is a LOWER bound on Linux's block
   (Run.v:3466), and the revision's auxv is 432 or 464 bytes.
   The premises are fed by [assumption] rather than positionally, so a further move of
   which Section hypotheses these lemmas discharge does not move this call site. *)
Lemma argv_str_fits :
  forall (sp mbase brk : word) (rdraw : EntryDraw) (inp : ProcInput) k,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (k < length (in_argv inp))%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp)
                  (in_execfn inp) k)
   + Z.of_nat (length (nth k (in_argv inp) [])) + 1 <= sp_window_hi)%Z.
Proof.
  intros sp mbase brk rdraw inp k Hsp Hva Hve Hvl Hlau Hk.
  pose proof Hsp as (Hlo & Hhi & _).
  pose proof (u_cat_argv_ptr Sv48 inp mbase RPH (Z_to_bv 64 0) sp brk rdraw) as Hu.
  pose proof (struct_av_bound inp mbase RPH (Z_to_bv 64 0) sp brk rdraw) as Hsa.
  pose proof (lay_usp_fit Sv48 inp mbase RPH (Z_to_bv 64 0) sp brk rdraw) as Htop.
  repeat (lazymatch type of Hu with
          | ?P -> _ => let h := fresh "Hp" in assert (h : P) by assumption;
                       specialize (Hu h); clear h
          end).
  repeat (lazymatch type of Htop with
          | ?P -> _ => let h := fresh "Hp" in assert (h : P) by assumption;
                       specialize (Htop h); clear h
          end).
  rewrite (Hu k Hk).
  pose proof (total_firstn_succ k (in_argv inp) Hk).
  pose proof (Nat.le_0_l (total_arg_bytes_nat (in_envp inp))).
  unfold va_stack_top, sp_window_hi in *. lia.
Qed.

Section Consumers.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Variable inp : ProcInput.
  Variables mbase tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 rdraw inp mbase tid regs mem.

  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH (0x6549c : word) sp0 rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  (* #38, rule 12i: this lemma was FALSE as written and is the single widest claim
     left in the unit.  It promised a store anywhere in [[sp0 - stack_max_size, sp0)]
     -- the whole 8 MiB -- and discharged it with [unfold win_lo; lia] against
     [MemSplit.store_ok_cmem_win], whose second premise the revision narrowed from
     [win_lo sp0 <= a] to [wok_lo sp0 <= a].  At origin/main the unit's own
     MemSplit.v had no [wok_lo] at all and that premise WAS [win_lo], which is why
     the old text was sound then and is not now (the narrowing landed inside the
     revision series at 091615f4, "the 8 MiB stack window counts the entry image,
     as Linux does").  [unfold win_lo; lia] cannot prove
     [sp0 + 2244095 - 8388608 <= a] from [sp0 - 8388608 <= a]: it is short by
     exactly [stack_window_reach] = 2244095 bytes.

     OLD  (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->      (* 8 MiB *)
     NEW  (wok_lo sp0 <= bv_unsigned a)%Z ->                            (* 6144513 *)

     The new premise is exactly the hypothesis [store_ok_cmem_win] asks for, so the
     proof hands it over unchanged instead of trying to widen it.  Free in all five
     kernel fields: [wok_lo] mentions none of kb_rseq/thp/aslr/guard/rnd_bits, and
     neither does [stack_window_reach]; the bound is the same Z for every kernel.
     Every consumer is re-checked in this commit -- the only ones are the [KWr]
     knowledge rows over the stack window, which narrow with it. *)
  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply store_ok_cmem_win; [exact HJ | exact Hlo | exact Hhi].
  Qed.

  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main1 inp sp0 tid rdraw a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main1 inp sp0 tid rdraw) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
