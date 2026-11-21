(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: main_open restates bmain_at's new layout parts, with lemmas for the stack span, the hidden bytes, argv[0]'s place and argv's pointer words. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run StackLayout.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prog ProgA ProgZ EquivZA ModelZ ZSafe AsanProgDeps RSim AsanNodeSem AsanOK AsanHandoffBoth.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
Require OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common.Spec.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg AProto.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* LPS 727298f3: [MainEntryBoth.bmain_at]'s body, opened (the block's layout facts per CONFIG_RSEQ value,
   the hidden block bytes against the launch's initial memory, the stack span below sp) *)
Definition main_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  let rseq := kb_rseq (in_kernel inp) in
      ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
                 (Z_to_bv 64 (V 2425%nat)) (Z_to_bv 64 (V 2426%nat)) (Z_to_bv 64 (V 2427%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 2428%nat)) (Z_to_bv 64 (V 2429%nat)) (Z_to_bv 64 (V 2430%nat)) (Z_to_bv 64 (V 2431%nat))
                 (Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 2432%nat)) (Z_to_bv 64 (V 2433%nat)) (Z_to_bv 64 (V 2434%nat)) (Z_to_bv 64 (V 2435%nat)))
            bvmap_empty (Z_to_bv 64 BMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Z.of_nat (block_pad_len rseq (en_sp en) (ed_top (en_draw en)) (in_argv inp) (in_envp inp) (in_execfn inp))
        /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp)
        /\ V 11%nat = Z.of_nat (block_items (in_argv inp) (in_envp inp) mod 2)
        /\ V 12%nat = bv_unsigned (in_gid inp))
    /\ Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w ++ both_mem_facts_l (brz inp))
    /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w ++ both_pure_facts_l (brz inp))
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - STACK_SPAN) usp
    /\ (forall a, hidden_arg en inp a -> m (wa a) = bmem0 en inp (wa a))
    /\ bshadow0 V m
    /\ bmodel V (en_sp en) (in_fs inp) mo.

(* LPS 727298f3: the parts of [main_open] the main phase reads about the launch's block *)
Lemma main_stk : forall en inp w V m ms mo, main_open en inp w V m ms mo ->
  stk bsegs m (bv_unsigned (en_sp en) - STACK_SPAN) (bv_unsigned (en_sp en)).
Proof. intros en inp w V m ms mo (_ & _ & _ & _ & _ & _ & ST & _). exact ST. Qed.

Lemma main_hidden : forall en inp w V m ms mo, main_open en inp w V m ms mo ->
  forall a, hidden_arg en inp a -> m (wa a) = bmem0 en inp (wa a).
Proof. intros en inp w V m ms mo (_ & _ & _ & _ & _ & _ & _ & HID & _). exact HID. Qed.

(* argv[0] sits [launch_string_bytes + 8] below the stack VMA's end, i.e. at InitMem's [str_base] *)
Lemma main_geom : forall sp brk mb dr inp,
  valid_entry (mkImage bsegs b_init_pc b_phdrs) (mkEntry sp brk mb dr) inp -> valid_input_either inp ->
  str0_of (mkEntry sp brk mb dr) inp + Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)) + 8
  = bv_unsigned (ed_top dr).
Proof.
  intros sp brk mb dr inp VE VI. rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE.
  destruct VE as (Hsp & _ & _ & _ & Hlau).
  assert (Hva : valid_argv (in_argv inp))
    by (clear - VI; red in VI; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hve : valid_envp (in_envp inp))
    by (clear - VI; red in VI; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  pose proof (valid_input_either_launch inp VI) as Hlaunch.
  unfold str0_of. cbn [en_sp en_draw].
  eapply AsanInit.str0_hi; try eassumption.
  Unshelve. all: first [exact b_phdrs | exact b_init_pc | exact mb | exact brk].
Qed.

Local Ltac argw_close :=
  match goal with VR1 : 0 <= ?V 1%nat < 2 ^ 64, H0 : bytes_at _ _ _ _, H1 : bytes_at _ _ _ _ |- _ =>
    cbn [zv] in H0, H1;
    split; [| intros HA2;
              replace (1 mod two64 <? V 1%nat mod two64) with true in H1
                by (symmetry; unfold two64 in *; rewrite !Z.mod_small by lia; apply Z.ltb_lt; lia);
              cbn [Z.b2z] in H1 ]
  end;
  match goal with
  | H : bytes_at _ _ ?a (word_to_le_bytes _ (Z_to_bv _ ?x)) |- bytes_at _ _ ?a' (word_to_le_bytes _ (Z_to_bv _ ?x')) =>
      replace a' with a by lia; replace x' with x by lia; exact H
  end.

(* LPS 727298f3: argv's first two pointer words, at sp + 8 and sp + 16, name argv[0]'s string at
   [str0_of] and argv[1]'s right after it (the start state's own facts, [both_mem_facts_l]) *)
Lemma main_argv_words : forall en inp w V m ms mo, main_open en inp w V m ms mo ->
  bytes_at bsegs m (bv_unsigned (en_sp en) + 8) (word_to_le_bytes 8 (Z_to_bv 64 (str0_of en inp)))
  /\ (2 <= Z.of_nat (length (in_argv inp)) ->
      bytes_at bsegs m (bv_unsigned (en_sp en) + 16)
        (word_to_le_bytes 8 (Z_to_bv 64 (str0_of en inp + Z.of_nat (length (nth 0 (in_argv inp) [])) + 1)))).
Proof.
  intros en inp w V m ms mo (_ & VR & PIN & HMF & _).
  destruct PIN as (P0 & P6 & P10 & USP & P1 & P2 & P3 & P7 & P4 & P5 & P8 & P9 & P11 & P12).
  apply Forall_app in HMF as [_ HMF]. apply Forall_app in HMF as [_ HL].
  unfold both_mem_facts_l in HL. apply Forall_cons_iff in HL as [H0 HL]. apply Forall_cons_iff in HL as [H1 _].
  cbn [mfact_ok] in H0, H1. rewrite !zv_mkaddr in H0, H1.
  pose proof (head_len_eq (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) as HLE.
  unfold head_len, gap_len, Lib.InitMem.argc, Lib.InitMem.envc in HLE.
  pose proof (VR 1%nat) as VR1.
  let ev := eval vm_compute in sp0_z in change sp0_z with ev in H0, H1.
  unfold str0_of.
  destruct (brz_cases inp) as [[Er Ea] | [Er Ea]]; rewrite Ea in H0, H1; rewrite Er in *.
  - change (auxv_count false) with 27%nat in HLE.
    let v0 := eval vm_compute in (str0_z 0) in change (str0_z 0) with v0 in H0.
    let v1 := eval vm_compute in (argv1_z 0) in change (argv1_z 0) with v1 in H1.
    argw_close.
  - change (auxv_count true) with 29%nat in HLE.
    let v0 := eval vm_compute in (str0_z 1) in change (str0_z 1) with v0 in H0.
    let v1 := eval vm_compute in (argv1_z 1) in change (argv1_z 1) with v1 in H1.
    argw_close.
Qed.

Lemma main_at_open : forall en inp ms mo,
  bmain_at en inp ms mo <-> exists w V m, main_open en inp w V m ms mo.
Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Definition impl_stmt (rsA : Z) : Prop :=
  forall en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    main_open en inp w V m ms mo ->
    exists NMAX RNG A Q,
      tree_atA bsegs (at_nodeA bsegs) nstepA minvA (nsafeA NMAX) fstepS NMAX RNG A
        (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
        Q ms (MX mo []) mo
      /\ tglob nstepA PhiA
           (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp))) (MX mo []).

Section Assembly.
  (* [comment removed for export] *)
  Local Notation SPEC := OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common.Spec.spec.
  Definition TS : tfam := fun inp _ => SPEC (in_argv inp) (in_fs inp).

  (* [comment removed for export] *)
  Hypothesis PLAIN : side_ok psegs p_init_pc p_phdrs source_alloc_limit TS.
  Hypothesis NOKILL : tfam_no_kill TS.
  Hypothesis SPEC_nil : forall argv fs, SPEC argv fs [].

  Variable rsA : Z.
  Hypothesis IMPL : impl_stmt rsA.

  Lemma target_side : side_ok bsegs b_init_pc b_phdrs target_alloc_limit TS.
  Proof.
    apply both_side_ok. intros en inp Hv Hi. split.
    - apply SPEC_nil.
    - intros ms mo HM.
      apply main_at_open in HM as (w & V & m & HM).
      pose proof HM as (_ & _ & _ & _ & HP & _ & _ & _ & _ & HMOD).
      apply Forall_app in HP as [HP _].
      destruct (IMPL en inp w V m ms mo Hv Hi HM) as (NMAX & RNG & A & Q & HT & HG).
      eapply SpinAlg.srz_conseq.
      + exact (implF_srealizes bsegs (at_nodeA bsegs) nstepA nexitA minvA (nsafeA NMAX) fstepS NMAX (nodesA_sound bsegs NMAX) _ RNG A Q ms (MX mo []) mo HT).
      + (* [comment removed for export] *)
        destruct (moZ0_ok inp (valid_input_either_reader _ Hi)) as (Z1 & Z2 & Z3 & Z4).
        destruct (equiv_ZA_asan 0 rsA V (en_sp en) inp mo (moZ0 inp) Hi HMOD HP HG Z1 Z2 Z3 Z4 (progZ_no_leaf inp (moZ0 inp) 0 Hi Z1 Z2 Z3 Z4)) as [HEQ _].
        intros tr. unfold TS. rewrite <- (bridgeU' inp (moZ0 inp) 0 Hi Z1 Z2 Z3 Z4 tr). symmetry. apply HEQ.
  Qed.

  (* [comment removed for export] *)
  Theorem base :
    strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs)
      (mkImage bsegs b_init_pc b_phdrs).
  Proof.
    eapply (side_ok_equiv_budgets_abort _ _ _ _ _ _ TS TS); [exact PLAIN | exact target_side | exact NOKILL |].
    intros enS enT inp HvS HvT Hi tr. reflexivity.
  Qed.

  (* [comment removed for export] *)
End Assembly.
