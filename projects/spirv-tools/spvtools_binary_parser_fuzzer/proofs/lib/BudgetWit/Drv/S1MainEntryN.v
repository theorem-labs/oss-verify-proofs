(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Drv/S1MainEntryN.v for the budget-premise witness: the same proofs over BudgetWit.SRealizes.srealizes, the released srealizes with a no-allocation-call check at each node; only module paths change. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; the revised stack window). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv MuslStrlen SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefLayout StartupTac SymDriveX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib S1BootDefs S1Boot S1StartInit S1CxxTable.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit.Drv Require Import S1Start S1CxxLink S1StartupFacts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1ExitKn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit.Drv Require Import S1MainEntry.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MainEntryN.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Context {fs0 : Fs.Fs} {stdin0 : InputStream} {mbase : word}.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  (* 75d69e00: [S1Start.main_entry] takes the run's whole ProcInput and the
     mmap base in place of (argv, envp, uid, hwcap); this Section still
     applied it positionally at the old nine, the fifth of the six stale
     sites an earlier repair of this unit lists.  [in_argv]/[in_envp]/[in_uid]/[in_hwcap] of
     [INP] reduce to exactly the four the old spelling named, so this is the
     same premise, not a narrower one.  Spelling copied from the already
     migrated sibling S1MainEntry.v:305-311. *)
  Local Notation INP := (mkProcInputC av envv fs0 stdin0) (only parsing).
  Hypothesis ME : main_entry sp0 rdraw INP mbase tid regs mem.

  (* LPS 75d69e00 (#38): argv[0] sits in the string block below [ed_top rdraw] after
     AT_EXECFN's bytes, as [S1MainEntry.p0] reads it; [auxvpN] is the body of
     [S1BootDefs.auxv_w] for this input, spelled out (as [S1MainEntry.auxvp]) so it
     does not take the input's fs/stdin, which it does not read. *)
  Definition p0N : word := cat_argv_ptr (ed_top rdraw) av envv a_execfn 0.
  Definition auxvpN : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length envv)).
  Definition rndN : word := canary rdraw.

  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid] ++ junk_vals regs.
  Definition EN : env := Env (vals_ev valsN) (blobs_ev []).

  Definition sr_mainN : list expr :=
    [ELit 0; ELit 0xcfab0; spx (-48); ELit 0x10800; ELit 0x1006b8; EVar 11; EVar 12; EVar 13;
     spx 8; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x655e8; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stackN : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     (* #38 rule 12i: certified window is [[wok_lo sp0, sp0)]; symbol, not literal. *)
     KWr (SA (EVar 0) (- stack_window_depth)) stack_window_depth;
     KWord (SA (EVar 0) 8) 8 (EVar 1);
     KRange (EVar 1) 0x7fff80000000 0x800000400000].

  Definition kn_mainN : list kentry := kn_stackN ++ kn_image.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Lemma len_avN : (1 <= length av <= 1024)%nat.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma evN_junk : forall i, (i < 32)%nat -> ev EN (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold EN. cbn [ev]. unfold valsN.
    change (6 + i)%nat with (length [sp0; p0N; p0N; auxvpN; rndN; tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spxN_val : forall k, edenot EN (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev EN 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  (* [main_entry]'s projections take its seven parameters, then the record. *)
  Ltac reg_caseN :=
    cbn [nth sr_mainN all_regs];
    first [ rewrite spxN_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot EN (EVar n)) with (ev EN n);
              first [ rewrite (evN_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact (me_ra _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ _ ME); cbn; tauto
          | idtac ].

  Theorem main_regs_okN : regs_ok EN sr_mainN regs.
  Proof.
    pose proof Hlo. pose proof Hhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
  Qed.

  Lemma me38N_vl : valid_launch INP.
  Proof. exact (me_vl _ _ _ _ _ _ _ ME). Qed.
  Lemma me38N_lau : exists brk, entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) INP.
  Proof. exact (me_lau _ _ _ _ _ _ _ ME). Qed.

  (* Rewrite the launch input's projections back to the names this Section uses, so
     [lia] sees one atom per quantity (as [S1MainEntry]'s [inp_norm]). *)
  Ltac inp_normN H :=
    try change (in_argv (mkProcInputC av envv fs0 stdin0)) with av in H;
    try change (in_envp (mkProcInputC av envv fs0 stdin0)) with envv in H;
    try change (in_execfn (mkProcInputC av envv fs0 stdin0)) with a_execfn in H;
    try change (in_kernel (mkProcInputC av envv fs0 stdin0)) with a_kernel in H.

  (* #38: argv string [k] is at [cat_argv_ptr (ed_top rdraw) av envv a_execfn k], in the
     string block below [ed_top], not at a fixed offset from sp0 (the same proof as
     [S1MainEntry.main_str], for any argv). *)
  Lemma main_strN : forall k, (k < length av)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv a_execfn k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv a_execfn k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv a_execfn k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv a_execfn k) + Z.of_nat (length (nth k av []))))
                         8 = Some t8).
  (* [Hve] is no longer read (the launch facts come from [ME]); it stays a parameter so
     the positional callers ([S1RFirst]) keep their argument list. *)
  Proof using Hva Hve Hvsp ME.
    intros k Hka. pose proof Hlo. pose proof Hhi.
    destruct me38N_lau as [brk Hlau]. pose proof me38N_vl as Hvl.
    assert (Hk' : (k < length (in_argv INP))%nat) by exact Hka.
    destruct (argv_ptr_bounds Sv48 INP mbase sp0 brk rdraw k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv INP) (in_envp INP) (in_execfn INP) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel INP)) sp0 (ed_top rdraw)
                                  (in_argv INP) (in_envp INP) (in_execfn INP)
                                + total_arg_bytes_nat (firstn k (in_argv INP))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 INP mbase RPH (0x6549c : word) sp0 brk rdraw);
          try eassumption; first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    pose proof (struct_av_bound INP mbase RPH (0x6549c : word) sp0 brk rdraw) as Hsb.
    pose proof (lay_bsb_len Sv48 INP mbase RPH (0x6549c : word) sp0 brk rdraw Hvl Hlau) as Hl.
    pose proof (entry_stack_image_no_wrap Sv48 INP mbase RPH (0x6549c : word) sp0 brk rdraw Hlau) as Hnw.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (valid_argv_str_len av k Hva Hka) as Hlen.
    inp_normN B1. inp_normN B2. inp_normN Hu. inp_normN Hsb.
    pose proof (rdn_wmem_stack RSEGS INP mbase RPH (0x6549c : word) sp0 rdraw) as Hw. unfold wmem in Hw.
    repeat split.
    - rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by lia.
      rewrite Hw by lia.
      exact (read_argv_cstr_k Sv48 RSEGS INP mbase RPH (0x6549c : word) sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
    - destruct (read_word_stack Sv48 RSEGS INP mbase RPH (0x6549c : word) sp0 brk rdraw k (length (nth k av []))
                  Hlau Hk' (le_n _) Hnw) as (t8 & Hl8 & Hr8).
      exists t8. rewrite w_add_nat in Hr8.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  Lemma keN0 : ev EN 0 = sp0. Proof. reflexivity. Qed.
  Lemma keN1 : ev EN 1 = p0N. Proof. reflexivity. Qed.
  Lemma keN3 : ev EN 3 = auxvpN. Proof. reflexivity. Qed.
  Lemma keN5 : ev EN 5 = tid. Proof. reflexivity. Qed.

  Lemma know_stackN : know_ok RSEGS EN mem kn_stackN.
  Proof.
    pose proof Hlo. pose proof Hhi. pose proof Hal. pose proof len_avN as Hlen.
    destruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
    unfold kn_stackN, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?keN0, ?keN1;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
    - split; [lia | exact Hal].
    - lia.
    - (* [stack_window_depth] is an opaque model constant (as in [S1MainEntry.know_stack]). *)
      rewrite ?stack_window_depth_val. split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win _ _ _ _ _ _ _ ME);
        rewrite ?stack_window_depth_val; rewrite u_small by lia;
        try unfold wok_lo; try unfold stack_window_reach; try unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      destruct me38N_lau as [brk Hlau]. pose proof me38N_vl as Hvl.
      assert (Hr : rdn RSEGS (wrap_mem INP mbase RPH (0x6549c : word) sp0 rdraw)
                     (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv INP) (in_envp INP) (in_execfn INP) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 INP mbase RPH (0x6549c : word) sp0 brk rdraw);
            try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia
                  | change (in_argv (mkProcInputC av envv fs0 stdin0)) with av; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - unfold p0N. lia.
  Qed.

  Lemma auxvpN_w : auxvpN = auxv_w INP sp0.
  Proof. reflexivity. Qed.

  Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x122000)%Z ->
    kentry_ok RSEGS EN mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    destruct (missb_parts lo _ Hb) as (_ & _ & Hlo0 & _).
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 INP tid rdraw Hva).
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.

  Lemma know_imageN0 : know_ok RSEGS EN mem kn_image0.
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    unfold kn_image0, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    -   split; [lia|]. intros d m Hd Hm.
      apply store_ok_of_all; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
      apply rw_wview. lia.
    - kw_dataN (D_main_self sp0 INP tid rdraw Hva).
    - kw_dataN (D_main_tid sp0 INP tid rdraw Hva).
    - kw_dataN (D_main_canary sp0 INP tid rdraw Hva).
    - kw_dataN (D_main_guard sp0 INP tid rdraw Hva).
    - rewrite auxvpN_w. kw_dataN (D_main_auxv sp0 INP tid rdraw Hva).
    - kw_dataN (D_main_pagesize sp0 INP tid rdraw Hva).
    -   lia.
  Qed.

  Lemma know_cellsN : forall cells, cells_in_cxx cells = true ->
    know_ok RSEGS EN mem (map (fun c : Z * nat * Z => match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end) cells).
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI.
    induction cells as [|[[a w] v] rest IH]; intros Hc; [constructor|].
    cbn [cells_in_cxx forallb] in Hc. apply andb_prop in Hc as [Hc Hrest].
    apply andb_prop in Hc as [Hc HL]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [H0 H1].
    apply Nat.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (lookup_runs D_CXX a w) as [zs|] eqn:HLK; [|discriminate].
    constructor; [|apply IH; exact Hrest].
    cbn [kentry_ok a_base a_off edenot]. split; [exact H0|]. unfold flat, estart, adenot. cbn [a_base a_off edenot].
    rewrite (u_small 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small 0) by lia. rewrite Z.add_0_l.
    rewrite (main_entry_rdn_data _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    rewrite (D_main_cxx sp0 INP tid rdraw RSEGS a w zs) by (try exact HLK; lia).
    f_equal. apply byte_list_eq2. rewrite map_map. apply zlist_eqb_eq in HL. exact HL.
  Qed.

  Lemma know_imageN : know_ok RSEGS EN mem kn_image.
  Proof.
    unfold kn_image. unfold know_ok. rewrite !Forall_app. split; [apply know_imageN0|]. split.
    - unfold kn_cxx_exit2. apply know_cellsN. vm_compute. reflexivity.
    - pose proof Hlo as HLO. pose proof Hhi as HHI.
      repeat apply Forall_cons; try apply Forall_nil.
      cbn [kentry_ok a_base a_off edenot]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off edenot].
      rewrite (u_small 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small 0) by lia. rewrite Z.add_0_l.
      rewrite (main_entry_rdn_data _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
      erewrite (D_main_cxx sp0 INP tid rdraw RSEGS); [ | lia | cbn; lia | reflexivity].
      f_equal. apply byte_list_eq2. vm_compute. reflexivity.
  Qed.

  Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
  Proof.
    unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
  Qed.

  Lemma evN_argc : ev EN 16 = len_word av.
  Proof. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ _ ME). Qed.
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
