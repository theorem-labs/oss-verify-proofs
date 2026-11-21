(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the zero-filled stack window, the rseq-dependent auxv, the launch input's kernel build): changed D_main_auxvpN, ME, auxvpN and 12 more; added entry, inp, mbase. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv MuslStrlen
  SymExec SymExec2 SymExec2Sound SymRun SymDrive
  MemSplit RefLayout StartupTac Pm10StartupDefs Pm10Startup Pm10StartupFacts Pm10MainEntry SymDriveX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

Section MainEntryN.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Hypothesis ME : main_entry inp mbase entry sp0 av envv uid hw rdraw tid regs mem.

  Definition p0N : word := cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0.
  Definition auxvpN : word := Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length envv)).
  Definition rndN : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av envv.

  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid] ++ junk_vals regs.

  Definition blobsN : list (list byte) := [[]; []; word_to_le_bytes 8 (canary_w (ed_random rdraw)); word_to_le_bytes 8 hw].
  Definition EN : env := Env (vals_ev valsN) (blobs_ev blobsN).

  Definition sr_mainN : list expr :=
    [ELit 0; ELit 0xa4d60; spx (-48); ELit 0x10800; ELit 0xd49b0; EVar 11; EVar 12; EVar 13;
     spx 8; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x38f5c; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stackN : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-6144513)) 6144513;
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

  Ltac reg_caseN :=
    cbn [nth sr_mainN all_regs];
    first [ rewrite spxN_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot EN (EVar n)) with (ev EN n);
              first [ rewrite (evN_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact (me_ra _ _ _ _ _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ _ _ _ _ _ _ ME); cbn; tauto
          | idtac ].

  Theorem main_regs_okN : regs_ok EN sr_mainN regs.
  Proof.
    pose proof Hlo. pose proof Hhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
  Qed.

  Lemma main_strN : forall k, (k < length av)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) + Z.of_nat (length (nth k av []))))
                         8 = Some t8).
  Proof.
    intros k Hk0. pose proof Hlo. pose proof Hhi.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & Hvl & brk & Hlau).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    rewrite <- Eav, <- Eev. rewrite <- Eav in Hk0. rename Hk0 into Hk'.
    pose proof (entry_stack_image_no_wrap Sv48 inp mbase RPH entry sp0 brk rdraw Hlau) as Hnw.
    destruct (argv_ptr_bounds Sv48 inp mbase sp0 brk rdraw k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw)
                                  (in_argv inp) (in_envp inp) (in_execfn inp)
                                + total_arg_bytes_nat (firstn k (in_argv inp))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
          first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    assert (Hsb : (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)
                    + total_arg_bytes_nat (in_argv inp) + total_arg_bytes_nat (in_envp inp)
                    <= length (entry_stack_image inp mbase RPH entry sp0 rdraw))%nat)
      (* [struct_av_bound]'s post-section signature, printed by
         a build round:
           forall (inp : ProcInput) (mbase : word) (ph : PhdrInfo) (entry sp : word),
             word -> forall rdraw : EntryDraw, <conclusion>
         SEVEN explicit arguments and NO hypotheses -- RefLayout's six Hypotheses are
         not used in its proof, so none is retained.  The bare [eapply] therefore left
         the ANONYMOUS [word] (that is [brk], which the conclusion does not mention) as
         an evar, and no alternative in the [first [...]] list produces a [word]:
         "No applicable tactic" named the list while the unsolved goal was an argument.
         Supplied positionally, exactly as :129 already does for [u_cat_argv_ptr]. *)
      by (exact (struct_av_bound inp mbase RPH entry sp0 brk rdraw)).
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (valid_argv_str_len (in_argv inp) k Hva' Hk') as Hlen.
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
    repeat split.
    - rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by lia.
      rewrite Hw by lia. exact (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
    - destruct (read_word_stack Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k (length (nth k (in_argv inp) [])) Hlau Hk' ltac:(lia) Hnw) as (t8 & Hl8 & Hr8).
      exists t8. rewrite w_add_nat in Hr8.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  (* 08b1429: the strings end at the stack VMA's end less 8 (CatExec.u_cat_string_base), at most the Sv48 stack top *)
  Lemma main_strN_fits : forall k, (k < length av)%nat ->
    (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) + Z.of_nat (length (nth k av [])) + 9 <= 0x800000000000)%Z.
  Proof.
    intros k Hk0.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & Hvl & brk & Hlau).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    rewrite <- Eav, <- Eev. rewrite <- Eav in Hk0. rename Hk0 into Hk'.
    pose proof (launch_string_base_arith Sv48 inp mbase sp0 brk rdraw Hlau) as HA.
    pose proof (u_cat_string_base Sv48 inp mbase sp0 brk rdraw Hlau) as Hu.
    pose proof (u64_range sp0). pose proof (u64_range (ed_top rdraw)).
    pose proof (Nat2Z.is_nonneg
      (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat (firstn k (in_argv inp)))).
    assert (Hstr : (Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                    + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                    <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                   (in_execfn inp)))%Z).
    { pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk') as Hw.
      unfold launch_string_bytes. rewrite length_flatten_strings.
      pose proof (Nat2Z.is_nonneg (length (flatten_strings (in_envp inp)))).
      pose proof (Nat2Z.is_nonneg (length (in_execfn inp))).
      lia. }
    pose proof Hlau as Hlau2. cbn [entry_launch_ok_va] in Hlau2. destruct Hlau2 as ((_ & Htop & _) & _).
    assert (Hv : (va_stack_top Sv48 <= 0x800000000000)%Z) by (unfold Z.le; vm_compute; discriminate).
    rewrite (cat_argv_ptr_offset _ _ _ _ k Hk'), word_add_nat_Z2bv, Hu.
    rewrite u_Z2bv_lt by lia.
    lia.
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
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME);
        rewrite u_small by lia; unfold wok_lo, stack_window_reach, stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & Hvl & brk & Hlau).
      assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Eav; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p0N. rewrite Eav, Eev. reflexivity.
    - unfold p0N. lia.
  Qed.

  Lemma D_main_auxvpN : forall segs,
    rdn segs (D_main inp sp0 rdraw (ed_random rdraw) tid) (Z_to_bv 64 0xf4c48) 8
    = Some (word_to_le_bytes 8 auxvpN).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range (in_hwcap inp)). pose proof Hlo. pose proof Hhi.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & _).
    assert (Ea : auxvpN = auxv_w inp sp0) by (unfold auxvpN, auxv_w; rewrite Eav, Eev; reflexivity).
    rewrite Ea.
    unfold auxv_w, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_dataN : wseg_ok RSEGS (Z_to_bv 64 0xc2000) 0x34000 = true.
  Proof. vmc_refl. Qed.

  Lemma range_disjoint_subN : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
  Proof.
    intros lo n [c w] i H Hlo' Hhi'. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  Lemma missb_subN : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
  Proof.
    intros lo n i H Hlo' Hhi'. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_subN lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.

  Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0xf6000)%Z ->
    kentry_ok RSEGS EN mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & _).
    apply (D_main_none inp sp0 rdraw (ed_random rdraw) tid i ltac:(rewrite Eav; exact Hva)); [lia | lia |].
    apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.
  Ltac kblob8N L :=
    unorm; rewrite ?Z.add_0_l; repeat split; try lia;
    try (unfold EN; cbn [eb blobs_ev blobsN nth]; rewrite length_N_to_le_bytes; reflexivity);
    intros i Hi; unfold EN; cbn [eb blobs_ev blobsN nth];
    rewrite (main_entry_mem_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    apply L; lia.

  Lemma know_imageN : know_ok RSEGS EN mem kn_image.
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    destruct (main_entry_inp inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) as (Eav & Eev & Euid & Ehw & _).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    -   split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xc2000) (Z_to_bv 64 (0xc2000 + d)) 0x34000 m 0xc2000 0xf6000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_dataN (D_main_self inp sp0 rdraw tid).
    - kw_memN (main_entry_tid sp0 av envv uid hw rdraw tid Hva HLO regs mem inp mbase entry ME).
    - kw_dataN (D_main_locale inp sp0 rdraw tid).
    - kblob8N (D_canary_pt inp sp0 rdraw tid Hva').
    - kblob8N (D_guard_pt inp sp0 rdraw tid Hva').
    - kw_dataN D_main_auxvpN.
    - kw_dataN (D_main_pagesize inp sp0 rdraw tid Hva').
    - unorm; rewrite ?Z.add_0_l; repeat split; try lia;
        try (unfold EN; cbn [eb blobs_ev blobsN nth]; rewrite length_N_to_le_bytes; reflexivity);
        intros i Hi; unfold EN; cbn [eb blobs_ev blobsN nth];
        rewrite (main_entry_mem_data inp mbase entry sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
        rewrite <- Ehw; apply (D_hwcap_pt inp sp0 rdraw tid Hva'); lia.
    -   lia.
  Qed.

  Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
  Proof.
    unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
  Qed.

  Lemma valsN_length : length valsN = 38%nat.
  Proof. unfold valsN. rewrite length_app, junk_vals_length. reflexivity. Qed.

  Lemma evN_argc : ev EN 16 = len_word av.
  Proof. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ _ _ _ _ _ _ ME). Qed.
End MainEntryN.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
