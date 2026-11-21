(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the argv strings sit at the top of the stack block after the exec file name, AT_RANDOM's place depends on the kernel's rseq flag, and the mapped window under sp is the launch's; the lemmas re-proved over the launch input that main_entry names; encoded (CDefT) statements and recorded lia answers replaced by plain text and plain lia). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk FileSim ArgvEnv MuslStrlen SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit Layout StartupTac SymDriveX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup_defs U_startup U_startup_facts U_main_entry.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MainEntryN.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid rd regs mem.

  (* 08b1429: the strings sit at the top of the block (over the stack VMA's end and the exec file name,
     which [main_entry] fixes to the ambient one), and AT_RANDOM's place depends on the kernel's rseq flag *)
  Definition p0N : word := cat_argv_ptr (ed_top rd) av envv a_execfn 0.
  Definition auxvpN : word := Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length envv)).
  Definition rndN : word := at_random_ptr sp0 (kb_rseq a_kernel) av envv.

  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid; canary_w rd; a_hwcap] ++ junk_vals2 regs.
  Definition EN : env := Env (vals_ev valsN) (blobs_ev []).

  Definition sr_mainN : list expr := (cons (ELit 0) (cons (ELit 0x3f2a8) (cons (spx (-48)) (cons (ELit 0x10800) (cons (ELit 0x5d0c8) (cons (EVar 11) (cons (EVar 12) (cons (EVar 13) (cons (spx 8) (cons (EVar 15) (cons (EVar 16) (cons (spx 8) (cons (EVar 18) (cons (EVar 19) (cons (EVar 20) (cons (EVar 21) (cons (EVar 22) (cons (EVar 23) (cons (ELit 0x1d24c) (cons (EVar 25) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (ELit 0) (cons (EVar 34) (cons (EVar 35) (cons (EVar 36) [(EVar 37)]))))))))))))))))))))))))))))))).

  (* 08b1429: the mapped window under sp is [wok_lo sp0, sp0) ([MemSplit.wok_lo]): 6144513 bytes *)
  Definition kn_stackN : list kentry := (cons (KAlign (EVar 0) 16) (cons (KRange (EVar 0) 0x7fff80000000 0x800000000000) (cons (KWr (SA (EVar 0) (-6144513)) 6144513) (cons (KWord (SA (EVar 0) 8) 8 (EVar 1)) [(KRange (EVar 1) 0x7fff80000000 0x800000400000)])))).

  Definition kn_mainN : list kentry := kn_stackN ++ kn_image.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  #[using="sp0 Hva"] Lemma len_avN : (1 <= length av <= 1024)%nat.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  #[using="Hvsp Hlo"] Lemma evN_junk : forall i, (2 <= i < 32)%nat -> ev EN (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold EN. cbn [ev]. unfold valsN.
    replace (6 + i)%nat with (length [sp0; p0N; p0N; auxvpN; rndN; tid; canary_w rd; a_hwcap] + (i - 2))%nat by (cbn [length]; lia).
    unfold vals_ev. rewrite app_nth2_plus. unfold junk_vals2.
    rewrite (nth_map_seq_gen (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. f_equal. f_equal. lia.
  Qed.

  #[using="Type"] Lemma spxN_val : forall k, edenot EN (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev EN 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

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

  #[using="mem Hvsp Htid ME Hlo Hhi"] Theorem main_regs_okN : regs_ok EN sr_mainN regs.
  Proof.
    pose proof Hlo. pose proof Hhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)


  #[using="AMB tid rd regs Hva Hve Hvsp ME Hlo Hhi"] Lemma main_strN : forall k, (k < length av)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rd) av envv a_execfn k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rd) av envv a_execfn k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rd) av envv a_execfn k) <= bv_unsigned sp0 + 0x2028b8)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 0x1ffff)%Z
    /\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rd) av envv a_execfn k)
                                           + Z.of_nat (length (nth k av [])))) 8 = Some t8).
  Proof.
    intros k Hk. pose proof Hlo. pose proof Hhi.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    assert (Ec : cat_argv_ptr (ed_top rd) av envv a_execfn k
                 = cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) k) by (rewrite Eav, Eev, Eef; reflexivity).
    assert (El : nth k av [] = nth k (in_argv inp) []) by (rewrite Eav; reflexivity).
    rewrite Ec, El.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Eav; exact Hk).
    destruct (argv_ptr_bounds Sv48 inp mbase sp0 brk rd k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rd)
                                  (in_argv inp) (in_envp inp) (in_execfn inp)
                                + total_arg_bytes_nat (firstn k (in_argv inp))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 inp mbase RPH (0x1d100 : word) sp0 brk rd); try eassumption;
          first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    assert (Hsb : (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp)
                    + total_arg_bytes_nat (in_argv inp) + total_arg_bytes_nat (in_envp inp)
                    <= length (entry_stack_image inp mbase RPH (0x1d100 : word) sp0 rd))%nat)
      by (eapply struct_av_bound; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    assert (Hl : (Z.of_nat (length (entry_stack_image inp mbase RPH (0x1d100 : word) sp0 rd)) <= 2101782)%Z)
      by (eapply lay_bsb_len; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    assert (Hnw : (bv_unsigned sp0 + Z.of_nat (length (entry_stack_image inp mbase RPH (0x1d100 : word) sp0 rd)) < 2^64)%Z)
      by (eapply lay_bsb_nw; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact kp_al | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (valid_argv_str_len (in_argv inp) k Hva' Hk') as Hlen.
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH (0x1d100 : word) sp0 rd) as Hw. unfold wmem in Hw.
    repeat split.
    - rewrite RDA by lia.
      rewrite Hw by lia.
      exact (read_argv_cstr_k Sv48 RSEGS inp mbase RPH (0x1d100 : word) sp0 brk rd k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
    - destruct (read_word_stack Sv48 RSEGS inp mbase RPH (0x1d100 : word) sp0 brk rd k (length (nth k (in_argv inp) []))
                  Hlau Hk' ltac:(lia) Hnw) as (t8 & Hl8 & Hr8).
      exists t8. rewrite w_add_nat in Hr8.
      rewrite RDA by (rewrite u_small by lia; lia).
      rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma keN0 : ev EN 0 = sp0. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN1 : ev EN 1 = p0N. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN3 : ev EN 3 = auxvpN. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN5 : ev EN 5 = tid. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN6 : ev EN 6 = canary_w rd. Proof. reflexivity. Qed.
  #[using="Type"] Lemma keN7 : ev EN 7 = a_hwcap. Proof. reflexivity. Qed.

  #[using="Hva Hve Hvsp ME Hlo Hhi Hal"] Lemma know_stackN : know_ok RSEGS EN mem kn_stackN.
  Proof.
    pose proof Hlo. pose proof Hhi. pose proof Hal. pose proof len_avN as Hlen.
    destruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    unfold kn_stackN, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?keN0, ?keN1;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 av envv tid rd regs mem ME);
        rewrite u_small by lia; unfold wok_lo, stack_window_reach, stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      rewrite RDA by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH (0x1d100 : word) sp0 rd) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH (0x1d100 : word) sp0 brk rd); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Eav; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. unfold p0N. rewrite Eav, Eev, Eef. reflexivity.
    - unfold p0N. lia.
  Qed.

  #[using="Hvsp Hlo Hhi"] Lemma D_main_auxvpN : forall (inp : ProcInput) segs, in_argv inp = av -> in_envp inp = envv ->
    rdn segs (D_main sp0 inp rd tid) (Z_to_bv 64 0x7d358) 8 = Some (word_to_le_bytes 8 auxvpN).
  Proof.
    intros inp segs Ea Ee. pose proof (u64_range tid). pose proof Hlo. pose proof Hhi.
    assert (E' : auxvpN = auxv_w sp0 inp) by (unfold auxvpN, auxv_w; rewrite Ea, Ee; reflexivity).
    rewrite E'.
    unfold auxv_w, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)

  #[using="Type"] Lemma wseg_dataN : wseg_ok RSEGS (Z_to_bv 64 0x4c000) 0x32000 = true.
  Proof. vm_compute. reflexivity. Qed.

  #[using="sp0 Hvsp Hlo"] Lemma range_disjoint_subN : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
  Proof.
    intros lo n [c w] i H Hlo' Hhi'. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  #[using="sp0 Hvsp Hlo"] Lemma missb_subN : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
  Proof.
    intros lo n i H Hlo' Hhi'. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_subN lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.

  #[using="Hva Hvsp ME Hlo Hhi"] Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x7e000)%Z ->
    kentry_ok RSEGS EN mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite MD by (rewrite u_small by lia; rewrite stack_max_size_val; lia).
    apply (D_main_none inp sp0 rd tid i Hva'); [lia | lia |].
    apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN RD L :=
    kw_preN;
    rewrite RD by (rewrite u_small by lia; rewrite stack_max_size_val; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.

  #[using="Hva Hvsp Htid ME Hlo Hhi"] Lemma know_imageN : know_ok RSEGS EN mem kn_image.
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5, ?keN6, ?keN7; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x4c000) (Z_to_bv 64 (0x4c000 + d)) 0x32000 m 0x4c000 0x7e000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_dataN RDD (D_main_self inp sp0 tid rd).
    - kw_memN (main_entry_tid sp0 av envv tid rd HLO regs mem ME).
    - kw_dataN RDD (D_main_canary inp sp0 tid rd).
    - kw_memN (main_entry_guard sp0 av envv tid rd HLO regs mem ME). rewrite canary_store. reflexivity.
    - (* [kw_dataN] applies its lemma to RSEGS; D_main_auxvpN binds segs before its premises *)
      kw_dataN RDD (fun segs => D_main_auxvpN inp segs Eav Eev).
    - kw_dataN RDD (D_main_pagesize inp sp0 tid rd Hva').
    - kw_dataN RDD (D_main_hwcap inp sp0 tid rd Hva'); rewrite ?Ehw; try reflexivity.
    - lia.
  Qed.

  #[using="Hva Hve Hvsp Htid ME Hlo Hhi Hal"] Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
  Proof.
    unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
  Qed.

  #[using="Type"] Lemma valsN_length : length valsN = 38%nat.
  Proof. unfold valsN, junk_vals2. rewrite length_app, length_map, length_seq. reflexivity. Qed.

  (* 08b1429: the argv strings end at the stack VMA's end less 8 ([CatExec.u_cat_string_base],
     [launch_string_base_arith]), and that end is at most the Sv48 stack top; the old proof went
     through [main_entry_block_top], which no longer bounds the block. *)
  #[using="AMB tid rd regs mem Hva Hve Hvsp ME Hlo Hhi"] Lemma main_strN_top : forall k, (k < length av)%nat ->
    (bv_unsigned (cat_argv_ptr (ed_top rd) av envv a_execfn k) + Z.of_nat (length (nth k av [])) + 1 <= 0x800000000000)%Z.
  Proof.
    intros k Hk.
    destruct (main_entry_launch sp0 av envv tid rd regs mem ME) as (inp & mbase & brk & Eav & Eev & Euid & Egid & Ehw & Ekb & Eef & Hvl & Hlau & RDA & MD & RDD).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva). assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    assert (Ec : cat_argv_ptr (ed_top rd) av envv a_execfn k
                 = cat_argv_ptr (ed_top rd) (in_argv inp) (in_envp inp) (in_execfn inp) k) by (rewrite Eav, Eev, Eef; reflexivity).
    assert (El : nth k av [] = nth k (in_argv inp) []) by (rewrite Eav; reflexivity).
    rewrite Ec, El.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Eav; exact Hk).
    pose proof (launch_string_base_arith Sv48 inp mbase sp0 brk rd Hlau) as HA.
    pose proof (u_cat_string_base Sv48 inp mbase sp0 brk rd Hlau) as Hu.
    pose proof (u64_range sp0). pose proof (u64_range (ed_top rd)).
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

  (* [comment removed for export] *)
  #[using="mem Hvsp ME Hlo"] Lemma evN_argc : ev EN 16 = len_word av.
  Proof. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ _ ME). Qed.
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
