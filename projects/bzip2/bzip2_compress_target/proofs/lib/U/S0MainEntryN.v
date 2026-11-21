(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main entry over the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv and the init stack window). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require StoreOk.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive MemSplit RefLayout StartupTac StartupRnd U.S0StartupDefs U.S0Startup.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require U.S0MainEntry.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require U.S0MainEntry SymDriveX.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.FileSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ArgvEnv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk.MuslStrlen OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StartupTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0StartupDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry.S0StartupFacts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX.
Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The blobs of the argc <> 2 entry: the AT_RANDOM bytes, the canary and
   AT_HWCAP.  Outside the section so a consumer can name the hwcap word. *)
Definition blobsN (hw : word) (rnd : EntryDraw) : list (list byte) :=
  [[]; []; at_random_bytes (ed_random rnd); canary_bytes rnd; word_to_le_bytes 8 hw].

Section MainEntryN.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variable rnd : EntryDraw.   (* the launch's random draw *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation envv := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.

  Definition p0N : word := cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) 0.
  Definition auxvpN : word := auxv_w inp sp0.
  Definition rndN : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp).

  (* [comment removed for export] *)
  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid] ++ junk_vals regs.
  Definition EN : env := Env (vals_ev valsN) (blobs_ev (blobsN hw rnd)).

  Definition sr_mainN : list expr :=
    [ELit 0; ELit 0x28c48; spx (-48); ELit 0x10800; ELit 0x441e0; EVar 11; EVar 12; EVar 13;
     spx 8; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x13580; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stackN : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     (* LPS 75d69e00 (#38): was [KWr (SA (EVar 0) (-8388608)) 8388608].  BYTES.
        Narrowed from the allocator ceiling [stack_max_size] to the span
        [stack_window_depth = 8388608 - 2244095 = 6144513], which is all
        [main_entry_store_ok_win] gives since 75d69e00. *)
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
          | exact (me_ra _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ _ _ ME); cbn; tauto
          | idtac ].

  Theorem main_regs_okN : regs_ok EN sr_mainN regs.
  Proof.
    pose proof Hlo. pose proof Hhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma main_strN : forall k, (k < length av)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rnd) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rnd) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rnd) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rnd) av envv (in_execfn inp) k) + Z.of_nat (length (nth k av []))))
                         8 = Some t8).
  Proof.
    intros k Hk'. pose proof Hlo. pose proof Hhi.
    destruct (argv_ptr_bounds Sv48 inp mbase sp0 brk rnd k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rnd)
                                  (in_argv inp) (in_envp inp) (in_execfn inp)
                                + total_arg_bytes_nat (firstn k (in_argv inp))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rnd); try eassumption;
          first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    (* RefLayout's Section Layout discharges (inp mbase ph entry sp brk rdraw);
       the call was missing [brk], so [rnd] landed on a word slot. *)
    pose proof (struct_av_bound inp mbase RPH entry sp0 brk rnd) as Hsb.
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rnd Hvl Hlau) as Hl.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (valid_argv_str_len (in_argv inp) k Hva Hk') as Hlen.
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rnd) as Hw. unfold wmem in Hw.
    repeat split.
    - rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by lia.
      rewrite Hw by lia. exact (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rnd k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
    - cps_destruct (read_word_stack Sv48 RSEGS inp mbase RPH entry sp0 brk rnd k (length (nth k av [])) Hlau Hk' ltac:(lia)) as (t8 & Hl8 & Hr8).
      exists t8. rewrite w_add_nat in Hr8.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; lia).
      rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  Lemma keN0 : ev EN 0 = sp0. Proof. reflexivity. Qed.
  Lemma keN1 : ev EN 1 = p0N. Proof. reflexivity. Qed.
  Lemma keN3 : ev EN 3 = auxvpN. Proof. reflexivity. Qed.
  Lemma keN5 : ev EN 5 = tid. Proof. reflexivity. Qed.

  Lemma know_stackN : know_ok RSEGS EN mem kn_stackN.
  Proof.
    pose proof Hlo. pose proof Hhi. pose proof Hal. pose proof len_avN as Hlen.
    cps_destruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
    unfold kn_stackN, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?keN0, ?keN1;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      (* LPS 75d69e00 (#38): span floor; was [... ; unfold stack_max_size; lia]. *)
      apply (main_entry_store_ok_win inp mbase entry sp0 rnd tid regs mem ME);
        rewrite u_small by lia; clear - Hd Hm; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rnd) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rnd) (in_argv inp) envv (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rnd); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | lia]). rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - unfold p0N. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvpN : forall segs,
    rdn segs (D_main inp sp0 rnd tid) (Z_to_bv 64 0x64478) 8
    = Some (word_to_le_bytes 8 auxvpN).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof Hlo. pose proof Hhi.
    unfold auxvpN, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_dataN : wseg_ok RSEGS (Z_to_bv 64 0x33000) 208896 = true.
  Proof. exact wseg_data. Qed.  (* [comment removed for export] *)

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

  Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x66000)%Z ->
    kentry_ok RSEGS EN mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none inp sp0 rnd tid i Hva); [lia | lia |].
    apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.

  Lemma kblob_static8N : forall (a : Z) (k : nat) bs,
    (0x10000 <= a)%Z -> (a + 8 <= 0x66000)%Z -> eb EN k = bs -> length bs = 8%nat ->
    rdn [] mem (Z_to_bv 64 a) 8 = Some bs ->
    kentry_ok RSEGS EN mem (KBlob (SA (ELit 0) a) (ELit 8) k).
  Proof.
    intros a k bs Ha Hb Hk Hlen Hr. pose proof Hlo as HLO.
    apply (kblob_intro RSEGS EN mem (ELit 0) (Z_to_bv 64 0) a (ELit 8) k bs); cbn [edenot]; rewrite ?u_small by lia; try lia;
      try reflexivity; try exact Hk; try (rewrite Hlen; reflexivity).
    rewrite Hlen. intros i Hi.
    pose proof (rdn_pointwise_inv [] mem 8 (Z_to_bv 64 a) bs ltac:(intros j Hj; reflexivity)
                  ltac:(rewrite u_small by lia; lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
    rewrite u_small, Z2Nat.id in Hp by lia. rewrite Z.add_0_l. exact Hp.
  Qed.

  Lemma know_imageN : know_ok RSEGS EN mem kn_image.
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      try (lazymatch goal with
           | |- kentry_ok _ _ _ (KBlob (SA (ELit 0) 0x441d0) _ _) =>
               apply (kblob_static8N 0x441d0 3 (canary_bytes rnd)); [lia | lia | reflexivity | apply length_canary_bytes
                 | rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
                   rewrite <- word_to_le_bytes_canary; apply (D_main_canary inp sp0 rnd tid)]
           | |- kentry_ok _ _ _ (KBlob (SA (ELit 0) 0x64450) _ _) =>
               apply (kblob_static8N 0x64450 3 (canary_bytes rnd)); [lia | lia | reflexivity | apply length_canary_bytes
                 | apply (main_entry_guard inp mbase entry sp0 rnd tid HLO regs mem ME)]
           | |- kentry_ok _ _ _ (KBlob (SA (ELit 0) 0x644d8) _ _) =>
               apply (kblob_static8N 0x644d8 4 (word_to_le_bytes 8 hw)); [lia | lia | reflexivity | apply length_N_to_le_bytes
                 | rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
                   apply (D_main_hwcap inp sp0 rnd tid Hva)]
           end);
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x33000) (Z_to_bv 64 (0x33000 + d)) 208896 m 0x33000 0x66000);
        [reflexivity | vm_cast_no_check (@eq_refl Z 0x66000%Z) | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_dataN (D_main_self inp sp0 rnd tid).
    - kw_memN (main_entry_tid inp mbase entry sp0 rnd tid HLO regs mem ME).
    - kw_dataN D_main_auxvpN.
    - kw_dataN (D_main_pagesize inp sp0 rnd tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.

  Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
  Proof.
    unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma evN_argc : ev EN 16 = argcN inp.
  Proof. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ _ _ ME). Qed.
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
