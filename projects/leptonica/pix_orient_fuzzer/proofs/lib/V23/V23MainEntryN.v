(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the CONFIG_RSEQ flag; the new auxv layout; the launch's stack window; the recorded proofs of total_arg_bytes_firstn_S, len_avN, evN_junk, spxN_val, main_regs_okN, main_strN_fits and 15 more replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv MuslStrlen SymExec MemSplit RefLayout StartupTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23StartupDefs V23Startup V23StartupFacts V23MainEntry.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma total_arg_bytes_firstn_S : forall k l, (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l Hk.
  - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons. cbn. lia.
  - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth length] in *. rewrite !total_arg_bytes_cons.
    specialize (IH l' ltac:(lia)). lia.
Qed.

Section MainEntryN.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs mem.

  Definition p0N : word := cat_argv_ptr (ed_top a_draw) av envv a_execfn 0.
  Definition auxvpN : word := auxv_w sp0 (inpA av envv).
  Definition rndN : word := at_random_ptr sp0 (kb_rseq a_kernel) av envv.

  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid] ++ junk_vals regs.
  Definition EN : env := Env (vals_ev valsN) (blobs_ev [[]; []; guard_bytes a_draw]).   (* [comment removed for export] *)

  Definition sr_mainN : list expr :=
    [ELit 0; ELit 0x10df20; spx (-48); ELit 0x10800; ELit 0x1381d0; EVar 11; EVar 12; EVar 13;
     spx 8; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x63140; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
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
          | exact (me_ra _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ ME); cbn; tauto
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

  (* [comment removed for export] *)
  Lemma main_strN_fits : forall k, (k < length av)%nat -> entry_stack_fits sp0 av envv ->
    (bv_unsigned (cat_argv_ptr (ed_top a_draw) av envv a_execfn k) + Z.of_nat (length (nth k av [])) + 1 <= 0x800000000000)%Z.
  Proof using Hva Hve Hvsp ME.
    intros k Hk _. exact (me_argv_fits sp0 av envv tid regs mem ME Hva Hve Hvsp k Hk).
  Qed.

  Lemma main_strN : forall k, (k < length av)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top a_draw) av envv a_execfn k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top a_draw) av envv a_execfn k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top a_draw) av envv a_execfn k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top a_draw) av envv a_execfn k) + Z.of_nat (length (nth k av []))))
                         8 = Some t8).
  Proof using Hva Hve Hvsp ME.
    intros k Hk'. pose proof Hlo. pose proof Hhi.
    destruct (me_argv_bounds sp0 av envv tid regs mem ME Hva Hve Hvsp k Hk') as [B1 B2].
    pose proof (me_argv_near sp0 av envv tid regs mem ME Hva Hve Hvsp k Hk') as Bn.
    pose proof (valid_argv_str_len av k Hva Hk') as Hlen.
    repeat split.
    - apply rdn_app.
      + exact (me_argv_str sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS k Hk').
      + pose proof (me_argv_byte sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS k (length (nth k av [])) Hk' ltac:(lia)) as Hb.
        rewrite app_nth2, Nat.sub_diag in Hb by lia. cbn [nth] in Hb. exact Hb.
    - exact B1.
    - lia.
    - exact Hlen.
    - exact (me_word_after sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS k Hk').
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma keN0 : ev EN 0 = sp0.
  Proof. reflexivity. Qed.
  Lemma keN1 : ev EN 1 = p0N.
  Proof. reflexivity. Qed.
  Lemma keN3 : ev EN 3 = auxvpN.
  Proof. reflexivity. Qed.
  Lemma keN5 : ev EN 5 = tid.
  Proof. reflexivity. Qed.

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
      apply (main_entry_store_ok_win sp0 av envv tid regs mem ME); rewrite u_small by lia;
        unfold wok_lo, stack_window_reach, stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      pose proof (me_argv_ptr sp0 av envv tid regs mem ME Hva Hve Hvsp RSEGS 0%nat ltac:(lia)) as Hr.
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - unfold p0N. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvpN : forall segs,
    rdn segs (D_main sp0 (inpA av envv) a_draw tid) (Z_to_bv 64 0x158468) 8
    = Some (word_to_le_bytes 8 auxvpN).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof Hlo. pose proof Hhi.
    unfold auxvpN, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_dataN : wseg_ok RSEGS (Z_to_bv 64 0x127000) 0x32000 = true.
  Proof. exact wseg_data. Qed.   (* [comment removed for export] *)

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

  Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x159000)%Z ->
    kentry_ok RSEGS EN mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 (inpA av envv) a_draw tid i Hva); [lia | lia |].
    apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.

  Lemma know_imageN : know_ok RSEGS EN mem kn_image.
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x127000) (Z_to_bv 64 (0x127000 + d)) 0x32000 m 0x127000 0x159000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_dataN (D_main_self sp0 av envv tid).
    - kw_memN (main_entry_tid sp0 av envv tid HLO regs mem ME).
    - (* [comment removed for export] *)
      rewrite (u_small 8) by lia.
      split; [lia|]. split; [change (eb EN 2) with (guard_bytes a_draw); rewrite length_guard_bytes; reflexivity|].
      intros i Hi. change (eb EN 2) with (guard_bytes a_draw).
      rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
      rewrite Z.add_0_l. apply (D_main_guard_at sp0 av envv tid). lia.
    - kw_dataN D_main_auxvpN.
    - kw_dataN (D_main_pagesize sp0 av envv tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.

  Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
  Proof.
    unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
  Qed.

  Lemma valsN_length : length valsN = 38%nat.
  Proof. unfold valsN. rewrite length_app, junk_vals_length. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma evN_argc : ev EN 16 = argcN (inpA av envv).
  Proof. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ ME). Qed.
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
