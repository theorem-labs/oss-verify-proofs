(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv MuslStrlen
  SymExec SymExec2 SymExec2Sound SymRun SymDrive
  MemSplit RefLayout StartupTac DrawDefs U7StartupDefs U7Startup U7StartupFacts U7MainEntry SymDriveX.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments.
Abbreviation RPH := Tgt_zlib_uncompress2_fuzzer_ubsan.M.phdrs.
(* the entry pc as the launch block sees it. *)
Local Notation ENT := (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress2_fuzzer_ubsan.M.init_pc)) (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MainEntryN.
  (* over the launch input and the ruled VLAUNCH + LOK; av / envv are notations. *)
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation envv := (in_envp inp) (only parsing).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.

  Definition p0N : word := cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0.
  Definition auxvpN : word := auxv_w sp0 inp.
  Definition rndN : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av envv.

  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid; canary_w rdraw; secret_w rdraw] ++ junk_vals regs.
  Definition EN : env := Env (vals_ev valsN) (blobs_ev []).

  Definition sr_mainN : list expr :=
    [ELit 0; ELit 0x19f10; spx (-48); ELit 0x10800; ELit 0x74270; EVar 13; EVar 14; EVar 15;
     spx 8; EVar 17; EVar 18; spx 8; EVar 20; EVar 21; EVar 22; EVar 23;
     EVar 24; EVar 25; ELit 0x148fc; EVar 27; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 36; EVar 37; EVar 38; EVar 39].

  Definition kn_stackN : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-6144513)) 6144513;   (* the ruled stack figure *)
     KWord (SA (EVar 0) 8) 8 (EVar 1);
     KRange (EVar 1) 0x7fff80000000 0x800000400000].

  Definition kn_mainN : list kentry := kn_stackN ++ kn_image.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Lemma len_avN : (1 <= length av <= 1024)%nat.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma evN_junk : forall i, (i < 32)%nat -> ev EN (8 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold EN. cbn [ev]. unfold valsN.
    change (8 + i)%nat with (length [sp0; p0N; p0N; auxvpN; rndN; tid; canary_w rdraw; secret_w rdraw] + i)%nat.
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
              first [ rewrite (evN_junk (n - 8)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact (me_ra _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ _ ME); cbn; (first [solve [liafast_keep_section; tauto] | tauto])
          | idtac ].

  Theorem main_regs_okN : regs_ok EN sr_mainN regs.
  Proof.
    pose proof Hlo. pose proof Hhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
  Qed.


  Lemma main_strN : forall k, (k < length av)%nat ->
    rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (exists t8, rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) + Z.of_nat (length (nth k av []))))
                         8 = Some t8).
  Proof.
    intros k Hk'. pose proof Hlo. pose proof Hhi.
    pose proof (lay_bsb_nw Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau ltac:(unfold sp_window_hi; lia)) as Hnw.
    pose proof (lay_bsb_len Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau) as Hbl.
    destruct (argv_ptr_bounds_at Sv48 inp mbase sp0 brk rdraw Hlau k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound inp mbase RPH ENT sp0 brk rdraw) as Hsb.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (argv_str_len inp Hva k Hk') as Hlen.
    pose proof (rdn_wmem_stack (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 rdraw) as Hw. unfold wmem in Hw.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by lia.
      rewrite Hw by lia. exact (read_argv_cstr727_k Sv48 (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
    - destruct (read_word_stack Sv48 (run_segments RSEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 brk rdraw k (length (nth k av [])) Hlau Hk' ltac:(lia) Hnw) as (t8 & Hl8 & Hr8).
      exists t8. rewrite w_add_nat in Hr8.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.


  Lemma keN0 : ev EN 0 = sp0. Proof. reflexivity. Qed.
  Lemma keN1 : ev EN 1 = p0N. Proof. reflexivity. Qed.
  Lemma keN3 : ev EN 3 = auxvpN. Proof. reflexivity. Qed.
  Lemma keN5 : ev EN 5 = tid. Proof. reflexivity. Qed.

  Lemma know_stackN : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) EN mem kn_stackN.
  Proof.
    pose proof Hlo. pose proof Hhi. pose proof Hal. pose proof len_avN as Hlen.
    destruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
    unfold kn_stackN, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?keN0, ?keN1;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      apply (main_entry_store_ok_win sp0 inp mbase rdraw tid regs mem ME); rewrite u_small by lia; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w (run_segments RSEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH ENT sp0 brk rdraw Hva Hvl Hlau ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - unfold p0N. lia.
  Qed.

  Lemma D_main_auxvpN : forall segs,
    rdn segs (D_main sp0 inp rdraw tid) (Z_to_bv 64 0x94500) 8
    = Some (word_to_le_bytes 8 auxvpN).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof (u64_range (in_hwcap inp)). pose proof Hlo. pose proof Hhi.
    unfold auxvpN, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.


  Lemma wseg_dataN {RCa1 : RunCtx}  : wseg_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x23000) 0x72000 = true.
  Proof. exact wseg_data. Qed.

  Lemma range_disjoint_subN : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
  Proof.
    intros lo n [c w] i H Hlo' Hhi'. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia_old.
  Qed.

  Lemma missb_subN : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
  Proof.
    intros lo n i H Hlo' Hhi'. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia_old | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia_old].
    apply forallb_forall. intros c Hc. apply (range_disjoint_subN lo n); [|lia_old|lia_old].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.

  Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x95000)%Z ->
    kentry_ok (run_segments RSEGS rc_inp rc_sp rc_mb) EN mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 inp rdraw tid i Hva); [lia | lia |].
    apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data sp0 inp mbase rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L (run_segments RSEGS rc_inp rc_sp rc_mb)); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L (run_segments RSEGS rc_inp rc_sp rc_mb)); try reflexivity.
  Lemma keN6 : ev EN 6 = canary_w rdraw. Proof. reflexivity. Qed.

  Lemma know_imageN : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) EN mem kn_image.
  Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5, ?keN6; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x23000) (Z_to_bv 64 (0x23000 + d)) 0x72000 m 0x23000 0x95000);
        [reflexivity | vm_cast_no_check (@eq_refl Z 0x95000%Z) | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_dataN (D_main_self sp0 inp rdraw tid).
    - kw_memN (main_entry_tid sp0 inp mbase rdraw tid HLO regs mem ME).
    - kw_dataN (D_main_canary sp0 inp rdraw tid).
    - kw_dataN (U7StartupFacts.D_main_guard_w sp0 inp rdraw tid).
    - kw_dataN D_main_auxvpN.
    - kw_dataN (D_main_pagesize sp0 inp rdraw tid Hva).
    - lia.
  Qed.

  Theorem main_know_okN : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) EN mem kn_mainN.
  Proof.
    unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
  Qed.


  Lemma evN_argc : ev EN 18 = argcN inp.
  Proof. change 18%nat with (8 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ _ ME). Qed.
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
