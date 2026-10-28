(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs El_defs El_throw_site.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Atp_kitu El_acc_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Str_tac.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Section A23.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Definition arr_iter_post (SITE D : Z) (XP : mem -> Z -> Prop) (XR : Z -> word -> Prop)
      (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' =>
      (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
         ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom usegs)
         /\ munch [(q - 16 - D, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
         /\ ttype (ae_T E 1) = t_arr)
      \/ (exists x1 t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 t3 t4 t5 t6 m' (junk : list byte),
         ms' = MS (mkR x1 (Z_to_bv 64 (q - 16 - D)) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 SITE) fc None m' (seg_rom usegs)
         /\ rw_cells usegs m' (q + -16) [CB 8 junk; C8 ra]
         /\ munch [(q - 16 - D, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (q + -16)
         /\ XP m' (q + -16) /\ XR (q + -16) xs1
         /\ ttype (ae_T E 1) <> t_arr).

  Lemma begin_spec : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node lo : Z),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m ->
    stk usegs m lo q -> ae_lo E <= lo -> lo <= q - 16 -> q <= ae_B E -> q mod 16 = 0 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    evt usegs (arr_iter_post 0x3d968 0 xp_none xr_none ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 node) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_BEGIN) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros AI ROOT HEAP MI ST LOLO LOQ QB Q16 N0 N1 QD.
    destruct (acc_facts E OK s m HEAP) as ((T0 & TH & T8) & (S0 & SH) & (NR & SNR) & (CEIL & DB & B63 & D8) & TIR & EL).
    pose proof alloc_ceiling_range as CR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT. unfold EL_BEGIN. clear PTRB SBUFB HEAP.
    pose proof (length_map (Z_to_bv 64) (ae_tws E)) as LMT.
    pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step.
    astep. step. if_lia.
    zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
    astep. step. acc_tix E 252224.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDB.
    astep. step. step. if_cases K; zify_cond K; rewrite ?a_u8_small, ?a_u64_small in K by lia.
    - apply (proj1 (rw_cells_app _ _ [_] _)) in FR. destruct FR as [FR0 FR1].
      destruct (rw_cells_forget _ _ _ _ FR0) as [j0 FR0']. cbn [cells_size csize Nat.add] in FR0'.
      lazymatch type of FR1 with rw_cells usegs ?mx _ [?c1] =>
        assert (FRJ : rw_cells usegs mx (q + -16) [CB 8 j0; c1])
          by (apply (proj2 (rw_cells_app _ _ [_] _)); split; [exact FR0'| exact FR1])
      end.
      apply evt_done. unfold arr_iter_post. right. do 27 eexists.
      split; [atp_st_eq_goal|].
      try (replace (q - 16 - 0) with (q + -16) by lia).
      split; [exact FRJ|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [exact I|]. split; [exact I|]. unfold t_arr; lia.
    - astep. astep. astep. astep. astep. step. release_frame FR ST q. step.
      apply evt_done. unfold arr_iter_post. left. do 16 eexists.
      split; [atp_st_eq_goal|].
      try (replace (q - 16 - 0) with (q + -16) by lia).
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      unfold t_arr; lia.
  Qed.

  Lemma end_spec : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node lo : Z),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m ->
    stk usegs m lo q -> ae_lo E <= lo -> lo <= q - 80 -> q <= ae_B E -> q mod 16 = 0 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    evt usegs (arr_iter_post 0x3f010 64 xp_end xr_end ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 node) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_END) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros AI ROOT HEAP MI ST LOLO LOQ QB Q16 N0 N1 QD.
    destruct (acc_facts E OK s m HEAP) as ((T0 & TH & T8) & (S0 & SH) & (NR & SNR) & (CEIL & DB & B63 & D8) & TIR & EL).
    pose proof alloc_ceiling_range as CR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    clear HEAP.
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT. unfold EL_END. clear PTRB SBUFB.
    pose proof (length_map (Z_to_bv 64) (ae_tws E)) as LMT.
    pose proof (munch_refl [(q - 16 - 64, q)] m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [8; 8; 8; 4; 4; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step.
    astep. step. if_lia.
    zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
    astep. step. acc_tix E 0x3d9d0.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDB.
    astep. step. step. if_cases K; zify_cond K.
    - lstep. lstep. astep. lstep. astep. step.
      step. carve_frame 32%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 32 junk0 [] [8; 8; 8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
      lstep. lstep. step. astep. astep.
      astep. step. if_lia. step. if_lia.
      pose proof FR0 as FRX. apply (proj1 (rw_cells_app _ _ [_] _)) in FRX. destruct FRX as [_ FRX]. cbn [cells_size csize Nat.add] in FRX.
      replace (q + -80 + Z.of_nat 8) with (q + -16 - 56) in FRX by lia.
      pose proof FR as FRE. apply (proj1 (rw_cells_app _ _ [_; _; _] _)) in FRE. destruct FRE as [_ FRE]. cbn [cells_size csize Nat.add] in FRE.
      apply (proj1 (rw_cells_app _ _ [_] _)) in FRE. destruct FRE as [FRE _].
      replace (q + -48 + Z.of_nat 24) with (q + -16 - 8) in FRE by lia.
      pose proof FR as FRR. apply (proj1 (rw_cells_app _ _ [_; _; _; _; _] _)) in FRR. destruct FRR as [FRL FRR]. cbn [cells_size csize Nat.add] in FRR.
      replace (q + -48 + Z.of_nat 32) with (q + -16) in FRR by lia.
      apply (proj1 (rw_cells_app _ _ [_] _)) in FRR. destruct FRR as [FRS FRA].
      destruct (rw_cells_forget _ _ _ _ FRS) as [js FRS']. cbn [cells_size csize Nat.add] in FRS'.
      pose proof (proj2 (rw_cells_app _ _ [CB 8 js] [C8 ra]) (conj FRS' FRA)) as FRT.
      release_frame FR0 ST (q + -48). release_frame FRL ST (q + -16).
      apply evt_done. right. do 27 eexists. split; [atp_st_eq_goal|].
      split; [exact FRT|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      unfold xp_end, xp_err, xr_end, wz. split; [split; [exists 17; split; [lia| exact FRE]| do 2 eexists; exact FRX]|].
      split; [f_equal; lia| unfold t_arr; exact K].
    - astep. step. step. lstep. lstep. step. lstep. astep. step.
      step. carve_frame 32%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 32 junk0 [] [8; 8; 8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
      lstep. lstep. step. astep. astep.
      astep. step. if_lia. step. if_lia.
      step. step. if_lia.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
      step. astep. step. acc_tix E 0x3ef84.
      clear RDB. pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDB.
      astep. rewrite K.
      astep. astep. step.
      if_false.
      astep. astep. astep. astep. step.
      if_true.
      astep. astep. astep. astep. astep. step.
      if_false.
      step. step. if_lia.
      zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
      step. step. acc_tix E 0x3efe4.
      assert (RD4 : ov_read_bytes usegs m2 (wa (ae_TAPE E + 8 * 1)) 4 = Some (le4 (Z_to_bv 64 (ae_T E 1)))).
      { rewrite (bytes_at_read usegs m2 (ae_TAPE E) _ (8 * 1) 4 TAPEB); [| lia| rewrite u64s_length, length_map; lia]. f_equal.
        change (Z.to_nat (8 * 1)) with (8 * 1)%nat.
        match goal with |- firstn 4 ?X = _ => replace (firstn 4 X) with (firstn 4 (firstn 8 X)) by (rewrite firstn_firstn; reflexivity) end.
        rewrite (u64s_read _ 1) by (rewrite length_map; lia).
        unfold Tf. rewrite (map_nth (Z_to_bv 64)). unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes firstn]. reflexivity. }
      astep. step.
      astep. astep. step. step. step. astep. step.
      replace (ret_pc (Z_to_bv 64 0x3da0c)) with (Z_to_bv 64 0x3da0c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step. step. astep. step.
      release_frame FR0 ST (q + -48). release_frame FR ST q.
      apply evt_done. left. do 16 eexists. split; [atp_st_eq_goal|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| unfold t_arr; exact K].
  Qed.
End A23.
End WithCeiling0.
