(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_sec_defs R_mmapordie R_secalloc R_comballoc2 R_asan_defs R_allocate1 RT_state RT_rep RT_frame RT_trans RT_maltail RT_freelift RT_init RT_malcore_stmt RT_sys_stmt RT_vis RT_malsec_state RT_malsec_front.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Section FrontCps.
Variables (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z) (gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (n lo : Z).
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis Hn : 64512 < n <= 0x20001000.
Hypothesis Hcr : mcost n <= credit Σ.
Hypothesis HA : ART_A Σ mX.
Hypothesis MI : mem_inv bsegs mX.
Hypothesis ST : stk bsegs mX lo (B + -144).
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 16 <= USTACK_TOP.
Hypothesis GN : grant_node.

#[local] Notation fpost := (front_post B gp (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
                             (Z_to_bv 64 7) (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) F fc n lo mX).

Definition fK (P : Z) (ms' : machine_state) : Prop :=
  exists ms0, fpost ms0 /\ ms' = nretA ms0 (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (smsz n))]).

Lemma smsz_sa : smsz n = sa_msz (needed2 n) /\ roundup4k (sa_msz (needed2 n)) = smsz n /\ smsz n mod 4096 = 0.
Proof using Hn.
  pose proof (msec_size n Hn) as (K1 & _ & _ & K4).
  assert (E : smsz n = sa_msz (needed2 n)) by (unfold smsz, sa_msz, needed2, pg_up, roundup4k; rewrite K4; reflexivity).
  assert (M : smsz n mod 4096 = 0).
  { unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists ((needed n + rz_size n + 4095) / 4096 + 1). lia. }
  split; [exact E|]. split; [rewrite <- E; apply roundup4k_id; exact M | exact M].
Qed.

Lemma fc_evt : cps bsegs (ASTA RTA Σ PMc (eq (core_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX))) (ASTA RTA Σ PMc fpost).
Proof using MST Hn HA MI ST LOW LOR SPT.
  assert (W1 : forall ms, eq (core_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX) ms -> evt bsegs fpost ms)
    by (intros ms <-; exact (fs_evt Σ mX B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n lo Hn HA MI ST LOW LOR SPT)).
  exact (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1).
Qed.

Lemma fc_grant : cps bsegs (ASTA RTA Σ PMc fpost)
                   (fun c => exists P, sgrant_ok Σ P (smsz n) /\ ASTA RTA (sgΣ Σ P n) PMc (fK P) c).
Proof using FDO MST Hn Hcr HA GN.
  pose proof smsz_sa as (E1 & E2 & E3). pose proof (ART_wf Σ mX HA) as HW.
  pose proof (sec_eager_room Σ n HW ltac:(lia) Hcr) as (R1 & R2).
  pose proof (msec_size n Hn) as (K1 & K2 & K3 & K4).
  pose proof HW as (_ & _ & _ & (_ & HN & _) & _).
  assert (Hpos : 0 < smsz n) by (rewrite E1; unfold sa_msz; pose proof (roundup4k_facts (needed2 n) ltac:(lia)); lia).
  assert (Hle : smsz n <= 2 ^ 32) by (rewrite E1; unfold sa_msz; pose proof (roundup4k_facts (needed2 n) ltac:(lia)); lia).
  apply (GN Σ (fun P => sgΣ Σ P n) PMc fpost fK (smsz n) FDO MST HW Hpos E3 Hle).
  - destruct HN as [X|X]; rewrite X in R2; lia.
  - intros P. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite rt_maps_sg; apply Permutation_refl|].
    rewrite rt_eager_sg. destruct HN as [X|X]; rewrite X in R2; lia.
  - intros ms HP. pose proof HP as (m1 & _ & _ & _ & (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & m' & -> & _)).
    split; [reflexivity|].
    split; [transitivity (Z_to_bv 64 (roundup4k (sa_msz (needed2 n)))); [reflexivity | rewrite E2; reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros P _. exists (MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (B + -192)) - 96)) gp (Z_to_bv 64 tpA)
                          t0' t1' t2' a6' (sa_msz (needed2 n)) (Z_to_bv 64 sec_name) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (rz_size n))
                          (Z_to_bv 64 8) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 7) (Z_to_bv 64 7) (Z_to_bv 64 (l_T (lay Σ)))
                          (Z_to_bv 64 1) t3' t4' t5' t6') F (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None m' (seg_rom bsegs)).
    split; [exact HP | reflexivity].
Qed.

Lemma A_bytes_rtA_allow' : forall Σ0, layout_ok (lay Σ0) -> A_bytes (aw Σ0) <= CREDIT0 ->
  A_bytes (rtA_allow Σ0) <= CREDIT0 + 2 ^ 36 + 2 ^ 35.
Proof.
  intros Σ0 HL Haw. unfold rtA_allow. rewrite !A_bytes_app.
  pose proof (A_bytes_allow_main (lay Σ0) HL) as H1.
  assert (H2 : A_bytes (l_al0 (lay Σ0)) <= 2 ^ 36).
  { unfold layout_ok in HL. destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & H & _). exact H. }
  lia.
Qed.

Definition fA (P : Z) (ms : machine_state) : Prop :=
  exists ms0 mo, (ARTM_A (sgΣ Σ P n) mo /\ PMc mo) /\ fK P ms0 /\ revealed (rtA_allow Σ) (shw P n :: rtA_allow Σ) mo ms0 ms
    /\ (forall a, HID (rtA_allow Σ) mo a = true -> ms_mem ms0 a = None /\ SEGTOP_A <= bv_unsigned a)
    /\ (forall a, HID (shw P n :: rtA_allow Σ) mo a = true -> ms_mem ms a = None).

Lemma fc_allow : forall P, sgrant_ok Σ P (smsz n) ->
  cps bsegs (ASTA RTA (sgΣ Σ P n) PMc (fK P)) (ASTA RTA (saΣ Σ P n) PMc (fA P)).
Proof using Hn Hcr HA.
  intros P (HG & _). pose proof smsz_sa as (E1 & E2 & E3). pose proof (ART_wf Σ mX HA) as HW.
  pose proof (msec_size n Hn) as (K1 & K2 & K3 & K4).
  pose proof (sec_eager_room Σ n HW ltac:(lia) Hcr) as (R1 & R2).
  pose proof HW as (HL & _ & _ & (_ & HN & _) & _ & _ & (B1 & _ & B3 & _) & _).
  pose proof (A_bytes_rtA_allow' Σ HL ltac:(lia)) as HAB.
  unfold grant_ok in HG. destruct HG as (G1 & G2 & G3 & G4 & G5).
  unfold l_ACEIL, STACK_WIN in G3. pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  unfold sp_window_lo, sp_window_hi in *.
  assert (Hpos : 0 < smsz n) by (rewrite E1; unfold sa_msz; pose proof (roundup4k_facts (needed2 n) ltac:(lia)); lia).
  assert (Hle : smsz n <= 2 ^ 32) by (rewrite E1; unfold sa_msz; pose proof (roundup4k_facts (needed2 n) ltac:(lia)); lia).
  assert (HX : A_wf [shw P n] /\ A_bytes [shw P n] <= 2 ^ 30).
  { split.
    - unfold A_wf. apply Forall_cons; [|apply Forall_nil]. unfold shw, page_size. cbn [fst snd].
      split; [|split; [unfold pg_dn; apply Z_mod_mult | unfold pg_up; apply Z_mod_mult]].
      unfold pg_dn, pg_up, shad, SHB.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - unfold shw. cbn [A_bytes fst snd]. unfold pg_dn, pg_up, shad, SHB.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  destruct HX as (HXw & HXb).
  unfold ASTA. cbn [rt_allow ARTM RTA]. rewrite rtA_allow_sa, rtA_allow_sg.
  eapply (cps_conseq bsegs); [apply (ast_allow_x bsegs SEGTOP_A (rtA_allow Σ) [shw P n]) | intros c Hc; exact Hc |].
  - exact HXw.
  - intros mo (HM & _). pose proof HM as (_ & _ & Elim & Heu & _). rewrite Elim. rewrite rt_eager_sg in Heu.
    unfold E0_MAX, VMLIMIT, CREDIT0 in *. destruct HN as [X|X]; rewrite X in R2; lia.
  - intros c Hc. exact Hc.
Qed.

Theorem fc_front : cps bsegs (ASTA RTA Σ PMc (eq (core_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
  (fun c => exists P, sgrant_ok Σ P (smsz n) /\ ASTA RTA (saΣ Σ P n) PMc (fA P) c).
Proof using FDO MST Hn Hcr HA MI ST LOW LOR SPT GN.
  eapply (cps_seq bsegs); [exact fc_evt|]. eapply (cps_seq bsegs); [exact fc_grant|].
  apply (cps_ex bsegs). intros P T c (Hg & Hc) Hk.
  apply (fc_allow P Hg T c Hc). intros c' Hc'. apply Hk. exists P. split; [exact Hg | exact Hc'].
Qed.
End FrontCps.
