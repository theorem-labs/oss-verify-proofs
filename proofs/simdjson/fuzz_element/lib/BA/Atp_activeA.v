(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_activewA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SJ_W : list (Z * Z) := [(0x6a6340, 0x6a6348); (0x6a6360, 0x6a6362); (0x6a63e0, 0x6a640c); (0x6a6440, 0x6a6442)].

Lemma lib_in_fp : forall x, (0x6a6340 <= x < 0x6a6348) \/ (0x6a6360 <= x < 0x6a6368) \/ (0x6a63e0 <= x < 0x6a6410) \/ (0x6a6440 <= x < 0x6a6448) ->
  in_ranges LIB_FP x.
Proof.
  intros x H. unfold in_ranges, LIB_FP.
  destruct H as [H|[H|[H|H]]];
    [exists 0x6a6340, 0x6a6348| exists 0x6a6360, 0x6a6368| exists 0x6a63e0, 0x6a6410| exists 0x6a6440, 0x6a6448];
    (split; [cbn [In]; tauto| exact H]).
Qed.

Lemma sj_lib_loc : fp_local LIB_FP sj_lib.
Proof.
  intros m m' H AG.
  assert (AGZ : forall lo hi, (forall x, lo <= x < hi -> in_ranges LIB_FP x) -> agree_on (fun x => lo <= x < hi) m m').
  { intros lo hi HR a Ha. apply AG. apply HR. exact Ha. }
  destruct H as [(H1 & H2 & H3 & H4)|(H1 & H2 & H3 & H4)]; [left| right].
  all: split; [apply (rw_cells_agree_nw asegs m m' _ _ H1); apply AGZ; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply lib_in_fp; lia|].
  all: split; [apply (rw_cells_agree_nw asegs m m' _ _ H2); apply AGZ; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply lib_in_fp; lia|].
  all: split; [apply (rw_cells_agree_nw asegs m m' _ _ H3); apply AGZ; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply lib_in_fp; lia|].
  all: apply (rw_cells_agree_nw asegs m m' _ _ H4); apply AGZ; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply lib_in_fp; lia.
Qed.

Lemma lib1_loc : fp_local LIB_FP lib1.
Proof.
  intros m m' (H1 & H2 & H3 & H4) AG.
  assert (AGZ : forall lo hi, (forall x, lo <= x < hi -> in_ranges LIB_FP x) -> agree_on (fun x => lo <= x < hi) m m').
  { intros lo hi HR a Ha. apply AG. apply HR. exact Ha. }
  split; [apply (rw_cells_agree_nw asegs m m' _ _ H1); apply AGZ; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply lib_in_fp; lia|].
  split; [apply (rw_cells_agree_nw asegs m m' _ _ H2); apply AGZ; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply lib_in_fp; lia|].
  split; [apply (rw_cells_agree_nw asegs m m' _ _ H3); apply AGZ; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply lib_in_fp; lia|].
  apply (rw_cells_agree_nw asegs m m' _ _ H4); apply AGZ; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply lib_in_fp; lia.
Qed.

Section ActiveCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition getact_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> sj_lib m ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= USTACK_TOP -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                       t3 t4 t5 t6 F fc e_getact m)))
    (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SJ_ACTIVE) m' ms
         /\ rt_after RT Σ (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) SJ_W m m' /\ lib1 m')).

Theorem getact_ok : getact_cps.
Proof using AF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST LIB0 ART0 MI0 ST0 LOW LOR SPT FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (W1 : evt asegs (ga_post ra usp gp (tp) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_getact m)).
  { rewrite ESP. destruct LIB0 as [L0|L1]; [apply ga_walk_fresh| apply ga_walk_init]; try assumption; ul. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1); intros ms (m1 & _ & E1 & _); rewrite E1; exact FRM].
  eapply ASTA_conseq; [exact Hc1|]. intros ms (m1 & RS1 & _ & MU1 & WM1 & MI1 & ST1 & LIB1). exists m1.
  split; [rewrite ESP; exact RS1|].
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (usp - 32) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. unfold ga_W. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|].
    repeat (split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|]). exact I. }
  split; [split; [exact ART1| split; [exact MI1| split; [exact WM1| exact ST1]]]|].
  split; [| exact LIB1].
  intros a Ha Hout.
  pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
  apply MU1. unfold ga_W. cbn [outside].
  split; [clear - SPL LOW LOR; ul|].
  unfold SJ_W in Hout. cbn [outside] in Hout. destruct Hout as (O1 & O2 & O3 & O4 & _).
  split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4| exact I].
Qed.

End ActiveCPS.
