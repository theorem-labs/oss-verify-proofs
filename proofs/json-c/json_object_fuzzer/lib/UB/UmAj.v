(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOpO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Upt0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Upt0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBv7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q1u2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1u2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkRc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkRc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMt2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMt2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBMn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UohA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UohA.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition zblk (b : block) : Z * Z := (blk_addr b, blk_size b).

Definition zin_block (LB : list (Z * Z)) (a : Z) : Prop :=
exists b, In b LB /\ fst b <= a < fst b + snd b.

Fixpoint zlb_remove (p : Z) (LB : list (Z * Z)) : list (Z * Z) :=
match LB with
| [] => []
| b :: LB' => if Z.eqb (fst b) p then LB' else b :: zlb_remove p LB'
end.

#[using="Type"] Lemma zlb_remove_perm : forall LB p n,
List.NoDup (map fst LB) -> In (p, n) LB -> Permutation LB ((p, n) :: zlb_remove p LB).
Proof.
induction LB as [|b LB IH]; intros p n ND Hin; [destruct Hin|].
cbn [map] in ND. inversion ND as [|x l Hni ND']; subst. cbn [zlb_remove].
destruct Hin as [->|Hin].
- cbn [fst]. rewrite Z.eqb_refl. apply Permutation_refl.
- destruct (Z.eqb_spec (fst b) p) as [E|NE].
+ exfalso. apply Hni. rewrite E. apply in_map_iff. exists (p, n). split; [reflexivity| exact Hin].
+ eapply Permutation_trans; [apply perm_skip; apply (IH p n ND' Hin)| apply perm_swap].
Qed.

#[using="Type"] Lemma bptr_eqb_true_iff p q : bptr_eqb p q = true <-> p = q.
Proof.
unfold bptr_eqb. rewrite andb_true_iff, QSfG.Mq2.aptr_eqb_eq, Z.eqb_eq. destruct p, q; cbn; split; [intros [-> ->]; reflexivity| intros E; injection E; auto].
Qed.

#[using="Type"] Lemma lb_remove_split : forall (b0 : block) LB0,
In b0 LB0 -> List.NoDup (map blk_id LB0) ->
exists l1 l2, LB0 = l1 ++ b0 :: l2 /\ lb_remove (blk_id b0) LB0 = l1 ++ l2.
Proof.
intros b0 LB0. induction LB0 as [|b LB IH]; intros Hin ND; [destruct Hin|].
cbn [map] in ND. inversion ND as [|x l Hni ND']; subst. unfold lb_remove. rewrite filter_cons.
destruct Hin as [->|Hin].
- destruct (decide _) as [D|D].
{ exfalso. revert D. rewrite (proj2 (bptr_eqb_true_iff _ _) eq_refl). cbn. exact (fun x => x). }
exists [], LB. split; [reflexivity|]. cbn [app].
clear IH ND D. induction LB as [|b LB IH]; [reflexivity|].
cbn [map] in Hni, ND'. inversion ND'; subst. rewrite filter_cons.
destruct (decide _) as [D|D].
+ f_equal. apply IH; [intros H'; apply Hni; right; exact H'| assumption].
+ exfalso. apply Hni. left. destruct (bptr_eqb (blk_id b) (blk_id b0)) eqn:E; [| exfalso; apply D; exact I].
apply bptr_eqb_true_iff in E. exact E.
- destruct (IH Hin ND') as (l1 & l2 & E1 & E2).
destruct (decide _) as [D|D].
+ exists (b :: l1), l2. rewrite E1 at 1. split; [reflexivity|]. cbn [app]. f_equal. unfold lb_remove in E2. exact E2.
+ exfalso. apply Hni. destruct (bptr_eqb (blk_id b) (blk_id b0)) eqn:E; [| exfalso; apply D; exact I].
apply bptr_eqb_true_iff in E. rewrite E. apply in_map. exact Hin.
Qed.

#[using="Type"] Lemma ap_remove_perm : forall c l, In c l -> Permutation l (c :: ap_remove c l).
Proof.
induction l as [|y l IH]; intros Hin; [destruct Hin|]. cbn [ap_remove].
destruct (QSfG.Mq2.aptr_eqb_spec y c) as [->|NE]; [apply Permutation_refl|].
destruct Hin as [->|Hin]; [congruence|].
eapply Permutation_trans; [apply perm_skip; apply IH; exact Hin| apply perm_swap].
Qed.

#[using="Type"] Lemma ap_remove_sub : forall c l x, In x (ap_remove c l) -> In x l.
Proof.
induction l as [|y l IH]; intros x Hin; [destruct Hin|]. cbn [ap_remove] in Hin.
destruct (aptr_eqb y c); [right; exact Hin|]. destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; exact Hin].
Qed.

#[using="Type"] Lemma ap_remove_nodup : forall c l, List.NoDup l -> List.NoDup (ap_remove c l).
Proof.
induction l as [|y l IH]; intros ND; [constructor|]. inversion ND; subst. cbn [ap_remove].
destruct (aptr_eqb y c); [assumption|]. constructor; [| apply IH; assumption].
intros Hin. apply H1. apply (ap_remove_sub c). exact Hin.
Qed.

#[using="Type"] Lemma blk_addr_nodup : forall (LB0 : list block),
List.NoDup (map blk_id LB0) ->
(forall b1 b2, In b1 LB0 -> In b2 LB0 -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1) ->
Forall (fun b => 1 <= blk_size b) LB0 ->
List.NoDup (map blk_addr LB0).
Proof.
induction LB0 as [|b LB IH]; intros ND DJ SZ; [constructor|].
cbn [map] in ND |- *. inversion ND as [|x l Hni ND']; subst. inversion SZ as [|y l' SZb SZ']; subst.
constructor.
- intros Hin. apply in_map_iff in Hin as (b' & Ea & Hin').
assert (NE : blk_id b <> blk_id b') by (intros E; apply Hni; rewrite E; apply in_map; exact Hin').
pose proof (DJ b b' (or_introl eq_refl) (or_intror Hin') NE) as D.
pose proof (proj1 (Forall_forall _ _) SZ' b' Hin') as S'. cbn beta in S', SZb. rewrite Ea in D. lia.
- apply IH; [exact ND'| intros b1 b2 H1 H2; apply DJ; right; assumption| exact SZ'].
Qed.

#[using="Type"] Lemma wr_at_sub : forall segs m A N a n,
wr_at segs m A N -> A <= a -> a + n <= A + N -> wr_at segs m a n.
Proof.
intros segs m A N a n (H0 & H1 & H) Ha Hn. split; [lia|]. split; [lia|].
intros i Hi. replace (a + i) with (A + (a - A + i)) by lia. apply H. lia.
Qed.

Record hstate := mkHS { hs_s : PState; hs_L : mled }.

Definition RHEX_GOT : Z := 0x658d8.
Definition RHEX_PTR : Z := 0x66a30.
Definition RHEX_STR : Z := 0x12b12.
Definition HCELLS (m : mem) : Prop :=
bytes_at rsegs m (RATP - 16) (le8 rc_canary)
/\ bytes_at rsegs m RHEX_GOT (le8 (wz RHEX_PTR))
/\ bytes_at rsegs m RHEX_PTR (le8 (wz RHEX_STR)).

#[using="Type"] Lemma HCELLS_pres : forall LB SP m m', rheap_pres LB SP m m' -> HCELLS m -> HCELLS m'.
Proof.
intros LB SP m m' PRES (C1 & C2 & C3).
split; [|split]; (eapply rheap_pres_bytes_at; [exact PRES| eassumption|]); right; left; rewrite length_le8;
unfold RATP, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RHEX_GOT, RHEX_PTR; cbn; lia.
Qed.

Definition HEAPc (B : Z) (A : hstate) (LB : list (Z * Z)) (m : mem) (md : Model) : Prop :=
exists LB0 : list block,
Permutation LB (map zblk LB0)
/\ RHEAP (hs_s A) LB0 m
/\ mem_inv rsegs m
/\ HSIM (hs_s A) (hs_L A) LB0
/\ KL (hs_L A) (ps_brk (hs_s A)) md
/\ Permutation (ld_live (hs_L A)) (map blk_slot LB0)
/\ List.NoDup (ld_live (hs_L A))
/\ Forall (fun b => 1 <= blk_size b) LB0
/\ rauxv_ok m B
/\ HCELLS m.

Section Plumb.
Variable segs : list Segment.

#[using="Type"] Lemma implM_get_inv {A} (f : PState -> Ql2m.Mq3.M PState A) s Q ms :
implM segs (mbind mget f) s Q ms -> implM segs (f s) s Q ms.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma implM_upd_ret_inv {A} (g : PState -> PState) (v : A) s Q ms :
implM segs (mbind (mupd g) (fun _ => mret v)) s Q ms -> evt segs (Q v (g s)) ms.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma implM_upd_inv (g : PState -> PState) s Q ms :
implM segs (mupd g) s Q ms -> evt segs (Q tt (g s)) ms.
Proof. intros H. exact H. Qed.
End Plumb.

Definition rmalloc_stmt_at (pc : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM rsegs (raw_malloc n) s
(rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition rfree_stmt_at (pc : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM rsegs (raw_free p) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition rfree_null_stmt_at (pc : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
a0 = Z_to_bv 64 0 ->
evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

#[using="Type"] Lemma rmalloc_stmt_at_sym : rmalloc_stmt -> rmalloc_stmt_at RMALLOC_SYM. Proof. exact (fun H => H). Qed.
#[using="Type"] Lemma rfree_stmt_at_sym : rfree_stmt -> rfree_stmt_at RFREE_SYM. Proof. exact (fun H => H). Qed.
#[using="Type"] Lemma rfree_null_at_sym : rfree_null_stmt_at RFREE_SYM. Proof. exact rfree_null_spec. Qed.

#[using="Type"] Lemma rfree_null_at_impl : rfree_null_stmt_at rfree_entry.
Proof. intros until m. intros ->. unfold rfree_entry. step. if_true. step. apply evt_done. reflexivity. Qed.

Section Core.
Variables (B MENTRY FENTRY : Z).
Hypothesis HM : rmalloc_stmt_at MENTRY.
Hypothesis HF : rfree_stmt_at FENTRY.
Hypothesis HFN : rfree_null_stmt_at FENTRY.
Hypothesis HC0 : rcalloc_stmt.

#[using="HM"] Theorem heapc_malloc :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (T : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word),
HEAPc B A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 12 /\ HEAPc B A' LB m' md')
\/ (r <> 0 /\ (exists junk, rw_cells rsegs m' r [CB (Z.to_nat n) junk]) /\ rblock_range r n
/\ HEAPc B A' ((r, n) :: LB) m' md') ) ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 MENTRY) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP ST Hlo1 Hlo2 HB ERR Htp Ha0 Hn K.
destruct A as [s L]. cbn [hs_s hs_L] in *.
destruct HP as (LB0 & PLB & RH & MI & CR & HKL & PLV & NDL & SZ & AUX & CAN).
assert (Uerr : (bv_unsigned tp + (-164)) = RATP - 164) by (rewrite Htp; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
pose proof (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 n lo B errv
RH AUX HB ST Hlo1 Hlo2 ltac:(rewrite Uerr; exact ERR) MI Htp Ha0 ltac:(lia)) as IMPL.
unfold raw_malloc in IMPL. apply implM_get_inv in IMPL. apply implM_bind_inv in IMPL.
destruct CR as (st & BL & LS & LB1 & PB1 & Est & INV & CORR0).
pose proof (cmalloc_ctreeI st L BL LS n INV (HSIM_live_sub L LB0 st BL LB1 PB1 CORR0 PLV) ltac:(lia)) as CT. rewrite Est in CT.
eapply (membed_realizes_KL rsegs (cmalloc (ps_m s) n) _ s _ _ md L T IMPL CT HKL).
intros [cs' oc] s' ms' L' md' Hleaf HPost CP Em Efa Eso HK' HV'. cbn [snd] in HPost.
apply implM_upd_ret_inv in Hleaf.
apply rz_evt; [exact (KL_model_ok _ _ _ HK')|].
eapply evt_mono; [exact Hleaf|]. intros ms2 PM. unfold RZ.
destruct PM as (u0 & u1 & u2 & ra0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & PRES & _ & _ & RES).
set (L'' := match oc with Some c => set_live (c :: ld_live L') L' | None => L' end).

rewrite <- Est in CP. destruct (cmalloc_leaf_INVL st L BL LS n L' cs' oc INV ltac:(lia) CP) as (_ & st1 & LS1 & Est1 & RES1).
assert (SIM' : forall LBn, RHEAP (set_m cs' s') LBn m' -> HSIM (set_m cs' s') L'' LBn).
{ intros LBn (stn & LBa & Pa & Estn & _ & HINVn). subst L''.
destruct oc as [c|].
- destruct RES1 as (off1 & _ & INV1 & _). apply HSIM_set_live.
exact (HSIM_intro ref_reserved (set_m cs' s') L' LBn stn LBa _ st1 L' _ LS1 Pa Estn HINVn Est1 INV1 eq_refl).
- exact (HSIM_intro ref_reserved (set_m cs' s') L' LBn stn LBa _ st1 L' _ LS1 Pa Estn HINVn Est1 RES1 eq_refl). }
assert (HK'' : KL L'' (ps_brk s') md') by (subst L''; destruct oc; [apply KL_set_live|]; exact HK').
first [pose proof (cpath_live _ _ _ _ CP) as LIVE' | pose proof (cpath_live CP) as LIVE'].
pose proof (HCELLS_pres _ _ _ _ PRES CAN) as CAN'.
destruct oc as [c|]; cbv beta iota in RES.
-
destruct RES as (Ar & junk & -> & RNG & RH' & BLK & _).
eapply (K _ m' md' (mkHS (set_m cs' s') L'') Ar errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ exists LB0. split; [exact PLB| exact PRES].
+ rewrite <- Uerr. exact ERR'.
+ right. split; [destruct RNG as (R1 & _); lia|]. split; [exists junk; exact BLK|]. split; [exact RNG|].
exists (((c, fresh_off cs' c n), Ar, n) :: LB0). cbn [hs_s hs_L map zblk blk_addr blk_size blk_slot blk_id fst snd ps_m ps_brk set_m].
splits.
* apply perm_skip. exact PLB.
* exact RH'.
* exact MI'.
* exact (SIM' _ RH').
* exact HK''.
* subst L''. cbn. rewrite LIVE'. apply perm_skip. exact PLV.
* subst L''. cbn. constructor; [| rewrite LIVE'; exact NDL]. exact HPost.
* constructor; [cbn; lia| exact SZ].
* exact AUX'.
* exact CAN'.
-
destruct RES as (-> & He & RH').
eapply (K _ m' md' (mkHS (set_m cs' s') L'') 0 errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ exists LB0. split; [exact PLB| exact PRES].
+ rewrite <- Uerr. exact ERR'.
+ left. split; [reflexivity|]. split; [exact He|].
exists LB0. cbn [hs_s hs_L ps_m ps_brk set_m]. pose proof (SIM' _ RH') as CR'. subst L''. splits; auto.
rewrite LIVE'. exact PLV. rewrite LIVE'. exact NDL.
Qed.

#[using="HC0"] Theorem heapc_calloc :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (T : TSet)
(A : hstate) (LB : list (Z * Z)) (cnt sz lo : Z) (errv : word),
HEAPc B A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 ->
(calloc_overflows cnt sz = false -> 1 <= cnt * sz < 2^64) ->
(forall ms' m' md' A' (r : Z) (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 12 /\ HEAPc B A' LB m' md')
\/ (r <> 0 /\ rw_cells rsegs m' r [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))] /\ rblock_range r (cnt * sz)
/\ calloc_overflows cnt sz = false /\ HEAPc B A' ((r, cnt * sz) :: LB) m' md') ) ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP ST Hlo1 Hlo2 HB ERR Htp Ha0 Ha1 Hcnt Hsz Hn K.
destruct A as [s L]. cbn [hs_s hs_L] in *.
destruct HP as (LB0 & PLB & RH & MI & CR & HKL & PLV & NDL & SZ & AUX & CAN).
assert (Uerr : (bv_unsigned tp + (-164)) = RATP - 164) by (rewrite Htp; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
pose proof (HC0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 cnt sz lo B errv
RH AUX HB ST Hlo1 Hlo2 ltac:(rewrite Uerr; exact ERR) MI Htp Ha0 Ha1 Hcnt Hsz) as IMPL.
unfold raw_calloc in IMPL. apply implM_get_inv in IMPL. apply implM_bind_inv in IMPL.
destruct CR as (st & BL & LS & LB1 & PB1 & Est & INV & CORR0).
pose proof (ccalloc_ctreeI st L BL LS cnt sz INV (HSIM_live_sub L LB0 st BL LB1 PB1 CORR0 PLV) ltac:(lia) ltac:(lia)) as CT. rewrite Est in CT.
eapply (membed_realizes_KL rsegs (ccalloc (ps_m s) cnt sz) _ s _ _ md L T IMPL CT HKL).
intros [cs' oc] s' ms' L' md' Hleaf HPost CP Em Efa Eso HK' HV'. cbn [snd] in HPost.
apply implM_upd_ret_inv in Hleaf.
apply rz_evt; [exact (KL_model_ok _ _ _ HK')|].
eapply evt_mono; [exact Hleaf|]. intros ms2 PM. unfold RZ.
destruct PM as (u0 & u1 & u2 & ra0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & PRES & _ & _ & RES).
set (L'' := match oc with Some c => set_live (c :: ld_live L') L' | None => L' end).

rewrite <- Est in CP. destruct (@ccalloc_leaf_INVL _ st L BL LS cnt sz L' cs' oc INV ltac:(lia) ltac:(lia) CP) as (_ & st1 & LS1 & Est1 & RES1).
assert (NOV : oc <> None -> calloc_overflows cnt sz = false).
{ intros Hoc. unfold ccalloc in CP. destruct (calloc_overflows cnt sz); [| reflexivity]. exfalso. inversion CP; subst. exact (Hoc eq_refl). }
assert (SIM' : forall LBn, RHEAP (set_m cs' s') LBn m' -> HSIM (set_m cs' s') L'' LBn).
{ intros LBn (stn & LBa & Pa & Estn & _ & HINVn). subst L''.
destruct oc as [c|].
- destruct RES1 as (off1 & _ & INV1 & _). apply HSIM_set_live.
exact (HSIM_intro ref_reserved (set_m cs' s') L' LBn stn LBa _ st1 L' _ LS1 Pa Estn HINVn Est1 INV1 eq_refl).
- exact (HSIM_intro ref_reserved (set_m cs' s') L' LBn stn LBa _ st1 L' _ LS1 Pa Estn HINVn Est1 RES1 eq_refl). }
assert (HK'' : KL L'' (ps_brk s') md') by (subst L''; destruct oc; [apply KL_set_live|]; exact HK').
first [pose proof (cpath_live _ _ _ _ CP) as LIVE' | pose proof (cpath_live CP) as LIVE'].
pose proof (HCELLS_pres _ _ _ _ PRES CAN) as CAN'.
destruct oc as [c|]; cbv beta iota in RES.
-
destruct RES as (Ar & -> & RNG & RH' & BLK).
eapply (K _ m' md' (mkHS (set_m cs' s') L'') Ar errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ exists LB0. split; [exact PLB| exact PRES].
+ rewrite <- Uerr. exact ERR'.
+ right. split; [destruct RNG as (R1 & _); lia|]. split; [exact BLK|]. split; [exact RNG|]. split; [apply NOV; discriminate|].
pose proof (Hn (NOV ltac:(discriminate))) as Hn1.
exists (((c, fresh_off cs' c (cnt * sz)), Ar, cnt * sz) :: LB0). cbn [hs_s hs_L map zblk blk_addr blk_size blk_slot blk_id fst snd ps_m ps_brk set_m].
splits.
* apply perm_skip. exact PLB.
* exact RH'.
* exact MI'.
* exact (SIM' _ RH').
* exact HK''.
* subst L''. cbn. rewrite LIVE'. apply perm_skip. exact PLV.
* subst L''. cbn. constructor; [| rewrite LIVE'; exact NDL]. exact HPost.
* constructor; [cbn; lia| exact SZ].
* exact AUX'.
* exact CAN'.
-
destruct RES as (-> & He & RH').
eapply (K _ m' md' (mkHS (set_m cs' s') L'') 0 errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ exists LB0. split; [exact PLB| exact PRES].
+ rewrite <- Uerr. exact ERR'.
+ left. split; [reflexivity|]. split; [exact He|].
exists LB0. cbn [hs_s hs_L ps_m ps_brk set_m]. pose proof (SIM' _ RH') as CR'. subst L''. splits; auto.
rewrite LIVE'. exact PLV. rewrite LIVE'. exact NDL.
Qed.

#[using="HF"] Theorem heapc_free :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (T : TSet)
(A : hstate) (LB : list (Z * Z)) (p n lo : Z) (errv : word),
HEAPc B A LB m md -> In (p, n) LB ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 p ->
(forall ms' m' md' A' (r : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LBx, Permutation (zlb_remove p LB) (map zblk LBx) /\ rheap_pres LBx (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv] ->
HEAPc B A' (zlb_remove p LB) m' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FENTRY) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP HIN ST Hlo1 Hlo2 HB ERR Htp Ha0 K.
destruct A as [s L]. cbn [hs_s hs_L] in *.
destruct HP as (LB0 & PLB & RH & MI & CR & HKL & PLV & NDL & SZ & AUX & CAN).
assert (Uerr : (bv_unsigned tp + (-164)) = RATP - 164) by (rewrite Htp; unfold RATP; rewrite unsigned_lit by lia; reflexivity).

assert (Hb0 : exists b0, In b0 LB0 /\ zblk b0 = (p, n)).
{ pose proof (Permutation_in _ PLB HIN) as H. apply in_map_iff in H as (b0 & E & Hin0). exists b0. auto. }
destruct Hb0 as (b0 & Hin0 & Eb0).
pose proof (RHEAP_blocks_nodup_proof _ _ _ RH) as NDI.
destruct (lb_remove_split b0 LB0 Hin0 NDI) as (l1 & l2 & ELB0 & ERM).
assert (NDA : List.NoDup (map fst LB)).
{ eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PLB|].
rewrite map_map. change (fun x => fst (zblk x)) with blk_addr.
apply blk_addr_nodup; [exact NDI| intros b1 b2 H1 H2 NE; exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ RH H1 H2 NE)| exact SZ]. }
assert (PRM : Permutation (zlb_remove p LB) (map zblk (lb_remove (blk_id b0) LB0))).
{ apply (Permutation_cons_inv (a:=(p, n))).
eapply Permutation_trans; [apply Permutation_sym; apply zlb_remove_perm; [exact NDA| exact HIN]|].
eapply Permutation_trans; [exact PLB|]. rewrite ERM, ELB0, !map_app. cbn [map]. rewrite Eb0.
apply Permutation_sym. apply Permutation_middle. }
destruct b0 as [[pb Ab] nb]. unfold zblk, blk_addr, blk_size in Eb0. cbn [fst snd] in Eb0. injection Eb0 as -> ->.
unfold blk_id in ERM, PRM. cbn [fst] in ERM, PRM.
set (c := fst pb).
assert (LIVEc : In c (ld_live L)).
{ eapply Permutation_in; [apply Permutation_sym; exact PLV|]. apply in_map_iff. exists (pb, p, n). split; [reflexivity| exact Hin0]. }
destruct CR as (st & BL & LS & LB1 & PB1 & Est & INV & CORR0).
assert (Hin1 : In (pb, p, n) LB1) by (eapply Permutation_in; [apply Permutation_sym; exact PB1| exact Hin0]).
destruct (HSIM_block st LB1 BL (pb, p, n) CORR0 Hin1) as (off & HkBL & _). unfold blk_slot, blk_size in HkBL. cbn [fst snd] in HkBL. fold c in HkBL.
pose proof (HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 pb p n lo B errv
RH Hin0 AUX HB ST Hlo1 Hlo2 ltac:(rewrite Uerr; exact ERR) MI Htp Ha0) as IMPL.
unfold raw_free in IMPL. apply implM_get_inv in IMPL. apply implM_bind_inv in IMPL.
pose proof (cfree_ctree st L BL LS c off n INV HkBL) as CT. rewrite Est in CT.
change (fst pb) with c in IMPL.
eapply (membed_realizes_KL rsegs (cfree (ps_m s) (Some c)) _ s _ _ md L T IMPL CT HKL).
intros cs' s' ms' L' md' Hleaf _ CP Em Efa Eso HK' HV'.
apply implM_upd_inv in Hleaf.
apply rz_evt; [exact (KL_model_ok _ _ _ HK')|].
eapply evt_mono; [exact Hleaf|]. intros ms2 PM. unfold RZ.
destruct PM as (u0 & u1 & u2 & ra0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & ERR' & AUX' & PRES & _ & _ & RH').
set (L'' := set_live (ap_remove c (ld_live L')) L').
rewrite <- Est in CP. destruct (cfree_leaf_INVL st L BL LS c off n L' cs' INV HkBL CP) as (_ & st1 & LS1 & Est1 & INV1).
assert (CR' : HSIM (set_m cs' s') L'' (lb_remove pb LB0)).
{ pose proof RH' as (stn & LBa & Pa & Estn & _ & HINVn). subst L''. apply HSIM_set_live.
exact (HSIM_intro ref_reserved (set_m cs' s') L' _ stn LBa _ st1 L' _ LS1 Pa Estn HINVn Est1 INV1 eq_refl). }
assert (HK'' : KL L'' (ps_brk s') md') by (subst L''; apply KL_set_live; exact HK').
first [pose proof (cpath_live _ _ _ _ CP) as LIVE' | pose proof (cpath_live CP) as LIVE'].
pose proof (HCELLS_pres _ _ _ _ PRES CAN) as CAN'.
eapply (K _ m' md' (mkHS (set_m cs' s') L'') ra0).
- repeat eexists.
- exact HV'.
- exact ST'.
- exists (lb_remove pb LB0). split; [exact PRM| exact PRES].
- rewrite <- Uerr. exact ERR'.
- exists (lb_remove pb LB0). cbn [hs_s hs_L ps_m ps_brk set_m]. splits.
+ exact PRM.
+ exact RH'.
+ exact MI'.
+ exact CR'.
+ exact HK''.
+ subst L''. cbn. rewrite LIVE'. apply (Permutation_cons_inv (a:=c)).
eapply Permutation_trans; [apply Permutation_sym; apply ap_remove_perm; exact LIVEc|].
eapply Permutation_trans; [exact PLV|]. rewrite ERM, ELB0, !map_app. cbn [map]. unfold blk_slot at 2. cbn [fst]. fold c.
apply Permutation_sym. apply Permutation_middle.
+ subst L''. cbn. rewrite LIVE'. apply ap_remove_nodup. exact NDL.
+ rewrite ERM. rewrite ELB0 in SZ. apply Forall_app in SZ as [S1 S2]. inversion S2; subst. apply Forall_app. auto.
+ exact AUX'.
+ exact CAN'.
Qed.

#[using="HFN"] Theorem heapc_free_null :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (T : TSet),
model_ok md -> a0 = Z_to_bv 64 0 ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)) md) T ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FENTRY) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until T. intros MOK Ha0 K. apply rz_evt; [exact MOK|].
eapply evt_mono; [exact (HFN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Ha0)|].
intros ms' ->. exact K.
Qed.

#[using="Type"] Lemma heapc_model_ok A LB m md : HEAPc B A LB m md -> model_ok md.
Proof. intros (LB0 & _ & _ & _ & _ & HK & _). exact (KL_model_ok _ _ _ HK). Qed.

#[using="Type"] Lemma heapc_mem_inv A LB m md : HEAPc B A LB m md -> mem_inv rsegs m.
Proof. intros (LB0 & _ & _ & MI & _). exact MI. Qed.

#[using="Type"] Lemma heapc_in_blk A LB m md a n : HEAPc B A LB m md -> In (a, n) LB ->
exists LB0 b0, In b0 LB0 /\ blk_addr b0 = a /\ blk_size b0 = n /\ RHEAP (hs_s A) LB0 m /\ Permutation LB (map zblk LB0).
Proof.
intros (LB0 & PLB & RH & _) HIN. pose proof (Permutation_in _ PLB HIN) as H. apply in_map_iff in H as (b0 & E & Hin0).
exists LB0, b0. unfold zblk in E. injection E as E1 E2. auto 6.
Qed.

#[using="Type"] Lemma heapc_blk A LB m md a n : HEAPc B A LB m md -> In (a, n) LB ->
0 <= n /\ a mod 16 = 0 /\ 0 < a /\ a + n <= alloc_ceiling /\ wr_at rsegs m a n
/\ (a + n <= RIMG_LO \/ RIMG_HI <= a).
Proof.
intros HP HIN. destruct (heapc_in_blk A LB m md a n HP HIN) as (LB0 & b0 & Hin0 & <- & <- & RH & _).
pose proof (RHEAP_block_range_proof _ _ _ _ RH Hin0) as (R1 & R2 & R3 & R4 & R5).
splits; auto.
destruct RH as (st & LBp & HPp & Hst & MR & [_ AR]).
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (INp : In b0 LBp) by (eapply Permutation_in; [apply Permutation_sym; exact HPp| exact Hin0]).
destruct (rblock_inside st LBp m b0 MF MR INp) as (r & g & idx & Hr & Hk & _ & LO & HI & _).
destruct MR as (_ & _ & _ & _ & _ & SH). destruct (SH _ _ Hr Hk) as [W _].
eapply wr_at_sub; [exact W| exact LO| exact HI].
Qed.

#[using="Type"] Lemma heapc_blk_slack A LB m md a n : HEAPc B A LB m md -> In (a, n) LB ->
exists junk, bytes_at rsegs m (a + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16.
Proof.
intros HP HIN. destruct (heapc_in_blk A LB m md a n HP HIN) as (LB0 & b0 & Hin0 & <- & <- & RH & _).
pose proof (RHEAP_block_range_proof _ _ _ _ RH Hin0) as (R1 & R2 & R3 & R4 & R5).
destruct RH as (st & LBp & HPp & Hst & MR & [_ AR]).
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (INp : In b0 LBp) by (eapply Permutation_in; [apply Permutation_sym; exact HPp| exact Hin0]).
destruct (rblock_inside st LBp m b0 MF MR INp) as (r & g & idx & Hr & Hk & _ & LO & HI & _ & _ & _ & IMG).
destruct MR as (WF & _ & _ & _ & _ & SH). destruct (SH _ _ Hr Hk) as [W _].
destruct WF as (_ & WF2 & _). pose proof (WF2 _ _ Hr) as (_ & AL & _).
pose proof (QoCS.round_up_pg_mod (r_len r)) as RM. unfold PGSZ in RM.
set (k := (16 - blk_size b0 mod 16) mod 16).
assert (Hk16 : 0 <= k < 16) by (subst k; apply Z.mod_pos_bound; lia).
assert (FIT : blk_addr b0 + blk_size b0 + k <= r_base r + round_up_pg (r_len r)).
{ subst k. pose proof (Z_div_mod_eq_full (blk_addr b0) 16). pose proof (Z_div_mod_eq_full (blk_size b0) 16). pose proof (Z.mod_pos_bound (blk_size b0) 16 ltac:(lia)).
pose proof (Z_div_mod_eq_full (r_base r) 4096). pose proof (Z_div_mod_eq_full (round_up_pg (r_len r)) 4096).
destruct (Z.eq_dec (blk_size b0 mod 16) 0) as [E|NE].
- rewrite E. change ((16 - 0) mod 16) with 0. lia.
- rewrite Z.mod_small by lia. nia. }
destruct (rwr_at_bytes_exist m (blk_addr b0 + blk_size b0) k) as (bs & Hlen & Hbs).
- eapply wr_at_sub; [exact W| lia| lia].
- lia.
- lia.
- exists bs. split; [exact Hbs|]. rewrite Hlen. rewrite Z2Nat.id by lia. reflexivity.
Qed.

#[using="Type"] Lemma heapc_blk_disjoint A LB m md a n a' n' : HEAPc B A LB m md ->
In (a, n) LB -> In (a', n') LB -> a <> a' -> a + n <= a' \/ a' + n' <= a.
Proof.
intros (LB0 & PLB & RH & _) H1 H2 NE.
pose proof (Permutation_in _ PLB H1) as I1. apply in_map_iff in I1 as (b1 & E1 & I1).
pose proof (Permutation_in _ PLB H2) as I2. apply in_map_iff in I2 as (b2 & E2 & I2).
unfold zblk in E1, E2. injection E1 as <- <-. injection E2 as <- <-.
apply (RHEAP_blocks_disjoint_proof _ _ _ _ _ RH I1 I2). intros E. apply NE.
pose proof (RHEAP_blocks_nodup_proof _ _ _ RH) as ND.
enough (b1 = b2) by (subst; reflexivity).
clear -ND I1 I2 E. induction LB0 as [|b LB IH]; [destruct I1|]. cbn [map] in ND. inversion ND; subst.
destruct I1 as [<-|I1], I2 as [<-|I2]; [reflexivity| | | apply IH; assumption].
- exfalso. apply H1. rewrite E. apply in_map. exact I2.
- exfalso. apply H1. rewrite <- E. apply in_map. exact I1.
Qed.

#[using="Type"] Lemma heapc_blk_nodup A LB m md : HEAPc B A LB m md -> List.NoDup (map fst LB).
Proof.
intros (LB0 & PLB & RH & _ & _ & _ & _ & _ & SZ & _).
eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PLB|].
rewrite map_map. change (fun x => fst (zblk x)) with blk_addr.
apply blk_addr_nodup; [exact (RHEAP_blocks_nodup_proof _ _ _ RH)| intros b1 b2 H1 H2 NE; exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ RH H1 H2 NE)| exact SZ].
Qed.

#[using="Type"] Lemma heapc_perm A LB LB' m md : HEAPc B A LB m md -> Permutation LB LB' -> HEAPc B A LB' m md.
Proof.
intros (LB0 & PLB & REST) HP. exists LB0. split; [| exact REST].
eapply Permutation_trans; [apply Permutation_sym; exact HP| exact PLB].
Qed.

#[using="Type"] Lemma heapc_model_frame A LB m md md' : HEAPc B A LB m md ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_halted md' = None -> HEAPc B A LB m md'.
Proof.
intros (LB0 & P1 & P2 & P3 & P4 & HK & REST) E1 E2 Hh. exists LB0. splits; auto; try tauto.
eapply KL_model_frame; eauto.
Qed.

#[using="Type"] Lemma heapc_canary A LB m md : HEAPc B A LB m md ->
bytes_at rsegs m RGOT_SSP (le8 (Z_to_bv 64 RSSP_GUARD)) /\
bytes_at rsegs m RSSP_GUARD (le8 rc_canary) /\
bytes_at rsegs m (RATP - 16) (le8 rc_canary).
Proof.
intros (LB0 & _ & RH & _ & _ & _ & _ & _ & _ & _ & CAN & _).
destruct RH as (st & LBp & _ & _ & MR & _). destruct MR as (_ & _ & GL & _). destruct GL as (_ & _ & _ & [[_ G1] _] & [[_ G2] _]).
cbn [cells_bytes cbytes app] in G1, G2. rewrite app_nil_r in G1, G2. auto.
Qed.

#[using="Type"] Lemma heapc_consts A LB m md : HEAPc B A LB m md ->
bytes_at rsegs m RHEX_GOT (le8 (wz RHEX_PTR)) /\ bytes_at rsegs m RHEX_PTR (le8 (wz RHEX_STR)).
Proof. intros (LB0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C). exact C. Qed.

Definition ralloc_zone (a : Z) : Prop :=
(RLIBC <= a < RLIBC + 0x68) \/ (RMLOCK <= a < RCTX + 928) \/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8)
\/ (RATP - 16 <= a < RATP - 8) \/ (RHEX_GOT <= a < RHEX_GOT + 8) \/ (RHEX_PTR <= a < RHEX_PTR + 8).

Definition client_may_write (LB : list (Z * Z)) (a : Z) : Prop :=
zin_block LB a \/ (alloc_ceiling <= a < B) \/ (RDATA_LO <= a < RIMG_HI /\ ~ ralloc_zone a).

Definition frameW (LB0 : list block) : list ivl :=
(alloc_ceiling, B) :: (RDATA_LO, RHEX_GOT) :: (RHEX_GOT + 8, RGOT_SSP) :: (RGOT_SSP + 8, RHEX_PTR) :: (RHEX_PTR + 8, RATP - 16)
:: (RATP - 8, RSSP_GUARD) :: (RSSP_GUARD + 8, RLIBC) :: (RLIBC + 0x68, RMLOCK) :: (RCTX + 928, RIMG_HI)
:: map (fun b => (blk_addr b, blk_addr b + blk_size b)) LB0.

#[using="Type"] Lemma outside_blocks : forall (LB0 : list block) a,
outside (map (fun b => (blk_addr b, blk_addr b + blk_size b)) LB0) a -> ~ in_block LB0 a.
Proof.
induction LB0 as [|b LB IH]; intros a H (b' & Hin & Hr); [destruct Hin|].
cbn [map outside] in H. destruct H as [H1 H2]. destruct Hin as [<-|Hin]; [exact (H1 Hr)|].
apply (IH a H2). exists b'. auto.
Qed.

#[using="Type"] Lemma frameW_outside : forall LB LB0 a, Permutation LB (map zblk LB0) -> alloc_ceiling <= B ->
outside (frameW LB0) a -> ~ client_may_write LB a.
Proof.
intros LB LB0 a PLB HB H [C|[C|[C NZ]]]; cbn [frameW outside] in H; destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HB0).
- destruct C as (b & Hin & Hr). apply (outside_blocks LB0 a HB0).
pose proof (Permutation_in _ PLB Hin) as Hin'. apply in_map_iff in Hin' as (b0 & <- & Hin0).
exists b0. split; [exact Hin0|]. unfold zblk in Hr. cbn [fst snd] in Hr. exact Hr.
- lia.
- unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR in *. lia.
Qed.

#[using="Type"] Lemma heapc_frame A LB m m' md : HEAPc B A LB m md ->
(forall a, 0 <= a < 2^64 -> ~ client_may_write LB a -> m' (wa a) = m (wa a)) ->
wmono rsegs m m' -> mem_inv rsegs m' ->
HEAPc B A LB m' md.
Proof.
intros (LB0 & PLB & RH & MI & CR & HK & PLV & NDL & SZ & AUX & CAN) CH WM MI'.
pose proof AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HBc & _).
assert (MU : munch (frameW LB0) m m').
{ intros x Hout. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
rewrite <- (Z_to_bv_bv_unsigned x). apply CH; [lia|]. eapply frameW_outside; [exact PLB| exact HBc| exact Hout]. }
assert (FW : Forall (rclient_write_ok2 LB0) (frameW LB0)).
{ unfold frameW. repeat apply Forall_cons.
1-7,9: left; unfold rclient_write_ok; cbn [fst snd]; unfold RLIBC, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR; first [left; lia | right; left; lia].
right; cbn [fst snd]; lia.
apply Forall_forall. intros iv Hin. apply in_map_iff in Hin as (b & <- & Hb). left. right; right. exists b. cbn [fst snd]. split; [exact Hb| lia]. }
exists LB0. splits; auto.
- eapply RHEAP_frame2; [exact RH| exact MU| exact WM| exact FW].
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
unfold frameW. repeat apply Forall_cons.
1-9: cbn [fst snd]; unfold RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RAUXV_CELL, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR; unfold alloc_ceiling in *; lia.
apply Forall_forall. intros iv Hin. apply in_map_iff in Hin as (b & <- & Hb). cbn [fst snd].
pose proof (RHEAP_block_range_proof _ _ _ _ RH Hb) as (R1 & R2 & R3 & R4 & R5). unfold RAUXV_CELL. unfold alloc_ceiling in *. lia.
-
assert (CHZ : forall a, RDATA_LO <= a < RIMG_HI -> ralloc_zone a -> m' (wa a) = m (wa a)).
{ intros a Ha Hz. apply CH; [unfold RDATA_LO, RIMG_HI in Ha; lia|]. intros [C|[C|[C NZ]]].
+ destruct C as (b & Hin & Hr). pose proof (Permutation_in _ PLB Hin) as Hin'. apply in_map_iff in Hin' as (b0 & <- & Hin0).
pose proof (RHEAP_block_range_proof _ _ _ _ RH Hin0) as (R1 & R2 & R3 & R4 & R5). unfold zblk in Hr. cbn [fst snd] in Hr. unfold RDATA_LO, RIMG_HI in Ha. lia.
+ unfold alloc_ceiling, RDATA_LO, RIMG_HI in *. lia.
+ exact (NZ Hz). }
assert (KEEP : forall A bs, bytes_at rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> RDATA_LO <= a < RIMG_HI /\ ralloc_zone a) ->
bytes_at rsegs m' A bs).
{ intros Ax bs (C0 & C1 & CB) HZ. split; [exact C0|]. split; [exact C1|]. intros i Hi. rewrite <- (CB i Hi). unfold mrd.
destruct (HZ (Ax + Z.of_nat i) ltac:(lia)) as [Ha Hz]. rewrite (CHZ _ Ha Hz). reflexivity. }
destruct CAN as (CA & CG & CP). split; [|split]; (eapply KEEP; [eassumption|]); intros a Ha; rewrite length_le8 in Ha;
unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR in *; lia.
Qed.

#[using="Type"] Lemma heapc_intro s L LB0 m md :
RHEAP s LB0 m -> mem_inv rsegs m -> HSIM s L LB0 -> KL L (ps_brk s) md ->
Permutation (ld_live L) (map blk_slot LB0) -> List.NoDup (ld_live L) ->
Forall (fun b => 1 <= blk_size b) LB0 -> rauxv_ok m B -> HCELLS m ->
HEAPc B (mkHS s L) (map zblk LB0) m md.
Proof. intros. exists LB0. cbn [hs_s hs_L]. splits; auto. Qed.

#[using="Type"] Lemma heapc_init m md pbrk :
RHEAP (ps_init_s rc_secret (reservedZ rsegs)) [] m -> mem_inv rsegs m ->
KL (led_init (reservedZ rsegs)) pbrk md -> pbrk = 0 ->
rauxv_ok m B -> HCELLS m ->
HEAPc B (mkHS (ps_init_s rc_secret (reservedZ rsegs)) (led_init (reservedZ rsegs))) [] m md.
Proof.
intros RH MI HK -> AUX CAN. apply (heapc_intro _ _ [] m md RH MI); auto.
- apply HSIM_init_s. exact rc_secret_range.
- constructor.
Qed.

End Core.

End RC__1.
