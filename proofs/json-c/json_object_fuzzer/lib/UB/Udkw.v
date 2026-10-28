(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq Lib.GwApply Qfw3 Q9A7 QlEo Q5Rg UEQM Qy5Y Q4J3 Qnxq QPjm UKNz UQXM Uv2Y UXT6 UOpO Unip Upt0 QZAi QUZl Q7S0 Qfya QYTG Ql2m QGeV QRjH QHnV QCcH UC8c QeZD QMt2 UmAj Uc9I Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq.Mq0 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3.Mq2 Q9A7.Mq1 QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0 Q5Rg.
Import UEQM.
Import Qy5Y.Mq4 Q4J3.Mq3 Qnxq QPjm.Mq4.
Import UKNz UQXM Uv2Y UXT6 UOpO Unip Upt0.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QYTG.Mq0 Ql2m.Mq3 QGeV.
Import QRjH.
Import QHnV QCcH.
Import UC8c.Mq0.
Import QeZD QMt2.
Import UmAj Uc9I.Mq1 Uc9I.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lb_remove_zlb : forall p LB, QCcH.lb_remove p LB = zlb_remove p LB.
Proof.
induction LB as [|[a n] LB IH]; [reflexivity|]. cbn [QCcH.lb_remove zlb_remove QCcH.blk_addr fst].
destruct (a =? p); [reflexivity|]. rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma in_block_zin : forall LB a, QCcH.in_block LB a <-> zin_block LB a.
Proof. intros. unfold QCcH.in_block, zin_block, QCcH.blk_addr, QCcH.blk_size. tauto. Qed.

#[using="Type"] Lemma vm_only_model : forall md md', vm_only md md' -> model_vm_only md md'.
Proof. intros md md' H. exact H. Qed.

#[using="Type"] Lemma heap_pres_of_r : forall LB LB0 SP m m',
Permutation LB (map zblk LB0) -> rheap_pres LB0 SP m m' -> heap_pres S4L LB SP m m'.
Proof.
intros LB LB0 SP m m' PLB HP a Ha Hc. apply (HP a Ha).
destruct Hc as [Hc|[Hc|(b & Hin & Hr)]]; [left; exact Hc| right; left| right; right].
{ cbn [hl_client_static S4L] in Hc. unfold s4_client_static in Hc. unfold ralloc_static, RLIBC, RMLOCK, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RATP. lia. }
pose proof (Permutation_in _ PLB Hin) as H. apply in_map_iff in H as (b0 & <- & Hin0).
exists b0. split; [exact Hin0|]. unfold QCcH.blk_addr, QCcH.blk_size, zblk in Hr. cbn in Hr. exact Hr.
Qed.

#[using="Type"] Lemma lb_remove_notin : forall p LB, ~ In p (map fst LB) -> zlb_remove p LB = LB.
Proof.
induction LB as [|[a n] LB IH]; intros H; [reflexivity|]. cbn. cbn in H.
destruct (Z.eqb_spec a p) as [->|NE]; [exfalso; apply H; left; reflexivity|]. f_equal. apply IH. tauto.
Qed.

#[using="Type"] Lemma rmalloc_stmt_at_impl : rmalloc_impl_stmt -> rmalloc_stmt_at rmalloc_entry. Proof. exact (fun H => H). Qed.
#[using="Type"] Lemma rfree_stmt_at_impl : rfree_impl_stmt -> rfree_stmt_at rfree_entry. Proof. exact (fun H => H). Qed.

Section Inst.
Variable B : Z.
Hypothesis HBlt : alloc_ceiling < B.
Hypothesis HM : rmalloc_impl_stmt.
Hypothesis HF : rfree_impl_stmt.
Hypothesis HC0 : rcalloc_stmt.
Hypothesis HR0 : rrealloc_stmt.

Notation AST := hstate.
Notation HEAP4 := (HEAPc B).

#[using="Type"] Lemma S4_malloc_at (MENTRY : Z) (HMx : rmalloc_stmt_at MENTRY) :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AST) (LB : list blk) (n lo : Z) (errv : word),
HEAP4 A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack S4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= B ->
rw_cells rsegs m (hl_tp S4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp S4L) ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
heap_pres S4L LB (bv_unsigned sp) m m' ->
rw_cells rsegs m' (hl_tp S4L - 164) [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAP4 A' LB m' md')
\/ (r <> 0 /\ (exists junk, rw_cells rsegs m' r [CB (Z.to_nat n) junk])
/\ HEAP4 A' ((r, n) :: LB) m' md') ) ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 MENTRY) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP ST H1 H2 _ HB ERR Htp Ha0 Hn K. rewrite QYTG.Mq0.alloc_ceiling_State in H1.
assert (H2' : lo <= bv_unsigned sp - RMALLOC_STACK) by (unfold RMALLOC_STACK; cbn [hl_stack S4L] in H2; lia).
eapply (heapc_malloc B MENTRY HMx) with (lo := lo); [exact HP| exact ST| exact H1| exact H2'| exact HB| exact ERR| exact Htp| exact Ha0| exact Hn|].
intros ms' m' md' A' r errv' RS VM ST' (LB0 & PLB & PRES) ERR' RES.
eapply K; [exact RS| exact (vm_only_model _ _ VM)| exact ST'| exact (heap_pres_of_r _ _ _ _ _ PLB PRES)| exact ERR'|].
destruct RES as [X|(X1 & X2 & _ & X4)]; [left; exact X| right; auto].
Qed.

#[using="Type"] Lemma S4_free_at (FENTRY : Z) (HFx : rfree_stmt_at FENTRY) (HFNx : rfree_null_stmt_at FENTRY) :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AST) (LB : list blk) (p lo : Z) (errv : word),
HEAP4 A LB m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack S4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= B ->
rw_cells rsegs m (hl_tp S4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp S4L) ->
a0 = Z_to_bv 64 p ->
(forall ms' m' md' A' (r : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
heap_pres S4L (QCcH.lb_remove p LB) (bv_unsigned sp) m m' ->
rw_cells rsegs m' (hl_tp S4L - 164) [C4 errv] ->
HEAP4 A' (QCcH.lb_remove p LB) m' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FENTRY) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP Hp ST H1 H2 _ HB ERR Htp Ha0 K. rewrite lb_remove_zlb in K. rewrite QYTG.Mq0.alloc_ceiling_State in H1.
destruct Hp as [->|[n HIN]].
-
rewrite lb_remove_notin in K.
2:{ intros Hin. apply in_map_iff in Hin as ([a n] & E & Hin). cbn in E. subst a.
pose proof (heapc_blk B A LB m md 0 n HP Hin). lia. }
apply (heapc_free_null FENTRY HFNx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md T (heapc_model_ok B _ _ _ _ HP) Ha0).
eapply (K _ m md A a0).
+ unfold ret_state. repeat eexists.
+ apply model_vm_only_refl.
+ exact ST.
+ intros a Ha _. auto.
+ exact ERR.
+ exact HP.
- assert (H2' : lo <= bv_unsigned sp - RFREE_STACK) by (unfold RFREE_STACK; cbn [hl_stack S4L] in H2; lia).
eapply (heapc_free B FENTRY HFx) with (lo := lo); [exact HP| exact HIN| exact ST| exact H1| exact H2'| exact HB| exact ERR| exact Htp| exact Ha0|].
intros ms' m' md' A' r RS VM ST' (LBx & PLB & PRES) ERR' HP'.
eapply K; [exact RS| exact (vm_only_model _ _ VM)| exact ST'| exact (heap_pres_of_r _ _ _ _ _ PLB PRES)| exact ERR'| exact HP'].
Qed.

#[using="HC0"] Lemma S4_calloc :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AST) (LB : list blk) (cnt sz lo : Z) (errv : word),
HEAP4 A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack S4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= B ->
rw_cells rsegs m (hl_tp S4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp S4L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 1 <= cnt * sz < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
heap_pres S4L LB (bv_unsigned sp) m m' ->
rw_cells rsegs m' (hl_tp S4L - 164) [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAP4 A' LB m' md')
\/ (r <> 0 /\ rw_cells rsegs m' r [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
/\ HEAP4 A' ((r, cnt * sz) :: LB) m' md') ) ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_calloc S4L)) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP ST H1 H2 _ HB ERR Htp Ha0 Ha1 Hcnt Hsz Hn K. rewrite QYTG.Mq0.alloc_ceiling_State in H1.
assert (H2' : lo <= bv_unsigned sp - RCALLOC_STACK) by (unfold RCALLOC_STACK, RMALLOC_STACK; cbn [hl_stack S4L] in H2; lia).
eapply (heapc_calloc B HC0) with (lo := lo); [exact HP| exact ST| exact H1| exact H2'| exact HB| exact ERR| exact Htp| exact Ha0| exact Ha1| exact Hcnt| exact Hsz| intros _; exact Hn|].
intros ms' m' md' A' r errv' RS VM ST' (LB0 & PLB & PRES) ERR' RES.
eapply K; [exact RS| exact (vm_only_model _ _ VM)| exact ST'| exact (heap_pres_of_r _ _ _ _ _ PLB PRES)| exact ERR'|].
destruct RES as [X|(X1 & X2 & _ & _ & X4)]; [left; exact X| right; auto].
Qed.

#[using="HR0"] Lemma S4_realloc :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AST) (LB : list blk) (p n0 n lo : Z) (errv : word) (old : list byte) (junk0 : list byte),
HEAP4 A LB m md -> In (p, n0) LB ->
rw_cells rsegs m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack S4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= B ->
rw_cells rsegs m (hl_tp S4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp S4L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
rw_cells rsegs m' (hl_tp S4L - 164) [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ heap_pres S4L LB (bv_unsigned sp) m m' /\ HEAP4 A' LB m' md')
\/ (r <> 0 /\ heap_pres S4L (QCcH.lb_remove p LB) (bv_unsigned sp) m m'
/\ (exists junk, rw_cells rsegs m' r
[CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)])
/\ HEAP4 A' ((r, n) :: QCcH.lb_remove p LB) m' md') ) ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc S4L)) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until junk0. intros HP HIN OLD ST H1 H2 _ HB ERR Htp Ha0 Ha1 Hn K. rewrite QYTG.Mq0.alloc_ceiling_State in H1.
rewrite lb_remove_zlb in K.
assert (H2' : lo <= bv_unsigned sp - RREALLOC_STACK) by (unfold RREALLOC_STACK, RMALLOC_STACK; cbn [hl_stack S4L] in H2; lia).
assert (LEN : (length old <= Z.to_nat n0)%nat).
{ destruct OLD as [[WF _] _]. cbn in WF. rewrite length_app in WF. lia. }
eapply (heapc_realloc B HR0) with (lo := lo); [exact HP| exact HIN| exact OLD| exact ST| exact H1| exact H2'| exact HB| exact ERR| exact Htp| exact Ha0| exact Ha1| exact Hn|].
intros ms' m' md' A' r errv' RS VM ST' ERR' RES.
eapply K; [exact RS| exact (vm_only_model _ _ VM)| exact ST'| exact ERR'|].
destruct RES as [(X1 & Xe & (LB0 & PLB & PRES) & X3)|(X1 & (LBx & PLB & PRES) & (junk & BLK) & _ & X4)].
- left. split; [exact X1|]. split; [exact Xe|]. split; [exact (heap_pres_of_r _ _ _ _ _ PLB PRES)| exact X3].
- right. split; [exact X1|]. split; [exact (heap_pres_of_r _ _ _ _ _ PLB PRES)|]. split; [| exact X4].
exists junk. replace (Z.to_nat (Z.min n (Z.of_nat (length old)))) with (Nat.min (Z.to_nat (Z.min n n0)) (length old)) by lia.
rewrite firstn_min_len. exact BLK.
Qed.

Definition S4_heap_iface : heap_iface S4L.
Proof.
unshelve refine (@HI _ S4L hstate (HEAPc B) B HBlt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(S4_malloc_at RMALLOC_SYM (rmalloc_stmt_at_sym (rmalloc_stmt_of_impl HM)))
(S4_free_at RFREE_SYM (rfree_stmt_at_sym (rfree_stmt_of_impl HF)) rfree_null_at_sym)
(S4_malloc_at rmalloc_entry (rmalloc_stmt_at_impl HM))
(S4_free_at rfree_entry (rfree_stmt_at_impl HF) rfree_null_at_impl)
S4_calloc S4_realloc).
-  intros A LB m md HP. exact (heapc_model_ok B _ _ _ _ HP).
-  intros A LB m md HP. exact (heapc_mem_inv B _ _ _ _ HP).
-  intros A LB m md a n HP HIN. pose proof (heapc_blk B _ _ _ _ _ _ HP HIN). tauto.
-  intros A LB m md a n HP HIN. cbn. pose proof (heapc_blk B _ _ _ _ _ _ HP HIN). unfold RIMG_LO, RIMG_HI in *. tauto.
-  intros A LB m md a n a' n' HP I1 I2 NE. exact (heapc_blk_disjoint B _ _ _ _ _ _ _ _ HP I1 I2 NE).
-  intros A LB m md HP. exact (heapc_blk_nodup B _ _ _ _ HP).
-  intros A LB m md a n i HP HIN Hi H. cbn in H. unfold s4_client_static in H.
pose proof (heapc_blk B _ _ _ _ _ _ HP HIN) as (_ & _ & _ & _ & _ & IMG). unfold RIMG_LO, RIMG_HI in IMG. lia.
-  intros A LB LB' m md HP P. exact (heapc_perm B _ _ _ _ _ HP P).
-  intros A LB m md a n HP HIN. exact (heapc_blk_slack B _ _ _ _ _ _ HP HIN).
-  intros A LB m md md' HP E1 E2 E3 Hh. exact (heapc_model_frame B _ _ _ _ _ HP E1 E2 Hh).
-  intros A LB m m' md HP CH WM MI'. eapply (heapc_frame B _ _ _ _ _ HP); [| exact WM| exact MI'].
intros a Ha NCW. apply (CH a Ha).
+ intros [C LT]. apply NCW. destruct C as [C|[C|C]]; [rewrite QYTG.Mq0.alloc_ceiling_State in C; right; left; lia| | left; apply in_block_zin; exact C].
right; right. cbn in C. unfold s4_client_static in C. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
+ intros SC. apply NCW. right; right. cbn in SC. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR. lia.
-  intros A LB m md HP. exists rc_canary. pose proof (heapc_canary B _ _ _ _ HP) as (C1 & C2 & C3). cbn. auto.
-  intros A LB m md HP. exact (heapc_auxv B _ _ _ _ HP).
-  intros A LB m md HP. exact (heapc_need_locks B _ _ _ _ HP).
-  intros A LB m md HP. pose proof (heapc_consts B _ _ _ _ HP) as [C1 C2]. constructor; [exact C1| constructor; [exact C2| constructor]].
Defined.

End Inst.

End RC__1.
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBv7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkRc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkRc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMt2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMt2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qh1B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qh1B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMIO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMIO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QwQw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwQw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBMn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I.Mq0.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section DrvF.
Variable B : Z.
Hypothesis HF : rfree_stmt.

#[using="HF"] Theorem heapc_free_drvP (P : mstate -> Prop) :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (T : TSet)
(A : hstate) (LB : list (Z * Z)) (p n lo : Z) (errv : word) (W0 : Z) (D0 : nat),
HEAPc B A LB m md -> In (p, n) LB ->
(forall st L0 BL LS c off, INVL x0 st L0 BL LS -> strip st = ps_m (hs_s A) -> In ((c, off), n) BL ->
KSUM isF P W0 D0 L0 (cfree (strip st) (Some c)) KS W0 (S D0)) ->
BUD md W0 (S D0) -> 0 <= W0 ->
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
HEAPc B A' (zlb_remove p LB) m' md' -> P (ps_m (hs_s A')) -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until D0. intros HP HIN KSH HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 K.
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
pose proof (KSH st L BL LS c off INV Est HkBL) as KSM. rewrite Est in KSM.
apply (rz_conseq rsegs _ (TK T T KS)); [| apply TK_KS].
eapply (membed_realizes_strong_KL rsegs isF P W0 D0 (cfree (ps_m s) (Some c)) _ s _ _ md L T T KS W0 (S D0) IMPL CT HKL HBUD HW0 KSM).
intros cs' s' ms' L' md' Hleaf _ HPF CP Em Efa Eso HK' HV' HB'. cbn [isF].
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
+ rewrite ERM. rewrite ELB0 in SZ. apply Forall_app in SZ as [SZ1 SZ2]. inversion SZ2; subst. apply Forall_app. auto.
+ exact AUX'.
+ exact CAN'.
- cbn [hs_s ps_m set_m]. exact HPF.
- exact HB'.
Qed.

End DrvF.

End RC__1.
