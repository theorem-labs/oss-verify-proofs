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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMIO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QwQw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwQw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBMn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udkw.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition DSH (A : hstate) : Prop := exists g0, GSH (ps_m (hs_s A)) g0.

#[using="Type"] Lemma GSH_initA sec resv L : GSH (ps_m (hs_s (mkHS (ps_init_s sec resv) L))) None.
Proof. cbn [hs_s ps_m ps_init_s]. apply (proj1 (GSH_strip _ None)). apply GSH_init. Qed.

#[using="Type"] Lemma DSH_g0 A g : GSH (ps_m (hs_s A)) (Some g) ->
hactive A 44 = Some g /\ m_sizeclass (hmeta A g) = 44 /\ get_stride (hmeta A g) < UNIT * size_class 44 /\ m_next (hmeta A g) = Some g.
Proof. intros (_ & S2 & _ & S4). destruct (S4 g eq_refl) as [(L1 & L2 & L3) _]. unfold hactive, hmeta. repeat split; assumption. Qed.

Definition S3W (SH n : Z) : Z := if MMAP_THRESHOLD <=? n then BIGW SH n else SMALLW SH.
Definition S3D : nat := SMALLD.

#[using="Type"] Lemma BUD_mono' md W W' D D' : BUD md W D -> 0 <= W' <= W -> (D' <= D)%nat -> BUD md W' D'.
Proof. intros. eapply BUD_mono; eauto. Qed.

#[using="Type"] Lemma AMW_nonneg SH : 0 <= SH -> 0 <= AMW SH.
Proof. intros. unfold AMW, PGSZ. pose proof (Z.pow_nonneg 2 (SH + 1)). lia. Qed.
#[using="Type"] Lemma AMW_mono a b : 0 <= a <= b -> AMW a <= AMW b.
Proof. intros. unfold AMW, PGSZ. pose proof (Z.pow_le_mono_r 2 (a + 1) (b + 1)). lia. Qed.
#[using="Type"] Lemma FRESHW_le_SMALLW SH : 0 <= SH -> FRESHW SH <= SMALLW SH.
Proof. intros. unfold FRESHW, SMALLW, LW. pose proof (AMW_mono SH (SH + 1)). pose proof (AMW_nonneg (SH + 1)). lia. Qed.

Section DrvS.
Variable B : Z.
Hypothesis HM : rmalloc_stmt.
Hypothesis HF : rfree_stmt.

#[using="HM"] Theorem heapc_malloc_first :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (Tn Ts : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word) (SH W0 : Z) (D0 : nat),
HEAPc B A LB m md -> GSH (ps_m (hs_s A)) None -> hshift A <= SH -> 0 <= SH <= 16 ->
first_req n ->
BUD md (W0 + FRESHW SH) (D0 + FRESHD)%nat -> 0 <= W0 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n ->
(forall ms' m' md' A' (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
HEAPc B A' LB m' md' -> hshift A' <= SH + 1 -> DSH A' -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Tn) ->
(forall ms' m' md' A' (r : Z) (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells rsegs m' r [CB (Z.to_nat n) junk]) -> rblock_range r n ->
HEAPc B A' ((r, n) :: LB) m' md' -> hshift A' <= SH + 1 -> DSH A' -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Ts) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)) md) Ts.
Proof.
intros until D0. intros HP HG HSHA HSH Hn HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 KN KY.
pose proof Hn as (Hn1 & _ & _).
eapply (heapc_malloc_strongP B HM (PG SH) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv W0 (FRESHW SH) D0 FRESHD HP);
try eassumption.
- intros st L0 BL LS INV Est. apply (cmalloc_first_gks SH W0 D0 HSH st L0 BL LS n INV); [| exact Hn|].
+ apply (proj2 (GSH_strip st None)). rewrite Est. exact HG.
+ unfold hshift in HSHA. rewrite <- Est in HSHA. exact HSHA.
- unfold MMAP_THRESHOLD in *. lia.
- intros ms' m' md' A' errv' H1 H2 H3 H4 H5 H6 [HPA [g0 HG']] H8. eapply (KN ms' m' md' A' errv'); try eassumption.
all: try (unfold PSH in HPA; cbn [fst] in HPA; unfold hshift; exact HPA). all: exists g0; exact HG'.
- intros ms' m' md' A' r errv' H1 H2 H3 H4 H5 H6 H7 H8 H9 [c [HPA [g0 HG']]] H10. eapply (KY ms' m' md' A' r errv'); try eassumption.
all: try (unfold PSH in HPA; cbn [fst] in HPA; unfold hshift; exact HPA). all: exists g0; exact HG'.
Qed.

#[using="HM"] Theorem heapc_malloc_big_dsh :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (Tn Ts : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word) (SH W0 : Z) (D0 : nat),
HEAPc B A LB m md -> DSH A -> hshift A <= SH -> 0 <= SH <= 16 ->
MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2 ^ 30 ->
BUD md (W0 + BIGW SH n) (D0 + BIGD)%nat -> 0 <= W0 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n ->
(forall ms' m' md' A' (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
HEAPc B A' LB m' md' -> hshift A' <= SH + 1 -> DSH A' -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Tn) ->
(forall ms' m' md' A' (r : Z) (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells rsegs m' r [CB (Z.to_nat n) junk]) -> rblock_range r n ->
HEAPc B A' ((r, n) :: LB) m' md' -> hshift A' <= SH + 1 -> DSH A' -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Ts) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)) md) Ts.
Proof.
intros until D0. intros HP [g0 HG] HSHA HSH Hbig Hn30 HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 KN KY.
eapply (heapc_malloc_strongP B HM (PG SH) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv W0 (BIGW SH n) D0 BIGD HP);
try eassumption.
- intros st L0 BL LS INV Est. apply (cmalloc_big_gks SH W0 D0 HSH st L0 BL LS n g0 INV); [| exact Hbig| exact Hn30|].
+ apply (proj2 (GSH_strip st g0)). rewrite Est. exact HG.
+ unfold hshift in HSHA. rewrite <- Est in HSHA. exact HSHA.
- unfold MMAP_THRESHOLD, IB, UNIT in *. lia.
- intros ms' m' md' A' errv' H1 H2 H3 H4 H5 H6 [HPA [g1 HG']] H8. eapply (KN ms' m' md' A' errv'); try eassumption.
all: try (unfold PSH in HPA; cbn [fst] in HPA; unfold hshift; exact HPA). all: exists g1; exact HG'.
- intros ms' m' md' A' r errv' H1 H2 H3 H4 H5 H6 H7 H8 H9 [c [HPA [g1 HG']]] H10. eapply (KY ms' m' md' A' r errv'); try eassumption.
all: try (unfold PSH in HPA; cbn [fst] in HPA; unfold hshift; exact HPA). all: exists g1; exact HG'.
Qed.

#[using="HF"] Theorem heapc_free_dsh :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (T : TSet)
(A : hstate) (LB : list (Z * Z)) (p n lo : Z) (errv : word) (W0 : Z) (D0 : nat),
HEAPc B A LB m md -> In (p, n) LB -> DSH A ->
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
HEAPc B A' (zlb_remove p LB) m' md' -> hshift A' = hshift A -> DSH A' -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until D0. intros HP HIN [g0 HG] HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 K.
eapply (heapc_free_drvP B HF (PGF (hshift A)) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md T A LB p n lo errv W0 D0 HP HIN);
try eassumption.
- intros st L0 BL LS c off INV Est Hk. unfold hshift. rewrite <- Est.
apply (cfree_gks W0 D0 pans0 pupd0 pans0_range tt st L0 BL LS c off n g0 INV Hk).
apply (proj2 (GSH_strip st g0)). rewrite Est. exact HG.
- intros ms' m' md' A' r H1 H2 H3 H4 H5 H6 [HPA [g1 HG']] H8. eapply (K ms' m' md' A' r); try eassumption.
all: try exact HPA. all: exists g1; exact HG'.
Qed.

#[using="HM"] Theorem heapc_malloc_site3 :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (Tn Ts : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word) (SH W0 : Z) (D0 : nat),
HEAPc B A LB m md -> DSH A -> hshift A <= SH -> 0 <= SH <= 15 ->
1 <= n -> n + IB + UNIT <= 2 ^ 30 ->
BUD md (W0 + S3W SH n) (D0 + S3D)%nat -> 0 <= W0 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n ->
(forall ms' m' md' A' (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
HEAPc B A' LB m' md' -> hshift A' <= SH + 2 -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Tn) ->
(forall ms' m' md' A' (r : Z) (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells rsegs m' r [CB (Z.to_nat n) junk]) -> rblock_range r n ->
HEAPc B A' ((r, n) :: LB) m' md' -> hshift A' <= SH + 2 -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Ts) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)) md) Ts.
Proof.
intros until D0. intros HP HD HSHA HSH Hn1 Hn30 HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 KN KY.
pose proof HD as [g0 HG]. pose proof HG as (S1 & S2 & S3 & S4).
pose proof (AMW_nonneg SH ltac:(lia)) as AM0. pose proof (FRESHW_le_SMALLW SH ltac:(lia)) as FS.
assert (KN' : forall ms' m' md' A' (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' -> stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
HEAPc B A' LB m' md' -> hshift A' <= SH + 1 -> BUD md' W0 D0 -> realizes rsegs (mkCfg ms' md') Tn).
{ intros. eapply KN; try eassumption. lia. }
assert (KY' : forall ms' m' md' A' (r : Z) (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' -> stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells rsegs m' r [CB (Z.to_nat n) junk]) -> rblock_range r n ->
HEAPc B A' ((r, n) :: LB) m' md' -> hshift A' <= SH + 1 -> BUD md' W0 D0 -> realizes rsegs (mkCfg ms' md') Ts).
{ intros. eapply KY; try eassumption. lia. }
unfold S3W, S3D in HBUD. revert HBUD.
destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall]; intros HBUD; cbv iota in HBUD.
-
eapply (heapc_malloc_big B HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv SH W0 D0 HP);
try eassumption.
all: try lia.
eapply BUD_mono'; [exact HBUD| | unfold BIGD, SMALLD; lia]. unfold BIGW. pose proof (round_up_pg_ge (n + IB + UNIT)). unfold IB, UNIT in *. lia.
- pose proof (size_to_class_ok n ltac:(lia)) as [SC _].
destruct (Z.eq_dec (size_to_class n) 44) as [E44|NE44].
+ pose proof (size_to_class_44_lb n ltac:(lia) E44) as LB44.
destruct g0 as [g|].
*
destruct (DSH_g0 A g HG) as (HA & HSC & HSTR & HNX).
eapply (heapc_malloc_fullhead B HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv SH W0 D0 g HP);
try eassumption.
all: try lia.
all: try (rewrite E44; exact HA).
all: try (rewrite HSC; exact HSTR).
eapply BUD_mono'; [exact HBUD| unfold FRESHW in *; lia| unfold FRESHD, SMALLD; lia].
*
eapply (heapc_malloc_small B HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv SH W0 100 D0 HP);
try eassumption.
all: try (intros j Hj NE; unfold hactive; destruct (Z.eq_dec j 44) as [->|NE']; [exact S2| exact (S1 j Hj NE')]).
all: try (pose proof (lor1_le (size_to_class n) ltac:(lia)); lia).
+
eapply (heapc_malloc_small B HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv SH W0 44 D0 HP);
try eassumption.
all: try (intros j Hj NE; unfold hactive; exact (S1 j Hj NE)).
all: try (apply lor1_ne_44).
all: try lia.
Qed.

End DrvS.

End RC__1.
