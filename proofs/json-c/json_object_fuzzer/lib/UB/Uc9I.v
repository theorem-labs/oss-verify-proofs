(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq Lib.GwApply Qfw3 Q9A7 QlEo Q5Rg UEQM Qy5Y Q4J3 Qnxq QPjm QTyG Q3o5 UKNz UQXM Uv2Y UXT6 UOpO Upt0 QZAi QUZl Q7S0 Qfya Ql2m QGeV Qatc QPWv Q4en QBv7 QRjH QHnV QeZD QkRc QMt2 Qn5J QqWy Qh1B QMIO QvVk QwQw Q3dN QV3E QBMn UmAj Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq.Mq0 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3.Mq2 Q9A7.Mq1 QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0 Q5Rg.
Import UEQM.
Import Qy5Y.Mq4 Q4J3.Mq3 Qnxq QPjm.Mq4.

Import Q3o5.Mq1.
Import UKNz UQXM Uv2Y UXT6 UOpO Upt0.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Qfya Ql2m.Mq3 QGeV Qatc QPWv Q4en QBv7.
Import QRjH.
Import QHnV.
Import QeZD QkRc QMt2 Qn5J QqWy Qh1B QMIO QvVk QwQw Q3dN.Mq0 QV3E.Mq0 QV3E.
Import QBMn UmAj.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition hshift (A : hstate) : Z := c_meta_alloc_shift (s_ctx (ps_m (hs_s A))).
Definition hactive (A : hstate) (sc : Z) : optr := active (ps_m (hs_s A)) sc.
Definition hmeta (A : hstate) (g : aptr) : meta := MR (ps_m (hs_s A)) g.

#[using="Type"] Lemma hshift_init sec resv L : hshift (mkHS (ps_init_s sec resv) L) = 0.
Proof. reflexivity. Qed.

Section Drv.
Variable B : Z.
Hypothesis HM : rmalloc_stmt.

#[using="HM"] Theorem heapc_malloc_strongP (P : mstate * option cptr -> Prop) :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (Tn Ts : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word) (W0 Wx : Z) (D0 Dx : nat),
HEAPc B A LB m md ->
(forall st L0 BL LS, INVL x0 st L0 BL LS -> strip st = ps_m (hs_s A) ->
KSUM isCC P W0 D0 L0 (cmalloc (strip st) n) KS (W0 + Wx) (D0 + Dx)%nat) ->
BUD md (W0 + Wx) (D0 + Dx)%nat -> 0 <= W0 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^64 ->

(forall ms' m' md' A' (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
HEAPc B A' LB m' md' -> P (ps_m (hs_s A'), None) -> BUD md' W0 D0 ->
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
HEAPc B A' ((r, n) :: LB) m' md' -> (exists c, P (ps_m (hs_s A'), Some c)) -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Ts) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)) md) Ts.
Proof.
intros until Dx. intros HP KS HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 Hn KN KY.
destruct A as [s L]. cbn [hs_s hs_L] in *.
destruct HP as (LB0 & PLB & RH & MI & CR & HKL & PLV & NDL & SZ & AUX & CAN).
assert (Uerr : (bv_unsigned tp + (-164)) = RATP - 164) by (rewrite Htp; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
pose proof (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 n lo B errv
RH AUX HB ST Hlo1 Hlo2 ltac:(rewrite Uerr; exact ERR) MI Htp Ha0 ltac:(lia)) as IMPL.
unfold raw_malloc in IMPL. apply implM_get_inv in IMPL. apply implM_bind_inv in IMPL.
destruct CR as (st & BL & LS & LB1 & PB1 & Est & INV & CORR0).
pose proof (cmalloc_ctreeI st L BL LS n INV (HSIM_live_sub L LB0 st BL LB1 PB1 CORR0 PLV) ltac:(lia)) as CT. rewrite Est in CT.
pose proof (KS st L BL LS INV Est) as KSM. rewrite Est in KSM.
apply (rz_conseq rsegs _ (TK Tn Ts Qn5J.KS)); [| apply TK_KS].
eapply (membed_realizes_strong_KL rsegs isCC P W0 D0 (cmalloc (ps_m s) n) _ s _ _ md L Tn Ts Qn5J.KS (W0 + Wx) (D0 + Dx)%nat IMPL CT HKL HBUD HW0 KSM).
intros [cs' oc] s' ms' L' md' Hleaf HPost HPSH CP Em Efa Eso HK' HV' HB'. cbn [snd] in HPost.
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
destruct oc as [c|]; cbv beta iota in RES; cbn [isCC snd].
-
destruct RES as (Ar & junk & -> & RNG & RH' & BLK & _).
eapply (KY _ m' md' (mkHS (set_m cs' s') L'') Ar errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ exists LB0. split; [exact PLB| exact PRES].
+ rewrite <- Uerr. exact ERR'.
+ destruct RNG as (R1 & _); lia.
+ exists junk; exact BLK.
+ exact RNG.
+ exists (((c, fresh_off cs' c n), Ar, n) :: LB0). cbn [hs_s hs_L map zblk blk_addr blk_size blk_slot blk_id fst snd ps_m ps_brk set_m].
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
+ cbn [hs_s ps_m set_m]. exists c. exact HPSH.
+ exact HB'.
-
destruct RES as (-> & He & RH').
eapply (KN _ m' md' (mkHS (set_m cs' s') L'') errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ exists LB0. split; [exact PLB| exact PRES].
+ rewrite <- Uerr. exact ERR'.
+ exists LB0. cbn [hs_s hs_L ps_m ps_brk set_m]. pose proof (SIM' _ RH') as CR'. subst L''. splits; auto.
rewrite LIVE'. exact PLV. rewrite LIVE'. exact NDL.
+ cbn [hs_s ps_m set_m]. exact HPSH.
+ exact HB'.
Qed.

#[using="HM"] Theorem heapc_malloc_strong :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (Tn Ts : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word) (SH W0 Wx : Z) (D0 Dx : nat),
HEAPc B A LB m md ->
(forall st L0 BL LS, INVL x0 st L0 BL LS -> strip st = ps_m (hs_s A) ->
KSUM isCC (PSH SH) W0 D0 L0 (cmalloc (strip st) n) KS (W0 + Wx) (D0 + Dx)%nat) ->
BUD md (W0 + Wx) (D0 + Dx)%nat -> 0 <= W0 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^64 ->

(forall ms' m' md' A' (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
(exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
HEAPc B A' LB m' md' -> hshift A' <= SH + 1 -> BUD md' W0 D0 ->
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
HEAPc B A' ((r, n) :: LB) m' md' -> hshift A' <= SH + 1 -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Ts) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)) md) Ts.
Proof.
intros until Dx. intros HP KS HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 Hn KN KY.
eapply (heapc_malloc_strongP (PSH SH) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv W0 Wx D0 Dx
HP KS HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 Hn).
- intros ms' m' md' A' errv' H1 H2 H3 H4 H5 H6 HPA H8. eapply (KN ms' m' md' A' errv'); try eassumption.
all: unfold PSH in HPA; cbn [fst] in HPA; unfold hshift; exact HPA.
- intros ms' m' md' A' r errv' H1 H2 H3 H4 H5 H6 H7 H8 H9 [c HPA] H10. eapply (KY ms' m' md' A' r errv'); try eassumption.
all: unfold PSH in HPA; cbn [fst] in HPA; unfold hshift; exact HPA.
Qed.

#[using="HM"] Theorem heapc_malloc_big :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (Tn Ts : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word) (SH W0 : Z) (D0 : nat),
HEAPc B A LB m md -> hshift A <= SH -> 0 <= SH <= 16 ->
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
HEAPc B A' LB m' md' -> hshift A' <= SH + 1 -> BUD md' W0 D0 ->
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
HEAPc B A' ((r, n) :: LB) m' md' -> hshift A' <= SH + 1 -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Ts) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)) md) Ts.
Proof.
intros until D0. intros HP HSHA HSH Hbig Hn30 HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 KN KY.
eapply (heapc_malloc_strong ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv SH W0 (BIGW SH n) D0 BIGD HP);
try eassumption.
- intros st L0 BL LS INV Est. apply (cmalloc_big_ks SH W0 D0 HSH st L0 BL LS n INV Hbig Hn30).
unfold hshift in HSHA. rewrite <- Est in HSHA. exact HSHA.
- unfold MMAP_THRESHOLD, IB, UNIT in *. lia.
Qed.

#[using="HM"] Theorem heapc_malloc_small :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (Tn Ts : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word) (SH W0 XC : Z) (D0 : nat),
HEAPc B A LB m md -> hshift A <= SH -> 0 <= SH <= 15 -> 23 < XC ->
1 <= n < MMAP_THRESHOLD ->
(forall j, 0 <= j < 48 -> j <> XC -> hactive A j = None) ->
size_to_class n <> XC -> Z.lor (size_to_class n) 1 <> XC ->
BUD md (W0 + SMALLW SH) (D0 + SMALLD)%nat -> 0 <= W0 ->
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
intros until D0. intros HP HSHA HSH HXC Hn NA NX1 NX2 HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 KN KY.
replace (SH + 2) with ((SH + 1) + 1) in KN, KY by lia.
eapply (heapc_malloc_strong ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv (SH + 1) W0 (SMALLW SH) D0 SMALLD HP);
try eassumption.
- intros st L0 BL LS INV Est. apply (cmalloc_small_ks SH W0 D0 XC HSH HXC st L0 BL LS n INV ltac:(lia)).
+ unfold hshift in HSHA. rewrite <- Est in HSHA. exact HSHA.
+ intros j Hj NE. pose proof (NA j Hj NE) as HAj. unfold hactive in HAj. rewrite <- Est in HAj. exact HAj.
+ exact NX1.
+ exact NX2.
- unfold MMAP_THRESHOLD in *. lia.
Qed.

#[using="HM"] Theorem heapc_malloc_fullhead :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (Tn Ts : TSet)
(A : hstate) (LB : list (Z * Z)) (n lo : Z) (errv : word) (SH W0 : Z) (D0 : nat) (g : aptr),
HEAPc B A LB m md -> hshift A <= SH -> 0 <= SH <= 16 ->
1004 < n < MMAP_THRESHOLD ->
hactive A (size_to_class n) = Some g ->
get_stride (hmeta A g) < UNIT * size_class (m_sizeclass (hmeta A g)) -> m_next (hmeta A g) = Some g ->
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
HEAPc B A' LB m' md' -> hshift A' <= SH + 1 -> BUD md' W0 D0 ->
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
HEAPc B A' ((r, n) :: LB) m' md' -> hshift A' <= SH + 1 -> BUD md' W0 D0 ->
realizes rsegs (mkCfg ms' md') Ts) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)) md) Ts.
Proof.
intros until g. intros HP HSHA HSH Hn HA HU NX HBUD HW0 ST Hlo1 Hlo2 HB ERR Htp Ha0 KN KY.
eapply (heapc_malloc_strong ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md Tn Ts A LB n lo errv SH W0 (FRESHW SH) D0 FRESHD HP);
try eassumption.
- intros st L0 BL LS INV Est.
unfold hactive, hmeta in HA, HU, NX. rewrite <- Est in HA, HU, NX.
change (active (strip st) (size_to_class n)) with (active st (size_to_class n)) in HA.
change (MR (strip st) g) with (MR st g) in HU, NX.

destruct (hd_facts x0 st L0 BL LS (size_to_class n) g INV HA) as (SC44 & Esc & bg & ai & Hbg).
pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbg) as GO.
destruct (g_under _ _ _ _ _ _ GO ltac:(cbn; discriminate) ltac:(lia) HU) as [AV FR].
apply (cmalloc_fullhead_ks SH W0 D0 HSH st L0 BL LS n g INV Hn); try assumption.
unfold hshift in HSHA. rewrite <- Est in HSHA. exact HSHA.
- unfold MMAP_THRESHOLD in *. lia.
Qed.

End Drv.

End RC__1.
End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q1u2 QAnn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq.Mq0 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3.Mq2 Q9A7.Mq1 QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0 Q5Rg.
Import UEQM.
Import Qy5Y.Mq4 Q4J3.Mq3 Qnxq QPjm.Mq4.

Import Q3o5.Mq1.
Import UKNz UQXM Uv2Y UXT6 UOpO Upt0.
Import QZAi.Mq1 QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Qfya Ql2m.Mq3 QGeV Qatc Q4en QBv7 Q1u2 QAnn.
Import QRjH.
Import QHnV.
Import QeZD QkRc QMt2.
Import QBMn UmAj.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ap_remove_notin : forall c l, List.NoDup l -> ~ In c (ap_remove c l).
Proof.
induction l as [|y l IH]; intros ND Hin; [destruct Hin|]. inversion ND; subst. cbn [ap_remove] in Hin.
destruct (QSfG.Mq2.aptr_eqb_spec y c) as [->|NE]; [exact (H1 Hin)|].
destruct Hin as [->|Hin]; [congruence| exact (IH H2 Hin)].
Qed.

#[using="Type"] Lemma firstn_min_len {A} (k : nat) (l : list A) : firstn (Nat.min k (length l)) l = firstn k l.
Proof.
revert k. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.

Section Realloc.
Variable B : Z.
Hypothesis HR0 : rrealloc_stmt.

#[using="HR0"] Theorem heapc_realloc :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (T : TSet)
(A : hstate) (LB : list (Z * Z)) (p n0 n lo : Z) (errv : word) (old junk0 : list byte),
HEAPc B A LB m md -> In (p, n0) LB ->
rw_cells rsegs m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
bv_unsigned sp <= B ->
rw_cells rsegs m (RATP - 164) [C4 errv] ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
(exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)) ->
vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
rw_cells rsegs m' (RATP - 164) [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 12 /\ (exists LB0, Permutation LB (map zblk LB0) /\ rheap_pres LB0 (bv_unsigned sp) m m') /\ HEAPc B A' LB m' md')
\/ (r <> 0 /\ (exists LBx, Permutation (zlb_remove p LB) (map zblk LBx) /\ rheap_pres LBx (bv_unsigned sp) m m')
/\ (exists junk, rw_cells rsegs m' r [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n n0)) old ++ junk)])
/\ rblock_range r n
/\ HEAPc B A' ((r, n) :: zlb_remove p LB) m' md') ) ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until junk0. intros HP HIN OLD ST Hlo1 Hlo2 HB ERR Htp Ha0 Ha1 Hn K.
destruct A as [s L]. cbn [hs_s hs_L] in *.
destruct HP as (LB0 & PLB & RH & MI & CR & HKL & PLV & NDL & SZ & AUX & CAN).
assert (Uerr : (bv_unsigned tp + (-164)) = RATP - 164) by (rewrite Htp; unfold RATP; rewrite unsigned_lit by lia; reflexivity).

assert (Hb0 : exists b0, In b0 LB0 /\ zblk b0 = (p, n0)).
{ pose proof (Permutation_in _ PLB HIN) as H. apply in_map_iff in H as (b0 & E & Hin0). exists b0. auto. }
destruct Hb0 as (b0 & Hin0 & Eb0).
pose proof (RHEAP_blocks_nodup_proof _ _ _ RH) as NDI.
destruct (lb_remove_split b0 LB0 Hin0 NDI) as (l1 & l2 & ELB0 & ERM).
assert (NDA : List.NoDup (map fst LB)).
{ eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PLB|].
rewrite map_map. change (fun x => fst (zblk x)) with blk_addr.
apply blk_addr_nodup; [exact NDI| intros b1 b2 H1 H2 NE; exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ RH H1 H2 NE)| exact SZ]. }
assert (PRM : Permutation (zlb_remove p LB) (map zblk (lb_remove (blk_id b0) LB0))).
{ apply (Permutation_cons_inv (a:=(p, n0))).
eapply Permutation_trans; [apply Permutation_sym; apply zlb_remove_perm; [exact NDA| exact HIN]|].
eapply Permutation_trans; [exact PLB|]. rewrite ERM, ELB0, !map_app. cbn [map]. rewrite Eb0.
apply Permutation_sym. apply Permutation_middle. }
destruct b0 as [[pb Ab] nb]. unfold zblk, blk_addr, blk_size in Eb0. cbn [fst snd] in Eb0. injection Eb0 as -> ->.
unfold blk_id in ERM, PRM. cbn [fst] in ERM, PRM.
set (c := fst pb).
assert (LIVEc : In c (ld_live L)).
{ eapply Permutation_in; [apply Permutation_sym; exact PLV|]. apply in_map_iff. exists (pb, p, n0). split; [reflexivity| exact Hin0]. }
destruct CR as (st & BL & LS & LB1 & PB1 & Est & INV & CORR0).
assert (Hin1 : In (pb, p, n0) LB1) by (eapply Permutation_in; [apply Permutation_sym; exact PB1| exact Hin0]).
destruct (HSIM_block st LB1 BL (pb, p, n0) CORR0 Hin1) as (off & HkBL & Ep). unfold blk_slot, blk_size, blk_addr in HkBL, Ep. cbn [fst snd] in HkBL, Ep. fold c in HkBL, Ep.
assert (Eoff : real_off (ps_m s) c p = off).
{ unfold real_off. rewrite <- Est, conc_strip, Ep. replace (conc st c + UNIT * off - conc st c) with (off * UNIT) by lia. unfold UNIT. apply Z.div_mul. lia. }
pose proof (HR0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 pb p n0 n lo B errv old junk0
RH Hin0 OLD AUX HB ST Hlo1 Hlo2 ltac:(rewrite Uerr; exact ERR) MI Htp Ha0 Ha1 Hn) as IMPL.
change (fst pb) with c in IMPL. rewrite Eoff in IMPL.
unfold raw_realloc in IMPL. apply implM_get_inv in IMPL. apply implM_bind_inv in IMPL.
pose proof (crealloc_ctree st L BL LS c off n0 n INV HkBL ltac:(lia)) as CT. rewrite Est in CT.
eapply (membed_realizes_KL rsegs (crealloc (ps_m s) c off n) _ s _ _ md L T IMPL CT HKL).
intros [cs' rw] s' ms' L' md' Hleaf HPost CP Em Efa Eso HK' HV'. cbn [snd] in HPost.
apply implM_upd_ret_inv in Hleaf.
apply rz_evt; [exact (KL_model_ok _ _ _ HK')|].
eapply evt_mono; [exact Hleaf|]. intros ms2 PM. unfold RZ.
destruct PM as (u0 & u1 & u2 & ra0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & _ & _ & RES).

rewrite <- Est in CP. destruct (crealloc_leaf_INVL st L BL LS c off n0 n L' cs' rw INV HkBL ltac:(lia) CP) as (LIVE' & st1 & LS1 & Est1 & RES1).
assert (LIVEsub : forall x, In x (ld_live L) -> In x (map bslot BL)) by (exact (HSIM_live_sub L LB0 st BL LB1 PB1 CORR0 PLV)).
destruct rw as [[|b']|]; cbv iota in RES.
-
destruct RES as (Ar & junk & -> & RNG & RH' & PRES & BLK).
pose proof (HCELLS_pres _ _ _ _ PRES CAN) as CAN'.
set (L'' := set_live (c :: ap_remove c (ld_live L')) L').
eapply (K _ m' md' (mkHS (set_m cs' s') L'') Ar errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ rewrite <- Uerr. exact ERR'.
+ right. split; [destruct RNG as (R1 & _); lia|]. split; [exists (lb_remove pb LB0); split; [exact PRM| exact PRES]|].
split; [exists junk; exact BLK|]. split; [exact RNG|].
exists (((c, off), Ar, n) :: lb_remove pb LB0). cbn [hs_s hs_L map zblk blk_addr blk_size blk_slot blk_id fst snd ps_m ps_brk set_m].
splits.
* apply perm_skip. exact PRM.
* exact RH'.
* exact MI'.
* pose proof RH' as (stn & LBa & Pa & Estn & _ & HINVn). subst L''. apply HSIM_set_live.
exact (HSIM_intro ref_reserved (set_m cs' s') L' _ stn LBa _ st1 L' _ LS1 Pa Estn HINVn Est1 RES1 eq_refl).
* subst L''. apply KL_set_live. exact HK'.
* subst L''. cbn. rewrite LIVE'. apply perm_skip. apply (Permutation_cons_inv (a:=c)).
eapply Permutation_trans; [apply Permutation_sym; apply ap_remove_perm; exact LIVEc|].
eapply Permutation_trans; [exact PLV|]. rewrite ERM, ELB0, !map_app. cbn [map]. unfold blk_slot at 2. cbn [fst]. fold c.
apply Permutation_sym. apply Permutation_middle.
* subst L''. cbn. rewrite LIVE'. constructor; [apply ap_remove_notin; exact NDL| apply ap_remove_nodup; exact NDL].
* constructor; [cbn; lia|]. rewrite ERM. rewrite ELB0 in SZ. apply Forall_app in SZ as [Z1 Z2]. inversion Z2; subst. apply Forall_app. auto.
* exact AUX'.
* exact CAN'.
-
destruct RES as (Ar & junk & -> & RNG & RH' & PRES & BLK). destruct RES1 as (off' & INV1 & NI).
pose proof (HCELLS_pres _ _ _ _ PRES CAN) as CAN'.
set (L'' := set_live (fst b' :: ap_remove c (ld_live L')) L').
eapply (K _ m' md' (mkHS (set_m cs' s') L'') Ar errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ rewrite <- Uerr. exact ERR'.
+ right. split; [destruct RNG as (R1 & _); lia|]. split; [exists (lb_remove pb LB0); split; [exact PRM| exact PRES]|].
split; [exists junk; exact BLK|]. split; [exact RNG|].
exists ((b', Ar, n) :: lb_remove pb LB0). cbn [hs_s hs_L map zblk blk_addr blk_size blk_slot blk_id fst snd ps_m ps_brk set_m].
splits.
* apply perm_skip. exact PRM.
* exact RH'.
* exact MI'.
* pose proof RH' as (stn & LBa & Pa & Estn & _ & HINVn). subst L''. apply HSIM_set_live.
exact (HSIM_intro ref_reserved (set_m cs' s') L' _ stn LBa _ st1 L' _ LS1 Pa Estn HINVn Est1 INV1 eq_refl).
* subst L''. apply KL_set_live. exact HK'.
* subst L''. cbn. rewrite LIVE'. apply perm_skip. apply (Permutation_cons_inv (a:=c)).
eapply Permutation_trans; [apply Permutation_sym; apply ap_remove_perm; exact LIVEc|].
eapply Permutation_trans; [exact PLV|]. rewrite ERM, ELB0, !map_app. cbn [map]. unfold blk_slot at 2. cbn [fst]. fold c.
apply Permutation_sym. apply Permutation_middle.
* subst L''. cbn. rewrite LIVE'. constructor; [| apply ap_remove_nodup; exact NDL].
intros Hin. apply NI. apply LIVEsub. apply (ap_remove_sub c). exact Hin.
* constructor; [cbn; lia|]. rewrite ERM. rewrite ELB0 in SZ. apply Forall_app in SZ as [Z1 Z2]. inversion Z2; subst. apply Forall_app. auto.
* exact AUX'.
* exact CAN'.
-
destruct RES as (-> & He & RH' & PRES).
pose proof (HCELLS_pres _ _ _ _ PRES CAN) as CAN'.
eapply (K _ m' md' (mkHS (set_m cs' s') L') 0 errv').
+ repeat eexists.
+ exact HV'.
+ exact ST'.
+ rewrite <- Uerr. exact ERR'.
+ left. split; [reflexivity|]. split; [exact He|]. split; [exists LB0; split; [exact PLB| exact PRES]|].
exists LB0. cbn [hs_s hs_L ps_m ps_brk set_m]. splits; auto.
* pose proof RH' as (stn & LBa & Pa & Estn & _ & HINVn).
exact (HSIM_intro ref_reserved (set_m cs' s') L' _ stn LBa _ st1 L' _ LS1 Pa Estn HINVn Est1 RES1 eq_refl).
* rewrite LIVE'. exact PLV.
* rewrite LIVE'. exact NDL.
Qed.
End Realloc.

End RC__1.
End Mq1.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMt2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMt2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBMn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition auxv_keys : list Z := [3; 4; 5; 16; 6; 11; 12; 23; 25].

#[using="Type"] Lemma bytes_at_u64s_nth segs m a ws i w :
bytes_at segs m a (u64s ws) -> nth_error ws i = Some w -> bytes_at segs m (a + 8 * Z.of_nat i) (le8 w).
Proof.
intros Hb Hn. destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
rewrite Eu in Hb. apply bytes_at_app in Hb as [_ Hb]. apply bytes_at_app in Hb as [Hb _].
rewrite Hlu in Hb. replace (a + 8 * Z.of_nat i) with (a + Z.of_nat (8 * i)) by lia. exact Hb.
Qed.

Section Aux.
Variable B : Z.

#[using="Type"] Theorem heapc_auxv A LB m md : HEAPc B A LB m md ->
exists (aw : Z) (keys : list Z),
(bytes_at rsegs m RAUXV_CELL (le8 (Z_to_bv 64 aw)) /\ aw mod 8 = 0 /\
Forall (fun k => 0 < k < 2^64 /\ k <> 33) keys /\
(forall i k, nth_error keys i = Some k -> bytes_at rsegs m (aw + 16 * Z.of_nat i) (le8 (Z_to_bv 64 k))) /\
bytes_at rsegs m (aw + 16 * Z.of_nat (length keys)) (le8 (Z_to_bv 64 0))) /\
B <= aw.
Proof.
intros HP.
destruct HP as (LB0 & _ & _ & _ & _ & _ & _ & _ & _ & AUX & _).

destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & CELL & ARR & _ & HB1 & HB2 & HAV & REST).
assert (AL : av mod 8 = 0) by (repeat match type of REST with _ /\ _ => destruct REST as [_ REST] end; exact REST).
exists av, auxv_keys.
pose proof (rw_cells_bytes_at _ _ _ _ CELL) as BC. cbn [cells_bytes cbytes app] in BC. rewrite app_nil_r in BC.
split; [| exact HB2].
split; [exact BC|]. split; [exact AL|]. split.
{ unfold auxv_keys. repeat constructor; lia. }
split.
- intros i k Hk.
assert (NTH : nth_error (rauxv_list x3 x4 x5 x16 x6 x11 x12 x23 rnd) (2 * i) = Some (wz k)).
{ unfold auxv_keys in Hk. unfold rauxv_list.
destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; cbn in Hk |- *; try (injection Hk as <-; reflexivity). destruct i; discriminate. }
pose proof (bytes_at_u64s_nth _ _ _ _ _ _ ARR NTH) as H. replace (av + 16 * Z.of_nat i) with (av + 8 * Z.of_nat (2 * i)) by lia. exact H.
- assert (NTH : nth_error (rauxv_list x3 x4 x5 x16 x6 x11 x12 x23 rnd) 18 = Some (wz 0)) by reflexivity.
pose proof (bytes_at_u64s_nth _ _ _ _ _ _ ARR NTH) as H. cbn [length auxv_keys]. replace (av + 16 * Z.of_nat 9) with (av + 8 * Z.of_nat 18) by lia. exact H.
Qed.
End Aux.

Section NeedLocks.
Variable B : Z.
#[using="Type"] Theorem heapc_need_locks A LB m md : HEAPc B A LB m md -> bytes_at rsegs m (RLIBC + 3) [Z_to_bv 8 0].
Proof.
intros (LB0 & _ & RH & _).
destruct RH as (st & LBp & _ & _ & MR & _). destruct MR as (_ & _ & GL & _). destruct GL as (_ & [[_ NL] _] & _).
cbn [cells_bytes cbytes app] in NL. change RNEED_LOCKS with (RLIBC + 3) in NL. exact NL.
Qed.
End NeedLocks.

Section MoreCells.
Variable B : Z.
#[using="Type"] Theorem heapc_page_size A LB m md : HEAPc B A LB m md -> rw_cells rsegs m RPAGE_SIZE [C8 (wz 4096)].
Proof.
intros (LB0 & _ & RH & _).
destruct RH as (st & LBp & _ & _ & MR & _). destruct MR as (_ & _ & GL & _). destruct GL as (_ & _ & PS & _). exact PS.
Qed.
#[using="Type"] Theorem heapc_guard_cells A LB m md : HEAPc B A LB m md ->
rw_cells rsegs m RGOT_SSP [C8 (wz RSSP_GUARD)] /\ rw_cells rsegs m RSSP_GUARD [C8 rc_canary].
Proof.
intros (LB0 & _ & RH & _).
destruct RH as (st & LBp & _ & _ & MR & _). destruct MR as (_ & _ & GL & _). destruct GL as (_ & _ & _ & G1 & G2). exact (conj G1 G2).
Qed.
End MoreCells.

End RC__1.
