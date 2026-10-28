(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0qn X0px X0qc X0qp X0q5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1le X1kg.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3 X1r4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition RCALLOC_SYM : Z := 0x31788.
Definition RCALLOC_STACK : Z := 8224.

Lemma impl_post_evt {node} segs atn {R} (t : itree node R) : forall (Q Q' : R -> machine_state -> Prop) ms,
impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> impl segs atn t Q' ms.
Proof.
induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. intros ms' H'. exact (HQ _ _ H').
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk| exact HQ].
Qed.

Lemma implM_post_evt {A} (c : X1qx.M PState A) s (Q Q' : A -> PState -> machine_state -> Prop) ms :
implM rsegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt rsegs (Q' a s') ms') -> implM rsegs c s Q' ms.
Proof.
unfold implM. intros H HQ. eapply impl_post_evt; [exact H|]. intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

Lemma rheap_pres_of_munch LB SP W m m' :
munch W m m' -> wmono rsegs m m' -> (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) -> rheap_pres LB SP m m'.
Proof.
intros MU WM OUT a Ha CA. split.
- apply MU. rewrite wa_unsigned by lia. exact (OUT a Ha CA).
- apply WM.
Qed.

Lemma outside_single lo hi a : ~ (lo <= a < hi) -> outside [(lo, hi)] a.
Proof. intros H. cbn. split; [exact H| exact I]. Qed.

Definition rcalloc_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres LB (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
| Some p => exists A,
a0 = Z_to_bv 64 A /\ rblock_range A n
/\ RHEAP s' ((p, A, n) :: LB) m'
/\ rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
/\ (raddr_exposed s n -> A = ptr_addr s' p)
/\ rsmall_block s' p
end.

Definition rcalloc_stmt_at {RCEIL : RunCeiling} (ENTRY : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (m0 n0 lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 m0 -> a1 = Z_to_bv 64 n0 -> 0 <= m0 < 2^64 -> 0 <= n0 < 2^64 -> n0 * m0 <= RSMALL_MAX ->
implM rsegs (raw_calloc m0 n0) s
(rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (n0 * m0) lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).
Definition rcalloc_stmt {RCEIL : RunCeiling} : Prop := rcalloc_stmt_at RCALLOC_SYM.

Theorem rcalloc_spec {RCEIL : RunCeiling} : rcalloc_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB m0 n0 lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA0 HA1 M0 N0 SMALL. unfold RCALLOC_STACK in LO. unfold RCALLOC_SYM.
pose proof (bv_unsigned_in_range 64 sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0.
assert (NM : 0 <= n0 * m0 <= RSMALL_MAX) by (unfold RSMALL_MAX in *; nia). unfold RSMALL_MAX in NM.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
rewrite (raw_calloc_small m0 n0) by lia.
subst a0 a1.
set (n := n0 * m0) in *.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TP; unfold errno_addr, RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR. unfold RERRNO in ERR.
pose proof (RHEAP_replaced _ _ _ HEAP) as RPL. unfold RREPLACED in RPL.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 32%nat ST.

eapply (implM_evt rsegs _ _ _ (fun ms1 => exists (x12 : word) j8 m1,
ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 m0) (Z_to_bv 64 n0) x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x317cc) fc None m1 (seg_rom rsegs)
/\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -32)
/\ rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]
/\ rw_cells rsegs m1 316332 [C4 errv] /\ rw_cells rsegs m1 449264 [C4 (wz 0)]
/\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1)).
{ step. step. step. step. step. if_cases K0.
- apply evt_done. sf_eexists 3%nat. split; [reflexivity|]. repeat (split; [eassumption|]). exact WM.
- step. step. if_cases K1; zify_cond K1.
2:{ exfalso. apply K1. rewrite ?unsigned_lit, Z.shiftr_div_pow2 by lia. rewrite Z.div_small by (unfold RSMALL_MAX in *; nia). reflexivity. }
apply evt_done. sf_eexists 3%nat. split; [reflexivity|]. repeat (split; [eassumption|]). exact WM. }
intros ms1 sfH_; first [ sf_destruct 11%nat sfH_ as x12 j8 m1 -> MI1 ST1 FR1 ERR1 RPL1 MU1 WM1 | sf_fb; destruct sfH_ as (x12 & j8 & m1 & -> & MI1 & ST1 & FR1 & ERR1 & RPL1 & MU1 & WM1) ].
clear MU WM ST FR MI ERR RPL.
assert (HEAP1 : RHEAP s LB m1).
{ eapply RHEAP_frame_proof; [exact HEAP| exact MU1| exact WM1|]. constructor; [|constructor]. left. cbn [fst]. lia. }
assert (AUX1 : rauxv_ok m1 B).
{ eapply rauxv_ok_frame; [exact AUXB| exact MU1| exact WM1|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }

eapply (implM_evt rsegs _ _ _ (fun ms2 => ms2 = _)).
{ step. step. step. apply evt_done. reflexivity. }
cbv beta. intros ms' ->. rewrite ?unsigned_lit by lia.
replace (Z_to_bv 64 (n0 * m0)) with (Z_to_bv 64 n) by reflexivity.
eapply implM_post_evt.
{ eapply rmalloc_spec.
- exact HEAP1.
- exact AUX1.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST1.
- exact CLO.
- unfold RMALLOC_STACK. rewrite unsigned_lit by lia. lia.
- rewrite ETP. unfold RERRNO. exact ERR1.
- exact MI1.
- exact TP.
- reflexivity.
- lia. }
cbv beta. intros r s' ms' POST.
first [ sf_destruct 26%nat POST as w0 w1 w2 ra0 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m2 errv2 -> MI2 ST2 ERR2 AUX2 HP2 PSF PSO RES | sf_fb; destruct POST as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & PSF & PSO & RES) ].
rewrite unsigned_lit in ST2, HP2 by lia. rewrite ETP in ERR2. unfold RERRNO in ERR2.
rewrite ret_pc_even by lia.

assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [exact HP2| exact FR1|]. left. lia. }
destruct r as [p|].
- first [ sf_destruct 8%nat RES as A ujunk -> BR HEAP2 UCH EXPO SMALLB | sf_fb; destruct RES as (A & ujunk & -> & BR & HEAP2 & UCH & EXPO & SMALLB) ].
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as A0 A16 N0' ACE AIMG | sf_fb; destruct sfP_ as (A0 & A16 & N0' & ACE & AIMG) ]. unfold alloc_ceiling in ACE.
pose proof (RHEAP_replaced _ _ _ HEAP2) as RPL2. unfold RREPLACED in RPL2.
step. if_cases Kp; zify_cond Kp. { exfalso. rewrite ?unsigned_lit in Kp by lia. lia. }
step. step. step. rewrite sx32_wz by lia. step. if_cases Kr; zify_cond Kr. 2:{ exfalso. apply Kr. reflexivity. }

pose proof HEAP2 as sfP_; first [ sf_destruct 6%nat sfP_ as st2 LB0 PERM Hst MR2 [[BL2 AR2] _] | sf_fb; destruct sfP_ as (st2 & LB0 & PERM & Hst & MR2 & [[BL2 AR2] _]) ].
assert (IN0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| left; reflexivity]).
first [ pose proof (hdr_facts_of_areach st2 LB0 (p, A, n) AR2 IN0) as sfP_; sf_destruct 11%nat sfP_ as r g bm ai ar b3 lo8 hi i off HF | sf_fb; destruct (hdr_facts_of_areach st2 LB0 (p, A, n) AR2 IN0) as (r & g & bm & ai & ar & b3 & lo8 & hi & i & off & HF) ].
specialize (SMALLB ltac:(unfold RSMALL_MAX; lia)). first [ sf_destruct 5%nat SMALLB as g' i' SL' SC27 STR' | sf_fb; destruct SMALLB as (g' & i' & SL' & SC27 & STR') ].
rewrite <- Hst in SL', SC27, STR'. change (s_slots (strip st2)) with (s_slots st2) in SL'.
change (get_meta_rec (strip st2) g') with (get_meta_rec st2 g') in SC27, STR'.
pose proof (hf_slot _ _ _ _ _ _ _ _ _ _ _ _ HF) as SL. cbn [blk_slot fst] in SL. rewrite SL in SL'. inversion SL'; subst g' i'. clear SL'.

step. step.
eapply evt_cut.
{ eapply (rallzerop_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 st2 (p, A, n) r g bm ai ar b3 lo8 hi i off MR2 MI2 HF);
[cbn [blk_addr fst snd]; apply unsigned_lit; lia | lia | exact STR']. }
cbv beta. intros ms3 sfH_; first [ sf_destruct 7%nat sfH_ as v1 v2 v3 v4 v5 v6 -> | sf_fb; destruct sfH_ as (v1 & v2 & v3 & v4 & v5 & v6 & ->) ]. rewrite ret_pc_even by lia.

step. if_cases Kz; zify_cond Kz. { exfalso. apply Kz. reflexivity. }
step. step. step. if_cases Kc; zify_cond Kc.
2:{ exfalso. apply Kc. rewrite ?unsigned_lit, Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }

step. step. step. step. step. step. step. step.
replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp by (replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
eapply evt_cut.
{ eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 ujunk); [| exact MI2].
rewrite !unsigned_lit by lia. exact UCH. }
cbv beta. intros ms4 sfH_; first [ sf_destruct 20%nat sfH_ as u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m3 -> MU4 WM4 MI3 ZCH | sf_fb; destruct sfH_ as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU4 & WM4 & MI3 & ZCH) ].
rewrite !unsigned_lit in MU4, ZCH by lia. rewrite (unsigned_lit 0) in ZCH by lia. change (0 mod 256) with 0 in ZCH.
change X1ff.rsegs with rsegs in *.

release_frame FR2 ST2 (bv_unsigned sp).
assert (DJhi : forall a k, alloc_ceiling <= a -> disjoint_from [(A, A + n)] a k).
{ intros a k Ha. cbn. unfold alloc_ceiling in Ha. split; [right; lia| exact I]. }
assert (DJimg : forall a k, 0x10000 <= a -> a + k <= 0x6e000 -> disjoint_from [(A, A + n)] a k).
{ intros a k H1 H2. cbn. split; [lia| exact I]. }
apply evt_done. unfold rcalloc_post. sf_eexists 15%nat. exists m3, errv2.
split; [reflexivity|]. split; [exact MI3|].
split. { eapply stk_transport_disjoint; [exact ST2| exact MU4| exact WM4| apply DJhi; exact CLO]. }
split. { rewrite ETP. unfold RERRNO. eapply rw_cells_transport; [exact ERR2| exact MU4| exact WM4| apply DJimg; cbn; lia]. }
split. { eapply rauxv_ok_frame; [exact AUX2| exact MU4| exact WM4|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. unfold alloc_ceiling in CLO. lia. }
split.
{ eapply rheap_pres_trans; [| eapply rheap_pres_trans; [eapply (rheap_pres_weaken LB LB (bv_unsigned sp + -32) (bv_unsigned sp)); [exact HP2| lia| auto]|]].
- eapply rheap_pres_of_munch; [exact MU1| exact WM1|]. intros a Ha CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
pose proof (RHEAP_block_range_proof _ _ _ b HEAP Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct sfP_ as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia.
- eapply rheap_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
assert (NE : blk_id b <> blk_id (p, A, n)).
{ intros E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND. cbn [map] in ND. inversion ND; subst.
apply H1. rewrite <- E. apply in_map. exact Hb. }
destruct (RHEAP_blocks_disjoint_proof _ _ _ b (p, A, n) HEAP2 ltac:(right; exact Hb) ltac:(left; reflexivity) NE) as [D|D];
cbn [blk_addr blk_size fst snd] in D; unfold in_block in Hab; lia. }
split; [exact PSF|]. split; [exact PSO|].
exists A. split; [reflexivity|]. split; [exact BR|].
split. { eapply RHEAP_frame_proof; [exact HEAP2| exact MU4| exact WM4|]. constructor; [|constructor].
right; right. exists (p, A, n). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
split; [exact ZCH|]. split; [exact EXPO|].
exists g, i. rewrite <- Hst. change (s_slots (strip st2)) with (s_slots st2). change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g).
split; [exact SL| split; [exact SC27| exact STR']].
-
destruct RES as [-> HEAP2].
step. if_cases Kp; zify_cond Kp. 2:{ exfalso. apply Kp. reflexivity. }
step. step. step. step. step. step.
replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp by (replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold rcalloc_post. sf_eexists 15%nat. exists m2, errv2.
split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
split; [rewrite ETP; unfold RERRNO; exact ERR2|]. split; [exact AUX2|].
split.
{ eapply rheap_pres_trans; [| eapply (rheap_pres_weaken LB LB (bv_unsigned sp + -32) (bv_unsigned sp)); [exact HP2| lia| auto]].
eapply rheap_pres_of_munch; [exact MU1| exact WM1|]. intros a Ha CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
pose proof (RHEAP_block_range_proof _ _ _ b HEAP Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct sfP_ as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia. }
split; [exact PSF|]. split; [exact PSO|]. split; [reflexivity| exact HEAP2].
Qed.
