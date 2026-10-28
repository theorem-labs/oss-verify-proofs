(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1po X1q3 X1pj X1qd X1q6 X1qm X1pn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0pa X0oz X0p3 X0p4 X0qn X0qd X0px X0qc
X0qp X0py X0q7 X0q8 X0q5 X0q6 X0qb.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lw X1m5 X1m6 X1kr X1kt X1lq X1lr X1ls X1lt X1fd X1ec.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3 X1r4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Import ListNotations.
Import X1bs.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition RREALLOC_SYM : Z := 0x3326c.
Definition RREALLOC_STACK : Z := 8256.

Definition rrealloc_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (oldbytes : list byte) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m' /\ rw_cells rsegs m' A [CB (Z.to_nat old) oldbytes] /\ rtop_known s' p
| Some q => exists A' junk,
a0 = Z_to_bv 64 A' /\ rblock_range A' n
/\ RHEAP s' ((q, A', n) :: lb_remove p LB) m'
/\ rw_cells rsegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n old)) oldbytes ++ junk)]
/\ rtop_known s' q /\ (q = p -> A' = A)
end.

Definition rrealloc_stmt_at {RCEIL : RunCeiling} (ENTRY : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbytes : list byte),
RHEAP s LB m -> In (p, A, old) LB -> rtop_known s p -> RBIG <= n ->
rw_cells rsegs m A [CB (Z.to_nat old) oldbytes] ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
implM rsegs (raw_realloc p n) s
(rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbytes m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).
Definition rrealloc_stmt {RCEIL : RunCeiling} : Prop := rrealloc_stmt_at RREALLOC_SYM.
Definition rlibc_realloc_stmt {RCEIL : RunCeiling} : Prop := rrealloc_stmt_at rrealloc_entry.

Lemma rre_epilogue : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(v6 v5 v4 v3 v2 v1 v0 vra : word) F fc (m : mem) (SP : Z),
64 <= SP < 2^64 ->
sp = Z_to_bv 64 (SP - 64) ->
rw_cells rsegs m (SP - 64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 SP) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc vra) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x33688) fc None m (seg_rom rsegs)).
Proof.
intros until SP. intros HSP -> FR.
step. step. step. step. step. step. step. step. step. step.
apply evt_done. rewrite ?unsigned_lit by lia. replace (SP - 64 + 64) with SP by lia. reflexivity.
Qed.

Section INPLACE_HEAP.
Context {RCEIL : RunCeiling}.
Variables (s : PState) (LB LB0 : list block) (st : mstate) (m1 : mem) (p : bptr) (A old n : Z)
(r : region) (g bm : aptr) (ai : Z) (ar : area) (b3 lo8 hi8 i off : Z).
Hypothesis PERM : Permutation LB0 LB.
Hypothesis Hst : strip st = ps_m s.
Hypothesis MR : rmrep st m1.
Hypothesis BL : brk_link st (ps_brk s).
Hypothesis AR : AREACH_from ref_reserved st LB0.
Hypothesis RPL : rw_cells rsegs m1 RREPLACED [C4 (wz 0)].
Hypothesis GA : RGA st (ps_hdr s) LB0.
Hypothesis HIN : In (p, A, old) LB.
Hypothesis HF : hdr_facts st (p, A, old) r g bm ai ar b3 lo8 hi8 i off.
Hypothesis EOFF : snd p = off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : UNIT * off + n <= get_stride (get_meta_rec st g) - IB.

Let c : cptr := fst p.
Let stride : Z := get_stride (get_meta_rec st g).
Let E : Z := r_base r + (snd c + stride - IB).
Let W : list (Z * Z) := [(A - 3, A - 2); (A + n, E)].
Let m' : mem := rre_ip_mem m1 A E n b3.

#[using="LB PERM HIN"] Lemma rip_IN0 : In (p, A, old) LB0.
Proof. eapply Permutation_in; [apply Permutation_sym; exact PERM| exact HIN]. Qed.

Lemma rip_geo :
A = r_base r + snd c + UNIT * off /\ 16 <= snd c + UNIT * off /\ 0 <= old /\ A + old <= E
/\ E + 4 <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ 4096 <= r_base r /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x6e000 <= r_base r)
/\ 16 <= stride /\ stride mod 16 = 0 /\ 0 <= off <= 255.
Proof using MR HF.
pose proof (hf_addr _ _ _ _ _ _ _ _ _ _ _ _ HF) as Faddr. pose proof (hf_snd _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fsnd.
pose proof (hf_b0 _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fb0. pose proof (hf_off _ _ _ _ _ _ _ _ _ _ _ _ HF) as Foff.
pose proof (hf_size _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fsize. pose proof (hf_fit _ _ _ _ _ _ _ _ _ _ _ _ HF) as Ffit.
pose proof (hf_span _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fspan. pose proof (hf_stride _ _ _ _ _ _ _ _ _ _ _ _ HF) as [S16 SM].
pose proof (hf_i _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fi. pose proof (hf_li _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fli.
pose proof (hf_reg _ _ _ _ _ _ _ _ _ _ _ _ HF) as Freg. pose proof (hf_rbase _ _ _ _ _ _ _ _ _ _ _ _ HF) as (RB0 & RBM & RBC).
unfold blk_addr, blk_slot, blk_size in Faddr, Fsnd, Fsize, Ffit, Freg. cbn [fst snd] in Faddr, Fsnd, Fsize, Ffit, Freg. fold c in Faddr, Fsnd, Freg. fold stride in Ffit, Fspan, S16, SM.
pose proof MR as (WF & _). pose proof WF as (_ & WR & _). first [ pose proof (WR (fst c) r Freg) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RFr | sf_fb; destruct (WR (fst c) r Freg) as (_ & _ & _ & _ & RFr) ].
pose proof (round_up_pg_ge (r_len r)) as RUP.
assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
assert (SIL : stride * i + stride <= stride * (m_last_idx (get_meta_rec st g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
assert (RP : 0 < round_up_pg (r_len r)) by (unfold UNIT, IB in *; lia).
pose proof (rreserved_disjoint1 _ _ RFr RP) as IMG.
unfold E. unfold UNIT, IB in *. repeat split; try lia.
all: (clear -RB0 RBM; Z.div_mod_to_equations; lia).
Qed.

Lemma rip_fn : A + n <= E.
Proof using HF FIT.
pose proof (hf_addr _ _ _ _ _ _ _ _ _ _ _ _ HF) as Faddr. unfold blk_addr, blk_slot in Faddr. cbn [fst snd] in Faddr.
unfold E, stride, c. clear -FIT Faddr. lia.
Qed.

Lemma rip_wr : wr_at rsegs m1 (A - 3) (E - A + 4) /\ bytes_at rsegs m1 (A - 3) [b8 b3].
Proof using MR HF FIT. clear N0.
pose proof rip_geo as sfP_; first [ sf_destruct 11%nat sfP_ as Faddr PLO OLD0 FO EHI RBC RB4 IMG S16 SM OFF | sf_fb; destruct sfP_ as (Faddr & PLO & OLD0 & FO & EHI & RBC & RB4 & IMG & S16 & SM & OFF) ]. pose proof rip_fn as FN.
pose proof (hf_reg _ _ _ _ _ _ _ _ _ _ _ _ HF) as Freg. pose proof (hf_kind _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fkind.
pose proof (hf_k3 _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fk3. unfold blk_slot in Freg, Fk3. cbn [fst snd] in Freg, Fk3. fold c in Freg, Fk3.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF _ _ _ _ SH | sf_fb; destruct sfP_ as (WF & _ & _ & _ & _ & SH) ]. destruct (SH (fst c) r Freg Fkind) as [HW HB].
split.
- eapply wr_at_sub; [exact HW| unfold E in *; lia| unfold E in *; lia].
- destruct (HB (snd c + UNIT * off - 3) b3 ltac:(unfold E in *; lia) Fk3) as [BK _].
replace (A - 3) with (r_base r + (snd c + UNIT * off - 3)) by lia. exact BK.
Qed.

Lemma rip_munch : munch W m1 m' /\ wmono rsegs m1 m'.
Proof using MR HF N0 FIT.
pose proof rip_geo as sfP_; first [ sf_destruct 11%nat sfP_ as Faddr PLO OLD0 FO EHI RBC RB4 IMG S16 SM OFF | sf_fb; destruct sfP_ as (Faddr & PLO & OLD0 & FO & EHI & RBC & RB4 & IMG & S16 & SM & OFF) ]. pose proof rip_fn as FN.
unfold alloc_ceiling in RBC.
unfold m', rre_ip_mem. cbv zeta. unfold W.
destruct (Z.eqb_spec (E - A - n) 0) as [R0|R0]; destruct (Z.leb_spec 5 (E - A - n)) as [R5|R5]; try lia.
- split; [| apply wmono_write; apply wmono_refl].
apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia].
- split; [| repeat apply wmono_write; apply wmono_refl].
apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [| lia| rewrite length_le4; cbn; lia| rewrite length_le4; cbn -[Z.add Z.sub Z.le Z.lt Z.mul]; lia].
apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia].
- split; [| repeat apply wmono_write; apply wmono_refl].
apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia].
Qed.

Lemma rip_out : forall SP a, alloc_ceiling <= SP -> rclient_addr (lb_remove p LB) SP a -> outside W a.
Proof using PERM MR AR HIN HF N0 FIT.
intros SP a HSP CA.
pose proof rip_geo as sfP_; first [ sf_destruct 11%nat sfP_ as Faddr PLO OLD0 FO EHI RBC RB4 IMG S16 SM OFF | sf_fb; destruct sfP_ as (Faddr & PLO & OLD0 & FO & EHI & RBC & RB4 & IMG & S16 & SM & OFF) ]. pose proof rip_fn as FN.
pose proof (hf_reg _ _ _ _ _ _ _ _ _ _ _ _ HF) as Freg. pose proof (hf_kind _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fkind.
pose proof (hf_slot _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fslot. unfold blk_slot in Freg, Fslot. cbn [fst snd] in Freg, Fslot. fold c in Freg, Fslot.
unfold alloc_ceiling in *. cbn.
destruct CA as [CA|[[CA NS]|(b & Hb & Hab)]].
- split; [|split; [|exact I]]; lia.
- split; [|split; [|exact I]]; lia.
- unfold lb_remove in Hb. apply In_filter_iff in Hb. destruct Hb as [HbL Hne].
assert (Hb0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact HbL]).
pose proof (X0q8.areach_facts_proof _ _ AR) as MF.
assert (NEs : blk_slot b <> c).
{ intros Es. pose proof (NoDup_map_inj_in blk_slot LB0 (mf_nodup _ _ MF) b (p, A, old) Hb0 rip_IN0 Es) as ->.
revert Hne. cbn [blk_id fst snd]. unfold bptr_eqb. rewrite X1pv.aptr_eqb_refl, Z.eqb_refl. cbn. tauto. }
unfold in_block in Hab.
destruct (N.eq_dec (fst (blk_slot b)) (fst c)) as [EF|NEF].
+
destruct (blocks_apart_of_areach st LB0 b (p, A, old) g i AR Hb0 rip_IN0 NEs EF Fslot) as [X|X];
unfold blk_slot, blk_addr, blk_size in X; cbn [fst snd] in X; fold c in X; rewrite (conc_region' st c r Freg) in X; unfold blk_addr, blk_size in Hab; cbn [fst snd] in Hab;
unfold E, IB, UNIT in *; (split; [|split; [|exact I]]); lia.
+
first [ pose proof (rblock_inside st LB0 m1 b MF MR Hb0) as sfP_; sf_destruct 9%nat sfP_ as rb gb ib Hrb Krb _ LOb HIb _ | sf_fb; destruct (rblock_inside st LB0 m1 b MF MR Hb0) as (rb & gb & ib & Hrb & Krb & _ & LOb & HIb & _) ].
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ DJ _ | sf_fb; destruct sfP_ as (_ & _ & DJ & _) ].
destruct (DJ _ _ _ _ Freg Hrb ltac:(congruence)) as [X|X]; rewrite ?(lr_lo_group rb Krb), ?(lr_lo_group r Fkind) in X;
unfold blk_addr, blk_size in Hab, LOb, HIb; cbn [fst snd] in Hab, LOb, HIb; unfold E in *; (split; [|split; [|exact I]]); lia.
Qed.

Lemma rip_block (oldbytes : list byte) :
rw_cells rsegs m1 A [CB (Z.to_nat old) oldbytes] ->
exists junk, rw_cells rsegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n old)) oldbytes ++ junk)].
Proof using MR HF N0 FIT.
intros OLD1. pose proof rip_geo as sfP_; first [ sf_destruct 11%nat sfP_ as Faddr PLO OLD0 FO EHI RBC RB4 IMG S16 SM OFF | sf_fb; destruct sfP_ as (Faddr & PLO & OLD0 & FO & EHI & RBC & RB4 & IMG & S16 & SM & OFF) ]. pose proof rip_fn as FN.
unfold alloc_ceiling in RBC.
pose proof rip_munch as [MU WM]. pose proof rip_wr as [WR _].
pose proof OLD1 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LEN _].
destruct (Z.le_gt_cases n old) as [LE|GT].
- exists []. rewrite Z.min_l, app_nil_r by lia.
pose proof (rw_cells_split_CB rsegs m1 A [] (Z.to_nat old) oldbytes [] [Z.to_nat n; (Z.to_nat old - Z.to_nat n)%nat] OLD1 ltac:(cbn; lia)) as SPL.
cbn [app mk_CB_cells] in SPL. apply rw_cells_uncons in SPL. destruct SPL as [SPL _].
eapply rw_cells_transport; [exact SPL| exact MU| exact WM|]. unfold W. cbn [cells_size csize disjoint_from Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
- assert (OLD' : rw_cells rsegs m' A [CB (Z.to_nat old) oldbytes]).
{ eapply rw_cells_transport; [exact OLD1| exact MU| exact WM|]. unfold W. cbn [cells_size csize disjoint_from Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
assert (WR' : wr_at rsegs m' (A + old) (n - old)).
{ eapply wr_at_transport; [| exact WM]. eapply wr_at_sub; [exact WR| lia| lia]. }
destruct (rwr_at_bytes_exist m' (A + old) (n - old) WR' ltac:(lia) ltac:(lia)) as (junk & LJ & BJ).
exists junk. rewrite Z.min_r by lia. rewrite firstn_all2 by lia.
assert (J : rw_cells rsegs m' A ([CB (Z.to_nat old) oldbytes] ++ [CB (Z.to_nat (n - old)) junk])).
{ apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact OLD'|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
split; [split; [cbn; split; [lia| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BJ]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WR'. }
pose proof (rw_cells_merge rsegs m' A [] ([CB (Z.to_nat old) oldbytes] ++ [CB (Z.to_nat (n - old)) junk]) []) as MG.
rewrite !app_nil_r in MG. cbn [app] in MG. specialize (MG J). cbn [cells_size csize cells_bytes cbytes app Nat.add] in MG.
rewrite ?app_nil_r, ?Nat.add_0_r in MG. replace (Z.to_nat old + Z.to_nat (n - old))%nat with (Z.to_nat n) in MG by lia. exact MG.
Qed.

Hypothesis SC48 : m_sizeclass (get_meta_rec st g) < 48.

Lemma rip_R32 : stride - IB - UNIT * off - n < 2^32 /\ stride < 2^20.
Proof using AR HF N0 FIT SC48.
pose proof (stride_small_of_areach st LB0 bm g ai AR (hf_hosts _ _ _ _ _ _ _ _ _ _ _ _ HF) SC48) as S20. fold stride in S20.
pose proof (hf_off _ _ _ _ _ _ _ _ _ _ _ _ HF) as Foff. unfold UNIT, IB in *. lia.
Qed.

Lemma rip_heap : RHEAP s ((p, A, n) :: lb_remove p LB) m'.
Proof using PERM Hst MR BL AR RPL GA HIN HF EOFF N0 FIT SC48.
pose proof rip_geo as sfP_; first [ sf_destruct 11%nat sfP_ as Faddr PLO OLD0 FO EHI RBC RB4 IMG S16 SM OFF | sf_fb; destruct sfP_ as (Faddr & PLO & OLD0 & FO & EHI & RBC & RB4 & IMG & S16 & SM & OFF) ]. pose proof rip_fn as FN.
pose proof rip_R32 as [R32 S20].
pose proof (hf_slot _ _ _ _ _ _ _ _ _ _ _ _ HF) as Fslot. pose proof (hf_reg _ _ _ _ _ _ _ _ _ _ _ _ HF) as Freg.
unfold blk_slot in Fslot, Freg. cbn [fst snd] in Fslot, Freg. fold c in Fslot, Freg.
pose proof (X0q8.areach_facts_proof _ _ AR) as MF.
pose proof (mf_ticks _ _ MF) as TK.
assert (Haddr : blk_addr (p, A, old) = conc st (blk_slot (p, A, old)) + UNIT * off).
{ unfold blk_addr, blk_slot. cbn [fst snd]. fold c. rewrite (conc_region' st c r Freg). lia. }
assert (FIT' : forall g0 idx, s_slots st !! (blk_slot (p, A, old)) = Some (g0, idx) ->
UNIT * off + n <= get_stride (get_meta_rec st g0) - IB /\ get_stride (get_meta_rec st g0) - IB - UNIT * off - n < 2^32).
{ unfold blk_slot. cbn [fst]. fold c. intros g0 idx Hs. rewrite Fslot in Hs. inversion Hs; subst. split; [exact FIT| exact R32]. }
assert (EST : resize_state st c off n = X1qm.stf st c off n g i).
{ unfold resize_state. rewrite Fslot. unfold X1qm.stf. rewrite <- (resize_body_eq st c off n g i). reflexivity. }
pose proof (rre_ip_rmrep st m1 (p, A, old) r g bm ai ar b3 lo8 hi8 i off n MR TK HF N0 FIT R32) as [MR' TK'].
unfold blk_slot in MR'. cbn [fst snd] in MR'. fold c in MR'. fold stride in MR'.
replace (r_base r + (snd c + UNIT * off)) with A in MR' by lia.
exists (resize_state st c off n), (lb_resize (p, A, old) n LB0).
split.
{ unfold lb_resize. cbn [blk_id blk_addr fst snd]. apply perm_skip.
rewrite (lb_remove_lbrm LB p A old (NoDup_map_perm blk_slot LB0 LB PERM (mf_nodup _ _ MF)) HIN). unfold lbrm. cbn [blk_slot fst].
apply filter_Permutation. exact PERM. }
split.
{ rewrite <- Hst, EST. pose proof (resize_ctrl st c off n g i) as [CE _]. unfold strip.
rewrite (ce_ctx _ _ CE), (ce_regions _ _ CE), (ce_next_rid _ _ CE), (ce_metas _ _ CE), (ce_areas _ _ CE), (ce_groups _ _ CE),
(ce_slots _ _ CE), (ce_secret _ _ CE), (ce_ceil _ _ CE), (ce_reserved _ _ CE). reflexivity. }
split; [rewrite EST; exact MR'|].
split.
{ split.
- pose proof (resize_ctrl st c off n g i) as [CE _]. rewrite EST. unfold brk_link, ctx, conc, get_region in *.
rewrite (ce_ctx _ _ CE), (ce_regions _ _ CE). exact BL.
- exact (areach_resize st LB0 (p, A, old) off n AR rip_IN0 ltac:(lia) Haddr N0 FIT'). }
split.
{ pose proof rip_munch as [MU WM]. eapply rw_cells_transport; [exact RPL| exact MU| exact WM|].
unfold RREPLACED. cbn. unfold E in *. repeat split; lia. }
exact (rga_resize ref_reserved st LB0 (p, A, old) off n (ps_hdr s) AR rip_IN0 ltac:(lia) Haddr N0 FIT' GA).
Qed.

End INPLACE_HEAP.

Section TOPLEVEL.
Context {RCEIL : RunCeiling}.
Hypothesis HM : rlibc_malloc_stmt.
Hypothesis HFR : rlibc_free_stmt.

#[using="Type"] Lemma in_lb_remove_sub (q : bptr) L b : In b (lb_remove q L) -> In b L.
Proof. unfold lb_remove. intros H. apply In_filter_iff in H. tauto. Qed.

#[using="HM HFR"] Lemma rre_move : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m1 : mem)
(s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbytes : list byte),
RHEAP s LB m1 -> In (p, A, old) LB -> rtop_known s p -> RBIG <= n ->
rw_cells rsegs m1 A [CB (Z.to_nat old) oldbytes] ->
rauxv_ok m1 B -> bv_unsigned sp <= B ->
stk rsegs m1 lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> mem_inv rsegs m1 -> tp = Z_to_bv 64 RATP ->
0 <= n < MMAP_THRESHOLD ->
rw_cells rsegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rheap_pres (lb_remove p LB) (bv_unsigned sp) m0 m1 ->
implM rsegs (mbind (raw_malloc n) (fun q => match q with None => mret None | Some q' => mbind (raw_free p) (fun _ => mret (Some q')) end)) s
(rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbytes m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x335f8) fc None m1 (seg_rom rsegs)).
Proof.
intros until oldbytes. intros HEAP1 HIN TOPK BIGN OLD1 AUX1 SB ST1 CLO LO ERR1 MI1 TP N FR1 PRES01.
unfold RREALLOC_STACK in LO. unfold MMAP_THRESHOLD, IB, UNIT in N.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TP; unfold errno_addr, RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR1. unfold RERRNO in ERR1.
pose proof (RHEAP_block_range_proof _ _ _ _ HEAP1 HIN) as BR. unfold blk_addr, blk_size in BR. cbn [fst snd] in BR.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as A0 A16 OLD0 ACE AIMG | sf_fb; destruct sfP_ as (A0 & A16 & OLD0 & ACE & AIMG) ]. unfold alloc_ceiling in ACE.
pose proof OLD1 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LEN _].

eapply (implM_evt rsegs _ _ _ (fun ms2 => ms2 = _)).
{ step. step. step. step. apply evt_done. reflexivity. }
cbv beta. intros ms' ->.
eapply implM_bind.
{ eapply HM.
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
- unfold MMAP_THRESHOLD in N. lia. }
cbv beta. intros q s' ms' POST.
first [ sf_destruct 26%nat POST as w0 w1 w2 ra0 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m2 errv2 -> MI2 ST2 ERR2 AUX2 HP2 PSF PSO RES | sf_fb; destruct POST as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & PSF & PSO & RES) ].
rewrite unsigned_lit in ST2 by lia. rewrite unsigned_lit in HP2 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR2. unfold RERRNO in ERR2.
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [exact HP2| exact FR1|]. left. lia. }
assert (OLD2 : rw_cells rsegs m2 A [CB (Z.to_nat old) oldbytes]).
{ eapply rheap_pres_rw_cells; [exact HP2| exact OLD1|]. right; right. exists (p, A, old). split; [exact HIN|].
unfold blk_addr, blk_size. cbn [fst snd cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
assert (PRES02 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m0 m2).
{ eapply rheap_pres_trans; [exact PRES01|]. eapply rheap_pres_weaken; [exact HP2| lia| apply in_lb_remove_sub]. }
destruct q as [q|].
-
first [ sf_destruct 8%nat RES as A' junk -> BR' HEAP2 UCH EXPO SMALLB | sf_fb; destruct RES as (A' & junk & -> & BR' & HEAP2 & UCH & EXPO & SMALLB) ].
pose proof BR' as sfP_; first [ sf_destruct 5%nat sfP_ as A0' A16' N0' ACE' AIMG' | sf_fb; destruct sfP_ as (A0' & A16' & N0' & ACE' & AIMG') ]. unfold alloc_ceiling in ACE'.
cbv beta iota.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND. cbn [map] in ND. unfold blk_id in ND at 1. cbn [fst snd] in ND.
assert (NEqp : q <> p).
{ intros ->. inversion ND; subst. apply H1. apply (in_map blk_id LB (p, A, old)). exact HIN. }
pose proof (RHEAP_blocks_disjoint_proof _ _ _ (q, A', n) (p, A, old) HEAP2 ltac:(left; reflexivity) ltac:(right; exact HIN)
ltac:(unfold blk_id; cbn [fst snd]; exact NEqp)) as DJ. unfold blk_addr, blk_size in DJ; cbn [fst snd] in DJ.

eapply (implM_evt rsegs _ _ _ (fun ms3 => ms3 = MS (mkR (Z_to_bv 64 0x33608) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp w0 w1 w2 (Z_to_bv 64 n) (Z_to_bv 64 A)
(Z_to_bv 64 A') (Z_to_bv 64 old) (Z_to_bv 64 (Z.min n old)) w6 w7 w8 w9 w10 (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 w11 w12 w13 w14)
F (Z_to_bv 64 0x3361c) fc None m2 (seg_rom rsegs))).
{ step. if_cases Kq; zify_cond Kq. { exfalso. clear -Kq A0'. lia. }
step. rewrite ?unsigned_lit by lia. replace (A + old - A) with old by lia.
step. step. if_cases Kc; zify_cond Kc.
- apply evt_done. rewrite Z.min_l by lia. reflexivity.
- step. apply evt_done. rewrite Z.min_r by lia. reflexivity. }
cbv beta. intros ms3 ->.
set (mn := Z.min n old) in *. assert (MN : 0 <= mn <= n /\ mn <= old) by (subst mn; lia).
assert (Emn : mn = Z.min n old) by reflexivity. clearbody mn.

pose proof (rw_cells_split_CB rsegs m2 A' [] (Z.to_nat n) junk [] [Z.to_nat mn; (Z.to_nat n - Z.to_nat mn)%nat] UCH ltac:(cbn; lia)) as SPL.
cbn [app mk_CB_cells] in SPL. apply rw_cells_uncons in SPL. destruct SPL as [DST REST]. cbn [csize] in REST.
set (jr := firstn (Z.to_nat n - Z.to_nat mn) (skipn (Z.to_nat mn) junk)) in REST. clearbody jr.
pose proof (rw_cells_split_CB rsegs m2 A [] (Z.to_nat old) oldbytes [] [Z.to_nat mn; (Z.to_nat old - Z.to_nat mn)%nat] OLD2 ltac:(cbn; lia)) as SPL2.
cbn [app mk_CB_cells] in SPL2. apply rw_cells_uncons in SPL2. destruct SPL2 as [[[_ SRC] _] _].
cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
assert (LMN : length (firstn (Z.to_nat mn) oldbytes) = Z.to_nat mn) by (rewrite length_firstn; lia).

eapply (implM_evt rsegs _ _ _ (memcpy_post (Z_to_bv 64 0x33628) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 A') (Z_to_bv 64 A)
(Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 mn) (firstn (Z.to_nat mn) oldbytes) m2)).
{ step. step. step.
eapply memcpy_spec; rewrite ?unsigned_lit by lia; [exact SRC| exact LMN| exact DST| clear -DJ MN; lia| exact MI2]. }
cbv beta. intros ms4 sfH_; first [ sf_destruct 21%nat sfH_ as u0 u1 u2 ua1 ua2 u3 u4 u5 u6 u7 u11 u12 u13 u14 m3 -> MU3 WM3 MI3 DST3 SRC3 | sf_fb; destruct sfH_ as (u0 & u1 & u2 & ua1 & ua2 & u3 & u4 & u5 & u6 & u7 & u11 & u12 & u13 & u14 & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3) ].
rewrite ?unsigned_lit in MU3 by lia. rewrite ?unsigned_lit in DST3 by lia. rewrite ?unsigned_lit in SRC3 by lia. rewrite ret_pc_even by lia. change X1fd.rsegs with rsegs in *.

assert (HEAP3 : RHEAP s' ((q, A', n) :: LB) m3).
{ eapply RHEAP_frame_proof; [exact HEAP2| exact MU3| exact WM3|]. constructor; [|constructor].
right; right. exists (q, A', n). split; [left; reflexivity|]. unfold blk_addr, blk_size. cbn [fst snd]. clear -MN. lia. }
assert (DJhi : forall a k, lo <= a -> disjoint_from [(A', A' + mn)] a k) by (intros a k Ha; cbn; split; [right; lia| exact I]).
assert (DJimg : forall a k, a + k <= 0x6e000 -> 0x10000 <= a -> disjoint_from [(A', A' + mn)] a k) by (intros a k H1 H2; cbn; split; [lia| exact I]).
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| apply DJhi; lia]).
assert (ERR3 : rw_cells rsegs m3 316332 [C4 errv2]) by (eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| apply DJimg; cbn; lia]).
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3| apply DJhi; lia]).
assert (AUX3 : rauxv_ok m3 B).
{ eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
assert (REST3 : rw_cells rsegs m3 (A' + Z.of_nat (Z.to_nat mn)) [CB (Z.to_nat n - Z.to_nat mn) jr]).
{ eapply rw_cells_transport; [exact REST| exact MU3| exact WM3|]. cbn [cells_size csize Nat.add disjoint_from]. split; [right; lia| exact I]. }

eapply (implM_evt rsegs _ _ _ (fun ms5 => ms5 = _)).
{ step. step. apply evt_done. reflexivity. }
cbv beta. intros ms5 ->.
eapply implM_bind.
{ eapply (HFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 s' ((q, A', n) :: LB) p A old lo B errv2).
- exact HEAP3.
- right. exact HIN.
- exact AUX3.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST3.
- exact CLO.
- unfold RFREE_STACK. rewrite unsigned_lit by lia. lia.
- rewrite ETP. unfold RERRNO. exact ERR3.
- exact MI3.
- exact TP.
- reflexivity. }
cbv beta. intros [] s'' ms'' POSTF.
first [ sf_destruct 25%nat POSTF as v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 v11 v12 v13 v14 m4 -> MI4 ST4 ERR4 AUX4 HP4 PSF' PSO' HEAP4 | sf_fb; destruct POSTF as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v11 & v12 & v13 & v14 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & PSF' & PSO' & HEAP4) ].
rewrite unsigned_lit in ST4 by lia. rewrite unsigned_lit in HP4 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR4. unfold RERRNO in ERR4.
apply implM_ret.
assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [exact HP4| exact FR3|]. left. lia. }

step. step.
eapply evt_cut; [eapply (rre_epilogue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m4 (bv_unsigned sp)); [lia| f_equal; lia| ]|].
{ replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia. exact FR4. }
cbv beta. intros ms6 ->.
release_frame FR4 ST4 (bv_unsigned sp).

assert (ELB : lb_remove p ((q, A', n) :: LB) = (q, A', n) :: lb_remove p LB).
{ unfold lb_remove. rewrite filter_cons. destruct (decide _) as [D|D]; [reflexivity|]. exfalso. apply D.
unfold blk_id, bptr_eqb. cbn [fst snd].
destruct (X1pv.aptr_eqb_spec (fst q) (fst p)) as [E1|NE1]; cbn [andb negb]; [|exact I].
destruct (Z.eqb_spec (snd q) (snd p)) as [E2|NE2]; cbn [negb]; [|exact I].
exfalso. apply NEqp. destruct q, p; cbn in E1, E2; congruence. }
rewrite ELB in HP4, HEAP4.

assert (NEWB : rw_cells rsegs m4 A' [CB (Z.to_nat n) (firstn (Z.to_nat mn) oldbytes ++ jr)]).
{ assert (J : rw_cells rsegs m3 A' ([CB (Z.to_nat mn) (firstn (Z.to_nat mn) oldbytes)] ++ [CB (Z.to_nat n - Z.to_nat mn) jr])).
{ apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact DST3|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact REST3. }
pose proof (rw_cells_merge rsegs m3 A' [] ([CB (Z.to_nat mn) (firstn (Z.to_nat mn) oldbytes)] ++ [CB (Z.to_nat n - Z.to_nat mn) jr]) []) as MG.
rewrite !app_nil_r in MG. cbn [app] in MG. specialize (MG J). cbn [cells_size csize cells_bytes cbytes app Nat.add] in MG.
rewrite ?app_nil_r, ?Nat.add_0_r in MG. replace (Z.to_nat mn + (Z.to_nat n - Z.to_nat mn))%nat with (Z.to_nat n) in MG by lia.
eapply rheap_pres_rw_cells; [exact HP4| exact MG|]. right; right. exists (q, A', n). split; [left; reflexivity|].
unfold blk_addr, blk_size. cbn [fst snd cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
apply evt_done. unfold rrealloc_post. sf_eexists 15%nat. exists m4, errv2.
split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact MI4|]. split; [exact ST4|]. split; [rewrite ETP; unfold RERRNO; exact ERR4|]. split; [exact AUX4|].
split.
{ eapply rheap_pres_trans; [exact PRES02|]. eapply rheap_pres_trans.
- eapply rheap_pres_of_munch; [exact MU3| exact WM3|]. intros a Ha CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
pose proof (in_lb_remove_sub _ _ _ Hb) as HbL.
assert (NE : blk_id b <> blk_id (q, A', n)).
{ intros E. inversion ND; subst. apply H1. replace q with (blk_id b) by (rewrite E; reflexivity). apply in_map. exact HbL. }
destruct (RHEAP_blocks_disjoint_proof _ _ _ b (q, A', n) HEAP2 ltac:(right; exact HbL) ltac:(left; reflexivity) NE) as [D|D];
cbn [blk_addr blk_size fst snd] in D; unfold in_block in Hab; clear -D Hab MN; lia.
- eapply rheap_pres_weaken; [exact HP4| lia|]. intros b Hb. right. exact Hb. }
split; [rewrite PSF'; exact PSF|]. split; [rewrite PSO'; exact PSO|].
exists A', jr. split; [reflexivity|]. split; [exact BR'|]. split; [exact HEAP4|]. split; [rewrite <- Emn; exact NEWB|].
split; [| intros E; exfalso; exact (NEqp E)].
eapply (RHEAP_top_known_proof s'' _ m4 q A' n); [exact HEAP4| left; reflexivity| exact BIGN].
-
destruct RES as [-> HEAP2]. cbv beta iota. apply implM_ret.
step. if_cases Kq; zify_cond Kq. 2:{ exfalso. apply Kq. reflexivity. }
eapply evt_cut; [eapply (rre_epilogue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (bv_unsigned sp)); [lia| f_equal; lia| ]|].
{ replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia. exact FR2. }
cbv beta. intros ms6 ->.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold rrealloc_post. sf_eexists 15%nat. exists m2, errv2.
split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact MI2|]. split; [exact ST2|]. split; [rewrite ETP; unfold RERRNO; exact ERR2|]. split; [exact AUX2|].
split; [exact PRES02|]. split; [exact PSF|]. split; [exact PSO|].
split; [reflexivity|]. split; [exact HEAP2|]. split; [exact OLD2|]. exact TOPK.
Qed.
End TOPLEVEL.

Section TOPLEVEL2.
Context {RCEIL : RunCeiling}.
Hypothesis HM : rlibc_malloc_stmt.
Hypothesis HFR : rlibc_free_stmt.

#[using="HM HFR"] Theorem rlibc_realloc_spec_proof : rlibc_realloc_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A old n lo B errv oldbytes.
intros HEAP HIN TOPK BIGN OLD AUXB SB ST CLO LO ERR MI TP HA0 HA1 N. unfold rrealloc_entry.
pose proof LO as LOv. unfold RREALLOC_STACK in LOv. pose proof N as Nv. unfold MMAP_THRESHOLD, IB, UNIT in Nv.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
pose proof (RHEAP_block_range_proof _ _ _ _ HEAP HIN) as BR. unfold blk_addr, blk_size in BR. cbn [fst snd] in BR.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as A0 A16 OLD0 ACE AIMG | sf_fb; destruct sfP_ as (A0 & A16 & OLD0 & ACE & AIMG) ]. unfold alloc_ceiling in ACE.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TP; unfold errno_addr, RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR. unfold RERRNO in ERR.
subst a0 a1.

unfold raw_realloc.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (negb (ptop p)) with false by (symmetry; unfold ptop; unfold rtop_known in TOPK; rewrite (proj2 (Z.leb_le 0 (snd p)) TOPK); reflexivity).
eapply (implM_bind rsegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0' s1' ms1 (-> & -> & ->). cbv beta.

pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl rsegs m) as WM0.
carve_frame 64%nat ST.
eapply (implM_evt rsegs _ _ _ (fun ms2 => exists m1,
ms2 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 0x7fffffffffffefff) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x332c8) fc None m1 (seg_rom rsegs)
/\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -64)
/\ rw_cells rsegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1)).
{ step. if_cases KA; zify_cond KA. { exfalso. clear -KA A0. lia. }
step. step. step. step. step. step. step. step. step. step. step. step.
step. if_cases KN; zify_cond KN. 2:{ exfalso. apply KN. rewrite ?unsigned_lit by lia. lia. }
apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption. }
clear MU0 WM0. cbv beta. intros ms2 sfH_; first [ sf_destruct 7%nat sfH_ as m1 -> MI1 ST1 FR1 MU1 WM1 | sf_fb; destruct sfH_ as (m1 & -> & MI1 & ST1 & FR1 & MU1 & WM1) ].
assert (HEAP1 : RHEAP s LB m1).
{ eapply RHEAP_frame_proof; [exact HEAP| exact MU1| exact WM1|]. constructor; [|constructor]. left. cbn [fst]. lia. }
assert (AUX1 : rauxv_ok m1 B).
{ eapply rauxv_ok_frame; [exact AUXB| exact MU1| exact WM1|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
assert (OLD1 : rw_cells rsegs m1 A [CB (Z.to_nat old) oldbytes]).
{ eapply rw_cells_transport; [exact OLD| exact MU1| exact WM1|]. cbn [cells_size csize Nat.add disjoint_from]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [left; lia| exact I]. }
assert (ERR1 : rw_cells rsegs m1 316332 [C4 errv]).
{ eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. split; [left; lia| exact I]. }
assert (PRES01 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m1).
{ eapply rheap_pres_of_munch; [exact MU1| exact WM1|]. intros a Ha CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
pose proof (RHEAP_block_range_proof _ _ _ b HEAP (in_lb_remove_sub _ _ _ Hb)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct sfP_ as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. unfold in_block in Hab. lia. }
clear ST MI ERR OLD AUXB.

pose proof HEAP1 as HEAP1c. first [ sf_destruct 8%nat HEAP1c as st LB0 PERM Hst MR1 [BL1 AR] RPL1 GA | sf_fb; destruct HEAP1c as (st & LB0 & PERM & Hst & MR1 & [BL1 AR] & RPL1 & GA) ].
assert (IN0 : In (p, A, old) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact HIN]).
first [ pose proof (hdr_facts_of_areach st LB0 (p, A, old) AR IN0) as sfP_; sf_destruct 11%nat sfP_ as r g bm ai ar b3 lo8 hi8 i off HF | sf_fb; destruct (hdr_facts_of_areach st LB0 (p, A, old) AR IN0) as (r & g & bm & ai & ar & b3 & lo8 & hi8 & i & off & HF) ].
pose proof (hf_slot _ _ _ _ _ _ _ _ _ _ _ _ HF) as SL. pose proof (hf_addr _ _ _ _ _ _ _ _ _ _ _ _ HF) as HADDR.
pose proof (hf_reg _ _ _ _ _ _ _ _ _ _ _ _ HF) as HREG. pose proof (hf_off _ _ _ _ _ _ _ _ _ _ _ _ HF) as HOFF.
pose proof (hf_fit _ _ _ _ _ _ _ _ _ _ _ _ HF) as HFIT. pose proof (hf_stride _ _ _ _ _ _ _ _ _ _ _ _ HF) as [S16 SM16].
pose proof (hf_sc _ _ _ _ _ _ _ _ _ _ _ _ HF) as HSC.
unfold blk_slot, blk_addr, blk_size in SL, HADDR, HREG, HFIT. cbn [fst snd] in SL, HADDR, HREG, HFIT. unfold UNIT, IB in HADDR, HFIT, HOFF, S16, SM16.
set (c := fst p) in *. set (mr := get_meta_rec st g) in *. set (stride := get_stride mr) in *.

pose proof (proj1 (proj2 GA) _ IN0) as GE. unfold blk_slot, blk_id, blk_addr in GE. cbn [fst snd] in GE. fold c in GE.
assert (TOPc : slot_top st c = true).
{ unfold rtop_known in TOPK. clear - GE TOPK. destruct (slot_top st c); [reflexivity|]. exfalso. lia. }
rewrite TOPc in GE. destruct GE as (_ & GADDR & GHDR).
assert (CONC : conc st c = r_base r + snd c) by (apply conc_region'; exact HREG).
assert (EOFF : snd p = off) by (rewrite CONC in GADDR; unfold UNIT in *; lia).
rewrite <- Hst. cbv zeta. change (s_slots (strip st) !! c) with (s_slots st !! c). rewrite SL.
change (get_meta_rec (strip st) g) with mr. fold stride.
replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia). rewrite EOFF.

eapply implM_evt.
{ eapply (rre_hdr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st (p, A, old) r g bm ai ar b3 lo8 hi8 i off MR1 MI1 HF).
unfold blk_addr. cbn [fst snd]. apply unsigned_lit. lia. }
cbv beta. intros ms3 POST3. unfold rre_hdr_post in POST3. first [ sf_destruct 4%nat POST3 as y2 y3 y4 E3 | sf_fb; destruct POST3 as (y2 & y3 & y4 & E3) ].
unfold blk_addr, blk_slot, blk_size in E3. cbn [fst snd] in E3. fold c in E3. fold mr in E3. fold stride in E3. subst ms3.
set (E := r_base r + (snd c + stride - IB)) in *.
replace (E - (snd c + stride - IB - (snd c + UNIT * off) - old)) with (A + old) by (unfold E; lia).
set (sc := m_sizeclass mr) in *.
assert (AVAIL : E - A = stride - IB - UNIT * off) by (unfold E; lia).
assert (SCR : 0 <= sc < 48 \/ sc = 63) by (clear -HSC; destruct HSC as [(H & _)|(H & _)]; lia).
assert (FITn : n <= stride - 4 - 16 * off -> UNIT * off + n <= get_stride (get_meta_rec st g) - IB) by (unfold stride, mr, IB, UNIT in *; intros; lia).
pose proof (size_to_class_props n N) as (STC & _ & _).
unfold IB, UNIT in AVAIL.
pose proof (rip_geo st m1 p A old r g bm ai ar b3 lo8 hi8 i off MR1 HF) as sfP_; first [ sf_destruct 9%nat sfP_ as _ PLO _ FO EHI RBC RB4 IMG _ | sf_fb; destruct sfP_ as (_ & PLO & _ & FO & EHI & RBC & RB4 & IMG & _) ].
fold c in PLO, FO, EHI. fold mr in PLO, FO, EHI. fold stride in PLO, FO, EHI. fold E in FO, EHI. unfold alloc_ceiling in RBC. unfold UNIT in PLO.

assert (MOVE : forall (z5 z6 z7 z12 z13 z14 z15 z16 z17 z28 z29 : word),
implM rsegs (mbind (raw_malloc n) (fun q => match q with None => mret None | Some q' => mbind (raw_free p) (fun _ => mret (Some q')) end)) s
(rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbytes m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp z5 z6 z7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) z12 z13 z14 z15 z16 z17
(Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 t5 t6) F (Z_to_bv 64 0x335f8) fc None m1 (seg_rom rsegs))).
{ intros. eapply (rre_move HM HFR); try eassumption. all: try (rewrite ETP; unfold RERRNO; exact ERR1). all: match goal with |- ?G => idtac G end. }

destruct (Z.leb_spec n (stride - IB - UNIT * off)) as [LE|GT]; unfold IB, UNIT in LE |- || unfold IB, UNIT in GT |-.
- cbn [andb]. destruct (Z.leb_spec sc (size_to_class n + 1)) as [IP|MV].
+
assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by (unfold sc, mr in *; clear -SCR IP STC; lia).
apply implM_ret.

step. step. step. if_cases K1; zify_cond K1. { exfalso. clear -K1 Nv. rewrite ?unsigned_lit in K1 by lia. lia. }
step. if_cases K2; zify_cond K2. { exfalso. clear -K2 LE AVAIL. rewrite ?unsigned_lit in K2 by lia. lia. }

eapply evt_cut; [eapply (rre_stc_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n); [reflexivity| exact N| reflexivity| exact MI1]|].
cbv beta. intros ms4 sfH_; first [ sf_destruct 5%nat sfH_ as z1 z4 z5 z7 -> | sf_fb; destruct sfH_ as (z1 & z4 & z5 & z7 & ->) ].
step. if_cases K4; zify_cond K4.
2:{ exfalso. clear -K4 IP SCR STC. unfold sc in *. rewrite ?signed_wz_small in K4 by lia. lia. }

pose proof (rip_wr st m1 p A old n r g bm ai ar b3 lo8 hi8 i off MR1 HF (FITn LE)) as [WR BK]. fold c mr stride in WR. fold E in WR.
assert (FN : A + n <= E) by (clear -LE AVAIL; lia).
pose proof (rip_R32 LB0 st p A old n r g bm ai ar b3 lo8 hi8 i off AR HF ltac:(lia) (FITn LE) SC48) as [R32 S20]. fold mr stride in R32, S20.
eapply evt_cut.
{ eapply (rre_ip_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 A E n b3);
[apply unsigned_lit; (clear - FN LE RBC EHI FO S16 off g r st OLD0 A0 Nv n old A p RCEIL; lia)| exact MI1| exact WR| exact BK| (clear - LE RB4 PLO S16 HADDR off g r st A0 n A p RCEIL; lia)| (clear - FN E n A; lia)| (clear - LE RBC EHI S16 off g r st n p RCEIL; lia)| (clear - Nv n; lia)| unfold IB, UNIT in *; (clear - S20 LE RB4 EHI PLO EOFF CONC GADDR S16 HOFF off g r st A0 Nv n A p RCEIL; lia)| exact (hf_b3 _ _ _ _ _ _ _ _ _ _ _ _ HF)]. }
cbv beta. intros ms5 sfH_; first [ sf_destruct 7%nat sfH_ as z0 za1 za2 m' -> EM MI' | sf_fb; destruct sfH_ as (z0 & za1 & za2 & m' & -> & EM & MI') ].

pose proof (rip_munch st m1 p A old n r g bm ai ar b3 lo8 hi8 i off MR1 HF ltac:(lia) (FITn LE)) as [MU WM]. fold c mr stride in MU, WM. fold E in MU, WM. rewrite <- EM in MU, WM.
assert (FR' : rw_cells rsegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. cbn. repeat split; (clear - FN LE RBC EHI FO S16 off g r st OLD0 A0 CLOv Nv LOv lo n old A p sp RCEIL R32 K1 EOFF CONC GADDR; lia). }
eapply evt_cut; [eapply (rre_epilogue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' (bv_unsigned sp)); [lia| f_equal; lia| ]|].
{ replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia. exact FR'. }
cbv beta. intros ms6 ->.
assert (ST' : stk rsegs m' lo (bv_unsigned sp + -64)).
{ eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. cbn. repeat split; (clear - FN LE RBC EHI FO S16 off g r st OLD0 A0 CLOv Nv lo n old A p sp RCEIL; lia). }
release_frame FR' ST' (bv_unsigned sp).
destruct (rip_block st m1 p A old n r g bm ai ar b3 lo8 hi8 i off MR1 HF ltac:(lia) (FITn LE) oldbytes OLD1) as [junk' NEWB].
fold c mr stride in NEWB. fold E in NEWB. rewrite <- EM in NEWB.
pose proof (rip_heap s LB LB0 st m1 p A old n r g bm ai ar b3 lo8 hi8 i off PERM Hst MR1 BL1 AR RPL1 GA HIN HF EOFF ltac:(lia) (FITn LE) SC48) as HEAP'.
fold c mr stride in HEAP'. fold E in HEAP'. rewrite <- EM in HEAP'.
apply evt_done. unfold rrealloc_post. sf_eexists 15%nat. exists m', errv.
split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact MI'|]. split; [exact ST'|].
split. { rewrite ETP. unfold RERRNO. eapply rw_cells_transport; [exact ERR1| exact MU| exact WM|]. cbn. repeat split; lia. }
split. { eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn [fst snd]; (clear - FN LE IMG RBC EHI FO PLO S16 HADDR off g r st AIMG OLD0 A0 CLOv Nv LOv SB B lo n old A p sp RCEIL; lia)| constructor; [cbn [fst snd]; (clear - R32 FN K1 LE IMG RBC EHI FO PLO EOFF CONC GADDR S16 HADDR off g r st AIMG OLD0 A0 CLOv Nv LOv SB B lo n old A p sp RCEIL; lia)| constructor]]. }
split. { eapply rheap_pres_trans; [exact PRES01|]. eapply rheap_pres_of_munch; [exact MU| exact WM|]. intros a Ha CA.
exact (rip_out LB LB0 st m1 p A old n r g bm ai ar b3 lo8 hi8 i off PERM MR1 AR HIN HF ltac:(lia) (FITn LE) (bv_unsigned sp) a ltac:(lia) CA). }
split; [reflexivity|]. split; [reflexivity|].
exists A, junk'. split; [reflexivity|].
split. { split; [exact A0|]. split; [exact A16|]. split; [lia|]. unfold alloc_ceiling. (clear - FN K1 LE IMG RBC EHI PLO S16 HADDR off g r st AIMG OLD0 A0 n old A p RCEIL; lia). }
split; [exact HEAP'|]. split; [exact NEWB|]. split; [exact TOPK| intros _; reflexivity].
+
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia). rewrite Bool.andb_false_r.
eapply implM_evt; [| intros msx Hx; exact Hx].
step. step. step. if_cases K1; zify_cond K1. { exfalso. clear -K1 Nv. rewrite ?unsigned_lit in K1 by lia. lia. }
step. if_cases K2; zify_cond K2. { exfalso. clear -K2 LE AVAIL. rewrite ?unsigned_lit in K2 by lia. lia. }
eapply evt_cut; [eapply (rre_stc_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n); [reflexivity| exact N| reflexivity| exact MI1]|].
cbv beta. intros ms4 sfH_; first [ sf_destruct 5%nat sfH_ as z1 z4 z5 z7 -> | sf_fb; destruct sfH_ as (z1 & z4 & z5 & z7 & ->) ].
step. if_cases K4; zify_cond K4. { exfalso. clear -K4 MV SCR STC. unfold sc in *. rewrite ?signed_wz_small in K4 by lia. lia. }
apply evt_done. apply MOVE.
-
cbn [andb]. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia). rewrite Bool.andb_false_r.
eapply implM_evt; [| intros msx Hx; exact Hx].
step. step. step. if_cases K1; zify_cond K1. { exfalso. clear -K1 Nv. rewrite ?unsigned_lit in K1 by lia. lia. }
step. if_cases K2; zify_cond K2. 2:{ exfalso. clear -K2 GT AVAIL Nv FO EHI RBC A0 OLD0. rewrite ?unsigned_lit in K2 by lia. lia. }
step. step. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 Nv. rewrite ?unsigned_lit in K3 by lia. lia. }
apply evt_done. apply MOVE.
Qed.

#[using="HM HFR"] Theorem rrealloc_spec_proof : rrealloc_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A old n lo B errv oldbytes.
intros HEAP HIN TOPK BIGN OLD AUXB SB ST CLO LO ERR MI TP HA0 HA1 N.
eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom rsegs))).
{ unfold RREALLOC_SYM. step. apply evt_done. reflexivity. }
cbv beta. intros ms' ->.
exact (rlibc_realloc_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A old n lo B errv oldbytes
HEAP HIN TOPK BIGN OLD AUXB SB ST CLO LO ERR MI TP HA0 HA1 N).
Qed.
End TOPLEVEL2.
