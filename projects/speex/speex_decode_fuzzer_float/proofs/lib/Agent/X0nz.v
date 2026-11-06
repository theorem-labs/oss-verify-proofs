(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0pa X0p9 X0qn X0py X0qc X0qd X0pj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0qe X0ol X0pd X0qp X0p6 X0p5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ql X0q1 X0qf X0o1 X0o2 X0oj X0o3 X0o5 X0o6 X0o7 X0ob X0ns X0nt X0nv X0nw X0ny X0nx X0o0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Lemma conc_meta_stable' {RCEIL : RunCeiling} st stE m q : mrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
intros MR REL sfH_; first [ sf_destruct 6%nat sfH_ as ar arr kk Ha Hk -> | sf_fb; destruct sfH_ as (ar & arr & kk & Ha & Hk & ->) ]. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ WA _ | sf_fb; destruct sfP_ as (_ & _ & _ & WA & _) ].
destruct (WA ar arr Ha) as (r & Hr & _). first [ pose proof (mrel_regions _ _ REL _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' _ B' _ | sf_fb; destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _) ].
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma malloc_fp_widen {RCEIL : RunCeiling} st0 stA stB lo sp sp' a :
sp' <= sp ->
(forall rid r, (s_regions stA) !! rid = Some r ->
exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
malloc_fp st0 stA lo sp' a -> malloc_fp st0 stB lo sp a.
Proof.
intros LE HR H. apply (malloc_fp_mono st0 stA stB lo sp a HR).
destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma slot_ok_N st g b r idx n N :
slot_ok st g b r idx n -> get_stride (get_meta_rec st g) = N + 4 -> 0 <= N -> slot_ok st g b r idx N.
Proof.
intros SO STR N0. destruct SO. constructor; try assumption; try lia.
intros off O0 OF. apply so_q16; lia.
Qed.

Lemma outside_app' W1 W2 a : outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma arith_prog_dec a c s n : 0 < s ->
(exists j, 0 <= j <= n /\ a = c + s * j) \/ (forall j, 0 <= j <= n -> a <> c + s * j).
Proof.
intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
- pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
+ left. exists ((a - c) / s). split; [lia|]. lia.
+ right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
+ right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
- right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.

Lemma meta_slot_mono stA stB g :
(forall a, is_Some ((s_areas stA) !! a) -> is_Some ((s_areas stB) !! a)) -> meta_slot stA g -> meta_slot stB g.
Proof.
intros HA sfH_; first [ sf_destruct 6%nat sfH_ as ar arr kk Ha Hk E | sf_fb; destruct sfH_ as (ar & arr & kk & Ha & Hk & E) ]. destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
first [ unshelve sf_eexists 3%nat; [ exact (ar) | exact (arr') | exact (kk) | ] | sf_fb; exists ar, arr', kk ]. auto.
Qed.

Definition nreq (sc cnt1 : Z) : Z := UNIT + cnt1 * (UNIT * size_class sc) - IB.
Definition ncls (sc cnt1 : Z) : Z := size_to_class (nreq sc cnt1).

Lemma nest_class sc (SC : 0 <= sc < 48) cnt1 : 1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
nreq sc cnt1 = size_class sc * 16 * cnt1 + 12 /\ 0 <= ncls sc cnt1 <= 26 /\ 16 * size_class sc * cnt1 + 16 <= UNIT * size_class (ncls sc cnt1)
/\ sc < ncls sc cnt1 /\ 0 <= nreq sc cnt1 < 2^32 /\ nreq sc cnt1 + 4 <= 16 * size_class (ncls sc cnt1).
Proof.
intros C1 SM. pose proof (size_class_range sc SC) as SZR.
assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
split.
{ destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
split; [lia|]. nia.
Qed.

Section LEVEL.
Context {RCEIL : RunCeiling}.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
implT o (k st1 idx) s' Q ms'.
Hypothesis IHf : alloc_slot_stmt2 f.

Definition nest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
(m4 m'' : mem) (s' s'' : PState) (errv'' : word) (oo o3 : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
mem_inv asegs m'' /\ stk asegs m'' lo (bv_unsigned sp - 96) /\
rw_cells asegs m'' (errno_addr tp) [C4 errv''] /\ auxv_ok m'' (bv_unsigned sp - 96) /\ rw_cells asegs m'' MEDTAB medtab_cells /\
mrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
pres_except (malloc_fp st0 st3 lo (bv_unsigned sp - 96)) m4 m'' /\
mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
rw_cells asegs m'' (bv_unsigned sp - 96) (nest_frame (ncls sc cnt1) (conc st2 mm) cnt1 (size_class sc * 16) sc s4 s3 s2 s1 s0 ra) /\
pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ mrep st2 m4.

Definition NFAIL_stmt : Prop :=
forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' oo o3 (t0' t2' a1' a3' t5' t6' : word),
nest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' oo o3 ->
implT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
(MS (mkR (Z_to_bv 64 0x16a18) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0' (wz (size_class sc * 16)) t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
(Z_to_bv 64 (-1)) a1' (wz (ncls sc cnt1)) a3' (Z_to_bv 64 SIZE_CLASSES) (Z_to_bv 64 (-1)) (wz cnt1) (Z_to_bv 64 (conc st2 mm))
(Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc + 58)) (wz cnt1) t5' t6')
F (Z_to_bv 64 0x16b98) fc None m'' (seg_rom asegs)).

Definition NSUCC_stmt : Prop :=
forall st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' oo o3 g3 b3 r3 (t0' t2' a1' a3' t5' t6' : word),
nest_ctx st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' oo o3 ->
0 <= idx -> active st3 (ncls sc cnt1) = Some g3 -> slot_ok st3 g3 b3 r3 idx (nreq sc cnt1) ->
(forall a, r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx - 4 <= a
< r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx + get_stride (get_meta_rec st3 g3) - 4 ->
malloc_fp st0 st3 lo (bv_unsigned sp - 96) a) ->
(s_regions st0 = ∅ -> rdv pans_mem o st3 (fst b3, snd b3 + (16 + get_stride (get_meta_rec st3 g3) * idx) + -3) = 0) ->
implT o (ag_tail full_lay (upd_meta mm (m_set_maplen 0) (nest_layout st3 g3 idx (ncls sc cnt1) (UNIT * size_class sc) cnt1))
sc mm (slot_of st3 g3 idx) cnt1 (cnt1 - 1) (as_kq sc k bail)) s'' Q
(MS (mkR (Z_to_bv 64 0x16a18) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0' (wz (size_class sc * 16)) t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
(Z_to_bv 64 idx) a1' (wz (ncls sc cnt1)) a3' (Z_to_bv 64 SIZE_CLASSES) (Z_to_bv 64 (-1)) (wz cnt1) (Z_to_bv 64 (conc st2 mm))
(Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc + 58)) (wz cnt1) t5' t6')
F (Z_to_bv 64 0x16a40) fc None m'' (seg_rom asegs)).

End LEVEL.
