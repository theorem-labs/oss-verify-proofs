(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0pa X0p9 X0qn X0py X0qc X0qd X0qg X0qe X0qf X0qh X0qj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0ql X0q1 X0o1 X0o2 X0oj X0ns X0nt X0nz.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1ky X1lz X1m0 X1m1 X1lw X1lx X1m4 X1k8 X1jk X1k4 X1k6 X1jl X1jn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0qa.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rconc_meta_stable' {RCEIL : RunCeiling} st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
intros MR REL sfH_; first [ sf_destruct 6%nat sfH_ as ar arr kk Ha Hk -> | sf_fb; destruct sfH_ as (ar & arr & kk & Ha & Hk & ->) ]. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ WA _ | sf_fb; destruct sfP_ as (_ & _ & _ & WA & _) ].
destruct (WA ar arr Ha) as (r & Hr & _). first [ pose proof (mrel_regions _ _ REL _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' _ B' _ | sf_fb; destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _) ].
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma rmalloc_fp_widen {RCEIL : RunCeiling} st0 stA stB lo sp sp' a :
sp' <= sp ->
(forall rid r, (s_regions stA) !! rid = Some r ->
exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rmalloc_fp st0 stA lo sp' a -> rmalloc_fp st0 stB lo sp a.
Proof.
intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rregion_byte_raw {RCEIL : RunCeiling} st m rid r off v :
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) off = Known v -> m (wa (r_base r + off)) = Some (b8 v).
Proof.
intros MR Hr Hk Ho Hc.
destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
first [ pose proof (rregion_facts st m rid r MR Hr) as sfP_; sf_destruct 5%nat sfP_ as R4 RAL RC RI1 RI2 | sf_fb; destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2) ]. unfold alloc_ceiling in RC.
specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
cbn [ov_read_bytes] in RD.
destruct (m (wa (r_base r + off))) as [b|] eqn:E.
- cbn in RD. inversion RD. reflexivity.
- rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x4d3ac.
Proof. intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

Section LEVEL.
Context {RCEIL : RunCeiling}.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := X0qa.ist_facts_proof st0 LB st AR IS.

Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
mkR (Z_to_bv 64 0x32ae0) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6'.

Definition rnest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
(m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
mem_inv rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp - 144) /\
rw_cells rsegs m'' (errno_addr tp) [C4 errv''] /\ rauxv_ok m'' (bv_unsigned sp - 144) /\
rmrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
rpres_except (rmalloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
rw_cells rsegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ rmrep st2 m4.

Definition rNFAIL_stmt : Prop :=
forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
rnest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 ->
rimplT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
(MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
F (Z_to_bv 64 0x32b58) fc None m'' (seg_rom rsegs)).

Definition rNSUCC_stmt : Prop :=
forall st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
rnest_ctx st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 ->
0 <= idx -> active st3 (ncls sc cnt1) = Some g3 -> slot_ok st3 g3 b3 r3 idx (nreq sc cnt1) ->
(forall a, r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx - 4 <= a
< r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx + get_stride (get_meta_rec st3 g3) - 4 ->
rmalloc_fp st0 st3 lo (bv_unsigned sp - 144) a) ->
(s_regions st0 = ∅ -> rdv pans_mem o st3 (fst b3, snd b3 + (16 + get_stride (get_meta_rec st3 g3) * idx) + -3) = 0) ->
rimplT o (ag_tail full_lay (upd_meta mm (m_set_maplen 0) (nest_layout st3 g3 idx (ncls sc cnt1) (UNIT * size_class sc) cnt1))
sc mm (slot_of st3 g3 idx) cnt1 (cnt1 - 1) (as_kq sc k bail)) s'' Q
(MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 idx) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
F (Z_to_bv 64 0x32ae4) fc None m'' (seg_rom rsegs)).
End LEVEL.
