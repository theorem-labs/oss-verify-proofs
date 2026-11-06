(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0pa X0p9 X0qn X0py X0qc X0qd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0qe X0ol X0pd X0qp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ql X0q1 X0qf X0o1 X0o2 X0oc X0oi X0oj X0o3 X0o5 X0ns X0nt X0nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0qa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Definition epi_frame (jj : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
[CB 48 jj; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Lemma ag_frame_epi m A sc j s4v s3v s2v s1v s0v rav :
rw_cells asegs m A (ag_frame sc j s4v s3v s2v s1v s0v rav) ->
rw_cells asegs m A (epi_frame (cells_bytes [C8 (Z_to_bv 64 (sc * 2)); CB 40 j]) s4v s3v s2v s1v s0v rav).
Proof.
intros FR. unfold ag_frame in FR. unfold epi_frame.
pose proof (rw_cells_merge asegs m A [] [C8 (Z_to_bv 64 (sc * 2)); CB 40 j] [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] FR) as X.
cbn [app cells_size csize Nat.add] in X. exact X.
Qed.

Section EPI2.
Context {RCEIL : RunCeiling}.
Variables (lo : Z).
Hypothesis CLO : alloc_ceiling <= lo.

End EPI2.

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
Let F0 : ISTF st LB := X0qa.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_AS am_pre.

Definition HAG_stmt : Prop :=
forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word) j oo,
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
mrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -96) ->
rw_cells asegs m3 (bv_unsigned sp + -96) (ag_frame sc j s4 s3 s2 s1 s0 ra) ->
rw_cells asegs m3 (errno_addr tp) [C4 errv'] -> auxv_ok m3 (bv_unsigned sp) -> rw_cells asegs m3 MEDTAB medtab_cells ->
pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
implT o (ag_body f sc req k bail st2 mm) s' Q
(MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
(Z_to_bv 64 (conc st2 mm)) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1
s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 0x16404) fc None m3 (seg_rom asegs)).
Hypothesis HAG : HAG_stmt.

#[using="RCEIL sc req SC RQ TP"] Lemma errno_lit2 : errno_addr tp = 107900.
Proof. rewrite TP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="RCEIL m sc req SC RQ MR"] Lemma conc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
intros REL sfH_; first [ sf_destruct 6%nat sfH_ as ar arr kk Ha Hk -> | sf_fb; destruct sfH_ as (ar & arr & kk & Ha & Hk & ->) ]. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ WA _ | sf_fb; destruct sfP_ as (_ & _ & _ & WA & _) ].
destruct (WA ar arr Ha) as (r & Hr & _). first [ pose proof (mrel_regions _ _ REL _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' _ B' _ | sf_fb; destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _) ].
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

#[using="m sc req ER SC RQ MR"] Lemma ta_fp_malloc_fp stE mE a :
mrep stE mE -> mrel st stE -> (forall q, meta_slot st q -> meta_slot stE q) ->
ta_fp st lo (bv_unsigned sp) a -> malloc_fp st0 stE lo (bv_unsigned sp) a.
Proof.
intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- left. left. exact X.
- left. right. right. left. exact X.
- left. do 3 right.
pose proof (AREAS q MSq) as MSq'.
first [ pose proof (meta_chunk_facts stE mE q MRE MSq') as sfP_; sf_destruct 7%nat sfP_ as _ _ _ _ _ _ (rid0 & r0 & H0 & K0 & L0 & H0') | sf_fb; destruct (meta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')) ].
exists rid0, r0. split; [exact H0|]. split; [exact K0|].
rewrite (conc_meta_stable stE q REL MSq) in L0, H0'. lia.
- do 3 right. left. pose proof MR as (WF & _).
first [ pose proof (group_conc st bq gh WF Hbq) as sfP_; sf_destruct 8%nat sfP_ as rb Hrb Cb Kb B0 B16' M16 _ | sf_fb; destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _) ].
destruct ER as [_ EG EGR _ _ _ _ _].
destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
first [ unshelve sf_eexists 3%nat; [ exact (bq) | exact (gh0) | exact (rb) | ] | sf_fb; exists bq, gh0, rb ]. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
rewrite Cb in Xq. lia.
Qed.

#[using="RCEIL m sc req SC RQ MR CLO"] Lemma ta_fp_not_image a : 0x19000 <= a < 0x1b000 -> ~ (CTX <= a < CTX + 928) -> ~ ta_fp st lo (bv_unsigned sp) a.
Proof.
intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- unfold alloc_ceiling in CLO. lia.
- exact (Hc X).
- first [ pose proof (meta_slot_bounds st m q MR MSq) as sfP_; sf_destruct 4%nat sfP_ as _ _ GI _ | sf_fb; destruct (meta_slot_bounds st m q MR MSq) as (_ & _ & GI & _) ]. lia.
- pose proof MR as (WF & _). first [ pose proof (group_conc st bq gh WF Hbq) as sfP_; sf_destruct 7%nat sfP_ as rb Hrb Cb Kb B0 BE _ | sf_fb; destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _) ].
first [ pose proof (region_addr_facts st m (fst bq) rb MR Hrb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RI2 | sf_fb; destruct (region_addr_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & _ & RI2) ]. lia.
Qed.

#[using="RCEIL f m sc req SC RQ MR CLO LO"] Lemma ta_fp_not_high a : bv_unsigned sp <= a -> ~ ta_fp st lo (bv_unsigned sp) a.
Proof.
pose proof (AS_STACK_ge (S f)) as ASG. unfold alloc_ceiling in CLO.
intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- unfold CTX in X. lia.
- destruct (meta_slot_bounds st m q MR MSq) as (_ & GC & _). lia.
- pose proof MR as (WF & _). first [ pose proof (group_conc st bq gh WF Hbq) as sfP_; sf_destruct 9%nat sfP_ as rb Hrb Cb Kb B0 BE M16 RB0 RC | sf_fb; destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC) ]. unfold alloc_ceiling in RC. lia.
Qed.

#[using="UA"] Lemma unk_agree_keep stE mE :
s_shadow stE = s_shadow st ->
(forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
(forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
(forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
unk_agree stE o mE.
Proof.
intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
pose proof (ERG rid r Hk Hr) as Hr0.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros sfH_; first [ sf_destruct 5%nat sfH_ as bq gh Hbq Hf Hoff | sf_fb; destruct sfH_ as (bq & gh & Hbq & Hf & Hoff) ]. apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

#[using="RCEIL m sc req SC RQ MR CLO"] Lemma ta_fp_not_inband rid r off :
(s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
~ ta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof.
intros Hr Hk Ho NG. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 4%nat sfP_ as _ WR DJ _ | sf_fb; destruct sfP_ as (_ & WR & DJ & _) ].
first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as R0 _ _ RC _ | sf_fb; destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _) ]. unfold alloc_ceiling in RC, CLO.
intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- first [ pose proof (region_addr_facts st m rid r MR Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RI2 | sf_fb; destruct (region_addr_facts st m rid r MR Hr) as (_ & _ & _ & _ & RI2) ]. unfold CTX in X. lia.
- first [ pose proof (meta_chunk_facts st m q MR MSq) as sfP_; sf_destruct 7%nat sfP_ as _ _ _ _ _ GRG _ | sf_fb; destruct (meta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _) ]. destruct (GRG rid r Hr Hk); lia.
- first [ pose proof (group_conc st bq gh WF Hbq) as sfP_; sf_destruct 8%nat sfP_ as rb Hrb Cb Kb B0 B16' M16 _ | sf_fb; destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _) ].
destruct (N.eq_dec (fst bq) rid) as [E|NE].
+ apply NG. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
+ pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

End LEVEL.
