(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0p9 X0qn X0py X0qd X0qp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0p8 X0ol X0pd X0pe X0pa X0p7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0q8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma membed_strel_follow {RCEIL : RunCeiling} {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : X1qu.M R1) (t2 : X1qu.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
implM asegs (membed alloc_ceiling t1) s Q1 ms ->
implM asegs (membed alloc_ceiling t2) s
(fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
- cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
exists r1, []. cbn. auto.
- cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
impl asegs (at_node asegs) (X1bs.bind _ (Ret Unr) f) Qx msx = impl asegs (at_node asegs) (f Unr) Qx msx) by reflexivity.
destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
5:{ cbn [ev_step] in *. unfold munr in *. cbn [X1bs.bind] in *. exact H. }
5:{ cbn [ev_step] in *. unfold munr in *. cbn [X1bs.bind] in *. exact H. }
all: eapply impl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
eapply impl_epost_mono; [eapply IH; exact H1|];
intros [r2' s2] ms2; cbn; intros sfH_; first [ sf_destruct 6%nat sfH_ as r1' ans F1 F2 HR HQ | sf_fb; destruct sfH_ as (r1' & ans & F1 & F2 & HR & HQ) ];
exists r1', (z :: ans); cbn; auto.
Qed.

Lemma follow_steq {R} (t1 t2 : X1qu.M R) : steq t1 t2 -> forall ans, follow t1 ans = follow t2 ans.
Proof.
induction 1 as [r | e k1 k2 Hk IH]; intros ans; [reflexivity|].
cbn. destruct e; try reflexivity; destruct ans; try reflexivity; apply IH.
Qed.

Lemma follow_sbind {R S} (t : X1qu.M R) (f : R -> X1qu.M S) :
forall ans x y, follow t ans = Some x ->
(forall ans', follow (f x) ans' = Some y) ->
follow (sbind t f) ans = Some y.
Proof.
induction t as [r | e k IH]; intros ans x y H Hf.
- cbn in H. inversion H; subst. rewrite sbind_ret_l. apply Hf.
- rewrite sbind_vis. cbn in H |- *. destruct e; try discriminate; destruct ans as [|a ans]; try discriminate; eapply IH; eauto.
Qed.

Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : X1qu.M R1) (t2 : X1qu.M R2) :
strel RR t1 t2 -> forall ans r1 r2, follow t1 ans = Some r1 -> follow t2 ans = Some r2 -> RR r1 r2.
Proof.
induction 1 as [a b Hab | e k1 k2 Hk IH]; intros ans r1 r2 F1 F2.
- cbn in F1, F2. inversion F1; inversion F2; subst. exact Hab.
- cbn in F1, F2. destruct e; try discriminate; destruct ans as [|z ans]; try discriminate; eapply IH; eauto.
Qed.

Lemma implT_silent {RCEIL : RunCeiling} {R} o (t : X1qu.M R) o' (x : R) s Q ms :
mrun o t = SRet (o', x) -> implT o t s Q ms -> evt asegs (Q x s) ms.
Proof. intros E H. unfold implT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

Lemma mrun_enframe_full o st g b idx n ctr :
m_mem (get_meta_rec st g) = Some b ->
let stride := get_stride (get_meta_rec st g) in
let off := fold_off (if rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) =? 0 then Z.land ctr 255
else Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2)
+ 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
((stride - IB - n) / UNIT) in
mrun o (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p)))
= SRet (o, (havoc (snd (enframe_at st g idx n off)) n (fst (enframe_at st g idx n off)), Some (snd (enframe_at st g idx n off)))).
Proof.
intros Hmem stride off. unfold mrun, enframe_full, enframe_read_off.
assert (Hp0 : slot_start' (get_meta_rec st g) idx = (fst b, snd b + (16 + stride * idx))).
{ unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. reflexivity. }
rewrite Hp0. unfold aadd. cbn [fst snd]. fold stride.
rewrite (rd8_oracle pans_mem pans_mem_range).
assert (OFFa : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = 0 -> fold_off (Z.land ctr 255) ((stride - IB - n) / UNIT) = off).
{ intros E0. subst off. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
assert (OFFb : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) <> 0 ->
fold_off (Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
((stride - IB - n) / UNIT) = off).
{ intros E0. subst off. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
clearbody off.
destruct (Z.eqb_spec (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3)) 0) as [E|NE]; cbn [negb].
- rewrite (OFFa E). rewrite surj_pair_let. reflexivity.
- rewrite (rd16_oracle pans_mem pans_mem_range). unfold aadd. cbn [fst snd].
rewrite (OFFb NE). rewrite surj_pair_let. reflexivity.
Qed.

Lemma block_inside {RCEIL : RunCeiling} st LB m blk :
MFACTS st LB -> mrep st m -> In blk LB ->
exists r g idx, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
/\ (s_slots st) !! (blk_slot blk) = Some (g, idx)
/\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
/\ 0 <= blk_size blk
/\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x19000 \/ 0x1b000 <= r_base r).
Proof.
intros MF MR IN.
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
first [ sf_destruct 7%nat BS as g idx SL _ _ IDX (off & OFF0 & EA & FIT) | sf_fb; destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)) ].
destruct BR as (r & Hr & Hk).
pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as sfP_; first [ sf_destruct 5%nat sfP_ as b Hm Efst Esnd _ | sf_fb; destruct sfP_ as (b & Hm & Efst & Esnd & _) ].
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
first [ sf_destruct 11%nat FG as _ _ _ LI _ _ _ _ (r' & Hr' & _ & B0 & _ & SPAN) S16 _ | sf_fb; destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _) ].
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof (region_addr_facts st m _ r MR Hr) as sfP_; first [ sf_destruct 5%nat sfP_ as R4 _ RC _ RI1 | sf_fb; destruct sfP_ as (R4 & _ & RC & _ & RI1) ].
first [ unshelve sf_eexists 3%nat; [ exact (r) | exact (g) | exact (idx) | ] | sf_fb; exists r, g, idx ]. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Esnd in EA. unfold alloc_ceiling in *. lia.
Qed.

Lemma heap_pres_of_fp {RCEIL : RunCeiling} st st' LB lo sp m m' :
MFACTS st LB -> mrep st m -> mrep st' m' -> mrel st st' ->
pres_except (malloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
heap_pres LB sp m m'.
Proof.
intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
- destruct (malloc_fp_cases st st' lo sp m m' a MR MR' Hfp); unfold alloc_ceiling in *; lia.
- destruct (malloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold alloc_static, ERRNO, ATP, LIBC, CTX in *; lia.
- first [ pose proof (block_inside st LB m blk MF MR Hin) as sfP_; sf_destruct 12%nat sfP_ as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | sf_fb; destruct (block_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ].
unfold alloc_ceiling in *.
pose proof MR' as (WF' & _). pose proof WF' as sfP_; first [ sf_destruct 4%nat sfP_ as _ WR' DISJ' _ | sf_fb; destruct sfP_ as (_ & WR' & DISJ' & _) ].
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 4%nat sfP_ as _ WR DISJ _ | sf_fb; destruct sfP_ as (_ & WR & DISJ & _) ].
destruct REL as [RREG _ _]. first [ pose proof (RREG _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as r1 Hr1 K1 B1 L1 | sf_fb; destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1) ].
pose proof (round_up_pg_mono _ _ L1) as RL1.
pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
+ lia.
+ rewrite unsigned_lit in H by lia. lia.
+ unfold CTX in H. lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

Lemma strip_eq_proj a b : strip a = strip b ->
s_ctx a = s_ctx b /\ s_regions a = s_regions b /\ s_next_rid a = s_next_rid b /\ s_metas a = s_metas b
/\ s_areas a = s_areas b /\ s_groups a = s_groups b /\ s_slots a = s_slots b /\ s_reserved a = s_reserved b.
Proof.
intros E.
pose proof (f_equal s_ctx E) as E1. pose proof (f_equal s_regions E) as E2. pose proof (f_equal s_next_rid E) as E3.
pose proof (f_equal s_metas E) as E4. pose proof (f_equal s_areas E) as E5. pose proof (f_equal s_groups E) as E6.
pose proof (f_equal s_slots E) as E7. pose proof (f_equal s_reserved E) as E8.
cbn in E1, E2, E3, E4, E5, E6, E7, E8. repeat split; assumption.
Qed.

Lemma mrun_fst {R} (t : X1qu.M R) : forall o ans o1 x, follow (mrun o t) ans = Some (o1, x) -> o1 = o.
Proof.
unfold mrun, prun. induction t as [r | e k IH]; intros o ans o1 x H.
- cbn in H. inversion H. reflexivity.
- cbn [eruns] in H. destruct (psel pans_mem o e) as [a|] eqn:P.
+ unfold pupd_mem in H. eapply IH. exact H.
+ cbn in H. destruct e; try discriminate; destruct ans; try discriminate; unfold pupd_mem in H; eapply IH; exact H.
Qed.

Lemma mod16_slot (B s st k off : Z) : B mod 4096 = 0 -> s mod 16 = 0 -> st mod 16 = 0 -> 0 <= k ->
(B + s + 16 + st * k + 16 * off) mod 16 = 0.
Proof.
intros HB HS HT HK.
destruct (Z.mod_divide st 16 ltac:(lia)) as [D _]. destruct (D HT) as [q Hq].
assert (E : st * k = 16 * (q * k)) by (rewrite Hq; ring).
set (w := q * k) in E. clearbody w. rewrite E. Z.div_mod_to_equations. lia.
Qed.

Section TOPLEVEL.
Context {RCEIL : RunCeiling}.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis BIG : big_stmt.

Definition midQ (o : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
exists st2 r ans o1,
fst res = strip st2
/\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
/\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ coreQ o o st s ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo (st2, r) s' ms'.

End TOPLEVEL.
