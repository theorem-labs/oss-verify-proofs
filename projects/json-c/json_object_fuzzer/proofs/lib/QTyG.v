(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QnDM_c1 Q2qa Qy5Y QDUx Q4J3 QytA QJE4 QZAi QUZl Q7S0 Ql2m QGeV QLsg QWTl Q3o5 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA QJE4.Mq4.
Import Qy5Y.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QWTl.Mq5 Q3o5.
Import QDUx.Mqb.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition as_fm_link (st0 : mstate) (g head : aptr) : mstate :=
let hprev := m_prev (get_meta_rec st0 head) in
let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
upd_meta head (m_set_prev (Some g)) st2.

Definition as_fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition as_queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
match get_head st0 h with
| Some head => as_fm_link st0 g head
| None => as_fm_single st0 h g
end.

#[using="Type"] Lemma as_queue_eq : forall R h g st0 (k : mstate -> QUZl.M R) (bail : QUZl.M R),
m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
queue h g st0 k bail = k (as_queue_st h g st0).
Proof.
intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
unfold as_queue_st, as_fm_link, as_fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).

#[using="Type"] Lemma as_free_meta_eq : forall R st g (k : mstate -> QUZl.M R) (bail : QUZl.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
intros. unfold free_meta, as_fm_st. apply as_queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

#[using="Type"] Lemma outside_In W x lo hi : outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
induction W as [|[a b] W IH]; cbn; intros HO HI; [destruct HI|].
destruct HI as [E|HI]; [inversion E; subst; tauto|]. apply IH; tauto.
Qed.

#[using="Type"] Lemma sub_fp_single W lo hi : In (lo, hi) W -> sub_fp [(lo, hi)] W.
Proof. intros HI x HO. cbn. split; [exact (outside_In W x lo hi HO HI)| exact I]. Qed.

Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.

Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition failW : list (Z * Z) :=
(G, G + 40) :: (CTX + 16, CTX + 24)
:: match c_free_meta_head (ctx st) with
| Some h => (conc st h, conc st h + 40)
:: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
| None => []
end.

End FAILM.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq Q8P7 QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QnDM_c1.Mq0 QytA Qnxq Q4J3.Mq3 Q8P7 QkQT Q3o5. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya QPiB Qatc QSfG QdBa QpFQ QaiD QLaA QQg5 QoCS QQCz QhnL Q4en QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QdBa.Mq1 QpFQ QaiD QLaA QLaA.Mq0 QQg5.Mq2 QoCS.Mq0 QQCz QhnL Q4en QBv7.
Import QnDM_c1.Mq0 QytA Qy5Y.Mq4 Qnxq Q3o5.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma NoDup_map_on {A B} (f : A -> B) (l : list A) :
(forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
induction l as [|a l IH]; intros Hinj ND; cbn; [constructor|].
inversion ND; subst. constructor.
- intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Ey & Hy).
rewrite (Hinj a y ltac:(now left) ltac:(now right) (eq_sym Ey)) in H1. exact (H1 Hy).
- apply IH; [| assumption]. intros x y Hx Hy. apply Hinj; now right.
Qed.

#[using="Type"] Lemma NoDup_Z_length (l : list Z) (N : Z) : 0 <= N -> List.NoDup l -> (forall x, In x l -> 0 <= x < N) -> Z.of_nat (length l) <= N.
Proof.
intros Hn ND HB.
assert (INCL : incl l (map Z.of_nat (seq 0 (Z.to_nat N)))).
{ intros x Hx. apply in_map_iff. exists (Z.to_nat x). pose proof (HB x Hx). split; [lia|]. apply in_seq. lia. }
pose proof (NoDup_incl_length ND INCL) as Hlen. rewrite length_map, length_seq in Hlen. lia.
Qed.

#[using="Type"] Lemma zsum_bound (l : list Z) (K : Z) : (forall x, In x l -> 0 <= x <= K) -> 0 <= zsum l <= K * Z.of_nat (length l).
Proof.
induction l as [|a l IH]; intros HB; cbn -[Z.of_nat]; [lia|].
pose proof (HB a ltac:(now left)). specialize (IH ltac:(intros x Hx; apply HB; now right)).
unfold zsum in IH. rewrite Nat2Z.inj_succ. lia.
Qed.

Section MF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="RC__ X L BL LS INV ZB IM"] Lemma mem_hosts g b : m_mem (MR st g) = Some b -> hosts st b g.
Proof. intros H. destruct (im_group _ _ _ IM g b H) as [Hh|Hz]; [exact Hh|]. rewrite ZB in Hz. destruct Hz. Qed.

#[using="RC__ L BL INV IG"] Lemma hosts_GO b g : hosts st b g -> exists ai, s_groups st !! b = Some (mkGhdr (Some g) ai) /\ group_ok X st LS g b ai.
Proof. intros H. exact (hosts_ok _ _ _ IG _ _ H). Qed.

#[using="Type"] Lemma sstart_of_eq r i : sstart_of r i = sstart r i.
Proof. reflexivity. Qed.

#[using="RC__ X L BL LS INV IM IG IS"] Lemma group_in_region b m : hosts st b m ->
exists r, s_regions st !! fst b = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ gend (MR st m) <= round_up_pg (r_len r).
Proof.
intros Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 _].
destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Z0|NZ].
- destruct (top_chain _ _ _ _ IM IG IS m b Hm Z0) as (t & i & c & bt & Ha & Ht & Htl & Hf).
destruct (anc_box _ _ _ _ IM IG IS m t i c b Ha Hm) as (B1 & B2 & B3).
destruct (anc_facts _ _ _ _ IM IG IS m t i c Ha) as (bm & bp & Hm' & Hp' & _ & Hi & _).
pose proof (hosts_inj _ _ _ IM _ _ _ Ht Hp'); subst bp.
destruct (hosts_GO _ _ Ht) as (ait & Hbt & GOt).
destruct (g_top _ _ _ _ _ _ GOt Htl) as (S0 & r & Hr & Kr & ML & GE).
rewrite <- Hf. exists r. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|].
pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st t) + 1) Ht ltac:(lia)) as SM. rewrite <- gend_eq in SM. lia.
- destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE). exists r. repeat split; auto. lia.
Qed.

#[using="RC__ X L BL LS INV IM IG IS"] Lemma conc_group b m : hosts st b m -> exists r, s_regions st !! fst b = Some r /\ r_kind r = RKGroup /\
conc st b = r_base r + snd b /\ r_base r <= conc st b /\ conc st b + 32 <= r_base r + round_up_pg (r_len r).
Proof.
intros Hm. destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE). pose proof (gend_ge _ _ _ IM IG _ _ Hm) as G32.
exists r. unfold conc, get_region. rewrite Hr. repeat split; auto; lia.
Qed.

#[using="RC__ X L BL LS INV IA"] Lemma f_ctx : fact_ctx (strip st).
Proof.
pose proof (ia_ctx _ IA) as (C1 & C2 & C3 & C4). pose proof (ia_secret _ IA) as [S1 S2].
unfold fact_ctx. rewrite ctx_strip. unfold ctx.
split; [exact C1|]. split; [destruct S2 as [(_ & E & _)|[_ E]]; rewrite E; lia|].
split; [destruct S2 as [(E & _)|[E _]]; rewrite E; auto|]. split; [exact C2|].
split.
- intros i. unfold bounces, ctx. cbn. destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 i v E)).
- intros i. unfold unmap_seq, ctx. cbn. destruct (c_unmap_seq (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C4 i v E)).
Qed.

#[using="RC__ X L BL LS INV IM IL"] Lemma f_active : fact_active (strip st).
Proof.
intros sc g H. rewrite active_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
destruct (il_active _ _ IL sc g Hin) as (Hsc & [b Hb] & Esc). split; [exact Hsc|]. split; [exact Esc|].
rewrite (hosts_mem _ _ _ IM _ _ Hb). discriminate.
Qed.

#[using="RC__ X L BL LS INV ZB IM IG"] Lemma f_masks : fact_masks (strip st).
Proof.
intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
destruct (hosts_GO _ _ (mem_hosts _ _ H)) as (ai & Hb & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
split; [intros i Hi Ha; pose proof (M3 i Hi Ha); lia|]. split; [exact M4|].
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.testbit (m_avail (MR st g)) i) eqn:Ea; destruct (Z.testbit (m_freed (MR st g)) i) eqn:Ef; try reflexivity.
exfalso. exact (M5 i Hi Ea Ef).
Qed.

#[using="RC__ X L BL LS INV ZB IR IM IG"] Lemma f_maplen : fact_maplen (strip st).
Proof.
intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r & Hr & Kr & ML & GE).
destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CEIL & _). unfold alloc_ceiling in CEIL. lia.
Qed.

#[using="RC__ X L BL LS INV IM IS"] Lemma f_slots : fact_slots (strip st).
Proof.
intros p g idx H. rewrite s_slots_strip in H. rewrite !get_meta_rec_strip. fold (MR st g).
destruct (is_valid _ _ _ IS _ _ _ H) as ([b Hb] & Hi & Ep). exists b. split; [exact (hosts_mem _ _ _ IM _ _ Hb)|].
rewrite (slot_start'_eq _ _ _ IM _ _ idx Hb) in Ep. rewrite Ep. cbn. rewrite sstart_of_eq. auto.
Qed.

#[using="RC__ X L BL LS INV ZB IM IS"] Lemma f_slots_complete : fact_slots_complete (strip st).
Proof.
intros g b i H Hi. rewrite s_slots_strip. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
pose proof (mem_hosts _ _ H) as Hm. rewrite sstart_of_eq, <- (slot_start'_eq _ _ _ IM _ _ i Hm). exact (is_total _ _ _ IS _ _ _ Hm Hi).
Qed.

#[using="RC__ X L BL LS INV ZB IM ISH"] Lemma f_hdr0 : fact_hdr0 st.
Proof.
intros g b i H Hi. fold (MR st g) in *. rewrite sstart_of_eq. exact (ish_hdr0 _ _ ISH b g i (mem_hosts _ _ H) ltac:(unfold cnt_of; lia)).
Qed.

#[using="RC__ X L BL LS INV ISH"] Lemma f_cell_ticks : fact_cell_ticks st.
Proof. intros rid sh o v t Hs Hc. exact (proj2 (proj1 (ish_ticks _ _ ISH rid sh Hs) o v t Hc)). Qed.

#[using="RC__ X L BL LS INV ISH"] Lemma f_ticks : ticks_ok st.
Proof.
split.
- intros rid sh u hl ch Hs Hu Hin. exact (proj1 (proj2 (ish_ticks _ _ ISH rid sh Hs)) u hl ch Hu Hin).
- intros rid sh pg t Hs Hp. exact (proj2 (proj2 (ish_ticks _ _ ISH rid sh Hs)) pg t Hp).
Qed.

#[using="RC__ X L BL LS INV ZB NFR IA IM IG IS"] Lemma f_gmeta : fact_gmeta (strip st).
Proof.
intros g b H. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. cbn zeta.
pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
pose proof (g_li _ _ _ _ _ _ GO) as LI.
assert (AV : m_avail (MR st g) < 2 ^ 32).
{ apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
assert (FR : m_freed (MR st g) < 2 ^ 32).
{ apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
split.
{  pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! g) as [mr|] eqn:Em; [| congruence].
destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk). exists a, ar, ka. rewrite s_areas_strip. split; [exact Ha|]. split; [exact Hka|]. exact Emk. }
split; [lia|]. split; [lia|]. split; [exact LI|]. split; [exact (g_freeable _ _ _ _ _ _ GO)|].
pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
split. { destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & _)]; [left; lia| right; lia]. }
split; [exact ML|].
split. { exists ai. rewrite s_groups_strip. split; [exact Hb|]. split; [exact AI|]. exact M3. }
split. { destruct (group_in_region _ _ Hm) as (r & Hr & Kr & A0 & GE). exists r. rewrite s_regions_strip.
pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|]. split; [exact A16|]. rewrite sstart_of_eq. rewrite gend_eq in GE. exact GE. }
pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SM].
split; [exact SG|]. split; [exact SM|].
pose proof (g_stride _ _ _ _ _ _ GO) as GS.
split. { intros Hsc. destruct (GS Hsc) as (_ & _ & LT). unfold cnt_of in LT. nia. }
split. { intros Hsc i Hi Ht. destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| lia].
exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 _]. rewrite A0 in Ht. rewrite Z.bits_0 in Ht. discriminate. }
intros Hsc. destruct (GS Hsc) as (_ & _ & LT). unfold cnt_of in LT. lia.
Qed.

#[using="RC__ X L LS INV IM IS"] Lemma bit_slot_nonH g b ai i : s_groups st !! b = Some (mkGhdr (Some g) ai) -> 0 <= i <= m_last_idx (MR st g) ->
(Z.testbit (m_avail (MR st g)) i = true \/ Z.testbit (m_freed (MR st g)) i = true) ->
s_groups st !! (fst b, sstart (MR st g) i) = None /\ ~ In (fst b, sstart (MR st g) i) (map bslot BL).
Proof.
intros Hb Hil Hbits. assert (Hm : hosts st b g) by (exists ai; exact Hb).
pose proof (is_part _ _ _ IS b g ai i Hb Hil) as P. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm) in P.
unfold one5, tbit in P. destruct P as (_ & nAB & nAC & nAD & _ & nBC & nBD & _).
split.
- destruct (s_groups st !! (fst b, sstart (MR st g) i)) eqn:E; [| reflexivity]. exfalso.
destruct Hbits as [A|F]; [apply nAD| apply nBD]; split; auto; intros Y; rewrite Y in E; discriminate E.
- intros C. destruct Hbits as [A|F]; [apply nAC| apply nBC]; split; auto.
Qed.

#[using="RC__ X L BL LS INV IM"] Lemma hdr_hosts b gh : s_groups st !! b = Some gh -> exists m, hosts st b m.
Proof.
intros Hb. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Eg & _). exists m. destruct gh as [gm gai]; cbn in Eg; subst gm. exists gai. exact Hb.
Qed.

Variable LB : list block.
Hypothesis CR : CORR st LB BL.

#[using="CR"] Lemma LB_blk blk : In blk LB -> exists c off n, In ((c, off), n) BL /\ blk_slot blk = c /\ blk_size blk = n /\ blk_addr blk = conc st c + UNIT * off.
Proof.
intros Hb. destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)). destruct k as [[c off] n].
exists c, off, n. cbn [bslot boff bsize fst snd] in C1, C2, C3. auto.
Qed.

#[using="RC__ X L LS INV IG CR"] Lemma LB_geo blk : In blk LB -> exists c off n m bm i r,
In ((c, off), n) BL /\ blk_slot blk = c /\ blk_size blk = n /\
hosts st bm m /\ 0 <= i <= m_last_idx (MR st m) /\ c = (fst bm, sstart (MR st m) i) /\ s_groups st !! c = None /\
s_regions st !! (fst bm) = Some r /\ r_kind r = RKGroup /\
blk_addr blk = r_base r + sstart (MR st m) i + UNIT * off /\ 0 <= off /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB.
Proof.
intros Hb. destruct (LB_blk _ Hb) as (c & off & n & Hk & C1 & C2 & C3).
destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh. assert (Hm : hosts st bm m) by (exists ai; exact Hh).
destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr).
exists c, off, n, m, bm, i, r.
pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as Hn. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as Hf.
repeat split; auto; try lia.
rewrite C3, Ec. unfold conc, get_region. cbn [fst snd]. rewrite Hr. lia.
Qed.

#[using="RC__ X L BL LS INV ZB IM IG IS CR"] Lemma f_free_clear : fact_free_clear (strip st) LB.
Proof.
change (fact_free_clear st LB). intros g b i H Hi Hbits. fold (MR st g) in *. cbn zeta. rewrite !sstart_of_eq.
pose proof (mem_hosts _ _ H) as Hm. destruct (hosts_GO _ _ Hm) as (ai & Hb & GO).
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
assert (Hil : 0 <= i <= m_last_idx (MR st g)). { destruct Hbits as [A|F]; [pose proof (M3 i Hi A); lia | pose proof (M4 i Hi F); lia]. }
destruct (bit_slot_nonH _ _ _ _ Hb Hil Hbits) as [NH NB].
pose proof (sstart_succ st g i) as SS.
split.
- intros b' gh Hb' Hf. destruct (hdr_hosts _ _ Hb') as [m' Hm'].
destruct (sep_ghdr _ _ _ _ IM IG IS g b i Hm Hil NH m' b' Hm' Hf) as [A|A]; unfold IB; lia.
- intros blk Hblk Hf. destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr & Kr & Ea & Ho & Hn & Fit).
rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr. exists r. split; [reflexivity|].
rewrite Ea, C2. pose proof (sstart_succ st m2 i2) as SS2.
assert (NE : m2 <> g \/ i2 <> i). { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NB. rewrite <- Hf, <- Ec, <- C1.
destruct (Forall2_In_l _ _ _ _ CR Hblk) as (k & HkB & (Ek & _)). rewrite Ek. apply in_map. exact HkB. }
destruct (sep_ext _ _ _ _ IM IG IS g b i Hm Hil NH m2 b2 i2 Hm2 Hf Hi2 NE ltac:(rewrite Ec in NH2; exact NH2)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

#[using="RC__ X L BL LS INV ZB IM IG IS CR"] Lemma f_avail_clear : fact_avail_clear (strip st) LB.
Proof. intros g b i H Hi Ha. exact (f_free_clear g b i H Hi (or_introl Ha)). Qed.

#[using="RC__ X L BL LS INV IM IG IS CR"] Lemma f_hdr_clear : fact_hdr_clear (strip st) LB.
Proof.
change (fact_hdr_clear st LB). intros b gh blk r Hb Hblk Hf Hr.
destruct (LB_geo _ Hblk) as (c & off & n & m2 & b2 & i2 & r' & Hk & C1 & C2 & Hm2 & Hi2 & Ec & NH2 & Hr' & Kr & Ea & Ho & Hn & Fit).
rewrite C1, Ec in Hf. cbn [fst] in Hf. rewrite <- Hf, Hr' in Hr. inversion Hr; subst r'.
destruct (hdr_hosts _ _ Hb) as [m' Hm']. rewrite Ea, C2. pose proof (sstart_succ st m2 i2).
rewrite Ec in NH2. destruct (sep_ghdr _ _ _ _ IM IG IS m2 b2 i2 Hm2 Hi2 NH2 m' b Hm' (eq_sym Hf)) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

#[using="RC__ X L BL LS INV IS ISH CR"] Lemma f_blk_unknown : fact_blk_unknown st LB.
Proof.
intros blk r Hblk Hr a Ha. destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3).
destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & _). cbn [bslot fst snd] in Hs.
pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as (_ & _ & _ & _ & _ & _ & _ & U). cbn [bslot boff bsize fst snd] in U.
rewrite C1 in Hr |- *. rewrite C3, C2 in Ha. unfold conc, get_region in Ha. rewrite Hr in Ha.
destruct (U (a - r_base r) ltac:(lia)) as [h Hh]. exists h. exact Hh.
Qed.

#[using="RC__ X L BL LS INV IM IG IS CR"] Lemma f_blocks_disjoint : fact_blocks_disjoint st LB.
Proof.
intros b1 b2 H1 H2 Hf NE.
destruct (LB_geo _ H1) as (c1 & o1 & n1 & m1 & bm1 & i1 & r1 & K1 & C1 & S1 & Hm1 & Hi1 & E1 & N1 & R1 & _ & A1 & O1 & P1 & F1).
destruct (LB_geo _ H2) as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & C2 & S2 & Hm2 & Hi2 & E2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
rewrite C1, C2, E1, E2 in Hf. cbn [fst] in Hf. rewrite Hf, R2 in R1. inversion R1; subst r2.
rewrite A1, A2, S1, S2. pose proof (sstart_succ st m1 i1). pose proof (sstart_succ st m2 i2).
assert (NE' : m2 <> m1 \/ i2 <> i1). { destruct (aptr_eq_dec m2 m1) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, C2, E1, E2, Hf. reflexivity. }
rewrite E1 in N1. rewrite E2 in N2.
destruct (sep_ext _ _ _ _ IM IG IS m1 bm1 i1 Hm1 Hi1 N1 m2 bm2 i2 Hm2 ltac:(symmetry; exact Hf) Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.

#[using="RC__ X L BL LS INV IG CR"] Lemma LB_blocks_ok : Forall (block_ok st) LB.
Proof.
apply List.Forall_forall. intros blk Hblk. destruct (LB_blk _ Hblk) as (c & off & n & Hk & C1 & C2 & C3).
destruct (block_facts _ _ _ _ _ INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hh.
constructor.
- exists m, i. rewrite C1. split; [exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)|]. fold (MR st m).
split; [exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF)|]. split; [exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF)|].
split; [exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF)|].
exists off. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). rewrite C2, C3. repeat split; lia.
- rewrite C1. destruct (ig_region _ _ _ IG _ _ Hh) as (r & Hr & Kr). rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). cbn [fst]. exists r. auto.
- rewrite C2. exact (bf_n _ _ _ _ _ _ _ _ _ _ _ BF).
Qed.

#[using="RC__ X st L BL LS INV IS CR"] Lemma LB_nodup : List.NoDup (map blk_slot LB).
Proof.
rewrite (Forall2_map_eq (corr1 st) blk_slot bslot LB BL CR ltac:(intros a b (E & _); exact E)).
apply NoDup_ListNoDup. exact (is_nodup _ _ _ IS).
Qed.

#[using="RC__ X L BL LS INV IR"] Lemma region_rid rid r : s_regions st !! rid = Some r -> (rid < s_next_rid st)%N.
Proof. exact (ir_ids _ _ _ IR rid r). Qed.
#[using="RC__ X L BL LS INV IR IA"] Lemma area_rid a ar : s_areas st !! a = Some ar -> (fst a < s_next_rid st)%N.
Proof. intros Ha. destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & _) & _). exact (region_rid _ _ Hr). Qed.
#[using="RC__ X L BL LS INV IR IA"] Lemma area_rid' a : s_areas st !! a <> None -> (fst a < s_next_rid st)%N.
Proof. intros Ha. destruct (s_areas st !! a) as [ar|] eqn:E; [exact (area_rid _ _ E)| congruence]. Qed.
#[using="RC__ X L BL LS INV IR IA"] Lemma present_rid m : s_metas st !! m <> None -> (fst m < s_next_rid st)%N.
Proof.
intros Hm. destruct (s_metas st !! m) as [mr|] eqn:E; [| congruence].
destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & ->). unfold mslot, aadd. cbn [fst]. exact (area_rid _ _ Ha).
Qed.
#[using="Type"] Lemma nonzero_present m : MR st m <> meta0 -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; congruence. Qed.
#[using="RC__ X L BL INV IR IA"] Lemma listed_rid m h : In m (LS h) -> (fst m < s_next_rid st)%N.
Proof. intros H. apply present_rid. exact (listed_present _ _ _ _ _ INV m h H). Qed.
#[using="RC__ X L BL LS INV IR IG"] Lemma hosts_rid b m : hosts st b m -> (fst b < s_next_rid st)%N.
Proof. intros [ai Hb]. destruct (ig_region _ _ _ IG _ _ Hb) as (r & Hr & _). exact (region_rid _ _ Hr). Qed.

#[using="RC__ X L BL LS INV ZB IR IA IM IL IG ISH"] Lemma f_ptrs : fact_ptrs st.
Proof.
split.
- unfold ptrs_in. cbn zeta.
assert (HD : forall h, optr_in (fun rid => (rid < s_next_rid st)%N) (get_head st h)).
{ intros h. destruct (get_head st h) as [a|] eqn:E; cbn; [| exact I]. exact (listed_rid _ _ (head_listed _ _ _ _ _ INV h a E)). }
split; [exact (HD LFree)|].
split. { destruct (c_avail_meta (ctx st)) as [q|] eqn:E; cbn; [| exact I]. destruct (ia_availptr _ IA q E) as (r & Hr & _). exact (region_rid _ _ Hr). }
split. { destruct (c_meta_area_head (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_head _ IA q E)). }
split. { destruct (c_meta_area_tail (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (area_rid' _ (ia_tail _ IA q E)). }
split. { destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:E; cbn; [| exact I].
destruct (ir_cursor _ _ _ IR) as (_ & _ & CU). destruct (CU rid off E) as (r & Hr & _). exact (region_rid _ _ Hr). }
split; [intros sc; exact (HD (LActive sc))|].
split. { pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (c_brk (s_ctx st)) as [| |rid off]; try exact I.
destruct BR as (_ & r & Hr & _). exact (region_rid _ _ Hr). }
split.
{ intros g. fold (MR st g). pose proof (il_link _ _ IL g) as [[L1 L2] L3].
assert (NX : forall x, m_next (MR st g) = Some x -> (fst x < s_next_rid st)%N).
{ intros x Hx. destruct (L2 ltac:(rewrite Hx; discriminate)) as [h Hh]. exact (listed_rid _ _ (next_listed _ _ _ _ _ INV h g x Hh Hx)). }
split. { destruct (m_prev (MR st g)) as [p|] eqn:Ep; cbn; [| exact I].
destruct (m_next (MR st g)) as [x|] eqn:Ex; [| discriminate (L3 eq_refl)].
destruct (L2 ltac:(discriminate)) as [h Hh]. exact (listed_rid _ _ (prev_listed _ _ _ _ _ INV h g p Hh Ep)). }
split. { destruct (m_next (MR st g)) as [x|] eqn:Ex; cbn; [| exact I]. exact (NX x eq_refl). }
destruct (m_mem (MR st g)) as [b|] eqn:Eb; cbn; [| exact I]. exact (hosts_rid _ _ (mem_hosts _ _ Eb)). }
split.
{ intros a ar Ha. split; [exact (area_rid _ _ Ha)|]. destruct (a_next ar) as [a'|] eqn:E; cbn; [| exact I].
destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT). exact (area_rid' _ (NXT a' E)). }
intros b gh Hb. destruct (hdr_hosts _ _ Hb) as [m Hm]. split; [exact (hosts_rid _ _ Hm)|].
destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Eg & Hmem & _). rewrite Eg. cbn. apply present_rid. apply nonzero_present. intros E. rewrite E in Hmem. cbn in Hmem. discriminate.
- intros rid Hrid. split.
+ destruct (s_regions st !! rid) as [r|] eqn:E; [| reflexivity]. pose proof (region_rid _ _ E). lia.
+ destruct (s_shadow st !! rid) as [sh|] eqn:E; [| reflexivity]. destruct (ish_dom _ _ ISH _ _ E) as (r & Hr & _). pose proof (region_rid _ _ Hr). lia.
Qed.

#[using="RC__ X L BL LS INV IR IM IG IS"] Lemma conc_group_inj b1 b2 m1 m2 : hosts st b1 m1 -> hosts st b2 m2 -> conc st b1 = conc st b2 -> b1 = b2.
Proof.
intros H1 H2 E.
destruct (conc_group _ _ H1) as (r1 & R1 & K1 & C1 & LO1 & HI1). destruct (conc_group _ _ H2) as (r2 & R2 & K2 & C2 & LO2 & HI2).
destruct (N.eq_dec (fst b1) (fst b2)) as [Ef|NEf].
- rewrite Ef, R2 in R1. inversion R1; subst r1. apply injective_projections; [exact Ef| lia].
- exfalso. pose proof (ir_disj _ _ _ IR _ _ _ _ R1 R2 NEf) as D. unfold region_live_range in D. rewrite K1, K2 in D. lia.
Qed.

#[using="X L BL LS INV IR IM IG IS"] Lemma groups_count : Z.of_nat (length (map_to_list (s_groups st))) <= alloc_ceiling.
Proof.
rewrite <- (length_map (fun bh : aptr * ghdr => conc st (fst bh))).
assert (HIN : forall bh, In bh (map_to_list (s_groups st)) -> s_groups st !! (fst bh) = Some (snd bh)).
{ intros [b h] Hin. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
apply NoDup_Z_length; [unfold alloc_ceiling; lia| |].
- apply NoDup_map_on.
+ intros [b1 h1] [b2 h2] I1 I2 E. cbn in E. pose proof (HIN _ I1) as G1. pose proof (HIN _ I2) as G2. cbn in G1, G2.
destruct (hdr_hosts _ _ G1) as [m1 Hm1]. destruct (hdr_hosts _ _ G2) as [m2 Hm2].
pose proof (conc_group_inj _ _ _ _ Hm1 Hm2 E) as Eb. subst b2. rewrite G1 in G2. inversion G2. reflexivity.
+ pose proof (NoDup_fst_map_to_list (s_groups st)) as ND. apply NoDup_ListNoDup in ND.
apply (NoDup_map_inv fst). exact ND.
- intros x Hx. apply in_map_iff in Hx. destruct Hx as ([b h] & <- & Hin). cbn. pose proof (HIN _ Hin) as G. cbn in G.
destruct (hdr_hosts _ _ G) as [m Hm]. destruct (conc_group _ _ Hm) as (r & Hr & Kr & C & LO & HI).
destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CE & _). lia.
Qed.

#[using="RC__ X L BL LS INV ZB IR IM IG IS"] Lemma gcnt_bound sc : 0 <= gcnt st sc < 2 ^ 60.
Proof.
unfold gcnt.
pose proof (zsum_bound (map (fun bh : aptr * ghdr => match g_meta (snd bh) with
| Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0 | None => 0 end) (map_to_list (s_groups st))) 32) as ZS.
rewrite length_map in ZS. pose proof groups_count as GC. unfold alloc_ceiling in GC.
eassert (H : _); [| specialize (ZS H); lia].
intros x Hx. apply in_map_iff in Hx. destruct Hx as ([b h] & <- & Hin). cbn.
assert (G : s_groups st !! b = Some h). { apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
destruct (im_hdr _ _ _ IM _ _ G) as (m & Eg & Hmem & AI). rewrite Eg.
destruct (hosts_GO _ _ (mem_hosts _ _ Hmem)) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of.
destruct (m_sizeclass (MR st m) =? sc); lia.
Qed.

#[using="RC__ X L BL LS INV ZB IR IA IM IG IS"] Lemma f_usage : fact_usage (strip st).
Proof.
intros i. rewrite usage_strip. destruct (c_usage (s_ctx st) !! i) as [v|] eqn:E.
- pose proof (ia_usage_keys _ IA i v E) as Hi. rewrite (ia_usage _ IA i Hi). apply gcnt_bound.
- unfold usage, ctx. rewrite E. cbn. lia.
Qed.
End MF.
End RC__1.

Local Ltac inst f INV CR :=
first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV eq_refl) | exact (f _ _ _ _ _ INV eq_refl eq_refl)
| exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV eq_refl _ CR) | exact (f _ _ _ _ _ INV eq_refl eq_refl _ CR) ].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Theorem areach_facts_proof : forall {resv sec} st LB, AREACH_from resv sec st LB -> @MFACTS_g resv st LB.
Proof.
intros resv sec st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
constructor.
- inst LB_blocks_ok INV CR.
- inst LB_nodup INV CR.
- inst f_ticks INV CR.
- rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
- inst f_ctx INV CR.
- inst f_active INV CR.
- inst f_gmeta INV CR.
- inst f_avail_clear INV CR.
- inst f_hdr0 INV CR.
- inst f_free_clear INV CR.
- inst f_hdr_clear INV CR.
- inst f_usage INV CR.
- inst f_masks INV CR.
- inst f_maplen INV CR.
- inst f_slots INV CR.
- inst f_slots_complete INV CR.
- inst f_ptrs INV CR.
- inst f_blk_unknown INV CR.
- inst f_blocks_disjoint INV CR.
- inst f_cell_ticks INV CR.
Qed.

End RC__2.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma land_high_low x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof.
intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n k) as [LT|GE].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma lor_shl_small x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof. intros. apply lor_disjoint_add. apply land_high_low; assumption. Qed.

#[using="Type"] Lemma lor_small_shl x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor y (x * 2^k) = x * 2^k + y.
Proof. intros. rewrite Z.lor_comm. apply lor_shl_small; assumption. Qed.

#[using="Type"] Lemma lor_32 c : 0 <= c < 32 -> Z.lor c 32 = c + 32.
Proof. intros. change 32 with (1 * 2^5) at 1. rewrite lor_small_shl by lia. lia. Qed.

#[using="Type"] Lemma land_pg_mask q : 0 <= q < 2^52 -> Z.land (4096 * q) 18446744073709547520 = 4096 * q.
Proof.
intros Hq. replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma hdr_byte_facts x ai : 0 <= x < 256 -> 0 <= ai < 32 ->
0 <= Z.lor (Z.land x 18446744073709551584) ai < 256 /\ Z.land (Z.lor (Z.land x 18446744073709551584) ai) 31 = ai.
Proof.
intros Hx Hai.
assert (E : Z.land x 18446744073709551584 = Z.land x 224).
{ replace x with (Z.land x 255) at 1 by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite <- !Z.land_assoc. reflexivity. }
rewrite E. pose proof (land_upper x 224 ltac:(lia) ltac:(lia)).
split.
- change 256 with (2^8). apply lor_lt_pow2; lia.
- rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc. change (Z.land 224 31) with 0. rewrite Z.land_0_r. rewrite Z.lor_0_l.
change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma tail_low16 sc cnt q : 0 <= sc < 48 -> 1 <= cnt <= 32 -> 0 <= q < 16 ->
Z.lor (Z.lor (Z.land sc 63 * 2^6) (Z.lor (Z.land (cnt - 1) 31) 32)) (Z.land (4096 * q) 18446744073709547520)
= (cnt - 1) + 32 + 64 * sc + 4096 * q.
Proof.
intros Hsc Hc Hq.
replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
rewrite land_pg_mask by lia.
replace 32 with (1 * 2^5) at 1 by reflexivity. rewrite (lor_small_shl 1 5 (cnt - 1)) by lia.
rewrite (lor_shl_small sc 6) by (cbn; lia).
replace (4096 * q) with (q * 2^12) by (cbn; lia). rewrite (lor_small_shl q 12) by (cbn; lia). cbn. lia.
Qed.

#[using="Type"] Lemma firstn_le_bytes n k z : firstn n (Z_to_le_bytes (n + k) z) = Z_to_le_bytes n z.
Proof. revert z. induction n as [|n IH]; intros z; [reflexivity|]. cbn [Z_to_le_bytes Nat.add firstn]. f_equal. apply IH. Qed.

#[using="Type"] Lemma skipn_le_bytes n k z : skipn n (Z_to_le_bytes (n + k) z) = Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
revert z. induction n as [|n IH]; intros z.
- cbn. rewrite Z.shiftr_0_r. reflexivity.
- cbn [Z_to_le_bytes Nat.add skipn]. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma tail_word_bytes (s0r : word) (L W W' : Z) :
0 <= W < 2^64 -> 0 <= W' < 2^64 -> 0 <= L < 65536 ->
bv_unsigned s0r mod 65536 = L -> W' mod 65536 = L -> Z.shiftr W' 16 = Z.shiftr W 16 ->
le2 s0r ++ skipn 2 (le8 (wz W)) = le8 (wz W').
Proof.
intros HW HW' HL HS HM HH.
unfold le2, le8, word_to_le_bytes, wz. rewrite !unsigned_lit by lia.
change 8%nat with (2 + 6)%nat. rewrite skipn_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul].
rewrite <- (firstn_skipn 2 (Z_to_le_bytes (2 + 6) W')). rewrite firstn_le_bytes, skipn_le_bytes.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. rewrite HH. f_equal.
rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned s0r) 16) by (cbn; lia).
rewrite <- (Z_to_le_bytes_mod 2 W' 16) by (cbn; lia).
change (2^16) with 65536. rewrite HS, HM. reflexivity.
Qed.

#[using="Type"] Lemma word_low16_bytes W : 0 <= W < 2^64 -> firstn 2 (le8 (wz W)) = le2 (wz (W mod 65536)).
Proof.
intros HW. unfold le2, le8, word_to_le_bytes, wz. rewrite !unsigned_lit by (try lia; Z.div_mod_to_equations; lia).
change 8%nat with (2 + 6)%nat. rewrite firstn_le_bytes.
change 65536 with (2^16). rewrite Z_to_le_bytes_mod by (cbn; lia). reflexivity.
Qed.

#[using="Type"] Lemma sllw2_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (i mod 32))) = wz (sxv (2 ^ (i + 1))).
Proof.
intros Hi. rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

#[using="Type"] Lemma subw_sxv_word a b : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv a)) - bv_unsigned (wz (sxv b)))) = wz (sxv (a - b)).
Proof.
rewrite !wz_unsigned by (apply sxv_range). unfold wz, sxv.
rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 a mod 2 ^ 64 - bv_swrap 32 b mod 2 ^ 64))). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.

#[using="Type"] Lemma cell_read_hdr_havoc_old : forall st b o,
snd b mod 16 = 0 -> 0 <= o < 12 ->
(forall v t, (r_cells (get_shadow st (fst b))) !! (snd b + o) = Some (v, t) -> (t < s_tick st)%N) ->
exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
intros st b o B16 Ho OLD. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
rewrite lookup_insert_eq. cbn [default from_option id].
unfold cell_read. cbn [r_cells r_hav r_havp].
replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
rewrite lookup_insert_eq. cbn [default from_option id].
replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
unfold hav_add. unfold stale. cbn [existsb fst snd].
replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
destruct (r_cells (get_shadow st (fst b)) !! (snd b + o)) as [[v t]|] eqn:E.
- specialize (OLD v t eq_refl). replace (t <? s_tick st)%N with true by (symmetry; apply N.ltb_lt; exact OLD).
cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
- cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
Qed.

Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
(r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

Definition stA : mstate := hdr_havoc p stT.
Definition stB : mstate := set_usage sc (usage stT sc + cnt) stA.
Definition recA : meta := mkMeta None None (Some p) AV FR 0 0 0 ml.
Definition stC : mstate := put_meta mt recA stB.
Definition stD : mstate := put_group p (Some mt) ai stC.
Definition recF : meta := mkMeta (Some mt) (Some mt) (Some p) (AV - 1) FR (cnt - 1) 1 sc ml.
Definition stE : mstate := put_meta mt recF stD.
Definition stFin : mstate := set_active sc (Some mt) stE.

Definition st_model : mstate :=
let st := hdr_havoc p stT in
let st1 := set_usage sc (usage st sc + cnt) st in
let avail := mask_upto ai in
let freed := mask_upto (cnt - 1) - avail in
let st2 := upd_meta mt (fun r =>
m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
(m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
let st3 := put_group p (Some mt) ai st2 in
let st4 := add_slots mt p (get_stride (get_meta_rec st3 mt)) cnt st3 in
let st5 := upd_meta mt (fun r => m_set_avail (m_avail r - 1) r) st4 in
let st6 := upd_meta mt (fun r => m_set_prev (Some mt) (m_set_next (Some mt) r)) st5 in
set_active sc (Some mt) st6.

#[using="stT cnt ai mt p G P AV FR P0"] Lemma mask_upto_range k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
change (2^32) with (2 * 2^31). lia.
Qed.

#[using="stT mt p G P CNT AI P0"] Lemma AV_FR_range : 1 <= AV < 2^32 /\ 0 <= FR < 2^32 /\ 0 <= AV - 1 < 2^32.
Proof.
pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
assert (mask_upto ai <= mask_upto (cnt - 1)).
{ unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
unfold AV, FR. lia.
Qed.

#[using="Type"] Lemma rec_set_slots st v q : get_meta_rec (set_slots v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_put_group st b g a q : get_meta_rec (put_group b g a st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_hdr_havoc st b q : get_meta_rec (hdr_havoc b st) q = get_meta_rec st q. Proof. reflexivity. Qed.

Lemma st_model_eq_rec q : get_meta_rec st_model q = get_meta_rec stFin q.
Proof using SC CNT REC P0.
unfold st_model, stFin, stE, stD, stC, stB, stA. cbv zeta. unfold upd_meta, add_slots.
rewrite !rec_set_active.
destruct (decide (q = mt)) as [->|NE].
- rewrite !get_meta_rec_put_same, rec_set_slots, rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC.
unfold recF. cbv [m_set_prev m_set_next m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen].

replace (Z.land (cnt - 1) 31) with (cnt - 1) by (clear -CNT; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
replace (Z.land sc 63) with sc by (clear -SC; change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
change (Z.land 1 1) with 1. reflexivity.
- rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed.

Definition tailW : list (Z * Z) :=
[(CTX + 464 + 8 * sc, CTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z.

End TAIL.

End RC__1.
