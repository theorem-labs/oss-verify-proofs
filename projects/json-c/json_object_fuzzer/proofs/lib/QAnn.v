(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaiD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQCz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlOh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlOh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhnL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhnL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcV4.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBv7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1u2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1u2.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope stree_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition RK (st st' : mstate) (c : cptr) (BL : list blk) (moved : Prop) : Prop :=
forall rid r r', s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r' ->
r' = r \/ (moved /\ rid = fst c /\ forall k, In k BL -> fst (bslot k) = rid -> bslot k = c).

#[using="Type"] Lemma RK_of_GP st st' c BL X : GP st st' -> RK st st' c BL X.
Proof. intros [G _] rid r r' Hr K Hr'. left. rewrite (G rid r Hr K) in Hr'. congruence. Qed.

#[using="Type"] Lemma ranges_free_except_eq X st L old a n : inv_R X st L ->
ranges_free_except old (lranges L) a n = ranges_free_except old (live_ranges st) a n.
Proof. intros IR. unfold ranges_free_except. apply forallb_ext. apply (lranges_iff X st L IR). Qed.

#[using="Type"] Lemma mremap_answer_ok_eq X st L old ol nl z : inv_R X st L ->
mremap_answer_ok (lranges L) old ol nl z = mremap_answer_ok (live_ranges st) old ol nl z.
Proof. intros IR. unfold mremap_answer_ok. rewrite (ranges_free_eq X st L IR), (ranges_free_except_eq X st L _ _ _ IR). reflexivity. Qed.

#[using="Type"] Lemma ranges_free_except_regions st old a n rid r :
ranges_free_except old (live_ranges st) a n = true -> s_regions st !! rid = Some r ->
let '(b, l) := region_live_range r in b = old \/ a + n <= b \/ b + l <= a.
Proof.
intros H Hr. unfold ranges_free_except in H. rewrite forallb_forall in H.
specialize (H (region_live_range r)). destruct (region_live_range r) as [b l] eqn:E.
assert (Hin : In (b, l) (live_ranges st)).
{ unfold live_ranges. apply in_app_iff. right. apply in_map_iff. exists (rid, r). rewrite <- E. split; [reflexivity| apply In_map_to_list_regions; exact Hr]. }
specialize (H Hin). cbn in H. destruct (Z.eqb_spec b old); [left; assumption| right].
cbn in H. unfold iv_disjoint in H. apply Bool.orb_true_iff in H. destruct H as [H|H]; [apply Z.leb_le in H| apply Z.leb_le in H]; lia.
Qed.

#[using="Type"] Lemma mremap_ok_facts live old ol nl z :
mremap_answer_ok live old ol nl z = true -> is_err z = false -> old + round_up_pg ol <= alloc_ceiling ->
(z = old /\ (round_up_pg nl <= round_up_pg ol \/ (old + round_up_pg nl <= alloc_ceiling /\ ranges_free_except old live (old + round_up_pg ol) (round_up_pg nl - round_up_pg ol) = true)))
\/ (z <> old /\ round_up_pg ol < round_up_pg nl /\ 0 < z /\ z mod PGSZ = 0 /\ z + round_up_pg nl <= alloc_ceiling /\ ranges_free live z (round_up_pg nl) = true).
Proof.
unfold mremap_answer_ok, is_errno_form, is_err. cbv zeta. intros H E Hold.
apply Bool.orb_true_iff in H. destruct H as [H|H].
- apply Bool.orb_true_iff in H. destruct H as [H|H].
+ apply Bool.andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_ge in E. unfold TWO64 in *. lia.
+ apply Bool.andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. left. split; [exact H1|].
apply Bool.orb_true_iff in H2. destruct H2 as [H2|H2]; [left; apply Z.leb_le in H2; exact H2| right].
apply Bool.andb_true_iff in H2 as [H3 H4]. apply Z.leb_le in H3. auto.
- right. apply Bool.andb_true_iff in H as [H H6]. apply Bool.andb_true_iff in H as [H H5]. apply Bool.andb_true_iff in H as [H H4].
apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
apply Bool.negb_true_iff in H1. apply Z.eqb_neq in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. apply Z.eqb_eq in H4. apply Z.leb_le in H5. auto 10.
Qed.

#[using="Type"] Lemma mremap_ok_len live old ol nl z :
mremap_answer_ok live old ol nl z = true -> is_err z = false -> old + round_up_pg ol <= alloc_ceiling -> 0 < old ->
nl < LEN_MAX.
Proof.
intros H E Hold Hpos. pose proof (round_up_ge nl). pose proof (round_up_ge ol).
destruct (mremap_ok_facts _ _ _ _ _ H E Hold) as [(_ & [SH|(GR & _)])|(_ & _ & Z0 & _ & GR & _)]; unfold alloc_ceiling, LEN_MAX in *; lia.
Qed.

#[using="Type"] Lemma mremap_err_errno live old ol nl z :
mremap_answer_ok live old ol nl z = true -> is_err z = true -> old + round_up_pg ol <= alloc_ceiling -> 0 <= ol -> 0 <= nl -> is_errno_form z = true.
Proof.
unfold mremap_answer_ok, is_err. cbv zeta. intros H E Hold OL NL. apply Z.ltb_lt in E.
apply Bool.orb_true_iff in H. destruct H as [H|H].
- apply Bool.orb_true_iff in H. destruct H as [H|H]; [exact H|]. exfalso.
apply Bool.andb_true_iff in H as [H1 _]. apply Z.eqb_eq in H1. pose proof (round_up_ge ol). unfold alloc_ceiling, TWO64 in *. lia.
- exfalso. apply Bool.andb_true_iff in H as [H _]. apply Bool.andb_true_iff in H as [H H5]. apply Z.leb_le in H5.
pose proof (round_up_ge nl). unfold alloc_ceiling, TWO64 in *. lia.
Qed.

Definition RPOST (BL : list blk) (c : cptr) (off n : Z) (L' : mled) (r : mstate * optr) : Prop :=
match snd r with
| None => exists LS', INVL x0 (fst r) L' BL LS'
| Some p' => exists c' off' LS', p' = aadd c' (UNIT * off') /\ 0 <= off' <= 255
/\ INVL x0 (fst r) L' (((c', off'), n) :: bl_remove c BL) LS'
/\ ((c' = c /\ off' = off) \/ ~ In c' (map bslot BL))
end.

Section FT.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n0 n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis T0 : TF0 st.
Hypothesis Hk : In ((c, off), n0) BL.
Hypothesis Hn : 0 <= n.
Hypothesis BF : blk_facts st c off n0 m bm i ai a ar ka.

Let IR := proj1 INV.
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).

#[using="c off n0 i ai a ar ka BF"] Lemma ft_hosts : hosts st bm m. Proof. exists ai. exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). Qed.
#[using="RC__ L BL c off n0 i a ar ka INV BF IG"] Lemma ft_GO : group_ok x0 st LS m bm ai. Proof. exact (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)). Qed.
#[using="off n0 Hk"] Lemma ft_c_in : In c (map bslot BL). Proof. change c with (bslot ((c, off), n0)). apply in_map. exact Hk. Qed.

#[using="n0 Hk Hn"] Lemma general_ft (Lx : mled) (stx : mstate) LSx :
INVL x0 stx Lx BL LSx -> ld_live Lx = ld_live L ->
ftree Lx ('(st1, r) <-- malloc stx n ;;
match r with None => ret (st1, @None aptr) | Some q => st2 <-- free st1 (Some (rl_p c off)) ;; ret (st2, Some q) end)
(RPOST BL c off n).
Proof.
intros INVx LIVEx.
eapply ftree_bind; [exact (malloc_INVL stx Lx BL LSx n INVx Hn)|].
intros L1 [st1 [q|]] (LIVE1 & GP1 & POST); cbn [fst snd] in POST |- *.
- destruct POST as (c' & off' & LS1 & Eq & Ho & INV1 & NI).
eapply ftree_bind; [exact (free_INVL_closed st1 L1 (((c', off'), n) :: BL) LS1 c off n0 INV1 ltac:(right; exact Hk))|].
intros L2 st2 [LS2 INV2]. cbn. exists c', off', LS2. split; [exact Eq|]. split; [exact Ho|]. split; [| right; exact NI].
cbn [bl_remove bslot fst] in INV2. rewrite (aptr_eqb_neq c' c) in INV2; [exact INV2|]. intros ->. exact (NI ft_c_in).
- cbn. destruct POST as [LS1 INV1]. exists LS1. exact INV1.
Qed.

#[using="LS n0 m bm i ai a ar ka INV T0 Hk Hn BF IR IG"] Theorem realloc_body_INVL : ftree L (realloc_body st (rl_p c off) n) (RPOST BL c off n).
Proof.
pose proof ft_GO as GO. pose proof INV as (IR' & IA & IM & IL & IG' & IS & ISH).
destruct (size_overflows n) eqn:SO.
{ unfold realloc_body. rewrite SO. cbn. exists LS. exact INV. }
destruct (@realloc_body_unfold _ st c off n0 n m bm i ai a ar ka BF SO) as [-> RD3].
unfold rl_body.
pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF.
assert (IPL : UNIT * off + n <= get_stride (MR st m) - IB -> get_stride (MR st m) - IB - UNIT * off - n < 2 ^ 32 ->
ftree L (rr_set_size st (rl_p c off) (rl_e st m bm i) n (fun st1 => ret (havoc (rl_p c off) n st1, Some (rl_p c off)))) (RPOST BL c off n)).
{ intros F1 F2. unfold rr_set_size. rewrite (RD3 _ st) by reflexivity. cbn [ftree ret].
exists c, off, LS. split; [reflexivity|]. split; [exact OFF|]. split; [| left; auto].
replace (rl_e st m bm i) with (ip_e st c m).
2:{ unfold ip_e, rl_e, rl_stride. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). unfold aadd, sstart, gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn. f_equal. lia. }
change (rl_p c off) with (ip_p c off). change (rl_b3 st off n0 m i) with (ip_b3 st off n0 m i). cbn [fst].
rewrite (inplace_eq st c off n0 n m bm i).
apply (inplace_INVL st L BL LS c off n0 n m bm i ai a ar ka INV Hk BF (TF0_TF2 _ T0) Hn F1 F2). }
destruct (rl_inplace st off n m) eqn:INPL.
{
unfold rl_inplace in INPL. apply andb_prop in INPL as [INPL C3]. apply andb_prop in INPL as [C1 C2].
apply Z.leb_le in C1. apply Z.ltb_lt in C2. apply Z.leb_le in C3.
pose proof (size_to_class_ok n ltac:(lia)) as [SC _].
assert (SC48 : m_sizeclass (MR st m) < 48) by (destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|[E _]]; [lia| rewrite E in C3; lia]).
pose proof (small_stride x0 st L BL LS bm m INV ft_hosts SC48) as SS.
apply IPL; unfold rl_stride in *; clear -C1 SS OFF Hn; unfold UNIT, IB in *; lia. }
destruct (rl_big st n m) eqn:BIG; [| apply (general_ft L st LS INV eq_refl)].

unfold rl_big in BIG. apply andb_prop in BIG as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
assert (SC63 : m_sizeclass (MR st m) = 63) by (destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|[E _]]; [lia| exact E]).
destruct (@rl_big_facts _ st L BL LS c off n0 n m bm i ai a ar ka INV BF INPL ltac:(unfold rl_big; rewrite (proj2 (Z.leb_le _ _) B1), (proj2 (Z.leb_le _ _) B2); reflexivity) SC63)
as (I0 & LI0 & ML & B0 & Ecb & _ & N0 & FIT0 & ND).
apply ftree_guard; [apply Z.eqb_eq; exact SC63|]. cbv zeta.

destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r0 & Hr0 & K0 & ML0 & GE).
pose proof (ir_shape _ _ _ IR _ _ Hr0) as (RS1 & RS2 & RS3 & RS4 & RS5 & _).
assert (Ebase : conc st bm = r_base r0) by (unfold conc, get_region; rewrite Hr0, B0; lia).
assert (NLpos : 0 < rl_needed off n) by (unfold rl_needed, rr_needed; pose proof (round_up_ge (n + UNIT * off + UNIT + IB)); unfold UNIT, IB in *; lia).
assert (NLal : rl_needed off n mod PGSZ = 0) by (unfold rl_needed, rr_needed; apply round_up_pg_mod).
assert (NL64 : rl_needed off n < TWO64).
{ unfold rl_needed, rr_needed, TWO64. unfold size_overflows in SO. apply Z.leb_gt in SO.
pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [[_ U] _]. unfold UNIT, IB in *. lia. }
assert (FIN : forall z Lz,
0 < z /\ z mod PGSZ = 0 -> z + rl_needed off n <= alloc_ceiling ->
(forall rid2 r2, rid2 <> fst bm -> s_regions st !! rid2 = Some r2 -> let '(b2, l2) := region_live_range r2 in z + rl_needed off n <= b2 \/ b2 + l2 <= z) ->
Lz = rm_L' st L bm z (rl_needed off n) ->
ftree Lz (rr_set_size (wr8 (rl_e' off n bm) 0 (remap_region (fst bm) z (rl_needed off n) m st)) (rl_p c off) (rl_e' off n bm) n
(fun st3 => ret (havoc (rl_p c off) n st3, Some (rl_p c off)))) (RPOST BL c off n)).
{ intros z Lz Hz Hzc DISJ ->. unfold rr_set_size.
assert (NLlt : rl_needed off n < LEN_MAX) by (unfold LEN_MAX, alloc_ceiling in *; clear -Hz Hzc; lia).
rewrite (@rl_fin_rd3 _ st L BL LS c off n0 n m bm i ai a ar ka INV Hn BF SO _ _ _ INPL ltac:(unfold rl_big; rewrite (proj2 (Z.leb_le _ _) B1), (proj2 (Z.leb_le _ _) B2); reflexivity) SC63).
cbn [ftree ret]. exists c, off. eexists. split; [reflexivity|]. split; [exact OFF|]. split; [| left; auto].
unfold rl_p, rl_e'. change (rl_b3 st off n0 m i) with (rm_b3 st off n0 m i).
rewrite <- (remap_eq st L BL LS c off n0 n m bm i ai a ar ka z (rl_needed off n) INV Hk BF SC63 Hz (conj (conj NLpos NLlt) NLal)).
apply (remap_INVL st L BL LS c off n0 n m bm i ai a ar ka z (rl_needed off n) INV Hk BF T0 Hn SC63 Hz (conj (conj NLpos NLlt) NLal) Hzc DISJ ND).
unfold rl_needed, rr_needed. pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [[_ U] _]. unfold UNIT, IB in *. lia. }
assert (STR : get_stride (MR st m) = m_maplen (MR st m) * 4096 - UNIT).
{ unfold get_stride. rewrite LI0. replace (m_maplen (MR st m) =? 0) with false by (symmetry; apply Z.eqb_neq; exact ML). reflexivity. }
destruct (Z.eqb_spec (rl_oldlen st m) (rl_needed off n)) as [EQL|NEL].
-
unfold rl_oldlen in EQL. apply IPL; rewrite STR, EQL; [clear -ND N0 OFF Hn; unfold UNIT, IB in *; lia|].
unfold rl_needed, rr_needed. pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [[_ U] _]. clear -U OFF Hn N0. unfold UNIT, IB in *. lia.
- destruct (Z.leb_spec PTRDIFF_MAX (rl_needed off n)) as [PDM|PDM].
{  apply (general_ft L st LS); [exact INV| reflexivity]. }

rewrite Ebase.
assert (RUo : round_up_pg (rl_oldlen st m) = rl_oldlen st m) by (unfold rl_oldlen; rewrite ML0; apply round_up_pg_id; apply round_up_pg_mod).
assert (RUn : round_up_pg (rl_needed off n) = rl_needed off n) by (apply round_up_pg_id; exact NLal).
assert (OLc : r_base r0 + round_up_pg (rl_oldlen st m) <= alloc_ceiling) by (rewrite RUo; unfold rl_oldlen; rewrite ML0; exact RS5).
assert (INg : In (r_base r0, r_len r0) (ld_groups L)).
{ eapply Permutation_in; [apply Permutation_sym; exact (ir_groups _ _ _ IR)|]. apply in_map_iff. exists (fst bm, r0). split; [reflexivity|].
apply filter_In. split; [apply In_map_to_list_regions; exact Hr0| cbn; rewrite K0; reflexivity]. }
apply ftree_vis; [reflexivity| reflexivity| | |].
+ cbn. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [clear -NLpos NL64; lia|]. split; [exact NLal|].
exists (r_len r0). split; [exact INg|]. split; [unfold rl_oldlen; rewrite ML0; reflexivity| intros E; apply NEL; symmetry; exact E].
+ intros z Hz. cbn [answer_ok] in Hz. rewrite (mremap_answer_ok_eq x0 st L _ _ _ _ IR) in Hz. rewrite Hz. cbn [negb].
cbn [event_post]. destruct (is_err z) eqn:ER.
* rewrite (mremap_err_errno _ _ _ _ _ Hz ER OLc ltac:(unfold rl_oldlen; pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF); lia) ltac:(lia)). apply (general_ft L st LS INV eq_refl).
* assert (NEF : is_errno_form z = false).
{ unfold is_errno_form. unfold is_err in ER. apply Z.ltb_ge in ER. apply Bool.andb_false_iff. left. apply Z.leb_gt. clear -ER. unfold TWO64 in *. lia. }
rewrite NEF.
destruct (mremap_ok_facts _ _ _ _ _ Hz ER OLc) as [(Ez & CASES)|(NEz & GROW & Z0 & ZM & ZC & RF)].
--  subst z. apply (FIN (r_base r0)); [split; [exact RS1| exact RS2]| | | unfold rm_L', L', QcV4.Mq0.r0; rewrite Hr0; reflexivity].
++ rewrite RUn, RUo in CASES. destruct CASES as [SH|[GR _]]; [clear -SH OLc RUo; rewrite RUo in OLc; lia| exact GR].
++ intros rid2 r2 NE2 H2. pose proof (ir_disj _ _ _ IR (fst bm) rid2 r0 r2 Hr0 H2 ltac:(congruence)) as D.
unfold region_live_range in D at 1. rewrite K0, <- ML0 in D. fold (rl_oldlen st m) in D.
rewrite RUn, RUo in CASES.
assert (OLpos : 0 < rl_oldlen st m) by (unfold rl_oldlen; pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF); clear -ML H; lia).
assert (L2pos : 0 < snd (region_live_range r2)).
{ pose proof (ir_shape _ _ _ IR _ _ H2) as (T1 & _ & T3 & _ & _ & T6). pose proof (round_up_ge (r_len r2)) as T4.
unfold region_live_range. destruct (r_kind r2) eqn:EK; cbn [snd]; [| clear -T3 T4; lia| clear -T3 T4; lia].
destruct (T6 ltac:(left; exact EK)) as [_ T7]. clear -T4 T7. unfold PGSZ in *. lia. }
destruct CASES as [SH|[_ RFE]].
** destruct (region_live_range r2) as [b2 l2]. clear -D SH NLpos. lia.
** pose proof (ranges_free_except_regions st _ _ _ rid2 r2 RFE H2) as D2.
destruct (region_live_range r2) as [b2 l2]. cbn [snd] in L2pos. clear -D D2 L2pos OLpos NLpos. lia.
--  apply (FIN z); [split; [exact Z0| exact ZM]| rewrite <- RUn; exact ZC| | unfold rm_L', L', QcV4.Mq0.r0; rewrite Hr0; reflexivity].
intros rid2 r2 NE2 H2. rewrite RUn in RF. pose proof (ranges_free_regions st _ _ rid2 r2 RF H2) as D.
destruct (region_live_range r2) as [b2 l2]. clear -D. lia.
+ intros z Hz. cbn [answer_ok] in Hz. rewrite (mremap_answer_ok_eq x0 st L _ _ _ _ IR) in Hz. rewrite Hz. cbn [negb]. apply rejects_bad_answer.
Qed.
End FT.

#[using="Type"] Lemma strelU_follow_some {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strelU RR t1 t2 -> forall ans r1, follow t1 ans = Some r1 -> exists r2, follow t2 ans = Some r2 /\ RR r1 r2.
Proof.
induction 1 as [r1 r2 Hr|w k1 k2|e k1 k2 Hk IH]; intros ans x H; cbn [follow] in *.
- inversion H; subst. eauto.
- discriminate.
- destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

#[using="Type"] Lemma strelU_lafter {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strelU RR t1 t2 -> forall L ans, lafter L t1 ans = lafter L t2 ans.
Proof.
induction 1 as [r1 r2 Hr|w k1 k2|e k1 k2 Hk IH]; intros L ans; cbn [lafter]; [reflexivity| reflexivity|].
destruct e; destruct ans; try reflexivity; apply IH.
Qed.

#[using="Type"] Lemma ptree_strelU {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strelU RR t1 t2 -> forall L (P1 : mled -> R1 -> Prop) (P2 : mled -> R2 -> Prop),
(forall L' r1 r2, RR r1 r2 -> P1 L' r1 -> P2 L' r2) ->
ptree L t1 P1 -> ptree L t2 P2.
Proof.
induction 1 as [r1 r2 Hr|w k1 k2|e k1 k2 Hk IH]; intros L P1 P2 HP H; cbn [ftree ptree follow sbind] in *.
- eapply HP; eauto.
- destruct H.
- destruct e; try exact H. all: destruct H as [He H]; split; [exact He|]; intros a; specialize (H a);
case_ans; [eapply IH; eauto|].
all: specialize (Hk a); destruct (rejects_inv _ H) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I.
Qed.

Section SIM.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Local Notation PRUN := (prun pans pupd).

#[using="Hpans"] Lemma realloc_body_leaf_facts st L BL LS c off n0 n m bm i ai a ar ka o ans o' st' r :
INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n -> blk_facts st c off n0 m bm i ai a ar ka ->
follow (PRUN o (realloc_body st (rl_p c off) n)) ans = Some (o', (st', r)) ->
s_secret st' = s_secret st /\ (c_init_done (s_ctx st) = 1 -> c_init_done (s_ctx st') = 1) /\ RK st st' c BL (r <> None).
Proof.
intros INV Hk Hn BF Hf. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
assert (EASY : forall stx rx, ctrl_eq st stx -> s_secret stx = s_secret st /\ (c_init_done (s_ctx st) = 1 -> c_init_done (s_ctx stx) = 1) /\ RK st stx c BL rx).
{ intros stx rx CE. split; [exact (ce_secret _ _ CE)|]. split; [rewrite (ce_ctx _ _ CE); auto|].
intros rid rr rr' H1 _ H2. left. rewrite (ce_regions _ _ CE) in H2. congruence. }
destruct (size_overflows n) eqn:SO.
{ unfold realloc_body in Hf. rewrite SO, prun_ret in Hf. cbn [follow] in Hf. inversion Hf; subst. apply EASY. apply ctrl_eq_refl. }
destruct (@realloc_hdr_unfold _ O pans pupd st c off n0 n m bm i ai a ar ka BF SO o) as [EQ RD3]. rewrite EQ in Hf. clear EQ.

assert (MOVE : forall o1 ans1, follow (PRUN o1 ('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, @None aptr) | Some q => st2 <-- free st1 (Some (rl_p c off)) ;; ret (st2, Some q) end)) ans1 = Some (o', (st', r)) ->
s_secret st' = s_secret st /\ (c_init_done (s_ctx st) = 1 -> c_init_done (s_ctx st') = 1) /\ RK st st' c BL (r <> None)).
{ clear Hf. intros o1 ans1 H. unfold prun in H. rewrite (steq_follow ans1 (eruns_sbind _ _ _ _ _)) in H. rewrite follow_sbind in H.
destruct (followk _ ans1) as [[[o2 [st1 r1]] rest]|] eqn:FK; [| discriminate].
pose proof (followk_follow _ _ FK) as FF.
destruct (malloc_sim pans pupd Hpans st L BL LS n o1 ans1 _ _ _ INV Hn FF) as (rc & _ & _ & _ & GP1 & RES).
destruct GP1 as (G1 & G2 & G3).
destruct r1 as [q|].
- destruct rc as [c'|]; [| destruct RES]. destruct RES as (off1 & LS1 & Eq & Ho1 & INV1 & NI1).
change (fun s : O * (mstate * optr) => eruns (psel pans) pupd (fst s) (let (st1, r) := snd s in
match r with Some q0 => st2 <-- free st1 (Some (rl_p c off));; ret (st2, Some q0) | None => ret (st1, None) end))
with (fun s : O * (mstate * optr) => PRUN (fst s) (let (st1, r) := snd s in
match r with Some q0 => st2 <-- free st1 (Some (rl_p c off));; ret (st2, Some q0) | None => ret (st1, None) end)) in H.
cbn [fst snd] in H. unfold prun in H. rewrite (steq_follow rest (eruns_sbind _ _ _ _ _)) in H. rewrite follow_sbind in H.
destruct (followk _ rest) as [[[o3 st2] rest2]|] eqn:FK2; [| discriminate].
change (eruns (psel pans) pupd o2 (free st1 (Some (rl_p c off)))) with (PRUN o2 (free st1 (Some (aadd c (UNIT * off))))) in FK2.
pose proof (followk_follow _ _ FK2) as FF2.
destruct (free_leaf_facts pans pupd st1 _ _ LS1 c off n0 o2 rest o3 st2 INV1 ltac:(right; exact Hk) FF2) as (SUB & SEC & IDN & _).
cbn in H. inversion H; subst.
split; [rewrite SEC; exact G2|]. split; [intros Hi1; rewrite IDN; auto|].
intros rid rr rr' H1 K1 H2. left. pose proof (SUB _ _ H2) as H3. rewrite (G1 _ _ H1 K1) in H3. congruence.
- destruct rc as [c'|]; [destruct RES|]. cbn in H. inversion H; subst.
split; [exact G2|]. split; [exact G3|]. intros rid rr rr' H1 K1 H2. left. rewrite (G1 _ _ H1 K1) in H2. congruence. }
destruct (rl_inplace st off n m) eqn:INPL.
{ unfold rr_set_size in Hf. rewrite (RD3 _ st) in Hf by reflexivity. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf; subst.
change (havoc (rl_p c off) n (set_size (rl_p c off) (rl_e st m bm i) n (rl_b3 st off n0 m i) st))
with (havoc (ip_p c off) n (set_size (ip_p c off) (rl_e st m bm i) n (ip_b3 st off n0 m i) st)).
replace (rl_e st m bm i) with (ip_e st c m).
2:{ unfold ip_e, rl_e, rl_stride. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). unfold aadd, sstart, gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn. f_equal. lia. }
rewrite (inplace_eq st c off n0 n m bm i). apply EASY. apply inplace_ctrl. }
destruct (rl_big st n m) eqn:BIG; [| exact (MOVE o ans Hf)].
unfold guard in Hf. destruct (m_sizeclass (MR st m) =? 63) eqn:E63.
2:{ unfold prun in Hf. rewrite eruns_vis_keep in Hf by reflexivity. cbn [follow] in Hf. discriminate. }
apply Z.eqb_eq in E63. cbv zeta in Hf.
destruct (rl_oldlen st m =? rl_needed off n) eqn:EQL.
{ unfold rr_set_size in Hf. rewrite (RD3 _ st) in Hf by reflexivity. rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf; subst.
change (havoc (rl_p c off) n (set_size (rl_p c off) (rl_e st m bm i) n (rl_b3 st off n0 m i) st))
with (havoc (ip_p c off) n (set_size (ip_p c off) (rl_e st m bm i) n (ip_b3 st off n0 m i) st)).
replace (rl_e st m bm i) with (ip_e st c m).
2:{ unfold ip_e, rl_e, rl_stride. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). unfold aadd, sstart, gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn. f_equal. lia. }
rewrite (inplace_eq st c off n0 n m bm i). apply EASY. apply inplace_ctrl. }
destruct (PTRDIFF_MAX <=? rl_needed off n) eqn:PDM; [exact (MOVE _ _ Hf)|].
unfold prun in Hf. rewrite eruns_vis_keep in Hf by reflexivity. destruct ans as [|z rest]; [cbn [follow] in Hf; discriminate|]. cbn [follow] in Hf.
destruct (mremap_answer_ok (live_ranges st) (conc st bm) (rl_oldlen st m) (rl_needed off n) z) eqn:OK; cbn [negb] in Hf.
2:{ unfold bad_answer in Hf. rewrite eruns_vis_keep in Hf by reflexivity. cbn [follow] in Hf. discriminate. }
destruct (is_err z) eqn:ER; [exact (MOVE _ rest Hf)|].
unfold rr_set_size in Hf.
rewrite (@rl_fin_rd3 _ st L BL LS c off n0 n m bm i ai a ar ka INV Hn BF SO _ _ _ INPL BIG E63) in Hf.
match type of Hf with context [eruns (psel pans) pupd ?oo (ret ?x)] => change (eruns (psel pans) pupd oo (ret x)) with (PRUN oo (SRet x)) in Hf end.
rewrite prun_ret in Hf. cbn [follow] in Hf. inversion Hf; subst.

change (havoc (rl_p c off) n (set_size (rl_p c off) (rl_e' off n bm) n (rl_b3 st off n0 m i) (wr8 (rl_e' off n bm) 0 (remap_region (fst bm) z (rl_needed off n) m st))))
with (havoc (aadd c (UNIT * off)) n (set_size (aadd c (UNIT * off)) (aadd bm (UNIT + (rl_needed off n - UNIT) - IB)) n (rm_b3 st off n0 m i)
(wr8 (aadd bm (UNIT + (rl_needed off n - UNIT) - IB)) 0 (remap_region (fst bm) z (rl_needed off n) m st)))).
destruct (@rl_big_facts _ st L BL LS c off n0 n m bm i ai a ar ka INV BF INPL BIG E63) as (I0 & LI0 & ML & B0 & Ecb & _ & N0 & FIT0 & ND).
pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r0 & Hr0 & K0 & ML0 & GE).
pose proof (ir_shape _ _ _ IR _ _ Hr0) as (RS1 & RS2 & RS3 & RS4 & RS5 & _).
assert (Ebase : conc st bm = r_base r0) by (unfold conc, get_region; rewrite Hr0, B0; lia).
assert (NLpos : 0 < rl_needed off n) by (unfold rl_needed, rr_needed; pose proof (round_up_ge (n + UNIT * off + UNIT + IB)); pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF); clear -H H0 Hn; unfold UNIT, IB in *; lia).
assert (NLal : rl_needed off n mod PGSZ = 0) by (unfold rl_needed, rr_needed; apply round_up_pg_mod).
assert (RUo : round_up_pg (rl_oldlen st m) = rl_oldlen st m) by (unfold rl_oldlen; rewrite ML0; apply round_up_pg_id; apply round_up_pg_mod).
assert (OLc : r_base r0 + round_up_pg (rl_oldlen st m) <= alloc_ceiling) by (rewrite RUo; unfold rl_oldlen; rewrite ML0; exact RS5).
rewrite Ebase in OK.
assert (HZ : 0 < z /\ z mod PGSZ = 0).
{ destruct (mremap_ok_facts _ _ _ _ _ OK ER OLc) as [(-> & _)|(_ & _ & Z0 & ZM & _)]; split; assumption. }
pose proof (mremap_ok_len _ _ _ _ _ OK ER OLc RS1) as NLlt.
rewrite <- (remap_eq st L BL LS c off n0 n m bm i ai a ar ka z (rl_needed off n) INV Hk BF E63 HZ (conj (conj NLpos NLlt) NLal)).
destruct (addback_ctrl (rm_st4 st m bm z (rl_needed off n)) c off n m (rm_b3 st off n0 m i)) as [CE _].
split; [| split].
- unfold rm_stf. rewrite (ce_secret _ _ CE). unfold rm_st4. apply st4_secret.
- unfold rm_stf. rewrite (ce_ctx _ _ CE). unfold rm_st4. rewrite st4_ctx. auto.
- intros rid rr rr' H1 K1 H2. destruct (N.eq_dec rid (fst bm)) as [->|NE].
+ right. split; [discriminate|]. split; [rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity|].
intros [[c2 off2] n2] Hk2 Hf2. cbn [bslot fst snd] in *.
destruct (block_facts x0 st L BL LS INV c2 off2 n2 Hk2) as (m2 & b2 & i2 & ai2 & a2 & ar2 & ka2 & BF2).
pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF2) as Ec2. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF2) as Hi2.
assert (Hm2 : hosts st b2 m2) by (exists ai2; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF2)).
assert (Hfb : fst b2 = fst bm) by (rewrite Ec2 in Hf2; exact Hf2).
pose proof (rid_only x0 st L BL LS m bm ai z (rl_needed off n) INV (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) E63 b2 m2 Hm2 Hfb) as ->.
pose proof (hosts_inj _ _ _ IM _ _ _ Hm2 (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) as ->.
rewrite Ec2, (bf_c _ _ _ _ _ _ _ _ _ _ _ BF), I0. rewrite LI0 in Hi2. replace i2 with 0 by lia. reflexivity.
+ left. pose proof (remap_regions_kept st L BL LS c off n0 n m bm i ai a ar ka z (rl_needed off n) INV Hk BF E63 rid rr H1 K1 NE) as H3. congruence.
Qed.

#[using="Hpans"] Lemma realloc_body_cases st L BL LS c off n0 n m bm i ai a ar ka o ans o' st' r :
INVL x0 st L BL LS -> TF0 st -> In ((c, off), n0) BL -> 0 <= n -> blk_facts st c off n0 m bm i ai a ar ka ->
follow (PRUN o (realloc_body st (rl_p c off) n)) ans = Some (o', (st', r)) ->
let t := crealloc (strip st) c off n in
let L' := lafter L t ans in
(r = None /\ follow t ans = Some (strip st', None) /\ exists LS', INVL x0 st' L' BL LS')
\/ (r = Some (rl_p c off) /\ follow t ans = Some (strip st', Some RRSame) /\ exists LS', INVL x0 st' L' (((c, off), n) :: bl_remove c BL) LS')
\/ (exists c' off' x, r = Some (aadd c' (UNIT * off')) /\ 0 <= off' <= 255 /\ ~ In c' (map bslot BL)
/\ follow t ans = Some (strip st', Some (RRNew (c', x))) /\ exists LS', INVL x0 st' L' (((c', off'), n) :: bl_remove c BL) LS').
Proof.
intros INV T0 Hk Hn BF Hf. cbn zeta. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2].
assert (Hm : hosts st bm m) by (exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)).
pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
destruct (size_overflows n) eqn:SO.
{ left. unfold realloc_body in Hf. rewrite SO, prun_ret in Hf. cbn [follow] in Hf. inversion Hf; subst.
unfold crealloc. rewrite s_slots_strip, (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF), SO. cbn. split; [reflexivity|]. split; [reflexivity|]. exists LS. exact INV. }
destruct (@realloc_hdr_unfold _ O pans pupd st c off n0 n m bm i ai a ar ka BF SO o) as [EQ RD3]. rewrite EQ in Hf. clear EQ.
rewrite (@crealloc_unfold _ st c off n0 n m bm i ai a ar ka BF SO). unfold rl_cbody.

assert (IPL : forall stx, follow (PRUN o (rr_set_size st (rl_p c off) (rl_e st m bm i) n (fun st1 => ret (havoc (rl_p c off) n st1, Some (rl_p c off))))) ans = Some (o', (stx, r)) ->
UNIT * off + n <= get_stride (MR st m) - IB -> get_stride (MR st m) - IB - UNIT * off - n < 2 ^ 32 ->
r = Some (rl_p c off) /\ strip stx = strip st /\ exists LS', INVL x0 stx L (((c, off), n) :: bl_remove c BL) LS').
{ intros stx H F1 F2. unfold rr_set_size in H. rewrite (RD3 _ st) in H by reflexivity. rewrite prun_ret in H. cbn [follow] in H. inversion H; subst.
split; [reflexivity|]. split; [rewrite strip_havoc, strip_set_size; reflexivity|]. exists LS.
change (havoc (rl_p c off) n (set_size (rl_p c off) (rl_e st m bm i) n (rl_b3 st off n0 m i) st))
with (havoc (ip_p c off) n (set_size (ip_p c off) (rl_e st m bm i) n (ip_b3 st off n0 m i) st)).
replace (rl_e st m bm i) with (ip_e st c m).
2:{ unfold ip_e, rl_e, rl_stride. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). unfold aadd, sstart, gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn. f_equal. lia. }
rewrite (inplace_eq st c off n0 n m bm i). apply (inplace_INVL st L BL LS c off n0 n m bm i ai a ar ka INV Hk BF (TF0_TF2 _ T0) Hn F1 F2). }

assert (MOVE : forall o1 ans1 Lx, INVL x0 st Lx BL LS ->
follow (PRUN o1 ('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, @None aptr) | Some q => st2 <-- free st1 (Some (rl_p c off)) ;; ret (st2, Some q) end)) ans1 = Some (o', (st', r)) ->
let t := rl_cgen st c n in let L' := lafter Lx t ans1 in
(r = None /\ follow t ans1 = Some (strip st', None) /\ exists LS', INVL x0 st' L' BL LS')
\/ (exists c' off' x, r = Some (aadd c' (UNIT * off')) /\ 0 <= off' <= 255 /\ ~ In c' (map bslot BL)
/\ follow t ans1 = Some (strip st', Some (RRNew (c', x))) /\ exists LS', INVL x0 st' L' (((c', off'), n) :: bl_remove c BL) LS')).
{ clear Hf. intros o1 ans1 Lx INVx H. cbn zeta. unfold rl_cgen.
unfold prun in H. rewrite (steq_follow ans1 (eruns_sbind _ _ _ _ _)) in H. rewrite follow_sbind in H.
destruct (followk _ ans1) as [[[o2 [st1 r1]] rest]|] eqn:FK; [| discriminate].
pose proof (followk_follow _ _ FK) as FF.
destruct (malloc_sim pans pupd Hpans st Lx BL LS n o1 ans1 _ _ _ INVx Hn FF) as (rc & Hfc & CPc & LIVEc & GP1 & RES).
pose proof (@malloc_control _ O pans pupd Hpans st n o1) as MC.
destruct (strel_followk MC ans1 FK) as ([cs1 rc'] & FKc & [HS1 HR1]). cbn [fst snd] in HS1, HR1. subst cs1.
pose proof (followk_follow _ _ FKc) as Hfc'. rewrite Hfc in Hfc'. inversion Hfc'. subst rc'.
rewrite follow_sbind, FKc. rewrite (lafter_sbind _ _ Lx ans1 FKc).
destruct r1 as [q|].
- destruct rc as [c'|]; [| destruct RES]. destruct RES as (off1 & LS1 & Epq & Ho1 & INV1 & NI1).
change (fun s0 : O * (mstate * optr) => eruns (psel pans) pupd (fst s0) (let (st1, r) := snd s0 in
match r with Some q0 => st2 <-- free st1 (Some (rl_p c off));; ret (st2, Some q0) | None => ret (st1, None) end))
with (fun s0 : O * (mstate * optr) => PRUN (fst s0) (let (st1, r) := snd s0 in
match r with Some q0 => st2 <-- free st1 (Some (rl_p c off));; ret (st2, Some q0) | None => ret (st1, None) end)) in H.
cbn [fst snd] in H. unfold prun in H. rewrite (steq_follow rest (eruns_sbind _ _ _ _ _)) in H. rewrite follow_sbind in H.
destruct (followk _ rest) as [[[o3 st2] rest2]|] eqn:FK2; [| discriminate].
change (eruns (psel pans) pupd o2 (free st1 (Some (rl_p c off)))) with (PRUN o2 (free st1 (Some (aadd c (UNIT * off))))) in FK2.
pose proof (followk_follow _ _ FK2) as FF2. cbn in H. inversion H; subst.
destruct (free_sim pans pupd Hpans st1 _ _ LS1 c off n0 o2 rest _ _ INV1 ltac:(right; exact Hk) FF2) as (Hff & CPf & LIVEf & LSf & INVf).
right. exists c', off1, (fresh_off (strip st1) c' n). split; [reflexivity|]. split; [exact Ho1|]. split; [exact NI1|].
pose proof (free_control pans pupd st1 (aadd c (UNIT * off)) c o2 (INVL_hdr_ok pans pupd st1 _ _ LS1 c off n0 INV1 ltac:(right; exact Hk))) as FC.
destruct (strel_followk FC rest FK2) as (cs2 & FKc2 & HS2). unfold FREL in HS2. cbn [snd] in HS2. subst cs2.
rewrite follow_sbind, FKc2. cbn. split; [reflexivity|].
rewrite (lafter_sbind _ _ _ rest FKc2). cbn [lafter]. exists LSf.
cbn [bl_remove bslot fst] in INVf. rewrite (aptr_eqb_neq c' c) in INVf; [exact INVf|].
intros ->. apply NI1. change c with (bslot ((c, off), n0)). apply in_map. exact Hk.
- destruct rc as [c'|]; [destruct RES|]. cbn in H. inversion H; subst. left. split; [reflexivity|]. split; [cbn; reflexivity|].
cbn [lafter]. exact RES. }
destruct (rl_inplace st off n m) eqn:INPL.
{ unfold rl_inplace in INPL. apply andb_prop in INPL as [INPL C3]. apply andb_prop in INPL as [C1 C2].
apply Z.leb_le in C1. apply Z.ltb_lt in C2. apply Z.leb_le in C3.
pose proof (size_to_class_ok n ltac:(lia)) as [SC _].
assert (SC48 : m_sizeclass (MR st m) < 48) by (destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|[E _]]; [lia| rewrite E in C3; lia]).
pose proof (small_stride x0 st L BL LS bm m INV Hm SC48) as SS.
destruct (IPL st' Hf ltac:(unfold rl_stride in *; clear -C1 OFF Hn; unfold UNIT, IB in *; lia) ltac:(unfold rl_stride in *; clear -C1 SS OFF Hn; unfold UNIT, IB in *; lia)) as (-> & Es & INV').
right; left. cbn. rewrite Es. auto. }
destruct (rl_big st n m) eqn:BIG; [| destruct (MOVE o ans L INV Hf) as [A|A]; [left; exact A| right; right; exact A]].
unfold guard in Hf |- *. destruct (m_sizeclass (MR st m) =? 63) eqn:E63.
2:{ unfold prun in Hf. rewrite eruns_vis_keep in Hf by reflexivity. cbn [follow] in Hf. discriminate. }
apply Z.eqb_eq in E63.
destruct (@rl_big_facts _ st L BL LS c off n0 n m bm i ai a ar ka INV BF INPL BIG E63) as (I0 & LI0 & ML & B0 & Ecb & _ & N0 & FIT0 & ND).
assert (STR : get_stride (MR st m) = m_maplen (MR st m) * 4096 - UNIT).
{ unfold get_stride. rewrite LI0. replace (m_maplen (MR st m) =? 0) with false by (symmetry; apply Z.eqb_neq; exact ML). reflexivity. }
cbv zeta in Hf.
destruct (rl_oldlen st m =? rl_needed off n) eqn:EQL.
{ apply Z.eqb_eq in EQL. unfold rl_oldlen in EQL.
destruct (IPL st' Hf) as (-> & Es & INV').
- rewrite STR, EQL. clear -ND N0 OFF Hn. unfold UNIT, IB in *. lia.
- rewrite STR, EQL. unfold rl_needed, rr_needed. pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [[_ U] _]. clear -U OFF Hn N0. unfold UNIT, IB in *. lia.
- right; left. cbn. rewrite Es. auto. }
destruct (PTRDIFF_MAX <=? rl_needed off n) eqn:PDM; [destruct (MOVE o ans L INV Hf) as [A|A]; [left; exact A| right; right; exact A]|].
unfold prun in Hf. rewrite eruns_vis_keep in Hf by reflexivity. destruct ans as [|z rest]; [cbn [follow] in Hf; discriminate|]. cbn [follow] in Hf. cbn [follow lafter].
destruct (mremap_answer_ok (live_ranges st) (conc st bm) (rl_oldlen st m) (rl_needed off n) z) eqn:OK; cbn [negb] in Hf |- *.
2:{ unfold bad_answer in Hf. rewrite eruns_vis_keep in Hf by reflexivity. cbn [follow] in Hf. discriminate. }
destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r0 & Hr0 & K0 & ML0 & GE).
pose proof (ir_shape _ _ _ IR _ _ Hr0) as (RS1 & RS2 & RS3 & RS4 & RS5 & _).
assert (Ebase : conc st bm = r_base r0) by (unfold conc, get_region; rewrite Hr0, B0; lia).
assert (NLpos : 0 < rl_needed off n) by (unfold rl_needed, rr_needed; pose proof (round_up_ge (n + UNIT * off + UNIT + IB)); clear -H OFF Hn; unfold UNIT, IB in *; lia).
assert (NLal : rl_needed off n mod PGSZ = 0) by (unfold rl_needed, rr_needed; apply round_up_pg_mod).
assert (RUo : round_up_pg (rl_oldlen st m) = rl_oldlen st m) by (unfold rl_oldlen; rewrite ML0; apply round_up_pg_id; apply round_up_pg_mod).
assert (OLc : r_base r0 + round_up_pg (rl_oldlen st m) <= alloc_ceiling) by (rewrite RUo; unfold rl_oldlen; rewrite ML0; exact RS5).
rewrite Ebase in OK.
destruct (is_err z) eqn:ER.
{ assert (EP : event_post L (EMremap (r_base r0) (rl_oldlen st m) (rl_needed off n) MREMAP_MAYMOVE) z = L).
{ cbn. rewrite (mremap_err_errno _ _ _ _ _ OK ER OLc ltac:(unfold rl_oldlen; pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF); clear -H ML; lia) ltac:(clear -NLpos; lia)). reflexivity. }
rewrite Ebase, EP. destruct (MOVE _ rest L INV Hf) as [A|A]; [left; exact A| right; right; exact A]. }
unfold rr_set_size in Hf.
rewrite (@rl_fin_rd3 _ st L BL LS c off n0 n m bm i ai a ar ka INV Hn BF SO _ _ _ INPL BIG E63) in Hf.
match type of Hf with context [eruns (psel pans) pupd ?oo (ret ?x)] => change (eruns (psel pans) pupd oo (ret x)) with (PRUN oo (SRet x)) in Hf end.
rewrite prun_ret in Hf. cbn [follow] in Hf. clear MOVE IPL. inversion Hf. subst o' st' r.
right; left. split; [reflexivity|].
change (havoc (rl_p c off) n (set_size (rl_p c off) (rl_e' off n bm) n (rl_b3 st off n0 m i) (wr8 (rl_e' off n bm) 0 (remap_region (fst bm) z (rl_needed off n) m st))))
with (havoc (aadd c (UNIT * off)) n (set_size (aadd c (UNIT * off)) (aadd bm (UNIT + (rl_needed off n - UNIT) - IB)) n (rm_b3 st off n0 m i)
(wr8 (aadd bm (UNIT + (rl_needed off n - UNIT) - IB)) 0 (remap_region (fst bm) z (rl_needed off n) m st)))).
assert (HZ : 0 < z /\ z mod PGSZ = 0).
{ destruct (mremap_ok_facts _ _ _ _ _ OK ER OLc) as [(-> & _)|(_ & _ & Z0 & ZM & _)]; split; assumption. }
pose proof (mremap_ok_len _ _ _ _ _ OK ER OLc RS1) as NLlt.
split.
- cbn. rewrite strip_havoc, strip_set_size, strip_wr8, <- QcV4.Mq0.strip_remap_region. reflexivity.
- rewrite <- (remap_eq st L BL LS c off n0 n m bm i ai a ar ka z (rl_needed off n) INV Hk BF E63 HZ (conj (conj NLpos NLlt) NLal)).
assert (NEF : is_errno_form z = false).
{ unfold is_errno_form. unfold is_err in ER. apply Z.ltb_ge in ER. apply Bool.andb_false_iff. left. apply Z.leb_gt. clear -ER. unfold TWO64 in *. lia. }
cbn [lafter event_post]. rewrite NEF, Ebase.
assert (RUn : round_up_pg (rl_needed off n) = rl_needed off n) by (apply round_up_pg_id; exact NLal).
assert (EL : Qfya.set_groups ((z, rl_needed off n) :: g_remove (r_base r0) (ld_groups L)) L = rm_L' st L bm z (rl_needed off n)).
{ unfold rm_L', L', QcV4.Mq0.r0. rewrite Hr0. reflexivity. }
rewrite EL. eexists.
apply (remap_INVL st L BL LS c off n0 n m bm i ai a ar ka z (rl_needed off n) INV Hk BF T0 Hn E63 HZ (conj (conj NLpos NLlt) NLal)).
+ destruct (mremap_ok_facts _ _ _ _ _ OK ER OLc) as [(-> & CASES)|(NEz & GROW & Z0 & ZM & ZC & RF)].
* rewrite RUn, RUo in CASES. destruct CASES as [SH|[GR _]]; [clear -SH OLc RUo; rewrite RUo in OLc; lia| exact GR].
* rewrite <- RUn. exact ZC.
+ intros rid2 r2 NE2 H2.
assert (OLpos : 0 < rl_oldlen st m) by (unfold rl_oldlen; pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF); clear -ML H; lia).
destruct (mremap_ok_facts _ _ _ _ _ OK ER OLc) as [(Ez & CASES)|(NEz & GROW & Z0 & ZM & ZC & RF)].
* subst z. pose proof (ir_disj _ _ _ IR (fst bm) rid2 r0 r2 Hr0 H2 ltac:(congruence)) as D.
unfold region_live_range in D at 1. rewrite K0, <- ML0 in D. fold (rl_oldlen st m) in D.
rewrite RUn, RUo in CASES.
assert (L2pos : 0 < snd (region_live_range r2)).
{ pose proof (ir_shape _ _ _ IR _ _ H2) as (T1 & _ & T3 & _ & _ & T6). pose proof (round_up_ge (r_len r2)) as T4.
unfold region_live_range. destruct (r_kind r2) eqn:EK; cbn [snd]; [| clear -T3 T4; lia| clear -T3 T4; lia].
destruct (T6 ltac:(left; exact EK)) as [_ T7]. clear -T4 T7. unfold PGSZ in *. lia. }
destruct CASES as [SH|[_ RFE]].
-- destruct (region_live_range r2) as [b2 l2]. clear -D SH NLpos. lia.
-- pose proof (ranges_free_except_regions st _ _ _ rid2 r2 RFE H2) as D2.
destruct (region_live_range r2) as [b2 l2]. cbn [snd] in L2pos. clear -D D2 L2pos OLpos NLpos. lia.
* rewrite RUn in RF. pose proof (ranges_free_regions st _ _ rid2 r2 RF H2) as D.
destruct (region_live_range r2) as [b2 l2]. clear -D. lia.
+ exact ND.
+ unfold rl_needed, rr_needed. pose proof (round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [[_ U] _]. clear -U OFF Hn N0. unfold UNIT, IB in *. lia.
Qed.

#[using="Hpans"] Theorem realloc_sim st L BL LS c off n0 n o ans o' st' r :
INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n ->
follow (PRUN o (realloc st (Some (aadd c (UNIT * off))) n)) ans = Some (o', (st', r)) ->
let t := crealloc (strip st) c off n in
let L' := lafter L t ans in
exists rw, follow t ans = Some (strip st', rw) /\ cpath L t L' (strip st', rw) /\ ld_live L' = ld_live L
/\ s_secret st' = s_secret st /\ (c_init_done (s_ctx st) = 1 -> c_init_done (s_ctx st') = 1) /\ RK st st' c BL (r <> None)
/\ match r, rw with
| None, None => exists LS', INVL x0 st' L' BL LS'
| Some p', Some RRSame => p' = aadd c (UNIT * off) /\ exists LS', INVL x0 st' L' (((c, off), n) :: bl_remove c BL) LS'
| Some p', Some (RRNew b') => exists off' LS', p' = aadd (fst b') (UNIT * off') /\ 0 <= off' <= 255
/\ INVL x0 st' L' (((fst b', off'), n) :: bl_remove c BL) LS' /\ ~ In (fst b') (map bslot BL)
| _, _ => False
end.
Proof.
intros INV Hk Hn Hf. cbn zeta.
set (st0 := set_tick (N.succ (s_tick st)) st) in *.
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (T0 : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
assert (Es : strip st0 = strip st) by (apply strip_set_tick).
unfold realloc in Hf. fold st0 in Hf.
destruct (block_facts x0 st0 L BL LS INV0 c off n0 Hk) as (m & bm & i & ai & a & ar & ka & BF).
change (aadd c (UNIT * off)) with (rl_p c off) in Hf |- *.

pose proof (@realloc_body_control _ O pans pupd Hpans st0 L BL LS c off n0 n o INV0 Hk Hn) as REL. rewrite Es in REL.
destruct (strelU_follow_some _ _ _ REL ans _ Hf) as ([cs' rw] & Hf2 & [HS HR]). cbn [fst snd] in HS, HR. subst cs'.
exists rw. split; [exact Hf2|].

pose proof (ftree_prun pans pupd Hpans _ L _ o (realloc_body_INVL st0 L BL LS c off n0 n m bm i ai a ar ka INV0 T0 Hk Hn BF)) as PT.
pose proof (ptree_strelU _ _ _ REL L _ (fun _ _ => True) ltac:(intros; exact I) PT) as PT2.
destruct (ptree_follow_lafter _ L _ ans PT2 Hf2) as [CP _].
split; [exact CP|]. split; [exact (cpath_live CP)|].
destruct (realloc_body_leaf_facts st0 L BL LS c off n0 n m bm i ai a ar ka o ans o' st' r INV0 Hk Hn BF Hf) as (SEC & IDN & RKf).
split; [exact SEC|]. split; [exact IDN|]. split; [exact RKf|].
destruct (realloc_body_cases st0 L BL LS c off n0 n m bm i ai a ar ka o ans o' st' r INV0 T0 Hk Hn BF Hf)
as [(-> & F2 & POST)|[(-> & F2 & POST)|(c' & off' & x & -> & Ho & NI & F2 & POST)]]; rewrite Es in F2; rewrite F2 in Hf2; inversion Hf2; subst rw.
- exact POST.
- split; [reflexivity| exact POST].
- cbn [fst]. exists off'. destruct POST as [LS' INV']. exists LS'. auto.
Qed.

End SIM.

Section AREACH_STEP.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Local Notation PRUN := (prun pans pupd).

Local Notation ablock := ((cptr * Z) * Z * Z)%type.
Definition ab_slot (b : ablock) : cptr := fst (fst (fst b)).
Definition ab_addr (b : ablock) : Z := snd (fst b).
Definition ab_size (b : ablock) : Z := snd b.
Definition acorr1 (st : mstate) (b : ablock) (k : blk) : Prop :=
ab_slot b = bslot k /\ ab_size b = bsize k /\ ab_addr b = conc st (bslot k) + UNIT * boff k.

#[using="Type"] Lemma rs_blk_region X st L BL LS k : INVL X st L BL LS -> In k BL ->
exists r, s_regions st !! fst (bslot k) = Some r /\ r_kind r = RKGroup.
Proof.
intros INV Hk. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Es).
rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. rewrite Es. cbn [fst].
destruct Hb as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb).
Qed.
#[using="Type"] Lemma rs_conc_aadd st p d : (exists r, s_regions st !! fst p = Some r) -> conc st (aadd p d) = conc st p + d.
Proof. intros [r Hr]. unfold conc, get_region, aadd. cbn. rewrite Hr. lia. Qed.
#[using="Type"] Lemma rs_event_post_resv L e z : ld_resv (event_post L e z) = ld_resv L.
Proof.
destruct e as [rq|a len prot flags|a len|a len prot|p c h|w|ma ol nl fl]; cbn; try reflexivity.
4:{ destruct (is_errno_form z); reflexivity. }
- destruct (rq =? 0); [reflexivity|]. destruct (z =? rq); [| reflexivity]. destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[b l]|]; reflexivity.
- destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err z); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
- destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); reflexivity.
Qed.
#[using="Type"] Lemma rs_cpath_resv {R} L (t : M R) L' r : cpath L t L' r -> ld_resv L' = ld_resv L.
Proof. induction 1; [reflexivity|]. rewrite IHcpath. apply rs_event_post_resv. Qed.
#[using="Type"] Lemma rs_Forall2_In_l {A B} (P : A -> B -> Prop) l1 l2 a : Forall2 P l1 l2 -> In a l1 -> exists b, In b l2 /\ P a b.
Proof.
induction 1 as [|x y l1' l2' Hxy H IH]; intros Hin; [destruct Hin|].
destruct Hin as [<-|Hin]; [exists y; split; [left; reflexivity| exact Hxy]|].
destruct (IH Hin) as (b & Hb & Pb). exists b. split; [right; exact Hb| exact Pb].
Qed.
#[using="Type"] Lemma rs_Forall2_impl_in {A B} (P Q : A -> B -> Prop) l1 l2 :
Forall2 P l1 l2 -> (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 Q l1 l2.
Proof.
induction 1 as [|x y l1' l2' Hxy H IH]; intros HPQ; constructor.
- apply HPQ; [left; reflexivity| left; reflexivity| exact Hxy].
- apply IH. intros a b Ha Hb. apply HPQ; right; assumption.
Qed.
#[using="Type"] Lemma rs_Forall2_filter {A B} (P : A -> B -> Prop) (p : A -> bool) (q : B -> bool) l1 l2 :
Forall2 P l1 l2 -> (forall a b, P a b -> p a = q b) -> Forall2 P (filter p l1) (filter q l2).
Proof.
induction 1 as [|x y l1' l2' Hxy H IH]; intros E; cbn; [constructor|].
rewrite (E _ _ Hxy). destruct (q y); [constructor; [exact Hxy| apply IH; exact E]| apply IH; exact E].
Qed.
#[using="Type"] Lemma rs_filter_id {A} (p : A -> bool) l : (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
induction l as [|x l IH]; intros H; cbn; [reflexivity|].
rewrite (H x ltac:(left; reflexivity)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.
#[using="Type"] Lemma rs_bl_remove_filter c BL : NoDup (map bslot BL) ->
bl_remove c BL = filter (fun k => negb (aptr_eqb (bslot k) c)) BL.
Proof.
induction BL as [|k BL IH]; intros ND; cbn; [reflexivity|].
cbn in ND. apply NoDup_cons in ND as [NI ND].
destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; cbn.
- symmetry. apply rs_filter_id. intros y Hy. destruct (aptr_eqb_spec (bslot y) c) as [E'|NE']; [| reflexivity].
exfalso. apply NI. apply list_elem_of_In. rewrite E, <- E'. apply in_map. exact Hy.
- f_equal. apply IH. exact ND.
Qed.

#[using="Type"] Lemma rs_In_bl_remove BL k c : NoDup (map bslot BL) -> In k (bl_remove c BL) -> In k BL /\ bslot k <> c.
Proof.
intros ND. rewrite (rs_bl_remove_filter c BL ND). induction BL as [|k0 BL' IH]; cbn; [tauto|].
cbn in ND. apply NoDup_cons in ND as [NI ND]. specialize (IH ND).
destruct (aptr_eqb_spec (bslot k0) c) as [E|NE]; cbn.
- intros H. destruct (IH H) as [A B]. auto.
- intros [<-|H]; [split; [left; reflexivity| exact NE]|]. destruct (IH H) as [A B]. auto.
Qed.

#[using="Hpans"] Theorem realloc_areach_step (resv : list (Z * Z)) {sec : Z} st (LB : list ablock) (b : ablock) off n o o' ans st' (r : optr) cst (rw : option rr_where) :
(exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = sec /\ Forall2 (acorr1 st) LB BL) ->
In b LB -> 0 <= off -> 0 <= n ->
ab_addr b = conc st (ab_slot b) + UNIT * off ->
follow (PRUN o (realloc st (Some (aadd (ab_slot b) (UNIT * off))) n)) ans = Some (o', (st', r)) ->
follow (crealloc (strip st) (ab_slot b) off n) ans = Some (cst, rw) ->
let LB' : list ablock :=
match r, rw with
| Some pf, Some RRSame => ((ab_slot b, off), conc st' pf, n) :: filter (fun b' => negb (aptr_eqb (ab_slot b') (ab_slot b))) LB
| Some pf, Some (RRNew b') => (b', conc st' pf, n) :: filter (fun b' => negb (aptr_eqb (ab_slot b') (ab_slot b))) LB
| _, _ => LB
end in
exists L' LS' BL', INVL x0 st' L' BL' LS' /\ ld_live L' = map bslot BL' /\ ld_resv L' = resv /\ s_secret st' = sec /\ Forall2 (acorr1 st') LB' BL'.
Proof.
intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) Hb Hoff Hn Haddr FF FC. cbn zeta.
destruct (rs_Forall2_In_l _ _ _ _ CR Hb) as ([[c bo] n0] & Hk & (C1 & C2 & C3)). unfold ab_slot, ab_size, ab_addr in C1, C2, C3. cbn [bslot boff bsize fst snd] in C1, C2, C3.
assert (Eoff : bo = off).
{ unfold ab_addr, ab_slot in Haddr. rewrite C1 in Haddr. rewrite Haddr in C3. unfold UNIT in C3. lia. }
subst bo. unfold ab_slot in *. rewrite C1 in *.
destruct (realloc_sim pans pupd Hpans st L BL LS c off n0 n o ans o' st' r INV Hk Hn FF) as (rw0 & Hf2 & CP & LIVE' & SEC' & IDN & RKf & RES).
rewrite FC in Hf2. inversion Hf2. subst cst rw0.
set (L' := lafter L (crealloc (strip st) c off n) ans) in *.
pose proof (rs_cpath_resv _ _ _ _ CP) as RESV'.
pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) as ND.

assert (KEEP : forall BL' LS' k, INVL x0 st' L' BL' LS' -> In k BL -> In k BL' -> bslot k <> c -> conc st' (bslot k) = conc st (bslot k)).
{ intros BL' LS' k INV' HkB HkB' NE.
destruct (rs_blk_region _ _ _ _ _ k INV HkB) as (rr & Hr & Kr). destruct (rs_blk_region _ _ _ _ _ k INV' HkB') as (rr' & Hr' & _).
unfold conc, get_region. rewrite Hr, Hr'.
destruct (RKf _ _ _ Hr Kr Hr') as [->|(_ & E & ONLY)]; [reflexivity|]. exfalso. apply NE. apply ONLY; [exact HkB| reflexivity]. }
assert (CRf : forall BL' LS', INVL x0 st' L' BL' LS' -> (forall k, In k (bl_remove c BL) -> In k BL') ->
Forall2 (acorr1 st') (filter (fun b' => negb (aptr_eqb (ab_slot b') c)) LB) (bl_remove c BL)).
{ intros BL' LS' INV' SUB. rewrite (rs_bl_remove_filter c BL ND).
pose proof (rs_Forall2_filter (acorr1 st) (fun b' : ablock => negb (aptr_eqb (ab_slot b') c)) (fun k0 : blk => negb (aptr_eqb (bslot k0) c)) LB BL CR
ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
eapply rs_Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
rewrite <- (rs_bl_remove_filter c BL ND) in Hk'. destruct (rs_In_bl_remove BL k' c ND Hk') as [HkB NE].
rewrite (KEEP BL' LS' k' INV' HkB (SUB _ Hk') NE). reflexivity. }
destruct r as [pf|]; destruct rw as [[|b']|]; try (exfalso; exact RES).
-  destruct RES as (-> & LS' & INV').
exists (set_live (map bslot (((c, off), n) :: bl_remove c BL)) L'), LS', (((c, off), n) :: bl_remove c BL).
split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite RESV'; exact RESV|]. split; [rewrite SEC'; exact SEC|].
constructor.
+ split; [reflexivity|]. split; [reflexivity|]. unfold ab_addr. cbn [fst snd bslot boff]. apply rs_conc_aadd.
destruct (rs_blk_region _ _ _ _ _ ((c, off), n) INV' ltac:(left; reflexivity)) as (rr & Hr & _). exists rr. exact Hr.
+ apply (CRf _ LS' INV'). intros k Hk'. right. exact Hk'.
-  destruct RES as (off' & LS' & -> & Ho' & INV' & NI).
exists (set_live (map bslot (((fst b', off'), n) :: bl_remove c BL)) L'), LS', (((fst b', off'), n) :: bl_remove c BL).
split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite RESV'; exact RESV|]. split; [rewrite SEC'; exact SEC|].
constructor.
+ split; [reflexivity|]. split; [reflexivity|]. unfold ab_addr. cbn [fst snd bslot boff]. apply rs_conc_aadd.
destruct (rs_blk_region _ _ _ _ _ ((fst b', off'), n) INV' ltac:(left; reflexivity)) as (rr & Hr & _). exists rr. exact Hr.
+ apply (CRf _ LS' INV'). intros k Hk'. right. exact Hk'.
-  destruct RES as [LS' INV'].
exists (set_live (map bslot BL) L'), LS', BL.
split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [cbn; rewrite RESV'; exact RESV|]. split; [rewrite SEC'; exact SEC|].
eapply rs_Forall2_impl_in; [exact CR|]. intros b0 k0 Hb0 Hk0 (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
destruct (rs_blk_region _ _ _ _ _ k0 INV Hk0) as (rr & Hr & Kr). destruct (rs_blk_region _ _ _ _ _ k0 INV' Hk0) as (rr' & Hr' & _).
unfold conc, get_region. rewrite Hr, Hr'. destruct (RKf _ _ _ Hr Kr Hr') as [->|(X & _)]; [reflexivity| exfalso; apply X; reflexivity].
Qed.

End AREACH_STEP.

#[using="Type"] Lemma strelU_follow_some_r {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
strelU RR t1 t2 -> forall ans r2, follow t2 ans = Some r2 -> exists r1, follow t1 ans = Some r1 /\ RR r1 r2.
Proof.
induction 1 as [r1 r2 Hr|w k1 k2|e k1 k2 Hk IH]; intros ans x H; cbn [follow] in *.
- inversion H; subst. eauto.
- discriminate.
- destruct e; try discriminate; destruct ans as [|a ans']; try discriminate; eapply IH; exact H.
Qed.

Definition RCPOST (BL : list blk) (L' : mled) (r : mstate * option rr_where) : Prop :=
match snd r with Some (RRNew b') => ~ In (fst b') (map bslot BL) /\ ld_live L' = ld_live L' | _ => True end.

#[using="Type"] Theorem crealloc_ctree st L BL LS c off n0 n :
INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n ->
ctree_ok L (crealloc (strip st) c off n) (fun L' r => match snd r with Some (RRNew b') => ~ In (fst b') (map bslot BL) | _ => True end).
Proof.
intros INV Hk Hn.
set (st0 := set_tick (N.succ (s_tick st)) st).
assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
assert (T0 : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
assert (Es : strip st0 = strip st) by (apply strip_set_tick).
destruct (block_facts x0 st0 L BL LS INV0 c off n0 Hk) as (m & bm & i & ai & a & ar & ka & BF).
pose proof (@realloc_body_control _ unit pans0 pupd0 pans0_range st0 L BL LS c off n0 n tt INV0 Hk Hn) as REL. rewrite Es in REL.
apply (ctree_ok_paths _ L (fun _ _ => True)).
- apply ptree_ctree_ok. eapply (ptree_strelU _ _ _ REL); [intros; exact I|].
eapply ptree_mono; [intros; exact I|].
exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (realloc_body_INVL st0 L BL LS c off n0 n m bm i ai a ar ka INV0 T0 Hk Hn BF)).
- intros L' [cs' rw] CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
destruct (strelU_follow_some_r _ _ _ REL ans _ Hf) as ([o' [st' r]] & Hf1 & [HS HR]). cbn [fst snd] in HS, HR.
destruct (realloc_body_cases pans0 pupd0 pans0_range st0 L BL LS c off n0 n m bm i ai a ar ka tt ans o' st' r INV0 T0 Hk Hn BF Hf1)
as [(-> & F2 & _)|[(-> & F2 & _)|(c' & off' & x & -> & Ho & NI & F2 & _)]]; rewrite Es in F2; rewrite F2 in Hf; inversion Hf; subst; cbn; auto.
Qed.

#[using="Type"] Theorem crealloc_leaf_INVL st L BL LS c off n0 n L' cs' rw :
INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n ->
cpath L (crealloc (strip st) c off n) L' (cs', rw) ->
ld_live L' = ld_live L /\
exists st' LS', strip st' = cs' /\
match rw with
| None => INVL x0 st' L' BL LS'
| Some RRSame => INVL x0 st' L' (((c, off), n) :: bl_remove c BL) LS'
| Some (RRNew b') => exists off', INVL x0 st' L' (((fst b', off'), n) :: bl_remove c BL) LS' /\ ~ In (fst b') (map bslot BL)
end.
Proof.
intros INV Hk Hn CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
pose proof (@realloc_control _ unit pans0 pupd0 pans0_range st L BL LS c off n0 n tt INV Hk Hn) as REL.
destruct (strelU_follow_some_r _ _ _ REL ans _ Hf) as ([o' [st' r]] & Hf1 & [HS HR]). cbn [fst snd] in HS, HR.
destruct (realloc_sim pans0 pupd0 pans0_range st L BL LS c off n0 n tt ans o' st' r INV Hk Hn Hf1) as (rw0 & Hf2 & _ & LIVE' & _ & _ & _ & RES).
rewrite Hf in Hf2. inversion Hf2. subst cs' rw0. rewrite HL in LIVE', RES. split; [exact LIVE'|].
exists st'. destruct r as [p'|]; destruct rw as [[|b']|]; try (exfalso; exact RES).
- destruct RES as [_ [LS' INV']]. exists LS'. auto.
- destruct RES as (off' & LS' & _ & _ & INV' & NI). exists LS'. split; [reflexivity|]. exists off'. auto.
- destruct RES as [LS' INV']. exists LS'. auto.
Qed.

End RC__1.
