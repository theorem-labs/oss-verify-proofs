(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2j.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable segs : list Segment.
Lemma st_ok_parts : forall E ss ms,
st_ok segs E ss ms ->
regs_ok E (ss_regs ss) (ms_regs ms) /\ mem_ok segs E (ms_mem ms) (ss_mem ss) /\ facts_ok E (ss_facts ss).
Proof. intros E ss ms (_ & _ & _ & _ & _ & _ & H7 & H8 & H9). auto. Qed.
Lemma st_ok_rebuild : forall E E' ss ms sr rs G,
st_ok segs E ss ms -> ss_resv ss = None ->
regs_ok E' sr (ms_regs ms) -> mem_ok segs E' (ms_mem ms) rs -> facts_ok E' G ->
st_ok segs E' (mkSS (ss_pc ss) sr rs None G) ms.
Proof.
intros E E' ss ms sr rs G (H1 & H2 & H3 & H4 & H5 & H6 & _) Hrv HR HM HG.
unfold st_ok; cbn. rewrite Hrv in H4. cbn in H4. repeat (split; [assumption|]). auto.
Qed.
Lemma st_ok_add_region : forall E ss ms r,
st_ok segs E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r ->
Forall (extent_disjoint E r) (ss_mem ss) ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hwfr Hr Hd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [cbn; rewrite Hwfr, Hwf; reflexivity|]. split; [constructor; assumption|].
split; [|exact Hpd]. clear -Hd. induction Hd; cbn; auto.
Qed.
Lemma sv_atoms_lt_mono : forall k k' v, (k <= k')%nat -> sv_atoms_lt k v = true -> sv_atoms_lt k' v = true.
Proof.
intros k k' v Hle. induction v; cbn; intros H; try reflexivity;
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end;
try (rewrite IHv1, IHv2, IHv3 by assumption; reflexivity);
try (rewrite IHv1, IHv2 by assumption; reflexivity); try (apply IHv; assumption).
apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
Lemma forallb_mono {A} (f g : A -> bool) (l : list A) :
(forall x, f x = true -> g x = true) -> forallb f l = true -> forallb g l = true.
Proof. intros Hfg H. apply forallb_forall. intros x Hx. apply Hfg. exact (proj1 (forallb_forall _ _) H x Hx). Qed.
Lemma regs_atoms_lt_mono : forall k k' sr, (k <= k')%nat -> regs_atoms_lt k sr = true -> regs_atoms_lt k' sr = true.
Proof. intros k k' sr Hle. unfold regs_atoms_lt. apply forallb_mono. intros x. apply sv_atoms_lt_mono. exact Hle. Qed.
Lemma mem_atoms_lt_mono : forall k k' rs, (k <= k')%nat -> mem_atoms_lt k rs = true -> mem_atoms_lt k' rs = true.
Proof.
intros k k' rs Hle. unfold mem_atoms_lt. apply forallb_mono. intros r H. unfold region_atoms_lt in *.
apply andb_prop in H as [H1 H2]. apply andb_true_intro. split.
- destruct (r_base r); cbn in *; [|reflexivity]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt. lia.
- revert H2. apply forallb_mono. intros c. destruct (c_val c); cbn; auto. apply sv_atoms_lt_mono. exact Hle.
Qed.
Lemma facts_atoms_lt_mono : forall k k' G, (k <= k')%nat -> facts_atoms_lt k G = true -> facts_atoms_lt k' G = true.
Proof.
intros k k' G Hle H. unfold facts_atoms_lt in *. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply andb_true_intro. split; [apply andb_true_intro; split|].
- revert H1. apply forallb_mono. intros x Hx. apply Nat.ltb_lt in Hx. apply Nat.ltb_lt. lia.
- revert H2. apply forallb_mono. intros c Hc. unfold cond_atoms_lt in *. apply andb_prop in Hc as [Ha Hb].
rewrite !(sv_atoms_lt_mono k k') by assumption. reflexivity.
- revert H3. apply forallb_mono. intros p Hp. apply andb_prop in Hp as [Ha Hb]. rewrite !(sv_atoms_lt_mono k k') by assumption. reflexivity.
Qed.
Lemma ss_atoms_lt_mono : forall k k' ss, (k <= k')%nat -> ss_atoms_lt k ss = true -> ss_atoms_lt k' ss = true.
Proof.
intros k k' ss Hle H. unfold ss_atoms_lt in *.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
rewrite (regs_atoms_lt_mono k k'), (mem_atoms_lt_mono k k'), (facts_atoms_lt_mono k k') by assumption.
destruct (ss_resv ss); [rewrite (sv_atoms_lt_mono k k') by assumption|]; reflexivity.
Qed.
Lemma sr_upd_atoms : forall k sr i v,
forallb (sv_atoms_lt k) sr = true -> sv_atoms_lt k v = true -> forallb (sv_atoms_lt k) (sr_upd sr i v) = true.
Proof.
intros k sr i v. revert sr. induction i as [|i IH]; intros sr Hsr Hv; cbn.
- destruct sr; cbn in *; [rewrite Hv; reflexivity|]. apply andb_prop in Hsr as [_ H]. rewrite Hv, H. reflexivity.
- destruct sr; cbn in *.
+ apply IH; [reflexivity | exact Hv].
+ apply andb_prop in Hsr as [H1 H2]. rewrite H1. cbn. apply IH; assumption.
Qed.
Lemma regs_atoms_lt_set : forall k sr r v,
regs_atoms_lt k sr = true -> sv_atoms_lt k v = true -> regs_atoms_lt k (sr_set sr r v) = true.
Proof.
intros k sr r v Hsr Hv. unfold regs_atoms_lt, sr_set in *. destruct (bv_eqb r 0); [exact Hsr|].
apply sr_upd_atoms; assumption.
Qed.
Fixpoint junk_regs (rs : list reg) (n : nat) (ss : sstate) : sstate :=
match rs with
| [] => ss
| r :: rs' => junk_regs rs' (S n) (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss))
end.
Lemma junk_regs_ok : forall rs n E ss ms,
st_ok segs E ss ms -> ss_atoms_lt n ss = true -> forallb (fun r : reg => negb (bv_eqb r 0)) rs = true ->
exists E', env_agree n E E' /\ st_ok segs E' (junk_regs rs n ss) ms.
Proof.
induction rs as [|r rs IH]; intros n E ss ms HS Hat Hrs; cbn.
- exists E. split; [apply env_agree_refl | exact HS].
- cbn in Hrs. apply andb_prop in Hrs as [Hr Hrs]. apply negb_true_iff in Hr.
pose proof (st_ok_abstract_reg segs n E ss ms r HS Hat Hr) as HS1.
destruct (IH (S n) _ _ ms HS1) as (E' & HA & HS').
+ unfold ss_atoms_lt in Hat |- *. cbn [ss_regs ss_mem ss_facts ss_resv].
apply andb_prop in Hat as [Hat H4]. apply andb_prop in Hat as [Hat H3]. apply andb_prop in Hat as [H1 H2].
rewrite (mem_atoms_lt_mono n (S n) _ ltac:(lia) H2). rewrite (facts_atoms_lt_mono n (S n) _ ltac:(lia) H3).
rewrite regs_atoms_lt_set; [| apply (regs_atoms_lt_mono n (S n)); [lia | assumption] | cbn; apply Nat.leb_refl].
destruct (ss_resv ss); [rewrite (sv_atoms_lt_mono n (S n) _ ltac:(lia) H4)|]; reflexivity.
+ exact Hrs.
+ exists E'. split; [|exact HS'].
eapply env_agree_trans; [apply env_agree_ewset | eapply env_agree_le; [| exact HA]; lia].
Qed.
Definition cval_eqb (a b : cval) : bool :=
match a, b with
| CVal w v, CVal w' v' => N.eqb w w' && sv_eqb v v'
| CZero l, CZero l' => Z.eqb l l'
| CImg l, CImg l' => Z.eqb l l'
| CData d s l, CData d' s' l' => Nat.eqb d d' && Z.eqb s s' && Z.eqb l l'
| _, _ => false
end.
Lemma cval_eqb_eq : forall a b, cval_eqb a b = true -> a = b.
Proof.
intros [w v|l|l|d s l] [w' v'|l'|l'|d' s' l'] H; cbn in H; try discriminate.
- apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity.
- apply Z.eqb_eq in H. subst. reflexivity.
- apply Z.eqb_eq in H. subst. reflexivity.
- apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Definition chunk_eqb (a b : chunk) : bool := Z.eqb (c_off a) (c_off b) && cval_eqb (c_val a) (c_val b).
Lemma chunk_eqb_eq : forall a b, chunk_eqb a b = true -> a = b.
Proof.
intros [o v] [o' v'] H. unfold chunk_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply cval_eqb_eq in H2. subst. reflexivity.
Qed.
Definition obase_eqb' (a b : option nat) : bool :=
match a, b with Some x, Some y => Nat.eqb x y | None, None => true | _, _ => false end.
Definition subregionb (r' r : region) : bool :=
obase_eqb' (r_base r') (r_base r) && (r_lo r <=? r_lo r') && (r_hi r' <=? r_hi r)
&& ((r_whi r' <=? r_wlo r') || ((r_wlo r <=? r_wlo r') && (r_whi r' <=? r_whi r)))
&& forallb (fun c => existsb (chunk_eqb c) (r_chunks r)) (r_chunks r').
Lemma subregionb_sound : forall r' r, subregionb r' r = true -> subregion r' r.
Proof.
intros r' r H. unfold subregionb in H. repeat (apply andb_prop in H as [H ?]).
unfold subregion. split.
{ destruct (r_base r'), (r_base r); cbn in H; try discriminate; [|reflexivity]. apply Nat.eqb_eq in H. subst. reflexivity. }
apply Z.leb_le in H2. apply Z.leb_le in H3. split; [lia|]. split; [lia|]. split.
- apply orb_prop in H1 as [H1|H1]; [left; apply Z.leb_le in H1; lia|]. apply andb_prop in H1 as [Ha Hb].
apply Z.leb_le in Ha. apply Z.leb_le in Hb. right. lia.
- intros c Hc. pose proof (proj1 (forallb_forall _ _) H0 c Hc) as Hx. apply existsb_exists in Hx as (c' & Hc' & He).
apply chunk_eqb_eq in He. subst. exact Hc'.
Qed.
Fixpoint submemb (rs' rs : smem) : bool :=
match rs', rs with
| [], _ => true
| _ :: _, [] => false
| r' :: t', r :: t => if subregionb r' r then submemb t' t else submemb rs' t
end.
Lemma submemb_sound : forall rs rs', submemb rs' rs = true -> submem rs' rs.
Proof.
induction rs as [|r t IH]; intros [|r' t'] H; cbn in H; try discriminate.
- apply submem_nil.
- apply submem_nil.
- destruct (subregionb r' r) eqn:E.
+ apply submem_keep; [apply subregionb_sound; exact E | apply IH; exact H].
+ apply submem_drop. apply IH. exact H.
Qed.
Definition afact_eqb (a b : afact) : bool := Z.eqb (af_lo a) (af_lo b) && Z.eqb (af_hi a) (af_hi b) && Z.eqb (af_al2 a) (af_al2 b).
Definition bc_eqb (a b : branch_cond) : bool :=
match a, b with
| BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
| _, _ => false
end.
Definition acond_eqb (a b : acond) : bool := bc_eqb (ac_c a) (ac_c b) && sv_eqb (ac_a a) (ac_a b) && sv_eqb (ac_b a) (ac_b b).
Definition facts_subb (G' G : facts) : bool :=
forallb (fun p => existsb (fun q => Nat.eqb (fst p) (fst q) && afact_eqb (snd p) (snd q)) (f_atoms G)) (f_atoms G')
&& forallb (fun c => existsb (acond_eqb c) (f_conds G)) (f_conds G')
&& forallb (fun p => existsb (fun q => sv_eqb (fst p) (fst q) && sv_eqb (snd p) (snd q)) (f_alias G)) (f_alias G').
Lemma atoms_ok_In : forall E l n f, atoms_ok E l -> In (n, f) l -> afact_ok E n f.
Proof. induction l as [|[n' f'] l IH]; intros n f H Hin; [destruct Hin|]. cbn in H. destruct H as [H1 H2]. destruct Hin as [E1|Hin]; [injection E1 as -> ->; exact H1 | apply IH; assumption]. Qed.
Lemma atoms_ok_intro : forall E l, (forall n f, In (n, f) l -> afact_ok E n f) -> atoms_ok E l.
Proof. induction l as [|[n f] l IH]; intros H; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros n' f' Hin; apply H; right; exact Hin]. Qed.
Lemma conds_ok_In : forall E l c, conds_ok E l -> In c l -> acond_ok E c.
Proof. induction l as [|c' l IH]; intros c H Hin; [destruct Hin|]. cbn in H. destruct H as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1 | apply IH; assumption]. Qed.
Lemma conds_ok_intro : forall E l, (forall c, In c l -> acond_ok E c) -> conds_ok E l.
Proof. induction l as [|c l IH]; intros H; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros c' Hin; apply H; right; exact Hin]. Qed.
Lemma alias_ok_In : forall E l a b, alias_ok E l -> In (a, b) l -> sv_denot E a = sv_denot E b.
Proof. induction l as [|[a' b'] l IH]; intros a b H Hin; [destruct Hin|]. cbn in H. destruct H as [H1 H2]. destruct Hin as [E1|Hin]; [injection E1 as -> ->; exact H1 | apply IH; assumption]. Qed.
Lemma alias_ok_intro : forall E l, (forall a b, In (a, b) l -> sv_denot E a = sv_denot E b) -> alias_ok E l.
Proof. induction l as [|[a b] l IH]; intros H; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros a' b' Hin; apply H; right; exact Hin]. Qed.
Lemma facts_subb_sound : forall E G' G, facts_subb G' G = true -> facts_ok E G -> facts_ok E G'.
Proof.
intros E G' G H (HA & HC & HL). unfold facts_subb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
split; [|split].
- apply atoms_ok_intro. intros n f Hin. pose proof (proj1 (forallb_forall _ _) H1 _ Hin) as Hx.
apply existsb_exists in Hx as ([n' f'] & Hin' & He). cbn in He. apply andb_prop in He as [He1 He2].
apply Nat.eqb_eq in He1. unfold afact_eqb in He2. apply andb_prop in He2 as [He2 He4]. apply andb_prop in He2 as [He2 He3].
apply Z.eqb_eq in He2. apply Z.eqb_eq in He3. apply Z.eqb_eq in He4. subst n'.
pose proof (atoms_ok_In E _ _ _ HA Hin') as (Q1 & Q2 & Q3). unfold afact_ok. rewrite He2, He3, He4. auto.
- apply conds_ok_intro. intros c Hin. pose proof (proj1 (forallb_forall _ _) H2 _ Hin) as Hx.
apply existsb_exists in Hx as (c' & Hin' & He). unfold acond_eqb in He. apply andb_prop in He as [He He3]. apply andb_prop in He as [He1 He2].
pose proof (conds_ok_In E _ _ HC Hin') as Q. unfold acond_ok in *.
apply sv_eqb_eq in He2. apply sv_eqb_eq in He3. rewrite He2, He3.
destruct (ac_c c), (ac_c c'); cbn in He1; try discriminate; exact Q.
- apply alias_ok_intro. intros a b Hin. pose proof (proj1 (forallb_forall _ _) H3 _ Hin) as Hx.
apply existsb_exists in Hx as ([a' b'] & Hin' & He). cbn in He. apply andb_prop in He as [He1 He2].
apply sv_eqb_eq in He1. apply sv_eqb_eq in He2. subst. exact (alias_ok_In E _ _ _ HL Hin').
Qed.
Definition mergeb (ss' ss : sstate) : bool :=
Z.eqb (ss_pc ss') (ss_pc ss) && forallb (fun p => sv_eqb (fst p) (snd p)) (combine (ss_regs ss') (ss_regs ss))
&& Nat.eqb (length (ss_regs ss')) (length (ss_regs ss))
&& match ss_resv ss', ss_resv ss with None, None => true | _, _ => false end
&& submemb (ss_mem ss') (ss_mem ss) && regions_wf (ss_mem ss') && facts_subb (ss_facts ss') (ss_facts ss).
Lemma combine_eqb_eq : forall (l1 l2 : list sv),
forallb (fun p => sv_eqb (fst p) (snd p)) (combine l1 l2) = true -> length l1 = length l2 -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H Hl; cbn in *; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply sv_eqb_eq in H1. subst. f_equal. apply IH; [exact H2 | lia].
Qed.
Lemma st_ok_merge : forall E ss' ss ms, st_ok segs E ss ms -> mergeb ss' ss = true -> st_ok segs E ss' ms.
Proof.
intros E ss' ss ms HS H. unfold mergeb in H. repeat (apply andb_prop in H as [H ?]).
apply Z.eqb_eq in H. apply Nat.eqb_eq in H4.
pose proof (combine_eqb_eq _ _ H5 H4) as ER.
destruct (ss_resv ss') eqn:R1; [discriminate|]. destruct (ss_resv ss) eqn:R2; [discriminate|].
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9). rewrite R2 in S4.
unfold st_ok. rewrite H, ER, R1. repeat (split; [assumption|]). split.
- eapply mem_ok_sub; [apply submemb_sound; exact H2 | exact H1 | exact S8].
- eapply facts_subb_sound; [exact H0 | exact S9].
Qed.
Lemma apply_zeros1_at : forall m a len x,
0 <= a -> 0 < len < 2 ^ 64 -> a + len <= 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
apply_zeros m [(Z_to_bv 64 a, Z_to_bv 64 len)] (Z_to_bv 64 x) =
if (a <=? x) && (x <? a + len) then Some (Z_to_bv 8 0) else m (Z_to_bv 64 x).
Proof. intros m a len x Ha Hl Hal Hx. cbn [apply_zeros]. rewrite zeros_cover_1 by lia. reflexivity. Qed.
Lemma mem_ok_ext_outside : forall E m m' rs a len,
mem_ok segs E m rs ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + len) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
(forall r, In r rs -> base_val E (r_base r) + r_hi r <= a \/ a + len <= base_val E (r_base r) + r_lo r) ->
mem_ok segs E m' rs.
Proof.
intros E m m' rs a len (Hwf & Hok & Hpd) Hm Hdis. split; [exact Hwf|]. split; [|exact Hpd].
rewrite Forall_forall in Hok |- *. intros r Hin.
destruct (Hok r Hin) as (H1 & H2 & H3 & H4). specialize (Hdis r Hin).
assert (Hwfr : region_wf r = true) by (eapply regions_wf_In; eauto).
apply region_wf_facts in Hwfr as (Hlohi & Hw & Hci).
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. specialize (H3 o Ho). unfold writable_at, wview in H3 |- *. rewrite Hm by lia. exact H3.
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
unfold mbyte in Hb2 |- *. rewrite Hm by lia. exact Hb2.
Qed.
Lemma mem_ok_zeros_outside : forall E m rs a len,
mem_ok segs E m rs -> 0 <= a -> 0 < len < 2 ^ 64 -> a + len <= 2 ^ 64 ->
(forall r, In r rs -> base_val E (r_base r) + r_hi r <= a \/ a + len <= base_val E (r_base r) + r_lo r) ->
mem_ok segs E (apply_zeros m [(Z_to_bv 64 a, Z_to_bv 64 len)]) rs.
Proof.
intros E m rs a len HM Ha Hl Hal Hdis. eapply mem_ok_ext_outside; [exact HM | | exact Hdis].
intros x Hx Hn. rewrite apply_zeros1_at by lia.
replace ((a <=? x) && (x <? a + len)) with false; [reflexivity|].
symmetry. apply andb_false_iff. destruct (Z_lt_le_dec x a); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.
Definition zregion (n : nat) (off len : Z) : region :=
mkRegion (Some n) off (off + len) off (off + len) [mkChunk off (CZero len)].
Lemma zregion_wf : forall n off len, 0 < len -> region_wf (zregion n off len) = true.
Proof.
intros n off len Hl. unfold region_wf, zregion, chunk_inside, c_len; cbn -[Z.leb Z.add].
replace (off <=? off + len) with true by (symmetry; apply Z.leb_le; lia).
replace (off + len <=? off) with false by (symmetry; apply Z.leb_gt; lia).
replace (off <=? off) with true by (symmetry; apply Z.leb_le; lia).
replace (off + len <=? off + len) with true by (symmetry; apply Z.leb_le; lia).
replace (0 <=? len) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma zregion_ok : forall E m n off len,
let a := bv_unsigned (ew E n) + off in
0 <= a -> 0 <= len -> a + len <= 2 ^ 64 ->
(forall x, a <= x < a + len -> m (Z_to_bv 64 x) = Some (Z_to_bv 8 0)) ->
region_ok segs E m (zregion n off len).
Proof.
intros E m n off len a Ha Hl Hal Hz. unfold region_ok, zregion; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. subst a.
split; [lia|]. split; [lia|]. split.
- intros o Ho. unfold writable_at, wview. rewrite Hz by lia. discriminate.
- constructor; [|constructor]. intros i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (Z_to_bv 8 0). split; [reflexivity|]. unfold mbyte. rewrite Hz by lia. reflexivity.
Qed.
Definition chunks_equiv (E : env) (base : Z) (cs cs' : list chunk) : Prop :=
forall c', In c' cs' -> exists c, In c cs /\ c_off c = c_off c' /\ c_len c = c_len c' /\
forall i, 0 <= i < c_len c -> cbyte segs E (base + c_off c) (c_val c') i = cbyte segs E (base + c_off c) (c_val c) i.
Lemma region_ok_rechunk : forall E m r cs',
region_ok segs E m r -> chunks_equiv E (base_val E (r_base r)) (r_chunks r) cs' ->
region_ok segs E m (mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) cs').
Proof.
intros E m r cs' (H1 & H2 & H3 & H4) Heq. unfold region_ok; cbn. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
rewrite Forall_forall in H4 |- *. intros c' Hc' i Hi.
destruct (Heq c' Hc') as (c & Hc & Eo & El & Eb).
assert (Hi' : 0 <= i < c_len c) by (rewrite El; exact Hi).
destruct (H4 c Hc i Hi') as (b & Hb1 & Hb2). exists b. rewrite <- Eo. rewrite Eb by exact Hi'. auto.
Qed.
Lemma cval_word_equiv : forall E base o (w : N) v v',
sv_denot E v = sv_denot E v' ->
forall i, 0 <= i < c_len (mkChunk o (CVal w v)) ->
cbyte segs E base (CVal w v') i = cbyte segs E base (CVal w v) i.
Proof. intros E base o w v v' H i _. cbn. rewrite H. reflexivity. Qed.
Lemma u64_range' (x : word) : 0 <= bv_unsigned x < 2 ^ 64.
Proof. apply u64_range. Qed.
Lemma lor_nonzero_taken : forall (x y : word),
bv_unsigned x <> 0 -> branch_taken BC_NE (alu64 ALU_OR x y) (Z_to_bv 64 0) = true.
Proof.
intros x y Hx. rewrite branch_ne. apply negb_true_iff. apply Z.eqb_neq.
rewrite alu64_or. change (bv_unsigned (Z_to_bv 64 0)) with 0.
pose proof (u64_range x). pose proof (u64_range y).
intros E0. pose proof (Z.lor_eq_0_l _ _ E0). lia.
Qed.
Lemma mapok_taken' : forall a : word,
bv_unsigned a < 2 ^ 64 - 1 ->
branch_taken BC_NE (alu64 ALU_OR (Z_to_bv 64 0) (alu64 ALU_XOR a (Z_to_bv 64 (-1)))) (Z_to_bv 64 0) = true.
Proof.
intros a Ha. rewrite branch_ne. apply negb_true_iff. apply Z.eqb_neq.
rewrite alu64_or, alu64_xori_m1. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.lor_0_l.
pose proof (u64_range a). rewrite not64_eq by lia. lia.
Qed.
Lemma sll_2_denot : forall (shw : word) sh,
bv_unsigned shw = sh -> 0 <= sh <= 40 ->
alu64 ALU_SLL (Z_to_bv 64 2) shw = Z_to_bv 64 (Z.shiftl 2 sh).
Proof.
intros shw sh Hsh Hr. apply bv_eq. rewrite alu64_sll. rewrite Hsh. change (bv_unsigned (Z_to_bv 64 2)) with 2.
rewrite Z.mod_small by lia. unfold sll64.
assert (H : 0 <= Z.shiftl 2 sh < 2 ^ 64).
{ rewrite Z.shiftl_mul_pow2 by lia. split; [lia|].
apply (Z.le_lt_trans _ (2 * 2 ^ 40)); [apply Z.mul_le_mono_nonneg_l; [lia | apply Z.pow_le_mono_r; lia] |].
rewrite <- Z.pow_succ_r by lia. apply Z.pow_lt_mono_r; lia. }
rewrite Z.mod_small by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
Qed.
Lemma mul_4096_denot : forall (x : word) n,
bv_unsigned x = n -> 0 <= n -> n * 4096 < 2 ^ 64 ->
mul_div M_MUL x (Z_to_bv 64 4096) = Z_to_bv 64 (n * 4096).
Proof.
intros x n Hx Hn Hr. apply bv_eq. rewrite mul64_unsigned, Hx. change (bv_unsigned (Z_to_bv 64 4096)) with 4096.
unfold mul64. rewrite Z.mod_small by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
Qed.
End h.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
