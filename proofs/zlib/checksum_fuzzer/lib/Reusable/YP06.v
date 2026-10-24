(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m YP09 YP0l YP0k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition env_agree (k : nat) (E E' : env) : Prop :=
(forall n, (n < k)%nat -> ew E' n = ew E n) /\ ed E' = ed E.
Lemma env_agree_refl : forall k E, env_agree k E E.
Proof. intros. split; auto. Qed.
Fixpoint sv_atoms_lt (k : nat) (v : sv) : bool :=
match v with
| SLit _ => true
| SOff n _ => Nat.ltb n k
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => sv_atoms_lt k a && sv_atoms_lt k b
| SExt _ _ a => sv_atoms_lt k a
| SData _ _ _ => true
| SF1 _ a => sv_atoms_lt k a
| SF2 _ a b => sv_atoms_lt k a && sv_atoms_lt k b
| SF3 _ a b c => sv_atoms_lt k a && sv_atoms_lt k b && sv_atoms_lt k c
end.
Lemma sv_denot_agree : forall k E E' v,
env_agree k E E' -> sv_atoms_lt k v = true -> sv_denot E' v = sv_denot E v.
Proof.
intros k E E' v [HA HD]. induction v; cbn; intros H; try reflexivity;
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
- apply Nat.ltb_lt in H. rewrite HA by exact H. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv by assumption. reflexivity.
- unfold data_word. rewrite HD. reflexivity.
- rewrite IHv by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2, IHv3 by assumption. reflexivity.
Qed.
Definition regs_atoms_lt (k : nat) (sr : list sv) : bool := forallb (sv_atoms_lt k) sr.
Lemma sr_get_atoms : forall k sr r, regs_atoms_lt k sr = true -> sv_atoms_lt k (sr_get sr r) = true.
Proof.
intros k sr r H. unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
unfold regs_atoms_lt in H.
destruct (nth_in_or_default (ridx r) sr (SLit 0)) as [Hin| ->]; [|reflexivity].
apply (proj1 (forallb_forall _ _) H). exact Hin.
Qed.
Lemma regs_ok_agree : forall k E E' sr regs,
env_agree k E E' -> regs_atoms_lt k sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
intros k E E' sr regs HA Hsr Hr r. rewrite (sv_denot_agree k E E') by (auto using sr_get_atoms). apply Hr.
Qed.
Definition cval_atoms_lt (k : nat) (cv : cval) : bool :=
match cv with CVal _ v => sv_atoms_lt k v | _ => true end.
Definition obase_lt (k : nat) (b : option nat) : bool :=
match b with Some n => Nat.ltb n k | None => true end.
Definition region_atoms_lt (k : nat) (r : region) : bool :=
obase_lt k (r_base r) && forallb (fun c => cval_atoms_lt k (c_val c)) (r_chunks r).
Definition mem_atoms_lt (k : nat) (rs : smem) : bool := forallb (region_atoms_lt k) rs.
Lemma base_val_agree : forall k E E' b,
env_agree k E E' -> obase_lt k b = true -> base_val E' b = base_val E b.
Proof.
intros k E E' [x|] [HA _] H; cbn in *; [|reflexivity].
apply Nat.ltb_lt in H. rewrite HA by exact H. reflexivity.
Qed.
Lemma cbyte_agree : forall segs k E E' a cv i,
env_agree k E E' -> cval_atoms_lt k cv = true -> cbyte segs E' a cv i = cbyte segs E a cv i.
Proof.
intros segs k E E' a cv i HA H. destruct cv; cbn in *; try reflexivity.
- rewrite (sv_denot_agree k E E') by assumption. reflexivity.
- destruct HA as [_ HD]. rewrite HD. reflexivity.
Qed.
Lemma region_ok_agree : forall segs k E E' m r,
env_agree k E E' -> region_atoms_lt k r = true ->
region_ok segs E m r -> region_ok segs E' m r.
Proof.
intros segs k E E' m r HA H (H1 & H2 & H3 & H4).
unfold region_atoms_lt in H. apply andb_prop in H as [Hb Hc].
unfold region_ok. rewrite (base_val_agree k E E') by assumption.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
rewrite Forall_forall in H4 |- *. intros c Hin i Hi.
destruct (H4 c Hin i Hi) as (b & Hb1 & Hb2). exists b. split; [|exact Hb2].
rewrite (cbyte_agree segs k E E'); [exact Hb1| exact HA|].
apply (proj1 (forallb_forall _ _) Hc). exact Hin.
Qed.
Lemma extent_disjoint_agree : forall k E E' r1 r2,
env_agree k E E' -> obase_lt k (r_base r1) = true -> obase_lt k (r_base r2) = true ->
extent_disjoint E r1 r2 -> extent_disjoint E' r1 r2.
Proof.
intros k E E' r1 r2 HA H1 H2 H. unfold extent_disjoint in *.
rewrite !(base_val_agree k E E') by assumption. exact H.
Qed.
Lemma pairwise_disjoint_agree : forall k E E' rs,
env_agree k E E' -> mem_atoms_lt k rs = true ->
pairwise_disjoint E rs -> pairwise_disjoint E' rs.
Proof.
intros k E E' rs HA. induction rs as [|r rs IH]; cbn; intros H Hp; [exact I|].
apply andb_prop in H as [Hr Hrs]. destruct Hp as [Ha Hp]. split; [|apply IH; assumption].
unfold region_atoms_lt in Hr. apply andb_prop in Hr as [Hb _].
clear IH Hp. induction rs as [|r' rs IH']; cbn in *; [exact I|].
apply andb_prop in Hrs as [Hr' Hrs]. destruct Ha as [Hd Ha].
unfold region_atoms_lt in Hr'. apply andb_prop in Hr' as [Hb' _].
split; [eapply extent_disjoint_agree; eauto | apply IH'; assumption].
Qed.
Lemma mem_ok_agree : forall segs k E E' m rs,
env_agree k E E' -> mem_atoms_lt k rs = true -> mem_ok segs E m rs -> mem_ok segs E' m rs.
Proof.
intros segs k E E' m rs HA H (Hwf & Hok & Hpd). split; [exact Hwf|]. split.
- rewrite Forall_forall in Hok |- *. intros r Hin. eapply region_ok_agree; eauto.
apply (proj1 (forallb_forall _ _) H). exact Hin.
- eapply pairwise_disjoint_agree; eauto.
Qed.
Definition cond_atoms_lt (k : nat) (c : acond) : bool := sv_atoms_lt k (ac_a c) && sv_atoms_lt k (ac_b c).
Definition facts_atoms_lt (k : nat) (G : facts) : bool :=
forallb (fun p => Nat.ltb (fst p) k) (f_atoms G) && forallb (cond_atoms_lt k) (f_conds G)
&& forallb (fun p => sv_atoms_lt k (fst p) && sv_atoms_lt k (snd p)) (f_alias G).
Lemma facts_ok_agree : forall k E E' G,
env_agree k E E' -> facts_atoms_lt k G = true -> facts_ok E G -> facts_ok E' G.
Proof.
intros k E E' G HA H (Hat & Hco & Hal). unfold facts_atoms_lt in H.
apply andb_prop in H as [H HL]. apply andb_prop in H as [Ha Hc].
split; [|split].
- clear Hco Hc Hal HL. induction (f_atoms G) as [|[n f] l IH]; cbn in *; [exact I|].
apply andb_prop in Ha as [Hn Hl]. destruct Hat as [Hf Hl'].
split; [|apply IH; assumption].
unfold afact_ok in *. apply Nat.ltb_lt in Hn. rewrite (proj1 HA) by exact Hn. exact Hf.
- clear Hat Ha Hal HL. induction (f_conds G) as [|c l IH]; cbn in *; [exact I|].
apply andb_prop in Hc as [Hc1 Hl]. destruct Hco as [Hc0 Hl'].
split; [|apply IH; assumption].
unfold acond_ok, cond_atoms_lt in *. apply andb_prop in Hc1 as [H1 H2].
rewrite !(sv_denot_agree k E E') by assumption. exact Hc0.
- clear Hat Ha Hco Hc. induction (f_alias G) as [|[a b] l IH]; cbn in *; [exact I|].
apply andb_prop in HL as [Hab HL']. apply andb_prop in Hab as [H1 H2]. destruct Hal as [Heq Hal'].
split; [|apply IH; assumption].
rewrite !(sv_denot_agree k E E') by assumption. exact Heq.
Qed.
Definition ss_atoms_lt (k : nat) (ss : sstate) : bool :=
regs_atoms_lt k (ss_regs ss) && mem_atoms_lt k (ss_mem ss) && facts_atoms_lt k (ss_facts ss)
&& match ss_resv ss with Some a => sv_atoms_lt k a | None => true end.
Definition ss_atoms_ltF (k : nat) (ss : sstate) : bool :=
ss_atoms_lt k ss && regs_atoms_lt k (ss_fregs ss).
Lemma sfr_get_atoms_lt : forall k sfr r, regs_atoms_lt k sfr = true -> sv_atoms_lt k (sfr_get sfr r) = true.
Proof.
intros k sfr r H. unfold sfr_get. unfold regs_atoms_lt in H.
destruct (nth_in_or_default (ridx r) sfr (SLit 0)) as [Hin| ->]; [|reflexivity].
apply (proj1 (forallb_forall _ _) H). exact Hin.
Qed.
Lemma fregs_ok_agree : forall k E E' sfr fregs,
env_agree k E E' -> regs_atoms_lt k sfr = true -> fregs_ok E sfr fregs -> fregs_ok E' sfr fregs.
Proof.
intros k E E' sfr fregs HA Hat Hf r. rewrite (sv_denot_agree k E E') by (auto using sfr_get_atoms_lt). apply Hf.
Qed.
Section e.
Variable segs : list Segment.
Context {fx : FPState}.
Lemma st_ok_ecall_pend : forall E ss ms,
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
ms = pend_at (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (seg_rom segs)
/\ regs_ok E (ss_regs ss) (ms_regs ms)
/\ ms_pc_val ms = Z_to_bv 64 (ss_pc ss)
/\ mem_ok segs E (ms_mem ms) (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Proof.
intros E ss ms (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG) Hrv.
destruct ms as [regs fregs pcv pend resv fcsr mem rom]; cbn in *.
rewrite Hrv in Hresv. cbn in Hresv. subst.
split; [|auto]. unfold pend_at. rewrite <- (Hregs 17%bv). reflexivity.
Qed.
Definition resume (ss : sstate) (rv : sv) (rs : smem) (G : facts) : sstate :=
mkSS (ss_pc ss + 4) (sr_set (ss_regs ss) 10 rv) rs None G.
Lemma st_ok_resume : forall E E' k ss regs pc (mem' : word -> option byte) rv RET rs G,
regs_ok E (ss_regs ss) regs ->
pc = Z_to_bv 64 (ss_pc ss) ->
env_agree k E E' -> regs_atoms_lt k (ss_regs ss) = true ->
sv_denot E' rv = RET ->
mem_ok segs E' mem' rs ->
facts_ok E' G ->
st_ok segs E' (resume ss rv rs G) (mkst (regupd regs 10 RET) (v_addi pc 4) mem' (seg_rom segs)).
Proof.
intros E E' k ss regs pc mem' rv RET rs G Hregs Hpc HA Hat Hrv Hmem HG.
unfold st_ok, resume, mkst; cbn.
split; [reflexivity|]. split.
{ rewrite Hpc. unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_eq_mod.
unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Zplus_mod_idemp_l. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
- change (regupd regs 10 RET) with (if bv_eqb (10:reg) 0 then regs else regupd regs 10 RET).
apply regs_ok_set; [|exact Hrv]. eapply regs_ok_agree; eauto.
- exact (conj Hmem HG).
Qed.
Definition add_cond (ss : sstate) (c : acond) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts (f_atoms (ss_facts ss)) (c :: f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Lemma st_ok_add_cond : forall E ss ms c a b,
st_ok segs E ss ms ->
branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok segs E (add_cond ss (mkAC c a b)) ms.
Proof.
intros E ss ms c a b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HG) Hb.
unfold facts_ok in HG. destruct HG as (Ha & Hc & Hl).
unfold st_ok, add_cond, facts_ok; cbn.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
split; [exact Ha|]. split; [|exact Hl]. split; [exact Hb| exact Hc].
Qed.
Lemma st_ok_add_cond_neg : forall E ss ms c a b,
st_ok segs E ss ms ->
branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_ok segs E (add_cond ss (mkAC (neg_bc c) a b)) ms.
Proof.
intros E ss ms c a b HS Hb. apply st_ok_add_cond; [exact HS|].
rewrite branch_taken_neg, Hb. reflexivity.
Qed.
Definition add_atom (ss : sstate) (n : nat) (f : afact) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Lemma facts_ok_add_atom : forall E G n f,
facts_ok E G -> afact_ok E n f -> facts_ok E (mkFacts ((n, f) :: f_atoms G) (f_conds G) (f_alias G)).
Proof. intros E G n f [Ha Hc] Hf. split; [|exact Hc]. cbn. split; assumption. Qed.
Lemma facts_ok_add_alias : forall E G a b,
facts_ok E G -> sv_denot E a = sv_denot E b ->
facts_ok E (mkFacts (f_atoms G) (f_conds G) ((a, b) :: f_alias G)).
Proof. intros E G a b (Ha & Hc & Hl) Hab. split; [exact Ha|]. split; [exact Hc|]. cbn. split; assumption. Qed.
Definition subregion (r' r : region) : Prop :=
r_base r' = r_base r /\ r_lo r <= r_lo r' /\ r_hi r' <= r_hi r
/\ (r_whi r' <= r_wlo r' \/ (r_wlo r <= r_wlo r' /\ r_whi r' <= r_whi r))
/\ (forall c, In c (r_chunks r') -> In c (r_chunks r)).
Lemma region_ok_sub : forall E m r r',
subregion r' r -> r_lo r' <= r_hi r' -> region_ok segs E m r -> region_ok segs E m r'.
Proof.
intros E m r r' (Hb & Hlo & Hhi & Hw & Hc) Hle (H1 & H2 & H3 & H4).
unfold region_ok. rewrite Hb. split; [lia|]. split; [lia|]. split.
- intros o Ho. destruct Hw as [Hw|Hw]; [lia|]. apply H3. lia.
- rewrite Forall_forall in H4 |- *. intros c Hin. apply H4. apply Hc. exact Hin.
Qed.
Inductive submem : smem -> smem -> Prop :=
| submem_nil : forall rs, submem [] rs
| submem_drop : forall rs' r rs, submem rs' rs -> submem rs' (r :: rs)
| submem_keep : forall r' r rs' rs, subregion r' r -> submem rs' rs -> submem (r' :: rs') (r :: rs).
Lemma all_disjoint_sub : forall E r r0 rs' rs,
subregion r r0 -> submem rs' rs -> all_disjoint E r0 rs -> all_disjoint E r rs'.
Proof.
intros E r r0 rs' rs Hsub Hsm. induction Hsm as [rs1|rs1 x rs2 Hsm IH|x' x rs1 rs2 Hsr Hsm IH]; cbn; intros HA; [exact I| |].
- apply IH. tauto.
- destruct HA as [Hd Ha]. split; [|apply IH; exact Ha].
destruct Hsub as (Hb & Hlo & Hhi & _). destruct Hsr as (Hb' & Hlo' & Hhi' & _).
unfold extent_disjoint in *. rewrite Hb, Hb'. lia.
Qed.
Lemma pairwise_disjoint_sub : forall E rs' rs,
submem rs' rs -> pairwise_disjoint E rs -> pairwise_disjoint E rs'.
Proof.
intros E rs' rs Hsm. induction Hsm as [rs1|rs1 x rs2 Hsm IH|x' x rs1 rs2 Hsr Hsm IH]; cbn; intros HP; [exact I| |].
- apply IH. tauto.
- destruct HP as [Ha Hp]. split; [|apply IH; exact Hp].
eapply all_disjoint_sub; eauto.
Qed.
Lemma mem_ok_sub : forall E m rs rs',
submem rs' rs -> regions_wf rs' = true -> mem_ok segs E m rs -> mem_ok segs E m rs'.
Proof.
intros E m rs rs' Hsm Hwf' (Hwf & Hok & Hpd). split; [exact Hwf'|]. split.
- clear Hpd. induction Hsm as [rs1|rs1 x rs2 Hsm IH|x' x rs1 rs2 Hsr Hsm IH]; [constructor| |].
+ cbn in Hwf. apply andb_prop in Hwf as [_ Hwf]. inversion Hok; subst. apply IH; assumption.
+ cbn in Hwf, Hwf'. apply andb_prop in Hwf as [Hr Hwf]. apply andb_prop in Hwf' as [Hr' Hwf'2].
inversion Hok; subst. constructor; [|apply IH; assumption].
eapply region_ok_sub; [exact Hsr| |eassumption].
apply region_wf_facts in Hr' as (Hle & _). exact Hle.
- eapply pairwise_disjoint_sub; eauto.
Qed.
Definition zero_region (n : nat) (len : Z) : region :=
mkRegion (Some n) 0 len 0 len [mkChunk 0 (CZero len)].
Lemma zeros_cover_1 : forall a len x,
0 <= a < 2^64 -> 0 <= len < 2^64 -> a + len <= 2^64 -> 0 <= x < 2^64 ->
zeros_cover [(Z_to_bv 64 a, Z_to_bv 64 len)] (Z_to_bv 64 x) = ((a <=? x) && (x <? a + len)).
Proof.
intros a len x Ha Hl Hal Hx. unfold zeros_cover. cbn [existsb fst snd].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite !Z.mod_small by lia.
rewrite orb_false_r. reflexivity.
Qed.
Lemma mem_ok_add_zeros : forall E m rs n a len,
mem_ok segs E m rs ->
bv_unsigned (ew E n) = a -> 0 < len < 2^64 -> a + len <= 2^64 ->
(forall r, In r rs -> base_val E (r_base r) + r_hi r <= a \/ a + len <= base_val E (r_base r) + r_lo r) ->
mem_ok segs E (apply_zeros m [(Z_to_bv 64 a, Z_to_bv 64 len)]) (zero_region n len :: rs).
Proof.
intros E m rs n a len (Hwf & Hok & Hpd) Hn Hlen Hal Hdis.
pose proof (u64_range (ew E n)) as Hu.
assert (Hz : forall x, 0 <= x < 2^64 ->
apply_zeros m [(Z_to_bv 64 a, Z_to_bv 64 len)] (Z_to_bv 64 x) =
if (a <=? x) && (x <? a + len) then Some (Z_to_bv 8 0) else m (Z_to_bv 64 x)).
{ intros x Hx. cbn [apply_zeros]. rewrite zeros_cover_1 by lia. reflexivity. }
split; [|split].
- cbn -[Z.leb Z.add]. rewrite Hwf, andb_true_r.
unfold region_wf, zero_region, chunk_inside, c_len; cbn -[Z.leb Z.add].
rewrite !Z.add_0_l.
replace (0 <=? len) with true by (symmetry; apply Z.leb_le; lia).
replace (len <=? len) with true by (symmetry; apply Z.leb_le; lia).
replace (len <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
reflexivity.
- constructor.
+ unfold region_ok, zero_region; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split.
* intros o Ho. unfold writable_at, wview. rewrite Hz by lia.
replace ((a <=? a + o) && (a + o <? a + len)) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
discriminate.
* constructor; [|constructor]. intros i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (Z_to_bv 8 0). split; [reflexivity|]. unfold mbyte. rewrite Hz by lia.
replace ((a <=? a + 0 + i) && (a + 0 + i <? a + len)) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
reflexivity.
+ rewrite Forall_forall in Hok |- *. intros r Hin.
destruct (Hok r Hin) as (H1 & H2 & H3 & H4). specialize (Hdis r Hin).
split; [exact H1|]. split; [exact H2|]. split.
* intros o Ho. eapply writable_at_grows; [|apply H3; exact Ho].
intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (lit_of_word x) in Hx |- *.
rewrite Hz by lia. destruct (_ && _); [discriminate| exact Hx].
* rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
assert (Hwfr : region_wf r = true) by (eapply regions_wf_In; eauto).
apply region_wf_facts in Hwfr as (_ & _ & Hci).
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
unfold mbyte in Hb2 |- *. rewrite Hz by lia.
replace ((a <=? base_val E (r_base r) + c_off c + i) && (base_val E (r_base r) + c_off c + i <? a + len))
with false; [exact Hb2|].
symmetry. apply andb_false_iff. destruct Hdis; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
- cbn. split; [|exact Hpd].
clear Hok Hpd Hwf. induction rs as [|r rs IH]; cbn; [exact I|]. split.
+ unfold extent_disjoint, zero_region; cbn [r_base r_lo r_hi base_val]. rewrite Hn.
destruct (Hdis r (or_introl eq_refl)); lia.
+ apply IH. intros r' Hin. apply Hdis. right. exact Hin.
Qed.
Lemma mem_ok_unmap : forall E m rs a len,
mem_ok segs E m rs ->
0 <= a -> 0 < len < 2^64 -> a + len <= 2^64 ->
(forall r, In r rs -> base_val E (r_base r) + r_hi r <= a \/ a + len <= base_val E (r_base r) + r_lo r) ->
mem_ok segs E (apply_unmaps m [(Z_to_bv 64 a, Z_to_bv 64 len)]) rs.
Proof.
intros E m rs a len (Hwf & Hok & Hpd) Ha Hlen Hal Hdis.
assert (Hz : forall x, 0 <= x < 2^64 ->
apply_unmaps m [(Z_to_bv 64 a, Z_to_bv 64 len)] (Z_to_bv 64 x) =
if (a <=? x) && (x <? a + len) then None else m (Z_to_bv 64 x)).
{ intros x Hx. cbn [apply_unmaps]. rewrite zeros_cover_1 by lia. reflexivity. }
split; [exact Hwf|]. split; [|exact Hpd].
rewrite Forall_forall in Hok |- *. intros r Hin.
destruct (Hok r Hin) as (H1 & H2 & H3 & H4). specialize (Hdis r Hin).
assert (Hwfr : region_wf r = true) by (eapply regions_wf_In; eauto).
apply region_wf_facts in Hwfr as (Hlohi & Hw & Hci).
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. specialize (H3 o Ho). unfold writable_at, wview in H3 |- *. rewrite Hz by lia.
replace ((a <=? base_val E (r_base r) + o) && (base_val E (r_base r) + o <? a + len)) with false; [exact H3|].
symmetry. apply andb_false_iff. destruct Hdis; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
unfold mbyte in Hb2 |- *. rewrite Hz by lia.
replace ((a <=? base_val E (r_base r) + c_off c + i) && (base_val E (r_base r) + c_off c + i <? a + len))
with false; [exact Hb2|].
symmetry. apply andb_false_iff. destruct Hdis; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
Qed.
Definition rebase := list (nat * (nat * Z)).
Fixpoint rb_lookup (rb : rebase) (n : nat) : option (nat * Z) :=
match rb with
| [] => None
| (m, t) :: r => if Nat.eqb m n then Some t else rb_lookup r n
end.
Fixpoint sv_rebase (rb : rebase) (v : sv) : sv :=
match v with
| SLit z => SLit z
| SOff n z => match rb_lookup rb n with Some (n', d) => SOff n' (z + d) | None => SOff n z end
| SAlu op a b => SAlu op (sv_rebase rb a) (sv_rebase rb b)
| SAluw op a b => SAluw op (sv_rebase rb a) (sv_rebase rb b)
| SMd op a b => SMd op (sv_rebase rb a) (sv_rebase rb b)
| SMdw op a b => SMdw op (sv_rebase rb a) (sv_rebase rb b)
| SExt sg w a => SExt sg w (sv_rebase rb a)
| SData d i n => SData d i n
| SF1 op a => SF1 op (sv_rebase rb a)
| SF2 op a b => SF2 op (sv_rebase rb a) (sv_rebase rb b)
| SF3 op a b c => SF3 op (sv_rebase rb a) (sv_rebase rb b) (sv_rebase rb c)
end.
Definition rebase_ok (E E' : env) (rb : rebase) : Prop :=
(forall n n' d, rb_lookup rb n = Some (n', d) ->
Z_to_bv 64 (bv_unsigned (ew E n)) = Z_to_bv 64 (bv_unsigned (ew E' n') + d))
/\ (forall n, rb_lookup rb n = None -> ew E' n = ew E n)
/\ ed E' = ed E.
Lemma sv_rebase_sound : forall E E' rb v,
rebase_ok E E' rb -> sv_denot E' (sv_rebase rb v) = sv_denot E v.
Proof.
intros E E' rb v (H1 & H2 & H3). induction v; cbn; try reflexivity.
- destruct (rb_lookup rb n) as [[n' d]|] eqn:Hl; cbn.
+ specialize (H1 _ _ _ Hl). symmetry.
rewrite <- lit_add, H1, lit_add. f_equal. lia.
+ rewrite (H2 _ Hl). reflexivity.
- rewrite IHv1, IHv2. reflexivity.
- rewrite IHv1, IHv2. reflexivity.
- rewrite IHv1, IHv2. reflexivity.
- rewrite IHv1, IHv2. reflexivity.
- rewrite IHv. reflexivity.
- unfold data_word. rewrite H3. reflexivity.
- rewrite IHv. reflexivity.
- rewrite IHv1, IHv2. reflexivity.
- rewrite IHv1, IHv2, IHv3. reflexivity.
Qed.
Definition regs_rebase (rb : rebase) (sr : list sv) : list sv := map (sv_rebase rb) sr.
Lemma regs_ok_rebase : forall E E' rb sr regs,
rebase_ok E E' rb -> regs_ok E sr regs -> regs_ok E' (regs_rebase rb sr) regs.
Proof.
intros E E' rb sr regs Hrb Hr r. specialize (Hr r). unfold sr_get, regs_rebase in *.
destruct (bv_eqb r 0); [exact Hr|].
change (SLit 0) with (sv_rebase rb (SLit 0)). rewrite map_nth.
rewrite (sv_rebase_sound E E') by exact Hrb. exact Hr.
Qed.
Definition chunk_rebase (d : Z) (rb : rebase) (c : chunk) : chunk :=
mkChunk (c_off c + d) (match c_val c with CVal w v => CVal w (sv_rebase rb v) | cv => cv end).
Definition region_rebase (rb : rebase) (r : region) : region :=
match r_base r with
| Some n =>
match rb_lookup rb n with
| Some (n', d) => mkRegion (Some n') (r_lo r + d) (r_hi r + d) (r_wlo r + d) (r_whi r + d)
(map (chunk_rebase d rb) (r_chunks r))
| None => mkRegion (Some n) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (map (chunk_rebase 0 rb) (r_chunks r))
end
| None => mkRegion None (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (map (chunk_rebase 0 rb) (r_chunks r))
end.
Definition mem_rebase (rb : rebase) (rs : smem) : smem := map (region_rebase rb) rs.
Definition rebase_exact (E E' : env) (rb : rebase) (n : nat) : Prop :=
match rb_lookup rb n with
| Some (n', d) => bv_unsigned (ew E n) = bv_unsigned (ew E' n') + d
| None => ew E' n = ew E n
end.
Lemma base_val_rebase : forall E E' rb r,
(forall n, r_base r = Some n -> rebase_exact E E' rb n) ->
base_val E' (r_base (region_rebase rb r)) + r_lo (region_rebase rb r) = base_val E (r_base r) + r_lo r
/\ base_val E' (r_base (region_rebase rb r)) + r_hi (region_rebase rb r) = base_val E (r_base r) + r_hi r
/\ base_val E' (r_base (region_rebase rb r)) + r_wlo (region_rebase rb r) = base_val E (r_base r) + r_wlo r
/\ base_val E' (r_base (region_rebase rb r)) + r_whi (region_rebase rb r) = base_val E (r_base r) + r_whi r.
Proof.
intros E E' rb r Hx. unfold region_rebase. destruct (r_base r) as [n|] eqn:Hb; cbn.
- specialize (Hx n eq_refl). unfold rebase_exact in Hx.
destruct (rb_lookup rb n) as [[n' d]|]; cbn; [lia|]. rewrite Hx. lia.
- lia.
Qed.
Definition region_rb_delta (rb : rebase) (r : region) : Z :=
match r_base r with
| Some n => match rb_lookup rb n with Some (_, d) => d | None => 0 end
| None => 0
end.
Lemma region_rebase_fields : forall rb r,
r_lo (region_rebase rb r) = r_lo r + region_rb_delta rb r
/\ r_hi (region_rebase rb r) = r_hi r + region_rb_delta rb r
/\ r_wlo (region_rebase rb r) = r_wlo r + region_rb_delta rb r
/\ r_whi (region_rebase rb r) = r_whi r + region_rb_delta rb r
/\ r_chunks (region_rebase rb r) = map (chunk_rebase (region_rb_delta rb r) rb) (r_chunks r).
Proof.
intros rb r. unfold region_rebase, region_rb_delta.
destruct (r_base r) as [n|]; [destruct (rb_lookup rb n) as [[n' d]|]|]; cbn;
repeat split; try lia; try reflexivity.
all: f_equal; try lia.
all: apply map_ext; intros c; unfold chunk_rebase; f_equal; lia.
Qed.
Lemma c_len_rebase : forall d rb c, c_len (chunk_rebase d rb c) = c_len c.
Proof. intros d rb c. unfold chunk_rebase, c_len. cbn. destruct (c_val c); reflexivity. Qed.
Lemma region_wf_rebase : forall rb r, region_wf r = true -> region_wf (region_rebase rb r) = true.
Proof.
intros rb r H. apply region_wf_facts in H as (H1 & H2 & H3).
destruct (region_rebase_fields rb r) as (F1 & F2 & F3 & F4 & F5).
set (d := region_rb_delta rb r) in *.
unfold region_wf. rewrite F1, F2, F3, F4, F5.
apply andb_true_intro. split.
- apply andb_true_intro. split; [apply Z.leb_le; lia|].
destruct H2 as [H2|H2].
+ apply orb_true_intro. left. apply Z.leb_le. lia.
+ apply orb_true_intro. right. apply andb_true_intro. split; apply Z.leb_le; lia.
- apply forallb_forall. intros c' Hin. apply in_map_iff in Hin as (c & <- & Hin).
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) H3 c Hin)) as (C1 & C2 & C3).
unfold chunk_inside. rewrite c_len_rebase. cbn [c_off chunk_rebase r_lo r_hi].
rewrite F1, F2. rewrite !andb_true_iff, !Z.leb_le. unfold chunk_rebase; cbn. lia.
Qed.
Lemma all_disjoint_rebase : forall E E' rb r rs,
(forall n, r_base r = Some n -> rebase_exact E E' rb n) ->
(forall r0 n, In r0 rs -> r_base r0 = Some n -> rebase_exact E E' rb n) ->
all_disjoint E r rs -> all_disjoint E' (region_rebase rb r) (map (region_rebase rb) rs).
Proof.
intros E E' rb r rs Hr Hrs. induction rs as [|r0 rs IH]; cbn; intros H; [exact I|].
destruct H as [Hd Ha]. split.
- destruct (base_val_rebase E E' rb r Hr) as (B1 & B2 & _).
destruct (base_val_rebase E E' rb r0 ltac:(intros n Hn; eapply Hrs; [left; reflexivity| exact Hn])) as (C1 & C2 & _).
unfold extent_disjoint in *. lia.
- apply IH; [|exact Ha]. intros r1 n Hin Hn. eapply Hrs; [right; exact Hin| exact Hn].
Qed.
Lemma pairwise_disjoint_rebase : forall E E' rb rs,
(forall r n, In r rs -> r_base r = Some n -> rebase_exact E E' rb n) ->
pairwise_disjoint E rs -> pairwise_disjoint E' (map (region_rebase rb) rs).
Proof.
intros E E' rb rs Hrs. induction rs as [|r rs IH]; cbn; intros H; [exact I|].
destruct H as [Ha Hp]. split.
- apply (all_disjoint_rebase E E'); [intros n Hn; eapply Hrs; [left; reflexivity|exact Hn] | |exact Ha].
intros r0 n Hin Hn. eapply Hrs; [right; exact Hin|exact Hn].
- apply IH; [|exact Hp]. intros r0 n Hin Hn. eapply Hrs; [right; exact Hin|exact Hn].
Qed.
Lemma mem_ok_rebase : forall E E' rb m rs,
rebase_ok E E' rb ->
(forall r n, In r rs -> r_base r = Some n -> rebase_exact E E' rb n) ->
mem_ok segs E m rs -> mem_ok segs E' m (mem_rebase rb rs).
Proof.
intros E E' rb m rs Hrb Hex (Hwf & Hok & Hpd). split; [|split].
- unfold mem_rebase. clear Hok Hpd Hex. induction rs as [|r rs IH]; cbn in *; [reflexivity|].
apply andb_prop in Hwf as [Hr Hwf]. rewrite region_wf_rebase, IH by assumption. reflexivity.
- unfold mem_rebase. rewrite Forall_forall in Hok |- *. intros r' Hin'.
apply in_map_iff in Hin' as (r & <- & Hin). specialize (Hok r Hin).
destruct Hok as (H1 & H2 & H3 & H4).
destruct (base_val_rebase E E' rb r ltac:(intros n Hn; eapply Hex; eauto)) as (B1 & B2 & B3 & B4).
destruct (region_rebase_fields rb r) as (F1 & F2 & F3 & F4 & F5).
set (d := region_rb_delta rb r) in *.
assert (HB : base_val E' (r_base (region_rebase rb r)) = base_val E (r_base r) - d) by lia.
unfold region_ok. rewrite B1, B2. split; [exact H1|]. split; [exact H2|]. split.
+ intros o Ho. rewrite HB. replace (base_val E (r_base r) - d + o) with (base_val E (r_base r) + (o - d)) by lia.
apply H3. lia.
+ rewrite F5. apply Forall_forall. intros c' Hc'. apply in_map_iff in Hc' as (c & <- & Hc).
rewrite Forall_forall in H4. specialize (H4 c Hc).
intros i Hi. rewrite c_len_rebase in Hi. destruct (H4 i Hi) as (b & Hb1 & Hb2).
exists b. rewrite HB. unfold chunk_rebase; cbn [c_off c_val].
replace (base_val E (r_base r) - d + (c_off c + d)) with (base_val E (r_base r) + c_off c) by lia.
split; [|exact Hb2].
destruct (c_val c); cbn [cbyte] in Hb1 |- *; try exact Hb1.
* rewrite (sv_rebase_sound E E') by exact Hrb. exact Hb1.
* destruct Hrb as (_ & _ & HD). rewrite HD. exact Hb1.
- unfold mem_rebase. apply (pairwise_disjoint_rebase E E'); assumption.
Qed.
Definition ss_rebase (rb : rebase) (ss : sstate) (G : facts) : sstate :=
mkSST (ss_pc ss) (regs_rebase rb (ss_regs ss)) (regs_rebase rb (ss_fregs ss)) (mem_rebase rb (ss_mem ss))
(match ss_resv ss with Some a => Some (sv_rebase rb a) | None => None end) G.
Lemma st_ok_rebase : forall E E' rb ss ms G,
st_ok segs E ss ms -> rebase_ok E E' rb ->
(forall r n, In r (ss_mem ss) -> r_base r = Some n -> rebase_exact E E' rb n) ->
facts_ok E' G ->
st_ok segs E' (ss_rebase rb ss G) ms.
Proof.
intros E E' rb ss ms G (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hrb Hex HG.
unfold st_ok, ss_rebase; cbn.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
{ rewrite H4. destruct (ss_resv ss); cbn; [|reflexivity]. rewrite (sv_rebase_sound E E') by exact Hrb. reflexivity. }
split; [exact H5|]. split; [exact H6|]. split.
{ eapply regs_ok_rebase; eauto. }
split; [|exact HG]. eapply mem_ok_rebase; eauto.
Qed.
Lemma st_ok_facts : forall E ss ms G,
st_ok segs E ss ms -> facts_ok E G ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss) G) ms.
Proof.
intros E ss ms G (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HG.
unfold st_ok; cbn. repeat (split; [assumption|]). exact HG.
Qed.
Lemma st_ok_submem : forall E ss ms rs,
st_ok segs E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms rs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hs Hwf.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
eapply mem_ok_sub; eauto.
Qed.
Lemma st_ok_regs : forall E ss ms sr,
st_ok segs E ss ms -> (forall r, sv_denot E (sr_get sr r) = sv_denot E (sr_get (ss_regs ss) r)) ->
st_ok segs E (mkSS (ss_pc ss) sr (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms sr (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact (conj H8 H9)].
intros r. rewrite Hr. apply H7.
Qed.
Definition chunk_bytes (E : env) (abs : Z) (cv : cval) (k : Z) (n : nat) : list byte :=
match cv with
| CVal _ v => zbytes (bv_unsigned (sv_denot E v)) k n
| CZero _ => repeat (Z_to_bv 8 0) n
| CImg _ => map (fun i => match img_byte segs (abs + k + Z.of_nat i) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)
| CData d s _ => firstn n (skipn (Z.to_nat (s + k)) (ed E d))
end.
Lemma mem_ok_read : forall E m rs b off n r c,
mem_ok segs E m rs ->
find_region rs b off (Z.of_nat n) = Some r ->
find_chunk (r_chunks r) off (Z.of_nat n) = Some c ->
match c_val c with CData _ s _ => 0 <= s | _ => True end ->
rdn segs m (Z_to_bv 64 (base_val E b + off)) n
= Some (chunk_bytes E (base_val E b + c_off c) (c_val c) (off - c_off c) n).
Proof.
intros E m rs b off n r c HM Hfr Hfc Hs.
apply find_region_sound in Hfr as (Hrin & Hrb & Hrlo & Hrhi).
apply find_chunk_sound in Hfc as (Hcin & Hclo & Hchi).
pose proof (mem_ok_region segs E m rs r HM Hrin) as Hr.
pose proof (region_ok_chunk segs E m r c Hr Hcin) as Hc. rewrite Hrb in Hc.
set (k := off - c_off c).
destruct (c_val c) as [w cv | len | len | d s0 len] eqn:Hcv; cbn [chunk_bytes].
- rewrite zbytes_as_map. eapply chunk_read; [exact Hc| lia| lia|].
intros i Hi. rewrite Hcv. cbn [cbyte]. unfold byte_of_word. f_equal.
- replace (repeat (Z_to_bv 8 0) n) with (map (fun _ : nat => Z_to_bv 8 0) (seq 0 n))
by (rewrite map_const, length_seq; reflexivity).
eapply chunk_read; [exact Hc| lia| lia|]. intros i Hi. rewrite Hcv. reflexivity.
- eapply chunk_read; [exact Hc| lia| lia|]. intros i Hi. rewrite Hcv. cbn [cbyte].
destruct (Hc (k + Z.of_nat i) ltac:(subst k; lia)) as (b0 & Hb1 & Hb2).
rewrite Hcv in Hb1. cbn [cbyte] in Hb1.
replace (base_val E b + c_off c + (off - c_off c + Z.of_nat i)) with (base_val E b + c_off c + k + Z.of_nat i) by (subst k; lia).
replace (base_val E b + c_off c + (k + Z.of_nat i)) with (base_val E b + c_off c + k + Z.of_nat i) in Hb1 by lia.
rewrite Hb1. reflexivity.
- set (f := fun i : nat => match nth_error (ed E d) (Z.to_nat (s0 + k) + i)%nat with
| Some b0 => b0 | None => Z_to_bv 8 0 end).
assert (Hf : forall i, (i < n)%nat -> nth_error (ed E d) (Z.to_nat (s0 + k) + i)%nat = Some (f i)).
{ intros i Hi. destruct (Hc (k + Z.of_nat i) ltac:(subst k; lia)) as (b0 & Hb1 & Hb2).
rewrite Hcv in Hb1. cbn [cbyte] in Hb1.
replace (Z.to_nat (s0 + (k + Z.of_nat i))) with (Z.to_nat (s0 + k) + i)%nat in Hb1 by (subst k; lia).
unfold f. rewrite Hb1. reflexivity. }
rewrite (firstn_skipn_map n (Z.to_nat (s0 + k)) (ed E d) f Hf).
eapply chunk_read; [exact Hc| lia| lia|]. intros i Hi. rewrite Hcv. cbn [cbyte].
rewrite <- Hf by exact Hi. f_equal. subst k. lia.
Qed.
End e.
