(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0b.v (donor image sha256 1c29845fe605), with its module paths changed. *)
(* Relocated from proofs/libreac/fuzz_decode/lib/YG0b.v at 88154566652a by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan-ubsan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p YK15 YK18 YK0y YK1b YK00 YK01 YK13 YP0n YK04 YK05 YA0i YA0n YK0g. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YA05 YA09 YA08. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YA00.



From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK0c YK0e YK0f. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK09 YA0c YA0e.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YK06.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section K.
Variable segs : list Segment.
Definition grant_md (hole : bool) (flags addr n : word) (md : Model) : Model :=
if hole then with_mmap_backing flags addr n (mmap_model addr n md) else fixedin_ok_model 3 flags addr n md.
Definition cix (hole : bool) : Type := (unit + unit)%type.
Definition same_io (md md' : Model) : Prop :=
m_fd md' = m_fd md /\ m_io md' = m_io md /\ m_fsys md' = m_fsys md /\ m_proc md' = m_proc md.
Lemma same_io_refl : forall md, same_io md md. Proof. intros md. repeat split; reflexivity. Qed.
Lemma same_io_trans : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.
Lemma same_io_with_vmmaps : forall h md, same_io md (with_vmmaps h md). Proof. intros. repeat split; reflexivity. Qed.
Lemma same_io_with_vm_backing : forall l p md, same_io md (with_vm_backing l p md). Proof. intros. repeat split; reflexivity. Qed.
Lemma same_io_vm_forget_range : forall lo hi md, same_io md (vm_forget_range lo hi md). Proof. intros. apply same_io_with_vm_backing. Qed.
Lemma same_io_with_mmap_backing : forall flags a n md, same_io md (with_mmap_backing flags a n md).
Proof. intros. unfold with_mmap_backing, vm_add_lazy. destruct (mmap_noreserve_b flags); [apply same_io_with_vm_backing | apply same_io_refl]. Qed.
Lemma same_io_grant : forall hole flags addr n md, same_io md (grant_md hole flags addr n md).
Proof.
intros hole flags addr n md. unfold grant_md, fixedin_ok_model, mmap_model, with_mmap_replacement. destruct hole.
- eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_with_mmap_backing].
- eapply same_io_trans; [| apply same_io_with_mmap_backing]. eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_vm_forget_range].
Qed.
Lemma grant_md_halted : forall hole flags addr n md, m_halted (grant_md hole flags addr n md) = m_halted md.
Proof.
intros hole flags addr n md. unfold grant_md. destruct hole.
- rewrite with_mmap_backing_halted. unfold mmap_model. apply with_vmmaps_halted.
- unfold fixedin_ok_model. rewrite with_mmap_replacement_halted'. apply with_vmmaps_halted.
Qed.
Lemma page_in_subtract_false : forall l lo hi (p : word),
0 <= lo -> hi < 2 ^ 64 -> lo <= bv_unsigned p -> bv_unsigned p + page_size <= hi ->
page_in_ranges p (maps_subtract l lo hi) = false.
Proof.
intros l lo hi p Hlo Hhi H1 H2.
induction l as [|[a sz] l IH]; cbn [maps_subtract]; [reflexivity|].
unfold page_in_ranges in *. unfold page_size in *. rewrite existsb_app, IH, orb_false_r.
pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. pose proof (u64_range p) as Rp.
unfold iv_subtract. rewrite existsb_app. apply orb_false_intro.
- destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [|reflexivity]. cbn [existsb fst snd]. rewrite orb_false_r.
rewrite u64_lit by lia. apply andb_false_iff. destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); [right | left; reflexivity].
apply Z.leb_gt. lia.
- destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [|reflexivity]. cbn [existsb fst snd]. rewrite orb_false_r.
rewrite !u64_lit by lia. apply andb_false_iff. left. apply Z.leb_gt. lia.
Qed.
Definition Hcut (H : word -> bool) (lo hi : Z) : word -> bool :=
fun a => H a && negb ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi)).
Lemma Hcut_hsub : forall H lo hi, hsub (Hcut H lo hi) H.
Proof. intros H lo hi a Ha. unfold Hcut in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. Qed.
Lemma Hcut_in : forall H lo hi (a : word), lo <= bv_unsigned a < hi -> Hcut H lo hi a = false.
Proof.
intros H lo hi a Ha. unfold Hcut. replace ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi)) with true; [apply andb_false_r|].
symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma Hcut_off : forall H lo hi, H_off_segments segs H -> H_off_segments segs (Hcut H lo hi).
Proof. intros H lo hi HO a Ha. apply HO. exact (Hcut_hsub H lo hi a Ha). Qed.
Definition wexpose (W : world segs) (lo hi : Z) : world segs :=
mkW segs (Hcut (w_H W) lo hi) (w_A W) (Hcut_off (w_H W) lo hi (w_Hoff W)) (w_Awf W).
Lemma wexpose_wle : forall W lo hi, wle W (wexpose W lo hi).
Proof. intros W lo hi. unfold wle, wexpose. cbn [w_H]. apply Hcut_hsub. Qed.
Lemma grant_md_lazy : forall hole flags addr n md, mmap_noreserve_b flags = false ->
m_vm_lazy (grant_md hole flags addr n md) =
if hole then m_vm_lazy md else maps_subtract (m_vm_lazy md) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof.
intros hole flags addr n md Hnr. unfold grant_md, fixedin_ok_model, mmap_model, with_mmap_replacement, with_mmap_backing. rewrite Hnr.
destruct hole; reflexivity.
Qed.
Theorem commit_expose : forall (W : world segs) md (hole : bool) (flags addr n : word) mem,
mmap_noreserve_b flags = false ->
bv_unsigned addr mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> bv_unsigned addr + bv_unsigned n < 2 ^ 64 ->
(hole = true -> forall p : word, bv_unsigned addr <= bv_unsigned p -> bv_unsigned p + page_size <= bv_unsigned addr + bv_unsigned n ->
page_in_ranges p (m_vm_lazy md) = false) ->
AI segs (w_H W) (w_A W) (grant_md hole flags addr n md) ->
let W2 := wexpose W (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) in
wle W W2 /\ w_A W2 = w_A W /\ (forall a : word, bv_unsigned addr <= bv_unsigned a < bv_unsigned addr + bv_unsigned n -> w_H W2 a = false) /\
(forall a : word, w_H W a = false -> w_H W2 a = false) /\
AI segs (w_H W2) (w_A W2) (grant_md hole flags addr n md) /\
(forall a, bv_unsigned addr <= a < bv_unsigned addr + bv_unsigned n ->
apresent (w_H W2) (zfill addr n mem) a /\ zfill addr n mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
Proof.
intros W md hole flags addr n mem Hnr Hal Hnl Hhi Hhole HAI. cbn zeta.
pose proof (u64_range addr) as Ra. pose proof (u64_range n) as Rn.
split; [apply wexpose_wle|]. split; [reflexivity|].
split; [intros a Ha; unfold wexpose; cbn [w_H]; apply Hcut_in; exact Ha|].
split; [intros a Ha; unfold wexpose, Hcut; cbn [w_H]; rewrite Ha; reflexivity|].
split.
- unfold wexpose. cbn [w_H w_A]. apply (AI_hsub segs (w_H W)); [exact HAI | apply Hcut_hsub|].
intros w Hw Hw' Hl. exfalso. unfold Hcut in Hw'. rewrite Hw in Hw'. cbn [andb] in Hw'. apply negb_false_iff in Hw'.
apply andb_prop in Hw' as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
pose proof (u64_range w) as Rw. unfold page_size in *.
assert (PB : bv_unsigned (page_base w) = bv_unsigned w / 4096 * 4096).
{ unfold page_base, page_base_of, page_size. apply u64_lit. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia] |].
pose proof (Z.mul_div_le (bv_unsigned w) 4096 ltac:(lia)). lia. }
assert (B1 : bv_unsigned addr <= bv_unsigned (page_base w)).
{ rewrite PB. apply Z.mod_divide in Hal as [q Hq]; [|lia]. rewrite Hq in L1 |- *.
assert (q <= bv_unsigned w / 4096) by (apply Z.div_le_lower_bound; lia). nia. }
assert (B2 : bv_unsigned (page_base w) + 4096 <= bv_unsigned addr + bv_unsigned n).
{ rewrite PB. apply Z.mod_divide in Hal as [q Hq]; [|lia]. apply Z.mod_divide in Hnl as [r Hr]; [|lia]. rewrite Hq, Hr in L2 |- *.
assert (bv_unsigned w / 4096 < q + r) by (apply Z.div_lt_upper_bound; lia). nia. }
rewrite (grant_md_lazy hole flags addr n md Hnr) in Hl. destruct hole.
+ rewrite (Hhole eq_refl (page_base w) B1 B2) in Hl. discriminate Hl.
+ rewrite (page_in_subtract_false (m_vm_lazy md) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (page_base w) ltac:(lia) Hhi B1 B2) in Hl. discriminate Hl.
- intros a Ha. pose proof (zfill_in addr n mem (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; lia)) as Z0. split; [| exact Z0].
split; [| exists (Z_to_bv 8 0); exact Z0]. unfold wexpose. cbn [w_H]. apply Hcut_in. rewrite u64_lit by lia. lia.
Qed.
Definition MWF (md : Model) : Prop := model_ivs_wf md /\ seps (vm_maps (m_vmmaps md)).
Lemma MWF_same_but_materialized : forall md md', MWF md -> same_but_materialized md md' -> MWF md'.
Proof.
intros md md' [(W1 & W2 & W3 & W4) Ws] Hs. pose proof (same_but_materialized_frame md md' Hs) as (_ & Hv & Hl & _).
unfold MWF, model_ivs_wf. rewrite Hv, Hl. repeat split; assumption.
Qed.
Lemma pairwise_seps : forall l,
pairwise (fun p q : word * word => bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p)) l <-> seps l.
Proof.
induction l as [|x l IH]; cbn.
- split; [intros _; constructor | intros _; exact I].
- split.
+ intros [F P]. constructor; [| apply IH; exact P]. apply Forall_impl with (2 := F). intros q Hq. exact Hq.
+ intros Hs. inversion Hs as [| p l' F P]; subst. split; [| apply IH; exact P]. apply Forall_impl with (2 := F). intros q Hq. exact Hq.
Qed.
Lemma amwf_MWF_sp : forall md, YK06.init_sp_ok (m_vmmaps md) -> (amwf_ivs md <-> MWF md).
Proof.
intros md Hsp. unfold amwf_ivs, MWF, model_ivs_wf, ivs_wf, iv_wf, B, YK0g.S. rewrite pairwise_seps. tauto.
Qed.
Lemma amwf_MWF : forall md, amwf_ivs md <-> MWF md.
Proof.
intros md. unfold amwf_ivs, MWF, model_ivs_wf, ivs_wf, iv_wf, B, YK0g.S. rewrite pairwise_seps. tauto.
Qed.
Definition maps_nonempty (md : Model) : Prop := forall q, In q (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned (snd q).
Lemma cn_iv_subtract_nonempty : forall (a sz : word) lo hi q, 0 < bv_unsigned sz -> In q (iv_subtract a sz lo hi) -> 0 < bv_unsigned (snd q).
Proof.
intros a sz lo hi q Hsz Hq. pose proof (u64_range a). pose proof (u64_range sz). unfold iv_subtract in Hq.
apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
- destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [snd]. rewrite u64_lit by lia. lia.
- destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [snd]. rewrite u64_lit by lia. lia.
Qed.
Lemma cn_maps_subtract_nonempty : forall l lo hi, (forall q, In q l -> 0 < bv_unsigned (snd q)) ->
forall q, In q (maps_subtract l lo hi) -> 0 < bv_unsigned (snd q).
Proof.
induction l as [|[a sz] l IH]; intros lo hi Hl q Hq; [destruct Hq|]. cbn [maps_subtract] in Hq. apply in_app_iff in Hq as [Hq|Hq].
- apply (cn_iv_subtract_nonempty a sz lo hi q); [exact (Hl (a, sz) (or_introl eq_refl)) | exact Hq].
- apply (IH lo hi); [intros q' Hq'; apply Hl; right; exact Hq' | exact Hq].
Qed.
Theorem commit_nonempty : forall (hole : bool) (flags addr n : word) md,
0 < bv_unsigned n -> maps_nonempty md ->
maps_nonempty (grant_md hole flags addr n md).
Proof.
intros hole flags addr n md Hn H.
unfold grant_md. destruct hole.
+ unfold with_mmap_backing. destruct (mmap_noreserve_b flags); unfold mmap_model, maps_nonempty; model_proj; cbn [vm_maps];
(intros q [<-|Hq]; [exact Hn | exact (H q Hq)]).
+ unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb Pos.eqb].
destruct (mmap_noreserve_b flags); unfold maps_nonempty; model_proj; unfold mmap_fixed_rw_next; cbn [vm_maps]; exact H.
Qed.
Lemma eager_used_sem : forall m, model_ivs_wf m ->
eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
intros m Hwf. pose proof (vm_backing_used_sem m Hwf) as X. rewrite vm_backing_used_split in X. lia.
Qed.
Lemma iv_count_le_S : forall P p, iv_count P p <= YK0g.S p.
Proof. intros P p. unfold iv_count. pose proof (zcount_le_len P (B p) (Z.to_nat (YK0g.S p))). pose proof (S_range p). lia. Qed.
Lemma map_contains_In : forall l (lo n : word), map_contains l lo n = true ->
exists q, In q l /\ B q <= bv_unsigned lo /\ bv_unsigned lo + bv_unsigned n <= B q + YK0g.S q.
Proof.
intros l lo n H. unfold map_contains in H. apply existsb_exists in H as (q & Hin & Hq).
apply andb_prop in Hq as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists q. unfold B, YK0g.S. split; [exact Hin | lia].
Qed.
Lemma overlap_sum_seps_contains : forall l (lo n : word),
seps l -> 0 < bv_unsigned n -> map_contains l lo n = true ->
overlap_sum l (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) <= bv_unsigned n.
Proof.
intros l lo n Hs Hn. induction Hs as [| p l Hd Hs IH]; intros Hc; [discriminate Hc|].
rewrite overlap_sum_cons. unfold map_contains in Hc. cbn [existsb] in Hc. fold (map_contains l lo n) in Hc.
apply Bool.orb_prop in Hc as [Hp | Hl].
- apply andb_prop in Hp as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite (overlap_sum_region_free l lo n).
+ pose proof (iv_count_in_rng_le p (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) ltac:(lia)). lia.
+ apply region_free_intro. intros a sz Hin. pose proof (proj1 (Forall_forall _ _) Hd _ Hin) as D. unfold iv_disjoint in D. cbn [fst snd] in D.
unfold iv_overlap. apply andb_false_iff. destruct D as [D|D]; [right | left]; apply Z.ltb_ge; lia.
- destruct (map_contains_In l lo n Hl) as (q & Hq & Q1 & Q2).
pose proof (proj1 (Forall_forall _ _) Hd _ Hq) as D. unfold iv_disjoint in D. unfold B, YK0g.S in Q1, Q2.
rewrite iv_count_in_rng_disjoint by (unfold B, YK0g.S; lia). specialize (IH Hl). lia.
Qed.
Lemma page_in_subtract_back : forall l lo hi (p : word),
0 <= lo -> hi < 2 ^ 64 -> ivs_wf l -> page_in_ranges p (maps_subtract l lo hi) = true -> page_in_ranges p l = true.
Proof.
intros l lo hi p Hlo Hhi Hwf H. unfold page_in_ranges in *. apply existsb_exists in H as (q & Hin & Hq).
destruct (maps_subtract_pieces l lo hi q Hwf Hin) as (r & Hr & R1 & R2 & _).
apply existsb_exists. exists r. split; [exact Hr|]. apply andb_prop in Hq as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2.
apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma page_in_subtract_keep : forall l lo hi (p : word),
0 <= lo -> hi < 2 ^ 64 -> lo <= hi -> ivs_wf l ->
(bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
page_in_ranges p l = true -> page_in_ranges p (maps_subtract l lo hi) = true.
Proof.
intros l lo hi p Hlo Hhi Hlh Hwf Hout H. pose proof (u64_range p) as Rp.
induction l as [|[a sz] l IH]; [discriminate H|]. apply ivs_wf_cons_inv in Hwf as [Ha Hl].
unfold page_in_ranges in H |- *. cbn [existsb maps_subtract] in H |- *. rewrite existsb_app.
fold (page_in_ranges p l) in H. fold (page_in_ranges p (maps_subtract l lo hi)).
apply Bool.orb_prop in H as [H | H]; [| rewrite (IH Hl H); apply orb_true_r]. unfold page_size in *.
apply andb_prop in H as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. cbn [fst snd] in A1, A2.
unfold iv_wf, B, YK0g.S in Ha. cbn [fst snd] in Ha. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
apply orb_true_iff. left. unfold iv_subtract. rewrite existsb_app. apply orb_true_iff. destruct Hout as [Hout | Hout].
- left. destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [| exfalso; lia]. cbn [existsb fst snd].
rewrite u64_lit by lia. rewrite orb_false_r. apply andb_true_iff. split; apply Z.leb_le; lia.
- right. destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [| exfalso; lia]. cbn [existsb fst snd].
rewrite !u64_lit by lia. rewrite orb_false_r. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma seps_app : forall l1 l2, seps l1 -> seps l2 -> (forall p q, In p l1 -> In q l2 -> iv_disjoint p q) -> seps (l1 ++ l2).
Proof.
induction l1 as [|p l1 IH]; intros l2 H1 H2 Hx; cbn; [exact H2|].
inversion H1 as [| p' l' Hd Hs]; subst. apply seps_cons.
- apply Forall_app. split; [exact Hd|]. apply Forall_forall. intros q Hq. apply Hx; [left; reflexivity | exact Hq].
- apply IH; [exact Hs | exact H2 |]. intros a b Ha Hb. apply Hx; [right; exact Ha | exact Hb].
Qed.
Lemma iv_subtract_seps : forall (a sz : word) lo hi, 0 <= lo <= hi -> hi < 2 ^ 64 -> seps (iv_subtract a sz lo hi).
Proof.
intros a sz lo hi Hlh Hhi. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; cbn [app];
repeat (apply seps_cons; [| try apply seps_nil]); try apply Forall_nil; try apply seps_nil.
apply Forall_cons; [| apply Forall_nil]. unfold iv_disjoint. cbn [fst snd]. left.
rewrite !u64_lit by lia. lia.
Qed.
Lemma seps_maps_subtract : forall l lo hi, ivs_wf l -> 0 <= lo <= hi -> hi < 2 ^ 64 -> seps l -> seps (maps_subtract l lo hi).
Proof.
intros l lo hi Hwf Hlh Hhi Hs. induction Hs as [| p l Hd Hs IH]; cbn [maps_subtract]; [apply seps_nil|].
apply ivs_wf_cons_inv in Hwf as [Hp Hl]. destruct p as [a sz]. apply seps_app; [apply iv_subtract_seps; [exact Hlh | exact Hhi] | exact (IH Hl) |].
intros q r Hq Hr. destruct (iv_subtract_pieces a sz lo hi q Hp Hq) as (Q1 & Q2 & _).
destruct (maps_subtract_pieces l lo hi r Hl Hr) as (r0 & Hr0 & R1 & R2 & _).
pose proof (proj1 (Forall_forall _ _) Hd _ Hr0) as D. unfold iv_disjoint in D |- *. cbn [fst snd] in D. lia.
Qed.
Lemma page_round_up_Z_mod : forall z, page_round_up_Z z mod page_size = 0.
Proof. intros z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma AI_forget : forall (Hh : word -> bool) A md md' lo hi,
AI segs Hh A md -> ivs_wf (m_vm_lazy md) ->
0 <= lo <= hi -> hi < 2 ^ 64 -> lo mod page_size = 0 -> hi mod page_size = 0 ->
m_halted md' = None ->
m_vm_lazy md' = maps_subtract (m_vm_lazy md) lo hi ->
m_vm_materialized md' = List.filter (page_outside_range lo hi) (m_vm_materialized md) ->
eager_used md' + A_bytes A <= vm_limit (m_vmmaps md') ->
AI segs Hh A md'.
Proof.
intros Hh A md md' lo hi (H1 & H2 & H3 & H4 & H5) Wl Hlh Hhi Hlo Hhm Hh' Hl' Hm' Hb.
split; [exact H1|]. split; [exact H2|]. split.
- intros w Hl Hw. rewrite Hl' in Hl. apply (H3 w); [| exact Hw]. exact (page_in_subtract_back _ lo hi _ ltac:(lia) Hhi Wl Hl).
- split; [| exact Hh']. destruct H4 as [N1 N2 N3 N4 N5]. constructor; rewrite ?Hm', ?Hl'.
+ apply NoDup_filter. exact N1.
+ intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
+ intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
+ intros p Hp. apply filter_In in Hp as [Hp Ho]. pose proof (N2 p Hp) as Hal. pose proof (N4 p Hp) as Hpl.
apply page_in_subtract_keep; [lia | exact Hhi | lia | exact Wl | | exact Hpl].
unfold page_outside_range in Ho. apply negb_true_iff in Ho. apply andb_false_iff in Ho. unfold page_size in *.
pose proof (u64_range p) as Rp.
apply Z.mod_divide in Hal as [q Hq]; [|lia]. apply Z.mod_divide in Hlo as [ql Hql]; [|lia]. apply Z.mod_divide in Hhm as [qh Hqh]; [|lia].
destruct Ho as [Ho | Ho]; [apply Z.leb_gt in Ho; left | apply Z.ltb_ge in Ho; right; exact Ho]. rewrite Hq, Hql in *. nia.
+ exact Hb.
Qed.
Lemma mat_le_A : forall (Hh : word -> bool) A md, AI segs Hh A md -> Z.of_nat (length (m_vm_materialized md)) * page_size <= A_bytes A.
Proof.
intros Hh A md (_ & Hwf & _ & [N1 N2 N3 _ _] & _). exact (allowed_pages_bound A _ Hwf N1 N2 N3).
Qed.
Theorem commit_AI : forall (Hh : word -> bool) A md (hole : bool) (flags addr : word) (len : Z),
AI segs Hh A md -> MWF md -> mmap_noreserve_b flags = false ->
bv_unsigned addr mod page_size = 0 -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps md) ->
let n := Z_to_bv 64 (page_round_up_Z len) in
(if hole then region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) addr n = true
else region_free (vm_reserved (m_vmmaps md)) addr n = true /\ map_contains (vm_maps (m_vmmaps md)) addr n = true) ->
eager_used md + A_bytes A + page_round_up_Z len <= vm_limit (m_vmmaps md) ->
(AI segs Hh A (grant_md hole flags addr n md) /\ MWF (grant_md hole flags addr n md)) /\
(if hole then mmap_noreserve_backed_ok flags md (page_round_up_Z len) = true else mmap_fixed_rw_budget_ok flags md addr n = true).
Proof.
intros Hh A md hole flags addr len HAI HW Hnr Hal Hlen Hce n Hplace Hslack.
pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv. pose proof (u64_range addr) as Ra.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PR. pose proof (page_round_up_Z_mod len) as PM. unfold page_size in PR, PM.
assert (Un : bv_unsigned n = page_round_up_Z len) by (unfold n; apply u64_lit; lia).
pose proof HW as [(Wm & Wn & Wl & Wi) Ws]. pose proof HAI as (HH1 & HH2 & HH3 & HH4 & HH5).
set (lo := bv_unsigned addr) in *. set (hi := lo + bv_unsigned n).
assert (Hlh : 0 <= lo <= hi) by (subst hi; rewrite Un; lia). assert (Hhi : hi < 2 ^ 64) by (subst hi; rewrite Un; lia).
assert (Hhm : hi mod 4096 = 0).
{ subst hi. rewrite Un. unfold page_size in Hal. apply Z.mod_divide in Hal as [q Hq]; [|lia]. apply Z.mod_divide in PM as [r Hr]; [|lia].
rewrite Hq, Hr. apply Z.mod_divide; [lia|]. exists (q + r). lia. }
pose proof (eager_used_sem md (conj Wm (conj Wn (conj Wl Wi)))) as EQ0.
assert (E_piece : hole = false -> eager_used (vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)) <= eager_used md + bv_unsigned n).
{ intros Eh. rewrite Eh in Hplace. destruct Hplace as [_ Hmc].
assert (W' : model_ivs_wf (vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md))).
{ apply model_ivs_wf_vm_forget_range; [lia|]. apply model_ivs_wf_with_vmmaps; [exact (conj Wm (conj Wn (conj Wl Wi))) | exact Wm | | reflexivity].
unfold mmap_fixed_rw_next. cbn [vm_noaccess]. apply maps_subtract_wf; [exact Wn | lia]. }
rewrite (eager_used_sem _ W'), EQ0. model_proj. unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess]. fold lo. fold hi.
destruct (maps_subtract_sem (vm_noaccess (m_vmmaps md)) lo hi Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem (m_vm_lazy md) lo hi Wl ltac:(lia)) as (_ & _ & Cl).
eapply Z.le_trans.
{ apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) || in_rng lo hi x)).
intros x. rewrite !covered_app, Cn, Cl. destruct (covered (vm_noaccess (m_vmmaps md)) x), (covered (m_vm_lazy md) x), (in_rng lo hi x); cbn; congruence. }
pose proof (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x)) (in_rng lo hi) (vm_maps (m_vmmaps md))) as X.
pose proof (overlap_sum_seps_contains (vm_maps (m_vmmaps md)) addr n Ws ltac:(rewrite Un; lia) Hmc) as Y. unfold overlap_sum in Y. fold lo in Y. fold hi in Y. cbn beta in X. lia. }
assert (E_hole : hole = true -> eager_used (mmap_model addr n md) <= eager_used md + bv_unsigned n).
{ intros Eh. assert (W' : model_ivs_wf (mmap_model addr n md)).
{ unfold mmap_model. apply model_ivs_wf_with_vmmaps; [exact (conj Wm (conj Wn (conj Wl Wi))) | | exact Wn | reflexivity]. cbn [vm_maps].
apply ivs_wf_cons; [| exact Wm]. unfold iv_wf, B, YK0g.S. cbn [fst snd]. fold lo. lia. }
rewrite (eager_used_sem _ W'), EQ0. unfold mmap_model. model_proj. cbn [vm_maps vm_noaccess sum_count].
pose proof (iv_count_le_S (fun x => negb (covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x)) (addr, n)) as X.
unfold YK0g.S in X. cbn [snd] in X. lia. }
pose proof (mat_le_A Hh A md HAI) as MA. unfold page_size in MA.
split.
-   unfold grant_md. destruct hole.
+
assert (Em : with_mmap_backing flags addr n (mmap_model addr n md) = mmap_model addr n md) by (unfold with_mmap_backing; rewrite Hnr; reflexivity).
rewrite Em. split.
* apply (AI_transport segs Hh A md); [exact HAI | reflexivity | reflexivity | unfold mmap_model; rewrite with_vmmaps_halted; exact HH5 |].
unfold mmap_model at 2. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit]. pose proof (E_hole eq_refl). lia.
* split.
-- unfold mmap_model. apply model_ivs_wf_with_vmmaps; [exact (conj Wm (conj Wn (conj Wl Wi))) | | exact Wn | reflexivity]. cbn [vm_maps].
apply ivs_wf_cons; [| exact Wm]. unfold iv_wf, B, YK0g.S. cbn [fst snd]. fold lo. lia.
-- unfold mmap_model. rewrite m_vmmaps_with_vmmaps. cbn [vm_maps]. apply seps_cons; [| exact Ws].
rewrite YK13.region_free_app in Hplace. apply andb_true_iff in Hplace as [_ Hrf].
apply Forall_forall. intros [a sz] Hin. unfold iv_disjoint. cbn [fst snd].
assert (X : iv_overlap addr n a sz = false).
{ clear - Hrf Hin. induction (vm_maps (m_vmmaps md)) as [|[b s] l IH]; [destruct Hin|]. cbn [region_free] in Hrf.
apply andb_true_iff in Hrf as [H1 H2]. destruct Hin as [Heq | Hin]; [injection Heq as -> ->; apply negb_true_iff in H1; exact H1 | exact (IH H2 Hin)]. }
unfold iv_overlap in X. apply andb_false_iff in X as [X|X]; apply Z.ltb_ge in X; fold lo in X; lia.
+
assert (Em : fixedin_ok_model 3 flags addr n md = vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)).
{ unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite Hnr. cbn [Z.eqb]. reflexivity. }
rewrite Em. split.
* apply (AI_forget Hh A md _ lo hi HAI Wl Hlh Hhi Hal Hhm).
-- reflexivity || exact HH5.
-- reflexivity.
-- reflexivity.
-- pose proof (E_piece eq_refl) as EP. revert EP. model_proj. unfold mmap_fixed_rw_next. cbn [vm_limit]. intros EP. lia.
* split.
-- apply model_ivs_wf_vm_forget_range; [lia|]. apply model_ivs_wf_with_vmmaps; [exact (conj Wm (conj Wn (conj Wl Wi))) | exact Wm | | reflexivity].
unfold mmap_fixed_rw_next. cbn [vm_noaccess]. apply maps_subtract_wf; [exact Wn | lia].
-- model_proj. unfold mmap_fixed_rw_next. cbn [vm_maps]. exact Ws.
-   destruct hole.
+ unfold mmap_noreserve_backed_ok. rewrite Hnr. apply Z.leb_le. rewrite vm_backing_used_split. unfold page_size. lia.
+ unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit. apply Z.leb_le.
assert (Em : with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md) =
vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)).
{ unfold with_mmap_replacement, with_mmap_backing. rewrite Hnr. reflexivity. }
rewrite Em, vm_backing_used_split. pose proof (E_piece eq_refl) as EP.
assert (ML : Z.of_nat (length (m_vm_materialized (vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)))) <=
Z.of_nat (length (m_vm_materialized md))).
{ model_proj. pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized md)). lia. }
model_proj. unfold mmap_fixed_rw_next in *. cbn [vm_limit] in *. revert EP ML. model_proj. cbn [vm_limit]. unfold page_size. intros EP ML. nia.
Qed.
Theorem commit_eager : forall (Hh : word -> bool) A md (hole : bool) (flags addr : word) (len : Z),
AI segs Hh A md -> MWF md -> mmap_noreserve_b flags = false ->
bv_unsigned addr mod page_size = 0 -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps md) ->
let n := Z_to_bv 64 (page_round_up_Z len) in
(if hole then region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) addr n = true
else region_free (vm_reserved (m_vmmaps md)) addr n = true /\ map_contains (vm_maps (m_vmmaps md)) addr n = true) ->
eager_used md + A_bytes A + page_round_up_Z len <= vm_limit (m_vmmaps md) ->
eager_used (grant_md hole flags addr n md) <= eager_used md + page_round_up_Z len.
Proof.
intros Hh A md hole flags addr len HAI HW Hnr Hal Hlen Hce n Hplace Hslack.
pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv. pose proof (u64_range addr) as Ra.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PR. pose proof (page_round_up_Z_mod len) as PM. unfold page_size in PR, PM.
assert (Un : bv_unsigned n = page_round_up_Z len) by (unfold n; apply u64_lit; lia).
pose proof HW as [(Wm & Wn & Wl & Wi) Ws]. pose proof HAI as (HH1 & HH2 & HH3 & HH4 & HH5).
set (lo := bv_unsigned addr) in *. set (hi := lo + bv_unsigned n).
assert (Hlh : 0 <= lo <= hi) by (subst hi; rewrite Un; lia). assert (Hhi : hi < 2 ^ 64) by (subst hi; rewrite Un; lia).
assert (Hhm : hi mod 4096 = 0).
{ subst hi. rewrite Un. unfold page_size in Hal. apply Z.mod_divide in Hal as [q Hq]; [|lia]. apply Z.mod_divide in PM as [r Hr]; [|lia].
rewrite Hq, Hr. apply Z.mod_divide; [lia|]. exists (q + r). lia. }
pose proof (eager_used_sem md (conj Wm (conj Wn (conj Wl Wi)))) as EQ0.
assert (E_piece : hole = false -> eager_used (vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)) <= eager_used md + bv_unsigned n).
{ intros Eh. rewrite Eh in Hplace. destruct Hplace as [_ Hmc].
assert (W' : model_ivs_wf (vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md))).
{ apply model_ivs_wf_vm_forget_range; [lia|]. apply model_ivs_wf_with_vmmaps; [exact (conj Wm (conj Wn (conj Wl Wi))) | exact Wm | | reflexivity].
unfold mmap_fixed_rw_next. cbn [vm_noaccess]. apply maps_subtract_wf; [exact Wn | lia]. }
rewrite (eager_used_sem _ W'), EQ0. model_proj. unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess]. fold lo. fold hi.
destruct (maps_subtract_sem (vm_noaccess (m_vmmaps md)) lo hi Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem (m_vm_lazy md) lo hi Wl ltac:(lia)) as (_ & _ & Cl).
eapply Z.le_trans.
{ apply (sum_count_mono _ (fun x => negb (covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) || in_rng lo hi x)).
intros x. rewrite !covered_app, Cn, Cl. destruct (covered (vm_noaccess (m_vmmaps md)) x), (covered (m_vm_lazy md) x), (in_rng lo hi x); cbn; congruence. }
pose proof (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x)) (in_rng lo hi) (vm_maps (m_vmmaps md))) as X.
pose proof (overlap_sum_seps_contains (vm_maps (m_vmmaps md)) addr n Ws ltac:(rewrite Un; lia) Hmc) as Y. unfold overlap_sum in Y. fold lo in Y. fold hi in Y. cbn beta in X. lia. }
assert (E_hole : hole = true -> eager_used (mmap_model addr n md) <= eager_used md + bv_unsigned n).
{ intros Eh. assert (W' : model_ivs_wf (mmap_model addr n md)).
{ unfold mmap_model. apply model_ivs_wf_with_vmmaps; [exact (conj Wm (conj Wn (conj Wl Wi))) | | exact Wn | reflexivity]. cbn [vm_maps].
apply ivs_wf_cons; [| exact Wm]. unfold iv_wf, B, YK0g.S. cbn [fst snd]. fold lo. lia. }
rewrite (eager_used_sem _ W'), EQ0. unfold mmap_model. model_proj. cbn [vm_maps vm_noaccess sum_count].
pose proof (iv_count_le_S (fun x => negb (covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x)) (addr, n)) as X.
unfold YK0g.S in X. cbn [snd] in X. lia. }
unfold grant_md. destruct hole.
+ assert (Em : with_mmap_backing flags addr n (mmap_model addr n md) = mmap_model addr n md) by (unfold with_mmap_backing; rewrite Hnr; reflexivity).
rewrite Em, <- Un. exact (E_hole eq_refl).
+ assert (Em : fixedin_ok_model 3 flags addr n md = vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)).
{ unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite Hnr. cbn [Z.eqb]. reflexivity. }
rewrite Em, <- Un. exact (E_piece eq_refl).
Qed.
Lemma A_wf_cons : forall A slo shi, A_wf A -> slo <= shi -> slo mod page_size = 0 -> shi mod page_size = 0 -> A_wf ((slo, shi) :: A).
Proof. intros A slo shi HA H1 H2 H3. apply Forall_cons; [cbn [fst snd]; repeat split; assumption | exact HA]. Qed.
Definition wallow (W : world segs) (slo shi : Z) (H1 : slo <= shi) (H2 : slo mod page_size = 0) (H3 : shi mod page_size = 0) : world segs :=
mkW segs (Hcut (w_H W) slo shi) ((slo, shi) :: w_A W) (Hcut_off (w_H W) slo shi (w_Hoff W)) (A_wf_cons (w_A W) slo shi (w_Awf W) H1 H2 H3).
Theorem allow_expose : forall (W : world segs) md slo shi (H1 : slo <= shi) (H2 : slo mod page_size = 0) (H3 : shi mod page_size = 0),
AI segs (w_H W) (w_A W) md ->
eager_used md + A_bytes (w_A W) + (shi - slo) <= vm_limit (m_vmmaps md) ->
let W3 := wallow W slo shi H1 H2 H3 in
wle W W3 /\ w_A W3 = (slo, shi) :: w_A W /\ A_bytes (w_A W3) = (shi - slo) + A_bytes (w_A W) /\
(forall a : word, slo <= bv_unsigned a < shi -> w_H W3 a = false) /\ (forall a : word, w_H W a = false -> w_H W3 a = false) /\
AI segs (w_H W3) (w_A W3) md.
Proof.
intros W md slo shi H1 H2 H3 HAI Hb. cbn zeta.
split; [unfold wle, wallow; cbn [w_H]; apply Hcut_hsub|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros a Ha; unfold wallow; cbn [w_H]; apply Hcut_in; exact Ha|].
split; [intros a Ha; unfold wallow, Hcut; cbn [w_H]; rewrite Ha; reflexivity|].
unfold wallow. cbn [w_H w_A].
assert (HAI2 : AI segs (w_H W) ((slo, shi) :: w_A W) md).
{ change ((slo, shi) :: w_A W) with ([(slo, shi)] ++ w_A W). apply AI_grow_A; [exact HAI | | cbn [A_bytes fst snd]; lia].
apply A_wf_cons; [apply Forall_nil | exact H1 | exact H2 | exact H3]. }
apply (AI_hsub segs (w_H W)); [exact HAI2 | apply Hcut_hsub|].
intros w Hw Hw' Hl. unfold Hcut in Hw'. rewrite Hw in Hw'. cbn [andb] in Hw'. apply negb_false_iff in Hw'.
apply andb_prop in Hw' as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
unfold page_allowedb. cbn [existsb fst snd]. apply orb_true_iff. left.
pose proof (u64_range w) as Rw. unfold page_size in *.
assert (PB : bv_unsigned (page_base w) = bv_unsigned w / 4096 * 4096).
{ unfold page_base, page_base_of, page_size. apply u64_lit. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia] |].
pose proof (Z.mul_div_le (bv_unsigned w) 4096 ltac:(lia)). lia. }
rewrite PB. apply andb_true_iff. split; [apply Z.leb_le | apply Z.leb_le].
- apply Z.mod_divide in H2 as [q Hq]; [|lia]. rewrite Hq in L1 |- *. assert (q <= bv_unsigned w / 4096) by (apply Z.div_le_lower_bound; lia). nia.
- apply Z.mod_divide in H3 as [r Hr]; [|lia]. rewrite Hr in L2 |- *. assert (bv_unsigned w / 4096 < r) by (apply Z.div_lt_upper_bound; lia). nia.
Qed.
End K.
End c.
