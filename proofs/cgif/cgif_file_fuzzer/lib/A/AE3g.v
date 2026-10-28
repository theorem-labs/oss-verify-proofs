(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK18 YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE3e AE3f AF0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable segs : list Segment.
Definition chunk_out (lo hi : Z) (c : chunk) : bool := (c_off c + c_len c <=? lo) || (hi <=? c_off c).
Fixpoint forget_win (rs : smem) (i : nat) (lo hi : Z) : smem :=
match rs, i with
| [], _ => []
| r :: rs', O => keep_chunks (chunk_out lo hi) r :: rs'
| r :: rs', S i' => r :: forget_win rs' i' lo hi
end.
Lemma submem_forget_win : forall rs i lo hi, submem (forget_win rs i lo hi) rs.
Proof.
induction rs as [|r rs IH]; intros i lo hi; cbn; [constructor|].
destruct i as [|i].
- apply submem_keep; [apply subregion_keep_chunks | apply submem_refl].
- apply submem_keep; [apply subregion_refl | apply IH].
Qed.
Lemma regions_wf_forget_win : forall rs i lo hi, regions_wf rs = true -> regions_wf (forget_win rs i lo hi) = true.
Proof.
induction rs as [|r rs IH]; intros i lo hi H; cbn; [reflexivity|].
cbn in H. apply andb_prop in H as [Hr Hrs].
destruct i as [|i]; cbn.
- pose proof (regions_wf_clean_head (chunk_out lo hi) (r :: rs)) as W. cbn in W.
rewrite Hr, Hrs in W. specialize (W eq_refl). apply andb_prop in W as [W _]. rewrite W, Hrs. reflexivity.
- rewrite Hr. apply IH. exact Hrs.
Qed.
Lemma mem_ok_forget_win : forall E m rs i lo hi,
mem_ok segs E m rs -> mem_ok segs E m (forget_win rs i lo hi).
Proof.
intros E m rs i lo hi HM. apply (mem_ok_sub segs E m rs); [apply submem_forget_win| |exact HM].
apply regions_wf_forget_win. exact (proj1 HM).
Qed.
Lemma nth_error_forget_win : forall rs i lo hi r,
nth_error rs i = Some r -> nth_error (forget_win rs i lo hi) i = Some (keep_chunks (chunk_out lo hi) r).
Proof.
induction rs as [|x rs IH]; intros i lo hi r H; [destruct i; discriminate|].
destruct i as [|i]; cbn in H |- *; [injection H as ->; reflexivity| apply IH; exact H].
Qed.
Lemma chunk_ok_same : forall E (m m' : word -> option byte) base c,
chunk_ok segs E m base c ->
(forall i, 0 <= i < c_len c -> m' (Z_to_bv 64 (base + c_off c + i)) = m (Z_to_bv 64 (base + c_off c + i))) ->
chunk_ok segs E m' base c.
Proof.
intros E m m' base c H Hs i Hi. destruct (H i Hi) as (b & H1 & H2). exists b. split; [exact H1|].
unfold mbyte in *. rewrite (Hs i Hi). exact H2.
Qed.
Lemma nth_error_split' : forall {A} (l : list A) i x,
nth_error l i = Some x -> l = firstn i l ++ x :: skipn (S i) l.
Proof.
intros A l. induction l as [|a l IH]; intros i x H; [destruct i; discriminate|].
destruct i as [|i]; cbn in H |- *; [injection H as ->; reflexivity|].
f_equal. apply IH. exact H.
Qed.
Lemma mem_ok_window_change : forall E m m' rs i r lo hi,
mem_ok segs E m rs -> nth_error rs i = Some r ->
r_lo r <= lo -> lo <= hi -> hi <= r_hi r ->
(forall c, In c (r_chunks r) -> chunk_out lo hi c = true) ->
(forall x : word, ~ (base_val E (r_base r) + lo <= bv_unsigned x < base_val E (r_base r) + hi) -> m' x = m x) ->
(forall x : word, base_val E (r_base r) + lo <= bv_unsigned x < base_val E (r_base r) + hi -> wview segs m' x <> None) ->
mem_ok segs E m' rs.
Proof.
intros E m m' rs i r lo hi (Hwf & Hok & Hpd) Hi Hlo Hlh Hhi Hcs Hout Hdef.
split; [exact Hwf|]. split; [|exact Hpd].
pose proof (nth_error_split' rs i r Hi) as Hsplit.
set (l1 := firstn i rs) in Hsplit. set (l2 := skipn (S i) rs) in Hsplit.
assert (Hdis : Forall (extent_disjoint E r) (l1 ++ l2)).
{ rewrite Hsplit in Hpd. exact (pairwise_disjoint_split E l1 r l2 Hpd). }
assert (Hrin : In r rs) by (eapply nth_error_In; eauto).
pose proof (proj1 (Forall_forall _ _) Hok r Hrin) as (Hr0 & Hr1 & _ & _).
rewrite Forall_forall in Hok |- *. intros r' Hin'.
specialize (Hok r' Hin'). destruct Hok as (Hc0 & Hc1 & Hw' & Hcs').
assert (Hwf' : region_wf r' = true) by (apply (regions_wf_In rs); assumption).
apply region_wf_facts in Hwf' as (Hlohi' & Hwr' & Hcin').
assert (Hcase : r' = r \/ extent_disjoint E r r').
{ rewrite Hsplit in Hin'. apply in_app_iff in Hin'. destruct Hin' as [H|[H|H]].
- right. apply (proj1 (Forall_forall _ _) Hdis). apply in_app_iff. auto.
- left. symmetry. exact H.
- right. apply (proj1 (Forall_forall _ _) Hdis). apply in_app_iff. auto. }
split; [exact Hc0|]. split; [exact Hc1|]. split.
- intros o Ho. pose proof (Hw' o Ho) as W.
destruct (Z_lt_dec (base_val E (r_base r') + o) (base_val E (r_base r) + lo)) as [L|L].
+ apply (writable_at_eq segs m m'); [apply Hout; rewrite u_Z2bv by lia; lia| exact W].
+ destruct (Z_lt_dec (base_val E (r_base r') + o) (base_val E (r_base r) + hi)) as [L2|L2].
* unfold writable_at. apply Hdef. rewrite u_Z2bv by lia. lia.
* apply (writable_at_eq segs m m'); [apply Hout; rewrite u_Z2bv by lia; lia| exact W].
- rewrite Forall_forall in Hcs' |- *. intros c Hc.
pose proof (proj1 (forallb_forall _ _) Hcin' c Hc) as Hci. apply chunk_inside_facts in Hci.
apply (chunk_ok_same E m m'); [apply Hcs'; exact Hc|].
intros j Hj. apply Hout. rewrite u_Z2bv by lia.
destruct Hcase as [-> | Hd].
+ specialize (Hcs c Hc). unfold chunk_out in Hcs. apply orb_prop in Hcs as [Hcs|Hcs]; apply Z.leb_le in Hcs; lia.
+ unfold extent_disjoint in Hd. lia.
Qed.
Lemma keep_chunks_out : forall lo hi r c, In c (r_chunks (keep_chunks (chunk_out lo hi) r)) -> chunk_out lo hi c = true.
Proof. intros lo hi r c H. cbn in H. apply filter_In in H. tauto. Qed.
Lemma store_ok_of_region : forall E m rs i r lo n,
mem_ok segs E m rs -> nth_error rs i = Some r ->
r_wlo r <= lo -> lo + Z.of_nat n <= r_whi r -> (0 < n)%nat ->
0 <= base_val E (r_base r) + lo -> base_val E (r_base r) + lo + Z.of_nat n <= 2^64 ->
store_ok segs m (Z_to_bv 64 (base_val E (r_base r) + lo)) n = true.
Proof.
intros E m rs i r lo n (Hwf & Hok & _) Hi Hwlo Hwhi Hn H0 H64.
assert (Hrin : In r rs) by (eapply nth_error_In; eauto).
pose proof (proj1 (Forall_forall _ _) Hok r Hrin) as (_ & _ & Hw & _).
apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
intros x Hx. pose proof (Hw (bv_unsigned x - base_val E (r_base r)) ltac:(lia)) as W.
unfold writable_at in W. replace (base_val E (r_base r) + (bv_unsigned x - base_val E (r_base r))) with (bv_unsigned x) in W by lia.
rewrite Z_to_bv_bv_unsigned in W. exact W.
Qed.
Section g.
Variable H : word -> bool.
Variable A : list (Z * Z).
Lemma srz_writev_empty : forall regs pc mem rom model fd ch (b0 : word) T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some (Z_to_bv 64 0) ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 0 = true ->
ranges_avoid H [(getr regs 11, 16%nat)] ->
(forall model', AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) model') T) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd ch b0 T HAI Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hiok Hok0 Hav Hc.
set (CI := [(getr regs 11, 16%nat)]).
destruct (node_ret_only_copyins_lazy segs H A regs pc mem rom model CI (Z_to_bv 64 0) model [] HAI)
as (Hn & HA & Hs).
- intros eff. rewrite (chk66 segs) by exact Hno. rewrite Hfd, H32.
destruct Hfdc as [Hlk Hch].
unfold check_writev. cbn [in_mem sys_input]. rewrite Hlk, Hch, Hcnt.
change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
unfold import_iovecs, import_iovecs_accesses. rewrite bv_eqb_refl, Hiok. cbn [negb].
rewrite (read_iovec_entry_of (pend_at regs pc mem rom) (getr regs 11) b0 (Z_to_bv 64 0) Hb0 Hl0)
by (change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia).
change (Z.min (bv_unsigned (Z_to_bv 64 0)) MAX_RW_COUNT) with 0%Z. rewrite Hok0. cbn [negb].
cbv zeta.
replace (iovs_total (cap_iovecs [(b0, Z_to_bv 64 0)]) =? 0)%Z with true by reflexivity.
subst CI. destruct (check_ret_only_copyins _ _ _ _ _); reflexivity.
- exact (AI_halted segs H A model HAI).
- repeat split; reflexivity.
- exact Hav.
- exact (srz_silent1 segs _ _ T Hn (Hc _ HA Hs)).
Qed.
End g.
Lemma skeleton_forget_win : forall rs i lo hi, skeleton (forget_win rs i lo hi) = skeleton rs.
Proof.
induction rs as [|r rs IH]; intros i lo hi; cbn; [reflexivity|].
destruct i as [|i]; cbn; [reflexivity| rewrite IH; reflexivity].
Qed.
Lemma frame_of_agree : forall k E E' rs m m',
env_agree k E E' -> mem_atoms_lt k rs = true -> frame_of E' rs m m' -> frame_of E rs m m'.
Proof.
intros k E E' rs m m' HA Hat HF x Hx. apply HF. intros (r & Hin & Hr). apply Hx.
exists r. split; [exact Hin|].
unfold mem_atoms_lt in Hat. pose proof (proj1 (forallb_forall _ _) Hat r Hin) as Hr'.
unfold region_atoms_lt in Hr'. apply andb_prop in Hr' as [Hb _].
rewrite <- (base_val_agree k E E' (r_base r) HA Hb). exact Hr.
Qed.
End f.
Lemma mem_atoms_lt_submem : forall k rs' rs,
submem rs' rs -> mem_atoms_lt k rs = true -> mem_atoms_lt k rs' = true.
Proof.
intros k rs' rs Hsm. unfold mem_atoms_lt.
induction Hsm as [rs1|rs1 x rs2 Hsm IH|x' x rs1 rs2 Hsr Hsm IH]; intros H; cbn in *.
- reflexivity.
- apply andb_prop in H as [_ H]. apply IH. exact H.
- apply andb_prop in H as [Hx H]. rewrite (IH H), andb_true_r.
destruct Hsr as (Hbase & _ & _ & _ & Hcs). unfold region_atoms_lt in *. rewrite Hbase.
apply andb_prop in Hx as [Hx1 Hx2]. rewrite Hx1. cbn. apply forallb_forall. intros c Hc.
apply (proj1 (forallb_forall _ _) Hx2). apply Hcs. exact Hc.
Qed.
Definition WL_CLOB : list reg := [1; 10; 11; 12; 13; 14; 15; 18; 19; 20; 22]%bv.
Definition WL_DONE : Z := 0x92d80.
Definition WL_ECALL1 : Z := 0x92d74.
Definition wl_after (ss : sstate) (i : nat) (K : Z) (k : nat) : sstate :=
mkSS WL_DONE
(sr_sets (ss_regs ss) ((17%bv : reg, SLit 66) :: junk_upd k WL_CLOB))
(forget_win (ss_mem ss) i (K + 8) (K + 40))
None (ss_facts ss).
Lemma wl_kept_of_reg_in : forall r, reg_in r ((17%bv : reg) :: WL_CLOB) = false -> r <> 17%bv /\ wl_kept r.
Proof.
intros r H. unfold wl_kept.
repeat match goal with |- _ /\ _ => split end;
intros ->; vm_compute in H; discriminate H.
Qed.
Lemma word_to_nat_U : forall E v, word_to_nat (sv_denot E v) = Z.to_nat (U E v).
Proof. intros. reflexivity. Qed.
Section h.
Variable W : world tfibsegs.
Local Notation HH := (w_H W).
Lemma wview_restrict_vis : forall (m : word -> option byte) (x : word),
wview tfibsegs (mrestrict HH m) x <> None -> HH x = false.
Proof.
intros m x Hw. destruct (HH x) eqn:E; [|reflexivity]. exfalso. apply Hw.
unfold wview, mrestrict. rewrite E. rewrite (w_Hoff W x E). reflexivity.
Qed.
Lemma mem_grows_mrestrict : forall (m : word -> option byte), mem_grows (mrestrict HH m) m.
Proof.
intros m x Hx. unfold mrestrict in Hx. destruct (HH x); [exfalso; exact (Hx eq_refl) | exact Hx].
Qed.
Lemma u_add1 : forall a : word, bv_unsigned a + 1 < 2^64 -> bv_unsigned (a + 1)%bv = bv_unsigned a + 1.
Proof.
intros a Ha. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
replace (bv_unsigned (1%bv : word)) with 1 by reflexivity. pose proof (u64_range a). apply Z.mod_small. lia.
Qed.
Lemma store_ok_restrict_inv_w : forall (m : word -> option byte) (k : nat) (a : word),
bv_unsigned a + Z.of_nat k <= 2^64 ->
store_ok tfibsegs (mrestrict HH m) a k = true ->
store_ok tfibsegs m a k = true
/\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> HH x = false).
Proof.
intros m k a Hk Hst. split; [exact (store_ok_mono tfibsegs k _ _ a (mem_grows_mrestrict m) Hst)|].
revert a Hk Hst. induction k as [|k IH]; intros a Hk Hst x Hx; [lia|].
cbn [store_ok] in Hst. pose proof (u64_range a) as Hra.
destruct (wview tfibsegs (mrestrict HH m) a) as [b|] eqn:Hw; [|discriminate].
assert (Hva : HH a = false) by (apply (wview_restrict_vis m); rewrite Hw; discriminate).
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [e|ne].
- replace x with a by (apply bv_eq; lia). exact Hva.
- destruct k as [|k']; [lia|].
pose proof (u_add1 a ltac:(lia)) as Hu.
apply (IH (a + 1)%bv); [rewrite Hu; lia | exact Hst | rewrite Hu; lia].
Qed.
Lemma store_ok_restrict_inv : forall (m : word -> option byte) (a : Z) (k : nat),
0 <= a -> a + Z.of_nat k <= 2^64 ->
store_ok tfibsegs (mrestrict HH m) (Z_to_bv 64 a) k = true ->
store_ok tfibsegs m (Z_to_bv 64 a) k = true /\ vis_range W a (a + Z.of_nat k).
Proof.
intros m a k Ha Hk Hst. destruct k as [|k].
- split; [reflexivity | intros x Hx; cbn in Hx; lia].
- destruct (store_ok_restrict_inv_w m (S k) (Z_to_bv 64 a) ltac:(rewrite u_Z2bv by lia; lia) Hst) as [Hs Hv].
split; [exact Hs|]. intros x Hx. apply Hv. rewrite u_Z2bv by lia. lia.
Qed.
Lemma rdn_unfold : forall (m : word -> option byte) (a : word) n,
rdn tfibsegs m a (S n)
= match (match m a with Some b => Some b | None => seg_rom tfibsegs a end) with
| Some b => match rdn tfibsegs m (a + 1)%bv n with Some rest => Some (b :: rest) | None => None end
| None => None
end.
Proof. intros. reflexivity. Qed.
Lemma rdn_restrict_inv_w : forall (m : word -> option byte) (k : nat) (a : word) bs,
bv_unsigned a + Z.of_nat k <= 2^64 ->
rdn tfibsegs (mrestrict HH m) a k = Some bs ->
rdn tfibsegs m a k = Some bs
/\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> HH x = false).
Proof.
intros m k; induction k as [|k IH]; intros a bs Hk Hr.
- split; [exact Hr | intros x Hx; lia].
- rewrite rdn_unfold in Hr |- *. pose proof (u64_range a) as Hra.
assert (Hva : HH a = false).
{ destruct (HH a) eqn:E; [|reflexivity]. exfalso.
unfold mrestrict in Hr at 1. rewrite E in Hr. rewrite (seg_rom_hidden tfibsegs HH a (w_Hoff W) E) in Hr. discriminate. }
rewrite (mrestrict_vis W m a Hva) in Hr.
destruct (match m a with Some b => Some b | None => seg_rom tfibsegs a end) as [b|]; [|discriminate].
destruct k as [|k'].
+ cbn [rdn] in Hr |- *. split; [exact Hr|]. intros x Hx. replace x with a by (apply bv_eq; lia). exact Hva.
+ pose proof (u_add1 a ltac:(lia)) as Hu.
destruct (rdn tfibsegs (mrestrict HH m) (a + 1)%bv (S k')) as [rest|] eqn:Hrest; [|discriminate].
destruct (IH (a + 1)%bv rest ltac:(rewrite Hu; lia) Hrest) as [Hs Hv].
rewrite Hs. split; [exact Hr|]. intros x Hx.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [e|ne];
[replace x with a by (apply bv_eq; lia); exact Hva | apply Hv; rewrite Hu; lia].
Qed.
Lemma rdn_restrict_inv : forall (m : word -> option byte) (a : Z) (k : nat) bs,
0 <= a -> a + Z.of_nat k <= 2^64 ->
rdn tfibsegs (mrestrict HH m) (Z_to_bv 64 a) k = Some bs ->
rdn tfibsegs m (Z_to_bv 64 a) k = Some bs /\ vis_range W a (a + Z.of_nat k).
Proof.
intros m a k bs Ha Hk Hr. destruct k as [|k].
- split; [exact Hr | intros x Hx; cbn in Hx; lia].
- destruct (rdn_restrict_inv_w m (S k) (Z_to_bv 64 a) bs ltac:(rewrite u_Z2bv by lia; lia) Hr) as [Hs Hv].
split; [exact Hs|]. intros x Hx. apply Hv. rewrite u_Z2bv by lia. lia.
Qed.
Lemma rdn_of_restrict : forall (m : word -> option byte) (k : nat) (a : word) bs,
rdn tfibsegs (mrestrict HH m) a k = Some bs -> rdn tfibsegs m a k = Some bs.
Proof.
intros m k; induction k as [|k IH]; intros a bs Hr; [exact Hr|].
rewrite rdn_unfold in Hr |- *.
assert (Hva : HH a = false).
{ destruct (HH a) eqn:E; [|reflexivity]. exfalso.
unfold mrestrict in Hr at 1. rewrite E in Hr. rewrite (seg_rom_hidden tfibsegs HH a (w_Hoff W) E) in Hr. discriminate. }
rewrite (mrestrict_vis W m a Hva) in Hr.
destruct (match m a with Some b => Some b | None => seg_rom tfibsegs a end) as [b0|]; [|discriminate].
destruct (rdn tfibsegs (mrestrict HH m) (a + 1)%bv k) as [rest|] eqn:Hrest; [|discriminate].
rewrite (IH _ _ Hrest). exact Hr.
Qed.
Lemma mrestrict_agree_at : forall (m m' : word -> option byte) (x : word),
m' x = m x -> mrestrict HH m' x = mrestrict HH m x.
Proof. intros m m' x Hx. unfold mrestrict. rewrite Hx. reflexivity. Qed.
End h.
Theorem srz_sym_stdio_writev2 :
forall (W : world tfibsegs) E ss ms model fd ch (i b : nat) (K F : Z) r vb0 vl0 vb1 vl1 bs0 bs1 fdbs (k : nat) T,
AI tfibsegs (w_H W) (w_A W) model ->
st_ok_ecall tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = WL_ECALL1 ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd -> bv_unsigned fd < 2^31 ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 2 -> sv_denot E (sr_get (ss_regs ss) 18) = Z_to_bv 64 2 ->
sr_get (ss_regs ss) 2 = SOff b K ->
sr_get (ss_regs ss) 19 = SOff b (K + 8) -> sr_get (ss_regs ss) 11 = SOff b (K + 8) ->
U E (sr_get (ss_regs ss) 22) = U E vl0 + U E vl1 ->
U E (sr_get (ss_regs ss) 9) = F ->
nth_error (ss_mem ss) i = Some r -> r_base r = Some b ->
r_lo r <= K + 8 -> K + 40 <= r_hi r -> r_wlo r <= K + 8 -> K + 40 <= r_whi r ->
iov_read2 (ss_mem ss) (Some b) (K + 8) = Some (vb0, vl0, vb1, vl1) ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sv_denot E vb0) (word_to_nat (sv_denot E vl0)) = Some bs0 ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl0 + U E vl1 <= 2^25 ->
U E vb0 + U E vl0 <= 2^47 ->
(U E vb0 + U E vl0 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb0) ->
U E vb1 + U E vl1 <= 2^47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 (F + 120)) 4 = Some fdbs -> bytes_le_to_Z fdbs = bv_unsigned fd ->
0 <= F -> F + 124 <= 2^64 ->
(F + 124 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= F + 120) ->
0 <= bv_unsigned (ew E b) + K -> bv_unsigned (ew E b) + K + 40 <= 2^47 ->
ss_atoms_lt k ss = true ->
(forall ms' ws mat', st_ok tfibsegs (havoc E k ws) (wl_after ss i K k) (restrict (w_H W) ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
AI tfibsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy model) mat' model) ->
srealizes tfibsegs (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) T) ->
srealizes tfibsegs (mkCfg ms model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros W E ss ms model fd ch i b K F r vb0 vl0 vb1 vl1 bs0 bs1 fdbs k T
HAI HS Hrv Hpc H17 H10 Hfdc H32 Hfd31 H12 H18 H2 H19 H11 H22 H9 Hi Hb Hrlo Hrhi Hwlo Hwhi
Hiov Hbs0 Hbs1 Hlen Hnw0 Hd0 Hnw1 Hd1 Hfd Hfdv HF0 HF1 HFW HSP0 HSP1 Hat Hk.
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
rewrite Hpc. cbn [ms_mem pend_at] in Hbs0, Hbs1, Hfd, Hk.
set (SP := bv_unsigned (ew E b) + K).
pose proof (U_range E vb0) as R0. pose proof (U_range E vl0) as R1.
pose proof (U_range E vb1) as R2. pose proof (U_range E vl1) as R3. unfold M64 in R0, R1, R2, R3.
unfold iov_read2 in Hiov.
destruct (iov_read1 (ss_mem ss) (Some b) (K + 8)) as [[x0 y0]|] eqn:Hi0; [|discriminate].
destruct (iov_read1 (ss_mem ss) (Some b) (K + 8 + 16)) as [[x1 y1]|] eqn:Hi1; [|discriminate].
injection Hiov as -> -> -> ->.
destruct (iov_read1_sound tfibsegs E (mrestrict (w_H W) mem) _ _ _ _ _ Hmem Hi0) as [M0r L0r].
destruct (iov_read1_sound tfibsegs E (mrestrict (w_H W) mem) _ _ _ _ _ Hmem Hi1) as [M1r L1r].
cbn [base_val] in M0r, L0r, M1r, L1r.
pose proof (rdn_of_restrict W mem _ _ _ M0r) as M0. pose proof (rdn_of_restrict W mem _ _ _ L0r) as L0.
pose proof (rdn_of_restrict W mem _ _ _ M1r) as M1. pose proof (rdn_of_restrict W mem _ _ _ L1r) as L1.
clear M0r L0r M1r L1r.
rewrite (denot_lit_U E vb0) in M0, Hbs0. rewrite (denot_lit_U E vl0) in L0.
rewrite (denot_lit_U E vb1) in M1, Hbs1. rewrite (denot_lit_U E vl1) in L1.
rewrite word_to_nat_U in Hbs0, Hbs1.
assert (HF120 : 0 <= F + 120) by lia.
assert (B0 : U E vb0 + Z.of_nat (Z.to_nat (U E vl0)) <= 2^64) by (rewrite Z2Nat.id by lia; lia).
assert (B1 : U E vb1 + Z.of_nat (Z.to_nat (U E vl1)) <= 2^64) by (rewrite Z2Nat.id by lia; lia).
assert (BF : F + 120 + Z.of_nat 4 <= 2^64) by (cbn; lia).
destruct (rdn_restrict_inv W mem (U E vb0) (Z.to_nat (U E vl0)) bs0 (proj1 R0) B0 Hbs0) as [Hbs0f Hvis0].
destruct (rdn_restrict_inv W mem (U E vb1) (Z.to_nat (U E vl1)) bs1 (proj1 R2) B1 Hbs1) as [Hbs1f Hvis1].
rewrite Z2Nat.id in Hvis0, Hvis1 by lia.
destruct (rdn_restrict_inv W mem (F + 120) 4 fdbs HF120 BF Hfd) as [Hfdf HvisF].
pose proof (rdn_length _ _ _ _ _ Hbs0f) as Hl0. pose proof (rdn_length _ _ _ _ _ Hbs1f) as Hl1.
assert (HstR : store_ok tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 (SP + 8)) 32 = true).
{ replace (Z_to_bv 64 (SP + 8)) with (Z_to_bv 64 (base_val E (r_base r) + (K + 8))) by (rewrite Hb; cbn [base_val]; f_equal; subst SP; lia).
apply (store_ok_of_region tfibsegs E (mrestrict (w_H W) mem) (ss_mem ss) i r (K + 8) 32 Hmem Hi); try (cbn; lia);
rewrite Hb; cbn [base_val]; subst SP; lia. }
assert (BS1 : 0 <= SP + 8) by (subst SP; lia). assert (BS2 : SP + 8 + Z.of_nat 32 <= 2^64) by (subst SP; cbn; lia).
destruct (store_ok_restrict_inv W mem (SP + 8) 32 BS1 BS2 HstR) as [Hst HvisW].
change (SP + 8 + Z.of_nat 32) with (SP + 8 + 32) in HvisW. replace (SP + 8 + 32) with (SP + 40) in HvisW by lia.
change (F + 120 + Z.of_nat 4) with (F + 120 + 4) in HvisF. replace (F + 120 + 4) with (F + 124) in HvisF by lia.
apply (wl_entry_pend_r W fd ch model Hfdc H32 Hfd31 SP F fdbs mem regs T
ltac:(subst SP; lia) ltac:(lia) ltac:(subst SP; lia) Hfdf Hfdv HvisW HvisF)
with (c := 2) (b0 := U E vb0) (l0 := U E vl0) (b1 := U E vb1) (l1 := U E vl1).
-
intros regs' mem' model' Hkept H17' Hout Hst' HAI' Hsbm'.
pose proof Hsbm' as EQ. unfold same_but_materialized in EQ. rewrite EQ in HAI'. rewrite EQ. clear EQ.
apply (Hk (mkst regs' (Z_to_bv 64 0x92d80) mem' (seg_rom tfibsegs)) (map (getr regs') WL_CLOB) (m_vm_materialized model')).
+ rewrite restrict_mkst_fx.
set (E' := havoc E k (map (getr regs') WL_CLOB)).
assert (HA : env_agree k E E') by apply env_agree_havoc.
unfold ss_atoms_lt in Hat. rewrite Hrv in Hat.
apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [Hat HGa]. apply andb_prop in Hat as [Hra Hma].
unfold st_ok, wl_after. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [|split].
*
apply (regs_ok_sets E' (ss_regs ss) regs regs').
-- eapply regs_ok_agree; eauto.
-- apply reg_nodup_sound. vm_compute. reflexivity.
-- intros r0 Hr0. destruct (wl_kept_of_reg_in r0 Hr0) as [_ Hk0]. apply Hkept. exact Hk0.
-- constructor.
++ cbn [fst snd]. split; [reflexivity|]. cbn [sv_denot]. rewrite H17'. reflexivity.
++ subst E'. apply junk_upd_ok0. vm_compute. reflexivity.
*
eapply mem_ok_agree; [exact HA| |].
{ apply (mem_atoms_lt_submem k _ (ss_mem ss)); [apply submem_forget_win | exact Hma]. }
apply (mem_ok_window_change tfibsegs E (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') _ i (keep_chunks (chunk_out (K + 8) (K + 40)) r) (K + 8) (K + 40)).
-- apply mem_ok_forget_win. exact Hmem.
-- apply nth_error_forget_win. exact Hi.
-- cbn. lia. -- lia. -- cbn. lia.
-- apply keep_chunks_out.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx. apply (mrestrict_agree_at W). apply Hout. unfold inW. subst SP. lia.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx.
apply (store_ok_all tfibsegs (mrestrict (w_H W) mem') 32 (Z_to_bv 64 (SP + 8))); [rewrite u_Z2bv by lia; subst SP; lia| |].
{ apply (store_ok_vis W); [subst SP; lia | subst SP; cbn; lia | | exact Hst'].
intros z Hz. apply HvisW. cbn in Hz. lia. }
rewrite u_Z2bv by (subst SP; lia). subst SP. cbn. lia.
* eapply facts_ok_agree; eauto.
+
cbn [ms_mem mkst]. intros x Hnw. apply Hout. intros Hin. apply Hnw.
exists r. split; [eapply nth_error_In; exact Hi|]. rewrite Hb. cbn [base_val]. unfold inW in Hin. subst SP. lia.
+
cbn [ms_mem mkst]. intros x Hnw. apply (mrestrict_agree_at W). apply Hout. intros Hin. apply Hnw.
exists r. split; [eapply nth_error_In; exact Hi|]. rewrite Hb. cbn [base_val]. unfold inW in Hin. subst SP. lia.
+ exact HAI'.
- exact HAI.
- apply same_but_materialized_refl.
-
unfold wl_invR. cbn [Z.eqb Pos.eqb].
assert (G : forall rr : reg, getr regs rr = sv_denot E (sr_get (ss_regs ss) rr)) by (intros rr; apply Hregs).
repeat match goal with |- _ /\ _ => split end; try lia.
+ rewrite G, H2. cbn [sv_denot]. reflexivity.
+ rewrite G, denot_lit_U, H9. reflexivity.
+ rewrite G. exact H18.
+ rewrite G. exact H12.
+ rewrite G, H19. cbn [sv_denot]. f_equal. subst SP. lia.
+ rewrite G, H11. cbn [sv_denot]. f_equal. subst SP. lia.
+ rewrite G, denot_lit_U, H22. reflexivity.
+ rewrite G. exact H10.
+ rewrite G, H17. reflexivity.
+ intros rr _. reflexivity.
+ intros a _. reflexivity.
+ exact Hst.
+ unfold iov_mem. split; [intros _; split|split].
* replace (SP + 8) with (bv_unsigned (ew E b) + (K + 8)) by (subst SP; lia). exact M0.
* replace (SP + 16) with (bv_unsigned (ew E b) + (K + 8) + 8) by (subst SP; lia). exact L0.
* replace (SP + 24) with (bv_unsigned (ew E b) + (K + 8 + 16)) by (subst SP; lia). exact M1.
* replace (SP + 32) with (bv_unsigned (ew E b) + (K + 8 + 16) + 8) by (subst SP; lia). exact L1.
+ intros _. exact Hbs0f.
+ exact Hbs1f.
+ intros _. exact Hvis0.
+ exact Hvis1.
Qed.
Theorem srz_sym_stdio_writev1 :
forall (W : world tfibsegs) E ss ms model fd ch (i b : nat) (K F : Z) r vb1 vl1 bs1 fdbs (k : nat) T,
AI tfibsegs (w_H W) (w_A W) model ->
st_ok_ecall tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = WL_ECALL1 ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd -> bv_unsigned fd < 2^31 ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 1 -> sv_denot E (sr_get (ss_regs ss) 18) = Z_to_bv 64 1 ->
sr_get (ss_regs ss) 2 = SOff b K ->
sr_get (ss_regs ss) 19 = SOff b (K + 24) -> sr_get (ss_regs ss) 11 = SOff b (K + 24) ->
U E (sr_get (ss_regs ss) 22) = U E vl1 ->
U E (sr_get (ss_regs ss) 9) = F ->
nth_error (ss_mem ss) i = Some r -> r_base r = Some b ->
r_lo r <= K + 8 -> K + 40 <= r_hi r -> r_wlo r <= K + 8 -> K + 40 <= r_whi r ->
iov_read1 (ss_mem ss) (Some b) (K + 24) = Some (vb1, vl1) ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl1 <= 2^25 ->
U E vb1 + U E vl1 <= 2^47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 (F + 120)) 4 = Some fdbs -> bytes_le_to_Z fdbs = bv_unsigned fd ->
0 <= F -> F + 124 <= 2^64 ->
(F + 124 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= F + 120) ->
0 <= bv_unsigned (ew E b) + K -> bv_unsigned (ew E b) + K + 40 <= 2^47 ->
ss_atoms_lt k ss = true ->
(forall ms' ws mat', st_ok tfibsegs (havoc E k ws) (wl_after ss i K k) (restrict (w_H W) ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
AI tfibsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy model) mat' model) ->
srealizes tfibsegs (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) T) ->
srealizes tfibsegs (mkCfg ms model) (t_emit (map (WriteEv ch) bs1) T).
Proof.
intros W E ss ms model fd ch i b K F r vb1 vl1 bs1 fdbs k T
HAI HS Hrv Hpc H17 H10 Hfdc H32 Hfd31 H12 H18 H2 H19 H11 H22 H9 Hi Hb Hrlo Hrhi Hwlo Hwhi
Hiov Hbs1 Hlen Hnw1 Hd1 Hfd Hfdv HF0 HF1 HFW HSP0 HSP1 Hat Hk.
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
rewrite Hpc. cbn [ms_mem pend_at] in Hbs1, Hfd, Hk.
set (SP := bv_unsigned (ew E b) + K).
pose proof (U_range E vb1) as R2. pose proof (U_range E vl1) as R3. unfold M64 in R2, R3.
destruct (iov_read1_sound tfibsegs E (mrestrict (w_H W) mem) _ _ _ _ _ Hmem Hiov) as [M1r L1r].
cbn [base_val] in M1r, L1r.
pose proof (rdn_of_restrict W mem _ _ _ M1r) as M1. pose proof (rdn_of_restrict W mem _ _ _ L1r) as L1.
clear M1r L1r.
rewrite (denot_lit_U E vb1) in M1, Hbs1. rewrite (denot_lit_U E vl1) in L1.
rewrite word_to_nat_U in Hbs1.
assert (HF120 : 0 <= F + 120) by lia.
assert (B1 : U E vb1 + Z.of_nat (Z.to_nat (U E vl1)) <= 2^64) by (rewrite Z2Nat.id by lia; lia).
assert (BF : F + 120 + Z.of_nat 4 <= 2^64) by (cbn; lia).
destruct (rdn_restrict_inv W mem (U E vb1) (Z.to_nat (U E vl1)) bs1 (proj1 R2) B1 Hbs1) as [Hbs1f Hvis1].
rewrite Z2Nat.id in Hvis1 by lia.
destruct (rdn_restrict_inv W mem (F + 120) 4 fdbs HF120 BF Hfd) as [Hfdf HvisF].
pose proof (rdn_length _ _ _ _ _ Hbs1f) as Hl1.
assert (HstR : store_ok tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 (SP + 8)) 32 = true).
{ replace (Z_to_bv 64 (SP + 8)) with (Z_to_bv 64 (base_val E (r_base r) + (K + 8))) by (rewrite Hb; cbn [base_val]; f_equal; subst SP; lia).
apply (store_ok_of_region tfibsegs E (mrestrict (w_H W) mem) (ss_mem ss) i r (K + 8) 32 Hmem Hi); try (cbn; lia);
rewrite Hb; cbn [base_val]; subst SP; lia. }
assert (BS1 : 0 <= SP + 8) by (subst SP; lia). assert (BS2 : SP + 8 + Z.of_nat 32 <= 2^64) by (subst SP; cbn; lia).
destruct (store_ok_restrict_inv W mem (SP + 8) 32 BS1 BS2 HstR) as [Hst HvisW].
change (SP + 8 + Z.of_nat 32) with (SP + 8 + 32) in HvisW. replace (SP + 8 + 32) with (SP + 40) in HvisW by lia.
change (F + 120 + Z.of_nat 4) with (F + 120 + 4) in HvisF. replace (F + 120 + 4) with (F + 124) in HvisF by lia.
change bs1 with ([] ++ bs1).
apply (wl_entry_pend_r W fd ch model Hfdc H32 Hfd31 SP F fdbs mem regs T
ltac:(subst SP; lia) ltac:(lia) ltac:(subst SP; lia) Hfdf Hfdv HvisW HvisF)
with (c := 1) (b0 := 0) (l0 := 0) (b1 := U E vb1) (l1 := U E vl1).
-
intros regs' mem' model' Hkept H17' Hout Hst' HAI' Hsbm'.
pose proof Hsbm' as EQ. unfold same_but_materialized in EQ. rewrite EQ in HAI'. rewrite EQ. clear EQ.
apply (Hk (mkst regs' (Z_to_bv 64 0x92d80) mem' (seg_rom tfibsegs)) (map (getr regs') WL_CLOB) (m_vm_materialized model')).
+ rewrite restrict_mkst_fx.
set (E' := havoc E k (map (getr regs') WL_CLOB)).
assert (HA : env_agree k E E') by apply env_agree_havoc.
unfold ss_atoms_lt in Hat. rewrite Hrv in Hat.
apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [Hat HGa]. apply andb_prop in Hat as [Hra Hma].
unfold st_ok, wl_after. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [|split].
*
apply (regs_ok_sets E' (ss_regs ss) regs regs').
-- eapply regs_ok_agree; eauto.
-- apply reg_nodup_sound. vm_compute. reflexivity.
-- intros r0 Hr0. destruct (wl_kept_of_reg_in r0 Hr0) as [_ Hk0]. apply Hkept. exact Hk0.
-- constructor.
++ cbn [fst snd]. split; [reflexivity|]. cbn [sv_denot]. rewrite H17'. reflexivity.
++ subst E'. apply junk_upd_ok0. vm_compute. reflexivity.
*
eapply mem_ok_agree; [exact HA| |].
{ apply (mem_atoms_lt_submem k _ (ss_mem ss)); [apply submem_forget_win | exact Hma]. }
apply (mem_ok_window_change tfibsegs E (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') _ i (keep_chunks (chunk_out (K + 8) (K + 40)) r) (K + 8) (K + 40)).
-- apply mem_ok_forget_win. exact Hmem.
-- apply nth_error_forget_win. exact Hi.
-- cbn. lia. -- lia. -- cbn. lia.
-- apply keep_chunks_out.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx. apply (mrestrict_agree_at W). apply Hout. unfold inW. subst SP. lia.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx.
apply (store_ok_all tfibsegs (mrestrict (w_H W) mem') 32 (Z_to_bv 64 (SP + 8))); [rewrite u_Z2bv by lia; subst SP; lia| |].
{ apply (store_ok_vis W); [subst SP; lia | subst SP; cbn; lia | | exact Hst'].
intros z Hz. apply HvisW. cbn in Hz. lia. }
rewrite u_Z2bv by (subst SP; lia). subst SP. cbn. lia.
* eapply facts_ok_agree; eauto.
+
cbn [ms_mem mkst]. intros x Hnw. apply Hout. intros Hin. apply Hnw.
exists r. split; [eapply nth_error_In; exact Hi|]. rewrite Hb. cbn [base_val]. unfold inW in Hin. subst SP. lia.
+
cbn [ms_mem mkst]. intros x Hnw. apply (mrestrict_agree_at W). apply Hout. intros Hin. apply Hnw.
exists r. split; [eapply nth_error_In; exact Hi|]. rewrite Hb. cbn [base_val]. unfold inW in Hin. subst SP. lia.
+ exact HAI'.
- exact HAI.
- apply same_but_materialized_refl.
-
unfold wl_invR. cbn [Z.eqb Pos.eqb].
assert (G : forall rr : reg, getr regs rr = sv_denot E (sr_get (ss_regs ss) rr)) by (intros rr; apply Hregs).
repeat match goal with |- _ /\ _ => split end; try lia.
+ rewrite G, H2. cbn [sv_denot]. reflexivity.
+ rewrite G, denot_lit_U, H9. reflexivity.
+ rewrite G. exact H18.
+ rewrite G. exact H12.
+ rewrite G, H19. cbn [sv_denot]. f_equal. subst SP. lia.
+ rewrite G, H11. cbn [sv_denot]. f_equal. subst SP. lia.
+ rewrite G, denot_lit_U, H22. reflexivity.
+ rewrite G. exact H10.
+ rewrite G, H17. reflexivity.
+ intros rr _. reflexivity.
+ intros a _. reflexivity.
+ exact Hst.
+ unfold iov_mem. split; [intros HX; lia|split].
* replace (SP + 24) with (bv_unsigned (ew E b) + (K + 24)) by (subst SP; lia). exact M1.
* replace (SP + 32) with (bv_unsigned (ew E b) + (K + 24) + 8) by (subst SP; lia). exact L1.
+ exact Hbs1f.
+ reflexivity.
+ exact Hvis1.
Qed.
Theorem srz_sym_writev_empty : forall (W : world tfibsegs) E ss ms model fd ch (i bb : nat) r b off vb0 vl0 T,
AI tfibsegs (w_H W) (w_A W) model ->
st_ok_ecall tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 1 ->
U E (sr_get (ss_regs ss) 11) = base_val E b + off ->
iov_read1 (ss_mem ss) b off = Some (vb0, vl0) -> U E vl0 = 0 ->
nth_error (ss_mem ss) i = Some r -> r_base r = b ->
r_wlo r <= off -> off + 16 <= r_whi r -> 0 <= base_val E b + off -> base_val E b + off + 16 <= 2^64 ->
base_val E b + off + 16 <= 2^47 -> U E vb0 <= 2^47 ->
(forall ms' mat', st_ok tfibsegs E (resume ss (SLit 0) (ss_mem ss) (ss_facts ss)) (restrict (w_H W) ms') ->
ms_mem ms' = ms_mem ms ->
AI tfibsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy model) mat' model) ->
srealizes tfibsegs (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) T) ->
srealizes tfibsegs (mkCfg ms model) T.
Proof.
intros W E ss ms model fd ch i bb r b off vb0 vl0 T HAI HS Hrv H17 H10 Hfdc H32 H12 H11 Hiov Hvl0 Hi Hb Hwlo Hwhi HB0 HB1 Hiok Hok0 Hk.
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
cbn [ms_mem pend_at] in Hk.
destruct (iov_read1_sound tfibsegs E (mrestrict (w_H W) mem) _ _ _ _ _ Hmem Hiov) as [M0r L0r].
pose proof (rdn_of_restrict W mem _ _ _ M0r) as M0. pose proof (rdn_of_restrict W mem _ _ _ L0r) as L0. clear M0r L0r.
assert (Ha11 : getr regs 11 = Z_to_bv 64 (base_val E b + off)).
{ rewrite (Hregs 11%bv), denot_lit_U, H11. reflexivity. }
assert (HstR : store_ok tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 (base_val E (r_base r) + off)) 16 = true).
{ apply (store_ok_of_region tfibsegs E (mrestrict (w_H W) mem) (ss_mem ss) i r off 16 Hmem Hi); try (cbn; lia);
rewrite Hb; lia. }
rewrite Hb in HstR.
assert (BS2 : base_val E b + off + Z.of_nat 16 <= 2^64) by (cbn; lia).
destruct (store_ok_restrict_inv W mem (base_val E b + off) 16 HB0 BS2 HstR) as [_ Hvis].
eapply (srz_writev_empty tfibsegs (w_H W) (w_A W) regs _ mem (seg_rom tfibsegs) model fd ch (sv_denot E vb0) T HAI).
- rewrite (Hregs 17%bv), H17. reflexivity.
- exact Hfdc. - exact H32.
- rewrite (Hregs 10%bv). exact H10.
- rewrite (Hregs 12%bv), H12. reflexivity.
- apply ms_read_u64_of_rdn. rewrite Ha11. exact M0.
- apply ms_read_u64_of_rdn.
pose proof (U_range E (sr_get (ss_regs ss) 11)) as R. rewrite H11 in R. unfold M64 in R.
rewrite Ha11, u_Z2bv by lia.
rewrite (denot_lit_U E vl0), Hvl0 in L0. exact L0.
- pose proof (U_range E (sr_get (ss_regs ss) 11)) as R. rewrite H11 in R. unfold M64 in R.
rewrite Ha11. unfold access_okb, TASK_SIZE. rewrite u_Z2bv by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
- pose proof (U_range E vb0) as R0. unfold M64 in R0.
rewrite (denot_lit_U E vb0). unfold access_okb, TASK_SIZE. rewrite u_Z2bv by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
-
rewrite Ha11. intros c n Hin.
destruct Hin as [Heq | []]. injection Heq as <- <-.
apply (range_avoids_of_vis W _ 16 (base_val E b + off) (base_val E b + off + 16));
[exact Hvis | rewrite u_Z2bv by lia; lia | cbn; rewrite u_Z2bv by lia; lia | lia].
- intros model' HAI' Hsbm'.
pose proof Hsbm' as EQ. unfold same_but_materialized in EQ. rewrite EQ in HAI'. rewrite EQ. clear EQ.
apply Hk; [|reflexivity|exact HAI'].
rewrite restrict_mkst_fx.
change (Z_to_bv 64 0) with (sv_denot E (SLit 0)).
apply st_ok_resume_sv; auto.
Qed.
End d.
