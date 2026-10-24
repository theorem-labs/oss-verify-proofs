(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN3v YH00 YN3f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
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
Lemma rz_writev_empty : forall regs pc mem rom model fd ch (b0 : word) T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some (Z_to_bv 64 0) ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 0 = true ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd ch b0 T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hiok Hok0 Hc.
eapply (rz_ret_only_copyins_silent segs regs pc mem rom model [(getr regs 11, 16%nat)]
(Z_to_bv 64 0) model T Hh Hlz); [|exact Hh|exact Hlz|exact Hc].
intros eff. rewrite (chk66 segs) by exact Hno. rewrite Hfd, H32.
destruct Hfdc as [Hlk Hch].
unfold check_writev. cbn [in_mem sys_input]. rewrite Hlk, Hch, Hcnt.
change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
unfold import_iovecs, import_iovecs_accesses. rewrite bv_eqb_refl, Hiok. cbn [negb].
rewrite (read_iovec_entry_of (pend_at regs pc mem rom) (getr regs 11) b0 (Z_to_bv 64 0) Hb0 Hl0)
by (change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia).
change (Z.min (bv_unsigned (Z_to_bv 64 0)) MAX_RW_COUNT) with 0%Z. rewrite Hok0. cbn [negb].
cbv zeta.
replace (iovs_total (cap_iovecs [(b0, Z_to_bv 64 0)]) =? 0)%Z with true by reflexivity.
reflexivity.
Qed.
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
End e.
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
Definition WL_DONE : Z := 0x18154.
Definition WL_ECALL1 : Z := 0x18148.
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
Theorem rz_sym_stdio_writev2 :
forall E ss ms model fd ch (i b : nat) (K F : Z) r vb0 vl0 vb1 vl1 bs0 bs1 fdbs (k : nat) T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = WL_ECALL1 ->
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
rdn src0segs (ms_mem ms) (sv_denot E vb0) (word_to_nat (sv_denot E vl0)) = Some bs0 ->
rdn src0segs (ms_mem ms) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl0 + U E vl1 <= 2^25 ->
U E vb0 + U E vl0 <= 2^47 ->
(U E vb0 + U E vl0 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb0) ->
U E vb1 + U E vl1 <= 2^47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
rdn src0segs (ms_mem ms) (Z_to_bv 64 (F + 120)) 4 = Some fdbs -> bytes_le_to_Z fdbs = bv_unsigned fd ->
0 <= F -> F + 124 <= 2^64 ->
(F + 124 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= F + 120) ->
0 <= bv_unsigned (ew E b) + K -> bv_unsigned (ew E b) + K + 40 <= 2^47 ->
ss_atoms_lt k ss = true ->
(forall ms' ws, st_ok src0segs (havoc E k ws) (wl_after ss i K k) ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros E ss ms model fd ch i b K F r vb0 vl0 vb1 vl1 bs0 bs1 fdbs k T
Hh Hlz HS Hrv Hpc H17 H10 Hfdc H32 Hfd31 H12 H18 H2 H19 H11 H22 H9 Hi Hb Hrlo Hrhi Hwlo Hwhi
Hiov Hbs0 Hbs1 Hlen Hnw0 Hd0 Hnw1 Hd1 Hfd Hfdv HF0 HF1 HFW HSP0 HSP1 Hat Hk.
destruct (st_ok_ecall_shape src0segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
rewrite Hpc. cbn [ms_mem pend_at] in Hbs0, Hbs1, Hfd, Hk.
set (SP := bv_unsigned (ew E b) + K).
pose proof (U_range E vb0) as R0. pose proof (U_range E vl0) as R1.
pose proof (U_range E vb1) as R2. pose proof (U_range E vl1) as R3. unfold M64 in R0, R1, R2, R3.
unfold iov_read2 in Hiov.
destruct (iov_read1 (ss_mem ss) (Some b) (K + 8)) as [[x0 y0]|] eqn:Hi0; [|discriminate].
destruct (iov_read1 (ss_mem ss) (Some b) (K + 8 + 16)) as [[x1 y1]|] eqn:Hi1; [|discriminate].
injection Hiov as -> -> -> ->.
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hi0) as [M0 L0].
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hi1) as [M1 L1].
cbn [base_val] in M0, L0, M1, L1.
rewrite (denot_lit_U E vb0) in M0, Hbs0. rewrite (denot_lit_U E vl0) in L0.
rewrite (denot_lit_U E vb1) in M1, Hbs1. rewrite (denot_lit_U E vl1) in L1.
rewrite word_to_nat_U in Hbs0, Hbs1.
pose proof (rdn_length _ _ _ _ _ Hbs0) as Hl0. pose proof (rdn_length _ _ _ _ _ Hbs1) as Hl1.
apply (wl_entry_pend model Hh Hlz fd ch Hfdc H32 Hfd31 SP F fdbs mem regs T
ltac:(subst SP; lia) ltac:(lia) ltac:(subst SP; lia) Hfd Hfdv)
with (c := 2) (b0 := U E vb0) (l0 := U E vl0) (b1 := U E vb1) (l1 := U E vl1).
-
intros regs' mem' Hkept H17' Hout Hst'.
apply (Hk (mkst regs' (Z_to_bv 64 0x18154) mem' (seg_rom src0segs)) (map (getr regs') WL_CLOB)).
+ set (E' := havoc E k (map (getr regs') WL_CLOB)).
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
apply (mem_ok_window_change src0segs E mem mem' _ i (keep_chunks (chunk_out (K + 8) (K + 40)) r) (K + 8) (K + 40)).
-- apply mem_ok_forget_win. exact Hmem.
-- apply nth_error_forget_win. exact Hi.
-- cbn. lia. -- lia. -- cbn. lia.
-- apply keep_chunks_out.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx. apply Hout. unfold inW. subst SP. lia.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx.
apply (store_ok_all src0segs mem' 32 (Z_to_bv 64 (SP + 8))); [rewrite u_Z2bv by lia; subst SP; lia| exact Hst'|].
rewrite u_Z2bv by (subst SP; lia). subst SP. cbn. lia.
* eapply facts_ok_agree; eauto.
+
cbn [ms_mem mkst]. intros x Hnw. apply Hout. intros Hin. apply Hnw.
exists r. split; [eapply nth_error_In; exact Hi|]. rewrite Hb. cbn [base_val]. unfold inW in Hin. subst SP. lia.
-
unfold wl_inv. cbn [Z.eqb Pos.eqb].
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
+ replace (Z_to_bv 64 (SP + 8)) with (Z_to_bv 64 (base_val E (r_base r) + (K + 8))) by (rewrite Hb; cbn [base_val]; f_equal; subst SP; lia).
apply (store_ok_of_region src0segs E mem (ss_mem ss) i r (K + 8) 32 Hmem Hi); try (cbn; lia);
rewrite Hb; cbn [base_val]; subst SP; lia.
+ unfold iov_mem. split; [intros _; split|split].
* replace (SP + 8) with (bv_unsigned (ew E b) + (K + 8)) by (subst SP; lia). exact M0.
* replace (SP + 16) with (bv_unsigned (ew E b) + (K + 8) + 8) by (subst SP; lia). exact L0.
* replace (SP + 24) with (bv_unsigned (ew E b) + (K + 8 + 16)) by (subst SP; lia). exact M1.
* replace (SP + 32) with (bv_unsigned (ew E b) + (K + 8 + 16) + 8) by (subst SP; lia). exact L1.
+ intros _. exact Hbs0.
+ exact Hbs1.
Qed.
Theorem rz_sym_stdio_writev1 :
forall E ss ms model fd ch (i b : nat) (K F : Z) r vb1 vl1 bs1 fdbs (k : nat) T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = WL_ECALL1 ->
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
rdn src0segs (ms_mem ms) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl1 <= 2^25 ->
U E vb1 + U E vl1 <= 2^47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
rdn src0segs (ms_mem ms) (Z_to_bv 64 (F + 120)) 4 = Some fdbs -> bytes_le_to_Z fdbs = bv_unsigned fd ->
0 <= F -> F + 124 <= 2^64 ->
(F + 124 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= F + 120) ->
0 <= bv_unsigned (ew E b) + K -> bv_unsigned (ew E b) + K + 40 <= 2^47 ->
ss_atoms_lt k ss = true ->
(forall ms' ws, st_ok src0segs (havoc E k ws) (wl_after ss i K k) ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) bs1) T).
Proof.
intros E ss ms model fd ch i b K F r vb1 vl1 bs1 fdbs k T
Hh Hlz HS Hrv Hpc H17 H10 Hfdc H32 Hfd31 H12 H18 H2 H19 H11 H22 H9 Hi Hb Hrlo Hrhi Hwlo Hwhi
Hiov Hbs1 Hlen Hnw1 Hd1 Hfd Hfdv HF0 HF1 HFW HSP0 HSP1 Hat Hk.
destruct (st_ok_ecall_shape src0segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
rewrite Hpc. cbn [ms_mem pend_at] in Hbs1, Hfd, Hk.
set (SP := bv_unsigned (ew E b) + K).
pose proof (U_range E vb1) as R2. pose proof (U_range E vl1) as R3. unfold M64 in R2, R3.
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hiov) as [M1 L1].
cbn [base_val] in M1, L1.
rewrite (denot_lit_U E vb1) in M1, Hbs1. rewrite (denot_lit_U E vl1) in L1.
rewrite word_to_nat_U in Hbs1.
pose proof (rdn_length _ _ _ _ _ Hbs1) as Hl1.
change bs1 with ([] ++ bs1).
apply (wl_entry_pend model Hh Hlz fd ch Hfdc H32 Hfd31 SP F fdbs mem regs T
ltac:(subst SP; lia) ltac:(lia) ltac:(subst SP; lia) Hfd Hfdv)
with (c := 1) (b0 := 0) (l0 := 0) (b1 := U E vb1) (l1 := U E vl1).
-
intros regs' mem' Hkept H17' Hout Hst'.
apply (Hk (mkst regs' (Z_to_bv 64 0x18154) mem' (seg_rom src0segs)) (map (getr regs') WL_CLOB)).
+ set (E' := havoc E k (map (getr regs') WL_CLOB)).
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
apply (mem_ok_window_change src0segs E mem mem' _ i (keep_chunks (chunk_out (K + 8) (K + 40)) r) (K + 8) (K + 40)).
-- apply mem_ok_forget_win. exact Hmem.
-- apply nth_error_forget_win. exact Hi.
-- cbn. lia. -- lia. -- cbn. lia.
-- apply keep_chunks_out.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx. apply Hout. unfold inW. subst SP. lia.
-- cbn [keep_chunks r_base]. rewrite Hb. cbn [base_val]. intros x Hx.
apply (store_ok_all src0segs mem' 32 (Z_to_bv 64 (SP + 8))); [rewrite u_Z2bv by lia; subst SP; lia| exact Hst'|].
rewrite u_Z2bv by (subst SP; lia). subst SP. cbn. lia.
* eapply facts_ok_agree; eauto.
+
cbn [ms_mem mkst]. intros x Hnw. apply Hout. intros Hin. apply Hnw.
exists r. split; [eapply nth_error_In; exact Hi|]. rewrite Hb. cbn [base_val]. unfold inW in Hin. subst SP. lia.
-
unfold wl_inv. cbn [Z.eqb Pos.eqb].
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
+ replace (Z_to_bv 64 (SP + 8)) with (Z_to_bv 64 (base_val E (r_base r) + (K + 8))) by (rewrite Hb; cbn [base_val]; f_equal; subst SP; lia).
apply (store_ok_of_region src0segs E mem (ss_mem ss) i r (K + 8) 32 Hmem Hi); try (cbn; lia);
rewrite Hb; cbn [base_val]; subst SP; lia.
+ unfold iov_mem. split; [intros HX; lia|split].
* replace (SP + 24) with (bv_unsigned (ew E b) + (K + 24)) by (subst SP; lia). exact M1.
* replace (SP + 32) with (bv_unsigned (ew E b) + (K + 24) + 8) by (subst SP; lia). exact L1.
+ exact Hbs1.
+ reflexivity.
Qed.
Theorem rz_sym_writev_empty : forall E ss ms model fd ch b off vb0 vl0 T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms -> ss_resv ss = None ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
sr_get (ss_regs ss) 12 = SLit 1 ->
U E (sr_get (ss_regs ss) 11) = base_val E b + off ->
iov_read1 (ss_mem ss) b off = Some (vb0, vl0) -> U E vl0 = 0 ->
base_val E b + off + 16 <= 2^47 -> U E vb0 <= 2^47 ->
(forall ms', st_ok src0segs E (resume ss (SLit 0) (ss_mem ss) (ss_facts ss)) ms' -> ms_mem ms' = ms_mem ms ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) T.
Proof.
intros E ss ms model fd ch b off vb0 vl0 T Hh Hlz HS Hrv H17 H10 Hfdc H32 H12 H11 Hiov Hvl0 Hiok Hok0 Hk.
destruct (st_ok_ecall_shape src0segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
cbn [ms_mem pend_at] in Hk.
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hiov) as [M0 L0].
assert (Ha11 : getr regs 11 = Z_to_bv 64 (base_val E b + off)).
{ rewrite (Hregs 11%bv), denot_lit_U, H11. reflexivity. }
eapply (rz_writev_empty src0segs regs _ mem (seg_rom src0segs) model fd ch (sv_denot E vb0) T Hh Hlz).
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
- apply Hk; [|reflexivity].
change (Z_to_bv 64 0) with (sv_denot E (SLit 0)).
apply st_ok_resume_sv; auto.
Qed.
End d.
