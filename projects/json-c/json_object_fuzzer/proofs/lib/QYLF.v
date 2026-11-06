(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE Q3bI QU0c Q85Z Q6EJ QND5 QBCP QG64 Qek8 QHup QsSk QqZL QxyE QEdo Qt8n QWtD QDlz QOTP Q1LT QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 Q85Z Q6EJ QND5 QBCP.Mq0 QG64.Mq2 Q6EJ.Mq1 Qek8 QHup.Mq1 QsSk QqZL.Mq0 Q3bI.Mq0 Q3bI.Mq1 QxyE QEdo.
Import Qt8n QWtD QqZL.Mq2 QDlz QOTP Q1LT.
Import QQny.Mq0.
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma lit_diff_sound : forall E e f d,
lit_diff e f = Some d ->
0 <= d < two64 /\ (bv_unsigned (edenot E e) - bv_unsigned (edenot E f)) mod two64 = d.
Proof.
intros E e f d H. unfold lit_diff in H.
pose proof (mkAlu_denot E ALU_SUB e f) as D. unfold esub in H.
destruct (mkAlu ALU_SUB e f) eqn:Hm; try discriminate. injection H as <-.
cbn [edenot] in D. apply (f_equal bv_unsigned) in D. rewrite u_sub64 in D. rewrite u_lit64 in D.
split; [apply Z.mod_pos_bound; unfold two64; lia|]. unfold two64 in *. rewrite <- D. reflexivity.
Qed.

Lemma page_aligned_sound : forall SEGS E M k e,
know_ok SEGS E M k -> page_aligned k e = true -> bv_unsigned (edenot E e) mod 4096 = 0.
Proof.
intros SEGS E M k e HK H. unfold page_aligned in H.
assert (GEN : 12 <= ealign k e -> bv_unsigned (edenot E e) mod 4096 = 0).
{ intros Hle. destruct (ealign_sound SEGS E M k e HK) as [Hr Hdiv]. apply Z.mod_divide; [lia|].
eapply Z.divide_trans; [|exact Hdiv]. change 4096 with (2 ^ 12). apply pow2_divide_le. lia. }
destruct e; try (apply GEN; apply Z.leb_le; exact H).
apply Z.eqb_eq in H. cbn [edenot]. rewrite u_lit64. unfold two64.
rewrite Z.mod_mod_divide; [exact H|]. exists (2 ^ 52). reflexivity.
Qed.

Lemma region_free_false_of_overlap : forall L (lo n a sz : word),
In (a, sz) L -> iv_overlap lo n a sz = true -> region_free L lo n = false.
Proof.
intros L lo n a sz Hin Hov. induction L as [|[a' sz'] L IH]; [destruct Hin|].
cbn [region_free]. destruct Hin as [E|Hin].
- injection E as -> ->. rewrite Hov. reflexivity.
- rewrite (IH Hin). apply andb_false_r.
Qed.

Lemma regs_ok_regupd_same : forall E sr R (r : Prelude.reg) v,
regs_ok E sr R -> getr R r = v -> r <> 0%bv -> regs_ok E sr (regupd R r v).
Proof.
intros E sr R r v HR Hv Hr r'. destruct (bv_eq_dec _ r' r) as [->|Hne].
- rewrite getr_same by exact Hr. rewrite <- Hv. apply HR.
- rewrite getr_other by exact Hne. apply HR.
Qed.

Lemma brk_grow_ok_aligned_refuted : forall m d (a sz : word),
let h := m_vmmaps m in
let b := vm_brk h in
(bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
(0 < bv_unsigned b)%Z -> (bv_unsigned b + d + page_size < 2 ^ 64)%Z ->
In (a, sz) (vm_reserved h ++ vm_maps h) ->
(bv_unsigned b < bv_unsigned a + bv_unsigned sz)%Z -> (bv_unsigned a < bv_unsigned b + d + 4096)%Z ->
Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false.
Proof.
intros m d a sz h b Hbal Hdal Hd Hb0 Hnw Hin Hov1 Hov2.
unfold page_size in Hnw. pose proof (u64_range b) as Hbr.
assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia.
rewrite (region_free_false_of_overlap _ b (Z_to_bv 64 (d + page_size)) a sz Hin).
- rewrite andb_false_r. reflexivity.
- unfold iv_overlap. rewrite (u64_lit (d + page_size)) by (unfold page_size in *; lia).
assert (Hov2' : (bv_unsigned a < bv_unsigned b + (d + page_size))%Z) by (unfold page_size in *; lia).
rewrite (proj2 (Z.ltb_lt _ _) Hov1), (proj2 (Z.ltb_lt _ _) Hov2'). reflexivity.
Qed.

Lemma brk_grow_ok_aligned_elim : forall m d,
let h := m_vmmaps m in
let b := vm_brk h in
(bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
(0 < bv_unsigned b)%Z -> (bv_unsigned b + d + page_size < 2 ^ 64)%Z ->
Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true
/\ (bv_unsigned b + d <= alloc_top h)%Z.
Proof.
intros m d h b Hbal Hdal Hd Hb0 Hnw Hok.
unfold page_size in Hnw. pose proof (u64_range b) as Hbr.
assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in Hok. fold h in Hok. fold b in Hok. rewrite Hureq in Hok.
rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) in Hok by lia. cbn [andb] in Hok.
rewrite (page_round_up_Z_aligned (bv_unsigned b)) in Hok by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in Hok
by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _)) in Hok by lia.
replace (Z_to_bv 64 (bv_unsigned b)) with b in Hok by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z in Hok by lia.
apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Htop Hrf]. apply Z.leb_le in Htop.
split; [exact Hrf | exact Htop].
Qed.

Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof. intros l1 l2. induction l1 as [|iv l1 IH]; cbn [sum_sizes app]; [lia|]. rewrite IH. lia. Qed.

Lemma zfill_in : forall (b l : word) m (x : word),
bv_unsigned b <= bv_unsigned x < bv_unsigned b + bv_unsigned l ->
zfill b l m x = Some (Z_to_bv 8 0).
Proof.
intros b l m x Hx. unfold zfill, zmem.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma region_free_intro : forall L (lo n : word),
(forall a sz, In (a, sz) L -> iv_overlap lo n a sz = false) -> region_free L lo n = true.
Proof.
intros L lo n H. induction L as [|[a sz] L IH]; [reflexivity|]. cbn [region_free].
rewrite (H a sz (or_introl eq_refl)). cbn [negb andb]. apply IH. intros a' sz' Hin. apply H. right. exact Hin.
Qed.

Lemma eager_used_sem_brk : forall m,
ivs_wf (vm_maps (m_vmmaps m)) ->
eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
intros m W. unfold eager_used, vm_backed_maps. rewrite <- maps_subtract_all_app_cuts.
apply (proj1 (live_msa _ _ W)).
Qed.

Lemma eager_used_cons_le : forall m (b n : word) h',
ivs_wf (vm_maps (m_vmmaps m)) -> iv_wf (b, n) ->
vm_maps h' = (b, n) :: vm_maps (m_vmmaps m) ->
vm_noaccess h' = vm_noaccess (m_vmmaps m) ->
eager_used (with_vmmaps h' m) <= eager_used m + bv_unsigned n.
Proof.
intros m b n h' W Wb Hm Hn.
assert (W' : ivs_wf (vm_maps (m_vmmaps (with_vmmaps h' m)))).
{ rewrite m_vmmaps_with_vmmaps, Hm. apply ivs_wf_cons; assumption. }
rewrite (eager_used_sem_brk _ W'), (eager_used_sem_brk _ W).
rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, Hm, Hn. cbn [sum_count].
pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (B (b, n)) (Z.to_nat (S (b, n)))) as Hc.
unfold iv_count. unfold S in *. cbn [snd] in *. pose proof (u64_range n). rewrite Z2Nat.id in Hc by lia. lia.
Qed.

Lemma vm_backing_used_le : forall Aset m,
A_wf Aset -> MInv Aset m -> vm_backing_used m <= eager_used m + A_bytes Aset.
Proof.
intros Aset m Hwf [N1 N2 N3 N4 N5]. rewrite vm_backing_used_split.
pose proof (allowed_pages_bound Aset (m_vm_materialized m) Hwf N1 N2 N3). lia.
Qed.

Lemma in_ivs_cons : forall z (a n : word) l,
in_ivs z ((a, n) :: l) = (((bv_unsigned a <=? z) && (z <? bv_unsigned a + bv_unsigned n)) || in_ivs z l)%bool.
Proof. reflexivity. Qed.

Lemma seps_cons_inv : forall p l, seps (p :: l) -> Forall (iv_disjoint p) l /\ seps l.
Proof. intros p l H. inversion H; subst; auto. Qed.

Lemma seps_In_disjoint : forall l p q,
seps l -> (forall iv, In iv l -> 0 < bv_unsigned (snd iv)) -> In p l -> In q l -> p <> q -> iv_disjoint p q.
Proof.
induction l as [|h t IH]; intros p q Hs Hpos Hp Hq Hne; [destruct Hp|].
apply seps_cons_inv in Hs as [Hf Ht].
destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
- exfalso. exact (Hne eq_refl).
- exact (proj1 (Forall_forall _ _) Hf q Hq).
- pose proof (proj1 (Forall_forall _ _) Hf p Hp) as D. unfold iv_disjoint in *. lia.
- apply IH; auto. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.

Lemma seps_NoDup : forall l, seps l -> (forall iv, In iv l -> 0 < bv_unsigned (snd iv)) -> List.NoDup l.
Proof.
induction l as [|h t IH]; intros Hs Hpos; [constructor|].
apply seps_cons_inv in Hs as [Hf Ht]. constructor.
- intros Hin. pose proof (proj1 (Forall_forall _ _) Hf h Hin) as D. pose proof (Hpos h (or_introl eq_refl)). unfold iv_disjoint in D. lia.
- apply IH; [exact Ht|]. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.

Lemma lit_cover_end_covered_b : forall fuel ivs x z,
x <= z < lit_cover_end fuel ivs x -> exists p, In p ivs /\ fst p <= z < snd p.
Proof.
induction fuel as [|f IH]; intros ivs x z Hz; cbn [lit_cover_end] in Hz; [lia|].
destruct (List.find (fun p => (Z.leb (fst p) x && Z.ltb x (snd p))%bool) ivs) as [p|] eqn:Hf; [|lia].
apply find_some in Hf as [Hin Hp]. apply andb_prop in Hp as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (Z_lt_le_dec z (snd p)) as [Hlt|Hge].
- exists p. split; [exact Hin | lia].
- apply (IH ivs (snd p) z). lia.
Qed.
Lemma lit_cover_apart_b : forall E ms (a n z : Z),
QxyE.maps_apart E ms a n ->
LOWTOP <= z < lit_cover ms -> ~ (a <= z < a + n).
Proof.
intros E ms a n z Hap Hz Hin. unfold lit_cover in Hz.
destruct (lit_cover_end_covered_b _ _ _ _ Hz) as (p & Hp & Hpz).
destruct (QxyE.lit_ivs_In ms p Hp) as (m & b & l & Hm & Hfg & Hb & Hl & ->). cbn [fst snd] in Hpz.
pose proof (Hap m Hm Hfg) as D. rewrite Hb, Hl, !QxyE.u_elit in D. lia.
Qed.

Section SoundB.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Hypothesis USP_ok : APS.usp_ok USP.
Hypothesis HULL_cov : APS.hull_cov SEGS A.
Hypothesis NX0_ge : APS.nx0_ge nx0.
Hypothesis argH_sp : forall E (a : word), argH E a = true -> USP <= bv_unsigned a.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT USP SINV argH FS0).
#[local] Notation ATOP := (APS.ATOP USP).
Let ATOP_range' : CEIL <= ATOP <= ATOP_MAX := APS.ATOP_range USP USP_ok.

Theorem node_exit_sound : exit_stmt SEGS A LIMIT USP SINV argH FS0.
Proof.
intros cs code E R FULL model HC Hec Hn.
destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
unfold node_exit in Hn.
destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
destruct (reg_lit cs 10) as [c0|] eqn:H10.
2:{ destruct a7; try discriminate; repeat (destruct p; try discriminate). }
destruct (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 10 c0 HC ltac:(lia) H10) as [G10 Hc0].
assert (H94 : (a7 = 94 \/ a7 = 93) /\ code = Z.land c0 255).
{ destruct a7 as [|p|p]; try discriminate;
repeat (destruct p as [p|p|]; try discriminate); injection Hn as <-; auto. }
destruct H94 as [Ha7 ->].
assert (G17 : getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94 \/ getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 93).
{ destruct Ha7 as [-> | ->].
- left. exact (proj1 (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 17 94 HC ltac:(lia) H17)).
- right. exact (proj1 (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 17 93 HC ltac:(lia) H17)). }
unfold cfg_of. rewrite <- (bv_and_255 c0 Hc0).
eapply srz_exit_at_lazy; [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact G10].
Qed.

Theorem node_sys_sound_YSetTid : sys_stmt SEGS A nx0 LIMIT USP SINV argH FS0 YSetTid.
Proof.
intros cs cs' E R FULL model T HC Hec Hn Hk.
destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
cbn [node_sys] in Hn. unfold node_settid in Hn.
destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
destruct (negb (a_tidset cs) && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
apply andb_prop in Hc as [Hts Hfresh]. apply negb_true_iff in Hts.
apply Some_inj in Hn. rename Hn into Ecs'.
destruct (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 17 96 HC ltac:(lia) H17) as [G17 _].
pose proof (co_tid _ _ _ _ _ _ _ _ _ _ _ _ HC Hts) as Htid.
destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
unfold cfg_of.
eapply (srz_set_tid_lazy SEGS); [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact Htid |].
intros tid Htidr.
set (v := nxt cs) in *.
set (E' := ext1 E v tid).
assert (Hag : env_agree v E E') by apply (ext1_agree).
pose proof (cs_ok_agree SEGS A nx0 LIMIT USP NX0_ge SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
replace (pc cs + 4) with (pc cs') by (rewrite <- Ecs'; reflexivity).
apply (Hk E' (regupd R 10 tid) FULL (with_tid tid model)).
- split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
-
assert (Hv : edenot E' (EVar v) = tid) by (cbn [edenot]; unfold E'; apply ext1_at).
assert (HMr : Mr A USP argH E' cs' (with_tid tid model) FULL = Mr A USP argH E' cs model FULL).
{ unfold Mr. f_equal. apply functional_extensionality. intros a. rewrite <- Ecs'.
unfold hid, vis, in_allow, in_vis, in_sh. reflexivity. }
assert (HA : allowA A E' cs' = allowA A E' cs) by (rewrite <- Ecs'; reflexivity).
subst cs'.
destruct HC'; constructor; rewrite ?HMr, ?HA;
cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next];
try assumption; try reflexivity; try discriminate.
+  apply (regs_ok_set_n); [exact co_regs0 | lia | exact Hv].
+  constructor; [|exact co_know0].
cbn [kentry_ok]. rewrite Hv. unfold PID_MAX. unfold PID_MAX_ENVELOPE in Htidr. lia.
+  destruct co_minv0; constructor; assumption.
- reflexivity.
Qed.

Lemma brk_keep_ok : forall E cs R FULL model,
cs_ok E cs R FULL model ->
cs_ok E (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) (regupd R 10 (vm_brk (m_vmmaps model))) FULL model.
Proof.
intros E cs R FULL model HC.
change (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4))
with (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs (a_ss cs)) 10 (a_brk cs)) (kn cs) (nxt cs))).
eapply (cs_ok_frame SEGS A LIMIT USP SINV argH SINV_frame FS0);
[exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)
| | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
cbn [mk_ss s_regs]. apply (regs_ok_set_n);
[exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) | lia | symmetry; exact (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.

Lemma brk_req_sound : forall E cs R FULL model d,
cs_ok E cs R FULL model -> brk_req cs = Some d ->
0 < d /\ d mod 4096 = 0 /\ d <= 2 ^ 40 /\
(bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (vm_brk (m_vmmaps model))) mod two64 = d.
Proof.
intros E cs R FULL model d HC H. unfold brk_req in H.
destruct (lit_diff (reg cs 10) (a_brk cs)) as [d0|] eqn:Hld; [|discriminate].
destruct (Z.ltb 0 d0 && Z.eqb (d0 mod 4096) 0 && Z.leb d0 (2 ^ 40))%bool eqn:Hc; [|discriminate].
injection H as <-.
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3.
destruct (lit_diff_sound E _ _ _ Hld) as [_ Hm].
rewrite (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC). auto.
Qed.

Lemma brk_base_ok_sound : forall E cs R FULL model d,
cs_ok E cs R FULL model -> brk_base_ok A cs d = true ->
let b := vm_brk (m_vmmaps model) in
bv_unsigned b mod 4096 = 0 /\ 0 < bv_unsigned b /\ img_hi A <= bv_unsigned b /\ bv_unsigned b + d <= KHI.
Proof.
intros E cs R FULL model d HC H b. unfold brk_base_ok in H.
apply andb_prop in H as [Hal H].
destruct (xlo (kn cs) (a_brk cs)) as [lo|] eqn:Hlo; [|discriminate].
destruct (xhi (kn cs) (a_brk cs)) as [hi|] eqn:Hhi; [|discriminate].
apply andb_prop in H as [H Hk]. apply andb_prop in H as [H0 Hi].
apply Z.ltb_lt in H0. apply Z.leb_le in Hi. apply Z.leb_le in Hk.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hlo) as L.
pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hhi) as Hh.
pose proof (page_aligned_sound SEGS E _ (kn cs) _ HK Hal) as P.
rewrite <- (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) in L, Hh, P. unfold b. lia.
Qed.

Lemma brk_req_val : forall E cs R FULL model d,
cs_ok E cs R FULL model -> brk_req cs = Some d -> brk_base_ok A cs d = true ->
getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d).
Proof.
intros E cs R FULL model d HC Hr Hb.
destruct (brk_req_sound E cs R FULL model d HC Hr) as (D1 & D2 & D3 & Dm).
destruct (brk_base_ok_sound E cs R FULL model d HC Hb) as (B1 & B2 & B3 & B4).
rewrite (reg_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)).
pose proof (u64_range (edenot E (reg cs 10))) as Hr10. pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
apply bv_eq. rewrite u64_lit by (unfold KHI in *; lia). unfold two64, KHI in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem node_sys_sound_YBrk : sys_stmt SEGS A nx0 LIMIT USP SINV argH FS0 YBrk.
Proof.
intros cs cs' E R FULL model T HC Hec Hn Hk.
destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
cbn [node_sys] in Hn. unfold node_brk1 in Hn.
destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
destruct (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.

assert (POST : forall ok : bool, (if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None) = Some cs' ->
srealizes SEGS (mkCfg (mkst (regupd R 10 (vm_brk (m_vmmaps model))) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) T).
{ intros ok Hok. destruct ok; [|discriminate]. apply Some_inj in Hok.
rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
replace (pc cs + 4) with (pc cs') by (rewrite <- Hok; reflexivity).
apply (Hk E (regupd R 10 (vm_brk (m_vmmaps model))) FULL model);
[split; apply env_agree_refl | rewrite <- Hok; apply brk_keep_ok; exact HC | reflexivity]. }
unfold cfg_of.
destruct (reg_lit cs 10) as [[|p|p]|] eqn:H10.
1: {
destruct (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 10 0 HC ltac:(lia) H10) as [G10 _].
eapply (srz_brk_query_lazy SEGS); [exact HF | exact HE | exact Hh | exact G17 | exact G10 |].
exact (POST true Hn). }

all: destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
all: destruct (brk_grow_blocked A cs d) eqn:Hblk; [|discriminate].
all: specialize (POST true Hn).
all: unfold brk_grow_blocked in Hblk; apply andb_prop in Hblk as [Hbase Hex].
all: destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
all: destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
all: pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
all: apply existsb_exists in Hex as [m [Hmin Hm]]; apply andb_prop in Hm as [Hm Hm2]; apply andb_prop in Hm as [Hnf Hm1]; apply negb_true_iff in Hnf.
all: pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm1) as L1;
pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm2) as L2;
cbn [xt_den] in L1, L2; rewrite <- (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) in L1, L2.
all: pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
all: eapply (srz_brk_grow_blocked_lazy SEGS); [exact HF | exact HE | exact Hh | exact G17 | exact G10
| rewrite u64_lit by (unfold KHI in *; lia); lia
| rewrite u64_lit by (unfold KHI in *; lia); pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ _ HC); lia
| rewrite u64_lit by (unfold KHI in *; lia); lia
| | exact POST].
all: apply (brk_grow_ok_aligned_refuted model d (edenot E (am_base m)) (edenot E (am_len m)));
[exact B1 | exact D2 | exact D1 | exact B2 | unfold KHI, page_size in *; lia | | lia | lia].
all: apply in_or_app; right; exact (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hmin Hnf).
Qed.

Definition foot_safe (E : env) (ms : list amap) (s l : Z) : Prop :=
(uE E e_sp0 - STACK_MAX <= s /\ s + l <= 2 ^ 64)
\/ (img_lo A <= s /\ s + l <= img_hi A)
\/ (exists m, In m ms /\ bv_unsigned (edenot E (am_base m)) <= s
/\ s + l <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)))
\/ (LOWTOP <= s /\ s < lit_cover ms /\ s + l <= lit_cover ms).

Lemma inside_maps_sound : forall E M k ms b off len,
know_ok SEGS E M k -> inside_maps k ms b off len = true ->
exists m, In m ms /\ bv_unsigned (edenot E (am_base m)) <= estart E (SA b off)
/\ estart E (SA b off) + elenZ E len <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)).
Proof.
intros E M k ms b off len HK. induction ms as [|m ms IH]; intros H; [discriminate|].
cbn [inside_maps] in H. apply orb_prop in H as [H|H].
- apply andb_prop in H as [_ H].
destruct (APS.xinside2_sound SEGS E M k b off len (am_base m) 0 (am_len m) HK H) as [H1 H2].
unfold estart, elenZ in H1, H2 |- *. cbn [a_base a_off] in H1, H2 |- *.
exists m. split; [left; reflexivity|]. lia.
- destruct (IH H) as (m' & Hin & H'). exists m'. split; [right; exact Hin | exact H'].
Qed.

Lemma safe_range_sound : forall E M k ms b off len,
know_ok SEGS E M k -> safe_range A k ms b off len = true ->
foot_safe E ms (estart E (SA b off)) (elenZ E len).
Proof.
intros E M k ms b off len HK H. unfold safe_range in H. apply orb_prop in H as [H|H].
- destruct (xhi k len) as [lh|] eqn:Hlh; [|discriminate].
destruct (base_range k b) as [[lo hi]|] eqn:Hbr; [|discriminate].
pose proof (xhi_sound SEGS E M k len lh HK Hlh) as L1.
destruct (base_range_sound SEGS E M k b lo hi HK Hbr) as [L2 L3].
unfold foot_safe, estart, elenZ. cbn [a_base a_off]. unfold two64 in H.
apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
+ destruct (Z.leb (hi + off + lh) (2 ^ 64)) eqn:H2; [|discriminate]. apply Z.leb_le in H2.
pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as G. cbn [xt_den] in G. unfold uE. left. lia.
+ apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
+ apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
right. right. right. pose proof (u64_range (edenot E len)). lia.
- right. right. left. exact (inside_maps_sound E M k ms b off len HK H).
Qed.

Lemma kn_grant_filter_sound : forall E M M' k ms lo n,
know_ok SEGS E M k ->
lo + n <= uE E e_sp0 - STACK_MAX -> (lo + n <= img_lo A \/ img_hi A <= lo) -> 0 < n ->
(forall m, In m ms -> bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= lo
\/ lo + n <= bv_unsigned (edenot E (am_base m))) ->
(forall x : word, bv_unsigned x < lo \/ lo + n <= bv_unsigned x -> M' x = M x) ->
know_ok SEGS E M' (kn_grant_filter A k ms).
Proof.
intros E M M' k ms lo n HK Hce Hih Hn Hms Hout.
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
assert (Hap : maps_apart E ms lo n) by (intros m Hm _; destruct (Hms m Hm); [right|left]; lia).
assert (SAFE : forall s l, foot_safe E ms s l -> 0 <= l -> s + l <= lo \/ lo + n <= s).
{ intros s l [F|[F|[F|F]]] Hl; unfold CEIL, KHI in *; [lia|lia| |].
- destruct F as (m & Hin & F1 & F2). destruct (Hms m Hin); lia.
- destruct F as (F1 & F2 & F3).
destruct (Z_le_gt_dec (s + l) lo) as [|C1]; [left; lia|]. destruct (Z_le_gt_dec (lo + n) s) as [|C2]; [right; lia|].
exfalso. apply (lit_cover_apart_b E ms lo n (Z.max s lo) Hap); lia. }
unfold kn_grant_filter, kimg_clip, know_ok. apply Forall_forall. intros K Hin.
apply filter_In in Hin as [Hin Hclip]. apply filter_In in Hin as [Hin Hkeep].
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
eapply (kentry_keep_sem SEGS); [exact HKK | | exact Hout].
unfold kfoot_apart.

destruct K; repeat match goal with x : saddr |- _ => destruct x as [?b ?o] end;
cbn [grant_keep_b] in Hkeep; cbn [kfoot]; try exact I;
lazymatch type of Hkeep with
| ((Nat.leb ?w 8 && _)%bool = true) =>
apply andb_prop in Hkeep as [Hw Hs]; apply Nat.leb_le in Hw;
pose proof (safe_range_sound E M k ms _ _ _ HK Hs) as F;
rewrite (elenZ_lit E (Z.of_nat w)) in F by lia; apply (SAFE _ _ F); lia
| (safe_range _ _ _ _ _ _ = true) =>
apply (SAFE _ _ (safe_range_sound E M k ms _ _ _ HK Hkeep)); apply u64_range
| (true = true) =>
apply andb_prop in Hclip as [Hc H3]; apply andb_prop in Hc as [H1 H2];
apply Z.leb_le in H1; apply Z.leb_le in H2; apply Z.leb_le in H3; lia
end.
Qed.

Lemma vis_add_shape : forall cs b n k cs2,
vis_add A LIMIT cs b n k = Some cs2 ->
flat_x (kn cs) (fst (split_lit b)) (snd (split_lit b)) n = true
/\ pc cs2 = pc cs /\ s_regs (a_ss cs2) = s_regs (a_ss cs) /\ a_vis cs2 = (b, n) :: a_vis cs
/\ a_maps cs2 = a_maps cs /\ a_ghost cs2 = a_ghost cs.
Proof.
intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv.  unfold vis_add_ref in Hv.
destruct (split_lit b) as [bb bk] eqn:Hsplit.
destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
destruct (xhi (kn cs) n) as [nhi|] eqn:Hnhi; [|discriminate].
match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection Hv as <-. cbn [fst snd pc a_ss s_pc s_regs a_vis a_maps a_ghost mk_ss].
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Hflat].
repeat split; try reflexivity. exact Hflat.
Qed.

Lemma node_brk2_core : forall cs csa csb dec E R FULL model TB,
cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_brk2 A LIMIT cs = Some (csa, csb, dec) ->
(forall d m, brk_req cs = Some d -> In m (a_maps cs) ->
bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned (vm_brk (m_vmmaps model))
\/ bv_unsigned (vm_brk (m_vmmaps model)) + (d + 4096) <= bv_unsigned (edenot E (am_base m))) ->
(forall d, brk_req cs = Some d ->
Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) = true) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) TB.
Proof.
intros cs csa csb dec E R FULL model TB HC Hec Hn APG HADM HkB.
destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
pose proof ATOP_range' as AT. pose proof USP_ok as HUSP. unfold APS.usp_ok, sp_window_lo, sp_window_hi in HUSP.
pose proof (proj1 (co_sp0 _ _ _ _ _ _ _ _ _ _ _ _ HC)) as Hsp0.
unfold node_brk2 in Hn.
destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
destruct (brk_grow_open A LIMIT cs d && AP.expr_vars_lt (nxt cs) (reg cs 10))%bool eqn:Hc; [|discriminate].
apply andb_prop in Hc as [Hposs _].
specialize (APG d). specialize (HADM d eq_refl).
set (klearn := if brk_grow_possible A LIMIT cs d then [] else kdisj_all (a_maps cs) (a_brk cs) (ELit (d + 4096))) in Hn.
destruct (split_lit (a_brk cs)) as [bb bk] eqn:Hsplit.
set (csB := ACS _ _ _ _ _ _ _ _ _ _ _) in Hn.
destruct (vis_add A LIMIT csB (a_brk cs) (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB)) as [csB'|] eqn:Hva; [|discriminate].
assert (EcsA : set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4) = csa) by congruence.
assert (EcsB : csB' = csb) by congruence. subst csB'. clear Hn.

destruct (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
unfold brk_grow_open in Hposs.
apply andb_prop in Hposs as [Hposs Hbudget]. apply andb_prop in Hposs as [Hbase Hnf].
unfold budget_ok in Hbudget. apply Z.leb_le in Hbudget.
destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
pose proof (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hres.
pose proof (proj1 (APS.maps_match_exact nx0 (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC)) as Hmaps.
pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hlim. pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hsbrk.
pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hbrk.
set (h := m_vmmaps model) in *. set (b := vm_brk h) in *.
pose proof (u64_range b) as Hbr.
assert (Eb : edenot E (a_brk cs) = b) by (symmetry; exact Hbrk).

destruct (vis_add_shape csB (a_brk cs) (ELit d) _ _ Hva) as (Hflat & HpcB' & HregsB' & HvisB' & HmapsB' & HghostB').
rewrite Hsplit in Hflat. cbn [fst snd] in Hflat.

assert (APARTG : forall m, In m (a_maps cs) ->
bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
\/ bv_unsigned b + (d + 4096) <= bv_unsigned (edenot E (am_base m))).
{ intros m Hin. exact (APG m eq_refl Hin). }

assert (HKlearn : forall M, know_ok SEGS E M klearn).
{ intros M. unfold klearn. destruct (brk_grow_possible A LIMIT cs d); [constructor|].
unfold kdisj_all. apply Forall_flat_map. apply Forall_forall. intros m Hm.
destruct (is_fog m) eqn:Hfm; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Eb. rewrite (u64_lit (d + 4096)) by (unfold KHI in *; lia).
pose proof (APARTG m Hm) as D. lia. }
assert (HKf : know_ok SEGS E (Mr A USP argH E cs model FULL) (kn csB)).
{ unfold csB, kn. cbn [a_ss mk_ss s_know]. apply Forall_app. split; [apply HKlearn|]. unfold kn_grant_filter, kimg_clip.
apply know_ok_filter. apply know_ok_filter. exact HK. }
destruct (flat_x_sound SEGS E _ (kn csB) bb bk (ELit d) HKf Hflat) as (Fb1 & Fb2 & Fb3).
cbn [edenot] in Fb2, Fb3. rewrite (u64_lit d) in Fb2, Fb3 by (unfold KHI in *; lia).
assert (Hest : estart E (SA bb bk) = bv_unsigned b).
{ rewrite <- Eb. symmetry. apply (u_of_split E (a_brk cs) bb bk Hsplit). lia. }
assert (APART : forall m, In m (a_maps cs) ->
bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
\/ bv_unsigned b + d <= bv_unsigned (edenot E (am_base m))).
{ intros m Hin. destruct (APARTG m Hin) as [Hm|Hm]; [left; exact Hm | right; lia]. }

set (dw := Z_to_bv 64 d). assert (Udw : bv_unsigned dw = d) by (unfold dw; apply u64_lit; unfold KHI in *; lia).
assert (Hrf : region_free (vm_reserved h ++ vm_maps h) b dw = true).
{ apply region_free_intro. intros a sz Hin. apply in_app_iff in Hin as [Hin|Hin].
- rewrite Hres in Hin.
pose proof (proj1 (Forall_forall _ _) RES_hull _ Hin) as [R1 R2]. cbn [fst snd] in R1, R2.
unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge. lia.
- rewrite Hmaps in Hin. apply in_map_iff in Hin as (m & Em & Hin).
unfold amap_den in Em. injection Em as <- <-.
unfold iv_overlap. rewrite Udw. apply andb_false_iff.
destruct (APART m Hin) as [Hm|Hm]; [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; lia]. }

set (dwg := Z_to_bv 64 (d + page_size)).
assert (Udwg : bv_unsigned dwg = d + page_size) by (unfold dwg; apply u64_lit; unfold KHI, page_size in *; lia).
assert (Hrfg : region_free (vm_reserved h ++ vm_maps h) b dwg = true).
{ apply region_free_intro. intros a sz Hin. apply in_app_iff in Hin as [Hin|Hin].
- rewrite Hres in Hin.
pose proof (proj1 (Forall_forall _ _) RES_hull _ Hin) as [R1 R2]. cbn [fst snd] in R1, R2.
unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge. lia.
- rewrite Hmaps in Hin. apply in_map_iff in Hin as (m & Em & Hin).
unfold amap_den in Em. injection Em as <- <-.
unfold iv_overlap. rewrite Udwg. apply andb_false_iff.
destruct (APARTG m Hin) as [Hm|Hm]; [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; unfold page_size in *; lia]. }
pose proof (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs) as HAwf.
assert (Hused : vm_backing_used model <= a_eager cs + a_abytes cs).
{ pose proof (vm_backing_used_le _ _ HAwf (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)).
pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC). lia. }
assert (Hadm : Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true) by exact HADM.
unfold cfg_of.
eapply (srz_brk_grow_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w d TB HF HE Hh G17);
fold h b; [exact B1 | exact D2 | exact D1 | exact B2 | unfold KHI in *; lia
| lia | exact G10 | exact Hadm |].
-
set (req := Z_to_bv 64 (bv_unsigned b + d)) in *. fold dw.
assert (Ureq : bv_unsigned req = bv_unsigned b + d) by (unfold req; apply u64_lit; unfold KHI in *; lia).
set (h' := mkVmMapsFull (vm_reserved h) ((b, dw) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
set (model' := with_vmmaps h' model). set (FULL' := zfill b dw FULL). set (R' := regupd R 10 req).
assert (Hvm' : m_vmmaps model' = h') by reflexivity.
assert (Hlz' : m_vm_lazy model' = m_vm_lazy model) by reflexivity.

assert (V1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
vis A USP E csB model' x = vis A USP E cs model x).
{ intros x Hx. unfold vis. rewrite Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw.
replace ((bv_unsigned b <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned b + d))%bool with false
by (symmetry; apply andb_false_iff; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
reflexivity. }
assert (H1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
hid A USP argH E csB model' x = hid A USP argH E cs model x).
{ intros x Hx. unfold hid. rewrite (V1 x Hx). reflexivity. }
assert (F1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x -> FULL' x = FULL x).
{ intros x Hx. unfold FULL'. apply zfill_out. rewrite Udw. exact Hx. }
assert (M1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
Mr A USP argH E csB model' FULL' x = Mr A USP argH E cs model FULL x).
{ intros x Hx. unfold Mr, mrestrict. rewrite (H1 x Hx), (F1 x Hx). reflexivity. }

assert (NA : forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d ->
in_ivs (bv_unsigned x) (vm_noaccess h) = false).
{ intros x Hx. destruct (in_ivs (bv_unsigned x) (vm_noaccess h)) eqn:Hna; [|reflexivity]. exfalso.
pose proof (co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC (bv_unsigned x) Hna) as Hm. fold h in Hm. rewrite Hmaps in Hm.
apply (in_ivs_true) in Hm as (iv & Hin & Hiv).
apply in_map_iff in Hin as (m & <- & Hin). unfold amap_den in Hiv. cbn [fst snd] in Hiv.
destruct (APART m Hin); lia. }
assert (Wf : ivs_wf (vm_maps h)) by exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)).
assert (Wb : iv_wf (b, dw)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite Udw; unfold KHI in *; lia).
rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
replace (pc cs + 4) with (pc csb) by (rewrite HpcB'; reflexivity).
apply (HkB E R' FULL' model'); [split; apply env_agree_refl | | reflexivity].
apply (vis_add_sound SEGS A LIMIT USP (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) SHADOW_ok USP_ok SINV argH argH_sp FS0 0%nat
E csB (a_brk cs) (ELit d) _ csb R' FULL' model' Hva).
+
subst b. subst h.
destruct HC; constructor; unfold csB;
cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next];
fold csB; try assumption; try reflexivity.
all: try (change (m_halted model') with (m_halted model); assumption).
all: lazymatch goal with
| |- regs_ok _ _ _ =>
apply regs_ok_regupd_same; [exact co_regs0 | exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate]
| |- know_ok _ _ _ _ =>
apply Forall_app; split; [apply HKlearn|];
apply (kn_grant_filter_sound E (Mr A USP argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned (vm_brk (m_vmmaps model))) d HK);
[rewrite Hsp0; unfold CEIL, KHI, STACK_MAX in *; lia | right; exact B3 | lia | exact APART | exact M1]
| |- maps_match _ _ (vm_maps _) =>
rewrite Hvm'; unfold h'; cbn [vm_maps maps_match is_fog am_kind mkind_eqb];
exists (vm_maps (m_vmmaps model)); split; [|exact co_maps0];
unfold amap_den; cbn [am_base am_len edenot]; rewrite Eb; fold dw; reflexivity
| |- seps _ =>
rewrite Hvm'; unfold h'; cbn [vm_maps]; constructor; [|exact co_seps0];
rewrite Hmaps; apply Forall_forall; intros iv Hin; apply in_map_iff in Hin as (m & <- & Hin);
unfold iv_disjoint, amap_den; cbn [fst snd]; rewrite Udw; destruct (APART m Hin); lia
| |- model_ivs_wf _ =>
apply model_ivs_wf_with_vmmaps; [exact co_wf0 | apply ivs_wf_cons; [exact Wb | exact Wf] | exact (proj1 (proj2 co_wf0)) | reflexivity]
| |- Forall _ (vm_maps _) =>
rewrite Hvm'; unfold h'; cbn [vm_maps]; constructor; [|exact co_bounds0];
cbn [fst snd]; rewrite Udw; unfold CEIL, KHI, ATOP_MAX in *; lia
| |- forall z, in_ivs z _ = true -> _ =>
intros z Hz; rewrite Hvm'; unfold h'; cbn [vm_maps]; rewrite in_ivs_cons;
rewrite (co_nasub0 z Hz); apply orb_true_r
| |- Forall (hole_ok _ _ _ _ _) (_ :: _) =>
constructor; [intros Hk; discriminate|];
rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps];
apply Forall_forall; intros m0 Hm0 Hk0;
destruct (proj1 (Forall_forall _ _) co_holes0 m0 Hm0 Hk0) as [HF1 HF2]; split; [|exact HF2];
intros iv Hiv; apply in_app_iff in Hiv as [Hiv|[<-|Hiv]];
[ apply HF1; apply in_app_iff; left; exact Hiv
| cbn [fst snd]; rewrite Udw; unfold uE; destruct (APART m0 Hm0); lia
| apply HF1; apply in_app_iff; right; exact Hiv ]
| |- Forall _ (_ :: _) =>
constructor; [first [intros Hk; discriminate | intros [Hk|Hk]; discriminate] | assumption]
| |- sum_sizes _ <= _ =>
rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps]; rewrite sum_sizes_app in *; cbn [sum_sizes snd]; rewrite Udw;
cbn [sum_sizes] in co_totsz0; lia
| |- bv_unsigned (vm_init_sp _) = USP =>
rewrite Hvm'; unfold h'; cbn [vm_init_sp]; exact co_isp0
| |- vm_brk _ = _ =>
rewrite Hvm'; unfold h'; cbn [vm_brk];
rewrite <- (reg_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 10 ltac:(constructor; assumption) ltac:(lia)); symmetry; exact G10
| |- bv_unsigned (vm_start_brk _) <= _ =>
rewrite Hvm'; unfold h'; cbn [vm_start_brk vm_brk]; rewrite Ureq; lia
| |- eager_used _ <= _ =>
pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He; lia
| |- MInv _ _ =>
eapply MInv_transport; [exact co_minv0 | reflexivity | reflexivity |];
pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He;
rewrite Hvm'; unfold h'; cbn [vm_limit]; rewrite co_limit0;
change (allowA A E csB) with (allowA A E cs); lia
| |- forall a, hid _ _ _ _ _ _ a = true -> _ =>
intros a Ha Hm Hna Hlz Hgh;
rewrite Hvm' in Hm; unfold h' in Hm; cbn [vm_maps] in Hm; rewrite in_ivs_cons, Udw in Hm;
destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)))) as [Hlt|Hge];
[|destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)) + d)) as [Hlt2|Hge2]];
[ rewrite (F1 a ltac:(lia)); rewrite (H1 a ltac:(lia)) in Ha; apply (co_zero0 a Ha); [|exact Hna|exact Hlz|exact Hgh];
apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [Hm _]; apply Z.leb_le in Hm; lia
| unfold FULL'; apply zfill_in; rewrite Udw; lia
| rewrite (F1 a ltac:(lia)); rewrite (H1 a ltac:(lia)) in Ha; apply (co_zero0 a Ha); [|exact Hna|exact Hlz|exact Hgh];
apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [_ Hm]; apply Z.ltb_lt in Hm; lia ]
| |- SINV _ _ =>
eapply SINV_frame; [|exact co_sinv0]; intros a Ha; apply F1; pose proof (argH_sp _ _ Ha); unfold CEIL, KHI in *; lia
| |- ?g => idtac "UNSOLVED FIELD:" g
end.
+
assert (INB : forall i, 0 <= i < d ->
Mr A USP argH E csb model' FULL' (Z_to_bv 64 (bv_unsigned b + i)) = Some (Z_to_bv 8 0)).
{ intros i Hi. set (a := Z_to_bv 64 (bv_unsigned b + i)).
assert (Ua : bv_unsigned a = bv_unsigned b + i) by (unfold a; apply u64_lit; unfold KHI in *; lia).
assert (Hargh : argH E a = false).
{ destruct (argH E a) eqn:Ha; [|reflexivity]. pose proof (argH_sp _ _ Ha). unfold CEIL, KHI in *. lia. }
assert (Hvis : vis A USP E csb model' a = true).
{ assert (Hal : in_allow A E csb (bv_unsigned a) = true).
{ unfold in_allow, in_vis. rewrite HvisB'. cbn [existsb fst snd]. unfold uE at 1 2 3. rewrite Eb. cbn [edenot].
rewrite (u64_lit d) by (unfold KHI in *; lia). rewrite Ua.
replace (bv_unsigned b <=? bv_unsigned b + i) with true by (symmetry; apply Z.leb_le; lia).
replace (bv_unsigned b + i <? bv_unsigned b + d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
unfold vis. rewrite Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw, Hal.
rewrite (NA a) by lia. rewrite Ua.
replace (bv_unsigned b <=? bv_unsigned b + i) with true by (symmetry; apply Z.leb_le; lia).
replace (bv_unsigned b + i <? bv_unsigned b + d) with true by (symmetry; apply Z.ltb_lt; lia).
cbn [andb orb negb]. rewrite !orb_true_r. reflexivity. }
unfold Mr, mrestrict, hid. rewrite Hargh, Hvis. cbn [negb orb]. unfold FULL'. apply zfill_in. rewrite Udw, Ua. lia. }
assert (Hfl : flat E (SA bb bk) (elenZ E (ELit d))).
{ unfold flat. rewrite (elenZ_lit E d) by (unfold KHI in *; lia). rewrite Hest. unfold KHI in *. lia. }
constructor; [|constructor].
*  cbn [kentry_ok]. split; [exact Hfl|]. intros off m Hoff Hm.
rewrite (elenZ_lit E d) in Hm by (unfold KHI in *; lia). rewrite Hest.
destruct m as [|m']; [reflexivity|].
apply store_ok_of_all; [rewrite u64_lit by (unfold KHI in *; lia); unfold KHI in *; lia|].
intros x Hx. rewrite u64_lit in Hx by (unfold KHI in *; lia).
unfold wview. replace x with (Z_to_bv 64 (bv_unsigned b + (bv_unsigned x - bv_unsigned b)))
by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); unfold KHI in *; lia).
rewrite (INB (bv_unsigned x - bv_unsigned b)) by lia. discriminate.
*  cbn [kentry_ok]. split; [exact Hfl|]. intros i Hi.
rewrite (elenZ_lit E d) in Hi by (unfold KHI in *; lia). rewrite Hest. apply INB. exact Hi.
*
assert (HK1 : know_ok SEGS E (Mr A USP argH E csB model' FULL') (kn csB)).
{ unfold csB, kn. cbn [a_ss mk_ss s_know]. apply Forall_app. split; [apply HKlearn|].
apply (kn_grant_filter_sound E (Mr A USP argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned b) d HK);
[rewrite Hsp0; unfold CEIL, KHI, STACK_MAX in *; lia | right; exact B3 | lia | exact APART | exact M1]. }
unfold Mr in HK1 |- *.
apply (know_ok_unhide SEGS A E (hid A USP argH E csB model') (hid A USP argH E csb model') FULL' (kn csB)).
-- apply (H_off_segments_cs SEGS A USP SEGS_in_hull HULL_ok argH argH_high).
-- unfold csB, kn. cbn [a_ss mk_ss s_know]. apply (kimg_in_hull_app A); [|unfold kn_grant_filter; apply (kimg_clip_in_hull A)].
unfold klearn. destruct (brk_grow_possible A LIMIT cs d); [constructor|].
unfold kimg_in_hull, kdisj_all. apply Forall_flat_map. apply Forall_forall. intros m0 _.
destruct (is_fog m0); [constructor|]. constructor; [exact I | constructor].
-- intros a Ha. unfold hid in Ha |- *. apply orb_true_iff in Ha. apply orb_true_iff.
destruct Ha as [Ha|Ha]; [left; exact Ha|]. right. apply negb_true_iff in Ha. apply negb_true_iff.
destruct (vis A USP E csB model' a) eqn:Hv; [|reflexivity]. exfalso.
rewrite (vis_mono A USP E csB csb model' a) in Ha; [discriminate| |exact Hv].
intros z Hz. unfold in_allow, in_vis, in_sh in Hz |- *. rewrite HvisB'. cbn [existsb].
apply orb_true_iff in Hz. apply orb_true_iff.
destruct Hz as [Hz|Hz]; [left|right]; apply orb_true_iff; right; exact Hz.
-- intros a Ha. apply (hid_hull A USP HULL_ok argH argH_high). exact Ha.
-- exact HK1.
Qed.

Theorem node_brk2_sound : brk2_stmt SEGS A nx0 LIMIT USP SINV argH FS0.
Proof.
intros cs csa csb E R FULL model TB HC Hec Hn HkB.
pose proof Hn as Hn0. unfold node_brk2 in Hn.
destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
destruct (brk_grow_open A LIMIT cs d && AP.expr_vars_lt (nxt cs) (reg cs 10))%bool eqn:Hc; [|discriminate].
apply andb_prop in Hc as [Hopen _].
destruct (split_lit (a_brk cs)) as [bb bk] eqn:Hsplit.
set (csB := ACS _ _ _ _ _ _ _ _ _ _ _) in Hn.
destruct (vis_add A LIMIT csB (a_brk cs) (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB)) as [csB'|] eqn:Hva; [|discriminate].
assert (Hposs : brk_grow_possible A LIMIT cs d = true) by congruence.
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
pose proof ATOP_range' as AT.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
pose proof Hposs as Hposs0. unfold brk_grow_possible in Hposs. rewrite Hsplit in Hposs.
apply andb_prop in Hposs as [Hposs Hbudget]. apply andb_prop in Hposs as [Hbase Hapart]. apply andb_prop in Hbase as [Hbase Hnf].
unfold budget_ok in Hbudget. apply Z.leb_le in Hbudget.
destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hbrk.
pose proof (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hres.
pose proof (proj1 (APS.maps_match_exact nx0 (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC)) as Hmaps.
pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hlim.
set (h := m_vmmaps model) in *. set (b := vm_brk h) in *. pose proof (u64_range b) as Hbr.
assert (Eb : edenot E (a_brk cs) = b) by (symmetry; exact Hbrk).

destruct (vis_add_shape csB (a_brk cs) (ELit d) _ _ Hva) as (Hflat & _).
rewrite Hsplit in Hflat. cbn [fst snd] in Hflat.
assert (HKf : know_ok SEGS E (Mr A USP argH E cs model FULL) (kn csB)).
{ unfold csB, kn. cbn [a_ss mk_ss s_know]. rewrite Hposs0. cbn [app]. unfold kn_grant_filter, kimg_clip.
apply know_ok_filter. apply know_ok_filter. exact HK. }
destruct (flat_x_sound SEGS E _ (kn csB) bb bk (ELit d) HKf Hflat) as (Fb1 & Fb2 & Fb3).
cbn [edenot] in Fb2, Fb3. rewrite (u64_lit d) in Fb2, Fb3 by (unfold KHI in *; lia).
assert (Hest : estart E (SA bb bk) = bv_unsigned b).
{ rewrite <- Eb. symmetry. apply (u_of_split E (a_brk cs) bb bk Hsplit). lia. }
assert (APARTG : forall m, In m (a_maps cs) ->
bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
\/ bv_unsigned b + (d + 4096) <= bv_unsigned (edenot E (am_base m))).
{ intros m Hin. pose proof (proj1 (forallb_forall _ _) Hapart m Hin) as Hm. cbv beta in Hm.
pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hm) as Hd.
rewrite Hest in Hd. rewrite (elenZ_lit E (d + 4096)) in Hd by (unfold KHI in *; lia).
unfold estart, elenZ in Hd. cbn [a_base a_off] in Hd. lia. }

set (dwg := Z_to_bv 64 (d + page_size)).
assert (Udwg : bv_unsigned dwg = d + page_size) by (unfold dwg; apply u64_lit; unfold KHI, page_size in *; lia).
assert (Hrfg : region_free (vm_reserved h ++ vm_maps h) b dwg = true).
{ apply region_free_intro. intros a sz Hin. apply in_app_iff in Hin as [Hin|Hin].
- rewrite Hres in Hin.
pose proof (proj1 (Forall_forall _ _) RES_hull _ Hin) as [R1 R2]. cbn [fst snd] in R1, R2.
unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge. lia.
- rewrite Hmaps in Hin. apply in_map_iff in Hin as (m & Em & Hin).
unfold amap_den in Em. injection Em as <- <-.
unfold iv_overlap. rewrite Udwg. apply andb_false_iff.
destruct (APARTG m Hin) as [Hm|Hm]; [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; unfold page_size in *; lia]. }
pose proof (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs) as HAwf.
assert (Hused : vm_backing_used model <= a_eager cs + a_abytes cs).
{ pose proof (vm_backing_used_le _ _ HAwf (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)).
pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC). lia. }
assert (Hadm : Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true).
{ apply (brk_grow_ok_aligned_intro model d); fold h b;
[exact B1 | exact D2 | exact D1 | exact B2 | rewrite alloc_ceiling_val; unfold KHI in *; lia
| exact (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)))) | exact Hrfg |].
rewrite Hlim. lia. }
eapply (node_brk2_core cs csa csb true E R FULL model TB HC Hec Hn0); [| |exact HkB].
- intros d' m Hd' Hin. assert (d' = d) by congruence. subst d'. exact (APARTG m Hin).
- intros d' Hd'. assert (d' = d) by congruence. subst d'. exact Hadm.
Qed.

Lemma t_alt2_same : forall T, t_eq (t_alt2 T T) T.
Proof. intros T tr. unfold t_alt2. tauto. Qed.

Theorem node_brk2u_sound : brk2u_stmt SEGS A nx0 LIMIT USP SINV argH FS0.
Proof.
intros cs csa csb E R FULL model T HC Hec Hn HkA HkB.
pose proof Hn as Hn0. unfold node_brk2 in Hn.
destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
destruct (brk_grow_open A LIMIT cs d && AP.expr_vars_lt (nxt cs) (reg cs 10))%bool eqn:Hc; [|discriminate].
apply andb_prop in Hc as [Hopen _].
destruct (split_lit (a_brk cs)) as [bb bk] eqn:Hsplit.
set (csB := ACS _ _ _ _ _ _ _ _ _ _ _) in Hn.
destruct (vis_add A LIMIT csB (a_brk cs) (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB)) as [csB'|] eqn:Hva; [|discriminate].
assert (EcsA : set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4) = csa) by congruence.
destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
unfold brk_grow_open in Hopen.
apply andb_prop in Hopen as [Hopen Hbudget]. apply andb_prop in Hopen as [Hbase Hnf].
destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
destruct (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hbrk.
pose proof (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hres.
pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hsbrk.
pose proof (proj1 (APS.maps_match_exact nx0 (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC)) as Hmaps.
set (h := m_vmmaps model) in *. set (b := vm_brk h) in *. pose proof (u64_range b) as Hbr.
destruct (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d))) eqn:Hok.
-
assert (Hnw : bv_unsigned b + d + page_size < 2 ^ 64) by (unfold KHI, page_size in *; lia).
destruct (brk_grow_ok_aligned_elim model d B1 D2 D1 B2 Hnw Hok) as [Hrfg _]. fold h b in Hrfg.
eapply (node_brk2_core cs csa csb false E R FULL model T HC Hec Hn0); [| |exact HkB].
+ intros d' m Hd' Hin. assert (d' = d) by congruence. subst d'. fold h b.
assert (HinL : In (amap_den E m) (vm_reserved h ++ vm_maps h)).
{ apply in_app_iff. right. rewrite Hmaps. apply in_map. exact Hin. }
pose proof (Q6EJ.Mq1.region_free_In _ b (Z_to_bv 64 (d + page_size)) (fst (amap_den E m)) (snd (amap_den E m)) Hrfg
ltac:(destruct (amap_den E m); exact HinL)) as D0.
unfold amap_den in D0. cbn [fst snd] in D0. rewrite (u64_lit (d + page_size)) in D0 by (unfold KHI, page_size in *; lia).
unfold page_size in D0. lia.
+ intros d' Hd'. assert (d' = d) by congruence. subst d'. exact Hok.
-
unfold cfg_of.
eapply (srz_brk_grow_blocked_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w _ T HF HE Hh G17 G10);
fold h b; [rewrite u64_lit by (unfold KHI in *; lia); lia | rewrite u64_lit by (unfold KHI in *; lia); lia
| rewrite u64_lit by (unfold KHI in *; lia); lia | exact Hok |].
rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
replace (pc cs + 4) with (pc csa) by (rewrite <- EcsA; reflexivity).
apply (HkA E (regupd R 10 b) FULL model);
[split; apply env_agree_refl | rewrite <- EcsA; apply (brk_keep_ok); exact HC | reflexivity].
Qed.

End SoundB.

Section SoundMunmap.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : length (segments_reserved SEGS) = n_res A.
Hypothesis HULL_ok : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis SHADOW_ok : 0 <= shadow_off A <= 2 ^ 47.
Hypothesis RES_hullH : RES_hull_def SEGS A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis USP_ok : APS.usp_ok USP.
Hypothesis argH_sp : forall E (a : word), argH E a = true -> USP <= bv_unsigned a.
Variable FS0 : Fs.Fs.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT USP SINV argH FS0).
#[local] Notation HID := (APS.hid A USP argH).
#[local] Notation VIS := (APS.vis A USP).
#[local] Notation MR := (APS.Mr A USP argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).
#[local] Notation ATOP := (APS.ATOP USP).
Let ATOP_range' : CEIL <= ATOP <= ATOP_MAX := APS.ATOP_range USP USP_ok.

Let reg_sound' := APS.reg_sound SEGS A LIMIT USP SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT USP SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let hid_agree' := APS.hid_agree A nx0 USP argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT USP HS XN XE XB SHADOW_ok USP_ok SINV argH argH_sp FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A USP HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A USP SEGS_in_hull HULL_ok argH argH_high.

Lemma mmap_len_sound : forall E cs R FULL model ne nlo nhi,
CSOK E cs R FULL model -> mmap_len cs = Some (ne, nlo, nhi) ->
let len := bv_unsigned (edenot E (reg cs 11)) in
getr R (Z_to_bv 5 11) = Z_to_bv 64 len
/\ 0 < len < 2 ^ 64
/\ edenot E ne = Z_to_bv 64 (page_round_up_Z len)
/\ 0 < nlo /\ nlo <= page_round_up_Z len <= nhi
/\ page_round_up_Z len mod 4096 = 0
/\ (forall E', edenot E' (reg cs 11) = edenot E (reg cs 11) -> edenot E' ne = edenot E ne).
Proof.
intros E cs R FULL model ne nlo nhi HC HML len.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
pose proof (u64_range (edenot E (reg cs 11))) as Hr.
rewrite mmap_len_eq in HML.  unfold mmap_len_ref in HML.
destruct (reg_lit cs 11) as [lz|] eqn:H11.
- destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
assert (Hlen : len = lz).
{ unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
rewrite page_up_eq.
split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [apply page_round_up_Z_aligned'|]. intros E' _. reflexivity.
- destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection HML as <- <- <-.
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo Hal].
apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal. apply Z.leb_le in Hhi.
pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
destruct (ealign_sound SEGS E _ (kn cs) (reg cs 11) HK) as [_ Hdiv].
assert (Hmod : len mod 4096 = 0).
{ unfold len. destruct Hdiv as [q Hq]. rewrite Hq.
replace (2 ^ ealign (kn cs) (reg cs 11)) with (2 ^ (ealign (kn cs) (reg cs 11) - 12) * 4096)
by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
assert (Hpr : page_round_up_Z len = len).
{ unfold page_round_up_Z, page_size.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold len in *. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
rewrite Hpr.
split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
split; [unfold len in *; lia|]. split; [symmetry; apply Z_to_bv_bv_unsigned|].
split; [lia|]. split; [unfold len in *; lia|]. split; [exact Hmod|].
intros E' HE'. exact HE'.
Qed.

Lemma bv5_10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_11 : (11%bv : bv 5) = Z_to_bv 5 (Z.of_nat 11). Proof. apply bv_eq. reflexivity. Qed.

Lemma bv5_17 : (17%bv : bv 5) = Z_to_bv 5 (Z.of_nat 17). Proof. apply bv_eq. reflexivity. Qed.

Lemma some_inj : forall {T} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. injection H as H1. exact H1. Qed.

Lemma KHI_eq : kHighMemBeg = KHI.
Proof. reflexivity. Qed.

Lemma split_flat_estart : forall E M k e b off n,
know_ok SEGS E M k -> split_lit e = (b, off) -> flat_x k b off n = true ->
estart E (SA b off) = bv_unsigned (edenot E e)
/\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
intros E M k e b off n HK Hsp Hfl.
destruct (APS.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3).
pose proof (APS.u_of_split E e b off Hsp ltac:(lia)). repeat split; lia.
Qed.

Lemma covered_maps_subtract : forall l lo hi x,
ivs_wf l -> lo <= hi ->
covered (maps_subtract l lo hi) x = (covered l x && negb (in_rng lo hi x))%bool.
Proof. intros. apply (proj2 (proj2 (maps_subtract_sem l lo hi H H0))). Qed.

Lemma len_eqb_sound : forall E M k n m,
know_ok SEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
intros E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
- apply expr_eqb_eq in H. subst. reflexivity.
- apply andb_prop in H as [H1 H2].
pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as B1.
cbn [xt_den] in A1, B1. apply bv_eq. lia.
Qed.

Lemma kzero_x_sound : forall E M allkn k b off n,
know_ok SEGS E M allkn -> know_ok SEGS E M k -> kzero_x allkn k b off n = true ->
0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64
/\ forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n -> M x = Some (Z_to_bv 8 0).
Proof.
intros E M allkn k b off n HA HK. induction k as [|K k IH]; intros H; [discriminate|].
apply Forall_cons_iff in HK as [HKK HK]. cbn [kzero_x] in H.
assert (CONT : forall zb zk zn,
kentry_ok SEGS E M (KZero (SA zb zk) zn) ->
estart E (SA zb zk) <= estart E (SA b off) -> estart E (SA b off) + elenZ E n <= estart E (SA zb zk) + elenZ E zn ->
0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64
/\ forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n -> M x = Some (Z_to_bv 8 0)).
{ intros zb zk zn [Hfl Hz] I1 I2. destruct Hfl as (F1 & F2 & F3 & F4). split; [lia|]. split; [lia|].
intros x Hx. replace x with (Z_to_bv 64 (estart E (SA zb zk) + (bv_unsigned x - estart E (SA zb zk)))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); lia).
apply Hz. lia. }
destruct K as [|[zb zk] zn| | | | | | | |]; try (apply IH; assumption).
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end.
- destruct (expr_eqb b zb && (zk <=? off))%bool eqn:Hb; [|discriminate].
apply andb_prop in Hb as [Hb Hzk]. apply expr_eqb_eq in Hb. subst zb. apply Z.leb_le in Hzk.
destruct (xhi allkn n) as [nh|] eqn:Hnh; [|discriminate]. destruct (xlo allkn zn) as [zl|] eqn:Hzl; [|discriminate].
apply Z.leb_le in Hc. pose proof (xhi_sound SEGS E M allkn n nh HA Hnh). pose proof (xlo_sound SEGS E M allkn zn zl HA Hzl).
apply (CONT b zk zn HKK); unfold estart, elenZ; cbn [a_base a_off]; lia.
- destruct (xinside allkn b off n zb zk zn) eqn:Hins; [|apply IH; assumption].
pose proof (xinside_sound SEGS E M allkn b off n zb zk zn HA Hins) as [I1 I2]. apply (CONT zb zk zn HKK I1 I2).
Qed.

Lemma kentry_keep_foot : forall E M M' K,
kentry_ok SEGS E M K ->
(forall x : word, match kfoot E K with
| Some (s, l) => s <= bv_unsigned x < s + l
| None => False end -> M' x = M x) ->
(forall x : word, M x = None -> M' x = None) ->
kentry_ok SEGS E M' K.
Proof.
intros E M M' K HK Hin Hnone.
destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok kfoot] in *;
try exact HK.
-  destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
rewrite <- Hrd. apply rdn_ext; [rewrite (flat_u E _ _ Hfl); destruct Hfl; lia|].
intros x Hx. apply Hin. rewrite (flat_u E _ _ Hfl) in Hx. lia.
-  destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
-  destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
-  destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi. apply Hnone. apply HC. exact Hi.
-  destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
destruct m as [|m']; [reflexivity|].
apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
intros x Hx. rewrite u64_lit in Hx by lia.
unfold wview. rewrite Hin by lia. fold (wview SEGS M x).
eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
-  destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
-  destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
Qed.

Definition sh_iv (E : env) (k : list kentry) (p : expr * expr) : Z * Z :=
let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in (estart E (SA sb sk), elenZ E sn).

Lemma fold_unfill_inv : forall E M k gone acc K,
know_ok SEGS E M k ->
(forall K', In K' acc -> In K' k) ->
In K (fold_left (fun kk p => let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in kn_unfill kk sb sk sn) gone acc) ->
In K acc /\ (kimg_b K = true \/ forall p, In p gone -> kfoot_apart E K (fst (sh_iv E k p)) (snd (sh_iv E k p))).
Proof.
intros E M k gone. induction gone as [|p gone IH]; intros acc K HK Hacc Hin.
- cbn in Hin. split; [exact Hin|]. right. intros q [].
- cbn [fold_left] in Hin.
destruct (shadow_of A k (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
assert (Hacc' : forall K', In K' (kn_unfill acc sb sk sn) -> In K' k).
{ intros K' HK'. unfold kn_unfill in HK'. apply filter_In in HK' as [HK' _]. apply Hacc. exact HK'. }
destruct (IH _ K HK Hacc' Hin) as [Hin1 Hrest].
unfold kn_unfill in Hin1. apply filter_In in Hin1 as [Hin0 Hkeep]. split; [exact Hin0|].
apply orb_prop in Hkeep as [Himg|Hap]; [left; exact Himg|].
destruct Hrest as [Himg|Hrest]; [left; exact Himg|]. right.
intros q [<-|Hq]; [|apply Hrest; exact Hq].
unfold sh_iv. rewrite Hsh. cbn [fst snd].
rewrite APS.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [|exact Hap].
unfold know_ok. apply Forall_forall. intros K' HK'. exact (proj1 (Forall_forall _ _) HK K' (Hacc K' HK')).
Qed.

Lemma existsb_filter_split : forall {T} (g h : T -> bool) l,
existsb h l = (existsb h (List.filter g l) || existsb h (List.filter (fun x => negb (g x)) l))%bool.
Proof.
intros T g h l. induction l as [|x l IH]; cbn; [reflexivity|].
destruct (g x); cbn; rewrite IH; destruct (h x); cbn; rewrite ?orb_true_r; reflexivity.
Qed.

Lemma node_munmap_sound : forall cs cs' E R FULL model T,
CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
node_munmap A cs = Some cs' ->
(forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
intros cs cs' E R FULL model T HC Hec Hn HK.
destruct (QxyE.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
rewrite node_munmap_eq in Hn.  unfold node_munmap_ref in Hn.
destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML.
2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
assert (Hz : z17 = 215).
{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
subst z17.
destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsp.
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hgone]. apply andb_prop in Hcond as [Hcond Hhi64]. apply andb_prop in Hcond as [Hcond HFLAT]. apply andb_prop in Hcond as [Hhas Hpal].
set (k := kn cs) in *.
set (g := fun p : expr * expr => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) in *.
set (ng := fun p : expr * expr => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) in *.
assert (NG : forall l, List.filter ng l = List.filter (fun p => negb (g p)) l).
{ intros l. induction l as [|p l IH]; cbn; [reflexivity|]. rewrite IH. subst g ng. cbv beta. destruct (split_lit (fst p)); reflexivity. }
rewrite !NG in Hn, Hgone. clear NG ng.
set (gone := List.filter (fun p => negb (g p)) (a_vis cs)) in *.
set (kept := List.filter g (a_vis cs)) in *.
apply some_inj in Hn. subst cs'.

apply existsb_exists in Hhas as (m & Hm & Hmatch). unfold amap_match in Hmatch. apply andb_prop in Hmatch as [Hb Hlen_eq].
pose proof (len_eqb_sound E _ k ne (am_len m) HKN Hlen_eq) as Hne_eq.
destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & _ & _).
set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
set (addr := edenot E (reg cs 10)). set (n := edenot E (am_len m)).
assert (Haddr : True) by exact I.
apply andb_prop in Hb as [Hnf Hb]. apply negb_true_iff in Hnf. apply expr_eqb_eq in Hb.
assert (Haddr' : edenot E (am_base m) = addr) by (subst addr; rewrite Hb; reflexivity). clear Haddr. rename Haddr' into Haddr.
pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
pose proof (maps_match_In E _ _ m MM Hm Hnf) as HIN.
pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
assert (BPOS : forall iv, In iv (vm_maps (m_vmmaps model)) -> 0 < bv_unsigned (snd iv)).
{ intros iv Hiv. exact (proj1 (proj1 (Forall_forall _ _) HB iv Hiv)). }
pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5).
unfold amap_den in B1, B2, B3, B4, B5. cbn [fst snd] in B1, B2, B3, B4, B5. rewrite Haddr in B2, B4, B5. fold n in B1, B3, B4, B5.
pose proof (u64_range addr) as Ra. pose proof (u64_range n) as Rn.
destruct (xhi k (reg cs 10)) as [ahi|] eqn:Hahi; [|discriminate]. apply Z.ltb_lt in Hhi64.
pose proof (xhi_sound SEGS E _ k (reg cs 10) ahi HKN Hahi) as Hahi'. fold addr in Hahi'. unfold two64 in Hhi64.
assert (Un : bv_unsigned n = nZ).
{ unfold n. rewrite <- Hne_eq, Hne. apply u64_lit. lia. }
assert (HnZw : Z_to_bv 64 nZ = n) by (rewrite <- Un; apply Z_to_bv_bv_unsigned).
destruct (split_flat_estart E _ k (reg cs 10) bb bk ne HKN Hsp HFLAT) as (Hest & _ & _). fold addr in Hest.
assert (HelenZ : elenZ E ne = nZ) by (unfold elenZ; rewrite Hne; apply u64_lit; lia).
set (lo := bv_unsigned addr) in *. set (hi := lo + nZ).
pose proof ATOP_range' as AT. unfold CEIL, ATOP_MAX in AT.
assert (Hlohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= ATOP /\ lo < hi /\ lo mod 4096 = 0 /\ hi mod 4096 = 0).
{ subst hi. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. rewrite Z.add_mod, B2 by lia. rewrite <- Un, B3. reflexivity. }
pose proof HULL_ok as (HU0 & HU1 & HU2 & HU3).

destruct (reg_lit_sound' E cs R FULL model 17 215 HC ltac:(lia) H17) as [R17 _]. rewrite <- bv5_17 in R17.
pose proof (reg_sound' E cs R FULL model 10 HC ltac:(lia)) as R10. fold addr in R10. rewrite <- bv5_10 in R10.
change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.

pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS.
assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m'))).
{ intros m' Hm' Hnf' Hne'. pose proof (maps_match_disjoint SEGS A RES_len E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne') as D.
unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. rewrite Haddr in D. fold n lo in D. subst hi. lia. }

assert (DISJl : forall iv, In iv (vm_maps (m_vmmaps model)) -> iv <> amap_den E m ->
bv_unsigned (fst iv) + bv_unsigned (snd iv) <= lo \/ hi <= bv_unsigned (fst iv)).
{ intros iv Hiv Hne'. pose proof (seps_In_disjoint _ iv (amap_den E m) SEPS BPOS Hiv HIN Hne') as D.
unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. rewrite Haddr in D. fold n lo in D. subst hi. lia. }
assert (UNIQ : forall iv, In iv (vm_maps (m_vmmaps model)) -> fst iv = addr -> iv = amap_den E m).
{ intros [ib isz] Hiv Hb0. cbn [fst] in Hb0. subst ib.
destruct (bv_eqb isz n) eqn:Hs.
- apply bv_eqb_eq in Hs. subst isz. unfold amap_den. rewrite Haddr. reflexivity.
- exfalso. assert (Hne' : (addr, isz) <> amap_den E m).
{ unfold amap_den. rewrite Haddr. fold n. intros Heq. injection Heq as Heq. rewrite Heq, bv_eqb_refl in Hs. discriminate. }
pose proof (DISJl _ Hiv Hne') as D. cbn [fst snd] in D. pose proof (BPOS _ Hiv) as P. cbn [snd] in P. subst lo hi. lia. }
assert (MATCH : forall m', In m' (a_maps cs) -> negb (amap_match k (reg cs 10) ne m') = negb (amap_eqb m' m)).
{ intros m' Hm'. f_equal. unfold amap_match.
destruct (amap_eqb m' m) eqn:Hmm.
- apply APS.amap_eqb_eq in Hmm. subst m'. rewrite Hnf, <- Hb, expr_eqb_refl, Hlen_eq. reflexivity.
- assert (Hne' : m <> m') by (intros <-; rewrite amap_eqb_refl in Hmm; discriminate).
destruct (is_fog m') eqn:Hnf'; [reflexivity|]. cbn [negb andb].
destruct (expr_eqb (reg cs 10) (am_base m')) eqn:Heq; [|reflexivity]. exfalso.
apply expr_eqb_eq in Heq.
pose proof (DISJ' m' Hm' Hnf' Hne') as D. rewrite <- Heq in D. fold addr lo in D.
pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' MM Hm' Hnf')) as (C1 & _). unfold amap_den in C1. cbn [snd] in C1. lia. }
assert (MAPS' : maps_match E (List.filter (fun m' => negb (amap_match k (reg cs 10) ne m')) (a_maps cs)) (map_remove (vm_maps (m_vmmaps model)) addr)).
{ rewrite (filter_ext_in _ (fun m' => negb (amap_eqb m' m))) by (intros m' Hm'; exact (MATCH m' Hm')).
rewrite <- Haddr. apply maps_match_remove; [exact MM | exact Hm | exact Hnf | exact (seps_NoDup _ SEPS BPOS) |].
intros iv Hiv Hfst. apply UNIQ; [exact Hiv | rewrite Hfst; exact Haddr]. }
assert (INMAPS' : forall z, in_ivs z (map_remove (vm_maps (m_vmmaps model)) addr) = (in_ivs z (vm_maps (m_vmmaps model)) && negb (in_rng lo hi z))%bool).
{ intros z. unfold map_remove.
destruct (in_ivs z (List.filter (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model)))) eqn:Hl; symmetry.
- apply in_ivs_true' in Hl as (iv & Hiv & Hziv). apply filter_In in Hiv as [Hiv Hkeep]. apply negb_true_iff in Hkeep.
assert (Hne' : iv <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
pose proof (DISJl iv Hiv Hne') as D.
apply andb_true_intro. split; [apply (proj2 (in_ivs_true' _ _)); exists iv; auto|].
apply negb_true_iff. unfold in_rng. apply andb_false_iff. destruct D; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
- apply andb_false_iff.
destruct (in_ivs z (vm_maps (m_vmmaps model))) eqn:Hin; [right|left; reflexivity].
apply in_ivs_true' in Hin as (iv & Hiv & Hziv). apply negb_false_iff.
destruct (bv_eqb (fst iv) addr) eqn:Hfa.
+ apply bv_eqb_eq in Hfa. pose proof (UNIQ iv Hiv Hfa) as ->. unfold amap_den in Hziv. cbn [fst snd] in Hziv. rewrite Haddr in Hziv. fold n lo in Hziv.
unfold in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; subst hi; lia.
+ exfalso. assert (X : in_ivs z (List.filter (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) = true); [|congruence].
apply (proj2 (in_ivs_true' _ _)). exists iv. split; [|exact Hziv]. apply filter_In. rewrite Hfa. auto. }

assert (GONE : forall p, In p gone ->
(forall z, (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)) = true -> lo <= z < hi)%bool
/\ (0 <= fst (sh_iv E k p))
/\ (forall x : word, fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p) -> MR E cs model FULL x = Some (Z_to_bv 8 0))
/\ (forall z, (sh_lo A E p <=? z) && (z <? sh_hi A E p) = true -> fst (sh_iv E k p) <= z < fst (sh_iv E k p) + snd (sh_iv E k p))%bool).
{ intros p Hp.
pose proof (proj1 (forallb_forall _ _) Hgone p Hp) as G. cbv beta in G.
assert (Hpv : In p (a_vis cs)) by (unfold gone in Hp; apply filter_In in Hp as [Hp _]; exact Hp).
destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
destruct (shadow_of A k (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
apply andb_prop in G as [G Gz]. apply andb_prop in G as [G Gin]. apply andb_prop in G as [Gab Gan].
apply Z.leb_le in Gab. apply Z.leb_le in Gan.
assert (AL8 : forall e, 3 <= ealign k e -> uE E e mod 8 = 0).
{ intros e Hee. destruct (ealign_sound SEGS E _ k e HKN) as [_ [q Hq]]. unfold uE. rewrite Hq.
replace (2 ^ ealign k e) with (2 ^ (ealign k e - 3) * 8) by (rewrite <- (Z.pow_add_r 2 _ 3) by lia; f_equal; lia).
rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
pose proof (AL8 _ Gab) as A8b. pose proof (AL8 _ Gan) as A8n.
pose proof (xinside_sound SEGS E _ k pb pk (snd p) bb bk ne HKN Gin) as [I1 I2]. rewrite Hest, ?HelenZ in I1, I2. rewrite HelenZ in I2.
unfold elenZ in I2.
pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(pose proof (u64_range (edenot E (snd p))); lia)) as Up.
destruct (kzero_x_sound E _ k k sb sk sn HKN HKN Gz) as (Z1 & Z2 & Z3).
unfold sh_iv. rewrite Hsh. cbn [fst snd].
split; [|split; [exact Z1 | split; [exact Z3|]]].
- intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold uE in *. rewrite Up in Hz1, Hz2. subst hi. lia.
-
unfold shadow_of in Hsh.
destruct (split_lit (eadd (mkSrl k (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
assert (Usn : elenZ E (mkSrl k (snd p) 3) = bv_unsigned (edenot E (snd p)) / 8).
{ unfold elenZ. rewrite (mkSrl_denot SEGS E _ k (snd p) 3 (Z_to_bv 64 3) HKN) by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
rewrite Usn in *.
pose proof (APS.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
rewrite (mkSrl_denot SEGS E _ k (fst p) 3 (Z_to_bv 64 3) HKN) in D by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64 in D. pose proof SHADOW_ok as SO. pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn'.
change (2 ^ (3 mod 64)) with 8 in D.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite !u64_lit in D by lia.
rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by lia.
intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold sh_lo, sh_hi, uE in Hz1, Hz2.
unfold estart. cbn [a_base a_off]. unfold estart in Z1, Z2. cbn [a_base a_off] in Z1, Z2.

rewrite Z_to_bv_unsigned, bv_wrap64_mod in D. unfold uE in A8b, A8n. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }

pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & Wsp).
unfold cfg_of.
eapply (srz_munmap_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len T Hf He Hhalt R17 R10 B2 R11 ltac:(lia)).
{ unfold TASK_SIZE. fold nZ. lia. }
{ fold nZ. rewrite HnZw. apply map_has_intro. rewrite <- Haddr. exact HIN. }
fold nZ. rewrite HnZw. rewrite (v_addi_pc (pc cs) Hp0 Hp4).
set (model' := munmap_model addr n model). set (FULL' := unfill addr n FULL).
match goal with |- srealizes _ (mkCfg _ ?mo) _ => change mo with model' end.
set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _) in HK.
specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
unfold cfg_of in HK. replace (pc cs') with (pc cs + 4) in HK by reflexivity. rewrite bv5_10. apply HK; [|reflexivity]. clear HK.

assert (PM : vm_maps (m_vmmaps model') = map_remove (vm_maps (m_vmmaps model)) addr) by reflexivity.
assert (PN : vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) lo (lo + bv_unsigned n)) by reflexivity.
assert (PL : m_vm_lazy model' = maps_subtract (m_vm_lazy model) lo (lo + bv_unsigned n)) by reflexivity.
assert (PISP : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)) by reflexivity.
assert (PT : m_vm_materialized model' = List.filter (page_outside_range lo (lo + bv_unsigned n)) (m_vm_materialized model)) by reflexivity.
rewrite Un in PN, PL, PT. fold hi in PN, PL, PT.

assert (NOACC : forall z, in_ivs z (vm_noaccess (m_vmmaps model')) = (in_ivs z (vm_noaccess (m_vmmaps model)) && negb (in_rng lo hi z))%bool).
{ intros z. rewrite PN, !in_ivs_covered. apply covered_maps_subtract; [exact W2 | lia]. }
assert (LAZYOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
page_in_ranges (page_base x) (m_vm_lazy model') = page_in_ranges (page_base x) (m_vm_lazy model)).
{ intros x Hx. rewrite PL. destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
pose proof (page_of_byte_out_aligned x lo hi L4 L5 Hx). apply page_in_ranges_subtract_out; [exact W3 | lia | unfold page_size; lia]. }
assert (ALW : forall z, in_allow A E cs z = (in_allow A E cs' z || existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool gone
|| existsb (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool gone)%bool).
{ intros z. unfold in_allow, in_vis, in_sh, cs'. cbn [a_vis]. subst kept gone.
rewrite (existsb_filter_split g (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs)).
rewrite (existsb_filter_split g (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool (a_vis cs)).
destruct (existsb _ _), (existsb _ _), (existsb _ _), (existsb _ _); reflexivity. }
assert (VISLE : forall x : word, VIS E cs' model' x = true -> VIS E cs model x = true /\ (lo <= bv_unsigned x < hi -> False)).
{ intros x Hv. unfold vis in Hv |- *. rewrite PM, INMAPS', NOACC in Hv. destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
destruct (in_rng lo hi (bv_unsigned x)) eqn:Hr.
- unfold in_rng in Hr. apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2.
replace (in_hull A (bv_unsigned x)) with false in Hv by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1 as [L1|L1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
replace (ATOP <=? bv_unsigned x) with false in Hv by (symmetry; apply Z.leb_gt; lia).
rewrite andb_false_r in Hv. cbn in Hv. discriminate.
- assert (Hx : bv_unsigned x < lo \/ hi <= bv_unsigned x).
{ unfold in_rng in Hr. apply andb_false_iff in Hr as [Hr|Hr]; [apply Z.leb_gt in Hr | apply Z.ltb_ge in Hr]; lia. }
split; [|lia]. rewrite (LAZYOUT x Hx) in Hv. rewrite !andb_true_r in Hv.
apply orb_prop in Hv as [Hv|Hv]; [rewrite Hv; reflexivity|]. apply orb_true_iff. right.
apply andb_prop in Hv as [Hv1 Hv2]. apply andb_prop in Hv1 as [Hv0 Hv1]. rewrite Hv0, Hv1. cbn [andb negb].
apply orb_prop in Hv2 as [Hv2|Hv2]; [rewrite Hv2; reflexivity|]. rewrite (ALW (bv_unsigned x)), Hv2. cbn [orb]. apply orb_true_r. }
assert (VISEQ : forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
(forall p, In p gone -> ~ (fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p))) ->
VIS E cs' model' x = VIS E cs model x).
{ intros x Hx Hnsh. unfold vis. rewrite PM, INMAPS', NOACC, (LAZYOUT x Hx), (ALW (bv_unsigned x)).
replace (in_rng lo hi (bv_unsigned x)) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
cbn [negb]. rewrite !andb_true_r.
replace (existsb (fun p => (uE E (fst p) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p) + uE E (snd p)))%bool gone) with false.
2: { symmetry. apply APS.existsb_false_forall. intros p Hp. destruct (GONE p Hp) as (G1 & _).
match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
replace (existsb (fun p => (sh_lo A E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E p))%bool gone) with false.
2: { symmetry. apply APS.existsb_false_forall. intros p Hp. destruct (GONE p Hp) as (_ & _ & _ & G4).
match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. exact (Hnsh p Hp (G4 _ Ht)). }
rewrite !orb_false_r. reflexivity. }

assert (MRNONE : forall x : word, MR E cs model FULL x = None -> MR E cs' model' FULL' x = None).
{ intros x Hx. unfold Mr, mrestrict, hid in Hx |- *.
destruct (argH E x); [reflexivity|]. cbn [orb] in *.
destruct (VIS E cs' model' x) eqn:Hv'; [|reflexivity]. cbn [negb].
destruct (VISLE x Hv') as [Hv Hnin]. rewrite Hv in Hx. cbn [negb] in Hx.
unfold FULL'. rewrite unfill_out by (rewrite Un; lia). exact Hx. }
assert (MRKEEP : forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
(forall p, In p gone -> ~ (fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p))) ->
MR E cs' model' FULL' x = MR E cs model FULL x).
{ intros x Hx Hnsh. unfold Mr, mrestrict, hid. rewrite (VISEQ x Hx Hnsh). unfold FULL'. rewrite unfill_out by (rewrite Un; exact Hx). reflexivity. }

assert (HALLOW_in : forall iv, In iv (ALLOW E cs') <-> In iv (ALLOW E cs)).
{ intros iv. unfold allowA, cs'. cbn [a_vis a_ghost]. subst kept gone. rewrite <- ?app_assoc. apply in_flat_map_split. }
assert (HALLOW_bytes : A_bytes (ALLOW E cs') = A_bytes (ALLOW E cs)).
{ unfold allowA, cs'. cbn [a_vis a_ghost]. subst kept gone. rewrite <- ?app_assoc. apply A_bytes_flat_map_split. }
assert (DISJF : forall m', In m' (List.filter (fun m0 => negb (amap_match k (reg cs 10) ne m0)) (a_maps cs)) ->
In m' (a_maps cs) /\ m <> m'
/\ (is_fog m' = false -> bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m')))).
{ intros m' Hm'. apply filter_In in Hm' as [Hm' Hnm].
assert (Hne' : m <> m').
{ intros <-. unfold amap_match in Hnm. rewrite Hnf, <- Hb, expr_eqb_refl, Hlen_eq in Hnm. discriminate. }
split; [exact Hm'|]. split; [exact Hne'|]. intros Hnf'. exact (DISJ' m' Hm' Hnf' Hne'). }
assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
{ intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xsp0 Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv].
destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
assert (HAeq : ALLOW E cs' = flat_map (allow1 A E) (kept ++ gone ++ a_ghost cs)) by reflexivity.
constructor; rewrite ?HAeq; subst cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_next mk_ss];
try set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _) in *.
-  apply regs_ok_set_n'; [exact Xregs | lia | reflexivity].
- reflexivity.
-  unfold know_ok. apply Forall_forall. intros K HinK.
destruct (fold_unfill_inv E _ k gone (kn_unfill k bb bk ne) K Xknow
ltac:(intros K' HK'; unfold kn_unfill in HK'; apply filter_In in HK' as [HK' _]; exact HK') HinK) as [Hin0 Hsh].
unfold kn_unfill in Hin0. apply filter_In in Hin0 as [Hin0 Hkeep0].
pose proof (proj1 (Forall_forall _ _) Xknow K Hin0) as HKK.
destruct (kimg_b K) eqn:HnotImg.
{ destruct K; try discriminate. cbn [kentry_ok] in HKK |- *. destruct HKK as (HA' & HB' & HCC).
split; [exact HA'|]. split; [exact HB'|]. intros i Hi. apply MRNONE. apply HCC. exact Hi. }
apply kentry_keep_foot with (M := MR E cs model FULL); [exact HKK | | exact MRNONE].
intros x Hfx.
cbn [orb] in Hkeep0. rewrite APS.kentry_apart_bp_eq in Hkeep0.
pose proof (kentry_apart_b_sem' E _ k K bb bk ne Xknow Hkeep0) as Hap0. rewrite Hest, HelenZ in Hap0.
destruct Hsh as [Himg|Hsh]; [rewrite Himg in HnotImg; discriminate|].
unfold kfoot_apart in Hap0, Hsh.
destruct (kfoot E K) as [[fs fl]|] eqn:Hkf; [|destruct Hfx].
apply MRKEEP; [subst hi; lia|]. intros p Hp Hin. pose proof (Hsh p Hp) as HH. rewrite ?Hkf in HH. cbn [fst snd] in Hin. lia.
- unfold model'. rewrite munmap_model_halted. exact Xhalt.
- unfold fds_ok in *. exact Xfds.
- exact Xfs.
- exact Xtid.
- exact Xres.
- exact Xlimit.
- rewrite PM. exact MAPS'.
-
rewrite PM. apply Forall_forall. intros m' Hm' Hk'. destruct (DISJF m' Hm') as (Hm0 & _ & _).
destruct (proj1 (Forall_forall _ _) Xholes m' Hm0 Hk') as [HF1 HF2]. split; [|exact HF2].
intros iv Hiv. apply HF1. apply in_app_iff in Hiv as [Hiv|Hiv]; apply in_app_iff; [left; exact Hiv | right].
unfold map_remove in Hiv. apply filter_In in Hiv as [Hiv _]. exact Hiv.
-  rewrite PM. unfold map_remove. apply seps_filter. exact Xseps.
-  unfold model_ivs_wf. rewrite PM, PN, PL. split; [|split; [|split; [|unfold init_sp_ok in *; rewrite PISP; exact Wsp]]].
+ unfold map_remove. apply ivs_wf_filter. exact W1.
+ apply maps_subtract_wf; [exact W2 | lia].
+ apply maps_subtract_wf; [exact W3 | lia].
-  rewrite PM. unfold map_remove. apply Forall_forall. intros iv Hiv. apply filter_In in Hiv as [Hiv _]. exact (proj1 (Forall_forall _ _) Xbounds iv Hiv).
-  rewrite PL. apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. lia.
-  intros z Hz. rewrite PM, INMAPS'. rewrite NOACC in Hz. apply andb_prop in Hz as [Hz1 Hz2]. rewrite (Xnasub z Hz1), Hz2. reflexivity.
-  apply Forall_forall. intros m' Hm' Hk'. destruct (DISJF m' Hm') as (Hm0 & Hne' & D).
assert (Hnf' : is_fog m' = false) by (apply KNF; tauto). specialize (D Hnf').
rewrite PN. pose proof (proj1 (Forall_forall _ _) Xnone m' Hm0 Hk') as X.
pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' Xmaps Hm0 Hnf')) as (C1 & _).
unfold amap_den in *. apply maps_subtract_keeps; [lia | exact C1 | exact X | cbn [fst snd]; subst hi; lia].
-  apply Forall_forall. intros m' Hm' Hk' x Hx. destruct (DISJF m' Hm') as (Hm0 & Hne' & D).
specialize (D ltac:(apply KNF; tauto)).
destruct (proj1 (Forall_forall _ _) Xkinds m' Hm0 Hk' x Hx) as [K1 K2].
assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x) by lia.
rewrite NOACC, K1, (LAZYOUT x Hxo), K2. split; reflexivity.
-  rewrite PM. unfold map_remove. rewrite sum_sizes_app. rewrite sum_sizes_app in Xtotsz.
pose proof (sum_sizes_filter_le (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) as SF.
change (vm_reserved (m_vmmaps model')) with (vm_reserved (m_vmmaps model)). lia.
-  rewrite PISP. exact Xisp.
- exact Xsp0.
- exact Xbrk.
- exact Xsbrk.
-  rewrite (eager_used_sem model'), (eager_used_sem model Xwf) in *.
2: { unfold model_ivs_wf. rewrite PM, PN, PL. split; [unfold map_remove; apply ivs_wf_filter; exact W1|]. split; [apply maps_subtract_wf; try assumption; lia|]. split; [apply maps_subtract_wf; try assumption; lia | unfold init_sp_ok in *; rewrite PISP; exact Wsp]. }
rewrite PM. unfold map_remove.
eapply Z.le_trans; [|exact Xeager]. apply sum_count_filter_le.
intros q Hq Hkeep x Hx. apply negb_true_iff in Hkeep.

assert (Hxo : x < lo \/ hi <= x).
{ assert (Hne' : q <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
pose proof (DISJl q Hq Hne'). unfold B, S in Hx. lia. }
f_equal. rewrite !covered_app, PN, PL. rewrite !covered_maps_subtract by (first [exact W2 | exact W3 | lia]).
replace (in_rng lo hi x) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
cbn [negb]. rewrite !andb_true_r. reflexivity.
-  rewrite <- HAeq, HALLOW_bytes. exact Xabytes.
-  rewrite <- HAeq. destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?PT.
+ apply NoDup_filter. exact N1.
+ intros q Hq. apply filter_In in Hq as [Hq _]. exact (N2 q Hq).
+ intros q Hq. apply filter_In in Hq as [Hq _]. pose proof (N3 q Hq) as P3.
unfold page_allowedb in *. apply existsb_exists in P3 as (iv & Hiv & Hbb). apply existsb_exists. exists iv. split; [apply HALLOW_in; exact Hiv | exact Hbb].
+ intros q Hq. apply filter_In in Hq as [Hq Ho]. pose proof (N4 q Hq) as P4.
unfold page_outside_range in Ho. apply negb_true_iff in Ho.
pose proof (N2 q Hq) as Qa. unfold page_size in Qa.
rewrite PL. rewrite page_in_ranges_subtract_out; [exact P4 | exact W3 | lia | ].
unfold page_size.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
apply andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
+ rewrite HALLOW_bytes.
assert (EG : eager_used model' <= eager_used model); [|change (vm_limit (m_vmmaps model')) with (vm_limit (m_vmmaps model)); lia].
rewrite (eager_used_sem model'), (eager_used_sem model Xwf).
2: { unfold model_ivs_wf. rewrite PM, PN, PL. split; [unfold map_remove; apply ivs_wf_filter; exact W1|]. split; [apply maps_subtract_wf; try assumption; lia|]. split; [apply maps_subtract_wf; try assumption; lia | unfold init_sp_ok in *; rewrite PISP; exact Wsp]. }
rewrite PM. unfold map_remove. apply sum_count_filter_le.
intros q Hq Hkeep x Hx. apply negb_true_iff in Hkeep.
assert (Hxo : x < lo \/ hi <= x).
{ assert (Hne' : q <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
pose proof (DISJl q Hq Hne'). unfold B, S in Hx. lia. }
f_equal. rewrite !covered_app, PN, PL. rewrite !covered_maps_subtract by (first [exact W2 | exact W3 | lia]).
replace (in_rng lo hi x) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
cbn [negb]. rewrite !andb_true_r. reflexivity.
-  intros x Hh Hmx Hna Hlz Hgh.
assert (Hgh0 : in_ghost A E cs (bv_unsigned x) = false).
{ unfold in_ghost, in_ghostl in Hgh |- *. subst cs'. cbn [a_ghost] in Hgh. rewrite existsb_app in Hgh.
destruct (in_shwin A (bv_unsigned x)); [rewrite andb_false_r; reflexivity | rewrite andb_true_r in Hgh |- *].
apply orb_false_iff in Hgh as [_ Hgh]. exact Hgh. }
rewrite PM, INMAPS' in Hmx. apply andb_prop in Hmx as [Hmx Hxo'].
assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x).
{ apply negb_true_iff in Hxo'. unfold in_rng in Hxo'. apply andb_false_iff in Hxo' as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; lia. }
unfold FULL'. rewrite unfill_out by (rewrite Un; exact Hxo).
rewrite NOACC in Hna. apply andb_false_iff in Hna as [Hna|Hna]; [| rewrite Hxo' in Hna; discriminate].
rewrite (LAZYOUT x Hxo) in Hlz.

destruct (HID E cs model x) eqn:Hold; [exact (Xzero x Hold Hmx Hna Hlz Hgh0)|].
unfold hid in Hh, Hold. destruct (argH E x); [discriminate|]. cbn [orb] in Hh, Hold.
apply negb_true_iff in Hh. apply negb_false_iff in Hold.

assert (SHX : exists p, In p gone /\ fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p)).
{ destruct (existsb (fun p => (sh_lo A E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E p))%bool gone) eqn:Hex.
- apply existsb_exists in Hex as (p & Hp & Hpx). exists p. split; [exact Hp|]. destruct (GONE p Hp) as (_ & _ & _ & G4). exact (G4 _ Hpx).
- exfalso. unfold vis in Hh, Hold. rewrite PM, INMAPS', NOACC, (LAZYOUT x Hxo) in Hh. rewrite (ALW (bv_unsigned x)), Hex in Hold.
replace (existsb (fun p0 => (uE E (fst p0) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p0) + uE E (snd p0)))%bool gone) with false in Hold.
2: { symmetry. apply APS.existsb_false_forall. intros p0 Hq0. destruct (GONE p0 Hq0) as (G1 & _).
match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
rewrite Hxo' in Hh. cbn [negb] in Hh. rewrite !andb_true_r in Hh. rewrite !orb_false_r in Hold. rewrite Hh in Hold. discriminate. }
destruct SHX as (p & Hp & Hpx). destruct (GONE p Hp) as (_ & _ & G3 & _).
pose proof (G3 x Hpx) as Z0. unfold Mr, mrestrict, hid in Z0. rewrite Hold in Z0.
destruct (argH E x); [discriminate|]. cbn in Z0. exact Z0.
-  eapply SINV_frame; [|exact Xsinv]. intros x Hx. unfold FULL'. apply unfill_out. pose proof (argH_sp _ _ Hx). rewrite Un. subst hi.
unfold APS.ATOP, STACK_MAX in L2. lia.
Qed.

Theorem node_sys_sound_YMunmap : sys_stmt SEGS A nx0 LIMIT USP SINV argH FS0 YMunmap.
Proof. intros cs cs' E R FULL model T HC Hpre Hn HK. eapply node_munmap_sound; eauto. Qed.

End SoundMunmap.

Section SoundSys.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis USP_ok : APS.usp_ok USP.
Hypothesis NX0_ge : APS.nx0_ge nx0.
Hypothesis argH_sp : forall E (a : word), argH E a = true -> USP <= bv_unsigned a.

Local Ltac feed t :=
lazymatch type of t with
| forall _ : ?T, _ =>
first [ feed (t SEGS) | feed (t A) | feed (t nx0) | feed (t LIMIT) | feed (t USP) | feed (t SINV) | feed (t argH) | feed (t FS0)
| feed (t RES_len) | feed (t HULL_ok) | feed (t SHADOW_ok) | feed (t argH_high) | feed (t argH_agree)
| feed (t SINV_frame) | feed (t SINV_agree) | feed (t USP_ok) | feed (t NX0_ge) | feed (t argH_sp) | exact t ]
| _ => exact t
end.
Theorem node_sys_sound : forall y, sys_stmt SEGS A nx0 LIMIT USP SINV argH FS0 y.
Proof.
intros [| |].
- feed node_sys_sound_YMunmap.
- feed node_sys_sound_YBrk.
- feed node_sys_sound_YSetTid.
Qed.
End SoundSys.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ4Q Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 QJ4Q.Mq0 Q85Z Q6EJ QND5 Qo8J.Mq0 QG64 QsSk QqZL.Mq0.
Import Qt8n QWtD QqZL.Mq2 QOTP Q1LT.
Import QEdo.Mq0 QG64.Mq0 QDlz.
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section NodesD.

Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.

Variable sp : word.
#[local] Notation USP := (bv_unsigned sp).
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_ge : APS.nx0_ge nx0.

#[local] Notation Hv := (QEdo.Mq0.Hv A USP).
#[local] Notation lazy_cover_vis := (QEdo.Mq0.lazy_cover_vis SEGS A LIMIT USP SINV argH FS0 HULL_ok).
#[local] Notation H_off_segments_vis := (QEdo.Mq0.H_off_segments_vis SEGS A USP SEGS_in_hull).
#[local] Notation mrestrict_Hv_high := (QEdo.Mq0.mrestrict_Hv_high A USP).
#[local] Notation Mr_grows_Hv := (QEdo.Mq0.Mr_grows_Hv A USP argH).

Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
Hypothesis Fe1 : fetch_word SEGS (Z_to_bv 64 (x_envscan A)) = Some we1.
Hypothesis Fe2 : fetch_word SEGS (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
Hypothesis Fe3 : fetch_word SEGS (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
Hypothesis Fp0 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
Hypothesis Fp1 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
Hypothesis Fp2 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A)) = Some wp2.
Hypothesis Fp3 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
Hypothesis Fp4 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

Variable ph : PhdrInfo.
Variable rdraw : EntryDraw.
Variables argv envp : list (list byte).
Variable uid : word.
Variable hw : word.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hsp_lo : sp_window_lo <= bv_unsigned sp.
Hypothesis Hsp_hi : bv_unsigned sp <= sp_window_hi.

Let usp := bv_unsigned sp.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let s0 := nth 0 argv [].
Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.

Let EA := usp + 8 * argc + 16.
Let STR0 := usp + 8 * argc + 8 * envc + 184.

Hypothesis SINV_vals : forall E M, SINV E M ->
uE E e_envp = EA /\ ev E V_ENVC = Z_to_bv 64 envc /\ uE E e_str0 = STR0.
Hypothesis SINV_envp : forall E M (a : word), SINV E M ->
EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a.
Hypothesis SINV_str0 : forall E M (a : word), SINV E M ->
STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M a = wrap_mem ph sp argv envp uid hw rdraw a.

Lemma len_av : 1 <= argc <= 1024.
Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
Lemma len_ev : 0 <= envc <= 256.
Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
Lemma len_s0 : Z.of_nat (length s0) <= 131071.
Proof. unfold s0. apply (valid_argv_str_len argv 0 Hva). destruct Hva as [H _]. lia. Qed.
Lemma usp_lo : 0x7fff80000000 <= usp.
Proof. unfold usp. unfold sp_window_lo in Hsp_lo. lia. Qed.
Lemma usp_hi : usp <= 0x800000000000.
Proof. unfold usp. unfold sp_window_hi in Hsp_hi. lia. Qed.
Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
Proof. unfold usp, bsb. apply lay_bsb_nw; assumption. Qed.

Lemma STR0_eq : cat_argv_ptr sp argv envp 0 = Z_to_bv 64 STR0.
Proof.
pose proof len_av. pose proof len_ev. pose proof usp_hi.
rewrite (cat_argv_ptr_offset sp argv envp 0) by (destruct Hva as [Hl _]; lia).
unfold cat_string_base. rewrite nat_to_word_add_merge, word_add_nat.
lazymatch goal with |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => replace a with b; [reflexivity|] end.
change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat.
unfold cat_struct_size, auxv_size, STR0, usp, argc, envc. lia.
Qed.

Lemma rd_envp_k : forall M k, (k < length envp)%nat ->
(forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
rdn SEGS M (Z_to_bv 64 (EA + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (cat_envp_ptr sp argv envp k)).
Proof.
intros M k Hk HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi.
assert (Hk' : Z.of_nat k < envc) by (unfold envc; lia).
rewrite (rdn_ext SEGS 8 M (wrap_mem ph sp argv envp uid hw rdraw)).
- rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold EA in *; lia | rewrite u64_lit; unfold EA in *; [change (Z.of_nat 8) with 8|]; lia].
rewrite <- n_to_le_8_spec.
rewrite <- (read_envp_ptr_k SEGS ph sp rdraw argv envp uid hw Hva Hve Hsp_hi k Hk).
f_equal. rewrite word_add_nat. f_equal. unfold envp_off, EA, argc, usp. lia.
- rewrite u64_lit; unfold EA in *; [change (Z.of_nat 8) with 8|]; lia.
- intros a Ha. rewrite u64_lit in Ha by (unfold EA in *; lia). change (Z.of_nat 8) with 8 in Ha. apply HM. lia.
Qed.

Lemma rd_envp_null : forall M,
(forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
rdn SEGS M (Z_to_bv 64 (EA + 8 * Z.of_nat (length envp))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
intros M HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi.
rewrite (rdn_ext SEGS 8 M (wrap_mem ph sp argv envp uid hw rdraw)).
- rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold EA, envc in *; lia | rewrite u64_lit; unfold EA, envc in *; [change (Z.of_nat 8) with 8|]; lia].
rewrite <- n_to_le_8_spec.
rewrite <- (read_envp_null SEGS ph sp rdraw argv envp uid hw Hva Hve Hsp_hi).
f_equal. rewrite word_add_nat. f_equal. unfold envp_off, EA, argc, usp. lia.
- rewrite u64_lit; unfold EA, envc in *; [change (Z.of_nat 8) with 8|]; lia.
- intros a Ha. rewrite u64_lit in Ha by (unfold EA, envc in *; lia). change (Z.of_nat 8) with 8 in Ha. apply HM. unfold envc. lia.
Qed.

Lemma rd_str0_j : forall M j, (j <= length s0)%nat ->
(forall a : word, STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
rdn SEGS M (Z_to_bv 64 (STR0 + Z.of_nat j)) 1 = Some [byte_at s0 j].
Proof.
intros M j Hj HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi. pose proof len_s0.
rewrite (rdn_ext SEGS 1 M (wrap_mem ph sp argv envp uid hw rdraw)).
- rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold STR0 in *; lia | rewrite u64_lit; unfold STR0 in *; [change (Z.of_nat 1) with 1|]; lia].
unfold byte_at, s0.
rewrite <- (read_argv_byte_k ph SEGS sp argv envp 0 j uid hw rdraw ltac:(destruct Hva as [Hl _]; lia) Hj bsb_nw).
f_equal. rewrite STR0_eq, word_add_nat, u64_lit by (unfold STR0 in *; lia). reflexivity.
- rewrite u64_lit; unfold STR0 in *; [change (Z.of_nat 1) with 1|]; lia.
- intros a Ha. rewrite u64_lit in Ha by (unfold STR0 in *; lia). change (Z.of_nat 1) with 1 in Ha. apply HM. lia.
Qed.

Theorem x_sound_envscan : x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XEnvScan.
Proof.
intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_envscan in Hn.
destruct (Z.eqb (pc cs) (x_envscan A) && len_eqb (kn cs) (reg cs 9) e_envp)%bool eqn:Hc; [|discriminate].
injection Hn as <-. apply andb_prop in Hc as [Hpc Heq]. apply Z.eqb_eq in Hpc.
pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2.
destruct Xenv as (X1 & X2 & X3). destruct Ee as (Ee1 & Ee2 & Ee3).
pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
destruct (SINV_vals E FULL HS) as (V1 & V2 & V3).
pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 9) e_envp (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Heq) as H9e.
pose proof (reg_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as H9.
replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) in H9 by (apply bv_eq; reflexivity). rewrite H9e in H9.
assert (H9' : getr R 9%bv = Z_to_bv 64 (EA + 8 * Z.of_nat 0)).
{ rewrite H9. apply bv_eq. rewrite u64_lit by (unfold EA; lia). unfold uE in V1. rewrite V1. lia. }

set (H2 := Hv E cs model).
set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
assert (HM : forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> mrestrict H2 FULL a = wrap_mem ph sp argv envp uid hw rdraw a).
{ intros a Ha. unfold H2. rewrite mrestrict_Hv_high by (unfold EA, APS.ATOP, STACK_MAX in *; lia). eapply SINV_envp; [exact HS | exact Ha]. }
destruct (env_loop SEGS (x_envscan A) we1 we2 we3 ltac:(lia) Fe1 Fe2 Fe3 Ee1 Ee2 Ee3 De1 De2 De3
(mrestrict H2 FULL) (seg_rom SEGS) EA (length envp) (cat_envp_ptr sp argv envp)
ltac:(unfold EA, envc in *; lia)
ltac:(intros k Kk; split; [apply rd_envp_k; [exact Kk | exact HM] | apply (cat_envp_ptr_nz ph sp rdraw argv envp uid hw Hva Hve Hsp_lo Hsp_hi k Kk)])
(rd_envp_null _ HM) (length envp) 0%nat R ltac:(lia) H9') as [R' [Hms Hpost]].
unfold cfg_of. fold ms.
assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (mrestrict H2 FULL) (seg_rom SEGS))).
{ unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
(co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
intros model' Hinv' Hsame Hclean.
change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (mrestrict H2 FULL) (seg_rom SEGS)))
with (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
rewrite munrestrict_mrestrict.
specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
unfold cfg_of, pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk. rewrite X3 in Hk.
apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].

unfold set_pc, set_reg. rewrite !a_ss_with_ss, !with_ss_idem. cbn [s_regs s_know s_next].
eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
cbn [s_regs]. destruct Hpost as (P9 & P10 & Pag).
eapply (regs_ok_post2 E _ R R' 9 9%bv _ 10 10%bv); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) | lia | lia | lia | reflexivity | reflexivity | | |].
- rewrite P9. unfold eadd, escale. rewrite !mkAlu_denot, mkMd_denot, !edenot_lit. fold (reg cs 9). rewrite H9e.
apply bv_eq. rewrite !u_add64, u_mul64, !u64_lit by lia. cbn [edenot]. rewrite V2, u64_lit by lia. unfold uE in V1. rewrite V1.
rewrite (Z.mod_small (8 * envc)) by lia. rewrite (Z.mod_small (8 * envc + 8)) by lia.
rewrite Z.mod_small by (unfold EA; lia). unfold envc. lia.
- rewrite P10. rewrite edenot_lit. reflexivity.
- intros r N1 N2. apply (Pag r). intros [H|H]; [exact (N1 H) | exact (N2 H)].
Qed.

Theorem x_sound_pnscan : x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XPnScan.
Proof.
intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_pnscan in Hn.
destruct (reg_lit cs 10) as [p|] eqn:Hp10; [|discriminate].
destruct (reg_lit cs 12) as [c|] eqn:Hp12; [|discriminate].
destruct c as [|pc|pc]; try discriminate.
do 6 (destruct pc as [pc|pc|]; try discriminate).
lazymatch type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
injection Hn as <-.
apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Hlo].
apply andb_prop in Hc as [Hc Hwr]. apply andb_prop in Hc as [Hpc Heq].
apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2. pose proof len_s0 as Ls0.
destruct Xpn as (X1 & X2 & X3). destruct Ep as (Ep0 & Ep1 & Ep2 & Ep3 & Ep4).
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
destruct (SINV_vals E FULL HS) as (V1 & V2 & V3).
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.

destruct (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 10 p HC ltac:(lia) Hp10) as [H10 Hpr].
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
destruct (reg_lit_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 12 _ HC ltac:(lia) Hp12) as [H12 _].
replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in H12 by (apply bv_eq; reflexivity).
pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 11) (eaddz e_str0 1) HK Heq) as H11e.
pose proof (reg_sound SEGS A LIMIT USP SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as H11.
replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in H11 by (apply bv_eq; reflexivity). rewrite H11e in H11.
assert (H11' : getr R 11%bv = Z_to_bv 64 (STR0 + Z.of_nat 0 + 1)).
{ rewrite H11. unfold eaddz. rewrite mkAlu_denot, edenot_lit. apply bv_eq. rewrite u_add64, !u64_lit by (unfold STR0; lia).
unfold uE in V3. rewrite V3. rewrite Z.mod_small by (unfold STR0; lia). lia. }

destruct (kwritable_sound SEGS E _ (kn cs) (kn cs) (ELit 0) p 8 HK HK Hwr ltac:(lia)) as (HKW & _ & _).
unfold estart in HKW. cbn [a_base a_off] in HKW. rewrite edenot_lit, u64_lit in HKW by lia. rewrite Z.add_0_l in HKW.
change (Z.to_nat 8) with 8%nat in HKW.

set (H2 := Hv E cs model).
set (M0 := mrestrict H2 FULL).
set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
assert (Hst0 : store_ok SEGS M0 (Z_to_bv 64 p) 8 = true).
{ eapply store_ok_mono; [apply Mr_grows_Hv | exact HKW]. }
assert (HM : forall a : word, STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M0 a = wrap_mem ph sp argv envp uid hw rdraw a).
{ intros a Ha. unfold M0, H2. rewrite mrestrict_Hv_high by (unfold STR0, APS.ATOP, STACK_MAX in *; lia). eapply SINV_str0; [exact HS | exact Ha]. }
destruct (pn_loop SEGS (x_pnscan A) wp0 wp1 wp2 wp3 wp4 ltac:(lia) Fp0 Fp1 Fp2 Fp3 Fp4 Ep0 Ep1 Ep2 Ep3 Ep4 Dp0 Dp1 Dp2 Dp3 Dp4
M0 (seg_rom SEGS) p STR0 s0
ltac:(unfold KHI in *; lia) ltac:(unfold STR0; lia) ltac:(left; unfold STR0, KHI in *; lia)
(valid_argv_str_nz argv 0 Hva ltac:(destruct Hva as [Hl _]; lia))
(fun j Hj => rd_str0_j M0 j Hj HM) Hst0
s0 0%nat R M0 eq_refl ltac:(lia) H10 H11' H12 (cellrel_refl M0 p)) as (R' & M' & Hms & Hpost & HM').
unfold cfg_of. fold ms.
assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) M' (seg_rom SEGS))).
{ unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
(co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
intros model' Hinv' Hsame Hclean.
change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) M' (seg_rom SEGS)))
with (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) (munrestrict H2 FULL M') (seg_rom SEGS)).
set (FULL' := munrestrict H2 FULL M').
assert (HF : forall a : word, bv_unsigned a < p \/ p + 8 <= bv_unsigned a -> FULL' a = FULL a).
{ intros a Ha. unfold FULL', munrestrict. destruct (H2 a) eqn:H2a; [reflexivity|].
destruct HM' as [HM1 _]. rewrite (HM1 a Ha). unfold M0, mrestrict. rewrite H2a. reflexivity. }

set (v := nxt cs). set (E' := ext1 E v (getr R' 11%bv)).
assert (Hag : env_agree v E E') by apply ext1_agree.
destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
pose proof (cs_ok_agree SEGS A nx0 LIMIT USP NX0_ge SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
pose proof (hid_agree A nx0 USP argH argH_agree v E E' cs model Hag Fle Fallow) as Hhid.
specialize (Hk E' R' FULL' model' (conj (env_agree_le nx0 v E E' Hag Fle) Hag)).
unfold cfg_of, pc in Hk. cbn [a_ss with_ss mk_ss s_pc] in Hk. rewrite X3 in Hk.
apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].

eapply cs_ok_frame; [exact SINV_frame | exact HC' | exact Hsame | | | reflexivity | |].
- rewrite (allowA_agree A v E E' cs Hag Fallow). exact Hinv'.
- cbn [s_regs]. destruct Hpost as (P11 & P13 & Pag).
eapply (regs_ok_post2 E' _ R R' 11 11%bv _ 13 13%bv); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC') | lia | lia | lia | reflexivity | reflexivity | | |].
+ cbn [edenot]. unfold E'. rewrite ext1_at. reflexivity.
+ rewrite P13, edenot_lit. reflexivity.
+ intros r N1 N2. apply (Pag r). intros [H|H]; [exact (N1 H) | exact (N2 H)].
- cbn [s_know]. unfold Mr. rewrite Hhid.
apply (know_ok_havoc SEGS E' (mrestrict (hid A USP argH E cs model) FULL)).
+ apply kimg_cut_sound. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. unfold Mr in HK'. rewrite Hhid in HK'. exact HK'.
+ intros x Hx. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite !u64_lit in Hx by lia.
unfold mrestrict. rewrite HF by lia. reflexivity.
+ intros x Hx. unfold mrestrict in *. destruct (hid A USP argH E cs model x) eqn:Hh; [exact Hx|].
unfold FULL', munrestrict. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hvx].
unfold H2 at 1. unfold Hv. rewrite Hvx. cbn [negb].
destruct HM' as [_ HM2]. apply HM2. unfold M0, mrestrict, H2, Hv. rewrite Hvx. cbn [negb]. exact Hx.
- intros a Ha. rewrite Hhid in Ha. unfold hid in Ha. apply orb_prop in Ha as [Ha|Ha].
+ apply HF. right. pose proof (argH_high E a Ha). unfold CEIL, KHI in *. lia.
+ unfold FULL', munrestrict. unfold H2 at 1. unfold Hv. rewrite Ha. reflexivity.
Qed.

End NodesD.

Lemma some_inj_acs : forall a b : acs, Some a = Some b -> a = b.
Proof. intros a b H. exact (f_equal (fun o => match o with Some x => x | None => a end) H). Qed.

Section LayoutSound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

Lemma e_argv1w_ge2 : forall E, 2 <= bv_unsigned (ev E V_ARGC) -> edenot E e_argv1w = edenot E e_str1.
Proof.
intros E H. unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit by lia.
replace (1 <? bv_unsigned (ev E V_ARGC)) with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (u64_range (edenot E e_str1)). rewrite Z.mul_1_l. apply Z.mod_small. lia.
Qed.

Lemma e_argv1w_le1 : forall E, bv_unsigned (ev E V_ARGC) <= 1 -> edenot E e_argv1w = edenot E (ELit 0).
Proof.
intros E H. unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, !u64_lit by lia.
replace (1 <? bv_unsigned (ev E V_ARGC)) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity.
Qed.

Lemma kw_argv1_respell : forall E M v v',
kentry_ok SEGS E M (kw_argv1 v) -> edenot E v' = edenot E v -> kentry_ok SEGS E M (kw_argv1 v').
Proof. intros E M v v' HK Hv. unfold kw_argv1 in *. cbn [kentry_ok] in *. rewrite Hv. exact HK. Qed.

Theorem x_sound_layout : x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XLayout.
Proof.
intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_layout in Hn.
destruct (existsb (kentry_eqb (kw_argv1 e_argv1w)) (kn cs)) eqn:Hex; [|discriminate]. cbn [negb] in Hn.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.

apply existsb_exists in Hex as [K0 [Hin Heqb]]. apply kentry_eqb_eq in Heqb. subst K0.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HK0.
assert (HK' : know_ok SEGS E (Mr A USP argH E cs model FULL)
(List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) (kn cs)))
by (apply know_ok_filter; exact HK).
assert (FIN : forall v, edenot E v = edenot E e_argv1w ->
cs' = set_kn cs (kw_argv1 v :: List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) (kn cs)) ->
srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T).
{ intros v Hv ->. specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK'].
eapply kw_argv1_respell; [exact HK0 | exact Hv]. }

destruct args as [|[z| | | | | | |] [|e2 l2]]; try discriminate; destruct z as [|pz|pz]; try discriminate;
try (destruct pz; try discriminate).
-
destruct (xhi (kn cs) (EVar V_ARGC)) as [hi|] eqn:Hhi; [|discriminate].
destruct (Z.leb hi 1) eqn:Hle; [|discriminate]. apply Z.leb_le in Hle. apply some_inj_acs in Hn.
pose proof (xhi_sound SEGS E _ (kn cs) (EVar V_ARGC) hi HK Hhi) as B. cbn [edenot] in B.
apply (FIN (ELit 0)); [|symmetry; exact Hn]. symmetry. apply e_argv1w_le1. lia.
-
destruct (xlo (kn cs) (EVar V_ARGC)) as [lo|] eqn:Hlo; [|discriminate].
destruct (Z.leb 2 lo) eqn:Hle; [|discriminate]. apply Z.leb_le in Hle. apply some_inj_acs in Hn.
pose proof (xlo_sound SEGS E _ (kn cs) (EVar V_ARGC) lo HK Hlo) as B. cbn [edenot] in B.
apply (FIN e_str1); [|symmetry; exact Hn]. symmetry. apply e_argv1w_ge2. lia.
Qed.
End LayoutSound.

End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBCP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBCP.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG64.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qek8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qek8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHup.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxyE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxyE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQny.Mq0.
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Nodes.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
(segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Hypothesis USP_ok : APS.usp_ok USP.
Hypothesis HULL_cov : APS.hull_cov SEGS A.
Hypothesis NX0_ge : APS.nx0_ge nx0.
Hypothesis argH_sp : forall E (a : word), argH E a = true -> USP <= bv_unsigned a.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT USP SINV argH FS0).
#[local] Notation VIS := (APS.vis A USP).
#[local] Notation MR := (APS.Mr A USP argH).
#[local] Notation cfg := (cfg_of SEGS).
#[local] Notation ATOP := (APS.ATOP USP).

Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

Let reg_sound' := APS.reg_sound SEGS A LIMIT USP SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT USP SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT USP NX0_ge SINV argH argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT USP SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 USP argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT USP HS XN XE XB SHADOW_ok USP_ok SINV argH argH_sp FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A USP HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A USP SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.
Let ATOP_range' : CEIL <= ATOP <= ATOP_MAX := APS.ATOP_range USP USP_ok.

Let budget_slack := QxyE.budget_slack SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok.
Let dest_hyps := QxyE.dest_hyps SEGS A LIMIT USP SINV argH FS0.
Let escale_4096_denot := QxyE.escale_4096_denot SEGS A RES_len HULL_ok.
Let find_containing_sound := QxyE.find_containing_sound SEGS A RES_len.
Let fixed_args_sound := QxyE.fixed_args_sound SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok.
Let fixed_cs1 := QxyE.fixed_cs1 A.
Let gap_ok_sound := QxyE.gap_ok_sound SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let gap_weight_eq := QxyE.gap_weight_eq SEGS A RES_len.
Let grant_cs1_ok := QxyE.grant_cs1_ok SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok SINV_frame USP_ok argH_sp.
Let grant_eager_le := QxyE.grant_eager_le SEGS A RES_len HULL_ok.
Let grant_keep_apart := QxyE.grant_keep_apart SEGS A RES_len HULL_ok.
Let grant_new_facts := QxyE.grant_new_facts SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok argH_sp.
Let grant_vis_add := QxyE.grant_vis_add SEGS A LIMIT USP SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high USP_ok argH_sp.
Let grant_wf := QxyE.grant_wf SEGS A RES_len.
Let in_allow_ext := QxyE.in_allow_ext A.
Let inside_maps_apart := QxyE.inside_maps_apart SEGS A RES_len HULL_ok.
Let kimg_in_hull_cons2 := QxyE.kimg_in_hull_cons2 A USP HULL_ok SHADOW_ok USP_ok.
Let kimg_in_hull_pure := QxyE.kimg_in_hull_pure A.
Let kdisj_all_pure := QxyE.kdisj_all_pure.
Let kdisj_cover_pure := QxyE.kdisj_cover_pure.
Let kdisj_frame_pure := QxyE.kdisj_frame_pure A.
Let kdisj_shframe_pure := QxyE.kdisj_shframe_pure A.
Let kmem_ok := QxyE.kmem_ok SEGS A RES_len HULL_ok.
Let kn_grant_filter_ok := QxyE.kn_grant_filter_ok SEGS A RES_len HULL_ok.
Let kn_rezero_clip_ok := QxyE.kn_rezero_clip_ok SEGS A RES_len HULL_ok.
Let kn_rezero_hull_ok := QxyE.kn_rezero_hull_ok SEGS A RES_len HULL_ok.
Let kn_rezero_ok_gen := QxyE.kn_rezero_ok_gen SEGS A RES_len HULL_ok.
Let kn_unfill_clip_ok := QxyE.kn_unfill_clip_ok SEGS A RES_len HULL_ok.
Let maps_match_disjoint := QxyE.maps_match_disjoint SEGS A RES_len.
Let mmap_fixed_grant_cs1 := QxyE.mmap_fixed_grant_cs1 SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame USP_ok argH_sp.
Let mmap_fixed_old_facts := QxyE.mmap_fixed_old_facts SEGS A nx0 LIMIT USP SINV argH FS0 RES_len RES_hull HULL_ok USP_ok.
Let mmap_fixed_hole_facts := QxyE.mmap_fixed_hole_facts SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok SHADOW_ok USP_ok.
Let fixed_pre := QxyE.fixed_pre SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok.
Let mmap_len_sound := QxyE.mmap_len_sound SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok.
Let mmap_null_cs1 := QxyE.mmap_null_cs1 SEGS A nx0 LIMIT USP SINV argH FS0 RES_len HULL_ok SHADOW_ok argH_agree SINV_frame SINV_agree USP_ok HULL_cov NX0_ge argH_sp.
Let null_cs1 := QxyE.null_cs1 A.
Let overlap_sum_contained := QxyE.overlap_sum_contained SEGS A RES_len HULL_ok.
Let page_aligned_sound := QxyE.page_aligned_sound SEGS A RES_len.
Let refuse_cont := QxyE.refuse_cont SEGS A nx0 LIMIT USP SINV argH FS0 RES_len SINV_frame.
Let refuse_ok := QxyE.refuse_ok SEGS A LIMIT USP SINV argH FS0 RES_len SINV_frame.
Let region_free_of_apart := QxyE.region_free_of_apart SEGS A nx0 LIMIT USP SINV argH FS0 RES_len RES_hull HULL_ok.
Let regs_ok_regupd_same := QxyE.regs_ok_regupd_same SEGS A RES_len.
Let reserved_free_above := QxyE.reserved_free_above SEGS A RES_len RES_hull HULL_ok.
Let safe_range_apart := QxyE.safe_range_apart SEGS A RES_len HULL_ok.
Let seps_map_disjoint := QxyE.seps_map_disjoint SEGS A RES_len.
Let shadow_facts_new_ok := QxyE.shadow_facts_new_ok SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok SHADOW_ok USP_ok.
Let slice_args := QxyE.slice_args SEGS A LIMIT USP SINV argH FS0 RES_len RES_hull HULL_ok USP_ok.
Let slice_hyps := QxyE.slice_hyps SEGS A LIMIT USP SINV argH FS0.
Let split_flat_estart := QxyE.split_flat_estart SEGS A RES_len HULL_ok.
Let vis_add_inv := QxyE.vis_add_inv A LIMIT.
Let vis_add_slice_ok := QxyE.vis_add_slice_ok SEGS A LIMIT USP SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high USP_ok argH_sp.
Let vis_grant_out := QxyE.vis_grant_out SEGS A USP RES_len.
Let d_MR_in := QxyE.d_MR_in SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let d_MR_out := QxyE.d_MR_out SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let d_bounds := QxyE.d_bounds SEGS A LIMIT USP SINV argH FS0.
Let d_eager := QxyE.d_eager SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let d_in_maps := QxyE.d_in_maps SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok.
Let d_lazy_out := QxyE.d_lazy_out SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let d_lohi := QxyE.d_lohi SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let d_maps_in := QxyE.d_maps_in SEGS A LIMIT USP SINV argH FS0 RES_len.
Let d_maps_out := QxyE.d_maps_out SEGS A LIMIT USP SINV argH FS0 RES_len.
Let d_noacc_in := QxyE.d_noacc_in SEGS A LIMIT USP SINV argH FS0 RES_len.
Let d_noacc_out := QxyE.d_noacc_out SEGS A LIMIT USP SINV argH FS0 RES_len.
Let d_sub_in := QxyE.d_sub_in SEGS A LIMIT USP SINV argH FS0 RES_len.
Let d_sub_out := QxyE.d_sub_out SEGS A LIMIT USP SINV argH FS0 RES_len.
Let d_vis_in := QxyE.d_vis_in SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let d_vis_out := QxyE.d_vis_out SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let d_wf' := QxyE.d_wf' SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let dest_cs1_ok := QxyE.dest_cs1_ok SEGS A LIMIT USP SINV argH FS0 RES_len RES_hull HULL_ok SHADOW_ok SINV_frame USP_ok argH_sp.
Let page_base_aligned := QxyE.page_base_aligned SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok.
Let sl_MR_out := QxyE.sl_MR_out SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_bounds := QxyE.sl_bounds SEGS A LIMIT USP SINV argH FS0.
Let sl_eager := QxyE.sl_eager SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_in_maps := QxyE.sl_in_maps SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok.
Let sl_lazy_in := QxyE.sl_lazy_in SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_lazy_out := QxyE.sl_lazy_out SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_lohi := QxyE.sl_lohi SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_noacc_in := QxyE.sl_noacc_in SEGS A LIMIT USP SINV argH FS0 RES_len.
Let sl_noacc_out := QxyE.sl_noacc_out SEGS A LIMIT USP SINV argH FS0 RES_len.
Let sl_vis_in_E := QxyE.sl_vis_in_E SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_vis_in_F := QxyE.sl_vis_in_F SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_vis_in_G := QxyE.sl_vis_in_G SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_vis_out := QxyE.sl_vis_out SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let sl_wf' := QxyE.sl_wf' SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok USP_ok.
Let slice_cs1_ok := QxyE.slice_cs1_ok SEGS A LIMIT USP SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame USP_ok argH_sp.

Lemma mmap_null_sound2 : forall cs kd (eager visible : bool) cs' E R FULL model TB,
CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
reg_lit cs 17 = Some 222 -> reg_lit cs 10 = Some 0 ->
reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
reg_lit cs 13 = Some (if kind_lazy kd then 16418 else 34) ->
reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
(kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
visible = negb (kind_none kd) ->
mmap_null A nx0 LIMIT cs kd eager visible = Some cs' ->
(forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
intros cs kd eager visible cs' E R FULL model TB HC Hec H17 H10 H12 H13 H14 H15 Hkind Hkfog Hvisible Hn HK.
destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
pose proof Hn as Hn0.
unfold mmap_null in Hn.
destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hnoh].
apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hcond Hgap].
apply andb_prop in Hcond as [Hfresh Hnev].

destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
destruct (reg_lit_sound' E cs R FULL model 10 0 HC ltac:(lia) H10) as [R10 _].
destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
rewrite <- bv5_17 in R17. rewrite <- bv5_10 in R10. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
set (n := Z_to_bv 64 nZ).
destruct (gap_ok_sound E cs R FULL model nhi nZ HC Hgap ltac:(lia)) as [a0 Ha0].
pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.

pose proof (grant_ok_na_pin_of_gate _ _ _ _ Hisp Ha0) as Ha0'.

assert (CONT : forall (a : word) model' FULL',
grant_ok_na_pin model a nZ = true ->
grant_post kd a n model model' -> grant_mem kd a n FULL FULL' -> m_fs model' = m_fs model ->
srealizes SEGS (mkCfg (mkst (regupd R 10 a) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
{ intros a model' FULL' Hg GPo GM Hfs.
destruct (mmap_null_cs1 cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev
ltac:(intros ->; cbn in Hbud; unfold budget_ok in Hbud; apply Z.leb_le in Hbud; exact Hbud)
Hkind Hkfog Hnoh Hg GPo GM) as (HC1 & Hbase & HneE' & Un & Hag0 & NEW).
fold len nZ n in HC1, HneE', Un, NEW.
rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
set (E' := ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))) in *.
assert (Hpc : pc cs' = pc cs + 4).
{ destruct visible; [|injection Hn as <-; reflexivity].
destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
specialize (HK E' (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model' (conj Hag0 (ext1_agree'' E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))))).
unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
destruct visible.
-
assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hvisible |- *; congruence).
pose proof (u64_range a) as Ra.
unfold grant_ok_na_pin in Hg. apply andb_prop in Hg as [Hg _].
apply andb_prop in Hg as [Hg Hceil]. apply Z.leb_le in Hceil. pose proof (alloc_top_lt (m_vmmaps model)) as Htoplt. unfold two_pow_64 in Htoplt.
eapply (grant_vis_add E' (null_cs1 cs kd eager ne nlo nhi) cs' _ ne _ FULL' model' a n nZ HC1 Hn).
+ unfold null_cs1, add_entry. cbn [kn a_ss mk_ss s_know]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
apply kimg_in_hull_pure.
repeat (apply (proj2 (Forall_app _ _ _)); split); try apply kdisj_all_pure; try apply kdisj_cover_pure; try apply kdisj_frame_pure; try apply kdisj_shframe_pure.
apply Forall_cons; [exact I | apply null_kend_pure].
+ exact Hbase.
+ exact HneE'.
+ exact Un.
+ lia.
+ lia.
+ intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & _). rewrite (gp_noacc _ _ _ _ _ GPo), Hrw. auto.
+ intros x Hx. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity.
- injection Hn as <-. exact HC1. }

unfold cfg_of.
destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
-
destruct eager; [|discriminate].
eapply (srz_mmap_rw2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
+ exists a0. split; [exact Ha0'|]. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22.
apply Z.leb_le. cbn in Hbud. eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
+ intros a Hg _. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
* constructor; reflexivity.
* split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
-
destruct eager; [discriminate|].
eapply (srz_mmap_rw2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
+ exists a0. split; [exact Ha0'|]. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_4022. reflexivity.
+ intros a Hg _. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
* pose proof Hg as Hg'. unfold grant_ok_na_pin in Hg'. apply andb_prop in Hg' as [Hg' _].
apply andb_prop in Hg' as [Hg' Hceil]. apply andb_prop in Hg' as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.leb_le in Hceil. pose proof (alloc_top_lt (m_vmmaps model)) as Htoplt. unfold two_pow_64 in Htoplt. unfold page_size in Hal.
constructor; try reflexivity.
unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by lia; [exact HnZal | lia | lia].
* split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
-
destruct eager; [discriminate|].
eapply (srz_mmap_none2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
+ exists a0. exact Ha0'.
+ intros a Hg. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
* constructor; reflexivity.
* split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
-
destruct eager; [discriminate|].
eapply (srz_mmap_none2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
+ exists a0. exact Ha0'.
+ intros a Hg. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
* pose proof Hg as Hg'. unfold grant_ok_na_pin in Hg'. apply andb_prop in Hg' as [Hg' _].
apply andb_prop in Hg' as [Hg' Hceil]. apply andb_prop in Hg' as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.leb_le in Hceil. pose proof (alloc_top_lt (m_vmmaps model)) as Htoplt. unfold two_pow_64 in Htoplt. unfold page_size in Hal.
constructor; try reflexivity.
unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by lia; [exact HnZal | lia | lia].
* split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Definition fixed_free_flags (kd : mkind) (flg : Z) : Prop :=
flg = (if kind_lazy kd then 16434 else 50) \/ (flg = 1064994 /\ kind_lazy kd = true).

Lemma mmap_fixed_grant_sound2 : forall cs ms0 top b off ne nlo nhi kd (eager visible : bool) cs' E R FULL model TB flg,
CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
reg_lit cs 17 = Some 222 ->
reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
reg_lit cs 13 = Some flg -> fixed_free_flags kd flg ->
reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
(kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
visible = eager ->
fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= TOPIN ->
(negb eager || budget_ok LIMIT cs nhi)%bool = true ->
CSOK E (with_maps0 cs ms0) R FULL model ->
region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (edenot E (reg cs 10))
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true ->
(forall m, In m ms0 -> is_hole m = true ->
bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= uE E (am_base m)
\/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (edenot E (reg cs 10))) ->
bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= ATOP ->
mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kd eager visible = Some cs' ->
(forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
intros cs ms0 top b off ne nlo nhi kd eager visible cs' E R FULL model TB flg HC Hec H17 H12 H13 FLG H14 H15 Hkind Hkfog Hvisible HFA Htop Hbud HC0 Hrf Hholes HaT Hn HK.
pose proof ATOP_range' as AT.
destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
assert (Hbudget : eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
{ intros ->. cbn in Hbud. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }
unfold mmap_fixed_grant in Hn.

destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & _).
destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & _).
change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.

destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop)
as (HneE & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
fold len nZ n addr in HneE, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
fold len nZ addr in HaT.
assert (HaK : bv_unsigned addr + nZ <= ATOP_MAX) by lia.
rewrite <- bv5_10 in R10.
assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model)).
{ fold nZ. unfold alloc_top, stack_max_size. rewrite (co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC). unfold APS.ATOP, STACK_MAX in HaT. exact HaT. }

assert (CONT : forall model' FULL',
grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' -> m_fs model' = m_fs model ->
srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
{ intros model' FULL' GPo GM Hfs.
destruct (mmap_fixed_grant_cs1 cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 HaT Hrf Hholes Hbudget Hkind Hkfog GPo GM) as (HC1 & NEW).
fold len nZ n addr in HC1, NEW.
rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
assert (Hpc : pc cs' = pc cs + 4).
{ destruct visible; [|injection Hn as <-; reflexivity].
destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
destruct visible.
-
subst eager. assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hkind |- *; congruence).
pose proof (u64_range addr) as Ra.
eapply (vis_add_sound'); [exact Hn | exact HC1 |].
destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs2).
apply Forall_app. split.
+
assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat, elenZ; rewrite Hest, HneE, Un; unfold ATOP_MAX in HaK; lia).
assert (BYTE : forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
MR E cs' model' FULL' x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1. rewrite (gp_noacc _ _ _ _ _ GPo), Hrw, N2. cbn [negb andb].
assert (Hallow : in_allow A E cs' (bv_unsigned x) = true).
{ unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd with_maps0]. unfold uE. fold addr. rewrite HneE, Un.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
rewrite Hallow, !orb_true_r. cbn [negb]. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity. }
constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; unfold elenZ; rewrite Hest, HneE, Un.
* intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
apply store_ok_of_all; [rewrite u64_lit by (unfold ATOP_MAX in HaK; lia); unfold ATOP_MAX in HaK; lia|].
intros x Hx. rewrite u64_lit in Hx by (unfold ATOP_MAX in HaK; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
* intros i Hi. apply BYTE. rewrite u64_lit by (unfold ATOP_MAX in HaK; lia). lia.
+
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
eapply know_ok_unhide'; [apply H_off_segments_cs' | | | | exact HK1].
* unfold fixed_cs1, add_entry. cbn [kn a_ss mk_ss s_know with_maps0]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
destruct kd; cbn [mkind_eqb]; try (apply kimg_in_hull_pure; apply Forall_nil).
apply kimg_in_hull_pure. apply Forall_flat_map. apply Forall_forall. intros p _. unfold shadow_facts.
destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn]. destruct (find_containing _ _ _ _ _ _); [|apply Forall_nil].
apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
* intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
* intros y Hy. apply hid_hull'. exact Hy.
- injection Hn as <-. exact HC1. }

unfold cfg_of.
destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
-
destruct FLG as [-> | [_ F]]; [|discriminate F].
destruct eager; [|discriminate].
eapply (srz_mmap_fixed_rw_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce R12 R13 mmap_flags_core_32 R14 R15 Hrf).
+ unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_32. apply Z.leb_le. cbn in Hbud.
eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
+ rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
apply CONT; [constructor; reflexivity | | reflexivity].
split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
-
destruct eager; [discriminate|].
assert (STEP : forall flagsw, getr R 13 = flagsw -> mmap_noreserve_b flagsw = true ->
(mmap_flags_core flagsw = 50%Z \/ mmap_noreplace_flags_b flagsw = true) ->
srealizes SEGS (cfg R (pc cs) FULL model) TB).
{ intros flagsw R13w Hnrw [Hcw | Hcw].
- eapply (srz_mmap_fixed_rw_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len flagsw TB
Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce R12 R13w Hcw R14 R15 Hrf).
+ unfold mmap_noreserve_backed_ok. rewrite Hnrw. reflexivity.
+ rewrite with_mmap_backing_lazy by exact Hnrw.
fold nZ. fold n. apply CONT; [| | reflexivity].
* constructor; try reflexivity.
unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold ATOP_MAX in HaK; lia].
* split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
- eapply (srz_mmap_noreplace_rw_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len flagsw TB
Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce R12 R13w Hcw R14 R15 Hrf).
+ unfold mmap_noreserve_backed_ok. rewrite Hnrw. reflexivity.
+ rewrite with_mmap_backing_lazy by exact Hnrw.
fold nZ. fold n. apply CONT; [| | reflexivity].
* constructor; try reflexivity.
unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold ATOP_MAX in HaK; lia].
* split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx]. }
destruct FLG as [-> | [-> _]].
+ exact (STEP (Z_to_bv 64 16434) R13 mmap_noreserve_b_4032 (or_introl mmap_flags_core_4032)).
+ exact (STEP (Z_to_bv 64 1064994) R13 mmap_noreserve_b_104022 (or_intror mmap_noreplace_flags_b_104022)).
-
destruct FLG as [-> | [_ F]]; [|discriminate F].
destruct eager; [discriminate|].
eapply (srz_mmap_fixed_none_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce R12 R13 mmap_flags_core_32 R14 R15 Hrf).
+ rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
apply CONT; [constructor; reflexivity | | reflexivity].
split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
-
destruct eager; [discriminate|].
assert (STEP : forall flagsw, getr R 13 = flagsw -> mmap_noreserve_b flagsw = true ->
(mmap_flags_core flagsw = 50%Z \/ mmap_noreplace_flags_b flagsw = true) ->
srealizes SEGS (cfg R (pc cs) FULL model) TB).
{ intros flagsw R13w Hnrw [Hcw | Hcw].
- eapply (srz_mmap_fixed_none_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len flagsw TB
Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce R12 R13w Hcw R14 R15 Hrf).
+ rewrite with_mmap_backing_lazy by exact Hnrw.
fold nZ. fold n. apply CONT; [| | reflexivity].
* constructor; try reflexivity.
unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold ATOP_MAX in HaK; lia].
* split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
- eapply (srz_mmap_noreplace_none_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len flagsw TB
Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce R12 R13w Hcw R14 R15 Hrf).
+ rewrite with_mmap_backing_lazy by exact Hnrw.
fold nZ. fold n. apply CONT; [| | reflexivity].
* constructor; try reflexivity.
unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold ATOP_MAX in HaK; lia].
* split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx]. }
destruct FLG as [-> | [-> _]].
+ exact (STEP (Z_to_bv 64 16434) R13 mmap_noreserve_b_4032 (or_introl mmap_flags_core_4032)).
+ exact (STEP (Z_to_bv 64 1064994) R13 mmap_noreserve_b_104022 (or_intror mmap_noreplace_flags_b_104022)).
Qed.

Lemma mmap_fixed_free_sound2 : forall cs kd (eager visible : bool) cs' E R FULL model TB flg,
CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
reg_lit cs 17 = Some 222 ->
reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
reg_lit cs 13 = Some flg -> fixed_free_flags kd flg ->
reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
(kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
visible = eager ->
mmap_fixed_free A LIMIT cs kd eager visible = Some cs' ->
(forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
intros cs kd eager visible cs' E R FULL model TB flg HC Hec H17 H12 H13 FLG H14 H15 Hkind Hkfog Hvisible Hn HK.
unfold mmap_fixed_free in Hn.
destruct (fixed_args A cs KHI) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
-
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hnf Hall].
destruct (mmap_fixed_old_facts cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall) as (HC0 & Hrf & Hholes & Hside).
eapply (mmap_fixed_grant_sound2 cs (a_maps cs) KHI b off ne nlo nhi kd eager visible cs' E R FULL model TB flg
HC Hec H17 H12 H13 FLG H14 H15 Hkind Hkfog Hvisible HFA ltac:(unfold KHI, TOPIN; lia) Hbud
HC0 Hrf Hholes Hside Hn HK).
-
destruct (fixed_args A cs TOPIN) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA2; [|discriminate].
destruct (find_hole (kn cs) (a_maps cs) (reg cs 10) ne) as [h|] eqn:Hfh; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
apply andb_prop in Hcond as [Hap Hbud].
destruct (mmap_fixed_hole_facts cs b off ne nlo nhi h E R FULL model HC HFA2 Hfh Hap) as (HC0 & Hrf & Hholes & Hside).
eapply (mmap_fixed_grant_sound2 cs (unhole (a_maps cs) h) TOPIN b off ne nlo nhi kd eager visible cs' E R FULL model TB flg
HC Hec H17 H12 H13 FLG H14 H15 Hkind Hkfog Hvisible HFA2 ltac:(lia) Hbud
HC0 Hrf Hholes Hside Hn HK).
Qed.

Lemma node_mprotect_sound2 : forall cs cs' E R FULL model TB,
CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
node_mprotect A LIMIT cs = Some cs' ->
(forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
intros cs cs' E R FULL model TB HC Hec Hn HK.
destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
rewrite node_mprotect_eq in Hn.  unfold node_mprotect_ref in Hn.
destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
destruct (reg_lit cs 12) as [z12|] eqn:H12.
2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
destruct (fixed_args_in cs TOPIN) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
assert (Hz : z17 = 226 /\ z12 = 3).
{ repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
destruct Hz as [-> ->].
destruct (find_containing (kn cs) (a_maps cs) [KNONE; KNONELAZY] b off ne) as [m|] eqn:Hfind; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [Hbud _].
unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
destruct (reg_lit_sound' E cs R FULL model 17 226 HC ltac:(lia) H17) as [R17 _].
destruct (reg_lit_sound' E cs R FULL model 12 3 HC ltac:(lia) H12) as [R12 _].
rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12.
destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
pose proof (proj2 (proj2 (proj2 Hwf))) as Hisp.
pose proof (u64_range addr) as Ra.
assert (Hkind' : am_kind m = KNONE \/ am_kind m = KNONELAZY) by (cbn in Hkind; destruct Hkind as [<-|[<-|[]]]; auto).

assert (Hna : map_contains (vm_noaccess (m_vmmaps model)) addr n = true).
{ pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hkind') as X.
eapply map_contains_intro; [exact X | exact Hin1 | rewrite Un; exact Hin2]. }
unfold cfg_of.
eapply (srz_mprotect2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len TB Hf He Hhalt R17 R10 Hal R11 ltac:(lia)).
- unfold two_pow_64. fold nZ. pose proof ATOP_range' as AT. unfold CEIL, ATOP_MAX in AT. lia.
- exact R12.
- exact Hna.
- exact Hmc.
- apply mprotect_budget_ok_intro_gen; [exact Hwf|]. pose proof (budget_slack E cs R FULL model nhi HC ltac:(unfold budget_ok; apply Z.leb_le; exact Hbud)). fold nZ n. lia.
- fold nZ. fold n.
set (model' := mprotect_model addr n model). set (FULL' := zfill addr n FULL).
assert (SPo : slice_post SlM addr n model model') by (constructor; reflexivity).
assert (SM : slice_mem SlM addr n FULL FULL').
{ split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx]. }
assert (SH : slice_hyps E cs R FULL model SlM m addr n nZ model' FULL').
{ constructor; try assumption; intros HH; [discriminate HH|]. intros Hk. rewrite Hk in Hkind'. destruct Hkind'; discriminate. }
rewrite (v_addi_pc (pc cs) Hp0 Hp4).
destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs').
assert (Hpc : pc cs' = pc cs + 4) by (rewrite Ecs'; reflexivity).
specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
unfold cfg_of in HK. rewrite Hpc, <- bv5_10 in HK. apply HK; [|reflexivity]. clear HK.
assert (Hregs' : regs_ok E (sr_upd (s_regs (a_ss cs)) 10 (ELit 0)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0))).
{ apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) | lia | reflexivity]. }
assert (MROUT := fun x => sl_MR_out E cs R FULL model SlM m addr n nZ model' FULL' SH cs x eq_refl).
assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
MR E cs model' FULL' x = MR E cs model FULL x).
{ intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
{ eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT']. }
pose proof (slice_cs1_ok E cs R FULL model SlM m addr n nZ model' FULL' SH _ _ _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud)) as HC1.
cbn [sl_charge] in HC1.
eapply (vis_add_slice_ok E _ cs' (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
+ exact Hn.
+ cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
+ reflexivity.
+ exact Hest.
+ unfold elenZ. rewrite Hne. exact Un.
+ lia.
+ lia.
+ lia.
+ intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
split; [exact (sl_in_maps E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
split; [exact (sl_noacc_in E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
split; [destruct (argH E x) eqn:Ea; [pose proof (argH_sp _ _ Ea); unfold APS.ATOP, STACK_MAX in *; lia | reflexivity]|].
rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
Qed.

Lemma mmap_gate_sound : forall cs prot flags isnull,
mmap_gate cs = Some (prot, flags, isnull) ->
reg_lit cs 17 = Some 222 /\ reg_lit cs 12 = Some prot /\ reg_lit cs 13 = Some flags
/\ reg_lit cs 14 = Some (two64 - 1) /\ reg_lit cs 15 = Some 0
/\ (isnull = true -> reg_lit cs 10 = Some 0).
Proof.
intros cs prot flags isnull Hg. unfold mmap_gate in Hg.
destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
destruct (reg_lit cs 12) as [p|] eqn:H12.
2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
destruct (reg_lit cs 13) as [f|] eqn:H13.
2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
destruct (reg_lit cs 14) as [m1|] eqn:H14.
2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
destruct (reg_lit cs 15) as [z15|] eqn:H15.
2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
assert (Hz : z17 = 222 /\ z15 = 0).
{ repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
destruct Hz as [-> ->]. cbn iota in Hg.
match type of Hg with (if negb ?c then None else _) = _ => destruct c eqn:Hm1; [|discriminate] end. cbn [negb] in Hg.
apply Z.eqb_eq in Hm1. subst m1. injection Hg as <- <- <-.
repeat split; try reflexivity.
destruct (reg_lit cs 10) as [[|p10|p10]|]; intros H; try discriminate H. reflexivity.
Qed.

Theorem node_mmap2_sound : mm2_stmt SEGS A nx0 LIMIT USP SINV argH FS0 (node_mmap2 A nx0 LIMIT).
Proof.
intros cs csa csb E R FULL model TB HC Hec Hn HKB.
unfold node_mmap2 in Hn.
destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & H10).
match type of Hn with (match ?g with Some csG => _ | None => None end) = _ => destruct g as [csG|] eqn:HG; [|discriminate] end.
injection Hn as <- <-.
destruct isnull.
- specialize (H10 eq_refl).
assert (ARMS : (prot = 3 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KRW true true = Some csG)
\/ (prot = 3 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KRWLAZY false true = Some csG)
\/ (prot = 0 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KNONE false false = Some csG)
\/ (prot = 0 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KNONELAZY false false = Some csG)).
{ repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]].
+ eapply (mmap_null_sound2 cs KRW true true); eauto; reflexivity.
+ eapply (mmap_null_sound2 cs KRWLAZY false true); eauto; reflexivity.
+ eapply (mmap_null_sound2 cs KNONE false false); eauto; reflexivity.
+ eapply (mmap_null_sound2 cs KNONELAZY false false); eauto; reflexivity.
- assert (ARMS : (prot = 3 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csG)
\/ (prot = 3 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KRW true true = Some csG)
\/ (prot = 0 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csG)
\/ (prot = 0 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KNONE false false = Some csG)
\/ (prot = 3 /\ flags = 1064994 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csG)
\/ (prot = 0 /\ flags = 1064994 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csG)).
{ repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]]]].
+ eapply (mmap_fixed_free_sound2 cs KRWLAZY false false); eauto; [left; reflexivity | reflexivity..].
+ eapply (mmap_fixed_free_sound2 cs KRW true true); eauto; [left; reflexivity | reflexivity..].
+ eapply (mmap_fixed_free_sound2 cs KNONELAZY false false); eauto; [left; reflexivity | reflexivity..].
+ eapply (mmap_fixed_free_sound2 cs KNONE false false); eauto; [left; reflexivity | reflexivity..].
+ eapply (mmap_fixed_free_sound2 cs KRWLAZY false false); eauto; [right; split; reflexivity | reflexivity..].
+ eapply (mmap_fixed_free_sound2 cs KNONELAZY false false); eauto; [right; split; reflexivity | reflexivity..].
Qed.

Theorem node_mprotect2_sound : mm2_stmt SEGS A nx0 LIMIT USP SINV argH FS0 (node_mprotect2 A LIMIT).
Proof.
intros cs csa csb E R FULL model TB HC Hec Hn HKB.
unfold node_mprotect2 in Hn.
destruct (node_mprotect A LIMIT cs) as [csG|] eqn:HG; [|discriminate]. injection Hn as <- <-.
eapply node_mprotect_sound2; eauto.
Qed.

Definition slarm_of (arm : fixed_in_arm) : slarm := match arm with ArmE => SlE | ArmF => SlF | ArmG => SlG end.

Lemma mmap_fixed_in_sound3 : forall (hole : bool) cs arm b off ne nlo nhi m csO E R FULL model TB,
CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
reg_lit cs 17 = Some 222 ->
reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
fixed_in_args cs arm = Some (b, off, ne, nlo, nhi, m) ->
mmap_fixed_in A LIMIT cs arm = Some csO ->
(forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csO R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc csO) FULL' model') TB) ->
srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
intros hole cs arm b off ne nlo nhi m csO E R FULL model TB HC Hec H17 H12 H13 H14 H15 HFI Hn HKB.
destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).

rewrite fixed_in_args_eq in HFI.  unfold fixed_in_args_ref in HFI.
destruct (fixed_args_in cs TOPIN) as [[[[[b0 off0] ne0] nlo0] nhi0]|] eqn:HFA; [|discriminate].
destruct (find_containing (kn cs) (a_maps cs) _ b0 off0 ne0) as [m0|] eqn:Hfind; [|discriminate].
match type of HFI with (if ?c then _ else _) = _ => destruct c eqn:Hvars; [|discriminate] end.
injection HFI as -> -> -> -> -> ->.
rewrite mmap_fixed_in_eq in Hn.  unfold mmap_fixed_in_ref in Hn. rewrite fixed_in_args_eq in Hn. unfold fixed_in_args_ref in Hn. rewrite HFA, Hfind, Hvars in Hn.
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hbud; [|discriminate] end.
destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
pose proof (proj2 (proj2 (proj2 Hwf))) as Hisp.
pose proof (u64_range addr) as Ra.
pose proof ATOP_range' as AT.
assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model)).
{ fold nZ. unfold alloc_top, stack_max_size. rewrite (co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC). unfold APS.ATOP, STACK_MAX in HmC. lia. }
assert (HF : slarm_of arm = SlF -> am_kind m = KRWLAZY).
{ intros Hs. destruct arm; try discriminate. cbn in Hkind. destruct Hkind as [<-|[]]. reflexivity. }
assert (HnF : slarm_of arm <> SlF -> am_kind m <> KRWLAZY).
{ intros Hs Hk. destruct arm; [|exact (Hs eq_refl)|]; cbn in Hkind; rewrite Hk in Hkind; destruct Hkind as [|[|[|[]]]]; discriminate. }
set (prot := match arm with ArmG => 0 | _ => 3 end) in *.
set (flg := match arm with ArmF => 16434 | _ => 50 end) in *.
assert (Hprot : prot = 0 \/ prot = 3) by (destruct arm; cbn; lia).
assert (Hcore : mmap_flags_core (Z_to_bv 64 flg) = 50) by (destruct arm; [apply mmap_flags_core_32 | apply mmap_flags_core_4032 | apply mmap_flags_core_32]).

assert (CONTB : forall model' FULL',
slice_post (slarm_of arm) addr n model model' -> slice_mem (slarm_of arm) addr n FULL FULL' -> m_fs model' = m_fs model ->
srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
{ intros model' FULL' SPo SM Hfs.
assert (SH : slice_hyps E cs R FULL model (slarm_of arm) m addr n nZ model' FULL') by (constructor; assumption).
rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
assert (Hpc : pc csO = pc cs + 4).
{ destruct arm; try (injection Hn as <-; reflexivity). destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
specialize (HKB E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
unfold cfg_of in HKB. rewrite Hpc in HKB. apply HKB; [|exact Hfs]. clear HKB.
assert (Hregs' : regs_ok E (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)).
{ apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) | lia | rewrite <- bv5_10; exact R10]. }
assert (MROUT := fun x => sl_MR_out E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH cs x eq_refl).
assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
MR E cs model' FULL' x = MR E cs model FULL x).
{ intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
pose proof (slice_cs1_ok E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)) as CS1.
destruct arm; cbn [slarm_of sl_charge] in *.
-
assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
{ eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT']. }
unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
pose proof (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud)) as HC1.
eapply (vis_add_slice_ok E _ csO (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
+ exact Hn.
+ cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
+ reflexivity.
+ exact Hest.
+ unfold elenZ. rewrite Hne. exact Un.
+ lia.
+ lia.
+ lia.
+ intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
split; [exact (sl_in_maps E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
split; [exact (sl_noacc_in E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
split; [destruct (argH E x) eqn:Ea; [pose proof (argH_sp _ _ Ea); unfold APS.ATOP, STACK_MAX in *; lia | reflexivity]|].
rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
-
assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_rezero (kn cs) b off ne))).
{ eapply kn_rezero_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT' |].
intros x Hx Hdef. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx.
unfold Mr, mrestrict, hid in Hdef |- *.
rewrite (sl_vis_in_F E cs R FULL model SlF m addr n nZ model' FULL' SH eq_refl cs x eq_refl Hx).
destruct (argH E x); [exfalso; apply Hdef; reflexivity|]. cbn [orb] in *.
destruct (VIS E cs model x); [|exfalso; apply Hdef; reflexivity]. cbn [negb].
rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity. }
injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH)).
-
assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_cutout (kn cs) b off ne))).
{ apply know_ok_filter. eapply (APS.know_ok_cutout SEGS); [exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact MROUT']. }
injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH)). }

unfold cfg_of.
assert (R12' : getr R 12 = Z_to_bv 64 prot) by (destruct arm; exact R12).
assert (R13' : getr R 13 = Z_to_bv 64 flg) by (destruct arm; exact R13).
eapply (srz_mmap_fixedin_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w prot (Z_to_bv 64 flg) addr len TB
Hf He Hhalt R17 Hprot Hcore R10 Hal Hpos R11 ltac:(lia) Hce R12' R13' R14 R15 Hrfres Hmc).
-  intros Hp3. fold nZ n. destruct arm; cbn in Hp3; try discriminate Hp3; subst flg.
+ apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact Hwf |].
unfold budget_ok in Hbud. pose proof (budget_slack E cs R FULL model nhi HC Hbud). lia.
+ apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact Hwf | exact Hal | unfold page_size; rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL, ATOP_MAX in AT; lia |].
eapply vm_backing_used_limit; [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) | apply A_wf_allowA'].
- fold nZ. fold n. destruct arm; subst prot flg; cbn [Z.eqb slarm_of] in CONTB |- *.
+  unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
apply CONTB; [| | reflexivity].
* constructor; reflexivity.
* split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
+  unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_4032.
apply CONTB; [| | reflexivity].
* constructor; try reflexivity.
unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing, m_vm_lazy_vm_forget_range.
rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL, ATOP_MAX in AT; lia].
* split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
+  unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
apply CONTB; [| | reflexivity].
* constructor; reflexivity.
* split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Theorem node_mmapin_sound : forall hole : bool, mm3_stmt SEGS A nx0 LIMIT USP SINV argH FS0 (node_mmapin A LIMIT hole).
Proof.
intros hole cs csa csb cscs E R FULL model TB HC Hec Hn HKB.
unfold node_mmapin in Hn.
destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & _).
destruct isnull; [discriminate|]. cbv zeta in Hn.
assert (CASES : forall arm,
reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
match fixed_in_args cs arm, mmap_fixed_in A LIMIT cs arm with
| Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed A hole cs b off ne m)
| _, _ => None
end = Some (csa, csb, cscs) ->
srealizes SEGS (cfg R (pc cs) FULL model) TB).
{ intros arm H12' H13' Hn'.
destruct (fixed_in_args cs arm) as [[[[[[b off] ne] nlo] nhi] m]|] eqn:HFI; [|discriminate].
destruct (mmap_fixed_in A LIMIT cs arm) as [csO|] eqn:HO; [|discriminate]. injection Hn' as <- <- <-.
eapply (mmap_fixed_in_sound3 hole cs arm b off ne nlo nhi m csO); eauto. }
destruct prot as [|p|p]; try discriminate Hn; try (repeat (destruct p as [p|p|]; try discriminate Hn));
destruct flags as [|q|q]; try discriminate Hn; try (repeat (destruct q as [q|q|]; try discriminate Hn));
refine (CASES _ _ _ Hn); first [exact H12 | exact H13].
Qed.

End Nodes.

Section OBL.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis USP_ok : APS.usp_ok USP.
Hypothesis HULL_cov : APS.hull_cov SEGS A.
Hypothesis NX0_ge : APS.nx0_ge nx0.
Hypothesis argH_sp : forall E (a : word), argH E a = true -> USP <= bv_unsigned a.

End OBL.
