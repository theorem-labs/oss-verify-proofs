From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN03 YN02_cf YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN0b_cf YN07_cf YN0a_cf YN1q_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW0e_cf YX00_cf YX01_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN1y_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require YW04_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ad_rm (E0 : env) x l1 l2 l3 : all_disjoint E0 x (l1 ++ l2 ++ l3) -> all_disjoint E0 x (l1 ++ l3).
Proof.
induction l1 as [|y l1 IH]; cbn [app all_disjoint]; intros H.
- induction l2 as [|z l2 IH2]; cbn [app all_disjoint] in H; [exact H | exact (IH2 (proj2 H))].
- destruct H as [H1 H2]. split; [exact H1 | exact (IH H2)].
Qed.
Lemma pd_rm (E0 : env) l1 l2 l3 : pairwise_disjoint E0 (l1 ++ l2 ++ l3) -> pairwise_disjoint E0 (l1 ++ l3).
Proof.
induction l1 as [|y l1 IH]; cbn [app pairwise_disjoint]; intros H.
- induction l2 as [|z l2 IH2]; cbn [app pairwise_disjoint] in H; [exact H | exact (IH2 (proj2 H))].
- destruct H as [H1 H2]. split; [exact (ad_rm E0 y l1 l2 l3 H1) | exact (IH H2)].
Qed.
Lemma pd_app_l (E0 : env) l1 l2 : pairwise_disjoint E0 (l1 ++ l2) -> pairwise_disjoint E0 l1.
Proof. intros H. rewrite <- (app_nil_r l1). apply (pd_rm E0 l1 l2 []). rewrite app_nil_r. exact H. Qed.
Lemma Forall_rm {T : Type} (P : T -> Prop) l1 l2 l3 : Forall P (l1 ++ l2 ++ l3) -> Forall P (l1 ++ l3).
Proof. intros H. apply Forall_app in H as [H1 H2]. apply Forall_app in H2 as [_ H3]. apply Forall_app. split; assumption. Qed.
Lemma fa_cons_inv {T : Type} (P : T -> Prop) x l : Forall P (x :: l) -> P x /\ Forall P l.
Proof. intros H. inversion H. split; assumption. Qed.
Lemma ext_sep (E0 : env) x y lo hi :
(base_val E0 (r_base x) + r_hi x <= lo \/ hi <= base_val E0 (r_base x) + r_lo x) ->
lo <= base_val E0 (r_base y) + r_lo y -> base_val E0 (r_base y) + r_hi y <= hi -> extent_disjoint E0 x y.
Proof. intros H H1 H2. unfold extent_disjoint. lia. Qed.
Lemma bytes_xfer (m m' : word -> option byte) a w v :
(forall k, (k < w)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
bytes_are m a w v -> bytes_are m' a w v.
Proof. intros Hm Hb k Hk. rewrite <- (Hb k Hk). exact (proj1 (YW04_cf.same_views src0segs m m' _ (Hm k Hk))). Qed.
Lemma rc_cases x : 0 <= x ->
(x = 0 /\ rcase_of x = R0) \/ (1 <= x <= 4 /\ rcase_of x = R14) \/ (x = 5 /\ rcase_of x = R5) \/ (6 <= x /\ rcase_of x = R6).
Proof.
intros Hx. unfold rcase_of.
destruct (Z.eqb_spec x 0); [left; auto|]. destruct (Z.ltb_spec x 5); [right; left; split; [lia|reflexivity]|].
destruct (Z.eqb_spec x 5); [right; right; left; auto|]. right; right; right. split; [lia|reflexivity].
Qed.
Lemma mod64_shift x y : 0 <= y < 2 ^ 64 -> x = y + 1 * 2 ^ 64 -> x mod 2 ^ 64 = y.
Proof. intros Hy ->. rewrite Z.mod_add by lia. apply Z.mod_small. exact Hy. Qed.
Definition keepS : smem := [reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk1].
Lemma drop_mid r : drop_bases [aTQ] (head_memS ++ [reg_tq] ++ r_mem r) = head_memS ++ r_mem r.
Proof. destruct r; reflexivity. Qed.
Lemma drop_exit r nc : drop_bases [aP; aEND; aPN] (mem_at r nc) = keepS ++ tabs_of nc.
Proof. destruct r, nc; reflexivity. Qed.
Lemma wf_mid r : regions_wf ((head_memS ++ r_mem r) ++ tabsR) = true.
Proof. destruct r; vm_compute; reflexivity. Qed.
Lemma wf_exit nc t : regions_wf ((keepS ++ tabs_of nc) ++ reg_hdr :: t_memS t) = true.
Proof. destruct nc, t; vm_compute; reflexivity. Qed.
Lemma tab_vals n0 : 157 <= n0 < MMAP_THRESHOLD ->
10 <= kkS n0 <= 8190 /\ 3 <= t0_e (kkS n0) <= 12 /\ znth (dbj_idx (2 ^ t0_e (kkS n0))) DEBRUIJN = t0_e (kkS n0) /\
0 <= dbj_idx (2 ^ t0_e (kkS n0)) < 32 /\
(t0_i3 (kkS n0) = 4 * t0_e (kkS n0) - 4 \/ t0_i3 (kkS n0) = 4 * t0_e (kkS n0) - 2) /\
t0_t1 (kkS n0) = znth (4 * t0_e (kkS n0) - 3) size_classes.
Proof.
intros Hn.
assert (K : 10 <= kkS n0 <= 8190).
{ unfold kkS, nS. replace (n0 <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia).
unfold MMAP_THRESHOLD in Hn. split; [apply Z.div_le_lower_bound; lia|].
assert ((n0 + 3) / 16 < 8191) by (apply Z.div_lt_upper_bound; lia). lia. }
pose proof (t0_facts (kkS n0) K) as (_ & _ & _ & _ & _ & He & Hd).
split; [exact K|]. split; [exact He|]. split; [exact Hd|]. split; [apply dbj_idx_range|].
split; [unfold t0_i3; destruct (t0_b1 (kkS n0)); [left|right]; reflexivity | reflexivity].
Qed.
Section b.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : small_ctx L A regs mem md g am idx fr n a ka rg.
Local Abbreviation V := (vS L regs g am idx fr a rg).
Local Abbreviation XV := (xvS L regs g am idx fr a rg n).
Local Abbreviation HX f := (f L A regs mem md g am idx fr n a ka rg HC) (only parsing).
Lemma NUM :
4096 <= fv_glo V /\ fv_ghi V <= alloc_ceiling /\ fv_glo V <= XV aMEM /\ XV aMEM + 8 <= XV aP - 4 /\
XV aP <= XV aEND /\ XV aEND + 1 <= fv_ghi V /\ XV aP <= XV aPN /\ XV aPN + 1 <= fv_ghi V /\
(fv_ghi V <= 0x10000 \/ 0x55000 <= fv_glo V) /\
4096 <= XV aAREA /\ XV aAREA + 4096 <= alloc_ceiling /\ XV aAREA + 24 <= XV aG /\ XV aG + 40 <= XV aAREA + 4096 /\
(fv_ghi V <= XV aAREA \/ XV aAREA + 4096 <= fv_glo V) /\ (XV aAREA + 4096 <= 0x10000 \/ 0x55000 <= XV aAREA) /\
alloc_ceiling + 8256 <= XV aSP < 2 ^ 63 /\ CEIL_MIN <= alloc_ceiling <= CEIL_MAX /\
src0_D_size_classes <= XV aTQ <= src0_D_size_classes + 94 /\
XV aEND = XV aP + avail_of am fr /\ XV aN = n /\ 0 <= n /\ avail_of am fr < 2 ^ 20 /\ XV aNPN = XV aP + n /\
XV aP = ptr_addr L (frame_ptr am idx fr) /\ XV aEND = ptr_addr L (slot_end am idx) /\ XV aSP = spZ regs.
Proof using HC.
pose proof (HX FPS) as FP. pose proof (lin_facts _ _ _ _ FP) as LF. cbn zeta in LF. unfold CEIL in LF.
pose proof (sx_pre _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & _ & _ & Hceil & Hsp63 & _).
unfold REALLOC_STACK, ALLOC_STACK in Hceil.
pose proof alloc_ceiling_val as ACV.
pose proof (HX XS_P) as XP. pose proof (HX XS_N) as XN.
pose proof (sx_sc _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hsc. pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn.
pose proof (HX P_range) as (_ & _ & _ & _ & Poff & _ & Pst).
pose proof (sx_idx _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hidx.
pose proof (inv_groups (HX HWS) g am (sx_used _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & _ & Gcl & _).
assert (Hav : avail_of am fr < 2 ^ 20).
{ destruct Gcl as [(C63 & _) | (_ & _ & _ & Cb)]; [lia|].
assert (stride_of am <= stride_of am * (am_last am + 1)) by nia. unfold avail_of, IB, UNIT. lia. }
assert (EE : ptr_addr L (slot_end am idx) = ptr_addr L (frame_ptr am idx fr) + avail_of am fr).
{ unfold slot_end, frame_ptr, avail_of. rewrite !ptr_addr_padd'. lia. }
change (XV aP) with (fv_p V) in XP |- *.
change (XV aMEM) with (fv_mem V). change (XV aEND) with (ptr_addr L (slot_end am idx)).
change (fv_end V) with (ptr_addr L (slot_end am idx)) in LF.
change (XV aPN) with (fv_pn V). change (XV aAREA) with (fv_area V). change (XV aG) with (fv_g V).
change (XV aSP) with (fv_sp V). change (spZ regs) with (fv_sp V) in Hceil, Hsp63.
change (XV aTQ) with (TBL + 2 * am_sc am). change (fv_sc V) with (am_sc am) in LF.
change (XV aNPN) with (ptr_addr L (frame_ptr am idx fr) + n). unfold TBL.
repeat split; first [lia | reflexivity].
Qed.
Lemma TABV : 157 <= n < MMAP_THRESHOLD ->
XV aTQ1R = DEBR + dbj_idx (2 ^ t0_e (kkS n)) /\ XV aER = t0_e (kkS n) /\
XV aTQ2R = SCTR + 2 * (4 * t0_e (kkS n) - 3) /\ XV aT1R = znth (4 * t0_e (kkS n) - 3) size_classes /\
XV aTQ3R = SCTR + 2 * t0_i3 (kkS n) /\ XV aT2R = znth (t0_i3 (kkS n)) size_classes /\
3 <= t0_e (kkS n) <= 12 /\ znth (dbj_idx (2 ^ t0_e (kkS n))) DEBRUIJN = t0_e (kkS n) /\
0 <= dbj_idx (2 ^ t0_e (kkS n)) < 32 /\
(t0_i3 (kkS n) = 4 * t0_e (kkS n) - 4 \/ t0_i3 (kkS n) = 4 * t0_e (kkS n) - 2).
Proof using.
intros Hn. destruct (tab_vals n Hn) as (_ & He & Hd & Hj & Hi & Ht).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Ht|].
split; [reflexivity|]. split; [reflexivity|]. exact (conj He (conj Hd (conj Hj Hi))).
Qed.
Lemma OUTm r : Forall (fun x => base_val (EV XV) (r_base x) + r_hi x <= DEBR \/ SCTR + 96 <= base_val (EV XV) (r_base x) + r_lo x)
(head_memS ++ r_mem r).
Proof using HC.
pose proof NUM as NM. pose proof (HX XS) as XSH.
assert (CD : DEBR = 0x10564) by reflexivity. assert (CS : SCTR = 0x10584) by reflexivity.
assert (CC : src0_D_malloc_context = 0x53840) by reflexivity. assert (CL : src0_D_libc = 0x537c8) by reflexivity.
destruct r; cbn [head_memS r_mem app]; repeat (apply Forall_cons || apply Forall_nil);
cbn [r_base r_lo r_hi reg_hdr0 reg_grp reg_meta0 reg_area reg_ctx reg_nl stk1 reg_end1 reg_end5 reg_pn];
rewrite ?(base_val_EV _ XSH); cbn [base_val]; lia.
Qed.
Lemma OUTx nc : (forall b1 ge, nc = NMid b1 ge -> 157 <= n < MMAP_THRESHOLD) ->
Forall (fun x => base_val (EV XV) (r_base x) + r_hi x <= XV aP - 4 \/ fv_ghi V <= base_val (EV XV) (r_base x) + r_lo x)
(keepS ++ tabs_of nc).
Proof using HC.
intros Hm. pose proof NUM as NM. pose proof (HX XS) as XSH.
assert (CD : DEBR = 0x10564) by reflexivity. assert (CS : SCTR = 0x10584) by reflexivity.
assert (CC : src0_D_malloc_context = 0x53840) by reflexivity. assert (CL : src0_D_libc = 0x537c8) by reflexivity.
assert (CT : src0_D_size_classes = 0x10584) by reflexivity.
destruct nc as [| |ge|b1 ge]; cbn [keepS tabs_of tabsR app]; repeat (apply Forall_cons || apply Forall_nil);
cbn [r_base r_lo r_hi reg_grp reg_meta0 reg_area reg_ctx reg_nl stk1 reg_tq R_tq1R R_tq2R R_tq3R];
rewrite ?(base_val_EV _ XSH); cbn [base_val]; try lia.
all: pose proof (TABV (Hm b1 ge eq_refl)) as TT; lia.
Qed.
Theorem mid_st_okS b1 ge ms : nc_ok am fr n (NMid b1 ge) ->
st_ok src0segs (ES L regs g am idx fr a rg n) (SA (kcase_of am) (rcase_of (reserved_of am fr)) (NMid b1 ge)) ms ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - REALLOC_STACK <= x < spZ regs) -> ms_mem ms (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
st_ok src0segs (ES L regs g am idx fr a rg n) (midS (SA (kcase_of am) (rcase_of (reserved_of am fr)) (NMid b1 ge))) ms.
Proof using HC.
intros Hnc HS Hst. destruct Hnc as (Hn & _). unfold ES in *.
pose proof (HX XS) as XSH. pose proof NUM as NM.
pose proof (TABV Hn) as (Q1 & QE & Q2 & QT1 & Q3 & QT2 & He & Hd & Hj & Hi).
assert (CD : DEBR = 0x10564) by reflexivity. assert (CS : SCTR = 0x10584) by reflexivity.
destruct (SA_shape_mid (kcase_of am) (rcase_of (reserved_of am fr)) b1 ge (HX kc_small)) as (_ & _ & Hm & _).
destruct HS as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
rewrite Hm in F8. destruct F8 as (_ & ROK & PD).
assert (XF : forall x, DEBR <= x < SCTR + 96 -> ms_mem ms (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx. apply Hst; unfold REALLOC_STACK, ALLOC_STACK; lia. }
pose proof (mc_statics _ _ _ _ _ (HX MS)) as ST.
assert (TOK : Forall (region_ok src0segs (EV XV) (ms_mem ms)) tabsR).
{ unfold tabsR. repeat (apply Forall_cons || apply Forall_nil);
(apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_tq1R R_tq2R R_tq3R]; rewrite (base_val_EV _ XSH);
[lia | lia | intros o Ho; lia |]); (apply Forall_cons; [|apply Forall_nil]).
- eapply (chunk_ok_val XV _ _ _ 1); [apply (U_off0 XV XSH) | rewrite QE; change (2 ^ (8 * Z.of_N 1)) with 256; lia |].
rewrite Q1, QE, Z.add_0_r. apply (bytes_xfer mem); [intros k Hk; apply XF; cbn in Hk; lia|].
pose proof (YN1y_cf.deb_byte mem ST (dbj_idx (2 ^ t0_e (kkS n))) Hj) as DB. rewrite Hd in DB. exact DB.
- eapply (chunk_ok_val XV _ _ _ 2); [apply (U_off0 XV XSH) | rewrite QT1; pose proof (znth_sc_range (4 * t0_e (kkS n) - 3)); change (2 ^ (8 * Z.of_N 2)) with 65536; lia |].
rewrite Q2, QT1, Z.add_0_r. apply (bytes_xfer mem); [intros k Hk; apply XF; cbn in Hk; lia|].
apply (YN1y_cf.sct_bytes mem ST). lia.
- eapply (chunk_ok_val XV _ _ _ 2); [apply (U_off0 XV XSH) | rewrite QT2; pose proof (znth_sc_range (t0_i3 (kkS n))); change (2 ^ (8 * Z.of_N 2)) with 65536; lia |].
rewrite Q3, QT2, Z.add_0_r. apply (bytes_xfer mem); [intros k Hk; apply XF; cbn in Hk; lia|].
apply (YN1y_cf.sct_bytes mem ST). lia. }
assert (TPD : pairwise_disjoint (EV XV) tabsR).
{ unfold tabsR. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [r_base r_lo r_hi R_tq1R R_tq2R R_tq3R]. rewrite !(base_val_EV _ XSH).
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia. }
assert (TR : forall y, In y tabsR -> DEBR <= base_val (EV XV) (r_base y) + r_lo y /\ base_val (EV XV) (r_base y) + r_hi y <= SCTR + 96).
{ intros y Hy. unfold tabsR in Hy. destruct Hy as [<-|[<-|[<-|[]]]]; cbn [r_base r_lo r_hi R_tq1R R_tq2R R_tq3R];
rewrite (base_val_EV _ XSH); lia. }
unfold st_ok, midS. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts]. rewrite Hm, drop_mid.
do 7 (split; [assumption|]). split; [|exact F9].
split; [apply wf_mid|]. split.
- apply Forall_app. split; [exact (Forall_rm _ _ _ _ ROK) | exact TOK].
- apply pairwise_disjoint_app; [exact (pd_rm _ _ _ _ PD) | exact TPD |].
intros y Hy. pose proof (OUTm (rcase_of (reserved_of am fr))) as O. rewrite Forall_forall in O |- *. intros x Hx.
apply (ext_sep _ x y DEBR (SCTR + 96) (O x Hx)); [exact (proj1 (TR y Hy)) | exact (proj2 (TR y Hy))].
Qed.
Theorem exit_st_okS nc t ms : nc_ok am fr n nc -> (nc = NSmall true \/ exists b1, nc = NMid b1 true) ->
t = rcase_of (avail_of am fr - n) ->
(forall x, ptr_addr L (frame_ptr am idx fr) - 4 <= x <= ptr_addr L (slot_end am idx) -> writable_at src0segs mem x) ->
st_ok src0segs (ES L regs g am idx fr a rg n) (SIP (kcase_of am) (rcase_of (reserved_of am fr)) nc) ms ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - REALLOC_STACK <= x < spZ regs) -> ms_mem ms (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
st_ok src0segs (ES L regs g am idx fr a rg n) (exitS (SIP (kcase_of am) (rcase_of (reserved_of am fr)) nc) t) ms.
Proof using HC.
intros Hnc Hcase Ht Hw HS Hst. unfold ES in *.
pose proof (HX XS) as XSH. pose proof NUM as NM.
assert (Hna : n <= avail_of am fr) by (destruct Hcase as [->|[b1 ->]]; cbn [nc_ok] in Hnc; tauto).
assert (HM : forall b1 ge, nc = NMid b1 ge -> 157 <= n < MMAP_THRESHOLD) by (intros b1 ge ->; cbn [nc_ok] in Hnc; tauto).
destruct (SI_shape (kcase_of am) (rcase_of (reserved_of am fr)) nc (HX kc_small) Hcase) as (_ & _ & Hm).
destruct HS as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
rewrite Hm in F8.
assert (KP : Forall (region_ok src0segs (EV XV) (ms_mem ms)) (keepS ++ tabs_of nc) /\ pairwise_disjoint (EV XV) (keepS ++ tabs_of nc) /\
region_ok src0segs (EV XV) (ms_mem ms) reg_hdr0).
{ destruct F8 as (_ & ROK & PD). destruct Hcase as [-> | [b1 ->]].
- change (mem_at (rcase_of (reserved_of am fr)) (NSmall true)) with (reg_hdr0 :: ((keepS ++ [reg_tq]) ++ r_mem (rcase_of (reserved_of am fr)))) in ROK, PD.
destruct (fa_cons_inv _ _ _ ROK) as [RH ROK1]. apply Forall_app in ROK1 as [ROK1 _]. destruct PD as [_ PD].
split; [exact ROK1|]. split; [exact (pd_app_l _ _ _ PD) | exact RH].
- change (mem_at (rcase_of (reserved_of am fr)) (NMid b1 true)) with (reg_hdr0 :: (keepS ++ r_mem (rcase_of (reserved_of am fr)) ++ tabsR)) in ROK, PD.
destruct (fa_cons_inv _ _ _ ROK) as [RH ROK1]. destruct PD as [_ PD].
split; [exact (Forall_rm _ _ _ _ ROK1)|]. split; [exact (pd_rm _ _ _ _ PD) | exact RH]. }
destruct KP as (KROK & KPD & RH0).
assert (WR : forall x, XV aP - 4 <= x <= XV aEND -> writable_at src0segs (ms_mem ms) x).
{ intros x Hx. apply (proj1 (proj2 (YW04_cf.same_views src0segs mem (ms_mem ms) x (Hst x ltac:(lia) ltac:(unfold REALLOC_STACK, ALLOC_STACK; lia))))).
apply Hw. lia. }
assert (RH : region_ok src0segs (EV XV) (ms_mem ms) reg_hdr).
{ destruct RH0 as (H1 & H2 & _ & H4). apply region_ok_intro; [exact H1 | exact H2 | | exact H4].
cbn [r_base r_wlo r_whi reg_hdr]. intros o Ho. rewrite (base_val_EV _ XSH). apply WR. lia. }
assert (TOK : Forall (region_ok src0segs (EV XV) (ms_mem ms)) (t_memS t)).
{ assert (RN : 1 <= avail_of am fr - n -> region_ok src0segs (EV XV) (ms_mem ms) reg_npn).
{ intros H1. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_npn];
rewrite (base_val_EV _ XSH); [lia | lia | intros o Ho; apply WR; lia | apply Forall_nil]. }
assert (R5 : 5 <= avail_of am fr - n -> region_ok src0segs (EV XV) (ms_mem ms) reg_end5w).
{ intros H1. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_end5w];
rewrite (base_val_EV _ XSH); [lia | lia | intros o Ho; apply WR; lia | apply Forall_nil]. }
rewrite Ht. destruct (rc_cases (avail_of am fr - n) ltac:(lia)) as [[R E0]|[[R E0]|[[R E0]|[R E0]]]]; rewrite E0;
cbn [t_memS]; repeat (apply Forall_cons || apply Forall_nil); first [apply RN | apply R5]; lia. }
assert (PDN : pairwise_disjoint (EV XV) (reg_hdr :: t_memS t)).
{ rewrite Ht. destruct (rc_cases (avail_of am fr - n) ltac:(lia)) as [[R E0]|[[R E0]|[[R E0]|[R E0]]]]; rewrite E0;
cbn [t_memS pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi reg_hdr reg_npn reg_end5w];
rewrite ?(base_val_EV _ XSH); repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia. }
assert (NEWR : forall y, In y (reg_hdr :: t_memS t) ->
XV aP - 4 <= base_val (EV XV) (r_base y) + r_lo y /\ base_val (EV XV) (r_base y) + r_hi y <= fv_ghi V).
{ rewrite Ht. intros y Hy. destruct (rc_cases (avail_of am fr - n) ltac:(lia)) as [[R E0]|[[R E0]|[[R E0]|[R E0]]]]; rewrite E0 in Hy;
cbn [t_memS In] in Hy;
repeat (destruct Hy as [<-|Hy]; [cbn [r_base r_lo r_hi reg_hdr reg_npn reg_end5w]; rewrite (base_val_EV _ XSH); lia|]); destruct Hy. }
assert (WV : bv_unsigned (sv_denot (EV XV) WRSVR) = avail_of am fr - n).
{ change (sv_denot (EV XV) WRSVR) with (sext 64 (alu32 ALU_SUB (low32 (sv_denot (EV XV) (SOff aEND 0))) (low32 (sv_denot (EV XV) (SOff aNPN 0))))).
rewrite subw_rr_unsigned, !(U_off0 _ XSH), subw_small by lia. lia. }
assert (PN1 : forall z, bv_unsigned (sv_denot (EV XV) (SOff aEND z)) = XV aEND + z -> XV aP + n = XV aEND + z ->
sv_denot (EV XV) PNX = sv_denot (EV XV) (SOff aEND z)).
{ intros z Hz Hpz. apply (proj2 (word_eq _ _)). unfold PNX.
change (sv_denot (EV XV) (SAlu ALU_ADD (SOff aP 0) (SOff aN 0))) with (alu64 ALU_ADD (sv_denot (EV XV) (SOff aP 0)) (sv_denot (EV XV) (SOff aN 0))).
rewrite alu64_add, !(U_off0 _ XSH), Hz. unfold add64. rewrite Z.mod_small by lia. lia. }
unfold st_ok, exitS. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts]. rewrite Hm, drop_exit.
do 7 (split; [assumption|]). split.
- split; [apply wf_exit|]. split.
+ apply Forall_app. split; [exact KROK | apply Forall_cons; [exact RH | exact TOK]].
+ apply pairwise_disjoint_app; [exact KPD | exact PDN |].
intros y Hy. pose proof (OUTx nc HM) as O. rewrite Forall_forall in O |- *. intros x Hx.
apply (ext_sep _ x y (XV aP - 4) (fv_ghi V) (O x Hx)); [exact (proj1 (NEWR y Hy)) | exact (proj2 (NEWR y Hy))].
- destruct F9 as (FA & FC & FL). unfold facts_app. split; [|split]; cbn [f_atoms f_conds f_alias].
+ apply atoms_ok_app; [|exact FA]. rewrite Ht.
destruct (rc_cases (avail_of am fr - n) ltac:(lia)) as [[R E0]|[[R E0]|[[R E0]|[R E0]]]]; rewrite E0;
cbn [t_atomsS atoms_ok]; try exact I; (split; [|exact I]); unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite (ew_EV _ XSH); change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia.
+ apply conds_ok_app; [|exact FC]. rewrite Ht.
destruct (rc_cases (avail_of am fr - n) ltac:(lia)) as [[R E0]|[[R E0]|[[R E0]|[R E0]]]]; rewrite E0;
cbn [t_condsS conds_ok]; try exact I; (split; [|split; [|exact I]]); unfold acond_ok; cbn [ac_c ac_a ac_b].
* rewrite branch_ne, WV. cbn [sv_denot]. rewrite lit64_small by lia. apply negb_true_iff, Z.eqb_neq. lia.
* rewrite branch_lt, WV. cbn [sv_denot]. rewrite lit64_small by lia. rewrite !s64_small by lia. apply Z.ltb_lt. lia.
* rewrite branch_ne, WV. cbn [sv_denot]. rewrite lit64_small by lia. apply negb_true_iff, Z.eqb_neq. lia.
* rewrite branch_ge, WV. cbn [sv_denot]. rewrite lit64_small by lia. rewrite !s64_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
+ apply alias_ok_app; [|exact FL]. rewrite Ht.
assert (AL2 : 1 <= avail_of am fr - n ->
sv_denot (EV XV) (SAlu ALU_ADD (SOff aEND 0) (SAluw ALU_SUB (SLit 0) WRSVR)) = sv_denot (EV XV) (SOff aNPN 0)).
{ intros H1. apply (proj2 (word_eq _ _)).
change (sv_denot (EV XV) (SAlu ALU_ADD (SOff aEND 0) (SAluw ALU_SUB (SLit 0) WRSVR))) with
(alu64 ALU_ADD (sv_denot (EV XV) (SOff aEND 0)) (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (sv_denot (EV XV) WRSVR))))).
rewrite alu64_add, negw_unsigned, WV, !(U_off0 _ XSH). unfold negw. rewrite sx32_neg_small by lia.
unfold add64. apply mod64_shift; lia. }
assert (AL1 : sv_denot (EV XV) PNX = sv_denot (EV XV) (SOff aNPN 0)).
{ apply (proj2 (word_eq _ _)). unfold PNX.
change (sv_denot (EV XV) (SAlu ALU_ADD (SOff aP 0) (SOff aN 0))) with (alu64 ALU_ADD (sv_denot (EV XV) (SOff aP 0)) (sv_denot (EV XV) (SOff aN 0))).
rewrite alu64_add, !(U_off0 _ XSH). unfold add64. rewrite Z.mod_small by lia. lia. }
destruct (rc_cases (avail_of am fr - n) ltac:(lia)) as [[R E0]|[[R E0]|[[R E0]|[R E0]]]]; rewrite E0;
cbn [t_aliasS alias_ok].
* split; [|exact I]. apply PN1; [apply (U_off _ XSH); lia | lia].
* split; [exact AL1|]. split; [apply AL2; lia | exact I].
* split; [|exact I]. apply PN1; [apply (U_off _ XSH); lia | lia].
* split; [exact AL1|]. split; [apply AL2; lia | exact I].
Qed.
End b.
End a.
