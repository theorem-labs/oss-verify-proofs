(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB12 AB1h AB13 AB01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b YG0g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YD1h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1g AD2i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Lemma tfib_img_covered : img_covered_b TSEGS TFIB_IMG = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_img_segs_b : forallb (fun sg => (fst TFIB_IMG <=? Z.of_N (seg_base sg)) && (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst TFIB_IMG + snd TFIB_IMG))%bool TSEGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_img_segs : forall sg, In sg TSEGS -> fst TFIB_IMG <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst TFIB_IMG + snd TFIB_IMG.
Proof.
intros sg Hsg. pose proof (proj1 (forallb_forall _ _) tfib_img_segs_b sg Hsg) as X. cbn beta in X.
apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. exact (conj X1 X2).
Qed.
Definition AVIS13 : list (expr * expr) :=
[ (epg 518, ELit 4096); (epg 501, ELit 8388608); (epg 500, ELit 1048576); (epg 424, ELit 11571200); (epg 357, ELit 4096);
(epg 292, ELit 4096); (epg 275, ELit 65536); (epg 274, ELit 4096); RINFO_P; (epg 254, ELit 3727360); (epg 109, ELit 65536); IMG_P; STK_P ].
Definition avis_chk (ch : acs) : bool :=
forallb (fun p => existsb (pair_eqb p) AVIS13 || existsb (sub_of_map p) (musl_maps ch))%bool (a_vis ch).
Definition kz_chk (ch : acs) : bool :=
(kn_zero ch (EMd M_MUL (ELit 512) (EVar 501)) 2147450880 1048576
&& kn_zero ch (EMd M_MUL (ELit 512) (EVar 500)) 2147450880 131072
&& kn_zero ch (EMd M_MUL (ELit 512) (EVar 424)) 2147450880 1446400)%bool.
Lemma tfib_holes_chkB : forallb (fun ch => avis_chk ch && kz_chk ch)%bool HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Section f. Context {fx : YK11.FPState}.
Section g.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk argv envp uid hw) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation HID := (hid TFIB TOP argH E ch model).
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation V n := (bv_unsigned (ev E n)).
#[local] Notation vm := (vm_maps (m_vmmaps model)).
Context {rc : YM05.RunCeil}.
Hypothesis Hceil : YM05.ceil_of_top (usp - stack_max_size).
#[local] Notation ly0 := (AD1g.ly0 ch E model).
#[local] Notation rdS := (AD1g.rdS sp rdraw inp ch E FULL model).
#[local] Notation HS0 := (AD1g.HS0 sp rdraw inp ch E model).
Ltac inst H := try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H h); try specialize (H ch);
try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC);
try specialize (H HE); try specialize (H HM); try specialize (H rc); try specialize (H Hceil).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
#[local] Definition dm_vals := ltac:(get @AD1g.dm_vals).
#[local] Definition band_vals := ltac:(get @AD1g.band_vals).
#[local] Definition vm_shape := ltac:(get @AD1g.vm_shape).
#[local] Definition vm_bound := ltac:(get @AD1g.vm_bound).
#[local] Definition vm_In' := ltac:(get @AD1g.vm_In').
#[local] Definition vm_eq := ltac:(get @AD1g.vm_eq).
#[local] Definition vm_nth := ltac:(get @AD1g.vm_nth). #[local] Definition nth_ALLMAPS_tail := ltac:(get @AD1g.nth_ALLMAPS_tail). #[local] Definition vm_split := ltac:(get @AD1g.vm_split).
#[local] Definition extra_In := ltac:(get @AD1g.extra_In).
#[local] Definition extra_facts := ltac:(get @AD1g.extra_facts).
#[local] Definition statics_eq := ltac:(get @AD1g.statics_eq).
#[local] Definition tfib_layout_ok := ltac:(get @AD1g.tfib_layout_ok).
#[local] Definition tfib_ARm := ltac:(get @AD1g.tfib_ARm).
#[local] Definition tfib_hole_maps := ltac:(get @AD1g.tfib_hole_maps).
#[local] Definition hole_facts := ltac:(get @AD1g.hole_facts).
#[local] Definition tfib_hole_ghost := ltac:(get @AD1g.tfib_hole_ghost). #[local] Definition tfib_hole_ghostdisj := ltac:(get @AD1g.tfib_hole_ghostdisj).
#[local] Definition tfib_band_not_ghost := ltac:(get @AD1g.tfib_band_not_ghost).
#[local] Definition tfib_hole_stk := ltac:(get @AD1g.tfib_hole_stk). #[local] Definition tfib_hole_avis := ltac:(get @AD1g.tfib_hole_avis).
#[local] Definition uP := ltac:(get @AD1g.uP).   #[local] Definition uQ := ltac:(get @AD1g.uQ).   #[local] Definition uT := ltac:(get @AD1g.uT).   #[local] Definition uC := ltac:(get @AD1g.uC).
#[local] Definition uD := ltac:(get @AD1g.uD).   #[local] Definition uF := ltac:(get @AD1g.uF).   #[local] Definition uNB := ltac:(get @AD1g.uNB). #[local] Definition uSB := ltac:(get @AD1g.uSB).
#[local] Definition uGV := ltac:(get @AD1g.uGV). #[local] Definition uSp := ltac:(get @AD1g.uSp). #[local] Definition uSp1 := ltac:(get @AD1g.uSp1). #[local] Definition uTop := ltac:(get @AD1g.uTop).
#[local] Definition uS0 := ltac:(get @AD1g.uS0). #[local] Definition uTopRel := ltac:(get @AD1g.uTopRel). #[local] Definition usp_range := ltac:(get @AD1g.usp_range).
#[local] Definition ceil_le_TOP := ltac:(get @AD1g.ceil_le_TOP). #[local] Definition ceil_ge_TOP := ltac:(get @AD1g.ceil_ge_TOP). #[local] Definition ceil_of_top := ltac:(get @AD1g.ceil_of_top).
#[local] Definition HS0_sub := ltac:(get @AD1g.HS0_sub). #[local] Definition HS0_off := ltac:(get @AD1g.HS0_off). #[local] Definition RDX := ltac:(get @AD1g.RDX).
#[local] Definition sliver_hid := ltac:(get @AD1g.sliver_hid). #[local] Definition sliver_zero := ltac:(get @AD1g.sliver_zero).
#[local] Definition sliver_allowed := ltac:(get @AD1g.sliver_allowed). #[local] Definition sliver_where := ltac:(get @AD1g.sliver_where).
#[local] Definition VZ_facts := ltac:(get @AD1g.VZ_facts).
#[local] Definition Hseps := ho_seps TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
#[local] Ltac vin := apply vm_In'; cbn; tauto.
Lemma wiv_wzp : forall d, wiv (wzp d) = d.
Proof. intros [a b]. unfold wiv, wzp, w64. cbn [fst snd]. rewrite !Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma band_in_maps : forall a, in_band_rw a ->
(bv_unsigned (fst (dLow E)) <= a < bv_unsigned (fst (dLow E)) + bv_unsigned (snd (dLow E)))
\/ (bv_unsigned (fst (dHigh E)) <= a < bv_unsigned (fst (dHigh E)) + bv_unsigned (snd (dHigh E))).
Proof.
intros a Ha. pose proof band_vals as (VL & _ & VH). unfold wzp in VL, VH.
apply (f_equal fst) in VL as L1; apply (f_equal snd) in VL as L2. apply (f_equal fst) in VH as Y1; apply (f_equal snd) in VH as Y2.
cbn [fst snd] in L1, L2, Y1, Y2. rewrite L1, L2, Y1, Y2. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
Qed.
Lemma band_facts : forall x : word, in_band_rw (bv_unsigned x) ->
in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ page_in_ranges (page_base x) (m_vm_lazy model) = true /\
in_ivs (bv_unsigned x) vm = true.
Proof.
intros x Hx. pose proof (ho_kinds TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) as K. rewrite tfib_hole_maps in K.
assert (KD : forall m, In m TFIB_TAIL12 -> am_kind m = KRWLAZY ->
bv_unsigned (fst (dmm E m)) <= bv_unsigned x < bv_unsigned (fst (dmm E m)) + bv_unsigned (snd (dmm E m)) ->
in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ page_in_ranges (page_base x) (m_vm_lazy model) = true).
{ intros m Hm Hk Hr. apply (proj1 (Forall_forall _ _) K m); [apply in_app_iff; right; apply in_app_iff; right; exact Hm | exact Hk | exact Hr]. }
assert (IN : forall d, In d vm -> bv_unsigned (fst d) <= bv_unsigned x < bv_unsigned (fst d) + bv_unsigned (snd d) -> in_ivs (bv_unsigned x) vm = true).
{ intros d Hd Hr. unfold in_ivs. apply existsb_exists. exists d. split; [exact Hd|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
destruct (band_in_maps (bv_unsigned x) Hx) as [R0|R0].
- destruct (KD (mk (ELit 2147446784) 268435456 KRWLAZY) ltac:(cbn; tauto) eq_refl R0) as [A1 A2]. split; [exact A1|]. split; [exact A2|]. apply (IN (dLow E)); [vin | exact R0].
- destruct (KD (mk (ELit 2201439137792) 15392894357504 KRWLAZY) ltac:(cbn; tauto) eq_refl R0) as [A1 A2]. split; [exact A1|]. split; [exact A2|]. apply (IN (dHigh E)); [vin | exact R0].
Qed.
Theorem tfib_ALedger : ALedger TSEGS ly0 init_state model.
Proof.
pose proof dm_vals as (VP & VQ & VT & VF & VNB & VSB & VLow & VHigh & VGap & VGV & VD & V292 & VC & V254 & V109).
pose proof uP as [_ HPr].
constructor.
-
intros sg Hsg. cbn [ly_img AD1g.ly0]. exact (tfib_img_segs sg Hsg).
- rewrite (ho_limit TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC). unfold ASAN_VM_LMIN, YA02.LIMIT, target_alloc_limit. apply Z.leb_le. vm_compute. reflexivity.
- exact (ho_res TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC).
-
exists [(u eP, kPrimResvSize)]. split.
+ split; [|split].
* constructor; [|constructor]. cbn [fst snd]. unfold kPrimResvSize. split; [lia|]. split; [left; reflexivity | right; left; reflexivity].
* cbn. split; [constructor | exact I].
* intros a Ha. cbn [ly_prim AD1g.ly0] in Ha. split.
-- intros _ (c & hh & _ & Hin & _). rewrite reg_init in Hin. cbn in Hin. destruct Hin.
-- intros _. constructor. unfold in_zr. cbn [fst snd]. exact Ha.
+ intros p. cbn [ly_prim AD1g.ly0]. split.
* intros [<-|[]]. unfold kPrimResvSize. cbn [fst snd]. rewrite <- VP, wiv_wzp. split; [vin|]. lia.
* intros (Hin & Hpos & Hlo & Hhi). destruct p as [pb ps]. cbn [fst snd] in *. left.
assert (HdP : In (dP E) vm) by vin.
unfold kPrimResvSize in Hhi.
assert (Hpb : bv_unsigned (w64 pb) = pb) by (unfold w64; apply u64_lit; lia).
assert (Hps : bv_unsigned (w64 ps) = ps) by (unfold w64; apply u64_lit; lia).
destruct (seps_In_disjoint vm (wiv (pb, ps)) (dP E) Hseps Hin HdP) as [E0|D].
-- apply (f_equal wzp) in E0. rewrite VP in E0. unfold wzp, wiv in E0. cbn [fst snd] in E0. rewrite Hpb, Hps in E0.
injection E0 as E1 E2. unfold kPrimResvSize. rewrite <- E1, <- E2. reflexivity.
-- exfalso. unfold iv_disjoint, wiv in D. cbn [fst snd] in D. rewrite Hpb, Hps in D.
unfold dP in D. rewrite u_fst_dm, u_snd_dm in D by lia. lia.
- cbn [ly_Q AD1g.ly0]. change kPtrArrayResv with 8388608. rewrite <- VQ, wiv_wzp. vin.
- change (wiv (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg)) with (dHigh E). vin.
- intros e He. cbn in He. destruct He.
-
intros e He. unfold lazy_zones. cbn [ly_SB ly_prim ly_Q ly_C ly_extra AD1g.ly0 sec_extents init_state st_chunks flat_map]. rewrite app_nil_r.
assert (SELF : forall z, z = wzp e -> fst z <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst z + snd z)
by (intros z ->; unfold wzp; cbn [fst snd]; lia).
assert (STAT : forall d, In d [dP E; dQ E; dT E; dF E; dNB E; dSB E] -> e = d ->
Exists (fun z => fst z <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst z + snd z)
([(kLowShadowBeg, kLowShadowEnd - kLowShadowBeg); (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg);
(kLowShadowEnd, kHighShadowBeg - kLowShadowEnd); (u eSB, kStoreBlockSize); (u eP, kPrimResvSize); (u eQ, kPtrArrayResv); (u eC, kCtxMapSize)]
++ extra E model ++ static_extents ly0)).
{ intros d Hd ->. apply Exists_exists. exists (wzp d). split; [|apply SELF; reflexivity].
apply in_app_iff. right. apply in_app_iff. right. rewrite statics_eq. apply in_app_iff. left. apply in_map. exact Hd. }
destruct (known E e) eqn:Hk.
+ unfold known in Hk. apply existsb_exists in Hk as (k & HkK & Heq). apply iv_eqb_eq in Heq. subst k.
rewrite KNOWN_eq in HkK.
destruct HkK as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]].
* apply (STAT (dP E)); [cbn; tauto | reflexivity].
* apply (STAT (dQ E)); [cbn; tauto | reflexivity].
* apply (STAT (dT E)); [cbn; tauto | reflexivity].
* apply (STAT (dF E)); [cbn; tauto | reflexivity].
* apply (STAT (dNB E)); [cbn; tauto | reflexivity].
* apply (STAT (dSB E)); [cbn; tauto | reflexivity].
* apply Exists_exists. exists (kLowShadowBeg, kLowShadowEnd - kLowShadowBeg). split; [cbn; tauto|]. apply SELF. rewrite VLow. reflexivity.
* apply Exists_exists. exists (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg). split; [cbn; tauto|]. apply SELF. rewrite VHigh. reflexivity.
* apply Exists_exists. exists (kLowShadowEnd, kHighShadowBeg - kLowShadowEnd). split; [cbn; tauto|]. apply SELF. rewrite VGap. reflexivity.
* apply Exists_exists. exists (u eC, kCtxMapSize). split; [cbn; tauto|]. apply SELF. rewrite VC. reflexivity.
* apply Exists_exists. exists (wzp (dD E)). split; [|apply SELF; reflexivity].
apply in_app_iff. right. apply in_app_iff. right. rewrite statics_eq. apply in_app_iff. right. rewrite VD. cbn [In]. tauto.
+ apply Exists_exists. exists (wzp e). split; [|apply SELF; reflexivity].
apply in_app_iff. right. apply in_app_iff. left. unfold extra. apply in_map. apply List.filter_In. split; [exact He|]. rewrite Hk. reflexivity.
-
pose proof (ho_eager TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) as HEg.
pose proof hole_facts as (_ & _ & _ & _ & _ & _ & _ & _ & HEb & _).
pose proof (esec_nonneg (vm_noaccess (m_vmmaps model)) (m_vm_lazy model) (sec_extents ly0 init_state)) as EN.
replace (prim_committed init_state) with 0 by (vm_compute; reflexivity). cbn [st_sec_reserved init_state]. unfold E_BASE. lia.
-
intros z Hz. unfold perm_maps in Hz. cbn [ly_T ly_F ly_NB ly_SB ly_C ly_D ly_extra AD1g.ly0] in Hz.
apply in_app_iff in Hz as [Hz|Hz].
+ destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
* change kThreadObjSize with 4096. rewrite <- VT, wiv_wzp. vin.
* change kFakeStackSize with 11571200. rewrite <- VF, wiv_wzp. vin.
* change kNodesBlockSize with 1048576. rewrite <- VNB, wiv_wzp. vin.
* change kStoreBlockSize with 8388608. rewrite <- VSB, wiv_wzp. vin.
* change kCtxMapSize with 65536. rewrite <- VC, wiv_wzp. vin.
* rewrite <- VD, wiv_wzp. vin.
+ destruct (extra_In z Hz) as (iv & -> & Hiv & _). rewrite wiv_wzp. exact Hiv.
-
intros z Hz. unfold band_maps in Hz.
destruct Hz as [<-|[<-|[<-|[]]]].
+ pose proof band_vals as (VL & _ & _). rewrite <- VL at 1. hnf.
change (wiv (kLowShadowBeg, kLowShadowEnd - kLowShadowBeg)) with (dLow E). vin.
+ change (wiv (kLowShadowEnd, kHighShadowBeg - kLowShadowEnd)) with (dGap E). vin.
+ change (wiv (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg)) with (dHigh E). vin.
-   intros e z He _. cbn in He. destruct He.
-   rewrite (ho_top TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC). unfold YA02.TOP. exact ceil_of_top.
-   cbn [ly_img AD1g.ly0]. exact (img_covered_b_ok TSEGS TFIB_IMG tfib_img_covered).
-
apply YG0g.shna_of_uncovered.
+ intros q Hq. exact (proj1 (Forall_forall _ _) (ho_napos TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) q Hq).
+ intros x Hx.
assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hx; lia).
pose proof (band_facts (Z_to_bv 64 x)) as BF. rewrite Z_to_bv_unsigned, bv_wrap_small in BF by (change (bv_modulus 64) with (2 ^ 64); lia).
exact (proj1 (BF Hx)).
Qed.
Definition W0 : world TSEGS := AD2i.W1 sp rdraw inp Hsp Hva ch E model.
Lemma W0_H : w_H W0 = AD2i.H1 sp rdraw inp ch E model.   Proof. reflexivity. Qed.
Lemma W0_A : w_A W0 = allowA TFIB E ch.   Proof. reflexivity. Qed.
Theorem tfib_AI : AI TSEGS (w_H W0) (w_A W0) model.
Proof. pose proof (@AD2i.AI_main) as L. inst L. exact (L sliver_allowed). Qed.
Lemma H1_sub_HS0 : hsub (AD2i.H1 sp rdraw inp ch E model) HS0.
Proof.
intros a Ha. unfold AD2i.H1 in Ha. unfold AD1g.HS0.
apply andb_prop in Ha as [Ha Hs]. apply andb_prop in Ha as [Hh _]. rewrite Hh, Hs. reflexivity.
Qed.
Lemma rdW_ext : rd_ext rdS (aview TSEGS (w_H W0) FULL).
Proof. rewrite W0_H. unfold AD1g.rdS. apply YG0n.aview_ext; [exact HS0_off | exact H1_sub_HS0]. Qed.
Lemma tfib_abudget : abudget_ok TSEGS ly0 init_state W0.
Proof.
split; [| apply asecA_nil; reflexivity].
rewrite W0_A. unfold abudget, A_BASE, sec_hulls. cbn [st_nev init_state sec_live_bytes st_chunks st_secs fold_right]  .
pose proof (ho_abytes TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) as HA.
pose proof hole_facts as (_ & _ & _ & _ & _ & _ & _ & HAb & _). lia.
Qed.
Lemma tfib_amwf : amwf model.
Proof.
split.
- apply (proj2 (amwf_MWF model)). split.
+ exact (ho_wf TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC).
+ exact Hseps.
-   intros q Hq. exact (proj1 (vm_bound q Hq)).
Qed.
Lemma band_not_ghost : forall a, in_band_rw a -> in_ghost E ch a = false.
Proof.
intros a Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha.
apply tfib_band_not_ghost. lia.
Qed.
Lemma band_hidden_zero : forall a : word, in_band_rw (bv_unsigned a) -> HID a = true -> FULL a = Some (Z_to_bv 8 0).
Proof.
intros a Ha Hh. destruct (band_facts a Ha) as (Hna & Hlz & Hm).
exact (ho_zero TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC a Hh Hm Hna Hlz (band_not_ghost _ Ha)).
Qed.
Lemma MR_full : forall (a : word) b, MR a = Some b -> FULL a = Some b.
Proof. intros a b H. unfold Mr, mrestrict in H. destruct (HID a); [discriminate H | exact H]. Qed.
Lemma CHKB : avis_chk ch = true /\ kz_chk ch = true.
Proof.
pose proof (proj1 (forallb_forall _ _) tfib_holes_chkB ch (HS_tfib_In h ch Hch)) as H. cbn beta in H.
apply andb_prop in H as [H1 H2]. exact (conj H1 H2).
Qed.
Lemma avis_cases : forall p, In p (a_vis ch) -> In p AVIS13 \/ exists m, In m (musl_maps ch) /\ sub_of_map p m = true.
Proof.
intros p Hp. pose proof (proj1 (forallb_forall _ _) (proj1 CHKB) p Hp) as H. cbn beta in H. apply orb_prop in H as [H|H].
- left. apply existsb_exists in H as (q & Hq & He). apply pair_eqb_eq in He. subst q. exact Hq.
- right. apply existsb_exists in H as (m & Hm & Hs). exists m. exact (conj Hm Hs).
Qed.
Lemma kz_facts : kn_zero ch (EMd M_MUL (ELit 512) (EVar 501)) 2147450880 1048576 = true
/\ kn_zero ch (EMd M_MUL (ELit 512) (EVar 500)) 2147450880 131072 = true
/\ kn_zero ch (EMd M_MUL (ELit 512) (EVar 424)) 2147450880 1446400 = true.
Proof.
pose proof (proj2 CHKB) as H. unfold kz_chk in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. exact (conj H1 (conj H2 H3)).
Qed.
Lemma musl_extra : forall m, In m (musl_maps ch) -> In (wzp (dmm E m)) (extra E model).
Proof.
intros m Hm. pose proof hole_facts as (_ & _ & MOK & _).
destruct (musl_map_sound ch m (proj1 (Forall_forall _ _) MOK m Hm)) as (v & n & o & Hb & Hl & Hn & Hr & Ho).
apply In_nth_error in Hm as (j & Hj).
assert (Hjl : (j < length (musl_maps ch))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
assert (HA : nth_error (ALLMAPS ch) (3 + j) = Some m).
{ unfold ALLMAPS. rewrite nth_error_app2 by (cbn; lia). change (length TFIB_HEAD3) with 3%nat.
rewrite nth_error_app1 by lia. replace (3 + j - 3)%nat with j by lia. exact Hj. }
pose proof (vm_nth _ _ HA) as Hvm.
unfold extra. apply in_map. apply List.filter_In. split; [exact (nth_error_In _ _ Hvm)|].
destruct (known E (dmm E m)) eqn:Hk; [|reflexivity]. exfalso.
unfold known in Hk. apply existsb_exists in Hk as (k & HkK & Heq). apply iv_eqb_eq in Heq.
assert (LEN : bv_unsigned (snd (dmm E m)) = n) by (unfold dmm, amap_den; cbn [snd]; rewrite Hl; cbn [edenot]; apply u64_lit; lia).
pose proof dm_vals as (VP & VQ & VT & VF & VNB & VSB & VLow & VHigh & VGap & VGV & VD & V292 & VC & V254 & V109).
assert (LENK : forall d z, wzp d = z -> bv_unsigned (snd d) = snd z) by (intros d z <-; reflexivity).
rewrite KNOWN_eq in HkK.
assert (POS : forall i d, nth_error TFIB_TAIL12 i = Some (match i with 4%nat => mk eT 4096 KRW | _ => mk eD 4096 KRW end) -> (i = 4 \/ i = 1)%nat ->
dmm E m = d -> nth_error vm (3 + length (musl_maps ch) + i) = Some d -> False).
{ intros i d _ _ Ed Hi. pose proof (seps_pair _ Hseps (3 + j) (3 + length (musl_maps ch) + i) _ _ ltac:(lia) Hvm Hi) as D.
rewrite Ed in D. unfold iv_disjoint in D. pose proof (vm_bound d (nth_error_In _ _ Hi)) as (P0 & _). lia. }
destruct HkK as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
try (pose proof (LENK _ _ VP); pose proof (LENK _ _ VQ); pose proof (LENK _ _ VF); pose proof (LENK _ _ VNB); pose proof (LENK _ _ VSB);
pose proof (LENK _ _ VLow); pose proof (LENK _ _ VHigh); pose proof (LENK _ _ VGap); pose proof (LENK _ _ VC);
cbn [snd] in *; rewrite Heq in LEN; lia).
-   apply (POS 4%nat (dT E) eq_refl ltac:(lia) Heq). exact (vm_nth _ _ (nth_ALLMAPS_tail 4 _ eq_refl)).
-   apply (POS 1%nat (dD E) eq_refl ltac:(lia) Heq). exact (vm_nth _ _ (nth_ALLMAPS_tail 1 _ eq_refl)).
Qed.
End g.
End f.
