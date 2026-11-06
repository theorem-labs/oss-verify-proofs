(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull HeapIfaceAEx ShadowRLawsB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sj_div8_lt x y : x < y -> y mod 8 = 0 -> x / 8 < y / 8.
Proof.
  intros Hxy Hy. pose proof (Z.div_mod y 8 ltac:(lia)) as D. rewrite Hy, Z.add_0_r in D.
  apply Z.div_lt_upper_bound; lia.
Qed.
Lemma sj_S_mono x y : x <= y -> HeapIfaceA.S x <= HeapIfaceA.S y.
Proof. intros H. unfold HeapIfaceA.S. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.
Lemma sj_S_range x : 0 <= x < 2 ^ 47 -> SB <= HeapIfaceA.S x < BIGSHADOW_HI.
Proof.
  intros H. unfold HeapIfaceA.S, BIGSHADOW_HI, SB in *. split.
  - pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
  - assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma sj_mod8_of16 u : u mod 16 = 0 -> u mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod u 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (16 * (u / 16)) with ((2 * (u / 16)) * 8) by ring. apply Z_mod_mult.
Qed.
Lemma sj_ffbytes_mod8 k : In k [0; 1; 2; 3; 4; 5] -> ff_bytes k mod 8 = 0 /\ 64 <= ff_bytes k.
Proof. intros Hk. unfold ff_bytes. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; lia. Qed.
Lemma sj_frame_mod8 F k : In k [0; 1; 2; 3; 4; 5] -> F mod ff_bytes k = 0 -> F mod 8 = 0.
Proof.
  intros Hk HF. pose proof (sj_ffbytes_mod8 k Hk) as (K8 & K64).
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (ff_bytes k)); apply Z.mod_divide; lia.
Qed.

Lemma sj_sfilter_In : forall (A : Type) (P : A -> Prop) (D : forall x, Decision (P x)) (l : list A) x, In x (filter P l) <-> P x /\ In x l.
Proof.
  induction l as [|a l IH]; intros x; [cbn; tauto|]. rewrite list_basics.list.filter_cons. destruct (decide (P a)) as [Y | N]; cbn [In]; rewrite IH.
  - split; [intros [<- | H]; tauto | intros (Hp & [-> | H]); tauto].
  - split; [tauto | intros (Hp & [-> | H]); tauto].
Qed.
Lemma sj_lb_remove_in u (LB : list (Z * Z)) b : In b (lb_remove u LB) -> In b LB.
Proof.
  induction LB as [|b0 LB IH]; cbn [lb_remove]; [intros []|].
  destruct (Z.eqb (fst b0) u); [intros H; right; exact H|]. intros [E|H]; [left; exact E|right; exact (IH H)].
Qed.
Lemma sj_ff_remove_in F (FF : list fframe) f : In f (ff_remove F FF) -> In f FF.
Proof.
  induction FF as [|f0 FF IH]; cbn [ff_remove]; [intros []|].
  destruct (Z.eqb (ff_addr f0) F); [intros H; right; exact H|]. intros [E|H]; [left; exact E|right; exact (IH H)].
Qed.

Section Strict.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable HIR : asan_iface.

Definition rt_flag_in_fs : Prop :=
  forall LB FF LK cr A M V F k rs fl,
    ri_inv HIR LB FF LK cr A M V -> In (F, k, rs) FF -> cell_is (hl_segs L) M (F + ff_bytes k - 8) 8 fl -> 0 <= fl < 2 ^ 64 ->
    ar_fs ar <= fl < ar_fs ar + FS_BYTES.

Hypothesis IMG : hl_img_hi L <= BIGSHADOW_LO.
Hypothesis FLAG : rt_flag_in_fs.
Hypothesis OK : HAJ.asan_iface_okR L ar C scfg HIR.

#[local] Abbreviation HIS := (HAJ.strict_of HIR).
Definition sj_cls (FF LK : list fframe) : Prop := Forall (fun f => In (ff_class f) [1; 2; 3]) (FF ++ LK).

Definition sj_wf (LB : list (Z * Z)) (FF LK : list fframe) : Prop :=
  (forall b, In b LB -> ablock_range L ar (fst b) (snd b) /\ fframes_apart (fst b) (snd b) (FF ++ LK))
  /\ (forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                     /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) [0; 1; 2; 3; 4; 5])
  /\ app_mem (ar_fs ar) FS_BYTES
  /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\ ar_sptop ar mod 16 = 0.

#[using="OK"] Lemma sj_wf_of : forall LB FF LK cr A M V, ri_inv HIR LB FF LK cr A M V -> sj_wf LB FF LK.
Proof.
  intros LB FF LK cr A M V RI. destruct (HAJ.aior_wf _ _ _ _ _ OK LB FF LK cr A M V RI) as (WB & WF & W3 & _ & _ & _ & _ & _ & (_ & _ & W9 & W10) & _).
  split; [|split; [|split; [exact W3|exact (conj W9 W10)]]].
  - intros b Hb. destruct (WB b Hb) as (B1 & _ & _ & _ & _ & B6 & _). exact (conj B1 B6).
  - intros f Hf. destruct (WF f Hf) as (F1 & F2 & F3 & F4 & _). exact (conj F1 (conj F2 (conj F3 F4))).
Qed.

Lemma sj_bsh_range u n a : ablock_range L ar u n -> in_shadow_of u n a -> BIGSHADOW_LO < a < BIGSHADOW_HI /\ 0 <= a < 2 ^ 64.
Proof.
  intros (B1 & _ & _ & B4 & _ & (A0 & _ & A2)) (X1 & X2).
  pose proof (sj_S_range u ltac:(lia)) as R1. pose proof (sj_S_range (u + n - 1) ltac:(lia)) as R2.
  unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. lia.
Qed.

Lemma sj_bsh_not_w LB FF LK sp scr b a : sj_wf LB FF LK -> In b LB -> in_shadow_of (fst b) (snd b) a -> ~ aclientw L ar LB FF sp scr a.
Proof.
  intros (WB & WF & FSA & SP1 & SP2) Hb Hsh W. destruct (WB b Hb) as (BR & BA). pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (sj_bsh_range (fst b) (snd b) a BR Hsh) as (RA & _). pose proof Hsh as (X1 & X2).
  unfold aclientw, aclient_g in W. destruct W as [W|[W|[W|[W|[W|[W|W]]]]]].
  -
    destruct W as (b' & Hb' & Y). destruct (WB b' Hb') as ((_ & _ & _ & _ & _ & (_ & AM & _)) & _).
    unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
  -
    destruct W as (W & _). unfold BIGSHADOW_HI in *. lia.
  -
    destruct W as (W & _). lia.
  -
    destruct W as (f & Hf & Y & _). destruct (WF f Hf) as (F1 & F2 & _). destruct FSA as (_ & AM & _).
    unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *. pose proof (sj_ffbytes_mod8 (ff_class f)) as _. lia.
  -
    destruct W as (W & _). assert (E8 : ahl_ceil ar mod 8 = 0).
    { pose proof (Z.div_mod (ar_sptop ar) 16 ltac:(lia)) as D. rewrite SP2, Z.add_0_r in D.
      replace (ar_sptop ar - 8388608) with ((2 * (ar_sptop ar / 16) - 1048576) * 8) by lia. apply Z_mod_mult. }
    pose proof (sj_div8_lt (fst b + snd b - 1) (ahl_ceil ar) ltac:(lia) E8) as LT. unfold HeapIfaceA.S in *. lia.
  -
    destruct W as (f & Hf & (Y1 & Y2)). destruct (WF f Hf) as (F1 & F2 & F3 & F4).
    pose proof (sj_ffbytes_mod8 _ F4) as (K8 & K64). pose proof (sj_frame_mod8 _ _ F4 F3) as F8.
    pose proof (sj_mod8_of16 _ B3) as U8.
    destruct (BA f (in_or_app _ _ _ (or_introl Hf))) as [Ap|Ap].
    + pose proof (sj_div8_lt (fst b + snd b - 1) (ff_addr f) ltac:(lia) F8) as LT. unfold HeapIfaceA.S in *. lia.
    + pose proof (sj_div8_lt (ff_addr f + ff_bytes (ff_class f) - 1) (fst b) ltac:(lia) U8) as LT. unfold HeapIfaceA.S in *. lia.
  - destruct W as (_ & _ & []).
Qed.

Lemma sj_keep LB FF LK (M M' : word -> option byte) : sj_wf LB FF LK ->
  (forall b a, In b LB -> in_shadow_of (fst b) (snd b) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  Forall (fun b => shadow_blk M (fst b) (snd b)) LB -> Forall (fun b => shadow_blk M' (fst b) (snd b)) LB.
Proof.
  intros (WB & _) KEEP SB. rewrite Forall_forall in *. intros b Hb. destruct (WB b Hb) as ((B1 & _ & B3 & B4 & _) & _).
  apply (shadow_blk_frame M M' (fst b) (snd b)); [lia|exact (sj_mod8_of16 _ B3)|exact B4| |exact (SB b Hb)].
  intros a Ha. exact (KEEP b a Hb Ha).
Qed.
Lemma sj_keep_pres LB LB' FF LK sp scr (M M' : word -> option byte) : sj_wf LB FF LK -> incl LB' LB ->
  aheap_pres L ar LB' FF sp scr M M' ->
  Forall (fun b => shadow_blk M (fst b) (snd b)) LB -> Forall (fun b => shadow_blk M' (fst b) (snd b)) LB'.
Proof.
  intros WF INC (HP & _) SB. pose proof WF as (WB & _).
  assert (WF' : sj_wf LB' FF LK).
  { destruct WF as (W1 & W2 & W3). split; [|split; [exact W2|exact W3]]. intros b Hb. exact (W1 b (INC b Hb)). }
  apply (sj_keep LB' FF LK M M' WF').
  - intros b a Hb Ha. destruct (WB b (INC b Hb)) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (_ & Ra).
    apply HP; [exact Ra|]. do 6 right. exists b. split; [exact Hb|exact Ha].
  - rewrite Forall_forall in *. intros b Hb. exact (SB b (INC b Hb)).
Qed.

#[using="OK"] Theorem strict_malloc : amalloc_spec L ar scfg HIS.
Proof.
  intros fx R M model LB FF LK cr A n K (RI & SB & FC) HALT MI H10 Hn CR Htp Hra STK K0 POST.
  pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
  apply (HAJ.aior_malloc _ _ _ _ _ OK fx R M model LB FF LK cr A n K RI HALT MI H10 Hn CR Htp Hra STK K0).
  intros R' M' model' A' u Hu RP BR BA FA DEF SHu HP MRT INC MI' RI'.
  apply (POST R' M' model' A' u Hu RP BR BA FA DEF SHu HP MRT INC MI'). split; [exact RI'|]. split; [|exact FC].
  constructor; [exact SHu|]. exact (sj_keep_pres LB LB FF LK _ _ M M' WF (incl_refl _) HP SB).
Qed.

#[using="OK"] Theorem strict_aligned : aaligned16_spec L ar scfg HIS.
Proof.
  intros fx R M model LB FF LK cr A n K (RI & SB & FC) HALT MI H10 H11 Hn Hn16 CR Htp Hra STK K0 POST.
  pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
  apply (HAJ.aior_aligned _ _ _ _ _ OK fx R M model LB FF LK cr A n K RI HALT MI H10 H11 Hn Hn16 CR Htp Hra STK K0).
  intros R' M' model' A' u Hu RP BR BA FA DEF SHu HP MRT INC MI' RI'.
  apply (POST R' M' model' A' u Hu RP BR BA FA DEF SHu HP MRT INC MI'). split; [exact RI'|]. split; [|exact FC].
  constructor; [exact SHu|]. exact (sj_keep_pres LB LB FF LK _ _ M M' WF (incl_refl _) HP SB).
Qed.

#[using="OK"] Theorem strict_free : afree_spec L ar scfg HIS.
Proof.
  intros fx R M model LB FF LK cr A u n K (RI & SB & FC) HALT MI Hin H10 Htp Hra STK K0 POST.
  pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
  apply (HAJ.aior_free _ _ _ _ _ OK fx R M model LB FF LK cr A u n K RI HALT MI Hin H10 Htp Hra STK K0).
  intros R' M' model' A' RP HP MRT INC MI' RI'.
  apply (POST R' M' model' A' RP HP MRT INC MI'). split; [exact RI'|]. split; [|exact FC].
  exact (sj_keep_pres LB (lb_remove u LB) FF LK _ _ M M' WF (fun b Hb => sj_lb_remove_in u LB b Hb) HP SB).
Qed.

#[using="OK"] Theorem strict_free_null_of : afree_null_spec L ar scfg HIR -> afree_null_spec L ar scfg HIS.
Proof.
  intros FN fx R M model LB FF LK cr A K (RI & SB & FC) HALT MI H10 Htp Hra STK K0 POST.
  pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
  apply (FN fx R M model LB FF LK cr A K RI HALT MI H10 Htp Hra STK K0).
  intros R' M' model' A' RP HP MRT INC MI' RI'.
  apply (POST R' M' model' A' RP HP MRT INC MI'). split; [exact RI'|]. split; [|exact FC].
  exact (sj_keep_pres LB LB FF LK _ _ M M' WF (incl_refl _) HP SB).
Qed.

#[using="OK"] Theorem strict_stack_malloc : forall k, In k [1; 3] -> astack_malloc_spec L ar scfg HIS k.
Proof.
  intros k Hk fx R M model LB FF LK cr A K sp (RI & SB & FC) HALT MI Htp Hra STK ROOM RS K0 POST.
  pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
  assert (Hk' : In k [0; 1; 2; 3; 5]) by (cbn [In] in *; tauto).
  apply (HAJ.aior_stack_malloc _ _ _ _ _ OK k Hk' fx R M model LB FF LK cr A K RI HALT MI Htp Hra STK ROOM RS K0).
  intros R' M' model' F fl LK' H10 RP P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 HP MRT MI' RI'.
  apply (POST R' M' model' F fl LK' H10 RP P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 HP MRT MI'). split; [exact RI'|]. split.
  - exact (sj_keep_pres LB LB FF LK _ _ M M' WF (incl_refl _) HP SB).
  - unfold sj_cls in *. rewrite Forall_forall in *. intros f Hf. cbn [app] in Hf. destruct Hf as [<-|Hf]; [cbn [In] in Hk |- *; tauto|].
    apply FC. apply in_app_or in Hf. destruct Hf as [Hf|Hf]; apply in_or_app; [left; exact Hf|right; exact (P5 f Hf)].
Qed.

#[using="IMG FLAG OK"] Theorem strict_release : rt_release_frame L ar HIS.
Proof.
  intros LB FF LK cr A M M' V F k rs fl (RI & SB & FC) Hin CF W C0 DEF.
  pose proof (sj_wf_of LB FF LK cr A M V RI) as WF. pose proof (FLAG LB FF LK cr A M V F k rs fl RI Hin CF) as FL.
  split; [exact (HAJ.aior_release _ _ _ _ _ OK LB FF LK cr A M M' V F k rs fl RI Hin CF W C0 DEF)|]. split.
  - apply (sj_keep LB FF LK M M' WF); [|exact SB]. intros b a Hb Ha.
    pose proof WF as (WB & _ & (_ & AM & _) & _). destruct (WB b Hb) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (RA & Ra).
    assert (NE : a <> fl) by (intros ->; specialize (FL Ra); unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *; lia).
    destruct (W a Ra NE) as [E|X]; [exact E|exfalso; exact (sj_bsh_not_w LB FF LK 0 0 b a WF Hb Ha X)].
  - unfold sj_cls in *. rewrite Forall_forall in *. intros f Hf. apply FC. apply in_app_or in Hf. apply in_or_app.
    destruct Hf as [Hf|Hf]; [left; exact (sj_ff_remove_in F FF f Hf)|right; exact Hf].
Qed.

#[using="OK"] Theorem strict_leak : rt_leak_frames HIS.
Proof.
  intros LB FF LK cr A M V FX (RI & SB & FC) INC ND.
  split; [exact (HAJ.aior_leak _ _ _ _ _ OK LB FF LK cr A M V FX RI INC ND)|]. split; [exact SB|].
  unfold sj_cls in *. rewrite Forall_forall in *. intros f Hf. apply FC. apply in_app_or in Hf. apply in_or_app.
  destruct Hf as [Hf|Hf]; [left; exact (proj2 (proj1 (sj_sfilter_In _ _ _ _ _) Hf))|].
  apply in_app_or in Hf. destruct Hf as [Hf|Hf]; [left; exact (INC f Hf)|right; exact Hf].
Qed.

#[using="OK"] Theorem strict_no_return : ahandle_no_return_spec L ar scfg HIS.
Proof.
  intros fx R M model LB FF LK cr A K sp (RI & SB & FC) HALT MI Htp Hra STK K0 POST.
  pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
  apply (HAJ.aior_no_return _ _ _ _ _ OK fx R M model LB FF LK cr A K RI HALT MI Htp Hra STK K0).
  intros R' M' model' lo RP Hlo Hlo8 SZ KEEP SCR MRT MI' RI'.
  apply (POST R' M' model' lo RP Hlo Hlo8 SZ KEEP SCR MRT MI'). split; [exact RI'|]. split; [|exact FC].
  apply (sj_keep LB FF LK M M' WF); [|exact SB]. intros b a Hb Ha.
  pose proof WF as (WB & _ & _ & SP1 & SP2). destruct (WB b Hb) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (_ & Ra).
  pose proof BR as (_ & _ & _ & B4 & B5 & _). pose proof STK as (_ & ST2 & _).
  apply KEEP; [exact Ra| |].
  - do 6 right. exists b. split; [exact Hb|exact Ha].
  - intros (Y1 & _). pose proof (sj_S_mono (fst b + snd b - 1) lo ltac:(fold sp in ST2; lia)) as MO.
    destruct Ha as (_ & X2). assert (E8 : lo mod 8 = 0).
    { pose proof (Z.div_mod lo 4096 ltac:(lia)) as D. rewrite Hlo8, Z.add_0_r in D. rewrite D.
      replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by ring. apply Z_mod_mult. }
    pose proof (sj_div8_lt (fst b + snd b - 1) lo ltac:(fold sp in ST2; lia) E8) as LT. unfold HeapIfaceA.S in *. lia.
Qed.

Lemma sj_mem_keep fx R M model LB FF LK cr A dst n K (M' : word -> option byte) :
  amem_pre L ar HIR fx R M model LB FF LK cr A dst n K ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) a ->
             ~ (dst <= a < dst + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  Forall (fun b => shadow_blk M (fst b) (snd b)) LB -> Forall (fun b => shadow_blk M' (fst b) (snd b)) LB.
Proof.
  intros PRE KEEP SB. destruct PRE as (RI & _ & _ & _ & _ & _ & _ & _ & _ & _ & DW & _).
  pose proof (sj_wf_of LB FF LK cr A M (vml_of model) RI) as WF.
  apply (sj_keep LB FF LK M M' WF); [|exact SB]. intros b a Hb Ha.
  pose proof WF as (WB & _). destruct (WB b Hb) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (_ & Ra).
  apply KEEP; [exact Ra| |].
  - do 6 right. exists b. split; [exact Hb|exact Ha].
  - intros (Y1 & Y2). pose proof (DW (a - dst) ltac:(lia)) as X. replace (dst + (a - dst)) with a in X by ring.
    exact (sj_bsh_not_w LB FF LK _ _ b a WF Hb Ha X).
Qed.
#[using="OK"] Lemma sj_strict_mem_pre fx R M model LB FF LK cr A dst n K :
  amem_pre L ar HIS fx R M model LB FF LK cr A dst n K ->
  amem_pre L ar HIR fx R M model LB FF LK cr A dst n K /\ Forall (fun b => shadow_blk M (fst b) (snd b)) LB /\ sj_cls FF LK.
Proof. intros ((RI & SB & FC) & REST). exact (conj (conj RI REST) (conj SB FC)). Qed.

#[using="IMG OK"] Theorem strict_memset : amemset_spec L ar scfg HIS.
Proof.
  intros fx R M model LB FF LK cr A dst c n K PRE H11 POST.
  destruct (sj_strict_mem_pre _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (PRER & SB & FC).
  apply (HAJ.aior_memset _ _ _ _ _ OK fx R M model LB FF LK cr A dst c n K PRER H11).
  intros R' M' model' H10 RP NB KEEP SCR MRT MI' RI'.
  apply (POST R' M' model' H10 RP NB KEEP SCR MRT MI'). split; [exact RI'|]. split; [|exact FC].
  exact (sj_mem_keep fx R M model LB FF LK cr A dst n K M' PRER KEEP SB).
Qed.

#[using="IMG OK"] Theorem strict_memcpy_at : forall pc mo, amemcpy_spec_at L ar scfg HIR pc mo -> amemcpy_spec_at L ar scfg HIS pc mo.
Proof.
  intros pc mo MC fx R M model LB FF LK cr A dst src n bs K PRE H11 AC SRC APR CLS RD OV POST.
  destruct (sj_strict_mem_pre _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (PRER & SB & FC).
  apply (MC fx R M model LB FF LK cr A dst src n bs K PRER H11 AC SRC APR CLS RD OV).
  intros R' M' model' H10 RP NB KEEP SCR MRT MI' RI'.
  apply (POST R' M' model' H10 RP NB KEEP SCR MRT MI'). split; [exact RI'|]. split; [|exact FC].
  exact (sj_mem_keep fx R M model LB FF LK cr A dst n K M' PRER KEEP SB).
Qed.

#[using="OK"] Theorem strict_frame : rt_frame L ar HIS.
Proof.
  intros LB FF LK cr A M M' V (RI & SB & FC) PRIV DEF.
  pose proof (sj_wf_of LB FF LK cr A M V RI) as WF.
  split; [exact (HAJ.aior_frame _ _ _ _ _ OK LB FF LK cr A M M' V RI PRIV DEF)|]. split; [|exact FC].
  apply (sj_keep LB FF LK M M' WF); [|exact SB]. intros b a Hb Ha.
  pose proof WF as (WB & _). destruct (WB b Hb) as (BR & _). pose proof (sj_bsh_range _ _ a BR Ha) as (_ & Ra).
  apply PRIV; [exact Ra|]. right. right. exists b. split; [exact Hb|exact Ha].
Qed.

#[using="OK"] Theorem strict_wf : rt_wf L ar HIS.
Proof.
  intros LB FF LK cr A M V (RI & SB & FC).
  destruct (HAJ.aior_wf _ _ _ _ _ OK LB FF LK cr A M V RI) as (WB & WF & REST).
  rewrite Forall_forall in SB. unfold sj_cls in FC. rewrite Forall_forall in FC.
  split. { intros b Hb. destruct (WB b Hb) as (B1 & B2 & _ & B4 & B5 & B6 & B7).
           split; [exact B1|]. split; [exact B2|]. split; [exact (SB b Hb)|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|exact B7]. }
  split. { intros f Hf. destruct (WF f Hf) as (F1 & F2 & F3 & _ & F5 & F6).
           split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact (FC f (in_or_app _ _ _ (or_introl Hf)))|]. split; [exact F5|exact F6]. }
  exact REST.
Qed.

#[using="OK"] Theorem strict_lazy : rt_lazy L ar HIS.
Proof. intros LB FF LK cr A M model (RI & _ & _). exact (HAJ.aior_lazy _ _ _ _ _ OK LB FF LK cr A M model RI). Qed.

#[using="OK"] Theorem strict_perm : rt_perm HIS.
Proof.
  intros LB LB' FF FF' LK cr A M V (RI & SB & FC) ELB ND EFF NDF.
  split; [exact (HAJ.aior_perm _ _ _ _ _ OK LB LB' FF FF' LK cr A M V RI ELB ND EFF NDF)|]. split.
  - rewrite Forall_forall in *. intros b Hb. exact (SB b (proj2 (ELB b) Hb)).
  - unfold sj_cls in *. rewrite Forall_forall in *. intros f Hf. apply FC. apply in_app_or in Hf. apply in_or_app.
    destruct Hf as [Hf|Hf]; [left; exact (proj2 (EFF f) Hf)|right; exact Hf].
Qed.

#[using="OK"] Theorem strict_statics : rt_statics L C HIS.
Proof. intros LB FF LK cr A M V (RI & _ & _). exact (HAJ.aior_statics _ _ _ _ _ OK LB FF LK cr A M V RI). Qed.

#[using="OK"] Theorem strict_flagptr : rt_flagptr L HIS.
Proof.
  intros LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl (RI & _ & _) (RI' & _ & _).
  exact (HAJ.aior_flagptr _ _ _ _ _ OK LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl RI RI').
Qed.

#[using="OK"] Theorem strict_small_high : rt_small_high HIS.
Proof. intros LB FF LK cr A M V (RI & _ & _). exact (HAJ.aior_small_high _ _ _ _ _ OK LB FF LK cr A M V RI). Qed.

#[using="IMG FLAG OK"] Theorem strict_ok : asan_iface_okB L ar C scfg HIS.
Proof.
  constructor.
  - exact strict_malloc.
  - exact strict_aligned.
  - exact strict_free.
  - exact strict_stack_malloc.
  - exact strict_release.
  - exact strict_leak.
  - exact strict_no_return.
  - exact strict_memset.
  - exact (strict_memcpy_at _ _ (HAJ.aior_memcpy _ _ _ _ _ OK)).
  - exact (strict_memcpy_at _ _ (HAJ.aior_memmove _ _ _ _ _ OK)).
  - exact strict_frame.
  - exact strict_wf.
  - exact strict_lazy.
  - exact strict_perm.
  - exact strict_statics.
  - exact strict_flagptr.
  - exact strict_small_high.
Qed.
End Strict.

Lemma strict_of_nil (HIR : asan_iface) cr A M V : ri_inv HIR [] [] [] cr A M V -> ri_inv (HAJ.strict_of HIR) [] [] [] cr A M V.
Proof. intros RI. split; [exact RI|]. split; constructor. Qed.
