(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstCdReads.v (commit 67deba317dfb, blob 6508a2de0a5e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 10 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YA0i YA0n YG00 YG01 YG0a YG03 YG0f YG0n YG0s YI04 YK04 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG03cf ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstDrainR YGcfInstDrainRL.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFg7 AFgk AFk5 AFkn AFez.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMcdR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstDrainCg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstDrainCm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstDrainCn FGcN AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0b YA05 YA09 YG0g YG0j YK0g YGcfXs YGcfXsMapped YGcfRoomCf YGcfCker.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg}.
Definition CONST_CD_APART : Prop :=
forall B ly ce, im_syms B -> layout_ok ly ->
(forall sg, In sg im_segs -> fst (ly_img ly) <= Z.of_N (seg_base sg) /\
  Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly)) ->
ly_tsd ly = as_tsd B -> In ce (as_const B ly) ->
forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) ->
~ (ly_T ly + t_cache <= aeval B ly (c_at ce) + j < ly_T ly + kThreadObjSize).
End C.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma pairwise_nth_w : forall {A} (R : A -> A -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros A R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Lemma tfibsegs_ext : map (fun sg => (Z.of_N (seg_base sg), Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs =
[(65536, 200704); (200704, 659456); (659456, 667648); (667648, 6291456)].
Proof. vm_compute. reflexivity. Qed.

Lemma img_in_window : forall ly,
(forall sg, In sg tfibsegs -> fst (ly_img ly) <= Z.of_N (seg_base sg) /\
  Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly)) ->
fst (ly_img ly) <= 65536 /\ 6291456 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly SEG. pose proof tfibsegs_ext as E.
destruct tfibsegs as [|s0 [|s1 [|s2 [|s3 [|s4 t]]]]] eqn:ES; cbn [map] in E; try discriminate E.
injection E as E0 E0' E1 E1' E2 E2' E3 E3'.
pose proof (SEG s0 ltac:(left; reflexivity)) as [A0 _]. pose proof (SEG s3 ltac:(right; right; right; left; reflexivity)) as [_ A3].
lia.
Qed.

Theorem CONST_CD_APART_preset : CONST_CD_APART (IM := AImg_A).
Proof.
intros B ly ce TS LO SEG HTSD Hin j Hj HT.
change (TfibSyms B) in TS. change (forall sg, In sg tfibsegs -> fst (ly_img ly) <= Z.of_N (seg_base sg) /\
  Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly)) in SEG.
destruct (img_in_window ly SEG) as [IW1 IW2].
rewrite (ts_const _ TS ly) in Hin.
pose proof (proj1 (forallb_forall _ _) (AFg7.Tfib_const_locr ly) ce Hin) as K. unfold AFg7.const_loc_okr in K.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as IT.
cbn [fst snd] in IT.
assert (DTI : zdisjoint (ly_T ly, kThreadObjSize) (ly_img ly)) by exact (pairwise_nth_w zdisjoint _ 2 9 _ _ (lo_disj _ LO) ltac:(lia) eq_refl eq_refl).
assert (DTC : zdisjoint (ly_T ly, kThreadObjSize) (ly_C ly, 256)) by exact (pairwise_nth_w zdisjoint _ 2 6 _ _ (lo_disj _ LO) ltac:(lia) eq_refl eq_refl).
assert (DTD : zdisjoint (ly_T ly, kThreadObjSize) (ly_D ly, 4096)) by exact (pairwise_nth_w zdisjoint _ 2 7 _ _ (lo_disj _ LO) ltac:(lia) eq_refl eq_refl).
unfold zdisjoint in DTI, DTC, DTD. cbn [fst snd] in DTI, DTC, DTD.
pose proof (Z.le_max_l 1 (Z.of_nat (c_w ce))) as W1.
assert (LOW : forall a, AFg7.low_okr a (Z.max 1 (Z.of_nat (c_w ce))) = true -> ~ (ly_T ly + t_cache <= a + j < ly_T ly + kThreadObjSize)).
{ intros a L' Ha. unfold AFg7.low_okr in L'. apply orb_prop in L' as [L'|L']; apply andb_prop in L' as [L1 L2];
  apply Z.leb_le in L1; apply Z.leb_le in L2;
  unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, t_cache, kThreadObjSize in *.
  - lia.
  - change (65536 / 8) with 8192 in *. change (6291456 / 8) with 786432 in *. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
    destruct IT as [IT0 [IL|[IH1 IH2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia. }
destruct (c_at ce) eqn:Ec; try discriminate K; cbn [aeval] in HT.
- exact (LOW _ K HT).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2. unfold t_cache, kThreadObjSize in *. lia.
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2. unfold kThreadObjSize, t_cache in *. lia.
- rewrite HTSD, (ts_tsd _ TS) in HT. exact (LOW _ K HT).
- rewrite (ts_inst _ TS) in HT. exact (LOW _ K HT).
- rewrite (ts_tp _ TS) in HT. exact (LOW _ K HT).
- apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2. unfold kThreadObjSize, t_cache in *. lia.
Qed.
End W.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Hypothesis TS : TfibSyms B.
Hypothesis HIOK : YGcfInstBase.IOK_ok B IOK.
Local Notation ARX := (ARXr_cf (IM := AImg_A) B IOK Hp).

Lemma arx_M : forall inst ly X W mem md, ARX inst ly X W mem md -> ARmcfR B ly X Hp (aview tfibsegs (w_H W) mem).
Proof. intros inst ly X W mem md (_ & HA & _). exact (proj1 HA). Qed.
Lemma arx_L : forall inst ly X W mem md, ARX inst ly X W mem md -> ALedger_cf tfibsegs ly X md.
Proof. intros inst ly X W mem md (_ & HA & _). exact (proj1 (proj2 HA)). Qed.

Lemma off_img_of : forall ly X md lo len a, ALedger_cf tfibsegs ly X md -> in_app lo len ->
zdisjoint (lo, len) (ly_img ly) -> lo <= a < lo + len -> AF0x.off_img a.
Proof.
intros ly X md lo len a L IA DJ Ha. destruct (img_in_window ly (alc_img _ _ _ _ L)) as [I1 I2].
unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END.
destruct IA as [IA0 [IL|[IH1 IH2]]]; ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
Qed.

Lemma pres_of_view : forall H mem a, AF0x.off_img a -> aview tfibsegs H mem a <> None -> apresent H mem a.
Proof.
intros H mem a Ha Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:E.
- exact (AF0x.mbyte_off_apresent H mem a b Ha E).
- cbn in Hv. congruence.
Qed.

Lemma vis_present : forall ly (W : world tfibsegs) mem e len a, range_vis B ly (aview tfibsegs (w_H W) mem) (e, len) ->
aeval B ly e <= a < aeval B ly e + len -> AF0x.off_img a -> apresent (w_H W) mem a.
Proof.
intros ly W mem e len a V Ha Ho. apply pres_of_view; [exact Ho|].
pose proof (V (a - aeval B ly e) ltac:(cbn [snd]; lia)) as V'. cbn [fst] in V'.
replace (aeval B ly e + (a - aeval B ly e)) with a in V' by lia. exact V'.
Qed.

Lemma prim_off_img : forall ly X md a, layout_ok ly -> ALedger_cf tfibsegs ly X md ->
ly_prim ly <= a < ly_prim ly + kPrimResvSize -> AF0x.off_img a.
Proof.
intros ly X md a LO L Ha. apply (off_img_of ly X md (ly_prim ly) kPrimResvSize a L); [|exact (pairwise_nth_w zdisjoint _ 0 9 _ _ (lo_disj _ LO) ltac:(lia) eq_refl eq_refl) | exact Ha].
exact (in_high_app _ _ (lo_high _ LO)).
Qed.

Lemma in_combine_seq_iff : forall {A} (l : list A) s j (x : A),
In (j, x) (combine (seq s (length l)) l) <-> exists j', j = (s + j')%nat /\ nth_error l j' = Some x.
Proof.
intros A l. induction l as [|y t IH]; intros s j x.
- cbn. split; [intros [] | intros (j' & _ & H); destruct j'; discriminate H].
- cbn [length seq combine In]. rewrite IH. split.
  + intros [E | (j' & -> & H)]; [injection E as <- <-; exists 0%nat; split; [lia | reflexivity] | exists (S j'); split; [lia | exact H]].
  + intros (j' & -> & H). destruct j' as [|j']; [left; injection H as ->; f_equal; lia | right; exists j'; split; [lia | exact H]].
Qed.
Lemma in_combine_seq0 : forall {A} (l : list A) j (x : A), In (j, x) (combine (seq 0 (length l)) l) <-> nth_error l j = Some x.
Proof.
intros A l j x. rewrite in_combine_seq_iff. split; [intros (j' & -> & H); exact H | intros H; exists j; split; [lia | exact H]].
Qed.

Lemma zseq_mem : forall c, 1 <= c <= 31 -> In c (zseq 1 31).
Proof. intros c Hc. unfold zseq. apply in_map_iff. exists (Z.to_nat (c - 1)). split; [lia|]. apply in_seq. lia. Qed.

Lemma vm_eq : forall m a a' (w : nat) v, a = a' -> val_mem tfibsegs m a w v -> val_mem tfibsegs m a' w v.
Proof. intros m a a' w v -> H. exact H. Qed.

Theorem cr_geo : DMcdR.rd_geo ARX.
Proof.
intros inst ly X W mem md H. pose proof (arx_M _ _ _ _ _ _ H) as M. pose proof (arx_L _ _ _ _ _ _ H) as L.
split; [exact (amr_layout _ _ _ _ _ M)|]. split.
- destruct (img_in_window ly (alc_img _ _ _ _ L)) as [I1 I2]. unfold img_cover, TFIB_IMG_LO, TFIB_IMG_END. lia.
- rewrite (amr_tsd _ _ _ _ _ M). exact (ts_tsd _ TS).
Qed.

Theorem cr_thread : DMcdR.rd_thread ARX.
Proof.
intros inst ly X W mem md H a Ha. pose proof (arx_M _ _ _ _ _ _ H) as M. pose proof (arx_L _ _ _ _ _ _ H) as L.
pose proof (amr_layout _ _ _ _ _ M) as LO.
assert (V : range_vis B ly (aview tfibsegs (w_H W) mem) (AT 0, kThreadObjSize)).
{ apply (proj1 (Forall_forall _ _) (amr_areas _ _ _ _ _ M)). unfold aareas. rewrite !in_app_iff. right; right; right. cbn. tauto. }
apply (vis_present ly W mem (AT 0) kThreadObjSize a V); [cbn [aeval]; lia|].
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as IT.
exact (off_img_of ly X md (ly_T ly) kThreadObjSize a L IT (pairwise_nth_w zdisjoint _ 2 9 _ _ (lo_disj _ LO) ltac:(lia) eq_refl eq_refl) Ha).
Qed.

Theorem cr_rinfo : DMcdR.rd_rinfo ARX.
Proof.
intros inst ly X W mem md c H Hc a Ha. pose proof (arx_M _ _ _ _ _ _ H) as M. pose proof (arx_L _ _ _ _ _ _ H) as L.
pose proof (amr_layout _ _ _ _ _ M) as LO. pose proof (lo_space_in _ LO) as [S1 S2].
unfold AFgk.RGv, AFgk.RIv in Ha.
assert (V : range_vis B ly (aview tfibsegs (w_H W) mem) (ASp kRegionInfoOff, 4096)).
{ apply (proj1 (Forall_forall _ _) (amr_areas _ _ _ _ _ M)). unfold aareas. rewrite !in_app_iff. right; right; right. cbn. tauto. }
apply (vis_present ly W mem (ASp kRegionInfoOff) 4096 a V); [cbn [aeval]; lia|].
apply (prim_off_img ly X md a LO L). unfold kRegionInfoOff, kSpaceSize in *. lia.
Qed.

Theorem cr_fa : DMcdR.rd_fa ARX.
Proof.
intros inst ly X W mem md c H Hc a Ha. pose proof (arx_M _ _ _ _ _ _ H) as M. pose proof (arx_L _ _ _ _ _ _ H) as L.
pose proof (amr_layout _ _ _ _ _ M) as LO. unfold AFgk.FAv, AFgk.RBv in Ha.
assert (V : range_vis B ly (aview tfibsegs (w_H W) mem) (ASp (region_off c + kFreeArrayOffset), rg_mapped_fa (reg X c))).
{ apply (proj1 (Forall_forall _ _) (amr_areas _ _ _ _ _ M)). unfold aareas. rewrite !in_app_iff. left.
  apply in_flat_map. exists c. split; [apply zseq_mem; lia | right; left; reflexivity]. }
apply (vis_present ly W mem _ _ a V); [cbn [aeval]; lia|].
pose proof (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ M) c ltac:(lia)) as CL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & _).
apply (prim_off_img ly X md a LO L). unfold region_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.

Theorem cr_cache : DMcdR.rd_cache ARX.
Proof.
intros inst ly X W mem md c H Hc Hci. pose proof (arx_M _ _ _ _ _ _ H) as M.
pose proof (amr_cells _ _ _ _ _ M) as C. unfold acells_cf in C. rewrite !Forall_app in C. destruct C as (_ & C2 & _).
assert (CC : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (cache_cells X c)).
{ apply Forall_forall. intros ce Hce. apply (proj1 (Forall_forall _ _) C2). apply in_flat_map. exists c.
  split; [apply zseq_mem; lia | exact Hce]. }
unfold cache_cells in CC. rewrite Hci in CC.
apply Forall_cons_iff in CC as [C0 CC]. apply Forall_cons_iff in CC as [C4 CC]. apply Forall_cons_iff in CC as [C8 CS].
unfold AFgk.PCv. split; [|split; [|split]].
- apply (vm_eq _ (aeval B ly (AT (t_cache + 80 * c)))); [cbn [aeval]; lia|]. exact (cell_holds_val_mem B ly _ mem _ 4 _ C0).
- apply (vm_eq _ (aeval B ly (AT (t_cache + 80 * c + 4)))); [cbn [aeval]; lia|]. exact (cell_holds_val_mem B ly _ mem _ 4 _ C4).
- apply (vm_eq _ (aeval B ly (AT (t_cache + 80 * c + 8)))); [cbn [aeval]; lia|]. exact (cell_holds_val_mem B ly _ mem _ 8 _ C8).
- intros i v Hi. pose proof (proj1 (Forall_forall _ _) CS (z4 (aoff (AT (t_cache + 80 * c)) (16 + 4 * Z.of_nat i)) (v / 16))
    ltac:(apply in_map_iff; exists (i, v); split; [reflexivity|]; apply in_combine_seq0; exact Hi)) as Ci.
  apply (vm_eq _ (aeval B ly (AT (t_cache + 80 * c + (16 + 4 * Z.of_nat i))))); [cbn [aeval]; lia|].
  exact (cell_holds_val_mem B ly _ mem _ 4 _ Ci).
Qed.

Theorem cr_region : DMcdR.rd_region ARX.
Proof.
intros inst ly X W mem md c H Hc. pose proof (arx_M _ _ _ _ _ _ H) as M. cbv zeta.
pose proof (amr_cells _ _ _ _ _ M) as C. unfold acells_cf in C. rewrite !Forall_app in C. destruct C as (C1 & _).
assert (CR : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (region_cells_cf X c)).
{ apply Forall_forall. intros ce Hce. apply (proj1 (Forall_forall _ _) C1). apply in_flat_map. exists c.
  split; [apply zseq_mem; lia | exact Hce]. }
unfold region_cells_cf, region_cells in CR. cbn [removelast] in CR.
apply Forall_cons_iff in CR as [R0 CR]. apply Forall_cons_iff in CR as [R8 CR]. apply Forall_cons_iff in CR as [R16 CR].
apply Forall_cons_iff in CR as [R24 CR]. apply Forall_cons_iff in CR as [R32 CR]. apply Forall_cons_iff in CR as [R40 CR].
apply Forall_cons_iff in CR as [R48 CR]. apply Forall_cons_iff in CR as [R56 _].
unfold AFgk.RGv, AFgk.RIv.
split; [apply (vm_eq _ (aeval B ly (ASp (kRegionInfoOff + 128 * c)))); [cbn [aeval]; lia | exact (cell_holds_val_mem B ly _ mem _ 8 _ R0)]|].
split; [apply (vm_eq _ (aeval B ly (ASp (kRegionInfoOff + 128 * c + 8)))); [cbn [aeval]; lia | exact (cell_holds_val_mem B ly _ mem _ 8 _ R8)]|].
split; [apply (vm_eq _ (aeval B ly (ASp (kRegionInfoOff + 128 * c + 16)))); [cbn [aeval]; lia | exact (cell_holds_val_mem B ly _ mem _ 8 _ R16)]|].
split; [apply (vm_eq _ (aeval B ly (ASp (kRegionInfoOff + 128 * c + 24)))); [cbn [aeval]; lia | exact (cell_holds_val_mem B ly _ mem _ 8 _ R24)]|].
split; [apply (vm_eq _ (aeval B ly (ASp (kRegionInfoOff + 128 * c + 32)))); [cbn [aeval]; lia | exact (cell_holds_val_mem B ly _ mem _ 8 _ R32)]|].
split; [apply (vm_eq _ (aeval B ly (ASp (kRegionInfoOff + 128 * c + 40)))); [cbn [aeval]; lia | exact (cell_holds_val_mem B ly _ mem _ 8 _ R40)]|].
split; [apply (vm_eq _ (aeval B ly (ASp (kRegionInfoOff + 128 * c + 48)))); [cbn [aeval]; lia | exact (cell_holds_val_mem B ly _ mem _ 8 _ R48)]|].
apply (vm_eq _ (aeval B ly (ASp (kRegionInfoOff + 128 * c + 56)))); [cbn [aeval]; lia | exact (cell_holds_val_mem B ly _ mem _ 8 _ R56)].
Qed.

Theorem cr_img : DMcdR.rd_img B ARX.
Proof. intros inst ly X W mem md H. exact (amr_const _ _ _ _ _ (arx_M _ _ _ _ _ _ H)). Qed.

Theorem cr_inst : DMcdR.rd_inst B ARX.
Proof. intros inst ly X W mem md (HI & _). exact (HIOK inst HI). Qed.

Theorem cr_len : DMcdR.rd_len ARX.
Proof.
intros inst ly X W mem md H. pose proof (amr_wfr _ _ _ _ _ (arx_M _ _ _ _ _ _ H)) as WF.
rewrite (wfr_len_cache _ _ _ _ _ WF), (wfr_len_regions _ _ _ _ _ WF). lia.
Qed.

Theorem cr_user : DMcdR.rd_user ARX.
Proof.
intros inst ly X W mem md c' H Hc. pose proof (amr_wfr _ _ _ _ _ (arx_M _ _ _ _ _ _ H)) as WF.
pose proof (wfr_classes _ _ _ _ _ WF c' Hc) as CL. pose proof (class_ok c' Hc) as (K1 & K2 & _).
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as A2.
pose proof (wrc_mapped_al _ _ _ _ _ _ CL) as A3. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as A4.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
apply Z.mod_divide in A4 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [q2 Hq2]; [|lia].
apply Z.mod_divide; [lia|]. exists (q * q2 * 2). lia.
Qed.

Theorem cr_own : DMcdR.rd_own ARX (aowned B) RMAXD_cf.
Proof.
intros inst ly X W mem md c off H CDM. cbv zeta. intros a Ha. pose proof (arx_M _ _ _ _ _ _ H) as M.
destruct CDM as (Hc & Hci & Hcnt & Hpm & _ & _ & _ & _ & _ & _ & FN & FL & FB & _ & F27 & _).
pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
assert (D2 : max_cached c / 2 <= max_cached c) by (apply Z.div_le_upper_bound; lia).
assert (D0 : 0 <= max_cached c / 2) by (apply Z.div_pos; lia).
assert (CP : 0 <= AFgk.CNTPv c (Z.of_nat (length (pc_chunks (cache X c)))) <= max_cached c)
  by (unfold AFgk.CNTPv, AFgk.Nv, AFgk.MAXv; destruct (Z.eqb_spec (Z.of_nat (length (pc_chunks (cache X c)))) (max_cached c)); lia).
destruct Ha as [Hw|Hw].
- apply (RL.own_core_cf B ly X Hp _ (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd].
  unfold AFgk.WINF, AFgk.SLOTv, AFgk.PCv in Hw. unfold t_cache, kThreadObjSize in *. lia.
- destruct Hw as [Hfull [Hw|Hw]].
  + apply (RL.own_rinfo_cf B ly X Hp _ a M). pose proof (lo_space_in _ (amr_layout _ _ _ _ _ M)) as [S1 S2].
    unfold AFgk.WRG, AFgk.RGv, AFgk.RIv in Hw. unfold kRegionInfoOff, kSpaceSize in *. lia.
  + apply (RL.own_fa_cf B ly X Hp _ c a M ltac:(lia)).
    unfold AFgk.DSTv, AFgk.FAv, AFgk.RBv, AFgk.Nv, AFgk.MAXv in Hw. unfold fa_base, region_base.
    unfold kFreeArrayMax in *. change (2 ^ 27) with 134217728 in F27. lia.
Qed.

Theorem cr_grow : DMcdR.rd_grow ARX.
Proof.
intros inst ly X W mem md c H Hc. cbv zeta. intros Hgrow HB. destruct H as (HI & HA & HX).
destruct (YGcfInstDrainCg.cgp_rd_grow B ly X Hp W mem md c HA Hc Hgrow HB) as (G1 & G2 & G3 & G4 & _ & G6).
assert (EF : AFk5.FAv ly c = fa_base ly c) by (unfold AFk5.FAv, AFk5.RBv, fa_base, region_base; rewrite (region_off_eq c ltac:(lia)); lia).
rewrite EF. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
intros a Ha. apply G6. unfold AFkn.SHR, AFk5.SHBv in Ha. unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Lemma win_cdwin : forall ly X c regs a,
AFgk.WIN ly regs c (Z.of_nat (length (pc_chunks (cache X c)))) (fa_len (rg_free (reg X c))) a <->
YGcfInstDrainCm.cdwin ly X c (bv_unsigned (getr regs 2)) a.
Proof.
intros ly X c regs a. unfold AFgk.WIN, AFgk.WINR, YGcfInstDrainCm.cdwin, YGcfInstDrainCm.cmwinR, YGcfInstDrainCm.cmfull.
split; intros [Y|[Y|(E & Y)]];
  [left; exact Y | right; left; exact Y | right; right; split; [apply Z.eqb_eq; exact E | exact Y]
  |left; exact Y | right; left; exact Y | right; right; split; [apply Z.eqb_eq; exact E | exact Y]].
Qed.

Theorem cr_step : DMcdR.rd_step ARX (aowned B) RMAXD_cf.
Proof.
intros inst ly X W regs mem md c off mem' mat H MOD HSK. cbv zeta. intros GR HMEQ HPRES NC NS NFULL.
pose proof H as (HI & MR & HXM). pose proof (proj1 MR) as M.
destruct MOD as (Hc & Hci & Hcnt & Hpm & Hx0 & Hx1 & Hxm & Hxni & _).
assert (KC : 2 <= max_cached c <= 16) by (pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K & _); exact K).
assert (DV : 0 <= max_cached c / 2 <= max_cached c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (Hsp : ly_stk_lo ly + 320 <= bv_unsigned (getr regs 2) <= ly_stk_hi ly) by (unfold DMiface.KSTACK_CF in HSK; lia).
assert (Hroom : (Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c) = true ->
  4 * (fa_len (rg_free (reg X c)) + max_cached c / 2) <= rg_mapped_fa (reg X c)).
{ intros E. unfold AFgk.Nv, AFgk.MAXv in GR. rewrite E in GR. exact GR. }
unfold AFgk.MEQ in HMEQ.
assert (MEQ' : forall x : word, ~ YGcfInstDrainCm.cdwin ly X c (bv_unsigned (getr regs 2)) (bv_unsigned x) -> mem' x = mem x).
{ intros x Hx. apply HMEQ. intros Hw. apply Hx. exact (proj1 (win_cdwin ly X c regs _) Hw). }
assert (PRES' : forall a, YGcfInstDrainCm.cdwin ly X c (bv_unsigned (getr regs 2)) a -> apresent (w_H W) mem' a).
{ intros a Ha. apply HPRES. exact (proj2 (win_cdwin ly X c regs a) Ha). }
assert (NC' : val_mem tfibsegs (mrestrict (w_H W) mem') (YGcfInstDrainCm.cmPC ly c) 4 (YGcfInstDrainCm.cmCNTP X c + 1))
  by exact NC.
assert (NS' : val_mem tfibsegs (mrestrict (w_H W) mem') (YGcfInstDrainCm.cmSLOT ly X c) 4 ((off - region_off c) / 16))
  by exact NS.
assert (NR0 : YGcfInstDrainCm.cmfull X c = true -> val_mem tfibsegs (mrestrict (w_H W) mem') (YGcfInstDrainCm.cmRG ly c) 8 0).
{ intros F. unfold YGcfInstDrainCm.cmfull in F. apply Z.eqb_eq in F. exact (proj1 (NFULL F)). }
assert (NR16 : YGcfInstDrainCm.cmfull X c = true -> val_mem tfibsegs (mrestrict (w_H W) mem') (YGcfInstDrainCm.cmRG ly c + 16) 8
  (YGcfInstDrainCm.cmold X c + YGcfInstDrainCm.cmN c)).
{ intros F. unfold YGcfInstDrainCm.cmfull in F. apply Z.eqb_eq in F. exact (proj1 (proj2 (NFULL F))). }
assert (NFA : YGcfInstDrainCm.cmfull X c = true -> forall i v, 0 <= i < YGcfInstDrainCm.cmN c ->
  val_mem tfibsegs (mrestrict (w_H W) mem)
    (YGcfInstDrainCm.cmPC ly c + 16 + 4 * (YGcfInstDrainCm.cmcnt X c - YGcfInstDrainCm.cmN c) + 4 * i) 4 v ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (YGcfInstDrainCm.cmDST ly X c + 4 * i) 4 v).
{ intros F. unfold YGcfInstDrainCm.cmfull in F. apply Z.eqb_eq in F. exact (proj2 (proj2 (proj2 (NFULL F)))). }
assert (LO : layout_ok ly) by exact (amr_layout _ _ _ _ _ M).
pose proof (alc_img _ _ _ _ (arx_L _ _ _ _ _ _ H)) as SEG.

assert (CONST' : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly)).
{ apply Forall_forall. intros ce Hce.
  eapply (YGcfInstDrainCm.cell_xfer (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W mem mem');
    [eassumption .. | exact (proj1 (Forall_forall _ _) (amr_const _ _ _ _ _ M) ce Hce) | ].
  intros j Hj.
  pose proof (CONST_CD_APART_preset B ly ce TS LO SEG (amr_tsd _ _ _ _ _ M) Hce j Hj) as NT.
  destruct (proj1 (Forall_forall _ _) (amr_const_owned _ _ _ _ _ M) ce Hce j Hj) as [O|[O|O]].
  - apply Exists_exists in O as (r & Hr & R1 & R2).
    pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [S1 S2].
    eapply (YGcfInstDrainCm.ok_img (IM := AImg_A) B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp);
      [eassumption .. | unfold in_zr; lia].
  - apply Exists_exists in O as (e & He & E1 & E2). unfold core_extents in He. cbn [In] in He.
    destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in E1, E2.
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp)
        with (j := 1%nat); [eassumption .. | right; reflexivity | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCm.ok_T (IM := AImg_A) B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp);
        [eassumption .. | lia | ].
      intros HF. apply NT. revert HF.
      unfold YGcfInstDrainCm.cmwinF, YGcfInstDrainCm.cmSLOT, YGcfInstDrainCm.cmPC, YGcfInstDrainCm.cmCNTP,
        YGcfInstDrainCm.cmcnt, YGcfInstDrainCm.cmN, YGcfInstDrainCm.cmMAX.
      destruct (Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c) eqn:EE;
        [apply Z.eqb_eq in EE | apply Z.eqb_neq in EE]; unfold t_cache, kThreadObjSize; lia.
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp)
        with (j := 4%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp)
        with (j := 5%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp)
        with (j := 6%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp)
        with (j := 7%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
  - apply Exists_exists in O as (r & Hr & R1 & R2). cbn [fst snd] in R1, R2. unfold shadow_addr in R1, R2.
    pose proof (proj1 (Forall_forall _ _) (aso_static _ (amr_syms _ _ _ _ _ M)) r Hr) as (T1 & T2 & T3).
    assert (D0 : 0 <= fst r / 8) by (apply Z.div_pos; lia).
    assert (D1 : fst r / 8 <= fst r) by (apply Z.div_le_upper_bound; lia).
    assert (D2 : (snd r + 7) / 8 <= snd r + 7) by (apply Z.div_le_upper_bound; lia).
    eapply (YGcfInstDrainCm.ok_shadow (IM := AImg_A) B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp);
      [eassumption .. | unfold SHADOW_OFF, kHighMemBeg, kImgEnd in *; lia]. }

assert (CDE : cache_dealloc c off X = IRet (tt, AFez.S' X c off)).
{ pose proof (cr_len _ _ _ _ _ _ H) as [HL1 _].
  unfold AFez.S', AFez.X1, AFez.full.
  destruct (Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c) eqn:E.
  - pose proof (Hroom eq_refl) as RM. apply Z.eqb_eq in E.
    assert (LK : length (YFfh.kdrained c X) = Z.to_nat (max_cached c / 2)).
    { unfold YFfh.kdrained. cbv zeta. rewrite Hpm, length_skipn. lia. }
    apply YFfh.cache_dealloc_eq_full; [exact Hci | lia | lia | rewrite Hpm; exact E |].
    rewrite LK, Z2Nat.id by lia. exact RM.
  - apply Z.eqb_neq in E. apply YFfh.cache_dealloc_eq_push; [exact Hci | rewrite Hpm; exact E]. }
destruct (@YGcfInstDrainCm.cd_step_cf _ _ _ AImg_A B ly X c off (bv_unsigned (getr regs 2)) W mem mem' md Hp
  MR Hc Hci Hpm Hsp Hroom MEQ' PRES' CONST' NC' NS' NR0 NR16 NFA IOK inst HI HXM
  (AFez.S' X c off) CDE (conj Hx0 Hx1) Hxm Hxni (with_vm_backing (m_vm_lazy md) mat md)
  (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)) as [R1 R2].
split; [exact R1 | exact R2].
Qed.

Theorem cr_budget_x : DMcdR.rd_budget_x B ARX (DRq_cf B kQuarantineMax).
Proof.
intros inst ly X z W regs mem md (H & _) its zs D _.
destruct H as (_ & (M & L & (HA & _) & _) & _).
destruct D as (_ & _ & HU & HT & HG & _ & HN & _ & HHO).
pose proof (YGcfRoomCf.qloose_cut_of_pending X its HU HT HG HN) as QL.
pose proof (amr_wfr _ _ _ _ _ M) as WF.
pose proof (YGcfRoomCf.room_rec_cf_of_cut _ ly X md WF QL HHO) as R.
replace (eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768)
  with (eager_used md + A_bytes (w_A W) + (2 * kUserMapSize + 32768)) by lia.
apply (YGcfCker.room_wA_parts_R _ _ ly X md W _ WF L HA R).
apply Z.leb_le. reflexivity.
Qed.

Lemma cd_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz. Qed.
Lemma cd_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Ha. Qed.

Lemma cd_val_aview : forall H mem a (w : nat) v k, val_mem tfibsegs (mrestrict H mem) a w v -> (k < w)%nat ->
aview tfibsegs H mem (a + Z.of_nat k) = Some (le_byte v w k).
Proof.
intros H mem a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map].
change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal. apply cd_u8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma cd_aview_byte : forall (H : word -> bool) mem a (v : Z), H (Z_to_bv 64 a) = false ->
mem (Z_to_bv 64 a) = Some (Z_to_bv 8 v) -> aview tfibsegs H mem a = Some (bv_unsigned (Z_to_bv 8 v)).
Proof. intros H mem a v HH E. unfold aview, mbyte, mrestrict. rewrite HH, E. reflexivity. Qed.

Lemma cd_val_frame : forall (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v E V k Hk. pose proof (V k Hk) as Vk. unfold mbyte in Vk |- *. rewrite (E k Hk). exact Vk. Qed.

Lemma cd_grant_vmmaps : forall flags a n md,
m_vmmaps (YG0b.grant_md false flags a n md) = mmap_fixed_rw_next (m_vmmaps md) a n.
Proof.
intros flags a n md. change (YG0b.grant_md false flags a n md) with (YA05.fixedin_ok_model 3 flags a n md).
unfold YA05.fixedin_ok_model, with_mmap_replacement. rewrite YA09.with_mmap_backing_vmmaps. reflexivity.
Qed.

Theorem cr_growT : DMcdR.rd_growT ARX (aowned B) RMAXD_cf.
Proof.
intros inst ly X W regs mem md c off W3 mem1 mem' matN mat' H MOD. cbv zeta.
intros HSK FULL GROW WLE HWA HSUB HFH HWH HAB HAI HAMWF HSIO HEAG MEQ1 PRES1 V1 MEQT PREST VT.
pose proof (proj1 H) as HI. pose proof (proj1 (proj2 H)) as MR. pose proof (proj1 MR) as M.
pose proof MR as (_ & LED & _ & AMW & _).
assert (HXM : YGcfXs.xs_mapped_cf ly X md) by (eapply ARXr_cf_xsm; exact H).
destruct MOD as (Hc & Hci & Hcnt & Hpm & Hx0 & Hx1 & Hxm & Hxni & Hal & Halm & Hold0 & Hold4 & Hmfmax & Hmfmod & Hqm & Hgm).
pose proof (cr_len _ _ _ _ _ _ H) as [HL1 HL2].
assert (Hlenr : (Z.to_nat c < length (st_regions X))%nat) by lia.
assert (KC : 2 <= max_cached c <= 16) by (pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K & _); exact K).
assert (DV : 0 <= max_cached c / 2 <= max_cached c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (DV8 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
unfold AFgk.Nv, AFgk.MAXv in GROW, FULL, VT.
assert (Hgrow : rg_mapped_fa (reg X c) + kFreeArrayMapSize <= kFreeArrayMax) by (apply Hgm; exact GROW).
assert (Hsp : ly_stk_lo ly + 320 <= bv_unsigned (getr regs 2) <= ly_stk_hi ly) by (unfold DMiface.KSTACK_CF in HSK; lia).
assert (Hstk : ly_stk_lo ly <= bv_unsigned (getr regs 2) - 240 - AFl1.RSTACK /\
  bv_unsigned (getr regs 2) - 240 - AFl1.RSTACK <= bv_unsigned (getr regs 2) <= ly_stk_hi ly)
  by (unfold DMiface.KSTACK_CF, AFl1.RSTACK in *; lia).
assert (EF : AFk5.FAv ly c = fa_base ly c)
  by (unfold AFk5.FAv, AFk5.RBv, fa_base, region_base; rewrite (region_off_eq c ltac:(lia)); lia).
rewrite EF in *.
assert (ESH : AFk5.SHBv + (fa_base ly c + rg_mapped_fa (reg X c)) / 8 = shadow_addr (fa_base ly c + rg_mapped_fa (reg X c)))
  by (unfold AFk5.SHBv, shadow_addr, SHADOW_OFF; lia).
rewrite ESH in *. unfold AFkn.RANGE, AFkn.SHR in *.
destruct V1 as (V0 & V16 & V24 & VMAP & VSH).
destruct VT as (T1 & T2 & T3 & T4 & T5).

assert (MEQ1c : forall x : word, ~ YGcfInstDrainCn.cnwin ly X c (bv_unsigned (getr regs 2))
  (bv_unsigned (getr regs 2) - 240 - AFl1.RSTACK) (bv_unsigned x) -> mem1 x = mem x).
{ intros x Hx. apply MEQ1. intros Hw. apply Hx. unfold YGcfInstDrainCn.cnwin. unfold AFgk.RGv, AFgk.RIv in Hw.
  lia. }
assert (PRES1c : forall a, YGcfInstDrainCn.cnwin ly X c (bv_unsigned (getr regs 2))
  (bv_unsigned (getr regs 2) - 240 - AFl1.RSTACK) a -> apresent (w_H W3) mem1 a).
{ intros a Ha. apply PRES1. unfold YGcfInstDrainCn.cnwin in Ha. unfold AFgk.RGv, AFgk.RIv. lia. }
assert (VRG24 : forall k, (k < 8)%nat -> aview tfibsegs (w_H W3) mem1 (ly_space ly + kRegionInfoOff + 128 * c + 24 + Z.of_nat k) =
  Some (le_byte (rg_mapped_fa (reg X c) + kFreeArrayMapSize) 8 k)).
{ intros k Hk. exact (cd_val_aview _ _ _ _ _ k V24 Hk). }
assert (VMAPc : forall a, fa_base ly c + rg_mapped_fa (reg X c) <= a < fa_base ly c + rg_mapped_fa (reg X c) + kUserMapSize ->
  aview tfibsegs (w_H W3) mem1 a = Some (le_byte 0 1 0)).
{ intros a Ha. destruct (PRES1 a ltac:(lia)) as [HH _]. rewrite (cd_aview_byte _ _ _ 0 HH (VMAP a Ha)). reflexivity. }
assert (VSHc : forall a, shadow_addr (fa_base ly c + rg_mapped_fa (reg X c)) <= a <
  shadow_addr (fa_base ly c + rg_mapped_fa (reg X c)) + 32768 -> aview tfibsegs (w_H W3) mem1 a = Some (le_byte 250 1 0)).
{ intros a Ha. destruct (PRES1 a ltac:(lia)) as [HH _]. rewrite (cd_aview_byte _ _ _ 250 HH (VSH a Ha)). reflexivity. }
pose proof (YGcfInstDrainCn.cn_slot (IM := AImg_A) B ly X c W W3 mem mem1 md Hp MR Hc Hgrow HWH VMAPc VSHc) as (S1 & S2 & S3 & _).
pose proof (YGcfInstDrainCn.cn_al8_slot (IM := AImg_A) B ly X c W mem md Hp MR Hc) as [q Hq].

assert (HWFG : WfR_cf (as_universe B) 0 0 0 (YGcfInstDrainCg.cgX X c)).
{ assert (E27 : 2 ^ 27 = 134217728) by reflexivity.
  apply (YGcfInstDrainCg.cg_WfR X c Hc Hlenr (as_universe B) 0 0 0 (fa_len (rg_free (reg X c)) + max_cached c / 2)
    (amr_wfr _ _ _ _ _ M)); unfold kFreeArrayMapSize, kFreeArrayMax in *; try lia.
  apply FGcN.round_upF; unfold kFreeArrayMapSize in *; lia. }

pose proof (amr_layout _ _ _ _ _ M) as LO.
pose proof (alc_img _ _ _ _ (arx_L _ _ _ _ _ _ H)) as SEG.
assert (CONST1 : Forall (cell_holds B ly (aview tfibsegs (w_H W3) mem1)) (as_const B ly)).
{ apply Forall_forall. intros ce Hce.
  eapply (YGcfInstDrainCn.cn_cell_xfer (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1);
    [eassumption .. | exact (proj1 (Forall_forall _ _) (amr_const _ _ _ _ _ M) ce Hce) | ].
  intros j Hj.
  pose proof (CONST_CD_APART_preset B ly ce TS LO SEG (amr_tsd _ _ _ _ _ M) Hce j Hj) as NT.
  destruct (proj1 (Forall_forall _ _) (amr_const_owned _ _ _ _ _ M) ce Hce j Hj) as [O|[O|O]].
  - apply Exists_exists in O as (r & Hr & R1 & R2).
    pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
    eapply (YGcfInstDrainCn.okn_img (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp);
      [eassumption .. | unfold in_zr; lia].
  - apply Exists_exists in O as (e & He & E1 & E2). unfold core_extents in He. cbn [In] in He.
    destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in E1, E2.
    + eapply (YGcfInstDrainCn.okn_static (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp)
        with (j := 1%nat); [eassumption .. | right; reflexivity | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCn.okn_T (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp);
        [eassumption .. | lia | intros HF; apply NT; unfold t_cache, kThreadObjSize; lia
        | intros HF; apply NT; unfold t_cache, kThreadObjSize; lia].
    + eapply (YGcfInstDrainCn.okn_static (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp)
        with (j := 4%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCn.okn_static (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp)
        with (j := 5%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCn.okn_static (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp)
        with (j := 6%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCn.okn_static (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp)
        with (j := 7%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
  - apply Exists_exists in O as (r & Hr & R1 & R2). cbn [fst snd] in R1, R2. unfold shadow_addr in R1, R2.
    pose proof (proj1 (Forall_forall _ _) (aso_static _ (amr_syms _ _ _ _ _ M)) r Hr) as (A1 & A2 & A3).
    assert (D0 : 0 <= fst r / 8) by (apply Z.div_pos; lia).
    assert (D1 : fst r / 8 <= fst r) by (apply Z.div_le_upper_bound; lia).
    assert (D2 : (snd r + 7) / 8 <= snd r + 7) by (apply Z.div_le_upper_bound; lia).
    assert (D3 : kHighMemBeg / 8 <= (fa_base ly c + rg_mapped_fa (reg X c)) / 8) by (apply Z.div_le_mono; lia).
    assert (D4 : kHighMemBeg / 8 = 2199291686912) by reflexivity.
    eapply (YGcfInstDrainCn.okn_band (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp);
      [eassumption .. | unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kImgEnd in *; lia
      | unfold shadow_addr, SHADOW_OFF, kImgEnd in *; lia]. }

assert (AMW' : amwf (with_vm_backing (m_vm_lazy md) matN md)) by exact (YG0n.amwf_same md _ eq_refl eq_refl AMW).
assert (HVM : vm_maps (m_vmmaps (YG0b.grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c)))
  (Z_to_bv 64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md))) = vm_maps (m_vmmaps md))
  by (rewrite cd_grant_vmmaps; reflexivity).
assert (HVR : vm_reserved (m_vmmaps (YG0b.grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c)))
  (Z_to_bv 64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md))) = vm_reserved (m_vmmaps md))
  by (rewrite cd_grant_vmmaps; reflexivity).
assert (HVL : vm_limit (m_vmmaps (YG0b.grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c)))
  (Z_to_bv 64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md))) = vm_limit (m_vmmaps md))
  by (rewrite cd_grant_vmmaps; reflexivity).
assert (HVT : alloc_top (m_vmmaps (YG0b.grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c)))
  (Z_to_bv 64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md))) = alloc_top (m_vmmaps md))
  by (rewrite cd_grant_vmmaps; reflexivity).
assert (HVNA : forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true ->
  region_free (vm_noaccess (m_vmmaps (YG0b.grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c)))
  (Z_to_bv 64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md)))) lo n = true)
  by (intros lo n R; exact (YG0g.naf_grant_md false _ _ _ _ AMW' lo n R)).
pose proof (in_high_app _ _ (lo_high _ LO)) as PH.
assert (FB : 0 <= fa_base ly c + rg_mapped_fa (reg X c) /\ fa_base ly c + rg_mapped_fa (reg X c) + kUserMapSize <= 2 ^ 64)
  by (destruct PH as [P0 [PL|[P1 P2]]]; ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (U1 : bv_unsigned (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c))) = fa_base ly c + rg_mapped_fa (reg X c))
  by (apply cd_u64; unfold kUserMapSize in FB; lia).
assert (U2 : bv_unsigned (Z_to_bv 64 kUserMapSize) = kUserMapSize) by (apply cd_u64; unfold kUserMapSize; lia).
assert (HCOV : forall x, ~ (fa_base ly c + rg_mapped_fa (reg X c) <= x < fa_base ly c + rg_mapped_fa (reg X c) + kUserMapSize) ->
  YK0g.covered (vm_noaccess (m_vmmaps (YG0b.grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c)))
  (Z_to_bv 64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md))) ++
  m_vm_lazy (YG0b.grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c)))
  (Z_to_bv 64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md))) x =
  YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x).
{ intros x Hx. assert (WF' : YK0g.model_ivs_wf (with_vm_backing (m_vm_lazy md) matN md))
    by exact (proj1 (proj1 (YG0b.amwf_MWF _) (proj1 AMW'))).
  exact (YG0j.cov_grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c))) (Z_to_bv 64 kUserMapSize)
    _ x WF' ltac:(rewrite U1, U2; lia)
    ltac:(rewrite U1, U2; exact Hx)). }

pose proof (YGcfInstDrainCn.cn_grant_ARcfR (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md _ Hp
  MR Hc Hgrow Hsp _ Hstk MEQ1c PRES1c HWH VRG24 VMAPc VSHc Hlenr HWFG CONST1 HWA HVM HVR HVL HVT HVNA HCOV HEAG HAMWF) as MR2.

pose proof (YGcfInstDrainCg.cg_reg_c X c Hc Hlenr) as RGC.
assert (Hci2 : st_cache_inited (YGcfInstDrainCg.cgX X c) = true) by exact Hci.
assert (Hpm2 : pc_max (cache (YGcfInstDrainCg.cgX X c) c) = max_cached c) by exact Hpm.
assert (Hroom2 : (Z.of_nat (length (pc_chunks (cache (YGcfInstDrainCg.cgX X c) c))) =? max_cached c) = true ->
  4 * (fa_len (rg_free (reg (YGcfInstDrainCg.cgX X c) c)) + max_cached c / 2) <= rg_mapped_fa (reg (YGcfInstDrainCg.cgX X c) c))
  by (intros _; exact (YGcfInstDrainCg.cg_room X c Hc Hlenr Hold4 (proj2 KC))).
assert (CF : YGcfInstDrainCm.cmfull (YGcfInstDrainCg.cgX X c) c = true)
  by (unfold YGcfInstDrainCm.cmfull; apply Z.eqb_eq; exact FULL).
assert (MEQ2 : forall x : word, ~ YGcfInstDrainCm.cdwin ly (YGcfInstDrainCg.cgX X c) c (bv_unsigned (getr regs 2)) (bv_unsigned x) ->
  mem' x = mem1 x).
{ intros x Hx. apply MEQT. intros Hw. apply Hx. clear Hx.
  destruct Hw as [Y|[Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]]].
  - left; exact Y.
  - right; left; left; exact Y.
  - right; left; right; left; exact Y.
  - right; left; right; right; exact Y.
  - right; right; split; [exact CF | left; left; exact Y].
  - right; right; split; [exact CF | left; right; left; exact Y].
  - right; right; split; [exact CF | left; right; right; exact Y].
  - right; right; split; [exact CF | right]. unfold YGcfInstDrainCm.cmDST, YGcfInstDrainCm.cmold. rewrite RGC. exact Y. }
assert (PRES2 : forall a, YGcfInstDrainCm.cdwin ly (YGcfInstDrainCg.cgX X c) c (bv_unsigned (getr regs 2)) a ->
  apresent (w_H W3) mem' a).
{ intros a Ha. apply PREST. destruct Ha as [Y|[[Y|[Y|Y]]|[_ [[Y|[Y|Y]]|Y]]]].
  - left; exact Y.
  - right; left; exact Y.
  - right; right; left; exact Y.
  - right; right; right; left; exact Y.
  - do 4 right; left; exact Y.
  - do 5 right; left; exact Y.
  - do 6 right; left; exact Y.
  - do 7 right. unfold YGcfInstDrainCm.cmDST, YGcfInstDrainCm.cmold in Y. rewrite RGC in Y. exact Y. }
assert (NC2 : val_mem tfibsegs (mrestrict (w_H W3) mem') (YGcfInstDrainCm.cmPC ly c) 4
  (YGcfInstDrainCm.cmCNTP (YGcfInstDrainCg.cgX X c) c + 1)) by exact T1.
assert (NS2 : val_mem tfibsegs (mrestrict (w_H W3) mem') (YGcfInstDrainCm.cmSLOT ly (YGcfInstDrainCg.cgX X c) c) 4
  ((off - region_off c) / 16)) by exact T2.
assert (NR02 : YGcfInstDrainCm.cmfull (YGcfInstDrainCg.cgX X c) c = true ->
  val_mem tfibsegs (mrestrict (w_H W3) mem') (YGcfInstDrainCm.cmRG ly c) 8 0) by (intros _; exact T3).
assert (NR162 : YGcfInstDrainCm.cmfull (YGcfInstDrainCg.cgX X c) c = true ->
  val_mem tfibsegs (mrestrict (w_H W3) mem') (YGcfInstDrainCm.cmRG ly c + 16) 8
  (YGcfInstDrainCm.cmold (YGcfInstDrainCg.cgX X c) c + YGcfInstDrainCm.cmN c)).
{ intros _. unfold YGcfInstDrainCm.cmold. rewrite RGC. exact T4. }
assert (NFA2 : YGcfInstDrainCm.cmfull (YGcfInstDrainCg.cgX X c) c = true -> forall i v, 0 <= i < YGcfInstDrainCm.cmN c ->
  val_mem tfibsegs (mrestrict (w_H W3) mem1) (YGcfInstDrainCm.cmPC ly c + 16 +
    4 * (YGcfInstDrainCm.cmcnt (YGcfInstDrainCg.cgX X c) c - YGcfInstDrainCm.cmN c) + 4 * i) 4 v ->
  val_mem tfibsegs (mrestrict (w_H W3) mem') (YGcfInstDrainCm.cmDST ly (YGcfInstDrainCg.cgX X c) c + 4 * i) 4 v).
{ intros _ i v Hi V. unfold YGcfInstDrainCm.cmDST, YGcfInstDrainCm.cmold. rewrite RGC.
  unfold YGcfInstDrainCm.cmN, YGcfInstDrainCm.cmMAX in Hi.
  apply (T5 i v Hi). apply (cd_val_frame (mrestrict (w_H W3) mem1)); [|exact V].
  intros k Hk.
  assert (OK : YGcfInstDrainCn.okn ly X c (bv_unsigned (getr regs 2)) (bv_unsigned (getr regs 2) - 240 - AFl1.RSTACK)
    (AFgk.SRCv ly c (Z.of_nat (length (pc_chunks (cache X c)))) + 4 * i + Z.of_nat k)).
  { eapply (YGcfInstDrainCn.okn_T (IM := AImg_A) B ly X c (bv_unsigned (getr regs 2)) W W3 mem mem1 md Hp);
      [eassumption .. | | |]; unfold AFgk.SRCv, AFgk.PCv, AFgk.Nv, AFgk.MAXv, t_cache, kThreadObjSize; lia. }
  destruct OK as [O1 O2]. unfold mrestrict.
  rewrite (MEQ1c (Z_to_bv 64 _)) by (rewrite cd_u64 by exact O1; exact O2).
  rewrite (HWH (Z_to_bv 64 _)) by (rewrite cd_u64 by exact O1; intros HD; apply O2; unfold YGcfInstDrainCn.cnwin; tauto).
  reflexivity. }

assert (CONST2 : Forall (cell_holds B ly (aview tfibsegs (w_H W3) mem')) (as_const B ly)).
{ apply Forall_forall. intros ce Hce.
  eapply (YGcfInstDrainCm.cell_xfer (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c (bv_unsigned (getr regs 2)) W3 mem1 mem');
    [eassumption .. | exact (proj1 (Forall_forall _ _) CONST1 ce Hce) | ].
  intros j Hj.
  pose proof (CONST_CD_APART_preset B ly ce TS LO SEG (amr_tsd _ _ _ _ _ M) Hce j Hj) as NT.
  destruct (proj1 (Forall_forall _ _) (amr_const_owned _ _ _ _ _ M) ce Hce j Hj) as [O|[O|O]].
  - apply Exists_exists in O as (r & Hr & R1 & R2).
    pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
    eapply (YGcfInstDrainCm.ok_img (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp);
      [eassumption .. | unfold in_zr; lia].
  - apply Exists_exists in O as (e & He & E1 & E2). unfold core_extents in He. cbn [In] in He.
    destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in E1, E2.
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp)
        with (j := 1%nat); [eassumption .. | right; reflexivity | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCm.ok_T (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp);
        [eassumption .. | lia | ].
      intros HF. apply NT. revert HF.
      unfold YGcfInstDrainCm.cmwinF, YGcfInstDrainCm.cmSLOT, YGcfInstDrainCm.cmPC, YGcfInstDrainCm.cmCNTP,
        YGcfInstDrainCm.cmcnt, YGcfInstDrainCm.cmN, YGcfInstDrainCm.cmMAX.
      change (cache (YGcfInstDrainCg.cgX X c) c) with (cache X c).
      destruct (Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c) eqn:EE;
        [apply Z.eqb_eq in EE | apply Z.eqb_neq in EE]; unfold t_cache, kThreadObjSize; lia.
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp)
        with (j := 4%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp)
        with (j := 5%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp)
        with (j := 6%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
    + eapply (YGcfInstDrainCm.ok_static (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp)
        with (j := 7%nat); [eassumption .. | left; lia | reflexivity | cbn [fst snd]; lia].
  - apply Exists_exists in O as (r & Hr & R1 & R2). cbn [fst snd] in R1, R2. unfold shadow_addr in R1, R2.
    pose proof (proj1 (Forall_forall _ _) (aso_static _ (amr_syms _ _ _ _ _ M)) r Hr) as (A1 & A2 & A3).
    assert (D0 : 0 <= fst r / 8) by (apply Z.div_pos; lia).
    assert (D1 : fst r / 8 <= fst r) by (apply Z.div_le_upper_bound; lia).
    assert (D2 : (snd r + 7) / 8 <= snd r + 7) by (apply Z.div_le_upper_bound; lia).
    eapply (YGcfInstDrainCm.ok_shadow (IM := AImg_A) B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp);
      [eassumption .. | unfold SHADOW_OFF, kHighMemBeg, kImgEnd in *; lia]. }

assert (CDE : cache_dealloc c off (YGcfInstDrainCg.cgX X c) =
  IRet (tt, YFfh.XK_push c off (YFfh.XK_drain c (YGcfInstDrainCg.cgX X c)))).
{ assert (LK : length (YFfh.kdrained c X) = Z.to_nat (max_cached c / 2)).
  { unfold YFfh.kdrained. cbv zeta. rewrite Hpm, length_skipn. lia. }
  apply YFfh.cache_dealloc_eq_full; [exact Hci | lia | change (st_cache (YGcfInstDrainCg.cgX X c)) with (st_cache X); lia
    | change (cache (YGcfInstDrainCg.cgX X c) c) with (cache X c); rewrite Hpm; exact FULL |].
  change (YFfh.kdrained c (YGcfInstDrainCg.cgX X c)) with (YFfh.kdrained c X). rewrite LK, Z2Nat.id by lia.
  exact (YGcfInstDrainCg.cg_room X c Hc Hlenr Hold4 (proj2 KC)). }
assert (HXM2 : YGcfXs.xs_mapped_cf ly (YGcfInstDrainCg.cgX X c)
  (YG0b.grant_md false AFkn.FL50 (Z_to_bv 64 (fa_base ly c + rg_mapped_fa (reg X c))) (Z_to_bv 64 kUserMapSize)
  (with_vm_backing (m_vm_lazy md) matN md)))
  by exact (YGcfXsMapped.xs_mapped_cf_grant_md _ _ _ _ _ _ _ (YGcfXsMapped.xs_mapped_cf_wvb _ _ _ _ _ HXM)).
assert (Hx1' : off - region_off c < rg_alloc_user (reg (YGcfInstDrainCg.cgX X c) c)) by (rewrite RGC; exact Hx1).
assert (Hxni' : ~ In (off - region_off c) (class_elems (YGcfInstDrainCg.cgX X c) c)) by (unfold class_elems; rewrite RGC; exact Hxni).
destruct (@YGcfInstDrainCm.cd_step_cf _ _ _ AImg_A B ly (YGcfInstDrainCg.cgX X c) c off (bv_unsigned (getr regs 2)) W3 mem1 mem' _ Hp
  MR2 Hc Hci2 Hpm2 Hsp Hroom2 MEQ2 PRES2 CONST2 NC2 NS2 NR02 NR162 NFA2 IOK inst HI HXM2
  _ CDE (conj Hx0 Hx1') Hxm Hxni' (with_vm_backing (m_vm_lazy _) mat' _)
  (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)) as [R1 R2].
split; [exact R1|]. split; [intros a Ha; exact (R2 a Ha)|].

intros a Hw Hns.
destruct Hw as [Y|[Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]]].
- exfalso; exact (Hns Y).
- eapply RL.own_rinfo_cf; [exact M | unfold AFgk.RGv, AFgk.RIv in Y; lia].
- eapply RL.own_rinfo_cf; [exact M | unfold AFgk.RGv, AFgk.RIv in Y; lia].
- eapply RL.own_rinfo_cf; [exact M | unfold AFgk.RGv, AFgk.RIv in Y; lia].
- eapply RL.own_core_cf; [exact M | right; left; reflexivity | cbn [fst snd]; unfold kThreadObjSize; lia].
- eapply RL.own_core_cf; [exact M | right; left; reflexivity | cbn [fst snd]; unfold kThreadObjSize; lia].
- eapply (RL.own_fa_cf _ _ _ _ _ c); [exact M | lia | unfold kUserMapSize, kFreeArrayMapSize in *; lia].
- rewrite Hq in Y. unfold shadow_addr in Y. rewrite (Z.mul_comm 8 q), Z.div_mul in Y by lia.
  replace a with (shadow_addr (8 * (a - SHADOW_OFF))) by (unfold shadow_addr; rewrite (Z.mul_comm 8), Z.div_mul by lia; lia).
  eapply RL.own_shadow_prim_cf; [exact M | rewrite Hq in S1, S2; unfold kUserMapSize in *; lia].
Qed.

Theorem cd_reads_cf : DMcdR.cd_reads B ARX (aowned B) (DRq_cf B kQuarantineMax) RMAXD_cf.
Proof.
constructor; [exact cr_geo | exact cr_thread | exact cr_rinfo | exact cr_fa | exact cr_cache | exact cr_region | exact cr_img
  | exact cr_inst | exact cr_own | exact cr_len | exact cr_user | exact cr_grow | exact cr_budget_x | exact cr_growT
  | exact cr_step].
Qed.
End F.
