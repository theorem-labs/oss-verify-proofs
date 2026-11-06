(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the generic cf layer's Deallocate interface, its POST
   fields (DGif0.di_post_n, di_post_c) over the cf relation ARcf.  rule 24: no function proved (kind: interface-instance
   discharge: the allocator relation re-established at Deallocate's return).

   The cf twin of c5's DGif1.v:833-1279 (post_n_cgif) and :1321-1607 (post_c_cgif) with the released AR facts they
   call (YFf0.free_finn_ARm, YFex.free_fin_ARm, YFfy.depot_mem_ok_agree) re-proved over YG0ncf.ARmcf / ARcf with
   YG0scf / YG0qcf / YG03cf / YG03dcf's _cf lemmas, at the instance of the brief:
     ARX := YGcfInstBase.ARX_cf B IOK Hp, rpre := rpreD_free_cf B, fpre := fpre_hp_cf im_segs B Hp, U := U_cf B,
     ft := free_cf, lpost := qtight, dpost := CLdepot.dpost_x im_segs B.
   - section n: the NULL arm's relation at dtick S (YFf0's section k; preset's AFf0cf);
   - sections cs: the arm whose last batch has room, the model side (qfin_c's fields) and the memory side (YFex's
     section c0).  The walk's write set Dc contains the WHOLE depot zone, so no gap patch (DGif1's memP / ARm_gap) is
     needed: the depot's cells come from the depot post at the return memory, the constant cells from the depot post
     on the zone and from the entry memory off it (decided byte by byte on the read value, no decidability premise);
   - Wf_cf of the final state is free_cf's law ml_free_cf along the granted path, never an event bound;
   - the freed block's head is not hidden (fpre_hp_cf), so the hidden-head clause of shadow_ok_cf is off its bytes.
   Every image fact is a named premise of section 0 over DImg's zones, im_segs and the asyms fields; no numeral of any
   image; generic over CfImg / CfParams / AImg / DImg. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0dcf YG0scf YG0qcf YG03cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YG03dcf YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRmodel YGcfMallocCompose YGcfInstBase YGcfInstFreeView.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLdepot YFfl YGcfDIface.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Ltac dsplits := repeat match goal with |- _ /\ _ => split end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.

(* ================================================================================================================ *)
(* 0. The image premises, over DImg's zone fields, the segments and the symbol table only.                           *)

(* The internal allocator's zone lies in its area or in the owned static data: YGcfDIface.IZONE_OWNED (the layer's
   one name for that fact). *)
(* The internal allocator's zone is in the loaded segments and apart from the instance object and the depot's static
   data.  Replaces: the ROM fact YB13.tfib_rom_all on DGgi.IZONE, and YF0m's internal-allocator constants against its
   instance / depot / store constants (YFf0.LOWD, YFf0.ok_inst / ok_depot_tab / ok_store, YFex.ok_low). *)
Definition FP_IZONE_ROM : Prop := forall a, dg_izone a ->
  seg_rom im_segs (Z_to_bv 64 a) <> None /\ ~ (as_inst B <= a < as_inst B + 3632) /\
  ~ (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) /\ ~ (as_store B <= a < as_store B + 64).
(* The depot's static data (the image part of CLdepot.depot_footprint) lies in the owned static data.  Replaces:
   YFf0.LOWD / YFex.LOWD's depot / store constant bounds. *)
Definition FP_DSTAT : Prop := forall a,
  (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) ->
  Exists (in_zr a) (as_owned_static B).
(* The depot zone lies in the owned static data or the depot's two blocks: YGcfDIface.DZONE_OWNED. *)
(* The guard [LGUARD ly] of the two layout-quantified premises below: the facts the relation gives about any layout it
   admits: the layer's YGcfInstBase.ly_img_ok (layout_ok; the layout's TSD slot is the symbol table's; the owned
   static data, which holds the instance object by asyms_ok's cover, lies inside the image window), the image window
   covers the image, and the symbol table is well formed.  Under it the owned extents (NB, SB, T, C, D) are apart from
   the image window (lo_disj) and so from the instance object and the static cells, and the TSD-relative constant
   cells sit at the image's TSD. *)
Definition LGUARD (ly : alayout) : Prop := ly_img_ok B ly /\ im_img_cover ly /\ asyms_ok B.
Lemma LGUARD_of_ARmcf : forall ly S Hp rd md, ARmcf B ly S Hp rd -> YGcfDIface.IMG_COVER -> ALedger_cf im_segs ly S md ->
  LGUARD ly.
Proof.
intros ly S Hp rd md M HC L.
exact (conj (ly_img_ok_of_ARmcf B ly S Hp rd M) (conj (HC ly S md L) (amc_syms _ _ _ _ _ M))).
Qed.
(* The depot zone covers the depot's footprint and avoids the instance object, at every layout the relation admits.
   Replaces: DGgi.DZONE's text in DGif1.gap_low / gapb_true / gapb_false and the footprint-in-DZONE steps of
   post_c_cgif. *)
Definition FP_DZONE_FP : Prop := forall ly a, LGUARD ly ->
  (CLdepot.depot_footprint B ly a -> dg_dzone ly a) /\ (dg_dzone ly a -> ~ (as_inst B <= a < as_inst B + 3632)).
(* The constant cells avoid the internal allocator's zone and the walk's thread-object window, at every layout the
   relation admits.  Replaces: DGif1.const_loc / YFfy.Tfib_const_loc (cloc). *)
Definition FP_CONST : Prop := forall ly c j, LGUARD ly ->
  In c (as_const B ly) -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ dg_izone (aeval B ly (c_at c) + j) /\ ~ DGgiC.WINT ly (aeval B ly (c_at c) + j).
(* FP_CONST at one layout (the form the memory sections read). *)
Definition FP_CONST_at (ly : alayout) : Prop := forall c j, In c (as_const B ly) -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ dg_izone (aeval B ly (c_at c) + j) /\ ~ DGgiC.WINT ly (aeval B ly (c_at c) + j).

(* The two zone facts the proofs below read, assembled from the premises. *)
Definition FP_IZONE : Prop := forall a, dg_izone a ->
  Exists (in_zr a) (as_owned_static B) /\ seg_rom im_segs (Z_to_bv 64 a) <> None /\
  ~ (as_inst B <= a < as_inst B + 3632) /\
  ~ (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) /\ ~ (as_store B <= a < as_store B + 64).
Definition FP_DZONE (ly : alayout) : Prop := forall a,
  (CLdepot.depot_footprint B ly a -> dg_dzone ly a) /\
  (dg_dzone ly a -> ~ (as_inst B <= a < as_inst B + 3632) /\ (CLdepot.depot_footprint B ly a \/ Exists (in_zr a) (as_owned_static B))).
Lemma FP_IZONE_of : YGcfDIface.IZONE_OWNED B -> FP_IZONE_ROM -> asyms_ok B -> FP_IZONE.
Proof.
intros HO HR SY a Ha. destruct (HR a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R1 (conj R2 (conj R3 R4)))].
destruct (HO a Ha) as [X|X]; [|exact X].
pose proof (proj1 (Forall_forall _ _) (aso_cover _ SY) (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) ltac:(cbn; tauto)) as C.
apply Exists_exists in C as (r & Hr & [S1 S2]). cbn [fst snd] in S1, S2. apply Exists_exists. exists r.
split; [exact Hr|]. unfold in_zr. lia.
Qed.
Lemma FP_DZONE_of : YGcfDIface.DZONE_OWNED B -> FP_DZONE_FP -> forall ly, LGUARD ly -> FP_DZONE ly.
Proof.
intros HO HF ly G a. destruct (HF ly a G) as [F1 F2]. split; [exact F1|]. intros Hd. split; [exact (F2 Hd)|].
destruct (HO ly a Hd) as [X|[X|X]]; [right; exact X | left; unfold CLdepot.depot_footprint; tauto | left; unfold CLdepot.depot_footprint; tauto].
Qed.
Lemma FP_CONST_of : FP_CONST -> forall ly, LGUARD ly -> FP_CONST_at ly.
Proof. intros HC ly G c j Hc Hj. exact (HC ly c j G Hc Hj). Qed.

(* The relation's machine cells (ARmcf's amc_exh_cell / amc_errb_cells) are off the free walk's writes
   (YGcfInstFreeView section 5, XC; their ownership rows from ARmcf's amc_cells_owned).  The error-buffer object
   avoids the two zones the walk writes in the image: a per-unit image row. *)
Definition ERRB_APART : Prop := forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
  ~ dg_izone a /\ (forall ly, LGUARD ly -> ~ dg_dzone ly a).

(* Printf's two writable image cells (field round 3: ARmcf's amc_pf_cells; CfImg's cf_toolname_cell / cf_pfcb_cell)
   are kept by every builder that does not write them.  The free walk writes the internal allocator's zone and the
   depot's zone in the image, so the cells must avoid both: a per-unit image row, ERRB_APART's twin. *)
Definition pf_byte (a : Z) : Prop := cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8.
Definition PF_APART : Prop := forall a, pf_byte a -> ~ dg_izone a /\ (forall ly, LGUARD ly -> ~ dg_dzone ly a).

Lemma xw_iz : forall ly S Hp rd, ARmcf B ly S Hp rd -> ERRB_APART -> FP_IZONE ->
  forall a, XC B ly a -> ~ dg_izone a.
Proof.
intros ly S Hp rd M HR HIZ a [(c & Hc & Ea)|Ha] Hz.
- destruct (HIZ a Hz) as (OS & _). exact (x_exh_nstatic B ly S Hp rd M c a Hc Ea OS).
- exact (proj1 (HR a Ha) Hz).
Qed.

Lemma xw_dz : forall ly S Hp rd, ARmcf B ly S Hp rd -> ERRB_APART ->
  FP_DSTAT -> FP_DZONE ly -> LGUARD ly -> forall a, XC B ly a -> ~ dg_dzone ly a.
Proof.
intros ly S Hp rd M HR HDS HDZ HLG a X Hd. destruct X as [(c & Hc & Ea)|Ha].
- destruct (proj2 (HDZ a) Hd) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [F|[F|[F|F]]].
    * exact (x_exh_nstatic B ly S Hp rd M c a Hc Ea (HDS a (or_introl F))).
    * exact (x_NB B ly S Hp rd M a (or_introl (ex_intro _ c (conj Hc Ea))) F).
    * exact (x_SB B ly S Hp rd M a (or_introl (ex_intro _ c (conj Hc Ea))) F).
    * exact (x_exh_nstatic B ly S Hp rd M c a Hc Ea (HDS a (or_intror F))).
  + exact (x_exh_nstatic B ly S Hp rd M c a Hc Ea OS).
- exact (proj2 (HR a Ha) ly HLG Hd).
Qed.

(* ================================================================================================================ *)
(* 1. Byte helpers over im_segs.                                                                                    *)
Lemma aview_same_cf : forall (H : word -> bool) (mem mem' : word -> option byte) a,
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview im_segs H mem' a = aview im_segs H mem a.
Proof. intros H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma u8_small_cf : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz. Qed.

Lemma val_mem_aview_cf : forall H m a (w : nat) v kk, val_mem im_segs (mrestrict H m) a w v -> (kk < w)%nat ->
  aview im_segs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map].
change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply u8_small_cf.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* DGif1.v:886: a cell whose every byte reads as in one of two readers where it holds, holds. *)
Lemma cell_holds_mix_cf : forall ly (rd1 rd2 rd' : reader) c, cell_holds B ly rd1 c -> cell_holds B ly rd2 c ->
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
   rd' (aeval B ly (c_at c) + k) = rd1 (aeval B ly (c_at c) + k) \/ rd' (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
  cell_holds B ly rd' c.
Proof.
intros ly rd1 rd2 rd' c H1 H2 Hm. unfold cell_holds in *. cbv zeta in *. destruct (c_val c) as [e|m v].
- intros k Hk. destruct (Hm (Z.of_nat k) ltac:(lia)) as [E|E]; rewrite E; [exact (H1 k Hk) | exact (H2 k Hk)].
- destruct (Hm 0 ltac:(lia)) as [E|E]; rewrite Z.add_0_r in E; rewrite E; assumption.
Qed.

(* DGif1.v:900 *)
Lemma le_byte_hb1_cf : forall hb1, 0 <= hb1 < 256 -> YG0f.le_byte (2 + 256 * hb1) 4 1 = hb1.
Proof.
intros hb1 H. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (8 * Z.of_nat 1) with 8.
rewrite (Z.mod_small (2 + 256 * hb1) 4294967296) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace (2 + 256 * hb1) with (2 + hb1 * 256) by ring. rewrite Z.div_add by lia. change (2 / 256) with 0. rewrite Z.add_0_l.
apply Z.mod_small. lia.
Qed.

(* The internal allocator's initialized cells at a memory that satisfies ial_post_cf (DGif1.v:1231-1244 over the
   symbol table's fields). *)
Lemma ial_cells_of_post_cf : forall ly S (W : world im_segs) mem, st_internal_inited S = true -> ial_post_cf B W mem ->
  Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (ialloc_cells B S) /\
  Forall (range_zero B ly (aview im_segs (w_H W) mem)) (ialloc_zero B).
Proof.
intros ly S W mem HI IALP. unfold ial_post_cf in IALP. cbv zeta in IALP. destruct IALP as (I1 & I2 & I3 & I4 & I5).
unfold ialloc_cells, ialloc_zero. rewrite HI. split.
- apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_cf _ _ _ _ _ 0 I1). lia. }
  apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (val_mem_aview_cf _ _ _ _ _ 0 I2). lia. }
  apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval].
    replace (as_ialloc_lo B + (as_ialloc_w B - as_ialloc_lo B)) with (as_ialloc_w B) by lia.
    intros kk Hkk. exact (val_mem_aview_cf _ _ _ _ _ kk I3 Hkk). }
  apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval].
    replace (as_ialloc_lo B + (as_ialloc_w B - as_ialloc_lo B + 8)) with (as_ialloc_w B + 8) by lia.
    replace (as_ialloc_lo B + (as_ialloc_w B - as_ialloc_lo B + 16)) with (as_ialloc_w B + 16) by lia.
    intros kk Hkk. exact (val_mem_aview_cf _ _ _ _ _ kk I4 Hkk). }
- assert (ZR : forall a0, as_ialloc_lo B <= a0 < as_ialloc_w B \/ as_ialloc_w B + 16 <= a0 < as_ialloc_hi B ->
    aview im_segs (w_H W) mem a0 = Some 0).
  { intros a0 Ha0. unfold aview. rewrite (I5 a0 Ha0). reflexivity. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *; apply ZR; lia.
Qed.

(* ================================================================================================================ *)
(* 2. Geometry of ARmcf that the frames below read (image-free: the layout's extents and the symbol table).          *)
Section g.
Variables (ly : alayout) (S : astate) (Hp : list Z) (rd : reader).
Hypothesis M : ARmcf B ly S Hp rd.

Lemma g_img : fst (ly_img ly) = kImgLo /\ 0 < snd (ly_img ly) /\ kImgLo + snd (ly_img ly) <= kImgEnd.
Proof. pose proof (lo_img _ (amc_layout _ _ _ _ _ M)) as (I0 & I1 & I2 & _). auto. Qed.

Lemma g_static_img : forall a, Exists (in_zr a) (as_owned_static B) -> in_zr a (ly_img ly).
Proof.
intros a H. apply Exists_exists in H as (r & Hr & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
unfold in_zr. lia.
Qed.

Lemma g_zsh_img : forall r, In r (as_zero_shadow B) -> fst (ly_img ly) <= fst r /\ fst r + snd r <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros r Hr. pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; right; exact Hr)) as [Z1 Z2].
unfold zr_sub in *. lia.
Qed.

Lemma g_inst_img : forall a, as_inst B <= a < as_inst B + 3632 -> in_zr a (ly_img ly).
Proof.
intros a Ha. apply g_static_img.
pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amc_syms _ _ _ _ _ M)) (as_inst B, 3632) ltac:(cbn; tauto)) as X.
apply Exists_exists in X as (r & Hr & [S1 S2]). cbn [fst snd] in S1, S2. apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia.
Qed.

(* An owned extent other than the thread object, against the stack, the image and the thread object. *)
Lemma g_oext : forall i x sz a, nth_error (owned_extents ly) i = Some (x, sz) -> (i <> 2)%nat -> x <= a < x + sz ->
  4096 <= a < ASAN_CEIL /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly) /\ ~ (ly_T ly <= a < ly_T ly + kThreadObjSize).
Proof.
intros i x sz a He Hi Ha. pose proof (amc_layout _ _ _ _ _ M) as LO.
assert (Hi8 : (i < 8)%nat).
{ assert (HL : (i < length (owned_extents ly))%nat) by (apply nth_error_Some; rewrite He; discriminate).
  unfold owned_extents in HL. cbn [length] in HL. lia. }
assert (HS : nth_error (static_extents ly) i = Some (x, sz)) by (unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He).
destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (x, sz); split; [exact (nth_error_In _ _ He) | unfold in_zr; cbn; lia]))
  as (AA & NS & NI).
pose proof (app_addr_below_ceil a AA) as BC.
pose proof (SX_cf B ly S Hp rd M i 2 _ _ HS eq_refl Hi) as DT. unfold zdisjoint in DT. cbn [fst snd] in DT.
dsplits; try lia; assumption.
Qed.

Lemma g_T : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize ->
  4096 <= a < ASAN_CEIL /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly).
Proof.
intros a Ha. pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_T ly, kThreadObjSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn; lia]))
  as (AA & NS & NI).
pose proof (app_addr_below_ceil a AA). dsplits; try lia; assumption.
Qed.

Lemma g_sec : forall e a, In e (sec_extents ly S) -> in_zr a e ->
  4096 <= a < ASAN_CEIL /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly) /\ ~ (ly_T ly <= a < ly_T ly + kThreadObjSize).
Proof.
intros e a He Ha.
destruct (owned_sec_bound_cf B ly S Hp rd a M ltac:(apply Exists_exists; exists e; split; [exact He | exact Ha])) as (AA & NS & NI).
pose proof (app_addr_below_ceil a AA).
pose proof (SECX_cf B ly S Hp rd M e 2 _ He eq_refl) as DT. unfold zdisjoint, in_zr in *. cbn [fst snd] in DT.
dsplits; try lia; assumption.
Qed.

(* The image, against the stack and the thread object. *)
Lemma g_imgx : forall a, in_zr a (ly_img ly) ->
  0 <= a < kImgEnd /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ (ly_T ly <= a < ly_T ly + kThreadObjSize).
Proof.
intros a Ha. pose proof g_img as (I0 & I1 & I2).
pose proof (SX_cf B ly S Hp rd M 8 9 _ _ eq_refl eq_refl ltac:(lia)) as D8.
pose proof (SX_cf B ly S Hp rd M 2 9 _ _ eq_refl eq_refl ltac:(lia)) as D2.
unfold zdisjoint, in_zr in *. cbn [fst snd] in D8, D2. unfold kImgLo in *. dsplits; lia.
Qed.

(* The shadow region, against the stack, the image and the application ranges. *)
Lemma g_shx : forall a, kLowShadowBeg <= a < kHighMemBeg ->
  ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly) /\ ~ (ly_T ly <= a < ly_T ly + kThreadObjSize).
Proof.
intros a Ha. pose proof (lo_top _ (amc_layout _ _ _ _ _ M)) as (_ & _ & _ & _ & _ & _ & T7).
pose proof g_img as (I0 & I1 & I2).
destruct (owned_extents_bound ly (ly_T ly) (amc_layout _ _ _ _ _ M)
  ltac:(apply Exists_exists; exists (ly_T ly, kThreadObjSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn; unfold kThreadObjSize; lia]))
  as (AA & _ & _).
pose proof (proj1 (Forall_forall _ _) (lo_app _ (amc_layout _ _ _ _ _ M)) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as AP.
cbn [fst snd] in AP. ceil. unfold in_app, in_zr, kImgLo, kImgEnd, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. dsplits; lia.
Qed.

Lemma g_chunk : forall x a, In x (st_chunks S) -> ck_base B ly x <= a < ck_base B ly x + ck_extent x ->
  (ly_prim ly <= a < ly_prim ly + kPrimResvSize) \/ (exists e, In e (sec_extents ly S) /\ in_zr a e).
Proof.
intros x a Hx Ha. destruct (ext_zone_cf B ly S Hp rd M x Hx) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- left. unfold kFreeArrayOffset in X2. lia.
- right. exists (ly_sec ly r, ck_extent x + kPage). split; [exact Xin|]. unfold in_zr, kPage in *. cbn [fst snd]. lia.
Qed.

Lemma g_batch : forall b2 a, In b2 (all_batches S) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes ->
  ly_prim ly <= a < ly_prim ly + kPrimResvSize.
Proof.
intros b2 a Hb2 Ha. destruct (batch_geom_cf B ly S Hp rd M b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass (amc_layout _ _ _ _ _ M) ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
unfold kBatchBytes, kFreeArrayOffset in *. lia.
Qed.

(* hs_bounds (YFf0.v:151) *)
Lemma g_hs_bounds : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof.
intros g H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
pose proof (Z.div_le_mono 4096 g 8 ltac:(lia) H1) as X. change (4096 / 8) with 512 in X.
pose proof (Z.div_le_mono g (140737488355328 - 8) 8 ltac:(lia) ltac:(lia)) as Y. change ((140737488355328 - 8) / 8) with 17592186044415 in Y. lia.
Qed.

(* fa_poison_high (YFf0.v:139) *)
Lemma g_fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly S) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof.
intros lo len g Hin Hg. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF.
unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
  pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
  pose proof (wfc_classes _ _ _ _ _ WF c ltac:(lia)) as CL.
  pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3.
  pose proof (mapped_bound_cf (as_universe B) 0 0 0 S c WF ltac:(lia)) as MB. unfold kFreeArrayMax in *.
  unfold fa_base, kFreeArrayOffset in *. unfold region_base in *.
  unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (amc_placed _ _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
  ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. lia.
Qed.

(* A shadow byte the relation reads lies in the shadow region. *)
Lemma g_ashadow_sh : forall g v, g mod 8 = 0 -> ashadow B ly S g = Some v ->
  kLowShadowBeg <= shadow_addr g < kHighMemBeg /\ 4096 <= g /\ g + 8 <= kHighMemEnd.
Proof.
intros g v Hg8 HS. unfold ashadow in HS.
assert (GB : 4096 <= g /\ g + 8 <= kHighMemEnd).
{ destruct (find_chunk_at B ly (st_chunks S) g) as [x|] eqn:F.
  - apply find_chunk_at_In in F as [Hx Hgx]. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (X1 & X2 & X3 & _).
    unfold in_app in X1. apply Z.mod_divide in Hg8 as [c Hc]; [|lia]. apply Z.mod_divide in X3 as [c' Hc']; [|lia].
    ceil; unfold ASAN_CEIL, kHighMemEnd in *. nia.
  - destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
    pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). pose proof (g_fa_poison_high lo len g Hin Hg) as [Y1 Y2].
    apply Z.mod_divide in Hg8 as [c Hc]; [|lia]. ceil; unfold ASAN_CEIL, kHighMemEnd in *. nia. }
split; [apply g_hs_bounds; lia | exact GB].
Qed.

(* The zero-shadow ranges' bytes lie in the shadow region. *)
Lemma g_zsh_sh : forall r i, In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 ->
  kLowShadowBeg <= shadow_addr (fst r) + i < kHighMemBeg.
Proof.
intros r i Hr Hi. pose proof (amc_layout _ _ _ _ _ M) as LO.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi |- *.
- pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _ & T7). unfold page_aligned in T5. apply Z.mod_divide in T5 as [s0 Hs0]; [|lia].
  assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
  { unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by lia.
    replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
  rewrite E8. pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
  apply g_hs_bounds; unfold kHighMemBeg, kHighMemEnd in *; lia.
- pose proof (g_zsh_img r Hr) as [Z1 Z2]. pose proof g_img as (I0 & I1 & I2).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ M)) r Hr) as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct r as [lo len]. cbn [fst snd] in *. apply Z.mod_divide in Q3 as [c Hc]; [|lia].
  assert (E8 : shadow_addr lo + i = shadow_addr (lo + 8 * i)).
  { unfold shadow_addr. rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
  rewrite E8. pose proof (Z.mul_div_le len 8 ltac:(lia)).
  apply g_hs_bounds; unfold kImgLo, kImgEnd, kHighMemEnd in *; lia.
Qed.
(* An owned extent is in the application area. *)
Lemma g_app_oext : forall e a, In e (owned_extents ly) -> in_zr a e -> app_addr a.
Proof.
intros e a He Ha. pose proof (proj1 (Forall_forall _ _) (lo_app _ (amc_layout _ _ _ _ _ M)) e He) as AP.
exact (in_app_addr (fst e) (snd e) a AP Ha).
Qed.

(* Every byte of a constant cell is owned, so it is in the address space and off the stack (am_const_owned). *)
Lemma g_const_loc : forall c j, In c (as_const B ly) -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) ->
  0 <= aeval B ly (c_at c) + j < 2 ^ 64 /\ ~ (ly_stk_lo ly <= aeval B ly (c_at c) + j < ly_stk_hi ly).
Proof.
intros c j Hc Hj. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_top _ LO) as (_ & _ & _ & T4 & _ & _ & T7).
pose proof (proj1 (Forall_forall _ _) (amc_const_owned _ _ _ _ _ M) c Hc j Hj) as OW.
unfold owned_core in OW. destruct OW as [O|[O|O]].
- pose proof (owned_static_bound B _ (amc_syms _ _ _ _ _ M) O) as [X1 X2].
  ceil. unfold kImgEnd, kHighMemBeg, kHighMemEnd in *. split; lia.
- assert (OE : Exists (in_zr (aeval B ly (c_at c) + j)) (owned_extents ly)).
  { apply Exists_exists in O as (e & He & Hae). apply Exists_exists. exists e. split; [|exact Hae].
    unfold core_extents in He. unfold owned_extents. cbn in He |- *. tauto. }
  destruct (owned_extents_bound ly _ LO OE) as (AA & NS & _).
  pose proof (app_addr_below_ceil _ AA). ceil. unfold ASAN_CEIL in *. split; [lia | exact NS].
- apply Exists_exists in O as (r & Hr & [H1 H2]). cbn [fst snd] in H1, H2.
  pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (Y1 & Y2 & Y3).
  assert (D1 : fst r / 8 <= fst r) by (apply Z.div_le_upper_bound; lia).
  assert (D2 : (snd r + 7) / 8 <= snd r + 7) by (apply Z.div_le_upper_bound; lia).
  assert (D0 : 0 <= fst r / 8) by (apply Z.div_pos; lia).
  unfold shadow_addr, SHADOW_OFF, kImgEnd, kHighMemBeg, kHighMemEnd in *. split; lia.
Qed.

End g.

(* ================================================================================================================ *)
(* 3. The NULL arm: ARmcf of the ticked state from the return memory (YFf0's section k / preset's AFf0cf over the   *)
(*    image premises).  The walk writes its stack window, the unwinding byte and the internal allocator's zone.     *)
Section n.
Variables (ly : alayout) (S : astate) (Hp : list Z) (rd rd' : reader).
Hypothesis M : ARmcf B ly S Hp rd.
Hypothesis HIZ : FP_IZONE.
Hypothesis HDS : FP_DSTAT.
Local Notation T := (ly_T ly).
Local Notation S' := (dtick S).
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + DGbaseC.DFSTACK <= sp <= ly_stk_hi ly.
Definition DTn (a : Z) : Prop := T + t_unwinding <= a < T + t_unwinding + 1.
Definition DSn (a : Z) : Prop := sp - DGbaseC.DFSTACK <= a < sp.
Definition Dn (a : Z) : Prop := DTn a \/ DSn a \/ dg_izone a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ Dn a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_unw : rd' (T + t_unwinding) = Some 0.
Hypothesis IAL : Forall (cell_holds B ly rd') (ialloc_cells B S) /\ Forall (range_zero B ly rd') (ialloc_zero B).
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
(* the relation's machine cells at the return memory (ARmcf's amc_exh_cell / amc_errb_cells, field round 2): the
   caller frames them off the walk's writes (YGcfInstFreeView section 5) *)
Hypothesis EXHn : exh_cell_cf B ly S' rd'.
Hypothesis ERRn : errb_cells_cf B ly S' rd'.

Lemma n_WF : Wf_cf (as_universe B) S. Proof. exact (amc_wf _ _ _ _ _ M). Qed.
Lemma n_LO : layout_ok ly. Proof. exact (amc_layout _ _ _ _ _ M). Qed.
Lemma n_WS' : Wf_cf (as_universe B) S'. Proof. exact (WfP_cf_tick _ 0 0 0 S n_WF). Qed.

Definition okn (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ Dn a.
Definition okrn (lo len : Z) : Prop := forall a, lo <= a < lo + len -> okn a.
Lemma AGn : forall a, okn a -> rd' a = rd a. Proof. intros a [H1 H2]. exact (AG a H1 H2). Qed.

Lemma okn_out : forall a, 4096 <= a < ASAN_CEIL -> ~ (ly_stk_lo ly <= a < ly_stk_hi ly) -> ~ in_zr a (ly_img ly) ->
  ~ (T <= a < T + kThreadObjSize) -> okn a.
Proof.
intros a H1 H2 H3 H4. split; [ceil; unfold ASAN_CEIL in *; lia|]. intros [X|[X|X]].
- apply H4. unfold DTn, t_unwinding, kThreadObjSize in *. lia.
- apply H2. unfold DSn in X. unfold DGbaseC.DFSTACK in *. lia.
- apply H3. destruct (HIZ a X) as (X1 & _). exact (g_static_img ly S Hp rd M a X1).
Qed.
Lemma okn_oext : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> (i <> 2)%nat -> okrn x sz.
Proof. intros i x sz He Hi a Ha. destruct (g_oext ly S Hp rd M i x sz a He Hi Ha) as (A1 & A2 & A3 & A4). exact (okn_out a A1 A2 A3 A4). Qed.
Lemma okn_T : forall a, T <= a < T + kThreadObjSize -> ~ DTn a -> okn a.
Proof.
intros a Ha ND. destruct (g_T ly S Hp rd M a Ha) as (A1 & A2 & A3). split; [ceil; unfold ASAN_CEIL in *; lia|].
intros [X|[X|X]]; [exact (ND X) | apply A2; unfold DSn, DGbaseC.DFSTACK in *; lia |].
apply A3. destruct (HIZ a X) as (X1 & _). exact (g_static_img ly S Hp rd M a X1).
Qed.
Lemma okn_sec : forall e a, In e (sec_extents ly S) -> in_zr a e -> okn a.
Proof. intros e a He Ha. destruct (g_sec ly S Hp rd M e a He Ha) as (A1 & A2 & A3 & A4). exact (okn_out a A1 A2 A3 A4). Qed.
Lemma okn_img : forall a, in_zr a (ly_img ly) -> ~ dg_izone a -> okn a.
Proof.
intros a Ha NI. destruct (g_imgx ly S Hp rd M a Ha) as (A1 & A2 & A3). split; [unfold kImgEnd in *; lia|].
intros [X|[X|X]]; [apply A3; unfold DTn, t_unwinding, kThreadObjSize in *; lia | apply A2; unfold DSn, DGbaseC.DFSTACK in *; lia | exact (NI X)].
Qed.
Lemma okn_sh : forall a, kLowShadowBeg <= a < kHighMemBeg -> okn a.
Proof.
intros a Ha. destruct (g_shx ly S Hp rd M a Ha) as (A1 & A2 & A3). split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
intros [X|[X|X]]; [apply A3; unfold DTn, t_unwinding, kThreadObjSize in *; lia | apply A1; unfold DSn, DGbaseC.DFSTACK in *; lia |].
apply A2. destruct (HIZ a X) as (X1 & _). exact (g_static_img ly S Hp rd M a X1).
Qed.
Lemma okn_prim : okrn (ly_prim ly) kPrimResvSize. Proof. exact (okn_oext 0 _ _ eq_refl ltac:(lia)). Qed.
Lemma okn_Q : okrn (ly_Q ly) kPtrArrayResv. Proof. exact (okn_oext 1 _ _ eq_refl ltac:(lia)). Qed.
Lemma okn_F : okrn (ly_F ly) kFakeStackSize. Proof. exact (okn_oext 3 _ _ eq_refl ltac:(lia)). Qed.
Lemma okn_NB : okrn (ly_NB ly) kNodesBlockSize. Proof. exact (okn_oext 4 _ _ eq_refl ltac:(lia)). Qed.
Lemma okn_SB : okrn (ly_SB ly) kStoreBlockSize. Proof. exact (okn_oext 5 _ _ eq_refl ltac:(lia)). Qed.
Lemma okn_chunk : forall x a, In x (st_chunks S) -> ck_base B ly x <= a < ck_base B ly x + ck_extent x -> okn a.
Proof.
intros x a Hx Ha. destruct (g_chunk ly S Hp rd M x a Hx Ha) as [P|(e & He & Hae)]; [exact (okn_prim a P) | exact (okn_sec e a He Hae)].
Qed.
Lemma okn_secpage : forall x r o a, In x (st_chunks S) -> ck_beg x = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> okn a.
Proof.
intros x r o a Hx Ebx Ha. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Ebx in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _). apply (okn_sec _ a Gin). unfold in_zr, kPage in *. cbn [fst snd].
pose proof (sec_extents_len_cf B ly S Hp rd M) as SL. pose proof (proj1 (Forall_forall _ _) SL _ Gin) as L. cbn [snd] in L. lia.
Qed.
Lemma okn_batch : forall b2 a, In b2 (all_batches S) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> okn a.
Proof. intros b2 a Hb2 Ha. exact (okn_prim a (g_batch ly S Hp rd M b2 a Hb2 Ha)). Qed.
Lemma okn_rinfo : okrn (ly_rinfo ly) 4096.
Proof.
intros a Ha. apply okn_prim. pose proof (lo_space_in _ n_LO) as [S1 S2]. unfold ly_rinfo, kRegionInfoOff, kSpaceSize in *. lia.
Qed.
Lemma okn_fa : forall c, 1 <= c <= 31 -> okrn (fa_base ly c) kFreeArrayMax.
Proof.
intros c Hc a Ha. apply okn_prim. pose proof (region_in_prim ly c n_LO Hc) as (R1 & R2 & R3 & R4 & R5).
unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.
Lemma okn_inst : okrn (as_inst B) 3632.
Proof. intros a Ha. apply okn_img; [exact (g_inst_img ly S Hp rd M a Ha) | intros X; exact (proj1 (proj2 (proj2 (HIZ a X))) Ha)]. Qed.
Lemma okn_dtab : okrn (as_depot B) (4 * 2 ^ 20 + 32).
Proof.
intros a Ha. assert (Hd : as_depot B <= a < as_depot B + d_map1 + 8 * 32768) by (unfold d_map1; lia).
apply okn_img; [exact (g_static_img ly S Hp rd M a (HDS a (or_introl Hd))) | intros X; exact (proj1 (proj2 (proj2 (proj2 (HIZ a X)))) Hd)].
Qed.
Lemma okn_store : okrn (as_store B) 32.
Proof.
intros a Ha. assert (Hd : as_store B <= a < as_store B + 64) by lia.
apply okn_img; [exact (g_static_img ly S Hp rd M a (HDS a (or_intror Hd))) | intros X; exact (proj2 (proj2 (proj2 (proj2 (HIZ a X)))) Hd)].
Qed.
(* Printf's two cells (field round 3): owned static data (amc_pf_owned), so inside the image, and apart from the
   internal allocator's zone (the unit row PF_APART's first part). *)
Hypothesis HPFn : forall a, pf_byte a -> ~ dg_izone a.
Lemma okn_pf : forall a, pf_byte a -> okn a.
Proof.
intros a Ha. apply okn_img; [exact (g_static_img ly S Hp rd M a (proj1 (proj1 (amc_pf_owned _ _ _ _ _ M) a Ha))) | exact (HPFn a Ha)].
Qed.

Definition cell_in (lo len : Z) (c : acell) : Prop :=
lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len.
Lemma cell_xfer_n : forall c, cell_holds B ly rd c ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> okn (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGn, Hok, Hj. Qed.
Lemma cells_xfer_n : forall L lo len, okrn lo len -> Forall (cell_in lo len) L -> Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. apply Forall_forall. intros c Hc. apply cell_xfer_n; [exact (proj1 (Forall_forall _ _) OLD c Hc)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. apply OK. lia.
Qed.
Lemma batch_cells_within : forall l c, In c (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) c.
Proof.
induction l as [|b2 t IH]; intros c Hc; [destruct Hc|]. cbn [batch_cells] in Hc.
destruct Hc as [<-|[<-|[<-|Hc]]]; try (exists b2; split; [left; reflexivity | unfold cell_in; cbn; lia]).
apply in_app_iff in Hc as [Hc|Hc].
- apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. exists b2. split; [left; reflexivity | unfold cell_in; cbn; lia].
- destruct (IH c Hc) as (b3 & H3 & R3). exists b3. split; [right; exact H3 | exact R3].
Qed.
Lemma OLDn : forall c, In c (acells_cf B ly S) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) c Hc). Qed.
Ltac old_in := apply Forall_forall; intros ? HIN; apply OLDn; unfold acells_cf; rewrite !in_app_iff.
Ltac fcons := apply Forall_cons; [split; cbn; lia|].

Lemma n_cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf S') (zseq 1 31)).
Proof.
change (flat_map (region_cells_cf S') (zseq 1 31)) with (flat_map (region_cells_cf S) (zseq 1 31)).
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
apply (cells_xfer_n _ _ _ okn_rinfo).
- unfold region_cells_cf, region_cells. cbn [removelast]. unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. apply Forall_nil.
- old_in. left. apply in_flat_map. exists c. split; [apply In_zseq; lia | exact HIN].
Qed.
Lemma okrn_cache : okrn (T + t_cache + 80) (80 * 31).
Proof. intros a Ha. apply okn_T; unfold DTn, t_cache, t_unwinding, kThreadObjSize in *; lia. Qed.
Lemma n_cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
change (flat_map (cache_cells S') (zseq 1 31)) with (flat_map (cache_cells S) (zseq 1 31)).
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
apply (cells_xfer_n _ _ _ okrn_cache).
- pose proof (wfc_classes _ _ _ _ _ n_WF c ltac:(lia)) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
  unfold cache_cells, cell_in, t_cache. destruct (st_cache_inited S).
  + destruct WC as [PM PL]. repeat fcons. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
    apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
  + repeat fcons. apply Forall_nil.
- old_in. right; left. apply in_flat_map. exists c. split; [apply In_zseq; lia | exact HIN].
Qed.
Lemma n_cells_chunk : forall x, In x (st_chunks S) -> Forall (cell_holds B ly rd') (chunk_cells x).
Proof.
intros x Hx. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (E1 : forall d, aeval B ly (aoff (sptr_exp (ck_beg x)) d) = ck_base B ly x + d)
  by (intros d; exact (EA_cf B ly S Hp rd M x d Hx)).
assert (E2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg x)) d) d') = ck_base B ly x + d + d')
  by (intros d d'; exact (EA2_cf B ly S Hp rd M x d d' Hx)).
assert (E0 : aeval B ly (sptr_exp (ck_beg x)) = ck_base B ly x) by reflexivity.
apply (cells_xfer_n _ (ck_base B ly x) (ck_extent x)); [intros a Ha; exact (okn_chunk x a Hx Ha) | |].
- pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
  unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
  + repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?E2, ?E1, ?E0;
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz x) 16); [apply Forall_nil|].
    repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?E2, ?E1, ?E0;
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_in. do 2 right; left. apply in_flat_map. exists x. split; [exact Hx | exact HIN].
Qed.
Lemma n_cells_sec : Forall (cell_holds B ly rd') (sec_cells S').
Proof.
change (sec_cells S') with (sec_cells S).
pose proof (wfc_secondary _ _ _ _ _ n_WF) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells S)) by (old_in; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof okn_inst as OKI.
apply Forall_cons; [apply (cell_xfer_n _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_reserved; lia|].
apply Forall_cons; [apply (cell_xfer_n _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_n; lia|].
apply Forall_cons; [apply (cell_xfer_n _ O3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- apply (cells_xfer_n _ _ _ okn_Q); [|exact O4]. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc. apply in_flat_map in Hc as (x & Hx & Hc).
  destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
  assert (OKP : okrn (ly_sec ly r) 32) by (intros a Ha; eapply (okn_secpage x r o a Hx Ebx); unfold kPage; lia).
  apply (cell_xfer_n _ Oc). intros j Hj. apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; lia.
Qed.
Lemma n_cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
change (quar_cells S') with (quar_cells S).
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells S)) by (old_in; do 4 right; left; exact HIN).
pose proof okn_inst as OKI.
unfold quar_cells, qc_cells in OLDQ |- *.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
assert (OKQ : okrn (T + t_qc) 32) by (intros a Ha; apply okn_T; unfold DTn, t_qc, t_unwinding, kThreadObjSize in *; lia).
apply Forall_cons; [apply (cell_xfer_n _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_cmutex; lia|].
apply Forall_cons; [apply (cell_xfer_n _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_rmutex; lia|].
apply Forall_app. split.
- apply Forall_cons; [apply (cell_xfer_n _ O3); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
  apply Forall_cons; [apply (cell_xfer_n _ O4); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
  apply Forall_cons; [apply (cell_xfer_n _ O5); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
  apply Forall_cons; [apply (cell_xfer_n _ O6); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
  apply Forall_forall. intros c Hc. apply (cell_xfer_n _ (proj1 (Forall_forall _ _) OT c Hc)).
  destruct (batch_cells_within (qc_list (st_qthread S)) c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ n_WF)) b2 ltac:(unfold all_batches; apply in_app_iff; left; exact I2)) as [L1 L2].
  apply (okn_batch b2); [unfold all_batches; apply in_app_iff; left; exact I2 | unfold kBatchSlots, kBatchBytes in *; lia].
- apply Forall_cons; [apply (cell_xfer_n _ G1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_n _ G2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_n _ G3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_n _ G4); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_forall. intros c Hc. apply (cell_xfer_n _ (proj1 (Forall_forall _ _) OG c Hc)).
  destruct (batch_cells_within _ c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ n_WF)) b2 ltac:(unfold all_batches; apply in_app_iff; right; exact I2)) as [L1 L2].
  apply (okn_batch b2); [unfold all_batches; apply in_app_iff; right; exact I2 | unfold kBatchSlots, kBatchBytes in *; lia].
Qed.
Lemma n_cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
change (fs_cells S') with (fs_cells S).
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells S)) by (old_in; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. apply (cells_xfer_n _ _ _ okn_F); [|exact OLDF].
unfold cell_in, kFakeStackSize. fcons. fcons.
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma n_cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof.
change (depot_cells ly S') with (depot_cells ly S).
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly S)) by (old_in; do 6 right; left; exact HIN).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *.
apply Forall_cons_iff in OLDD as [O1 OLDD]. apply Forall_cons_iff in OLDD as [O2 OLDD]. apply Forall_cons_iff in OLDD as [O3 OLDD]. apply Forall_cons_iff in OLDD as [O4 _].
pose proof okn_dtab as OKD. pose proof okn_store as OKS. unfold d_nuniq, d_map1, s_total, s_block0 in *.
apply Forall_cons; [apply (cell_xfer_n _ O1); intros j Hj; apply OKD; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer_n _ O2); intros j Hj; apply OKD; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer_n _ O3); intros j Hj; apply OKS; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer_n _ O4); intros j Hj; apply OKS; cbn in Hj |- *; lia|]. apply Forall_nil.
Qed.
Lemma n_cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. apply Forall_cons; [|apply Forall_nil]. cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r, NEW_unw. reflexivity.
Qed.
Lemma n_cells_all : Forall (cell_holds B ly rd') (acells_cf B ly S').
Proof.
unfold acells_cf. rewrite !Forall_app. dsplits.
- exact n_cells_regions.
- exact n_cells_caches.
- change (st_chunks S') with (st_chunks S). apply Forall_flat_map'. intros x Hx. exact (n_cells_chunk x Hx).
- exact n_cells_sec.
- exact n_cells_quar.
- exact n_cells_fs.
- exact n_cells_depot.
- exact (proj1 IAL).
- exact n_cells_thread.
Qed.
Lemma n_fa : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. change (reg S' c) with (reg S c) in Hi, Hv.
rewrite AGn; [exact (amc_fa _ _ _ _ _ M c i v Hc Hi Hv kk Hkk)|].
pose proof (wfc_classes _ _ _ _ _ n_WF c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
apply (okn_fa c Hc). lia.
Qed.
Lemma n_flags : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hpos. change (frames S') with (frames S). rewrite AGn; [exact (amc_flags _ _ _ _ _ M cid pos Hc Hpos)|].
pose proof (flag_off_bounds cid pos Hc Hpos) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *. apply okn_F. unfold kFakeStackSize. lia.
Qed.
Lemma n_depot : depot_ok B ly rd' S'.
Proof.
pose proof (amc_depot _ _ _ _ _ M) as Xdepot. change (depot_ok B ly rd' S') with (depot_ok B ly rd' S).
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
- intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros kk Hkk. rewrite AGn; [exact (H2 kk Hkk)|].
  apply okn_dtab. unfold d_tab_words in Hb. lia.
- intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
  assert (NB : depot_ids S <= 4097).
  { unfold depot_ids. pose proof (depot_len_bound _ _ (amc_universe _ _ _ _ _ M) (wfc_depot _ _ _ _ _ n_WF)) as LL.
    unfold DEPOT_MAX in LL. lia. }
  assert (OR : forall kk, 0 <= kk < 16 -> okn (ly_NB ly + 16 * id + kk)) by (intros kk Hkk; apply okn_NB; unfold kNodesBlockSize; lia).
  split; intros kk Hkk; rewrite AGn; auto; [apply OR; lia|].
  replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by lia. apply OR. lia.
Qed.
Lemma n_shadow : shadow_ok_cf B ly Hp rd' S'.
Proof.
intros g v Hg8 HS'. change (ashadow B ly S' g) with (ashadow B ly S g) in HS'.
pose proof (amc_shadow _ _ _ _ _ M g v Hg8 HS') as SH.
rewrite AGn; [exact SH|]. apply okn_sh. exact (proj1 (g_ashadow_sh ly S Hp rd M g v Hg8 HS')).
Qed.
Lemma n_zshadow : zshadow_ok B ly rd'.
Proof.
pose proof (amc_zshadow _ _ _ _ _ M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *.
change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGn; [exact Z0|]. apply okn_sh. exact (g_zsh_sh ly S Hp rd M r i Hr Hi).
Qed.
Theorem n_ARmcf : ARmcf B ly S' Hp rd'.
Proof.
constructor.
- exact n_WS'.
- exact (amc_universe _ _ _ _ _ M).
- exact (amc_syms _ _ _ _ _ M).
- exact n_LO.
- change (sec_placed ly S') with (sec_placed ly S). exact (amc_placed _ _ _ _ _ M).
- exact CONST'.
- exact (amc_const_owned _ _ _ _ _ M).
- exact n_cells_all.
- exact n_fa.
- exact n_flags.
- exact n_depot.
- exact n_shadow.
- exact n_zshadow.
- change (ajunk_cf B ly S') with (ajunk_cf B ly S). exact (Forall_range_vis_keep B ly rd rd' _ VIS (amc_junk _ _ _ _ _ M)).
- change (aareas S') with (aareas S). exact (Forall_range_vis_keep B ly rd rd' _ VIS (amc_areas _ _ _ _ _ M)).
- change (aclient S') with (aclient S). exact (Forall_range_vis_keep B ly rd rd' _ VIS (amc_client _ _ _ _ _ M)).
- exact (proj2 IAL).
- exact (amc_tsd _ _ _ _ _ M).
- exact (amc_static_img _ _ _ _ _ M).
- change (st_chunks S') with (st_chunks S). exact (amc_hp_live _ _ _ _ _ M).
- change (xs_placed_cf ly S') with (xs_placed_cf ly S). exact (amc_xs_placed _ _ _ _ _ M).
- exact EXHn.
- exact ERRn.
- exact (amc_cells_owned _ _ _ _ _ M).
- exact (pf_cells_move_cf B ly S Hp rd rd' okn M (amc_pf_owned _ _ _ _ _ M) (fun a _ Ha => AGn a Ha) okn_pf
    (amc_pf_cells _ _ _ _ _ M)).
- exact (amc_pf_owned _ _ _ _ _ M).
Qed.
(* What the caller needs in one piece (so that one application fixes every section argument): the relation of the
   ticked state, and the agreement on the shadow bytes of the free granules that ahs_transfer_cf asks for. *)
Theorem n_post_parts : ARmcf B ly S' Hp rd' /\ (forall g, g mod 8 = 0 -> in_app g 8 -> rd' (shadow_addr g) = rd (shadow_addr g)).
Proof.
split; [exact n_ARmcf|]. intros g Hg Hga. apply AGn. apply okn_sh. apply g_hs_bounds.
- exact (proj1 Hga).
- ceil. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *. lia.
Qed.
End n.

(* A fold over the chunk list does not see a chunk replaced by one with the same beginning and request. *)
Lemma fold_chunk_mid : forall (f : chunk -> Z -> Z) (l1 : list chunk) x y l2, (forall acc, f x acc = f y acc) ->
  fold_right f 0 (l1 ++ x :: l2) = fold_right f 0 (l1 ++ y :: l2).
Proof. intros f l1 x y l2 E. induction l1 as [|h t IH]; cbn [app fold_right]; [apply E | rewrite IH; reflexivity]. Qed.

(* ================================================================================================================ *)
(* 4. The arm whose last batch has room: the state of the quarantined chunk (the model side).                       *)
Section cs.
Variables (ly : alayout) (S : astate) (Hp : list Z) (rd : reader).
Hypothesis M : ARmcf B ly S Hp rd.
Variables (k : chunk) (lastb : batch) (initr : list batch).
Hypothesis Hk : In k (st_chunks S).
Hypothesis Hst : ck_state k = CAllocated.
Hypothesis Hrev : rev (qc_list (st_qthread S)) = lastb :: initr.
Variables (z : Z) (tr : list Z).
Hypothesis HII : st_internal_inited S = true.
Local Notation S' := (qfin_c S k z tr).
Ltac zcase := unfold qfin_c, qx, YFl0C.depot_after, dtick; destruct (z =? 0); reflexivity.

Lemma cs_regions : st_regions S' = st_regions S.   Proof. zcase. Qed.
Lemma cs_cache : st_cache S' = st_cache S.         Proof. zcase. Qed.
Lemma cs_cinit : st_cache_inited S' = st_cache_inited S. Proof. zcase. Qed.
Lemma cs_secs : st_secs S' = st_secs S.             Proof. zcase. Qed.
Lemma cs_sec_arr : st_sec_arr S' = st_sec_arr S.    Proof. zcase. Qed.
Lemma cs_sec_res : st_sec_reserved S' = st_sec_reserved S. Proof. zcase. Qed.
Lemma cs_fs : st_fs S' = st_fs S.                   Proof. zcase. Qed.
Lemma cs_qglobal : st_qglobal S' = st_qglobal S.    Proof. zcase. Qed.
Lemma cs_qthread : st_qthread S' = qc_push (st_qthread S) (qk k) None. Proof. zcase. Qed.
Lemma cs_depot : st_depot S' = st_depot (YFl0C.depot_after z tr (dtick S)). Proof. reflexivity. Qed.
Lemma cs_inited : st_internal_inited S' = true.
Proof. unfold qfin_c, qx, YFl0C.depot_after, dtick; destruct (z =? 0); cbn [st_internal_inited set_qthread set_chunks set_depot set_nev]; exact HII. Qed.
Lemma cs_chunks : st_chunks S' = upd_chunk (st_chunks S) (qk k).
Proof. unfold qfin_c, qx. cbn [st_chunks set_qthread set_chunks]. f_equal. zcase. Qed.
Lemma cs_reg : forall c, reg S' c = reg S c.        Proof. intros c. unfold reg. rewrite cs_regions. reflexivity. Qed.
Lemma cs_cacheq : forall c, cache S' c = cache S c. Proof. intros c. unfold cache. rewrite cs_cache. reflexivity. Qed.
Lemma cs_frames : frames S' = frames S.             Proof. unfold frames. rewrite cs_fs. reflexivity. Qed.

Lemma cs_k'_beg : ck_beg (qk k) = ck_beg k.         Proof. reflexivity. Qed.
Lemma cs_k'_req : ck_req (qk k) = ck_req k.         Proof. reflexivity. Qed.

Lemma cs_split : exists l1 l2, st_chunks S = l1 ++ k :: l2 /\ st_chunks S' = l1 ++ qk k :: l2 /\
  ~ In (ck_beg k) (map ck_beg l1) /\ ~ In (ck_beg k) (map ck_beg l2).
Proof.
destruct (In_split_beg _ _ Hk (wfc_chunks_nodup _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as (l1 & l2 & E & N1 & N2).
exists l1, l2. split; [exact E|]. split; [|split; assumption].
rewrite cs_chunks, E. apply upd_chunk_present; [reflexivity | exact N1].
Qed.

Lemma cs_qlist : qc_list (st_qthread S) = rev initr ++ [lastb].
Proof. rewrite <- (rev_involutive (qc_list (st_qthread S))), Hrev. reflexivity. Qed.
Lemma cs_qlist' : qc_list (st_qthread S') = rev initr ++ [mkBatch (b_self lastb) (b_items lastb ++ [qk k])].
Proof. rewrite cs_qthread. cbn [qc_push qc_list]. rewrite Hrev. reflexivity. Qed.
Lemma cs_qbytes : qc_bytes (st_qthread S') = qc_bytes (st_qthread S) + ck_n k.
Proof. rewrite cs_qthread. reflexivity. Qed.
Lemma cs_batches : all_batches S = (rev initr ++ [lastb]) ++ qc_list (st_qglobal S).
Proof. unfold all_batches. rewrite cs_qlist. reflexivity. Qed.
Lemma cs_batches' : all_batches S' = (rev initr ++ [mkBatch (b_self lastb) (b_items lastb ++ [qk k])]) ++ qc_list (st_qglobal S).
Proof. unfold all_batches. rewrite cs_qlist', cs_qglobal. reflexivity. Qed.
Lemma cs_lastb_in : In lastb (all_batches S).
Proof. rewrite cs_batches. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity. Qed.

Lemma cs_sec_extents : sec_extents ly S' = sec_extents ly S.
Proof.
destruct cs_split as (l1 & l2 & E & E' & _). unfold sec_extents. rewrite E', E.
apply (YFfl.flat_map_mid _ l1 (qk k) k l2). reflexivity.
Qed.
Lemma cs_fa_poison : fa_poison_ranges ly S' = fa_poison_ranges ly S.
Proof.
destruct cs_split as (l1 & l2 & E & E' & _). unfold fa_poison_ranges, reg. rewrite cs_regions, E', E.
rewrite (YFfl.flat_map_mid _ l1 (qk k) k l2) by reflexivity. reflexivity.
Qed.
Lemma cs_budget : abudget_cf S' = abudget_cf S.
Proof.
destruct cs_split as (l1 & l2 & E & E' & _).
(* the hull term (field round 3: CfParams' cf_hull) moves only with st_secs and the live hulls: cf_hull_frame *)
assert (LH : sec_live_hulls S' = sec_live_hulls S).
{ unfold sec_live_hulls. rewrite E', E. rewrite !(fold_chunk_mid _ l1 (qk k) k l2) by reflexivity. reflexivity. }
unfold abudget_cf. rewrite (cf_hull_frame S S' cs_secs LH).
unfold prim_committed, sec_live_bytes, sec_live_hulls, errb_cap_cf, errb_e.
rewrite cs_regions, cs_sec_res, cs_secs, E', E.
rewrite !(fold_chunk_mid _ l1 (qk k) k l2) by reflexivity.
reflexivity.
Qed.
Lemma cs_ledger : forall md, ALedger_cf im_segs ly S md -> ALedger_cf im_segs ly S' md.
Proof.
intros md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17]. constructor; try assumption.
- destruct L4 as (pieces & P1 & P2). exists pieces. split; [|exact P2].
  unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in P1 |- *. rewrite cs_regions. exact P1.
- rewrite cs_sec_extents. exact L7.
- unfold errb_zone. rewrite cs_sec_extents.
  replace (xs_cf ly S') with (xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite cs_secs; reflexivity). exact L8.
- unfold eager_cf, prim_committed, errb_zone. rewrite cs_regions, cs_sec_res, cs_sec_extents.
  replace (xs_cf ly S') with (xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite cs_secs; reflexivity). exact L9.
- rewrite cs_sec_extents. exact L12.
- replace (xs_cf ly S') with (xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite cs_secs; reflexivity). exact L17.
Qed.
(* the quarantined chunk is no longer a client byte *)
Lemma cs_client : forall a, aclient_byte B ly S' a -> aclient_byte B ly S a.
Proof.
intros a [(x & Hx & Hsx & Hr)|(fp & Hcp & Hr)].
- left. destruct cs_split as (l1 & l2 & E & E' & N1 & N2). rewrite E' in Hx.
  assert (Hne : x <> qk k) by (intros ->; cbn [ck_state qk] in Hsx; discriminate Hsx).
  exists x. split; [rewrite E; apply in_app_iff; apply in_app_iff in Hx as [Hx|[Hx|Hx]];
    [left; exact Hx | exfalso; exact (Hne (eq_sym Hx)) | right; right; exact Hx]|]. split; [exact Hsx | exact Hr].
- right. exists fp. rewrite cs_frames in Hcp. split; [exact Hcp | exact Hr].
Qed.
(* qtight of the final state (YFex.qtight_S' over the cf sums) *)
Lemma cs_qtight : qc_bytes (st_qthread S) + ck_n k <= kQuarantineCacheMax -> qtight S -> qtight S'.
Proof.
intros Hc (T1 & T2 & T3). destruct cs_split as (l1 & l2 & E & E' & N1 & N2).
assert (EN : ck_n (qk k) = ck_n k) by reflexivity.
assert (QN : quar_n S' = quar_n S + ck_n k).
{ unfold quar_n. rewrite E', E, !quar_nl_split_cf.
  replace (is_alloc k) with true by (unfold is_alloc; rewrite Hst; reflexivity).
  replace (is_alloc (qk k)) with false by reflexivity. rewrite EN. lia. }
assert (QD : queued_n S' = queued_n S + ck_n k).
{ rewrite !queued_n_eq_cf, cs_qlist', cs_qlist, cs_qglobal, !flat_map_app.
  cbn [flat_map b_items]. rewrite !app_nil_r, !items_n_app, (items_n_cons_cf (qk k) []), items_n_nil_cf, EN. lia. }
unfold qtight. rewrite cs_qbytes, cs_qglobal, QN, QD. split; [exact Hc|]. split; [exact T2 | lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The memory side: the walk's write set and the relation at the return memory (YFex's section c0 over ARmcf).       *)
Variable rd' : reader.
Hypothesis HIZ : FP_IZONE.
Hypothesis HDS : FP_DSTAT.
Hypothesis HDZ : FP_DZONE ly.
Variable hb1 : Z.
Hypothesis Hhb1 : 0 <= hb1 < 256 /\ Z.land hb1 127 = 17.
Hypothesis Hroom : Z.of_nat (length (b_items lastb)) < kBatchSlots.
Hypothesis WFS' : Wf_cf (as_universe B) S'.
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + DGbaseC.DFSTACK <= sp <= ly_stk_hi ly.
Local Notation T := (ly_T ly).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Local Notation Bv := (ly_space ly + b_self lastb).
Local Notation SLOTv := (ly_space ly + b_self lastb + 24 + 8 * Z.of_nat (length (b_items lastb))).

Definition DKc (a : Z) : Prop := (u - 16 <= a < u - 8) \/ (u <= a < u + 8).
Definition DBc (a : Z) : Prop := (Bv + 8 <= a < Bv + 24) \/ (SLOTv <= a < SLOTv + 8).
Definition DSc (a : Z) : Prop := sp - DGbaseC.DFSTACK <= a < sp.
Definition DHc (a : Z) : Prop := shadow_addr u <= a < shadow_addr u + (nn + 7) / 8.
Definition Dc (a : Z) : Prop :=
  DGgiC.WINT ly a \/ DKc a \/ DBc a \/ DSc a \/ dg_izone a \/ dg_dzone ly a \/ DHc a.

Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ Dc a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_hdr : forall i, (i < 4)%nat -> rd' (u - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i).
Hypothesis NEW_n : forall i, (i < 4)%nat -> rd' (u - 12 + Z.of_nat i) = Some (YG0f.le_byte nn 4 i).
Hypothesis NEW_qs : forall i, (i < 8)%nat -> rd' (T + t_qc + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (qc_list (st_qthread S)))) 8 i).
Hypothesis NEW_qf : forall i, (i < 8)%nat -> rd' (T + t_qc + 8 + Z.of_nat i) =
  Some (YG0f.le_byte (match qc_list (st_qthread S) with [] => 0 | b0 :: _ => ly_space ly + b_self b0 end) 8 i).
Hypothesis NEW_ql : forall i, (i < 8)%nat -> rd' (T + t_qc + 16 + Z.of_nat i) = Some (YG0f.le_byte Bv 8 i).
Hypothesis NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes (st_qthread S) + nn) 8 i).
Hypothesis NEW_unw : rd' (T + t_unwinding) = Some 0.
Hypothesis NEW_bb : forall i, (i < 8)%nat -> rd' (Bv + 8 + Z.of_nat i) = Some (YG0f.le_byte (b_bytes lastb + nn) 8 i).
Hypothesis NEW_bc : forall i, (i < 8)%nat -> rd' (Bv + 16 + Z.of_nat i) =
  Some (YG0f.le_byte (Z.of_nat (length (b_items lastb)) + 1) 8 i).
Hypothesis NEW_slot : forall i, (i < 8)%nat -> rd' (SLOTv + Z.of_nat i) = Some (YG0f.le_byte (u - 16) 8 i).
Hypothesis NEW_sh : forall a, DHc a -> rd a <> None -> rd' a = Some shHeapFreed.
Hypothesis IAL : Forall (cell_holds B ly rd') (ialloc_cells B S') /\ Forall (range_zero B ly rd') (ialloc_zero B).
Hypothesis DEP : CLdepot.depot_mem_ok B ly (YFl0C.depot_after z tr (dtick S)) rd'.
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
(* the freed block's base is not a hidden head (the free site's premise fpre_hp_cf) *)
Hypothesis HPu : ~ In u Hp.
(* the relation's machine cells at the return memory (ARmcf's amc_exh_cell / amc_errb_cells, field round 2) *)
Hypothesis EXHc : exh_cell_cf B ly S' rd'.
Hypothesis ERRc : errb_cells_cf B ly S' rd'.

Lemma cWF : Wf_cf (as_universe B) S. Proof. exact (amc_wf _ _ _ _ _ M). Qed.
Lemma cLO : layout_ok ly. Proof. exact (amc_layout _ _ _ _ _ M). Qed.
Lemma cKF : cfacts_cf B ly S k. Proof. exact (chunk_facts_cf B ly S Hp rd k M Hk). Qed.
Lemma cHu : u = ck_base B ly k + ck_rz k. Proof. pose proof cKF as (_ & _ & _ & G4 & _). exact G4. Qed.
Lemma cER : ck_rz k + (nn + 7) / 8 * 8 <= ck_extent k /\ 1 <= nn /\ 0 <= (nn + 7) / 8 /\ nn <= (nn + 7) / 8 * 8 < nn + 8.
Proof. exact (ext_rounded_cf B ly S Hp rd M k Hk). Qed.
Lemma cU8 : u mod 8 = 0 /\ ck_base B ly k mod 8 = 0 /\ ck_rz k mod 8 = 0.
Proof. exact (u_al8_cf B ly S Hp rd M k Hk). Qed.

(* the batches of the quarantine are pairwise apart, and the last batch is apart from every other *)
Lemma c_bnodup : List.NoDup (map b_self (all_batches S)).
Proof.
pose proof (wfc_classes _ _ _ _ _ cWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _).
apply NoDup_app_iff in ND as (_ & ND & _). rewrite batch_offs_24 in ND.
clear - ND. induction (all_batches S) as [|x t IH]; cbn in *; [constructor|].
inversion ND as [|y l N1 N2]; subst. constructor; [|exact (IH N2)].
intros Hin. apply N1. apply in_map_iff in Hin as (x' & E & Hx'). apply in_map_iff. exists x'. split; [lia | exact Hx'].
Qed.
Lemma c_bapart : forall b1 b2, In b1 (all_batches S) -> In b2 (all_batches S) -> b_self b1 <> b_self b2 ->
  zdisjoint (ly_space ly + b_self b1, kBatchBytes) (ly_space ly + b_self b2, kBatchBytes).
Proof.
intros b1 b2 H1 H2 NE. destruct (batch_geom_cf B ly S Hp rd M b1 H1) as (x1 & E1 & P1 & A1 & _).
destruct (batch_geom_cf B ly S Hp rd M b2 H2) as (x2 & E2 & P2 & A2 & _).
unfold zdisjoint, kBatchBytes in *. cbn [fst snd]. rewrite E1, E2.
apply Z.mod_divide in A1 as [q1 Hq1]; [|lia]. apply Z.mod_divide in A2 as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros ->; apply NE; lia). nia.
Qed.
Lemma c_self_ne : forall b2, In b2 (rev initr) \/ In b2 (qc_list (st_qglobal S)) ->
  In b2 (all_batches S) /\ b_self b2 <> b_self lastb.
Proof.
intros b2 Hb2. pose proof c_bnodup as ND. rewrite cs_batches in ND |- *. rewrite !map_app in ND. cbn [map] in ND.
split; [rewrite !in_app_iff; cbn; tauto|].
rewrite <- app_assoc in ND. apply NoDup_app_iff in ND as (N1 & N2 & N3). cbn in N2. inversion N2 as [|y l N4 N5]; subst.
intros E. destruct Hb2 as [Hb2|Hb2].
- apply (N3 (b_self b2)); [apply in_map; exact Hb2 | left; symmetry; exact E].
- apply N4. rewrite <- E. apply in_map. exact Hb2.
Qed.

(* the block's shadow lies in the shadow region *)
Lemma cDH_sh : forall a, DHc a -> kLowShadowBeg <= a < kHighMemBeg.
Proof.
intros a Ha. pose proof cKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof cER as (ER & NN1 & NN2 & NN3). pose proof cU8 as (U8 & B8 & R8). pose proof cHu as EU.
assert (LO4 : 4096 <= ck_base B ly k) by (clear - G1; unfold in_app in G1; lia).
apply Z.mod_divide in U8 as [c Hc]; [|lia].
assert (E1 : shadow_addr u + (nn + 7) / 8 = shadow_addr (u + 8 * ((nn + 7) / 8))).
{ unfold shadow_addr. rewrite Hc. replace (c * 8 + 8 * ((nn + 7) / 8)) with ((c + (nn + 7) / 8) * 8) by lia.
  rewrite !Z_div_mult by lia. lia. }
assert (H1 : kLowShadowBeg <= shadow_addr u < kHighMemBeg).
{ apply (g_hs_bounds); ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia. }
assert (H2 : kLowShadowBeg <= shadow_addr (u + 8 * ((nn + 7) / 8 - 1)) < kHighMemBeg).
{ apply (g_hs_bounds); ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia. }
assert (E2 : shadow_addr (u + 8 * ((nn + 7) / 8 - 1)) = shadow_addr u + ((nn + 7) / 8 - 1)).
{ unfold shadow_addr. rewrite Hc. replace (c * 8 + 8 * ((nn + 7) / 8 - 1)) with ((c + ((nn + 7) / 8 - 1)) * 8) by lia.
  rewrite !Z_div_mult by lia. lia. }
unfold DHc in Ha. rewrite E2 in H2. lia.
Qed.

Definition okc (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ Dc a.
Definition okrc (lo len : Z) : Prop := forall a, lo <= a < lo + len -> okc a.
Lemma AGc : forall a, okc a -> rd' a = rd a. Proof. intros a [H1 H2]. exact (AG a H1 H2). Qed.

(* An application byte off every window the walk writes. *)
Lemma okc_app : forall a, app_addr a -> ~ (ly_stk_lo ly <= a < ly_stk_hi ly) -> ~ in_zr a (ly_img ly) ->
  ~ (T <= a < T + kThreadObjSize) -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
  ~ (Bv <= a < Bv + kBatchBytes) -> ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) ->
  ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> okc a.
Proof.
intros a AA NST NIM NT NK NB NNB NSB. pose proof cER as (ER & NN1 & NN2 & NN3). pose proof cHu as EU.
pose proof cKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
assert (Q8 : 8 <= (nn + 7) / 8 * 8).
{ pose proof (Z.div_le_mono 8 (nn + 7) 8 ltac:(lia) ltac:(lia)) as D. change (8 / 8) with 1 in D. lia. }
pose proof (app_addr_below_ceil a AA) as BC.
split; [ceil; unfold ASAN_CEIL in *; lia|]. intros [X|[X|[X|[X|[X|[X|X]]]]]].
- apply NT. unfold DGgiC.WINT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
- apply NK. unfold DKc in X. lia.
- apply NB. unfold DBc in X. unfold kBatchSlots, kBatchBytes in *. lia.
- apply NST. unfold DSc, DGbaseC.DFSTACK in *. lia.
- apply NIM. destruct (HIZ a X) as (X1 & _). exact (g_static_img ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply NIM. exact (g_static_img ly S Hp rd M a (HDS a (or_introl FP))).
    * exact (NNB FP).
    * exact (NSB FP).
    * apply NIM. exact (g_static_img ly S Hp rd M a (HDS a (or_intror FP))).
  + apply NIM. exact (g_static_img ly S Hp rd M a OS).
- pose proof (cDH_sh a X) as [S1 S2]. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* A shadow byte off the block's shadow. *)
Lemma okc_sh : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ DHc a -> okc a.
Proof.
intros a Ha ND. pose proof cKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof cER as (ER & NN1 & NN2 & NN3). pose proof cHu as EU.
assert (Q8 : 8 <= (nn + 7) / 8 * 8).
{ pose proof (Z.div_le_mono 8 (nn + 7) 8 ltac:(lia) ltac:(lia)) as D. change (8 / 8) with 1 in D. lia. }
pose proof (g_shx ly S Hp rd M a Ha) as (NS & NIM & NT).
assert (BPRIM : forall a0, Bv <= a0 < Bv + kBatchBytes -> app_addr a0).
{ intros a0 H0. apply (g_app_oext ly S Hp rd M (ly_prim ly, kPrimResvSize) a0 ltac:(unfold owned_extents; cbn; tauto)).
  unfold in_zr. cbn [fst snd]. exact (g_batch ly S Hp rd M lastb a0 cs_lastb_in H0). }
assert (NBP : forall a0, ly_NB ly <= a0 < ly_NB ly + kNodesBlockSize -> app_addr a0)
  by (intros a0 H0; apply (g_app_oext ly S Hp rd M (ly_NB ly, kNodesBlockSize) a0 ltac:(unfold owned_extents; cbn; tauto));
      unfold in_zr; cbn [fst snd]; exact H0).
assert (SBP : forall a0, ly_SB ly <= a0 < ly_SB ly + kStoreBlockSize -> app_addr a0)
  by (intros a0 H0; apply (g_app_oext ly S Hp rd M (ly_SB ly, kStoreBlockSize) a0 ltac:(unfold owned_extents; cbn; tauto));
      unfold in_zr; cbn [fst snd]; exact H0).
split; [ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|]. intros [X|[X|[X|[X|[X|[X|X]]]]]].
- apply NT. unfold DGgiC.WINT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
- unfold DKc in X. unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
- assert (HA0 : app_addr a) by (apply BPRIM; unfold DBc in X; unfold kBatchSlots, kBatchBytes in *; lia).
  unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
- apply NS. unfold DSc, DGbaseC.DFSTACK in *. lia.
- apply NIM. destruct (HIZ a X) as (X1 & _). exact (g_static_img ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply NIM. exact (g_static_img ly S Hp rd M a (HDS a (or_introl FP))).
    * pose proof (NBP a FP) as HA0. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
    * pose proof (SBP a FP) as HA0. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
    * apply NIM. exact (g_static_img ly S Hp rd M a (HDS a (or_intror FP))).
  + apply NIM. exact (g_static_img ly S Hp rd M a OS).
- exact (ND X).
Qed.

(* The regions the relation reads, each off the walk's windows. *)
Lemma okc_kbatch : ly_prim ly <= Bv /\ Bv + kBatchBytes <= ly_prim ly + kPrimResvSize /\
  Bv + kBatchBytes <= region_base ly kBatchClass + kFreeArrayOffset /\ region_base ly kBatchClass <= Bv.
Proof.
destruct (batch_geom_cf B ly S Hp rd M lastb cs_lastb_in) as (x & Ex & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass cLO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
unfold kBatchBytes, kFreeArrayOffset in *. dsplits; lia.
Qed.
Lemma okc_koff : (exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly k /\
    ck_base B ly k + ck_extent k <= region_base ly c + kFreeArrayOffset /\
    ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
  (exists e, In e (sec_extents ly S) /\ fst e <= ck_base B ly k /\ ck_base B ly k + ck_extent k <= fst e + snd e).
Proof.
pose proof cKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c0 p0] eqn:Eb; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
  pose proof (region_in_prim ly (prim_class o) cLO ltac:(lia)) as (R1 & R2 & _).
  exists (prim_class o). dsplits; lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  exists (ly_sec ly r, sec_map_size (ck_req k)). cbn [fst snd]. dsplits; [exact Gin | unfold kPage in *; lia | unfold kPage in *; lia].
Qed.
Lemma okc_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
  ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> ~ (Bv <= a < Bv + kBatchBytes) -> okc a.
Proof.
intros a Ha NK NB. pose proof (g_app_oext ly S Hp rd M (ly_prim ly, kPrimResvSize) a ltac:(unfold owned_extents; cbn; tauto)
  ltac:(unfold in_zr; cbn [fst snd]; lia)) as AA.
apply (okc_app a AA);
  [ exact (proj1 (proj2 (owned_extents_bound ly a cLO ltac:(apply Exists_exists; exists (ly_prim ly, kPrimResvSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn; lia]))))
  | exact (proj2 (proj2 (owned_extents_bound ly a cLO ltac:(apply Exists_exists; exists (ly_prim ly, kPrimResvSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn; lia]))))
  | | exact NK | exact NB | | ];
  [ pose proof (SX_cf B ly S Hp rd M 0 2 _ _ eq_refl eq_refl ltac:(lia)) as D
  | pose proof (SX_cf B ly S Hp rd M 0 4 _ _ eq_refl eq_refl ltac:(lia)) as D
  | pose proof (SX_cf B ly S Hp rd M 0 5 _ _ eq_refl eq_refl ltac:(lia)) as D ];
  unfold zdisjoint in D; cbn [fst snd] in D; unfold kThreadObjSize, kNodesBlockSize, kStoreBlockSize in *; lia.
Qed.
Lemma okc_oext : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> (i <> 0)%nat -> (i <> 2)%nat ->
  (i <> 4)%nat -> (i <> 5)%nat -> okrc x sz.
Proof.
intros i x sz He Hi0 Hi2 Hi4 Hi5 a Ha.
pose proof (g_app_oext ly S Hp rd M (x, sz) a (nth_error_In _ _ He) ltac:(unfold in_zr; cbn [fst snd]; lia)) as AA.
destruct (g_oext ly S Hp rd M i x sz a He Hi2 Ha) as (A1 & A2 & A3 & A4).
assert (Hi8 : (i < 8)%nat).
{ assert (HL : (i < length (owned_extents ly))%nat) by (apply nth_error_Some; rewrite He; discriminate).
  unfold owned_extents in HL. cbn [length] in HL. lia. }
assert (HS : nth_error (static_extents ly) i = Some (x, sz)) by (unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He).
pose proof (SX_cf B ly S Hp rd M i 0 _ _ HS eq_refl Hi0) as D0.
pose proof (SX_cf B ly S Hp rd M i 4 _ _ HS eq_refl Hi4) as D4.
pose proof (SX_cf B ly S Hp rd M i 5 _ _ HS eq_refl Hi5) as D5.
pose proof (anyX_cf B ly S Hp rd M k i _ Hk HS ltac:(lia)) as DK.
pose proof okc_kbatch as (KB1 & KB2 & _).
unfold zdisjoint in D0, D4, D5, DK. cbn [fst snd] in D0, D4, D5, DK.
apply (okc_app a AA A2 A3 A4); unfold kNodesBlockSize, kStoreBlockSize, kBatchBytes in *; lia.
Qed.
Lemma okc_Q : okrc (ly_Q ly) kPtrArrayResv. Proof. exact (okc_oext 1 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). Qed.
Lemma okc_F : okrc (ly_F ly) kFakeStackSize. Proof. exact (okc_oext 3 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). Qed.
Lemma okc_C : okrc (ly_C ly) 256. Proof. exact (okc_oext 6 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). Qed.
Lemma okc_T : forall a, T <= a < T + kThreadObjSize -> ~ DGgiC.WINT ly a -> okc a.
Proof.
intros a Ha NW. pose proof cHu as EU. pose proof cER as (ER & NN1 & NN2 & NN3).
pose proof cKF as (G1 & G2 & G3 & G4 & G5 & _).
assert (Q8 : 8 <= (nn + 7) / 8 * 8)
  by (pose proof (Z.div_le_mono 8 (nn + 7) 8 ltac:(lia) ltac:(lia)) as D; change (8 / 8) with 1 in D; lia).
pose proof (g_app_oext ly S Hp rd M (ly_T ly, kThreadObjSize) a ltac:(unfold owned_extents; cbn; tauto)
  ltac:(unfold in_zr; cbn [fst snd]; lia)) as AA.
destruct (g_T ly S Hp rd M a Ha) as (A1 & A2 & A3).
pose proof (SX_cf B ly S Hp rd M 2 0 _ _ eq_refl eq_refl ltac:(lia)) as D0.
pose proof (SX_cf B ly S Hp rd M 2 4 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (SX_cf B ly S Hp rd M 2 5 _ _ eq_refl eq_refl ltac:(lia)) as D5.
pose proof (anyX_cf B ly S Hp rd M k 2 _ Hk eq_refl ltac:(lia)) as DK.
pose proof okc_kbatch as (KB1 & KB2 & _).
unfold zdisjoint in D0, D4, D5, DK. cbn [fst snd] in D0, D4, D5, DK.
split; [ceil; unfold ASAN_CEIL in *; lia|]. intros [X|[X|[X|[X|[X|[X|X]]]]]].
- exact (NW X).
- unfold DKc in X. unfold kThreadObjSize, kBatchBytes in *. lia.
- unfold DBc in X. unfold kBatchSlots, kBatchBytes, kThreadObjSize in *. lia.
- apply A2. unfold DSc, DGbaseC.DFSTACK in *. lia.
- apply A3. destruct (HIZ a X) as (X1 & _). exact (g_static_img ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply A3. exact (g_static_img ly S Hp rd M a (HDS a (or_introl FP))).
    * unfold kNodesBlockSize, kThreadObjSize in *. lia.
    * unfold kStoreBlockSize, kThreadObjSize in *. lia.
    * apply A3. exact (g_static_img ly S Hp rd M a (HDS a (or_intror FP))).
  + apply A3. exact (g_static_img ly S Hp rd M a OS).
- pose proof (cDH_sh a X) as [SH1 SH2]. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma okc_k : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ DKc a -> okc a.
Proof.
intros a Ha ND. pose proof cKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof cER as (ER & NN1 & NN2 & NN3). pose proof cHu as EU.
assert (AA : app_addr a) by (exact (in_app_addr _ _ a G1 Ha)).
destruct (chunk_apart_cf B ly S Hp rd k a M Hk Ha) as (NIM & NST).
pose proof (anyX_cf B ly S Hp rd M k 2 _ Hk eq_refl ltac:(lia)) as D2.
pose proof (anyX_cf B ly S Hp rd M k 4 _ Hk eq_refl ltac:(lia)) as D4.
pose proof (anyX_cf B ly S Hp rd M k 5 _ Hk eq_refl ltac:(lia)) as D5.
pose proof (batch_vs_chunk_cf B ly S Hp rd M lastb k cs_lastb_in Hk) as DB.
unfold zdisjoint in D2, D4, D5, DB. cbn [fst snd] in D2, D4, D5, DB.
split; [pose proof (app_addr_below_ceil a AA); ceil; unfold ASAN_CEIL in *; lia|].
intros [X|[X|[X|[X|[X|[X|X]]]]]].
- unfold DGgiC.WINT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
- exact (ND X).
- unfold DBc in X. unfold kBatchSlots, kBatchBytes in *. lia.
- apply NST. unfold DSc, DGbaseC.DFSTACK in *. lia.
- apply NIM. destruct (HIZ a X) as (X1 & _). exact (g_static_img ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply NIM. exact (g_static_img ly S Hp rd M a (HDS a (or_introl FP))).
    * unfold kNodesBlockSize in *. lia.
    * unfold kStoreBlockSize in *. lia.
    * apply NIM. exact (g_static_img ly S Hp rd M a (HDS a (or_intror FP))).
  + apply NIM. exact (g_static_img ly S Hp rd M a OS).
- pose proof (cDH_sh a X) as [SH1 SH2]. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma okc_b : forall a, Bv <= a < Bv + kBatchBytes -> ~ DBc a -> okc a.
Proof.
intros a Ha ND. pose proof okc_kbatch as (KB1 & KB2 & KB3 & KB4).
pose proof cHu as EU. pose proof cER as (ER & NN1 & NN2 & NN3). pose proof cKF as (G1 & G2 & G3 & G4 & G5 & _).
assert (Q8 : 8 <= (nn + 7) / 8 * 8)
  by (pose proof (Z.div_le_mono 8 (nn + 7) 8 ltac:(lia) ltac:(lia)) as D; change (8 / 8) with 1 in D; lia).
pose proof (g_app_oext ly S Hp rd M (ly_prim ly, kPrimResvSize) a ltac:(unfold owned_extents; cbn; tauto)
  ltac:(unfold in_zr; cbn [fst snd]; unfold kBatchBytes in *; lia)) as AA.
destruct (owned_extents_bound ly a cLO ltac:(apply Exists_exists; exists (ly_prim ly, kPrimResvSize);
  split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn [fst snd]; unfold kBatchBytes in *; lia])) as (_ & NST & NIM).
pose proof (SX_cf B ly S Hp rd M 0 2 _ _ eq_refl eq_refl ltac:(lia)) as D2.
pose proof (SX_cf B ly S Hp rd M 0 4 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (SX_cf B ly S Hp rd M 0 5 _ _ eq_refl eq_refl ltac:(lia)) as D5.
pose proof (batch_vs_chunk_cf B ly S Hp rd M lastb k cs_lastb_in Hk) as DB.
unfold zdisjoint in D2, D4, D5, DB. cbn [fst snd] in D2, D4, D5, DB.
split; [pose proof (app_addr_below_ceil a AA); ceil; unfold ASAN_CEIL in *; lia|].
intros [X|[X|[X|[X|[X|[X|X]]]]]].
- unfold DGgiC.WINT, t_qc, t_unwinding, t_stats, kThreadObjSize, kBatchBytes in *. lia.
- unfold DKc in X. unfold kBatchBytes in *. lia.
- exact (ND X).
- apply NST. unfold DSc, DGbaseC.DFSTACK in *. unfold kBatchBytes in *. lia.
- apply NIM. destruct (HIZ a X) as (X1 & _). exact (g_static_img ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply NIM. exact (g_static_img ly S Hp rd M a (HDS a (or_introl FP))).
    * unfold kNodesBlockSize, kBatchBytes in *. lia.
    * unfold kStoreBlockSize, kBatchBytes in *. lia.
    * apply NIM. exact (g_static_img ly S Hp rd M a (HDS a (or_intror FP))).
  + apply NIM. exact (g_static_img ly S Hp rd M a OS).
- pose proof (cDH_sh a X) as [SH1 SH2]. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma okc_other : forall x a, In x (st_chunks S) -> ck_beg x <> ck_beg k ->
  ck_base B ly x <= a < ck_base B ly x + ck_extent x -> okc a.
Proof.
intros x a Hx Hne Ha. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
assert (AA : app_addr a) by (exact (in_app_addr _ _ a G1 Ha)).
destruct (chunk_apart_cf B ly S Hp rd x a M Hx Ha) as (NIM & NST).
pose proof (anyX_cf B ly S Hp rd M x 2 _ Hx eq_refl ltac:(lia)) as D2.
pose proof (anyX_cf B ly S Hp rd M x 4 _ Hx eq_refl ltac:(lia)) as D4.
pose proof (anyX_cf B ly S Hp rd M x 5 _ Hx eq_refl ltac:(lia)) as D5.
pose proof (batch_vs_chunk_cf B ly S Hp rd M lastb x cs_lastb_in Hx) as DB.
pose proof (chunks_disjoint_cf B ly S Hp rd x k M Hx Hk Hne) as DK.
unfold zdisjoint in D2, D4, D5, DB, DK. cbn [fst snd] in D2, D4, D5, DB, DK.
apply (okc_app a AA NST NIM); unfold kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kBatchBytes in *; lia.
Qed.
Lemma okc_batch_other : forall b2 a, In b2 (all_batches S) -> b_self b2 <> b_self lastb ->
  ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> okc a.
Proof.
intros b2 a Hb2 Hne Ha. apply (okc_prim a (g_batch ly S Hp rd M b2 a Hb2 Ha)).
- pose proof (batch_vs_chunk_cf B ly S Hp rd M b2 k Hb2 Hk) as DB.
  unfold zdisjoint in DB. cbn [fst snd] in DB. unfold kBatchBytes in *. lia.
- pose proof (c_bapart b2 lastb Hb2 cs_lastb_in Hne) as DB.
  unfold zdisjoint in DB. cbn [fst snd] in DB. unfold kBatchBytes in *. lia.
Qed.
(* a secondary's page header is apart from the freed chunk (YFex.secmap_vs_chunk at the cf facts) *)
Lemma c_secmap_vs_k : forall x r o, In x (st_chunks S) -> ck_beg x = PSec r o -> ck_beg x <> ck_beg k ->
  zdisjoint (ly_sec ly r, sec_map_size (ck_req x)) (ck_base B ly k, ck_extent k).
Proof.
intros x r o Hx Ebx Hne.
pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
rewrite Ebx in GG. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof cKF as (_ & _ & _ & _ & _ & _ & _ & _ & GK).
destruct (ck_beg k) as [|o'|r' o'|c' p'] eqn:Ebk; try solve [destruct GK].
- apply zdisjoint_sym.
  exact (prim_vs_secmap_cf B ly S Hp rd k o' (ly_sec ly r, sec_map_size (ck_req x)) M Hk Ebk Gin).
- destruct GK as (-> & _ & Kbase & Kext & Kin & _).
  pose proof (secmaps_disjoint_cf B ly S Hp rd x k r kPage r' kPage M Hx Hk Ebx Ebk ltac:(rewrite Ebk; exact Hne)) as DJ.
  unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. lia.
Qed.
Lemma okc_secpage : forall x r o a, In x (st_chunks S) -> ck_beg x = PSec r o ->
  ly_sec ly r <= a < ly_sec ly r + kPage -> okc a.
Proof.
intros x r o a Hx Ebx Ha. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
rewrite Ebx in GG. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (proj1 (Forall_forall _ _) (sec_extents_len_cf B ly S Hp rd M) _ Gin) as L. cbn [snd] in L.
destruct (g_sec ly S Hp rd M (ly_sec ly r, sec_map_size (ck_req x)) a Gin ltac:(unfold in_zr, kPage in *; cbn [fst snd]; lia))
  as (A1 & NST & NIM & NT).
destruct (owned_sec_bound_cf B ly S Hp rd a M ltac:(apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req x));
  split; [exact Gin | unfold in_zr, kPage in *; cbn [fst snd]; lia])) as (AA & _ & _).
pose proof (SECX_cf B ly S Hp rd M _ 0 _ Gin eq_refl) as D0.
pose proof (SECX_cf B ly S Hp rd M _ 4 _ Gin eq_refl) as D4.
pose proof (SECX_cf B ly S Hp rd M _ 5 _ Gin eq_refl) as D5.
pose proof okc_kbatch as (KB1 & KB2 & _).
assert (DK : ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k)).
{ intros HK. destruct okc_koff as [(c & Hc & X1 & X2 & X3 & X4)|(e & He & E1 & E2)].
  - unfold zdisjoint in D0. cbn [fst snd] in D0. unfold kPage, kFreeArrayOffset in *. lia.
  - destruct (sptr_eqb (ck_beg k) (PSec r kPage)) eqn:Eq.
    + apply sptr_eqb_spec in Eq. pose proof cKF as (_ & _ & _ & _ & _ & _ & _ & _ & GK). rewrite Eq in GK.
      destruct GK as (_ & _ & Kbase & _). unfold kPage in *. lia.
    + assert (Hne : ck_beg x <> ck_beg k) by (rewrite Ebx; intros E'; rewrite <- E', sptr_eqb_refl in Eq; discriminate).
      pose proof (c_secmap_vs_k x r kPage Hx Ebx Hne) as DD. unfold zdisjoint in DD. cbn [fst snd] in DD.
      unfold kPage in *. lia. }
assert (DBb : ~ (Bv <= a < Bv + kBatchBytes)).
{ intros HB. pose proof (proj2 (amc_placed _ _ _ _ _ M)) as PD.
  pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize)
    (sec_extents ly S) (static_extents ly) eq_refl PD Gin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
  unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold kPage, kBatchBytes in *. lia. }
unfold zdisjoint in D0, D4, D5. cbn [fst snd] in D0, D4, D5.
apply (okc_app a AA NST NIM NT DK DBb); unfold kPage, kNodesBlockSize, kStoreBlockSize in *; lia.
Qed.
Lemma okc_rinfo : okrc (ly_rinfo ly) 4096.
Proof.
intros a Ha. pose proof (lo_space_in _ cLO) as [SP1 SP2]. pose proof okc_kbatch as (KB1 & KB2 & KB3 & KB4).
assert (RB : region_base ly kBatchClass = ly_space ly + 24 * 2 ^ 32)
  by (unfold region_base; rewrite region_off_eq by (unfold kBatchClass; lia); unfold kBatchClass; lia).
apply (okc_prim a); [unfold ly_rinfo, kRegionInfoOff, kSpaceSize in *; lia | |].
- destruct okc_koff as [(c & Hc & X1 & X2 & X3 & X4)|(e & He & E1 & E2)].
  + assert (RC : region_base ly c = ly_space ly + c * 2 ^ 32)
      by (unfold region_base; rewrite region_off_eq by lia; reflexivity).
    unfold ly_rinfo, kRegionInfoOff, kFreeArrayOffset in *. rewrite RC in X2.
    assert (c * 2 ^ 32 <= 30 * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  + pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl
      (proj2 (amc_placed _ _ _ _ _ M)) He ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
    unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold ly_rinfo, kRegionInfoOff, kSpaceSize in *. lia.
- rewrite RB in KB3. unfold ly_rinfo, kRegionInfoOff, kFreeArrayOffset, kBatchBytes in *. lia.
Qed.
Lemma okc_fa : forall c, 1 <= c <= 31 -> okrc (fa_base ly c) kFreeArrayMax.
Proof.
intros c Hc a Ha. pose proof (region_in_prim ly c cLO Hc) as (R1 & R2 & R3 & R4 & R5).
pose proof okc_kbatch as (KB1 & KB2 & KB3 & KB4).
assert (RC : region_base ly c = ly_space ly + c * 2 ^ 32)
  by (unfold region_base; rewrite region_off_eq by lia; reflexivity).
assert (RB : region_base ly kBatchClass = ly_space ly + 24 * 2 ^ 32)
  by (unfold region_base; rewrite region_off_eq by (unfold kBatchClass; lia); unfold kBatchClass; lia).
assert (EF : fa_base ly c = region_base ly c + kFreeArrayOffset) by (unfold fa_base, region_base; lia).
apply (okc_prim a); [unfold kFreeArrayOffset, kFreeArrayMax in *; lia | |].
- destruct okc_koff as [(c' & Hc' & X1 & X2 & X3 & X4)|(e & He & E1 & E2)].
  + assert (RC' : region_base ly c' = ly_space ly + c' * 2 ^ 32)
      by (unfold region_base; rewrite region_off_eq by lia; reflexivity).
    destruct (Z.eq_dec c' c) as [->|Hne].
    * unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
    * destruct (Z.lt_ge_cases c' c).
      -- assert (HM : (c' + 1) * 2 ^ 32 <= c * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; lia).
         unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
      -- assert (HM : (c + 1) * 2 ^ 32 <= c' * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; lia).
         unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
  + pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl
      (proj2 (amc_placed _ _ _ _ _ M)) He ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
    unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
- destruct (Z.eq_dec c kBatchClass) as [->|Hne].
  + unfold kFreeArrayOffset, kFreeArrayMax, kBatchBytes in *. lia.
  + destruct (Z.lt_ge_cases c kBatchClass).
    * assert (HM : (c + 1) * 2 ^ 32 <= 24 * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; unfold kBatchClass in *; lia).
      unfold kFreeArrayOffset, kFreeArrayMax, kBatchBytes in *. lia.
    * assert (HM : (24 + 1) * 2 ^ 32 <= c * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; unfold kBatchClass in *; lia).
      unfold kFreeArrayOffset, kFreeArrayMax, kBatchBytes in *. lia.
Qed.
Lemma okc_img : forall a, in_zr a (ly_img ly) -> ~ dg_izone a -> ~ dg_dzone ly a -> okc a.
Proof.
intros a Ha NI ND. destruct (g_imgx ly S Hp rd M a Ha) as (A1 & A2 & A3).
pose proof okc_kbatch as (KB1 & KB2 & _).
pose proof (SX_cf B ly S Hp rd M 0 9 _ _ eq_refl eq_refl ltac:(lia)) as D0.
pose proof (SX_cf B ly S Hp rd M 4 9 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (SX_cf B ly S Hp rd M 5 9 _ _ eq_refl eq_refl ltac:(lia)) as D5.
pose proof (anyX_cf B ly S Hp rd M k 9 _ Hk eq_refl ltac:(lia)) as DK.
pose proof (g_img ly S Hp rd M) as (I0 & I1 & I2).
unfold zdisjoint, in_zr in *. cbn [fst snd] in D0, D4, D5, DK.
split; [unfold kImgEnd in *; lia|]. intros [X|[X|[X|[X|[X|[X|X]]]]]].
- apply A3. unfold DGgiC.WINT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
- unfold DKc in X. pose proof cHu as EU. pose proof cER as (ER & NN1 & NN2 & NN3).
  pose proof cKF as (G1 & G2 & G3 & G4 & G5 & _).
  assert (Q8 : 8 <= (nn + 7) / 8 * 8)
    by (pose proof (Z.div_le_mono 8 (nn + 7) 8 ltac:(lia) ltac:(lia)) as D; change (8 / 8) with 1 in D; lia).
  unfold kImgLo in *. lia.
- unfold DBc in X. unfold kBatchSlots, kBatchBytes, kImgLo in *. lia.
- apply A2. unfold DSc, DGbaseC.DFSTACK in *. lia.
- exact (NI X).
- exact (ND X).
- pose proof (cDH_sh a X) as [SH1 SH2]. unfold kImgEnd, kLowShadowBeg in *. lia.
Qed.
(* Printf's two cells (field round 3): owned static data (amc_pf_owned), so inside the image, and apart from the two
   zones the walk writes there (the unit row PF_APART at this layout). *)
Hypothesis HPFc : forall a, pf_byte a -> ~ dg_izone a /\ ~ dg_dzone ly a.
Lemma okc_pf : forall a, pf_byte a -> okc a.
Proof.
intros a Ha. destruct (HPFc a Ha) as [NI ND].
exact (okc_img a (g_static_img ly S Hp rd M a (proj1 (proj1 (amc_pf_owned _ _ _ _ _ M) a Ha))) NI ND).
Qed.
Lemma okc_inst : okrc (as_inst B) 3632.
Proof.
intros a Ha. apply okc_img.
- exact (g_inst_img ly S Hp rd M a Ha).
- intros X. exact (proj1 (proj2 (proj2 (HIZ a X))) Ha).
- intros X. exact (proj1 (proj2 (HDZ a) X) Ha).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cells of the final state at the return memory (YFex's cells_* over acells_cf).                                *)
Lemma OLDc : forall c, In c (acells_cf B ly S) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) c Hc). Qed.
Ltac old_inc := apply Forall_forall; intros ? HIN; apply OLDc; unfold acells_cf; rewrite !in_app_iff.
Ltac fconsc := apply Forall_cons; [split; cbn; lia|].
Lemma cell_xfer_c : forall c, cell_holds B ly rd c ->
  (forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> okc (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGc, Hok, Hj. Qed.
Lemma cells_xfer_c : forall L lo len, okrc lo len -> Forall (cell_in ly lo len) L ->
  Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. apply Forall_forall. intros c Hc. apply cell_xfer_c; [exact (proj1 (Forall_forall _ _) OLD c Hc)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. apply OK. lia.
Qed.
Lemma cEA : forall y d, In y (st_chunks S) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. intros y d Hy. exact (EA_cf B ly S Hp rd M y d Hy). Qed.
Lemma cEA2 : forall y d d', In y (st_chunks S) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. intros y d d' Hy. exact (EA2_cf B ly S Hp rd M y d d' Hy). Qed.
Lemma cEA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. reflexivity. Qed.
Lemma c_hdr_addr : forall y, In y (st_chunks S) -> aeval B ly (sptr_exp (ck_hdr y)) = ck_base B ly y + ck_rz y - kChunkHeaderSize.
Proof.
intros y Hy. pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_hdr, ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma c_hdr_bytes : YG0f.le_byte (3 + 256 * hb1) 4 0 = 3 /\ YG0f.le_byte (3 + 256 * hb1) 4 1 = hb1 /\
  YG0f.le_byte (3 + 256 * hb1) 4 2 = 0 /\ YG0f.le_byte (3 + 256 * hb1) 4 3 = 0.
Proof.
destruct Hhb1 as [R _]. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small _ 4294967296) by lia.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 0) with 1. change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
change (2 ^ 24) with 16777216. rewrite Z.div_1_r. dsplits.
- rewrite (Z.mul_comm 256 hb1), Z_mod_plus_full. reflexivity.
- rewrite Z.add_comm, (Z.mul_comm 256 hb1), Z_div_plus_full_l by lia. change (3 / 256) with 0. rewrite Z.add_0_r.
  apply Z.mod_small. lia.
- rewrite Z.div_small by lia. reflexivity.
- rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma c_cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells_cf, region_cells.
rewrite cs_reg. cbn [removelast].
apply (cells_xfer_c _ _ _ okc_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fconsc. apply Forall_nil.
- old_inc. left. apply in_flat_map. exists c. split; [apply In_zseq; lia|].
  unfold region_cells_cf, region_cells. cbn [removelast]. exact HIN.
Qed.
Lemma okrc_cache : okrc (T + t_cache + 80) (80 * 31).
Proof. intros a Ha. apply okc_T; unfold DGgiC.WINT, t_cache, t_qc, t_unwinding, t_stats, kThreadObjSize in *; lia. Qed.
Lemma c_cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold cache_cells. rewrite cs_cacheq, cs_cinit.
apply (cells_xfer_c _ _ _ okrc_cache).
- pose proof (wfc_classes _ _ _ _ _ cWF c ltac:(lia)) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC.
  pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
  unfold cell_in, t_cache. destruct (st_cache_inited S).
  + destruct WC as [PM PL]. repeat fconsc. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv).
    cbn [fst snd c_at c_w z4 c4 aeval aoff]. apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
  + repeat fconsc. apply Forall_nil.
- old_inc. right; left. apply in_flat_map. exists c. split; [apply In_zseq; lia|].
  unfold cache_cells. exact HIN.
Qed.
Lemma c_cells_chunk_other : forall x, In x (st_chunks S) -> ck_beg x <> ck_beg k -> Forall (cell_holds B ly rd') (chunk_cells x).
Proof.
intros x Hx Hne. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
apply (cells_xfer_c _ (ck_base B ly x) (ck_extent x)); [intros a Ha; exact (okc_other x a Hx Hne Ha) | |].
- unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
  + repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(cEA2 x), ?(cEA x) by exact Hx;
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz x) 16); [apply Forall_nil|].
    repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?(cEA2 x), ?(cEA x), ?(cEA0 x) by exact Hx;
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_inc. do 2 right; left. apply in_flat_map. exists x. split; [exact Hx | exact HIN].
Qed.
Lemma c_cells_chunk_k : Forall (cell_holds B ly rd') (chunk_cells (qk k)).
Proof.
pose proof cKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof cHu as EU.
pose proof cER as (ER & NN1 & NN2 & NN3). pose proof c_hdr_bytes as (HB0 & HB1 & HB2 & HB3). destruct Hhb1 as [_ HM].
assert (Hk1 : forall d, aeval B ly (aoff (sptr_exp (ck_beg (qk k))) d) = ck_base B ly k + d) by (intros d; exact (cEA k d Hk)).
assert (Hk2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg (qk k))) d) d') = ck_base B ly k + d + d')
  by (intros d d'; exact (cEA2 k d d' Hk)).
assert (EU16 : ck_base B ly k + (ck_rz k - 16) = u - 16) by lia.
unfold chunk_cells. change (ck_rz (qk k)) with (ck_rz k). change (ck_n (qk k)) with nn. unfold kChunkHeaderSize.
apply Forall_app. split.
- apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w z1 c1]. rewrite Hk1, EU16. change (aeval B ly (ANum (hdr_state (qk k)))) with 3.
    intros kk Hkk. rewrite NEW_hdr by lia. destruct kk; [|lia]. rewrite HB0. reflexivity. }
  apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w]. rewrite Hk2, EU16. exists hb1. split; [|exact HM].
    change (u - 16 + 1) with (u - 16 + Z.of_nat 1). rewrite (NEW_hdr 1%nat) by lia. rewrite HB1. reflexivity. }
  apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w z2 c2]. rewrite Hk2, EU16. change (aeval B ly (ANum 0)) with 0. intros kk Hkk.
    replace (u - 16 + 2 + Z.of_nat kk) with (u - 16 + Z.of_nat (2 + kk)) by lia. rewrite NEW_hdr by lia.
    destruct kk as [|[|]]; cbn [Nat.add]; [rewrite HB2; reflexivity | rewrite HB3; reflexivity | lia]. }
  apply Forall_cons; [|apply Forall_nil].
  { cbn [cell_holds c_at c_val c_w z4 c4]. rewrite Hk2, EU16. change (aeval B ly (ANum nn)) with nn. intros kk Hkk.
    replace (u - 16 + 4 + Z.of_nat kk) with (u - 12 + Z.of_nat kk) by lia. rewrite NEW_n by lia. reflexivity. }
- destruct (Z.eqb_spec (ck_rz k) 16) as [E16|N16]; [apply Forall_nil|].
  assert (R32 : 32 <= ck_rz k) by (apply Z.mod_divide in G6 as [q Hq]; [|lia]; lia).
  assert (OKM : okrc (ck_base B ly k) 16) by (intros a Ha; apply okc_k; [lia | unfold DKc; lia]).
  apply (cells_xfer_c _ _ _ OKM).
  + assert (Hk0 : aeval B ly (sptr_exp (ck_beg (qk k))) = ck_base B ly k) by reflexivity.
    unfold cell_in. apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite Hk0; cbn; lia|].
    apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite Hk1; cbn; lia|]. apply Forall_nil.
  + assert (OLDK : Forall (cell_holds B ly rd) (chunk_cells k))
      by (old_inc; do 2 right; left; apply in_flat_map; exists k; split; [exact Hk | exact HIN]).
    unfold chunk_cells, kChunkHeaderSize in OLDK. apply Forall_app in OLDK as [_ OLDK].
    destruct (Z.eqb_spec (ck_rz k) 16); [lia | exact OLDK].
Qed.
Lemma c_cells_chunks : forall l1 l2, st_chunks S = l1 ++ k :: l2 -> ~ In (ck_beg k) (map ck_beg l1) ->
  ~ In (ck_beg k) (map ck_beg l2) -> Forall (cell_holds B ly rd') (flat_map chunk_cells (l1 ++ qk k :: l2)).
Proof.
intros l1 l2 E N1 N2. rewrite flat_map_app. cbn [flat_map]. rewrite !Forall_app. dsplits.
- apply Forall_flat_map'. intros x Hx. apply c_cells_chunk_other;
    [rewrite E; apply in_app_iff; left; exact Hx | intros Ex; apply N1; rewrite <- Ex; apply in_map; exact Hx].
- exact c_cells_chunk_k.
- apply Forall_flat_map'. intros x Hx. apply c_cells_chunk_other;
    [rewrite E; apply in_app_iff; right; right; exact Hx | intros Ex; apply N2; rewrite <- Ex; apply in_map; exact Hx].
Qed.
Lemma c_cells_sec : Forall (cell_holds B ly rd') (sec_cells S').
Proof.
destruct cs_split as (l1 & l2 & E & E' & N1 & N2).
pose proof (wfc_secondary _ _ _ _ _ cWF) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells S)) by (old_inc; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *. rewrite cs_sec_res, cs_sec_arr, E'.
rewrite (YFfl.flat_map_mid _ l1 (qk k) k l2) by reflexivity. rewrite <- E.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS].
apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof okc_inst as OKI.
apply Forall_cons; [apply (cell_xfer_c _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_reserved; lia|].
apply Forall_cons; [apply (cell_xfer_c _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_n; lia|].
apply Forall_cons; [apply (cell_xfer_c _ O3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- apply (cells_xfer_c _ _ _ okc_Q); [|exact O4]. apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc.
  apply in_flat_map in Hc as (x & Hx & Hc).
  destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
  assert (OKP : okrc (ly_sec ly r) 32) by (intros a Ha; eapply (okc_secpage x r o a Hx Ebx); unfold kPage; lia).
  apply (cell_xfer_c _ Oc). intros j Hj. apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; lia.
Qed.
Lemma c_cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells S)) by (old_inc; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. rewrite cs_fs. apply (cells_xfer_c _ _ _ okc_F); [|exact OLDF].
unfold cell_in, kFakeStackSize. fconsc. fconsc.
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih.
apply in_seq in Hih. cbn. lia.
Qed.
Lemma c_cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof. destruct DEP as (D1 & _ & _). unfold depot_cells, depot_ids, depot_frames in D1 |- *. rewrite cs_depot. exact D1. Qed.
Lemma c_cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. apply Forall_cons; [|apply Forall_nil]. cbn [cell_holds c_at c_val c_w z1 c1 aeval].
intros kk Hkk. destruct kk; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, NEW_unw. reflexivity.
Qed.
Lemma c_b_bytes : b_bytes (mkBatch (b_self lastb) (b_items lastb ++ [qk k])) = b_bytes lastb + nn.
Proof.
unfold b_bytes. cbn [b_items]. rewrite YFfl.fold_ckn_app. cbn [fold_right].
change (ck_n (qk k)) with nn. lia.
Qed.
Lemma c_okrb_other : forall b2, In b2 (rev initr) \/ In b2 (qc_list (st_qglobal S)) ->
  okrc (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))).
Proof.
intros b2 Hb2 a Ha. destruct (c_self_ne b2 Hb2) as [IN NE].
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ cWF)) b2 IN) as [L1 L2].
unfold kBatchSlots in L2. apply (okc_batch_other b2 a IN NE). unfold kBatchBytes. lia.
Qed.
Lemma c_cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells S)) by (old_inc; do 4 right; left; exact HIN).
pose proof okc_inst as OKI.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ cWF)) lastb cs_lastb_in) as [BL1 BL2].
unfold quar_cells, qc_cells in OLDQ |- *. rewrite cs_qglobal, cs_qlist', cs_qbytes. rewrite cs_qlist in OLDQ.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT].
apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons; [apply (cell_xfer_c _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_cmutex; lia|].
apply Forall_cons; [apply (cell_xfer_c _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_rmutex; lia|].
apply Forall_app. split.
- apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w z8 c8]. intros kk Hkk. cbn [aeval]. rewrite NEW_qs by exact Hkk.
    rewrite cs_qlist, !length_app. reflexivity. }
  apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w c8]. intros kk Hkk. cbn [aeval aoff].
    replace (T + (t_qc + 8)) with (T + t_qc + 8) by lia. rewrite NEW_qf by exact Hkk. rewrite cs_qlist. do 2 f_equal.
    destruct (rev initr); reflexivity. }
  apply Forall_cons.
  { rewrite rev_app_distr. cbn [rev app cell_holds c_at c_val c_w c8 aeval aoff batch_exp b_self]. intros kk Hkk.
    replace (T + (t_qc + 16)) with (T + t_qc + 16) by lia. rewrite NEW_ql by exact Hkk. reflexivity. }
  apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk.
    replace (T + (t_qc + 24)) with (T + t_qc + 24) by lia. rewrite NEW_qb by exact Hkk. reflexivity. }
  destruct (YFfl.batch_cells_snoc (rev initr) lastb (mkBatch (b_self lastb) (b_items lastb ++ [qk k])) eq_refl)
    as (P & EP & EP' & HP).
  rewrite EP in OT. rewrite EP'. apply Forall_app in OT as [OP OB]. apply Forall_app. split.
  + apply Forall_forall. intros c Hc. apply (cell_xfer_c _ (proj1 (Forall_forall _ _) OP c Hc)).
    destruct (HP c Hc) as (b2 & I2 & Hb2).
    destruct Hb2 as [C2|(nx & _ & ->)].
    * destruct (batch_cells_within ly [b2] c C2) as (b3 & [<-|[]] & [R1 R2]). intros j Hj.
      apply (c_okrb_other b2 (or_introl I2)). lia.
    * intros j Hj. cbn in Hj |- *. apply (c_okrb_other b2 (or_introl I2)).
      pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ cWF)) b2
        (proj1 (c_self_ne b2 (or_introl I2)))) as [L1 _]. lia.
  + cbn [batch_cells app]. rewrite app_nil_r. cbn [batch_cells app] in OB. rewrite app_nil_r in OB.
    apply Forall_cons_iff in OB as [OB1 OB]. apply Forall_cons_iff in OB as [_ OB]. apply Forall_cons_iff in OB as [_ OB].
    assert (OKB : forall a, Bv <= a < Bv + 8 \/ Bv + 24 <= a < SLOTv -> okc a).
    { intros a Ha. apply okc_b; [unfold kBatchSlots, kBatchBytes in *; lia|]. unfold DBc. lia. }
    apply Forall_cons. { apply (cell_xfer_c _ OB1). intros j Hj. apply OKB. cbn in Hj |- *. lia. }
    apply Forall_cons.
    { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff batch_exp b_self]. intros kk Hkk.
      replace (ly_space ly + (b_self lastb + 8)) with (Bv + 8) by lia. rewrite NEW_bb by exact Hkk.
      rewrite c_b_bytes. reflexivity. }
    apply Forall_cons.
    { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff batch_exp b_self b_items]. intros kk Hkk.
      replace (ly_space ly + (b_self lastb + 16)) with (Bv + 16) by lia. rewrite NEW_bc by exact Hkk.
      rewrite length_app. cbn [length]. do 2 f_equal. lia. }
    cbn [b_items b_self]. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, (YFfl.combine_snoc _ _ _ eq_refl), map_app.
    cbn [map fst snd]. apply Forall_app. split.
    * apply Forall_forall. intros c Hc. apply (cell_xfer_c _ (proj1 (Forall_forall _ _) OB c Hc)).
      apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. intros j Hj.
      apply OKB. cbn in Hj |- *. lia.
    * apply Forall_cons; [|apply Forall_nil].
      cbn [cell_holds c_at c_val c_w c8 aeval aoff batch_exp b_self]. intros kk Hkk.
      replace (ly_space ly + (b_self lastb + (24 + 8 * Z.of_nat (length (b_items lastb)))) + Z.of_nat kk)
        with (SLOTv + Z.of_nat kk) by lia.
      rewrite NEW_slot by exact Hkk. change (ck_hdr (qk k)) with (ck_hdr k). rewrite (c_hdr_addr k Hk).
      pose proof cHu as EU. unfold kChunkHeaderSize. do 2 f_equal. lia.
- apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG].
  apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
  apply Forall_cons; [apply (cell_xfer_c _ G1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_c _ G2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_c _ G3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_c _ G4); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_forall. intros c Hc. apply (cell_xfer_c _ (proj1 (Forall_forall _ _) OG c Hc)).
  destruct (batch_cells_within ly _ c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
  apply (c_okrb_other b2 (or_intror I2)). lia.
Qed.
Lemma c_cells_all : Forall (cell_holds B ly rd') (acells_cf B ly S').
Proof.
destruct cs_split as (l1 & l2 & E & E' & N1 & N2). unfold acells_cf. rewrite E'. rewrite !Forall_app. dsplits.
- exact c_cells_regions.
- exact c_cells_caches.
- exact (c_cells_chunks l1 l2 E N1 N2).
- exact c_cells_sec.
- exact c_cells_quar.
- exact c_cells_fs.
- exact c_cells_depot.
- exact (proj1 IAL).
- exact c_cells_thread.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The remaining fields.                                                                                             *)
Lemma c_fa : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite cs_reg in Hi, Hv.
rewrite AGc; [exact (amc_fa _ _ _ _ _ M c i v Hc Hi Hv kk Hkk)|].
pose proof (wfc_classes _ _ _ _ _ cWF c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB. apply (okc_fa c Hc). lia.
Qed.
Lemma c_flags : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hpos. rewrite cs_frames. rewrite AGc; [exact (amc_flags _ _ _ _ _ M cid pos Hc Hpos)|].
pose proof (flag_off_bounds cid pos Hc Hpos) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *.
apply okc_F. unfold kFakeStackSize. lia.
Qed.
Lemma c_depot : depot_ok B ly rd' S'.
Proof. destruct DEP as (_ & D2 & _). unfold depot_ok, depot_ids, depot_traces in D2 |- *. rewrite cs_depot. exact D2. Qed.
(* the freed block's bytes are not a hidden head: a hidden head is the user base of another live block *)
Lemma c_head_off : forall g, ck_base B ly k <= g < ck_base B ly k + ck_extent k -> in_head Hp g = false.
Proof.
intros g Hg. destruct (in_head Hp g) eqn:E; [|reflexivity]. exfalso.
unfold in_head in E. apply existsb_exists in E as (p0 & Hp0 & Hb).
apply andb_prop in Hb as [HB1 HB2]. apply Z.leb_le in HB1. apply Z.ltb_lt in HB2.
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M) p0 Hp0) as (k0 & Hk0 & Hst0 & Ep0 & Hn0).
pose proof (chunk_facts_cf B ly S Hp rd k0 M Hk0) as (_ & _ & _ & G40 & G50 & _ & _ & G80 & _).
destruct (sptr_eqb (ck_beg k0) (ck_beg k)) eqn:Eb.
- apply sptr_eqb_spec in Eb.
  assert (k0 = k) by (apply (YFfl.NoDup_map_In ck_beg (st_chunks S) k0 k (wfc_chunks_nodup _ _ _ _ _ cWF) Hk0 Hk Eb)).
  subst k0. apply HPu. rewrite <- Ep0. exact Hp0.
- assert (Hne : ck_beg k0 <> ck_beg k) by (intros E'; rewrite E', sptr_eqb_refl in Eb; discriminate).
  pose proof (chunks_disjoint_cf B ly S Hp rd k0 k M Hk0 Hk Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ.
  unfold ck_n in Hn0. rewrite Ep0, G40 in HB1, HB2. lia.
Qed.
Lemma c_DH_iff : forall g, g mod 8 = 0 -> (DHc (shadow_addr g) <-> u <= g < u + (nn + 7) / 8 * 8).
Proof.
intros g Hg. pose proof cU8 as (U8 & _ & _). pose proof cER as (_ & _ & NN2 & _).
unfold DHc, shadow_addr. apply Z.mod_divide in Hg as [c Hc]; [|lia]. apply Z.mod_divide in U8 as [a0 Ha0]; [|lia].
rewrite Hc, Ha0. rewrite !Z_div_mult by lia. nia.
Qed.
Lemma c_shadow : shadow_ok_cf B ly Hp rd' S'.
Proof.
destruct cs_split as (l1 & l2 & E & E' & N1 & N2).
pose proof cKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof cHu as EU.
pose proof cER as (ER & NN1 & NN2 & NN3). pose proof cU8 as (U8 & B8 & R8).
intros g v Hg8 HS'. pose proof (amc_shadow _ _ _ _ _ M g) as SH.
unfold ashadow in HS', SH. rewrite E', cs_fa_poison in HS'. rewrite E in SH.
rewrite YFfl.find_chunk_at_app in HS', SH. cbn [find_chunk_at] in HS', SH.
change (ck_base B ly (qk k)) with (ck_base B ly k) in HS'. change (ck_extent (qk k)) with (ck_extent k) in HS'.
assert (OTHER : forall x, In x (st_chunks S) -> ck_beg x <> ck_beg k ->
  ck_base B ly x <= g < ck_base B ly x + ck_extent x ->
  rd (shadow_addr g) = Some (if in_head Hp g then shUserPoison else v) ->
  rd' (shadow_addr g) = Some (if in_head Hp g then shUserPoison else v)).
{ intros x Hx Hne Hgx Hrd. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (X1 & X2 & _).
  rewrite AGc; [exact Hrd|]. apply okc_sh.
  - apply g_hs_bounds; [unfold in_app in X1; lia | ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia].
  - intros HD. apply (c_DH_iff g Hg8) in HD.
    pose proof (chunks_disjoint_cf B ly S Hp rd x k M Hx Hk Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia. }
destruct (find_chunk_at B ly l1 g) as [x|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hx Hgx].
  apply (OTHER x); [rewrite E; apply in_app_iff; left; exact Hx
    | intros Ex; apply N1; rewrite <- Ex; apply in_map; exact Hx | exact Hgx | exact (SH v Hg8 HS')].
- destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
  + apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
    change (ck_base B ly (qk k)) with (ck_base B ly k) in HS'.
    rewrite (c_head_off g ltac:(lia)) in SH |- *.
    apply Z.mod_divide in Hg8 as [c Hc]; [|lia]. apply Z.mod_divide in B8 as [b0 Hb0]; [|lia].
    apply Z.mod_divide in R8 as [r0 Hr0]; [|lia].
    assert (J : (g - ck_base B ly k) / 8 = c - b0)
      by (rewrite Hc, Hb0; replace (c * 8 - b0 * 8) with ((c - b0) * 8) by lia; apply Z_div_mult; lia).
    assert (RU : ck_rz k / 8 = r0) by (rewrite Hr0; apply Z_div_mult; lia).
    rewrite J in HS', SH. unfold chunk_granule in HS', SH.
    change (ck_rz (qk k)) with (ck_rz k) in HS'. change (ck_n (qk k)) with nn in HS'.
    change (ck_state (qk k)) with CQuarantined in HS'. rewrite RU in HS', SH. rewrite Hst in SH.
    destruct (c - b0 <? r0) eqn:C1.
    * apply Z.ltb_lt in C1. injection HS' as <-. rewrite AGc; [exact (SH _ ltac:(rewrite Hc; apply Z_mod_mult) eq_refl)|].
      apply okc_sh; [apply g_hs_bounds; [unfold in_app in G1; lia | ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia]|].
      intros HD. apply (c_DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)) in HD. nia.
    * apply Z.ltb_ge in C1. destruct (c - b0 <? r0 + (nn + 7) / 8) eqn:C2.
      -- apply Z.ltb_lt in C2. injection HS' as <-.
         apply NEW_sh; [apply (c_DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)); nia|].
         rewrite (SH (if c - b0 <? r0 + nn / 8 then shAddressable
                      else if (c - b0 =? r0 + nn / 8) && negb (nn mod 8 =? 0) then nn mod 8 else shHeapLeftRz));
           [discriminate | rewrite Hc; apply Z_mod_mult | reflexivity].
      -- apply Z.ltb_ge in C2. injection HS' as <-.
         assert (OLDV : rd (shadow_addr g) = Some shHeapLeftRz).
         { apply SH; [rewrite Hc; apply Z_mod_mult|].
           assert (F1' : (c - b0 <? r0 + nn / 8) = false).
           { apply Z.ltb_ge. pose proof (Z.div_le_mono nn (nn + 7) 8 ltac:(lia) ltac:(lia)). lia. }
           rewrite F1'. destruct (Z.eqb_spec (nn mod 8) 0) as [Z0|NZ]; cbn [negb andb];
             [rewrite Bool.andb_false_r; reflexivity|].
           replace (c - b0 =? r0 + nn / 8) with false; [reflexivity|]. symmetry. apply Z.eqb_neq.
           pose proof (Z.div_mod nn 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as MB.
           pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)) as DM'. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)) as MB'. nia. }
         rewrite AGc; [exact OLDV|].
         apply okc_sh; [apply g_hs_bounds; [unfold in_app in G1; lia | ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia]|].
         intros HD. apply (c_DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)) in HD. nia.
  + assert (NK : ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)).
    { intros X. assert (TT : (ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k) = true)
        by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite TT in TK. discriminate. }
    destruct (find_chunk_at B ly l2 g) as [x|] eqn:F2.
    * apply find_chunk_at_In in F2 as [Hx Hgx].
      apply (OTHER x); [rewrite E; apply in_app_iff; right; right; exact Hx
        | intros Ex; apply N2; rewrite <- Ex; apply in_map; exact Hx | exact Hgx | exact (SH v Hg8 HS')].
    * destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
      pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg).
      pose proof (g_fa_poison_high ly S Hp rd M lo len g Hin Hg) as [Y1 Y2].
      rewrite AGc; [exact (SH v Hg8 HS')|].
      apply okc_sh; [apply g_hs_bounds; [lia | ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia]|].
      intros HD. apply (c_DH_iff g Hg8) in HD. lia.
Qed.
Lemma c_zshadow : zshadow_ok B ly rd'.
Proof.
pose proof (amc_zshadow _ _ _ _ _ M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *.
change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGc; [exact Z0|]. apply okc_sh; [exact (g_zsh_sh ly S Hp rd M r i Hr Hi)|].
intros HD. pose proof cKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof cHu as EU.
pose proof cER as (ER & NN1 & NN2 & NN3). pose proof cU8 as (U8 & B8 & R8).
pose proof (amc_layout _ _ _ _ _ M) as LO.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi, Z0, HD |- *.
- pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _ & T7). unfold page_aligned in T5.
  apply Z.mod_divide in T5 as [s0 Hs0]; [|lia].
  assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
  { unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by lia.
    replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
  rewrite E8 in HD. apply (c_DH_iff (ly_stk_lo ly + 8 * i)
    ltac:(rewrite Hs0; replace (s0 * 4096 + 8 * i) with ((512 * s0 + i) * 8) by lia; apply Z_mod_mult)) in HD.
  pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
  pose proof (anyX_cf B ly S Hp rd M k 8 _ Hk eq_refl ltac:(lia)) as D8.
  unfold zdisjoint in D8. cbn [fst snd] in D8. lia.
- pose proof (g_zsh_img ly S Hp rd M r Hr) as [Z1 Z2]. pose proof (g_img ly S Hp rd M) as (I0 & I1 & I2).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ M)) r Hr) as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct r as [lo len]. cbn [fst snd] in *. apply Z.mod_divide in Q3 as [c Hc]; [|lia].
  assert (E8 : shadow_addr lo + i = shadow_addr (lo + 8 * i)).
  { unfold shadow_addr. rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
  rewrite E8 in HD. apply (c_DH_iff (lo + 8 * i)
    ltac:(rewrite Hc; replace (c * 8 + 8 * i) with ((c + i) * 8) by lia; apply Z_mod_mult)) in HD.
  pose proof (Z.mul_div_le len 8 ltac:(lia)).
  pose proof (anyX_cf B ly S Hp rd M k 9 _ Hk eq_refl ltac:(lia)) as D9.
  unfold zdisjoint in D9. cbn [fst snd] in D9. unfold kImgLo in *. lia.
Qed.
Lemma c_vis_sub : forall r r', range_vis B ly rd r' -> aeval B ly (fst r') <= aeval B ly (fst r) ->
  aeval B ly (fst r) + snd r <= aeval B ly (fst r') + snd r' -> range_vis B ly rd' r.
Proof.
intros r r' V H1 H2 i Hi. apply VIS.
replace (aeval B ly (fst r) + i) with (aeval B ly (fst r') + (aeval B ly (fst r) + i - aeval B ly (fst r'))) by lia.
apply V. lia.
Qed.
Lemma c_junk : Forall (range_vis B ly rd') (ajunk_cf B ly S').
Proof.
destruct cs_split as (l1 & l2 & E & E' & N1 & N2). pose proof (amc_junk _ _ _ _ _ M) as J.
pose proof (amc_client _ _ _ _ _ M) as CL. pose proof cHu as EU.
assert (VK : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L)
  by (intros L HL; exact (Forall_range_vis_keep B ly rd rd' L VIS HL)).
unfold ajunk_cf in J |- *. unfold quar_junk in J |- *. rewrite cs_batches in J. rewrite cs_batches'.
unfold cache_junk, cache, sec_junk in J |- *. rewrite cs_cinit, cs_cache, cs_sec_arr, cs_sec_res, E'. rewrite E in J.
rewrite (YFfl.flat_map_mid (fun k0 : chunk => match ck_beg k0 with PSec r _ => [(ASec r 32, kPage - 32)] | _ => [] end) l1 (qk k) k l2)
  by reflexivity.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J].
apply Forall_app in J as [J6 J]. apply Forall_app in J as [J7 J].
apply Forall_cons; [intros i Hi; apply VIS; exact (J1 i Hi)|].
apply Forall_cons; [intros i Hi; apply VIS; exact (J2 i Hi)|].
apply Forall_app. split; [exact (VK _ J3)|]. apply Forall_app. split; [exact (VK _ J4)|].
apply Forall_app. split.
{ rewrite flat_map_app in J5 |- *. cbn [flat_map] in J5 |- *. apply Forall_app in J5 as [J5a J5].
  apply Forall_app in J5 as [J5k J5b].
  apply Forall_app. split; [exact (VK _ J5a)|]. apply Forall_app. split; [|exact (VK _ J5b)].
  unfold chunk_junk in J5k |- *. change (ck_rz (qk k)) with (ck_rz k). change (ck_n (qk k)) with nn.
  change (ck_extent (qk k)) with (ck_extent k). change (ck_state (qk k)) with CQuarantined. rewrite Hst in J5k.
  apply Forall_app in J5k as [Ja J5k]. apply Forall_app in J5k as [Jb J5k]. apply Forall_app in J5k as [_ Jd].
  apply Forall_app. split; [exact (VK _ Ja)|]. apply Forall_app. split; [exact (VK _ Jb)|].
  apply Forall_app. split; [|exact (VK _ Jd)].
  apply Forall_cons; [|apply Forall_nil].
  apply (c_vis_sub _ (sptr_exp (ck_user k), ck_n k)).
  - apply (proj1 (Forall_forall _ _) CL). unfold aclient. apply in_app_iff. left. apply in_flat_map.
    exists k. split; [exact Hk|]. unfold chunk_user. rewrite Hst. left. reflexivity.
  - cbn [fst snd]. change (sptr_exp (ck_beg (qk k))) with (sptr_exp (ck_beg k)). rewrite (cEA k _ Hk).
    fold (sptr_addr B ly (ck_user k)). lia.
  - cbn [fst snd]. change (sptr_exp (ck_beg (qk k))) with (sptr_exp (ck_beg k)). rewrite (cEA k _ Hk).
    fold (sptr_addr B ly (ck_user k)). lia. }
apply Forall_app. split; [exact (VK _ J6)|].
apply Forall_app. split.
{ rewrite !flat_map_app in J7 |- *. cbn [flat_map] in J7 |- *. rewrite app_nil_r in J7 |- *.
  apply Forall_app in J7 as [J7a J7]. apply Forall_app in J7a as [J7i J7b].
  apply Forall_app. split; [|exact (VK _ J7)]. apply Forall_app. split; [exact (VK _ J7i)|].
  unfold batch_junk in J7b |- *. apply Forall_cons; [|apply Forall_nil]. apply Forall_cons_iff in J7b as [J7b _].
  apply (c_vis_sub _ _ J7b); cbn -[Z.add Z.mul Z.sub Z.of_nat]; rewrite length_app; cbn [length]; unfold kBatchBytes; lia. }
exact (VK _ J).
Qed.
Lemma c_areas : Forall (range_vis B ly rd') (aareas S').
Proof.
destruct cs_split as (l1 & l2 & E & E' & N1 & N2). pose proof (amc_areas _ _ _ _ _ M) as A.
unfold aareas, reg in A |- *. rewrite cs_regions, cs_sec_res, E'. rewrite E in A.
rewrite (YFfl.flat_map_mid _ l1 (qk k) k l2) by reflexivity. exact (Forall_range_vis_keep B ly rd rd' _ VIS A).
Qed.
Lemma c_client : Forall (range_vis B ly rd') (aclient S').
Proof.
destruct cs_split as (l1 & l2 & E & E' & N1 & N2). pose proof (amc_client _ _ _ _ _ M) as A.
apply Forall_forall. intros r Hr i Hi. apply VIS.
assert (Hr0 : In r (aclient S)).
{ unfold aclient in Hr |- *. apply in_app_iff in Hr as [Hr|Hr]; apply in_app_iff; [left | right; rewrite cs_frames in Hr; exact Hr].
  apply in_flat_map in Hr as (x & Hx & Hrx). apply in_flat_map. exists x. split; [|exact Hrx].
  rewrite E' in Hx. rewrite E. apply in_app_iff in Hx as [Hx|[Hx|Hx]].
  - apply in_app_iff. left. exact Hx.
  - subst x. cbn [chunk_user qk ck_state In] in Hrx. destruct Hrx.
  - apply in_app_iff. right. right. exact Hx. }
exact (proj1 (Forall_forall _ _) A r Hr0 i Hi).
Qed.
Lemma c_hp_live : Forall (fun p => exists k0, In k0 (st_chunks S') /\ ck_state k0 = CAllocated /\
  p = sptr_addr B ly (ck_user k0) /\ cf_head <= ck_n k0) Hp.
Proof.
destruct cs_split as (l1 & l2 & E & E' & N1 & N2). apply Forall_forall. intros p0 Hp0.
destruct (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M) p0 Hp0) as (k0 & Hk0 & Hs0 & Ep0 & Hn0).
exists k0. split; [|exact (conj Hs0 (conj Ep0 Hn0))]. rewrite E'. rewrite E in Hk0.
apply in_app_iff in Hk0 as [X|[X|X]]; apply in_app_iff; [left; exact X | | right; right; exact X].
exfalso. subst k0. apply HPu. rewrite <- Ep0. exact Hp0.
Qed.
Lemma c_xs : xs_placed_cf ly S'.
Proof.
pose proof (amc_xs_placed _ _ _ _ _ M) as X. unfold xs_placed_cf in X |- *.
replace (xs_cf ly S') with (xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite cs_secs; reflexivity).
rewrite cs_sec_extents. exact X.
Qed.
Theorem c_post_parts : ARmcf B ly S' Hp rd' /\
  (forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> rd' (shadow_addr g) = rd (shadow_addr g)).
Proof.
split.
- constructor.
  + exact WFS'.
  + exact (amc_universe _ _ _ _ _ M).
  + exact (amc_syms _ _ _ _ _ M).
  + exact cLO.
  + unfold sec_placed. rewrite cs_sec_extents. exact (amc_placed _ _ _ _ _ M).
  + exact CONST'.
  + exact (amc_const_owned _ _ _ _ _ M).
  + exact c_cells_all.
  + exact c_fa.
  + exact c_flags.
  + exact c_depot.
  + exact c_shadow.
  + exact c_zshadow.
  + exact c_junk.
  + exact c_areas.
  + exact c_client.
  + exact (proj2 IAL).
  + exact (amc_tsd _ _ _ _ _ M).
  + exact (amc_static_img _ _ _ _ _ M).
  + exact c_hp_live.
  + exact c_xs.
  + exact EXHc.
  + exact ERRc.
  + exact (amc_cells_owned _ _ _ _ _ M).
  + exact (pf_cells_move_cf B ly S Hp rd rd' okc M (amc_pf_owned _ _ _ _ _ M) (fun a _ Ha => AGc a Ha) okc_pf
      (amc_pf_cells _ _ _ _ _ M)).
  + exact (amc_pf_owned _ _ _ _ _ M).
- intros g Hg Hga HF. pose proof cKF as (G1 & G2 & G3 & G4 & G5 & _). pose proof cHu as EU.
  pose proof cER as (ER & NN1 & NN2 & NN3).
  apply AGc. apply okc_sh.
  + apply g_hs_bounds; [exact (proj1 Hga) | ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia].
  + intros HD. apply (c_DH_iff g Hg) in HD.
    destruct (hfree_off_extent_cf B ly S Hp rd k g M Hk Hg HF) as [X|X]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The constant cells off the depot zone are off the walk's windows (DGif1.v:1502-1526's CD over owned_core).       *)
Hypothesis HCO : FP_CONST_at ly.
Lemma cDK_ext : forall a, DKc a -> ck_base B ly k <= a < ck_base B ly k + ck_extent k.
Proof.
intros a X. pose proof cKF as (G1 & G2 & G3 & G4 & G5 & _). pose proof cHu as EU. pose proof cER as (ER & NN1 & NN2 & NN3).
assert (Q8 : 8 <= (nn + 7) / 8 * 8)
  by (pose proof (Z.div_le_mono 8 (nn + 7) 8 ltac:(lia) ltac:(lia)) as D; change (8 / 8) with 1 in D; lia).
unfold DKc in X. lia.
Qed.
Lemma cDB_bat : forall a, DBc a -> Bv <= a < Bv + kBatchBytes.
Proof. intros a X. unfold DBc in X. unfold kBatchSlots, kBatchBytes in *. lia. Qed.
Lemma cDH_img : forall a r, In r (as_owned_static B) -> shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 ->
  ~ DHc a.
Proof.
intros a r Hr Ha HD. unfold DHc in HD.
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
pose proof (lo_img _ cLO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (Y1 & Y2 & Y3).
pose proof (anyX_cf B ly S Hp rd M k 9 _ Hk eq_refl ltac:(lia)) as DJI. unfold zdisjoint in DJI. cbn [fst snd] in DJI.
pose proof cKF as (G1 & G2 & G3 & G4 & G5 & _). pose proof cHu as EU. pose proof cER as (ER & NN1 & NN2 & NN3).
pose proof cU8 as (U8 & _ & _).
assert (EE : exists e, kImgLo + snd (ly_img ly) = 8 * e).
{ unfold page_aligned in I3. apply Z.mod_divide in I3 as [w Hw]; [|lia]. exists (8192 + 512 * w). unfold kImgLo. lia. }
destruct EE as [e He].
apply Z.mod_divide in U8 as [c Hc]; [|lia].
assert (SU : shadow_addr u = SHADOW_OFF + c) by (unfold shadow_addr; rewrite Hc, Z_div_mult by lia; reflexivity).
rewrite SU in HD. unfold zr_sub in Z1, Z2. cbn [fst snd] in Z1, Z2.
destruct DJI as [DJI|DJI].
- assert (F1 : kImgLo / 8 <= fst r / 8) by (apply Z.div_le_mono; lia).
  change (kImgLo / 8) with 8192 in F1. unfold shadow_addr in Ha. unfold kImgLo in *. lia.
- assert (F2 : fst r / 8 + (snd r + 7) / 8 <= (fst r + snd r + 7) / 8).
  { pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as MB.
    replace (fst r + snd r + 7) with (fst r / 8 * 8 + (fst r mod 8 + snd r + 7)) by lia.
    rewrite Z.div_add_l by lia.
    pose proof (Z.div_le_mono (snd r + 7) (fst r mod 8 + snd r + 7) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (F3 : (fst r + snd r + 7) / 8 < e + 1) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr in Ha. lia.
Qed.
Lemma c_const_ok : forall c j, In c (as_const B ly) -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ dg_dzone ly (aeval B ly (c_at c) + j) -> okc (aeval B ly (c_at c) + j).
Proof.
intros c j Hc Hj ND.
destruct (g_const_loc ly S Hp rd M c j Hc Hj) as [R64 NST]. destruct (HCO c j Hc Hj) as [NIZ NWT].
pose proof (proj1 (Forall_forall _ _) (amc_const_owned _ _ _ _ _ M) c Hc j Hj) as OW. unfold owned_core in OW.
pose proof okc_kbatch as (KB1 & KB2 & _). pose proof (g_img ly S Hp rd M) as (I0 & I1 & I2).
set (a := aeval B ly (c_at c) + j) in *.
split; [exact R64|]. intros [X|[X|[X|[X|[X|[X|X]]]]]].
- exact (NWT X).
- apply cDK_ext in X. destruct OW as [O|[O|O]].
  + pose proof (g_static_img ly S Hp rd M a O) as HI.
    pose proof (anyX_cf B ly S Hp rd M k 9 _ Hk eq_refl ltac:(lia)) as DJI. unfold zdisjoint, in_zr in *. cbn [fst snd] in *. lia.
  + apply Exists_exists in O as (e & He & Hae). unfold core_extents in He. unfold in_zr in Hae.
    cbn [In] in He. destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hae;
    [ pose proof (anyX_cf B ly S Hp rd M k 1 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 2 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 4 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 5 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 6 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 7 _ Hk eq_refl ltac:(lia)) as DD ];
    unfold zdisjoint in DD; cbn [fst snd] in DD; lia.
  + apply Exists_exists in O as (r & Hr & Hra). unfold in_zr in Hra. cbn [fst snd] in Hra.
    pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (Y1 & Y2 & Y3).
    pose proof cKF as (G1 & G2 & _).
    assert (D1 : fst r / 8 <= fst r) by (apply Z.div_le_upper_bound; lia).
    assert (D2 : (snd r + 7) / 8 <= snd r + 7) by (apply Z.div_le_upper_bound; lia).
    assert (D0 : 512 <= fst r / 8) by (pose proof (Z.div_le_mono 4096 (fst r) 8 ltac:(lia) ltac:(lia)) as D; exact D).
    unfold in_app, shadow_addr, SHADOW_OFF, kImgEnd, kLowShadowBeg, kHighMemBeg in *. lia.
- apply cDB_bat in X. destruct OW as [O|[O|O]].
  + pose proof (g_static_img ly S Hp rd M a O) as HI.
    pose proof (SX_cf B ly S Hp rd M 0 9 _ _ eq_refl eq_refl ltac:(lia)) as DJI. unfold zdisjoint, in_zr in *. cbn [fst snd] in *.
    unfold kBatchBytes in *. lia.
  + apply Exists_exists in O as (e & He & Hae). unfold core_extents in He. unfold in_zr in Hae.
    cbn [In] in He. destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hae;
    [ pose proof (SX_cf B ly S Hp rd M 0 1 _ _ eq_refl eq_refl ltac:(lia)) as DD
    | pose proof (SX_cf B ly S Hp rd M 0 2 _ _ eq_refl eq_refl ltac:(lia)) as DD
    | pose proof (SX_cf B ly S Hp rd M 0 4 _ _ eq_refl eq_refl ltac:(lia)) as DD
    | pose proof (SX_cf B ly S Hp rd M 0 5 _ _ eq_refl eq_refl ltac:(lia)) as DD
    | pose proof (SX_cf B ly S Hp rd M 0 6 _ _ eq_refl eq_refl ltac:(lia)) as DD
    | pose proof (SX_cf B ly S Hp rd M 0 7 _ _ eq_refl eq_refl ltac:(lia)) as DD ];
    unfold zdisjoint in DD; cbn [fst snd] in DD; unfold kBatchBytes in *; lia.
  + apply Exists_exists in O as (r & Hr & Hra). unfold in_zr in Hra. cbn [fst snd] in Hra.
    pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (Y1 & Y2 & Y3).
    pose proof (lo_high _ cLO) as LH. unfold in_high in LH. cbn [fst snd] in LH.
    assert (D1 : fst r / 8 <= fst r) by (apply Z.div_le_upper_bound; lia).
    assert (D2 : (snd r + 7) / 8 <= snd r + 7) by (apply Z.div_le_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF, kImgEnd, kHighMemBeg, kBatchBytes in *. lia.
- apply NST. unfold DSc, DGbaseC.DFSTACK in *. lia.
- exact (NIZ X).
- exact (ND X).
- destruct OW as [O|[O|O]].
  + pose proof (g_static_img ly S Hp rd M a O) as HI. pose proof (cDH_sh a X) as [S1 S2].
    unfold in_zr in HI. unfold kImgLo, kImgEnd, kLowShadowBeg in *. lia.
  + apply Exists_exists in O as (e & He & Hae).
    assert (HeO : In e (owned_extents ly)) by (unfold core_extents in He; unfold owned_extents; cbn in He |- *; tauto).
    pose proof (g_app_oext ly S Hp rd M e a HeO Hae) as AA. pose proof (cDH_sh a X) as [S1 S2].
    unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
  + apply Exists_exists in O as (r & Hr & Hra). exact (cDH_img a r Hr Hra X).
Qed.
End cs.

(* The depot's memory facts read the model only through its depot (AGix.depot_mem_ok_ext, image-free). *)
Lemma depot_mem_ok_same_cf : forall ly S1 S2 (rd0 : reader), st_depot S1 = st_depot S2 ->
  CLdepot.depot_mem_ok B ly S1 rd0 -> CLdepot.depot_mem_ok B ly S2 rd0.
Proof.
intros ly S1 S2 rd0 E (D1 & D2 & D3). split; [|split; [|exact D3]].
- replace (depot_cells ly S2) with (depot_cells ly S1) by (unfold depot_cells, depot_ids, depot_frames; rewrite E; reflexivity).
  exact D1.
- unfold depot_ok, depot_ids, depot_traces in *. rewrite <- E. exact D2.
Qed.
(* ... and the memory only on the depot's footprint (AGix.depot_mem_ok_agree over CLdepot.depot_footprint). *)
Lemma depot_mem_ok_fp_cf : forall ly S0 (rd1 rd2 : reader), depot_ids S0 <= 4098 ->
  (forall a, CLdepot.depot_footprint B ly a -> rd2 a = rd1 a) ->
  CLdepot.depot_mem_ok B ly S0 rd1 -> CLdepot.depot_mem_ok B ly S0 rd2.
Proof.
intros ly S0 rd1 rd2 HID He (D1' & D2 & D3).
assert (EZ : forall a, (as_depot B <= a < as_depot B + d_map1 + 8) \/ (as_store B <= a < as_store B + 32) \/
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> rd2 a = rd1 a).
{ intros a Ha. apply He. unfold CLdepot.depot_footprint, d_map1 in *. lia. }
split; [|split].
- apply Forall_forall. intros c Hc. apply (cell_holds_agree B ly rd1 rd2 c (proj1 (Forall_forall _ _) D1' c Hc)).
  intros kk Hk. apply EZ. unfold depot_cells in Hc. cbn in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [c_at c_w aeval aoff z4 z8 c4 c8] in *; cbn in Hk;
    unfold d_nuniq, d_map1, s_total, s_block0 in *; lia.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
  + intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros kk Hk. rewrite EZ; [exact (Hr kk Hk)|].
    unfold d_tab_words, d_map1 in *. lia.
  + intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
    * intros kk Hk. rewrite EZ; [exact (L2 kk Hk)|]. unfold kNodesBlockSize. lia.
    * intros kk Hk. rewrite EZ; [exact (L3 kk Hk)|]. unfold kNodesBlockSize. lia.
- apply Forall_forall. intros r Hr i Hi. rewrite EZ; [exact (proj1 (Forall_forall _ _) D3 r Hr i Hi)|].
  cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval aoff] in *; unfold d_nuniq, d_map1 in *; lia.
Qed.

(* The ledger of the ticked state (the tick touches no field the ledger reads). *)
Lemma ALedger_cf_dtick : forall ly S md, ALedger_cf im_segs ly S md -> ALedger_cf im_segs ly (dtick S) md.
Proof. intros ly S md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17]. constructor; assumption. Qed.

(* ================================================================================================================ *)
(* The errbuf extent's map: the arms below change neither the secondary table nor the model's maps (the one place
   ARX_cf's third conjunct is re-established; YGcfXsMapped's keep lemmas state the general case). *)
Lemma xs_mapped_keep_cf : forall ly S S' md md', st_secs S' = st_secs S -> m_vmmaps md' = m_vmmaps md ->
  xs_mapped_cf ly S md -> xs_mapped_cf ly S' md'.
Proof.
intros ly S S' md md' Hs Hm HX e He. rewrite Hm. apply HX.
assert (E : xs_cf ly S' = xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite Hs; reflexivity).
rewrite E in He. exact He.
Qed.

(* ================================================================================================================ *)
(* 4. The two post fields, at the image premises of section 0 and the instance predicate IOK.                       *)
Section p.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Hypothesis HIZO : YGcfDIface.IZONE_OWNED B.
Hypothesis HIZR : FP_IZONE_ROM.
Hypothesis HDS : FP_DSTAT.
Hypothesis HDZO : YGcfDIface.DZONE_OWNED B.
Hypothesis HDZF : FP_DZONE_FP.
Hypothesis HCO : FP_CONST.
Hypothesis HIAL : FV_IAL B.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
(* the error-buffer object avoids the walk's image zones (the relation's machine cells: ARmcf's fields) *)
Hypothesis HERRB : ERRB_APART.
(* Printf's two cells avoid the walk's image zones (ARmcf's amc_pf_cells, field round 3) *)
Hypothesis HPFA : PF_APART.

Lemma post_n_cf : forall inst ly S W mem0 md0 n tr sp0 mem' mat,
  ARX_cf B IOK Hp inst ly S W mem0 md0 -> rpreD_free_cf B S n -> fpre_hp_cf im_segs B Hp ly S W mem0 PNull n -> U_cf B tr S ->
  ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
  dmem_n W ly sp0 mem0 mem' ->
  (exists trc, apath (free_cf PNull tr S) trc (tt, dtick S) /\ gflag trc = true) ->
  ARX_cf B IOK Hp inst ly (dtick S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ qtight (dtick S).
Proof.
intros inst ly S W mem0 md0 n tr sp0 mem' mat (Ei & HAR & HXM) (HU & HQ & HII & HBR & _) _ _ Hlo Hhi Hbot Hal (MEQ & IALP & UNW & PRES) _.
pose proof HAR as (M & LED & BUD & MW & HSH).
pose proof (amc_exh_cell _ _ _ _ _ M) as HEX. pose proof (amc_errb_cells _ _ _ _ _ M) as HER.
pose proof (FP_IZONE_of HIZO HIZR (amc_syms _ _ _ _ _ M)) as HIZ.
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (LGUARD_of_ARmcf ly S Hp _ md0 M HIMG LED) as HLG.
set (rd := aview im_segs (w_H W) mem0) in *. set (rd' := aview im_segs (w_H W) mem').
assert (Hsp : ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 <= ly_stk_hi ly) by (split; assumption).
(* the frame: outside the stack window, the unwinding byte and the internal allocator's zone *)
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ Dn ly sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same_cf. apply (MEQ (Z_to_bv 64 a)); rewrite unsigned_lit_small by exact Ha.
  - intros X. apply ND. right; left. exact X.
  - intros X. apply ND. left. exact X.
  - intros X. apply ND. right; right. exact X. }
(* visibility: what the entry memory shows, the return memory shows *)
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv. subst rd rd'. unfold aview, mbyte, mrestrict in Hv |- *. set (x := Z_to_bv 64 a) in *.
  destruct (w_H W x) eqn:Hx; [exact Hv|].
  destruct (seg_rom im_segs x) eqn:ROM; [destruct (mem' x); discriminate|].
  destruct (mem' x) as [b|] eqn:E'; [discriminate|]. exfalso.
  assert (Hv0 : mem0 x <> None) by (intros E0; rewrite E0 in Hv; exact (Hv eq_refl)).
  set (a' := bv_unsigned x) in *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (EM : forall lo hi (c : Z), (lo <= c < hi) \/ ~ (lo <= c < hi)) by (intros; lia).
  assert (NIZ : ~ dg_izone a').
  { intros X. destruct (HIZ a' X) as (_ & R & _). rewrite Ex in R. exact (R ROM). }
  destruct (EM (sp0 - DGbaseC.DFSTACK) sp0 a') as [C1|C1].
  { destruct (PRES a' C1) as [_ [bb Hb]]. rewrite Ex in Hb. congruence. }
  destruct (EM (ly_T ly + t_unwinding) (ly_T ly + t_unwinding + 1) a') as [C2|C2].
  { pose proof (UNW 0%nat ltac:(lia)) as U0. rewrite Z.add_0_r in U0. unfold mbyte, mrestrict in U0.
    replace (ly_T ly + t_unwinding) with a' in U0 by lia. rewrite Ex, Hx, E', ROM in U0. discriminate. }
  rewrite (MEQ x C1 C2 NIZ) in E'. exact (Hv0 E'). }
(* the hidden bytes of the shadow band do not change *)
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem0 (w64 a)).
{ intros a Hb Hh.
  assert (Ha64 : 0 <= a < 2 ^ 64)
    by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia).
  unfold w64 in *. assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha64).
  apply (MEQ (Z_to_bv 64 a)); rewrite Ux.
  - intros C. destruct (PRES a C) as [Hh' _]. rewrite Hh in Hh'. discriminate.
  - intros C.
    destruct (owned_extents_bound ly (ly_T ly + t_unwinding) LY
      ltac:(apply Exists_exists; exists (ly_T ly, kThreadObjSize); split;
            [unfold owned_extents; cbn; tauto | unfold in_zr; cbn; unfold t_unwinding, kThreadObjSize; lia])) as (AA & _ & _).
    clear - C Hb AA. unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *.
    ceil. unfold ASAN_CEIL in *. lia.
  - intros C. destruct (HIZ a C) as (OS & _).
    pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M) OS) as [X1 X2].
    clear - Hb X1 X2. unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia. }
(* the unwinding byte, the internal allocator's cells and the constant cells at the return memory *)
assert (NEWU : rd' (ly_T ly + t_unwinding) = Some 0).
{ subst rd'. pose proof (val_mem_aview_cf (w_H W) mem' (ly_T ly + t_unwinding) 1 0 0%nat UNW ltac:(lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0. }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B S) /\ Forall (range_zero B ly rd') (ialloc_zero B))
  by (subst rd'; exact (ial_cells_of_post_cf ly S W mem' HII (proj1 (HIAL W mem') IALP))).
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd rd' c);
    [exact (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M) c Hc)|].
  intros j Hj. destruct (g_const_loc ly S Hp rd M c j Hc Hj) as [R64 NST].
  destruct (HCO ly c j HLG Hc Hj) as [NIZ NWT]. apply AG; [exact R64|]. intros [X|[X|X]].
  - apply NWT. unfold DGgiC.WINT. right; left. exact X.
  - apply NST. unfold DSn, DGbaseC.DFSTACK in *. lia.
  - exact (NIZ X). }
(* the machine cells (ARmcf's fields): off the walk's writes *)
assert (XN : forall a, XC B ly a -> rd' a = rd a).
{ intros a X. pose proof (x_owned B ly S Hp rd M a X) as [R64 _]. apply AG; [exact R64|].
  unfold Dn, DTn, DSn. intros [D|[D|D]].
  - apply (x_T B ly S Hp rd M a X). unfold t_unwinding, kThreadObjSize in *. lia.
  - exact (x_S B ly S Hp rd M a sp0 X Hsp D).
  - exact (xw_iz ly S Hp rd M HERRB HIZ a X D). }
assert (EXH' : exh_cell_cf B ly (dtick S) rd').
{ apply (exh_cell_cf_frame B ly ly S (dtick S) rd rd' HEX); [intros c; reflexivity|].
  intros c Hc. apply XN. left. exists c. split; [exact Hc | reflexivity]. }
assert (ERR' : errb_cells_cf B ly (dtick S) rd').
{ apply (errb_cells_cf_frame B ly ly S (dtick S) rd rd' HER); try reflexivity; [|exact VIS].
  intros a Ha. apply XN. right. exact Ha. }
destruct (n_post_parts ly S Hp rd rd' M HIZ HDS sp0 Hsp AG VIS NEWU IAL CONST' EXH' ERR' (fun a Ha => proj1 (HPFA a Ha)))
  as [MF SHAG].
split.
- apply ARX_cf_start; [exact Ei| |exact (xs_mapped_keep_cf ly S (dtick S) md0 _ eq_refl (m_vmmaps_wvb _ _ _) HXM)].
  split; [exact MF | split; [|split; [|split]]].
  + eapply ALedger_same_cf; [exact (ALedger_cf_dtick ly S md0 LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
  + (* the tick moves no budget field (the hull term by cf_hull_frame: YG0ncf.abudget_ok_cf_frame) *)
    eapply abudget_ok_cf_frame with (S := S); [reflexivity | reflexivity | reflexivity | reflexivity | exact BUD].
  + eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
  + eapply (ahs_transfer_cf im_segs B ly S Hp (dtick S) (w_H W) mem0 mem'
      (al_img_env_cf im_segs ly S md0 LY LED) M HSH VIS HSK).
    * intros a _ C. exact C.
    * reflexivity.
    * intros g Hg Hga HF _. exact (SHAG g Hg Hga).
- apply (qtight_ext S); [reflexivity | reflexivity | reflexivity | exact (qmeter_cf_tight S HQ)].
Qed.

Lemma post_c_cf : forall inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat,
  ARX_cf B IOK Hp inst ly S W mem0 md0 -> rpreD_free_cf B S n -> fpre_hp_cf im_segs B Hp ly S W mem0 p n -> In (p, n) (blocks S) -> U_cf B tr S ->
  find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
  rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
  qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
  ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
  0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
  dmem_c W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) lastb (CLdepot.dpost_x im_segs B inst ly S W tr z) mem' ->
  (exists trc, apath (free_cf p tr S) trc (tt, qfin_c S k z tr) /\ gflag trc = true) ->
  ARX_cf B IOK Hp inst ly (qfin_c S k z tr) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ qtight (qfin_c S k z tr).
Proof.
intros inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat (Ei & HAR & HXM) (HU & HQ & HII & HBR & _) HPN HBLK HUtr
  Hf Hst Hrev Hroom Hcache Hlo Hhi Hbot Hal Hhb HV0 DM (trc & Hpath & Hgf).
destruct DM as ((memD & (AOKD & DEPD & CSTD) & PRD & EQD) & MEQ & IALP & SHV & PRS & PRW & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
pose proof HAR as (M0 & LED & BUD & MW & HSH).
pose proof (amc_exh_cell _ _ _ _ _ M0) as HEX. pose proof (amc_errb_cells _ _ _ _ _ M0) as HER.
pose proof (amc_layout _ _ _ _ _ M0) as LY. pose proof (amc_wf _ _ _ _ _ M0) as WF.
pose proof (LGUARD_of_ARmcf ly S Hp _ md0 M0 HIMG LED) as HLG.
pose proof (FP_IZONE_of HIZO HIZR (amc_syms _ _ _ _ _ M0)) as HIZ. pose proof (FP_DZONE_of HDZO HDZF ly HLG) as HDZ.
pose proof (FP_CONST_of HCO ly HLG) as HCOl.
destruct (find_user_block_cf _ 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ WF) HBLK) as (k0 & Hf0 & Hk & Hst0 & Hu & Hr).
rewrite Hf in Hf0. injection Hf0 as <-. subst p n.
(* the final state's invariant: free_cf's law along the granted path *)
pose proof (ml_free_cf (as_universe B) (proj1 HU) S (ck_user k) (ck_req k) tr (proj2 HU) HBR (or_intror HBLK) HUtr) as ATOK.
destruct (atok_cf_apath _ _ _ trc (tt, qfin_c S k z tr) ATOK Hpath) as [ns FP].
assert (WFS' : Wf_cf (as_universe B) (qfin_c S k z tr)) by exact (proj1 FP).
(* the chunk header's second byte (the chunk cell AVmask 127 17 at the entry memory) *)
assert (HB1M : Z.land hb1 127 = 17).
{ assert (C : cell_holds B ly (aview im_segs (w_H W) mem0)
    (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
  { apply (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M0)). unfold acells_cf. rewrite !in_app_iff. do 2 right. left.
    apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_cells. apply in_app_iff. left. cbn. tauto. }
  cbn [cell_holds c_at c_val c_w] in C. rewrite (EA2_cf B ly S Hp _ M0 k _ _ Hk) in C. destruct C as (b & Hb & Hm).
  pose proof (chunk_facts_cf B ly S Hp _ k M0 Hk) as (_ & _ & _ & G4' & _).
  replace (ck_base B ly k + (ck_rz k - kChunkHeaderSize) + 1) with (sptr_addr B ly (ck_user k) - 16 + Z.of_nat 1) in Hb
    by (rewrite G4'; unfold kChunkHeaderSize; lia).
  rewrite (val_mem_aview_cf _ _ _ _ _ 1 HV0 ltac:(lia)) in Hb. injection Hb as <-. rewrite le_byte_hb1_cf in Hm by exact Hhb.
  exact Hm. }
assert (Hsp : ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 <= ly_stk_hi ly) by (split; assumption).
pose proof (al_img_env_cf im_segs ly S md0 LY LED) as SEGS.
pose proof (chunk_facts_cf B ly S Hp _ k M0 Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (ext_rounded_cf B ly S Hp _ M0 k Hk) as (ER & NN1 & NN2 & NN3).
set (rd := aview im_segs (w_H W) mem0) in *. set (rd' := aview im_segs (w_H W) mem') in *.
set (rdD := aview im_segs (w_H W) memD) in *.
(* the frame: outside the walk's windows, the depot zone, the internal allocator's zone and the block's shadow *)
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ Dc ly k lastb sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same_cf.
  assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
  apply MEQ; rewrite Ux.
  - unfold dwin_c. intros [X|[X|X]].
    + apply ND. do 3 right; left. unfold DSc. exact X.
    + apply ND. left. exact X.
    + apply ND. unfold DGgiC.WINB in X. destruct X as [X|[X|[X|X]]].
      * right; left. unfold DKc. left. exact X.
      * right; left. unfold DKc. right. exact X.
      * do 2 right; left. unfold DBc. left. exact X.
      * do 2 right; left. unfold DBc. right. exact X.
  - intros X. apply ND. do 5 right; left. exact X.
  - intros X. apply ND. do 4 right; left. exact X.
  - intros X. apply ND. do 6 right. unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in X.
    rewrite Z_div_mult in X by lia. unfold DHc, shadow_addr. exact X. }
(* visibility: what the entry memory shows, the return memory shows *)
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv. subst rd rd'. unfold aview, mbyte, mrestrict in Hv |- *. set (x := Z_to_bv 64 a) in *.
  destruct (w_H W x) eqn:Hx; [exact Hv|].
  destruct (seg_rom im_segs x) eqn:ROM; [destruct (mem' x); discriminate|].
  destruct (mem' x) as [b|] eqn:E'; [discriminate|]. exfalso.
  assert (Hv0 : mem0 x <> None) by (intros E0; rewrite E0 in Hv; exact (Hv eq_refl)).
  set (a' := bv_unsigned x) in *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False)
    by (intros m [_ [bb Hb]] Hm; rewrite Ex in Hb; congruence).
  assert (EM : forall lo hi (c : Z), (lo <= c < hi) \/ ~ (lo <= c < hi)) by (intros; lia).
  destruct (EM (DGgiC.SPv (sptr_addr B ly (ck_user k))) (DGgiC.SPv (sptr_addr B ly (ck_user k)) + DGgiC.CNT8v (req_size (ck_req k))) a')
    as [Y1|Y1].
  { rewrite (SHV x Y1) in E'. discriminate. }
  destruct (EM (sp0 - DGbaseC.DFSTACK) sp0 a') as [Y2|Y2]. { exact (PRX mem' (PRS a' Y2) E'). }
  assert (WD : (DGgiC.WINT ly a' \/ DGgiC.WINB ly (sptr_addr B ly (ck_user k)) lastb a') \/
    ~ (DGgiC.WINT ly a' \/ DGgiC.WINB ly (sptr_addr B ly (ck_user k)) lastb a')) by (unfold DGgiC.WINT, DGgiC.WINB; lia).
  destruct WD as [Y3|Y3]. { exact (PRX mem' (PRW a' Y3) E'). }
  assert (NDZ : ~ dg_dzone ly a').
  { intros Y5. assert (P0 : apresent (w_H W) mem0 a').
    { split; [rewrite Ex; exact Hx|]. destruct (mem0 x) as [b0|] eqn:E0; [exists b0; rewrite Ex; exact E0 | exfalso; exact (Hv0 eq_refl)]. }
    destruct (PRD a' Y5 P0) as [_ [bd Hbd]]. rewrite Ex in Hbd. rewrite (EQD x Y5) in E'. congruence. }
  assert (NIZ : ~ dg_izone a') by (intros X; destruct (HIZ a' X) as (_ & R & _); rewrite Ex in R; exact (R ROM)).
  rewrite (MEQ x) in E'; [exact (Hv0 E') | | exact NDZ | exact NIZ | exact Y1].
  unfold dwin_c. intros [X|X]; [exact (Y2 X) | exact (Y3 X)]. }
(* the values the walk wrote *)
assert (NEW_hdr : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V1 Hi)).
assert (NEW_n : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 12 + Z.of_nat i) = Some (YG0f.le_byte (ck_n k) 4 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V2 Hi)).
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + Z.of_nat i) =
  Some (YG0f.le_byte (Z.of_nat (length (qc_list (st_qthread S)))) 8 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V3 Hi)).
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 8 + Z.of_nat i) =
  Some (YG0f.le_byte (match qc_list (st_qthread S) with [] => 0 | b0 :: _ => ly_space ly + b_self b0 end) 8 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V4 Hi)).
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 16 + Z.of_nat i) = Some (YG0f.le_byte (ly_space ly + b_self lastb) 8 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V5 Hi)).
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (ly_T ly + t_qc + 24 + Z.of_nat i) =
  Some (YG0f.le_byte (qc_bytes (st_qthread S) + ck_n k) 8 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V6 Hi)).
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ subst rd'. pose proof (val_mem_aview_cf (w_H W) mem' (ly_T ly + t_unwinding) 1 0 0%nat V7 ltac:(lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0. }
assert (NEW_bb : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 8 + Z.of_nat i) =
  Some (YG0f.le_byte (b_bytes lastb + ck_n k) 8 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V8 Hi)).
assert (NEW_bc : forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lastb + 16 + Z.of_nat i) =
  Some (YG0f.le_byte (Z.of_nat (length (b_items lastb)) + 1) 8 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V9 Hi)).
assert (NEW_slot : forall i, (i < 8)%nat ->
  rd' (ly_space ly + b_self lastb + 24 + 8 * Z.of_nat (length (b_items lastb)) + Z.of_nat i) =
  Some (YG0f.le_byte (sptr_addr B ly (ck_user k) - 16) 8 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V10 Hi)).
assert (NEW_sh : forall a, DHc ly k a -> rd a <> None -> rd' a = Some shHeapFreed).
{ intros a Hd Hv. pose proof (cDH_sh ly S Hp rd M0 k lastb Hk a Hd) as [SH1 SH2].
  assert (Ha : kImgEnd <= a < 2 ^ 64) by (unfold kImgEnd, kLowShadowBeg, kHighMemBeg in *; lia).
  pose proof (seg_rom_none_above im_segs a SEGS Ha) as ROM. unfold w64 in ROM.
  subst rd rd'. unfold aview, mbyte, mrestrict in Hv |- *.
  destruct (w_H W (Z_to_bv 64 a)) eqn:Hx.
  - rewrite ROM in Hv. exfalso. exact (Hv eq_refl).
  - rewrite (SHV (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by (unfold kImgEnd in Ha; lia).
    unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v. rewrite Z_div_mult by lia. unfold DHc, shadow_addr in Hd. exact Hd. }
(* the internal allocator's cells, the depot's memory facts and the constant cells at the return memory *)
assert (HIF : st_internal_inited (qfin_c S k z tr) = true)
  by (unfold qfin_c, qx, YFl0C.depot_after, dtick; destruct (z =? 0); cbn [st_internal_inited set_qthread set_chunks set_depot set_nev]; exact HII).
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (qfin_c S k z tr)) /\ Forall (range_zero B ly rd') (ialloc_zero B))
  by (subst rd'; exact (ial_cells_of_post_cf ly (qfin_c S k z tr) W mem' HIF (proj1 (HIAL W mem') IALP))).
assert (DEP : CLdepot.depot_mem_ok B ly (YFl0C.depot_after z tr (dtick S)) rd').
{ assert (EDP : st_depot (CLdepot.depot_after z tr S) = st_depot (YFl0C.depot_after z tr (dtick S)))
    by (unfold CLdepot.depot_after, YFl0C.depot_after, dtick; destruct (z =? 0); reflexivity).
  pose proof (depot_mem_ok_same_cf ly _ _ rdD EDP DEPD) as DEP1.
  apply (depot_mem_ok_fp_cf ly _ rdD rd'); [| | exact DEP1].
  - pose proof (depot_len_bound _ _ (amc_universe _ _ _ _ _ M0) (wfc_depot _ _ _ _ _ WFS')) as LL.
    unfold depot_ids, DEPOT_MAX in *.
    change (st_depot (YFl0C.depot_after z tr (dtick S))) with (st_depot (qfin_c S k z tr)). lia.
  - intros a Hfp. pose proof (aso_cells _ (amc_syms _ _ _ _ _ M0)) as AC.
    assert (Ha : 0 <= a < 2 ^ 64).
    { unfold CLdepot.depot_footprint in Hfp. destruct Hfp as [X|[X|[X|X]]].
      - unfold d_map1, kLowMemEnd in *. lia.
      - pose proof (g_app_oext ly S Hp rd M0 (ly_NB ly, kNodesBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact X)) as AA. pose proof (app_addr_below_ceil a AA). ceil. unfold ASAN_CEIL in *. lia.
      - pose proof (g_app_oext ly S Hp rd M0 (ly_SB ly, kStoreBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact X)) as AA. pose proof (app_addr_below_ceil a AA). ceil. unfold ASAN_CEIL in *. lia.
      - unfold kLowMemEnd in *. lia. }
    subst rd' rdD. apply aview_same_cf. apply EQD. rewrite unsigned_lit_small by exact Ha. exact (proj1 (HDZ a) Hfp). }
assert (ODEC : forall o1 o2 : option Z, {o1 = o2} + {o1 <> o2}) by (decide equality; apply Z.eq_dec).
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc.
  apply (cell_holds_mix_cf ly rdD rd rd' c (proj1 (Forall_forall _ _) CSTD c Hc) (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M0) c Hc)).
  intros j Hj. destruct (g_const_loc ly S Hp rd M0 c j Hc Hj) as [R64 _].
  destruct (ODEC (rd' (aeval B ly (c_at c) + j)) (rdD (aeval B ly (c_at c) + j))) as [E|NE]; [left; exact E | right].
  assert (ND : ~ dg_dzone ly (aeval B ly (c_at c) + j)).
  { intros Hd. apply NE. subst rd' rdD. apply aview_same_cf. apply EQD. rewrite unsigned_lit_small by exact R64. exact Hd. }
  destruct (c_const_ok ly S Hp rd M0 k lastb initr Hk Hrev z tr rd' hb1 (conj Hhb HB1M) Hroom sp0 Hsp IAL HCOl c j Hc Hj ND)
    as [R64' NDc].
  exact (AG _ R64' NDc). }
(* the hidden bytes of the shadow band do not change *)
assert (SHP : forall a, DHc ly k a -> w_H W (Z_to_bv 64 a) = false).
{ intros a Hd. destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; [|reflexivity]. exfalso.
  pose proof (cDH_sh ly S Hp rd M0 k lastb Hk a Hd) as [SH1 SH2].
  assert (Ha : kImgEnd <= a < 2 ^ 64) by (unfold kImgEnd, kLowShadowBeg, kHighMemBeg in *; lia).
  pose proof (seg_rom_none_above im_segs a SEGS Ha) as ROM. unfold w64 in ROM.
  pose proof (u_al8_cf B ly S Hp rd M0 k Hk) as (U8 & B8 & R8).
  apply Z.mod_divide in U8 as [c Hc]; [|lia].
  unfold DHc, shadow_addr in Hd. rewrite Hc, Z_div_mult in Hd by lia.
  set (g := c * 8 + 8 * (a - (SHADOW_OFF + c))).
  assert (Eg : shadow_addr g = a) by (unfold shadow_addr, g; replace (c * 8 + 8 * (a - (SHADOW_OFF + c))) with ((a - SHADOW_OFF) * 8) by lia;
    rewrite Z_div_mult by lia; lia).
  assert (G8' : g mod 8 = 0) by (unfold g; replace (c * 8 + 8 * (a - (SHADOW_OFF + c))) with ((a - SHADOW_OFF) * 8) by lia; apply Z_mod_mult).
  assert (Gb : ck_base B ly k <= g < ck_base B ly k + ck_extent k) by (unfold g; lia).
  assert (FC : find_chunk_at B ly (st_chunks S) g = Some k)
    by (apply (find_chunk_at_hit_cf B ly S Hp rd (st_chunks S) k g M0 ltac:(intros y Hy; exact Hy) (wfc_chunks_nodup _ _ _ _ _ WF) Hk Gb)).
  pose proof (amc_shadow _ _ _ _ _ M0 g _ G8' ltac:(unfold ashadow; rewrite FC; reflexivity)) as R. rewrite Eg in R.
  subst rd. unfold aview, mbyte, mrestrict in R. rewrite Hx, ROM in R. discriminate R. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem0 (w64 a)).
{ intros a Hb Hh.
  assert (Ha64 : 0 <= a < 2 ^ 64)
    by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia).
  unfold w64 in *. assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha64).
  assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh' _]; rewrite Hh in Hh'; discriminate).
  apply MEQ; rewrite Ux.
  - unfold dwin_c. intros [X|[X|X]]; [exact (PRX mem' (PRS a X)) | exact (PRX mem' (PRW a (or_introl X)))
      | exact (PRX mem' (PRW a (or_intror X)))].
  - intros X. destruct (proj2 (HDZ a) X) as (_ & [FP'|OS]).
    + unfold CLdepot.depot_footprint in FP'. destruct FP' as [Y|[Y|[Y|Y]]].
      * pose proof (g_static_img ly S Hp rd M0 a (HDS a (or_introl Y))) as HI. pose proof (g_img ly S Hp rd M0) as (I0 & I1 & I2).
        unfold in_zr in HI. clear - Hb HI I0 I2. unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
      * pose proof (g_app_oext ly S Hp rd M0 (ly_NB ly, kNodesBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact Y)) as AA.
        clear - Hb AA. unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *.
        ceil. unfold ASAN_CEIL in *. lia.
      * pose proof (g_app_oext ly S Hp rd M0 (ly_SB ly, kStoreBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact Y)) as AA.
        clear - Hb AA. unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *.
        ceil. unfold ASAN_CEIL in *. lia.
      * pose proof (g_static_img ly S Hp rd M0 a (HDS a (or_intror Y))) as HI. pose proof (g_img ly S Hp rd M0) as (I0 & I1 & I2).
        unfold in_zr in HI. clear - Hb HI I0 I2. unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
    + pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M0) OS) as [X1 X2].
      clear - Hb X1 X2. unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
  - intros C. destruct (HIZ a C) as (OS & _).
    pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M0) OS) as [X1 X2].
    clear - Hb X1 X2. unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
  - intros X. assert (XD : DHc ly k a).
    { unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in X. rewrite Z_div_mult in X by lia. unfold DHc, shadow_addr. exact X. }
    pose proof (SHP a XD) as F. rewrite Hh in F. discriminate. }
(* the machine cells (ARmcf's fields): off the walk's writes *)
assert (LBc : In lastb (all_batches S)).
{ assert (QL : qc_list (st_qthread S) = rev initr ++ [lastb])
    by (rewrite <- (rev_involutive (qc_list (st_qthread S))), Hrev; reflexivity).
  unfold all_batches. rewrite QL, !in_app_iff. left. right. left. reflexivity. }
assert (XN : forall a, XC B ly a -> rd' a = rd a).
{ intros a X. pose proof (x_owned B ly S Hp rd M0 a X) as [R64 _]. apply AG; [exact R64|].
  unfold Dc, DKc, DBc, DSc, DHc. intros [D|[D|[D|[D|[D|[D|D]]]]]].
  - apply (x_T B ly S Hp rd M0 a X). unfold DGgiC.WINT in D.
    unfold t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
  - exact (x_kwords B ly S Hp rd M0 k a Hk X D).
  - exact (x_bcells B ly S Hp rd M0 lastb a LBc Hroom X D).
  - exact (x_S B ly S Hp rd M0 a sp0 X Hsp D).
  - exact (xw_iz ly S Hp rd M0 HERRB HIZ a X D).
  - exact (xw_dz ly S Hp rd M0 HERRB HDS HDZ HLG a X D).
  - exact (x_kshadow B ly S Hp rd M0 k a Hk X D). }
assert (EXH' : exh_cell_cf B ly (qfin_c S k z tr) rd').
{ apply (exh_cell_cf_frame B ly ly S (qfin_c S k z tr) rd rd' HEX).
  - intros c. unfold qfin_c, qx, YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity.
  - intros c Hc. apply XN. left. exists c. split; [exact Hc | reflexivity]. }
assert (ERR' : errb_cells_cf B ly (qfin_c S k z tr) rd').
{ apply (errb_cells_cf_frame B ly ly S (qfin_c S k z tr) rd rd' HER);
    try (unfold qfin_c, qx, YFl0C.depot_after, dtick; destruct (z =? 0); reflexivity); [|exact VIS].
  intros a Ha. apply XN. right. exact Ha. }
(* the relation of the final state *)
destruct (c_post_parts ly S Hp rd M0 k lastb initr Hk Hst Hrev z tr rd' HIZ HDS HDZ hb1 (conj Hhb HB1M) Hroom WFS' sp0 Hsp
  AG VIS NEW_hdr NEW_n NEW_qs NEW_qf NEW_ql NEW_qb NEW_unw NEW_bb NEW_bc NEW_slot NEW_sh IAL DEP CONST' HPN EXH' ERR'
  (fun a Ha => conj (proj1 (HPFA a Ha)) (proj2 (HPFA a Ha) ly HLG)))
  as [MF SHAG].
split.
- apply ARX_cf_start; [exact Ei| |exact (xs_mapped_keep_cf ly S _ md0 _ (cs_secs S k z tr) (m_vmmaps_wvb _ _ _) HXM)].
  split; [exact MF | split; [|split; [|split]]].
  + eapply ALedger_same_cf; [exact (cs_ledger ly S Hp rd M0 k Hk z tr md0 LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
  + destruct BUD as (BU1 & BU2 & BU3). split; [|split; [|exact BU3]].
    * rewrite (cs_budget ly S Hp rd M0 k Hk z tr). exact BU1.
    * intros e He. rewrite (cs_sec_extents ly S Hp rd M0 k Hk z tr) in He. exact (BU2 e He).
  + eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
  + eapply (ahs_transfer_cf im_segs B ly S Hp (qfin_c S k z tr) (w_H W) mem0 mem' SEGS M0 HSH VIS HSK).
    * intros a _ C. exact (cs_client ly S Hp rd M0 k Hk z tr a C).
    * exact (cs_sec_extents ly S Hp rd M0 k Hk z tr).
    * intros g Hg Hga HF _. exact (SHAG g Hg Hga HF).
- exact (cs_qtight ly S Hp rd M0 k lastb initr Hk Hst Hrev z tr Hcache (qmeter_cf_tight S HQ)).
Qed.
End p.
End a.
