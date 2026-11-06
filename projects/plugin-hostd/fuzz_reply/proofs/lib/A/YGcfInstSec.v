(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   The cf twin of proofs/cgif/cgif_file_fuzzer/lib/AGif5.v and AGif5E.v at c5 30a1993588f: the SECONDARY Allocate
   interfaces AGif4.AIfaceS, AGif4.AIfaceSw and ErrnoGS.AIfaceSE at the call-site relation YGcfInstBase.ARXq_cf,
   generic over CfImg / CfParams and the image classes ImgBase.AImg / ImgBaseAG.AGImg / ImgBaseAGS.AImgS.
   rule 24: no function proved (interface-instance discharge at a model relation; no machine walk is written).

   The fixed arguments are YGcfInstBase's: U := U_cf B, mt := malloc_cf, ARX := ARXq_cf B IOK Hp, AOX := AOX_cf B,
   rpre := rpre_cf B, nmax := cf_malloc_max, lmax := LIVE_MAX, lpost := qtight, dpost := YGcfInstHit.dpost_cf B,
   mtag := cf_pc_malloc_max and stag := cf_pc_spin_shadow (the two labels malloc_cf uses, YG00cf.v:237 / :249).
   The widened form takes NMAXW := cf_malloc_max, NOBW := cf_nob and the room ROOMW as a Section variable.

   Field order and lemma names follow AGif5.v (view, shape, fresh, depot, mwf, room, ledger, grant, apart, oom,
   post_null, post_grant), with AR replaced by ARcf, cgif's regime and meter premises by the relation's qtight, malloc by malloc_cf
   and MALLOC_MAX by cf_malloc_max.  What a unit must supply about its image (its symbol table at the image classes,
   its instance object's constant cells, its depot contract) is a NAMED Section hypothesis below; none names a unit's
   numeral.
   EVENT-FREE: no event counter, event bound, regime or cgif meter term appears in this file; the only event term is
   the tick update `set_nev (st_nev S + 1) S` inside the interfaces' own statements. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
(* YFib before YG04 / ImgBaseAGS: their KS / rS / sfinal / depF / resF / upd_chunk_fresh shadow YFib's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b YG0g YG0h YG0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG ImgBaseAGS AGif2 AllocG AGif4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YM03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoG ErrnoGS ErrnoApart ErrnoApartS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require SecGrantP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require SecGrantW CLdepot.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0qcf YG0scf YG03cf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstHit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstErrno YGcfInstDepot YGcfDIface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG02cf YG07cf YG07 YK0g YG0tcf YGcfRoomStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfAbudget YGcfRoomCf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfImgRows YGcfLazyMaps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfErrbSep.
(* stdpp, through the LPS modules, shadows several list names; the list lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
(* ErrnoGS / ErrnoApartS's Require hazard (their headers): restore lia's euclidean division after the Requires. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
(* plain linear arithmetic: this lib's lia is YM05's, which starts with rc_inst *)
Local Ltac zl := YM03.lf_lia_orig.
Local Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
(* YG0j's mproj (section-local there) *)
Local Ltac mproj :=
  repeat first [ rewrite YK0g.m_vmmaps_with_vm_backing | rewrite YK0g.m_vm_lazy_with_vm_backing
  | rewrite YK0g.m_vmmaps_with_vmmaps | rewrite YK0g.m_vm_lazy_with_vmmaps ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {IM : AImg} {AG : AGImg} {IMS : AImgS}.
Local Open Scope am_scope.

(* ================================================================================================================ *)
(* 0. Generic helpers (no image, no instance).                                                                      *)
Lemma pw_ij {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l (i + S j) = Some y -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hx Hy; [destruct i; discriminate|].
destruct P as [F P]. destruct i as [|i]; cbn in Hx, Hy.
- injection Hx as <-. apply (proj1 (Forall_forall _ _) F). exact (nth_error_In _ _ Hy).
- exact (IH i j x y P Hx Hy).
Qed.

Lemma aview_same_g : forall segs (H : word -> bool) (mem mem' : word -> option byte) a,
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview segs H mem' a = aview segs H mem a.
Proof. intros segs H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma owned_not_img : forall ly e a, layout_ok ly -> In e (owned_extents ly) -> in_zr a e -> ~ in_zr a (ly_img ly).
Proof.
intros ly e a LY He Ha Hi.
pose proof (cfb_pairwise_app zdisjoint (owned_extents ly) [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] e (ly_img ly)
  (lo_disj ly LY) He ltac:(right; left; reflexivity)) as D.
unfold zdisjoint, in_zr in *. zl.
Qed.

Lemma owned_range : forall ly e a, layout_ok ly -> In e (owned_extents ly) -> in_zr a e -> 0 <= a < 2 ^ 64.
Proof.
intros ly e a LY He Ha. pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e He) as [A1 A2]. ceil.
unfold in_zr in Ha. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zl.
Qed.

Lemma zr_dec : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. zl. Qed.

Lemma u8_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz. Qed.

(* A byte of a val_mem fact, read through aview (AGif5.vm_aview over any segment list). *)
Lemma vm_aview_g : forall segs (Hh : word -> bool) m a (w : nat) v k, val_mem segs (mrestrict Hh m) a w v -> (k < w)%nat ->
  aview segs Hh m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros segs Hh m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map].
change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal.
apply u8_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. zl.
Qed.
Lemma apresent_view_g : forall segs (Hh : word -> bool) m u, apresent Hh m u -> aview segs Hh m u <> None.
Proof. intros segs Hh m u [Hh0 [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh0, Hb. cbn. discriminate. Qed.
Lemma le_byte_zero : forall w k, YG0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YG0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; zl). rewrite Z.shiftr_0_l. reflexivity. Qed.

(* The secondary block's map size (AGjm's MSv over ImgBaseAGS) below 2 ^ 30, and the by_size_log word it selects. *)
Lemma msv_facts : forall n, 64513 <= n < 2 ^ 30 ->
  73728 <= ImgBaseAGS.MSv n <= 262147 * 4096 /\ ImgBaseAGS.MSv n mod 4096 = 0 /\ n + 8192 <= ImgBaseAGS.MSv n.
Proof.
intros n Hn. unfold ImgBaseAGS.MSv, ImgBaseAGS.NDv, ImgBaseAGS.R8v.
pose proof (Z.div_mod (n + 7) 8 ltac:(zl)) as D1. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zl)) as M1.
set (q := (n + 7) / 8) in *.
pose proof (Z.div_mod (q * 8 + 4096 + 4095) 4096 ltac:(zl)) as D2. pose proof (Z.mod_pos_bound (q * 8 + 4096 + 4095) 4096 ltac:(zl)) as M2.
set (p := (q * 8 + 4096 + 4095) / 4096) in *.
split; [zl|]. split; [|zl].
replace (p * 4096 + 4096) with ((p + 1) * 4096) by zl. apply Z_mod_mult.
Qed.
Lemma bsl_bounds : forall (regs0 : bvmap 5 word) n, 64513 <= n < 2 ^ 30 ->
  bv_unsigned (getr regs0 11) + 296 <= ImgBaseAGS.BSLv regs0 n /\ ImgBaseAGS.BSLv regs0 n + 8 <= bv_unsigned (getr regs0 11) + 416.
Proof.
intros regs0 n Hn. pose proof (msv_facts n Hn) as (M1 & _).
unfold ImgBaseAGS.BSLv, ImgBaseAGS.LGv.
assert (Q1 : 18 <= ImgBaseAGS.MSv n / 4096 <= 262147)
  by (split; [apply Z.div_le_lower_bound; zl | apply Z.div_le_upper_bound; zl]).
pose proof (Z.log2_le_mono (ImgBaseAGS.MSv n / 4096) 262147 ltac:(zl)) as L2. rewrite (eq_refl : Z.log2 262147 = 18) in L2.
pose proof (Z.log2_le_mono 18 (ImgBaseAGS.MSv n / 4096) ltac:(zl)) as L1. rewrite (eq_refl : Z.log2 18 = 4) in L1.
zl.
Qed.

Lemma cell_holds_agree_g : forall B ly (rd rd' : reader) c,
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
  cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros B ly rd rd' c He Hc. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. rewrite He by zl. exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm].
  rewrite <- (Z.add_0_r (aeval B ly (c_at c))). rewrite He by zl. rewrite Z.add_0_r. exact Hb.
Qed.
Lemma cell_holds_agree2_g : forall B ly (rd1 rd2 rd' : reader) c,
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
     rd' (aeval B ly (c_at c) + k) = rd1 (aeval B ly (c_at c) + k) \/ rd' (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
  cell_holds B ly rd1 c -> cell_holds B ly rd2 c -> cell_holds B ly rd' c.
Proof.
intros B ly rd1 rd2 rd' c He H1 H2. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. destruct (He (Z.of_nat k) ltac:(zl)) as [E|E]; rewrite E; [exact (H1 k Hk) | exact (H2 k Hk)].
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
  destruct (He 0 ltac:(zl)) as [E|E]; rewrite Z.add_0_r in E; rewrite E; [exists b1 | exists b2]; tauto.
Qed.

(* CLdepot's depot memory facts read their reader only through it (cgif: AGif5.depot_mem_ok_rdext). *)
Lemma dmo_rdext : forall B ly S (rd rd' : reader), rd_ext rd rd' ->
  CLdepot.depot_mem_ok B ly S rd -> CLdepot.depot_mem_ok B ly S rd'.
Proof.
intros B ly S rd rd' Hx (D1 & D2 & D3). split; [|split].
- eapply Forall_cell_holds_ext; eassumption.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
  + intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. apply Hx, Hr, Hk.
  + intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split; intros k Hk; apply Hx; auto.
- eapply Forall_range_vis_ext; eassumption.
Qed.

(* ... and only on the depot's footprint (cgif: AGif5.depot_mem_ok_agreeS over AGjm.DZONE; here over the image-free
   CLdepot.depot_footprint, which covers every byte the facts read when the depot has at most 4098 ids). *)
Lemma dmo_agree_fp : forall B ly S (rd rd' : reader), depot_ids S <= 4098 ->
  (forall a, CLdepot.depot_footprint B ly a -> rd' a = rd a) ->
  CLdepot.depot_mem_ok B ly S rd -> CLdepot.depot_mem_ok B ly S rd'.
Proof.
intros B ly S rd rd' HID He (D1' & D2 & D3).
assert (EZ : forall a, (as_depot B <= a < as_depot B + d_map1 + 8) \/ (as_store B <= a < as_store B + 32) \/
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> rd' a = rd a).
{ intros a Ha. apply He. unfold CLdepot.depot_footprint, d_map1 in *. zl. }
split; [|split].
- apply Forall_forall. intros c Hc. apply (cell_holds_agree_g B ly rd); [| exact (proj1 (Forall_forall _ _) D1' c Hc)].
  intros k Hk. apply EZ. unfold depot_cells in Hc. cbn in Hc.
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [c_at c_w aeval aoff z4 z8 c4 c8] in *; cbn in Hk;
  unfold d_nuniq, d_map1, s_total, s_block0 in *; zl.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
  + intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|].
    unfold d_tab_words, d_map1 in *. zl.
  + intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
    * intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. unfold kNodesBlockSize. zl.
    * intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. unfold kNodesBlockSize. zl.
- apply Forall_forall. intros r Hr i Hi. rewrite EZ; [exact (proj1 (Forall_forall _ _) D3 r Hr i Hi)|].
  cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval aoff] in *; unfold d_nuniq, d_map1 in *; zl.
Qed.

(* ================================================================================================================ *)
(* 0b. The anonymous grant at the cf ledger: YG0j.anon_grant_facts (YG0j.v:292-367) over ALedger_cf, and YFia's     *)
(*     grant facts (YFia.v:55-122) over it.  The only change: cgif's wf_noholes is YG0scf.wf_no_prim_hole_cf (the   *)
(*     cf classes carry one length-0 sentinel hole, which covers no address).                                        *)
Lemma anon_grant_facts_cf : forall segs U pp cc bb ly S md (a n : word),
layout_ok ly -> WfP_cf U pp cc bb S -> sec_placed ly S -> ALedger_cf segs ly S md ->
grant_ok_na_pin md a (bv_unsigned n) = true -> 0 < bv_unsigned n -> bv_unsigned n mod 4096 = 0 ->
page_aligned (bv_unsigned a) /\ in_app (bv_unsigned a) (bv_unsigned n) /\ bv_unsigned a + bv_unsigned n <= ASAN_CEIL /\
Forall (zdisjoint (bv_unsigned a, bv_unsigned n)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps).
Proof.
intros segs U pp cc bb ly S md a n LO W PL L G Hn Hnal.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
unfold grant_ok_na_pin in G. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. unfold page_size in G1.
assert (Hn64 : Z_to_bv 64 (bv_unsigned n) = n) by (apply w64_uw). rewrite Hn64 in G4.
set (lo := bv_unsigned a) in *. set (len := bv_unsigned n) in *.
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
assert (CE : lo + len <= ASAN_CEIL).
{ unfold ASAN_CEIL. apply (YM05.grant_below_ceil (alloc_top (m_vmmaps md)) (lo + len) L13); [| exact G3].
  apply Z.mod_divide in G1 as [q Hq]; [|zl]. apply Z.mod_divide in Hnal as [q' Hq']; [|zl]. rewrite Hq, Hq'.
  replace (q * 4096 + q' * 4096) with ((q + q') * 4096) by zl. apply Z_mod_mult. }
ceil.
assert (RF : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 ->
  In (wiv z) (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. pose proof (YK13.region_free_In _ a n (w64 (fst z)) (w64 (snd z)) G4 Hin) as D.
  unfold w64 in D. rewrite !Z_to_bv_unsigned, !bv_wrap_small in D by (unfold bv_modulus; zl). unfold zdisjoint. cbn [fst snd].
  subst lo len. zl. }
assert (RFm : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 -> In (wiv z) (vm_maps (m_vmmaps md)) ->
  zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. apply RF; [exact Z1 | exact Z2 | exact Z3 | apply in_app_iff; right; exact Hin]. }
assert (BAND : Forall (zdisjoint (lo, len)) band_maps).
{ apply Forall_forall. intros z Hz. apply RFm; [ | | | exact (L11 z Hz)]; unfold band_maps in Hz; cbn in Hz;
  destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; zl. }
assert (APP : in_app lo len).
{ pose proof BAND as B'. unfold band_maps in B'. apply Forall_cons_iff in B' as [D1 B']. apply Forall_cons_iff in B' as [D2 B'].
  apply Forall_cons_iff in B' as [D3 _].
  unfold zdisjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3. unfold in_app.
  unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *.
  split; [| clear - D1 D2 D3 Hn CE CR0; zl].
  apply Z.mod_divide in G1 as [q Hq]; [|zl]. subst lo len. clear - Hq G2. zl. }
split; [exact G1|]. split; [exact APP|]. split; [exact CE|].
pose proof (lo_high ly LO) as [HP1 HP2].
assert (PRIM : zdisjoint (lo, len) (ly_prim ly, kPrimResvSize)).
{ destruct L4 as (pieces & (P1 & P2 & P3) & P4).
  unfold zdisjoint. cbn [fst snd].
  destruct (Z_lt_le_dec lo (ly_prim ly + kPrimResvSize)) as [X1|X1]; [|right; zl].
  destruct (Z_lt_le_dec (ly_prim ly) (lo + len)) as [X2|X2]; [|left; zl]. exfalso.
  set (x := Z.max lo (ly_prim ly)).
  assert (Hx : ly_prim ly <= x < ly_prim ly + kPrimResvSize) by (subst x; unfold kPrimResvSize in *; zl).
  assert (NH : ~ prim_hole_at ly S x) by exact (wf_no_prim_hole_cf U pp cc bb S ly x W).
  apply (P3 x Hx) in NH. apply Exists_exists in NH as (p0 & Hp0 & Hin0). unfold in_zr in Hin0.
  pose proof (proj1 (P4 p0) Hp0) as (Hm0 & C1 & C2 & C3).
  pose proof (RFm p0 ltac:(unfold kHighMemBeg in HP1; zl) ltac:(zl)
    ltac:(clear - C2 C3 HP1 HP2 CR CR0; unfold kPrimResvSize, kHighMemBeg, ASAN_CEIL in *; zl) Hm0) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. subst x. zl. }
pose proof (lo_stk_ceil ly LO) as STK.
assert (IMG : zdisjoint (lo, len) (ly_img ly)).
{ pose proof (lo_img ly LO) as (J0 & J1 & J2 & J3). unfold zdisjoint. cbn [fst snd].
  destruct (Z_lt_le_dec lo (fst (ly_img ly) + snd (ly_img ly))) as [X1|X1]; [|right; zl].
  destruct (Z_lt_le_dec (fst (ly_img ly)) (lo + len)) as [X2|X2]; [|left; zl]. exfalso.
  set (x := Z.max lo (fst (ly_img ly))).
  destruct (L14 x ltac:(unfold in_zr; subst x; zl)) as (e & He & E1).
  pose proof (YK13.region_free_In _ a n (fst e) (snd e) G4 ltac:(apply in_app_iff; left; rewrite L3, <- surjective_pairing; exact He)) as D.
  subst lo len x. zl. }
assert (PERM : Forall (zdisjoint (lo, len)) (perm_maps ly)).
{ apply Forall_forall. intros z Hz. pose proof (perm_facts ly 1 LO ltac:(zl) z Hz) as (Z1 & Z2 & Z3 & _).
  apply RFm; [zl | zl | zl | exact (L10 z Hz)]. }
assert (SEC : Forall (zdisjoint (lo, len)) (sec_extents ly S)).
{ apply Forall_forall. intros e He. destruct PL as [PF _]. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [E1 E2] & E3).
  pose proof (proj1 (Forall_forall _ _) (sec_extents_sizes64P_cf U pp cc bb ly S W) e He) as E4. cbn beta in E4.
  apply RFm; [zl | zl | unfold ASAN_CEIL in *; zl | exact (L7 e He)]. }
rewrite !Forall_app. split; [| split; [exact SEC | split; [exact PERM | exact BAND]]].
unfold static_extents, owned_extents. apply Forall_app. split.
- pose proof PERM as PM. unfold perm_maps in PM. apply Forall_app in PM as [PM _].
  apply Forall_cons_iff in PM as [PT PM]. apply Forall_cons_iff in PM as [PFk PM]. apply Forall_cons_iff in PM as [PNB PM].
  apply Forall_cons_iff in PM as [PSB PM]. apply Forall_cons_iff in PM as [PC PM]. apply Forall_cons_iff in PM as [PD _].
  assert (QQ : zdisjoint (lo, len) (ly_Q ly, kPtrArrayResv)).
  { pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [Q1 Q2].
    cbn [fst snd] in Q1, Q2.
    apply RFm; [cbn [fst]; zl | cbn [snd]; unfold kPtrArrayResv; zl
      | cbn [fst snd]; unfold kLowShadowBeg, kPtrArrayResv, ASAN_CEIL in *; zl | exact L5]. }
  repeat apply Forall_cons; try apply Forall_nil; try assumption.
  unfold zdisjoint in PC |- *. cbn [fst snd] in PC |- *. unfold kCtxMapSize in PC. zl.
- apply Forall_cons; [| apply Forall_cons; [exact IMG | apply Forall_nil]].
  unfold zdisjoint. cbn [fst snd]. left. unfold ASAN_CEIL in *. zl.
Qed.

Section G.
Variables (segs : list Segment) (U : Univ) (ly : alayout) (S : astate) (md : Model) (a : word) (nZ : Z).
Hypothesis LY : layout_ok ly.
Hypothesis WF : Wf_cf U S.
Hypothesis PL : sec_placed ly S.
Hypothesis L : ALedger_cf segs ly S md.
Hypothesis HnZ : 0 < nZ < 2 ^ 40.
Hypothesis HnZal : nZ mod 4096 = 0.
Hypothesis HG : grant_ok_na_pin md a nZ = true.
Let A : Z := bv_unsigned a.
Lemma gf_word : bv_unsigned (Z_to_bv 64 nZ) = nZ.
Proof. apply w64_unsigned. zl. Qed.
Lemma gf_facts : page_aligned A /\ in_app A nZ /\ A + nZ <= ASAN_CEIL /\
  Forall (zdisjoint (A, nZ)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps).
Proof.
pose proof (anon_grant_facts_cf segs U 0 0 0 ly S md a (Z_to_bv 64 nZ) LY WF PL L) as X.
rewrite gf_word in X. exact (X HG (proj1 HnZ) HnZal).
Qed.
Lemma gf_img : zdisjoint (A, nZ) (ly_img ly).
Proof.
pose proof gf_facts as (_ & _ & _ & FA). rewrite !Forall_app in FA. destruct FA as (FS & _ & _ & _).
apply (proj1 (Forall_forall _ _) FS). unfold static_extents. apply in_or_app. right. cbn. tauto.
Qed.
Lemma gf_apart : Forall (zdisjoint (A, nZ)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Proof.
pose proof gf_facts as (_ & _ & _ & FA). rewrite !Forall_app in FA. destruct FA as (FS & FSEC & FP & FB).
rewrite !Forall_app. split; [exact FS | split; [| exact FSEC]].
pose proof FP as FP'. unfold perm_maps in FP'. apply Forall_app in FP' as [FP6 FX].
apply Forall_cons_iff in FP6 as [PT FP6]. apply Forall_cons_iff in FP6 as [PF FP6]. apply Forall_cons_iff in FP6 as [PNB FP6].
apply Forall_cons_iff in FP6 as [PSB FP6]. apply Forall_cons_iff in FP6 as [PC FP6]. apply Forall_cons_iff in FP6 as [PD _].
assert (PQ : zdisjoint (A, nZ) (ly_Q ly, kPtrArrayResv)).
{ apply (proj1 (Forall_forall _ _) FS). unfold static_extents, owned_extents. cbn. tauto. }
assert (PP : zdisjoint (A, nZ) (ly_prim ly, kPrimResvSize)).
{ apply (proj1 (Forall_forall _ _) FS). unfold static_extents, owned_extents. cbn. tauto. }
pose proof gf_img as PI.
pose proof (lo_space_in ly LY) as SPI.
unfold vis0_zones. apply Forall_app. split; [| exact FX].
repeat (apply Forall_cons; [first [assumption | unfold zdisjoint in *; cbn [fst snd] in *; unfold kRegionInfoOff, kPrimResvSize, kSpaceSize in *; zl] |]).
apply Forall_nil.
Qed.
Lemma gf_hfree : forall g, A <= g -> g + 8 <= A + nZ -> hfree ly S g.
Proof.
intros g G1 G2. unfold hfree. apply Forall_impl with (2 := gf_apart). intros z Hz. unfold zdisjoint in Hz. cbn [fst snd] in Hz. zl.
Qed.
Lemma gf_shadow_zero : forall mem g, ahz ly S mem -> g mod 8 = 0 -> A <= g -> g + 8 <= A + nZ ->
  mem (Z_to_bv 64 (shadow_addr g)) = Some (Z_to_bv 8 0).
Proof.
intros mem g HZ Hg G1 G2. pose proof gf_facts as (_ & AP & Hce & _).
apply (HZ g Hg); [| exact (gf_hfree g G1 G2)].
ceil. unfold in_app, ASAN_CEIL in *. zl.
Qed.
End G.

(* ================================================================================================================ *)
(* 1. The instance.                                                                                                 *)

(* The instance-cell image fact (the ONE name the cf instance files cite): the instance object's constant cells that
   AGif2.sview reads, wherever the constant cells hold [cgif: tfib_const_lookup / tfib_const_lookup_sym over
   Tfib_const, AGif5.v:248-257].  An IMAGE fact: a lookup in the unit's const-cell table. *)
Definition INST_CELLS_t (B : asyms) : Prop :=
  forall ly (H : word -> bool) (mem : word -> option byte), layout_ok ly -> ly_tsd ly = as_tsd B ->
  Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly) ->
  val_mem im_segs (mrestrict H mem) (as_inst B + o_space) 8 (ly_space ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 0xe20) 8 0x10000000000 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 0xe28) 8 0x108000010 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec) 8 4096 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_chunks) 8 (ly_Q ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 80) 8 (ly_Q ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 88) 8 kPtrArrayResv /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_mutex + 1) 3 0.

(* Printf's two writable image cells (field round 3: ARmcf's amc_pf_cells) lie apart from the out-of-memory byte, which
   the refusal arm writes, and from the secondary walk's depot write zone ims_dzone [cgif: toolname cell 0xa00e0, pfcb
   cell 0x137f90, oom byte 0x1284e0, AGjm.DZONE's image part from 0x178148].  An IMAGE fact. *)
Definition PF_SEP_t (B : asyms) : Prop :=
  forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
  a <> as_oom_byte B /\ ~ ims_dzone ly a.

Section b.
Variable B : asyms.
Variable IOK : Z -> Prop.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The unit's side: what its image and its instance object give.  Each is a fact about the unit's own symbol table, *)
(* image classes or released depot contract, discharged once at its image (cgif_file's values in brackets).          *)
(* The walk's instance object is the symbol table's: the model's secondary counters are at AInst (as_inst B + .)
   (the Base's one name, YGcfInstBase.IOK_ok). *)
Hypothesis IOK_inst : IOK_ok B IOK.
(* The ledger's image window covers the image: the kit's YGcfDIface.IMG_COVER [cgif: img_cover_of_ledger]. *)
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Let IMGC : forall ly S md, ALedger_cf im_segs ly S md -> im_img_cover ly := HIMG.
(* The symbol table at the image classes [cgif: ts_tsd, ts_oom]. *)
Hypothesis SYM_TSD : as_tsd B = im_tsd.
Hypothesis SYM_OOM : as_oom_byte B = im_oom.
(* The instance object's constant cells (INST_CELLS_t above). *)
Hypothesis INST_CELLS : INST_CELLS_t B.
(* The combined allocator's stats words are image bytes no world hides [cgif: rw_view, YB1h.tfib_rw_window]. *)
Hypothesis COMB_VIS : forall (H : word -> bool) (mem : word -> option byte) a,
  as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview im_segs H mem a <> None.
(* A grant apart from the image window in the application range is in the image's grant zones [cgif: zone3_intro]. *)
Hypothesis ZONE3 : forall ly x sz, im_img_cover ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) ->
  ims_zone3 x sz.
(* The released depot contract at the image [cgif: YFl0.tfib_depot_spec], as CLdepot states it. *)
Hypothesis HD : CLdepot.depot_spec_x im_segs ims_depot im_tp im_img_cover B.
(* The constant cells hold at a memory that keeps the secondary walk's const zone CZS and the depot zone as at the
   relation's memory, with the mutex's three pad bytes 0 [cgif: AGif5.const_cells_CZS, AGif5.v:336-372]. *)
Hypothesis CONST_KEEP_S : forall ly (H : word -> bool) (mem0 mem : word -> option byte),
  layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  Forall (cell_holds B ly (aview im_segs H mem0)) (as_const B ly) ->
  (forall x : word, ims_dzone ly (bv_unsigned x) \/ CZS ly (as_inst B) (bv_unsigned x) -> mem x = mem0 x) ->
  (forall k, 1 <= k < 4 -> aview im_segs H mem (as_inst B + o_sec_mutex + k) = Some 0) ->
  Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly).
(* What StackDepotPut writes is in the secondary walk's depot zone [cgif: AGif5.footprint_DZ]. *)
Hypothesis DEP_FP : YGcfInstDepot.dep_fp_img B ims_dzone.
(* The depot's image bytes are never hidden [cgif: YFff.rw_unhidden]. *)
Hypothesis DEP_UNHID : forall (W : world im_segs) a,
  (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) ->
  w_H W (Z_to_bv 64 a) = false.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Model facts of ARcf.                                                                                             *)
Section m.
Variables (Hp : list Z) (ly : alayout) (S : astate) (W : world im_segs) (mem : word -> option byte) (md : Model).
Hypothesis HAR : ARcf im_segs B ly S Hp W mem md.
Let M : ARmcf B ly S Hp (aview im_segs (w_H W) mem) := proj1 HAR.
Let L : ALedger_cf im_segs ly S md := proj1 (proj2 HAR).
Let LY : layout_ok ly := amc_layout _ _ _ _ _ M.

(* An area of the model off the image is present (AGif5.ar_range_present over ARmcf's areas). *)
Lemma ar_area_present_cf : forall e len a, In (e, len) (aareas S) -> aeval B ly e <= a < aeval B ly e + len ->
  0 <= a < 2 ^ 64 -> ~ in_zr a (ly_img ly) -> apresent (w_H W) mem a.
Proof.
intros e len a Hin Ha Hr Hi.
pose proof (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M) _ Hin) as RV.
specialize (RV (a - aeval B ly e) ltac:(cbn [snd]; zl)). cbn [fst] in RV.
replace (aeval B ly e + (a - aeval B ly e)) with a in RV by zl.
eapply aview_present_cf; [exact L | exact Hr | exact Hi | exact RV].
Qed.

(* The thread object is present (it is an area). *)
Lemma ar_T_present_cf : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> apresent (w_H W) mem a.
Proof.
intros a Ha.
assert (HT : In (ly_T ly, kThreadObjSize) (owned_extents ly)) by (unfold owned_extents; cbn; tauto).
apply (ar_area_present_cf (AT 0) kThreadObjSize a).
- unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
- cbn [aeval]. zl.
- exact (owned_range ly _ a LY HT ltac:(unfold in_zr; cbn [fst snd]; zl)).
- exact (owned_not_img ly _ a LY HT ltac:(unfold in_zr; cbn [fst snd]; zl)).
Qed.

(* The committed pointer array is present. *)
Lemma ar_Q_present_cf : forall a, ly_Q ly <= a < ly_Q ly + 8 * st_sec_reserved S -> apresent (w_H W) mem a.
Proof.
intros a Ha.
pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as WR.
assert (HQ : In (ly_Q ly, kPtrArrayResv) (owned_extents ly)) by (unfold owned_extents; cbn; tauto).
apply (ar_area_present_cf (AQ 0) (8 * st_sec_reserved S) a).
- unfold aareas. rewrite !in_app_iff. right; left. left; reflexivity.
- cbn [aeval]. zl.
- apply (owned_range ly _ a LY HQ). unfold in_zr, kPtrArrayResv, kPtrArrayEntriesPerCommit in *; cbn [fst snd]; zl.
- apply (owned_not_img ly _ a LY HQ). unfold in_zr, kPtrArrayResv, kPtrArrayEntriesPerCommit in *; cbn [fst snd]; zl.
Qed.

(* A cell of the model holds as a val_mem (AGif5.ar_cell_state). *)
Lemma ar_cell_cf : forall c, In c (acells_cf B ly S) -> cell_holds B ly (aview im_segs (w_H W) mem) c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) c Hc). Qed.
Lemma ar_sec_in_cf : forall c, In c (sec_cells S) -> In c (acells_cf B ly S).
Proof. intros c Hc. unfold acells_cf. do 3 (apply in_or_app; right). apply in_or_app. left. exact Hc. Qed.
End m.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (a) The view (AGif2.sview) of an ARXq_cf pre-state.                                                              *)
Lemma view_cf : forall Hp inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md ->
  sview B W ly inst mem (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S).
Proof.
intros Hp inst ly S W mem md H.
pose proof (IOK_inst inst (ARXq_cf_iok B IOK Hp inst ly S W mem md H)) as ->.
pose proof (ARXq_cf_ARcf B IOK Hp _ ly S W mem md H) as HAR.
destruct HAR as (M & L & _ & _ & _).
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as WR.
pose proof (wsc_reserved_al _ (wfc_secondary _ _ _ _ _ WF)) as [_ WA].
pose proof (amc_tsd _ _ _ _ _ M) as TSD.
destruct (INST_CELLS ly (w_H W) mem LY TSD (amc_const _ _ _ _ _ M)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
pose proof (ARXq_cf_ARcf B IOK Hp _ ly S W mem md H) as HAR.
assert (VRES : val_mem im_segs (mrestrict (w_H W) mem) (aeval B ly (AInst o_sec_reserved)) 8 (aeval B ly (ANum (st_sec_reserved S)))).
{ apply cell_holds_val_mem. apply (ar_cell_cf Hp ly S W mem md HAR). apply (ar_sec_in_cf ly S). unfold sec_cells. left. reflexivity. }
assert (VN : val_mem im_segs (mrestrict (w_H W) mem) (aeval B ly (AInst o_sec_n)) 8 (aeval B ly (ANum (Z.of_nat (length (st_sec_arr S)))))).
{ apply cell_holds_val_mem. apply (ar_cell_cf Hp ly S W mem md HAR). apply (ar_sec_in_cf ly S). unfold sec_cells. right; left. reflexivity. }
assert (VMTX : val_mem im_segs (mrestrict (w_H W) mem) (aeval B ly (AInst o_sec_mutex)) 1 (aeval B ly (ANum 0))).
{ apply cell_holds_val_mem. apply (ar_cell_cf Hp ly S W mem md HAR). apply (ar_sec_in_cf ly S). unfold sec_cells. right; right; left. reflexivity. }
assert (VUNW : val_mem im_segs (mrestrict (w_H W) mem) (aeval B ly (AT t_unwinding)) 1 (aeval B ly (ANum 0))).
{ apply cell_holds_val_mem. apply (ar_cell_cf Hp ly S W mem md HAR). unfold acells_cf. do 8 (apply in_or_app; right).
  unfold thread_cells. left. reflexivity. }
cbn [aeval] in VRES, VN, VMTX, VUNW.
constructor.
- exact LY.
- exact (IMGC ly S md L).
- rewrite TSD. exact SYM_TSD.
- exact (amc_const _ _ _ _ _ M).
- exact C1.
- exact C2.
- exact C3.
- exact C4.
- exact C5.
- exact C6.
- exact C7.
- exact VRES.
- exact VN.
- intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | exfalso; zl].
  + rewrite (VMTX 0%nat ltac:(zl)). reflexivity.
  + replace (as_inst B + o_sec_mutex + Z.of_nat 1) with (as_inst B + o_sec_mutex + 1 + Z.of_nat 0) by zl.
    rewrite (C8 0%nat ltac:(zl)). reflexivity.
  + replace (as_inst B + o_sec_mutex + Z.of_nat 2) with (as_inst B + o_sec_mutex + 1 + Z.of_nat 1) by zl.
    rewrite (C8 1%nat ltac:(zl)). reflexivity.
  + replace (as_inst B + o_sec_mutex + Z.of_nat 3) with (as_inst B + o_sec_mutex + 1 + Z.of_nat 2) by zl.
    rewrite (C8 2%nat ltac:(zl)). reflexivity.
- exact VUNW.
- intros a Ha. apply (ar_T_present_cf Hp ly S W mem md HAR). unfold t_cache_stats, t_unwinding, kThreadObjSize in *. zl.
- intros a Ha.
  assert (RV : range_vis B ly (aview im_segs (w_H W) mem) (AInst o_sec_stats, o_sec_mutex - o_sec_stats)).
  { apply (proj1 (Forall_forall _ _) (amc_junk _ _ _ _ _ M)). unfold ajunk_cf. right; right.
    do 3 (apply in_or_app; right). apply in_or_app; left. unfold sec_junk. right; left; reflexivity. }
  specialize (RV (a - (as_inst B + o_sec_stats)) ltac:(cbn [snd]; zl)). cbn [fst aeval] in RV.
  replace (as_inst B + o_sec_stats + (a - (as_inst B + o_sec_stats))) with a in RV by zl. exact RV.
- intros a Ha. exact (COMB_VIS (w_H W) mem a Ha).
- intros a Ha. exact (ar_Q_present_cf Hp ly S W mem md HAR a Ha).
- unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *. zl.
- split; [unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *; zl | exact WA].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* freshness of the new secondary slot (YFib.KS_fresh over Wf_cf's chunk_ok_cf).                                  *)
Lemma fresh_cf : forall Hp inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md ->
  forall k', In k' (st_chunks S) -> sptr_eqb (ck_beg k') (PSec (length (st_secs S)) kPage) = false.
Proof.
intros Hp inst ly S W mem md H k' Hk'.
destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (M & _).
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ (amc_wf _ _ _ _ _ M)) k' Hk') as [_ CK].
destruct (ck_beg k') as [|o|r o|c p]; cbn; try reflexivity.
destruct CK as (_ & _ & sm & Hn & _).
assert (LT : (r < length (st_secs S))%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
destruct (Nat.eqb_spec r (length (st_secs S))); [exfalso; zl | reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (c) the kernel fields.                                                                                           *)
Lemma mwf_cf : forall Hp inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md -> amwf md.
Proof. intros Hp inst ly S W mem md H. destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (_ & _ & _ & MW & _). exact MW. Qed.

(* The room fields' raw allowance: AIfaceS.ifs_room and AIfaceSw.ifs_room_w read the world's raw A_bytes.  At the
   interim ledger (Main's hold) ARcf's abudget_ok_cf bounds exactly that, so it is derived here; when the canonical
   ledger_cf (A_bytes - sec_dead_hulls_cf + RESMAX_k <= abudget_cf) returns, this lemma is the one place to change:
   the world keeps every dead secondary's hull, so the raw A_bytes can then exceed abudget_cf (the raw-A gap). *)
Lemma room_raw_A_of_ARXq : forall Hp inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md ->
  A_bytes (w_A W) <= abudget_cf S.
Proof.
intros Hp inst ly S W mem md H. destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (_ & _ & [AB _] & _ & _). exact AB.
Qed.

(* The room below the vm limit, at any head R <= CF_HEAD (AGif5.room_AR's twin): the room of record
   (YGcfRoomCf.room_live_canon_cf: eager_used by the ledger's alc_eager_x, the allowance by abudget_cf, the live terms
   by YG08cf's bounds wherever the quarantine is loose and the hull admission holds; qtight gives qloose, rpre_cf's
   last conjunct gives cf_hull_ok), at the raw allowance room_raw_A_of_ARXq. *)
Lemma room_gen_cf : forall R Hp inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md -> cf_hull_ok S -> R <= CF_HEAD ->
  eager_used md + A_bytes (w_A W) + R <= vm_limit (m_vmmaps md).
Proof.
intros R Hp inst ly S W mem md H HO HR.
destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (M & L & _).
exact (room_live_canon_cf (as_universe B) im_segs ly S md (A_bytes (w_A W)) R (amc_wf _ _ _ _ _ M)
  (qtight_qloose S (ARXq_cf_qtight B IOK Hp inst ly S W mem md H)) HO L
  (Z.le_trans _ _ _ (room_raw_A_of_ARXq Hp inst ly S W mem md H) (abudget_le_kit_cf (as_universe B) S (amc_wf _ _ _ _ _ M))) HR).
Qed.

Lemma room_cf : forall Hp inst ly S W mem md n, ARXq_cf B IOK Hp inst ly S W mem md -> rpre_cf B S n ->
  eager_used md + A_bytes (w_A W) + 2 ^ 30 <= vm_limit (m_vmmaps md).
Proof.
intros Hp inst ly S W mem md n H (_ & _ & _ & HO). apply (room_gen_cf (2 ^ 30) Hp inst ly S W mem md H HO).
apply Z.leb_le. vm_compute. reflexivity.
Qed.

Lemma ledger_fld_cf : forall Hp inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md ->
  vm_reserved (m_vmmaps md) = segments_reserved im_segs /\
  (forall sg, In sg im_segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) /\
  In (wiv (ly_Q ly, kPtrArrayResv)) (vm_maps (m_vmmaps md)) /\
  YM05.ceil_of_top (alloc_top (m_vmmaps md)).
Proof.
intros Hp inst ly S W mem md H. destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LY.
split; [exact (alc_reserved _ _ _ _ L)|].
split; [intros sg Hsg; eapply al_img_env_cf; [exact LY | exact L | exact Hsg]|].
split; [exact (alc_Q _ _ _ _ L) | exact (alc_top _ _ _ _ L)].
Qed.

(* The model the kernel node asks, with the walk's materialized pages: its ledger and wf are ARcf's. *)
Lemma ledger_wvb_cf : forall ly S md mat, ALedger_cf im_segs ly S md ->
  ALedger_cf im_segs ly S (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S md mat L. eapply ALedger_same_cf; [exact L | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
Qed.

(* SecGrantW's per-state facts at ARXq_cf (its HAX, SecGrantW.v:70-73), with xs := the errbuf slot xs_cf. *)
Lemma hax_cf : forall Hp inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md ->
  layout_ok ly /\ SecGrantP.sec_chunks_ok cf_malloc_max S /\
  SecGrantP.ledger_cover im_segs ly md (sec_extents ly S ++ xs_cf ly S) /\ amwf md /\
  Z.of_nat (length (st_sec_arr S)) + Z.of_nat (length (xs_cf ly S)) <= cf_place_limit /\
  Forall (fun e => 0 <= snd e <= cf_nob) (xs_cf ly S).
Proof.
intros Hp inst ly S W mem md H. destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (M & L & _ & MW & _).
pose proof (amc_wf _ _ _ _ _ M) as WF.
split; [exact (amc_layout _ _ _ _ _ M)|].
split.
{ split; [exact (wfc_chunks_nodup _ _ _ _ _ WF)|]. split.
  - eapply Forall_impl; [|exact (wfc_chunks _ _ _ _ _ WF)]. intros k Hk. unfold chunk_ok_cf in Hk. destruct Hk as [Hr Hb].
    split; [exact Hr|]. intros r o E. rewrite E in Hb. destruct Hb as (_ & Ho & _). exact Ho.
  - intros k r Hk E. apply (proj2 (wsc_arr_chunks _ (wfc_secondary _ _ _ _ _ WF) r)). exists k. split; [exact Hk | exact E]. }
split.
{ split; [exact (alc_img _ _ _ _ L)|]. split; [exact (alc_reserved _ _ _ _ L)|]. split; [exact (alc_top _ _ _ _ L)|].
  intros e He. pose proof (alc_cover _ _ _ _ L e He) as X. unfold errb_zone in X. exact X. }
split; [exact MW|].
split.
{ pose proof (wfc_sec_live _ _ _ _ _ WF). pose proof (xs_cf_length ly S). pose proof cf_sec_live_place_lt. zl. }
unfold xs_cf. destruct (last_cap_idx (st_secs S) 0 None); [|constructor].
constructor; [|constructor]. cbn [snd]. exact (errb_cap_bound_cf _ 0 0 0 S WF).
Qed.

(* A grant of the block's size exists, up to cf_nob (SecGrantW.ifs_grant_w_cf). *)
Lemma grant_w_cf : forall Hp, AGif4.ifs_grant_w (ARXq_cf B IOK Hp) cf_nob.
Proof. intros Hp. exact (SecGrantW.ifs_grant_w_cf (ARXq_cf B IOK Hp) (fun ly S => xs_cf ly S) (hax_cf Hp)). Qed.

(* Every grant of up to 2 ^ 40 bytes is in the image's grant zones, apart from what the allocator owns, with a zero
   shadow (AGif5.apart_AR's twin; YFia.grant_zone / grant_apart / grant_shadow_zero over ALedger_cf). *)
Lemma apart_gen_cf : forall Hp inst ly S W mem md mat sz (a : word), ARXq_cf B IOK Hp inst ly S W mem md ->
  0 < sz < 2 ^ 40 -> sz mod 4096 = 0 ->
  grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true ->
  ims_zone3 (bv_unsigned a) sz /\
  Forall (zdisjoint (bv_unsigned a, sz)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) /\
  (forall g, g mod 8 = 0 -> bv_unsigned a <= g -> g + 8 <= bv_unsigned a + sz ->
     mem (Z_to_bv 64 (shadow_addr g)) = Some (Z_to_bv 8 0)).
Proof.
intros Hp inst ly S W mem md mat sz a H Hsz Hal HG.
destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (M & L & _ & _ & [_ HZ]).
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_placed _ _ _ _ _ M) as PL.
pose proof (ledger_wvb_cf ly S md mat L) as LN.
pose proof (gf_facts im_segs _ ly S _ a sz LY WF PL LN Hsz Hal HG) as (_ & APP & _).
split; [exact (ZONE3 ly (bv_unsigned a) sz (IMGC ly S md L) ltac:(zl) APP (gf_img im_segs _ ly S _ a sz LY WF PL LN Hsz Hal HG))|].
split; [exact (gf_apart im_segs _ ly S _ a sz LY WF PL LN Hsz Hal HG)|].
intros g Hg G1 G2. exact (gf_shadow_zero im_segs _ ly S _ a sz LY WF PL LN Hsz Hal HG mem g HZ Hg G1 G2).
Qed.

(* (d) the out-of-memory byte is the allocator's (AGif5.ar_oom_owned). *)
Lemma oom_cf : forall Hp inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md -> AOX_cf B ly S im_oom.
Proof.
intros Hp inst ly S W mem md H. destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (M & _).
left. rewrite <- SYM_OOM.
apply (own_area_cf B ly S Hp (aview im_segs (w_H W) mem) (as_oom_byte B, 1) (as_oom_byte B) M); [unfold asyms_areas; cbn; tauto | cbn [fst snd]; zl].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The depot callee at a later world (ifs_depot): AGif5.depot_S's script with the world free, over the released     *)
(* depot contract at Wf_cf (YGcfInstDepot.depot_spec_d_of_x).                                                       *)
Lemma depot_cf : forall Hp inst ly S W mem0 md0 tr (Wy : world im_segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (buf : Z),
  ARXq_cf B IOK Hp inst ly S W mem0 md0 -> U_cf B tr S ->
  (forall x : word, w_H W x = false -> w_H Wy x = false) ->
  (forall x : word, ims_dzone ly (bv_unsigned x) \/ CZS ly inst (bv_unsigned x) -> mem x = mem0 x) ->
  (forall k, 1 <= k < 4 -> aview im_segs (w_H Wy) mem (inst + o_sec_mutex + k) = Some 0) ->
  getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
  getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
  (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H Wy) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
  buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
  buf + 8 * 30 <= bv_unsigned (getr regs 2) - ImgBaseAGS.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
  bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - ImgBaseAGS.DEP_STK ->
  bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
  (forall a, bv_unsigned (getr regs 2) - ImgBaseAGS.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H Wy) mem a) ->
  SRr im_segs Wy (mkCfg (mkst regs (Z_to_bv 64 ims_depot) mem (seg_rom im_segs)) md)
  (fun W' c' => W' = Wy /\ exists z regs' mem' mat,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    regs_preserved regs regs' /\
    (forall x : word, ~ (bv_unsigned (getr regs 2) - ImgBaseAGS.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
       ~ ims_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
    (forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
    dpost_cf B inst ly S W tr z mem').
Proof.
intros Hp inst ly S W mem0 md0 tr Wy regs mem md buf HX HU MONy MEQ PAD R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
pose proof (IOK_inst inst (ARXq_cf_iok B IOK Hp inst ly S W mem0 md0 HX)) as EI. subst inst.
pose proof (ARXq_cf_ARcf B IOK Hp _ ly S W mem0 md0 HX) as HAR.
destruct HAR as (M & L & _ & _ & _).
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (IMGC ly S md0 L) as IMG. pose proof (amc_tsd _ _ _ _ _ M) as TSD.
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (wfc_depot _ _ _ _ _ WF) as DF.
pose proof (ARXq_cf_ARcf B IOK Hp _ ly S W mem0 md0 HX) as HAR.
assert (RX : forall m, rd_ext (aview im_segs (w_H W) m) (aview im_segs (w_H Wy) m)).
{ intros m. apply aview_ext; [apply w_Hoff|]. intros x Hx. destruct (w_H W x) eqn:E; [reflexivity|].
  rewrite (MONy x E) in Hx. discriminate Hx. }
assert (IDS0 : depot_ids S <= 4097).
{ pose proof (depot_len_bound _ _ (amc_universe _ _ _ _ _ M) DF). unfold depot_ids, DEPOT_MAX in *. zl. }
(* the footprint's bytes are machine addresses, and the world never hides them *)
assert (FPR : forall a, CLdepot.depot_footprint B ly a -> 0 <= a < 2 ^ 64).
{ pose proof (aso_cells _ (amc_syms _ _ _ _ _ M)) as AC.
  pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as [N1 N2].
  pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as [S1 S2].
  cbn [fst snd] in N1, N2, S1, S2. ceil.
  intros a Ha. unfold CLdepot.depot_footprint, d_map1, kLowMemEnd, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zl. }
assert (FPU : forall a, CLdepot.depot_footprint B ly a -> w_H W (Z_to_bv 64 a) = false).
{ intros a Ha. pose proof (FPR a Ha) as Ra. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - exact (DEP_UNHID W a (or_introl Ha)).
  - assert (HN : In (ly_NB ly, kNodesBlockSize) (owned_extents ly)) by (unfold owned_extents; cbn; tauto).
    refine (proj1 (ar_area_present_cf Hp ly S W mem0 md0 HAR (ANB 0) kNodesBlockSize a _ _ Ra _)).
    + unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
    + cbn [aeval]. zl.
    + exact (owned_not_img ly _ a LY HN ltac:(unfold in_zr; cbn [fst snd]; zl)).
  - assert (HS : In (ly_SB ly, kStoreBlockSize) (owned_extents ly)) by (unfold owned_extents; cbn; tauto).
    refine (proj1 (ar_area_present_cf Hp ly S W mem0 md0 HAR (ASB 0) kStoreBlockSize a _ _ Ra _)).
    + unfold aareas. rewrite !in_app_iff. right; right; right. cbn [In]. tauto.
    + cbn [aeval]. zl.
    + exact (owned_not_img ly _ a LY HS ltac:(unfold in_zr; cbn [fst snd]; zl)).
  - exact (DEP_UNHID W a (or_intror Ha)). }
(* the call memory at Wy: the constant cells (the unit's keep fact) and the depot facts (kept on the footprint) *)
assert (CST0 : Forall (cell_holds B ly (aview im_segs (w_H Wy) mem0)) (as_const B ly))
  by exact (Forall_cell_holds_ext B ly _ _ _ (RX mem0) (amc_const _ _ _ _ _ M)).
assert (CST1 : Forall (cell_holds B ly (aview im_segs (w_H Wy) mem)) (as_const B ly))
  by exact (CONST_KEEP_S ly (w_H Wy) mem0 mem LY IMG TSD CST0 MEQ PAD).
assert (DEP1 : CLdepot.depot_mem_ok B ly S (aview im_segs (w_H Wy) mem)).
{ apply (dmo_agree_fp B ly S (aview im_segs (w_H Wy) mem0)); [zl | |].
  - intros a Ha. apply aview_same_g. apply MEQ. left. rewrite w64_unsigned by exact (FPR a Ha).
    exact (DEP_FP ly a LY IMG TSD Ha).
  - apply (dmo_rdext B ly S _ _ (RX mem0)). exact (YGcfInstDepot.depot_at0_cf B ly S Hp _ M). }
eapply SRr_mono.
{ exact (YGcfInstDepot.depot_spec_d_of_x im_segs ims_depot im_tp im_img_cover B HD Wy ly S regs mem md buf tr LY IMG
    DF HU CST1 DEP1 R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES). }
intros W' c' _ (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [reflexivity|]. split; [exact RP|].
split.
{ intros x N1 N2. apply FR; [exact N1|]. intros FPx. apply N2. exact (DEP_FP ly (bv_unsigned x) LY IMG TSD FPx). }
split; [exact PR'|].
unfold dpost_cf, CLdepot.dpost_x. split; [exact AOK|]. split.
- apply (dmo_agree_fp B ly _ (aview im_segs (w_H Wy) mem')); [| | exact DEP'].
  + unfold CLdepot.depot_after. destruct (z =? 0); [zl|]. unfold depot_ids in *. cbn [st_depot set_depot].
    rewrite length_app. cbn [length]. zl.
  + intros a Ha. pose proof (FPU a Ha) as Hf. unfold aview, mbyte, mrestrict. rewrite Hf, (MONy _ Hf). reflexivity.
- apply Forall_forall. intros c Hc.
  apply (cell_holds_agree2_g B ly (aview im_segs (w_H Wy) mem') (aview im_segs (w_H W) mem0));
    [| exact (proj1 (Forall_forall _ _) CST' c Hc) | exact (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M) c Hc)].
  intros k Hk. unfold aview, mbyte, mrestrict.
  destruct (w_H W (Z_to_bv 64 (aeval B ly (c_at c) + k))) eqn:E; [right; reflexivity | left; rewrite (MONy _ E); reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (d) The refusal arm (AGif5.post_null_S's twin): ARcf after the arm's writes (the twin of AGic.AR_snull, over the  *)
(*     image-free junk set below), then the tick (ARcf_tick_sec).                                                     *)

(* The tick keeps ARcf: nothing in it reads the event counter except Wf_cf's event lower bounds, which the tick keeps
   (WfP_cf_tick; the layer's YGcfInstRefill.ARcf_tick_cf at ad082add249, which d50ec3c8a93 removed). *)
Lemma ARcf_tick_sec : forall Hp ly S W mem md,
  ARcf im_segs B ly S Hp W mem md -> ARcf im_segs B ly (set_nev (st_nev S + 1) S) Hp W mem md.
Proof.
intros Hp ly S W mem md (M & L & BUD & MW & HS).
split; [|split; [|split; [| split; [exact MW | exact HS]]]].
- pose proof (amc_wf _ _ _ _ _ M) as WM.
  (* the two cells read no event count, so the tick's state gives them by conversion (try assumption) *)
  destruct M. constructor; try assumption. exact (YG02cf.WfP_cf_tick _ _ _ _ _ WM).
- destruct L. constructor; assumption.
- (* the budget reads cf_hull, which the tick leaves alone (cf_hull_frame: same st_secs, same live hulls) *)
  destruct BUD as [A1 A2]. split; [|exact A2].
  assert (EH : cf_hull (set_nev (st_nev S + 1) S) = cf_hull S) by (apply cf_hull_frame; reflexivity).
  unfold abudget_cf in *. rewrite EH. exact A1.
Qed.

(* The bytes the refusal arm writes with values no model cell pins: the thread's stats windows, the instance's sorted
   byte, its stats words and by_size_log word, the combined stats and the out-of-memory byte.  Its other writes (the
   two secondary counters, the mutex and the unwinding flag) store the values the model's cells already hold. *)
Definition snull_junk (ly : alayout) (regs0 : bvmap 5 word) (n a : Z) : Prop :=
  (ly_T ly + 2768 <= a < ly_T ly + 2824) \/ (ly_T ly + 2872 <= a < ly_T ly + 2888) \/ (ly_T ly + 2904 <= a < ly_T ly + 2912) \/
  (as_inst B + o_sec_sorted <= a < as_inst B + o_sec_sorted + 1) \/ (as_inst B + o_sec_stats <= a < as_inst B + o_sec_stats + 32) \/
  (ImgBaseAGS.BSLv regs0 n <= a < ImgBaseAGS.BSLv regs0 n + 8) \/
  (as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40) \/ a = as_oom_byte B.

(* The unit's side, for the refusal arm and the errno add-ons. *)
(* No constant cell lies in the junk set [cgif: AGic.v's keep of Tfib_const, from its addresses]. *)
Hypothesis CONST_NOT_JUNK : forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < cf_malloc_max ->
  In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ snull_junk ly regs0 n (aeval B ly (c_at c) + k).
(* The symbol table's first six areas (instance object, depot, store, internal allocator, its flag, out-of-memory byte)
   are pairwise apart [cgif: TfibSyms' addresses; the later areas are not pinned by TfibSyms and are not needed]. *)
Hypothesis AREAS_DISJ : pairwise zdisjoint (firstn 6 (asyms_areas B)).
(* errno at the image classes and its bytes [cgif: ts_errno, YB13.tfib_segs_eq, Tfib_owned_static, rw_view]. *)
Hypothesis SYM_ERRNO : as_errno B = im_errno.
Hypothesis TS : im_syms B.
Hypothesis EIMG : ErrnoApart.errno_in_img.
Hypothesis ERR_SEG : YGcfInstErrno.errno_seg_t B.
Hypothesis ERR_NST : YGcfInstErrno.errno_nstatic_t B.
Hypothesis ERRNO_VIS : forall (H : word -> bool) (mem : word -> option byte) a, as_errno B <= a < as_errno B + 4 ->
  aview im_segs H mem a <> None.
(* The walk's frame at Allocate's entry puts its stack window inside the stack [cgif: AGif0cgif.wframe's Hsp]. *)
Hypothesis WFRAME_SP : forall W ly regs0 mem0 tr, ims_wframe W ly regs0 mem0 tr ->
  ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) <= ly_stk_hi ly.
(* The two machine cells ARmcf carries (amc_exh_cell / amc_errb_cells) are owned through ARmcf's amc_cells_owned
   (YGcfImgRows.EXH_OFF_t and errb_obj_owned_t); the errbuf object's place is YGcfErrbSep.ERRB_SEP_t, read through
   ERRB_SEP_at at the symbol table TS. *)
Hypothesis ERRB_SEP : ERRB_SEP_t B.
Hypothesis PF_SEP : PF_SEP_t B.

Section n.
Variables (Hp : list Z) (ly : alayout) (S : astate) (W : world im_segs) (mem0 mem' : word -> option byte) (md0 : Model).
Variables (regs0 : bvmap 5 word) (n : Z).
Hypothesis HAR : ARcf im_segs B ly S Hp W mem0 md0.
Hypothesis Hinst : bv_unsigned (getr regs0 11) = as_inst B.
Hypothesis HSP : ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) <= ly_stk_hi ly.
Hypothesis Hn : 64513 <= n < cf_malloc_max.
Hypothesis MEQ : forall x : word, ~ ImgBaseAGS.WINP ly regs0 n (bv_unsigned x) -> bv_unsigned x <> im_oom ->
  ~ (im_errno <= bv_unsigned x < im_errno + 4) -> mem' x = mem0 x.
Hypothesis PRS : forall a, bv_unsigned (getr regs0 2) - ImgBaseAGS.AFSTACK <= a < bv_unsigned (getr regs0 2) ->
  apresent (w_H W) mem' a.
Hypothesis PRW : forall a, ImgBaseAGS.WINT ly a -> apresent (w_H W) mem' a.
Hypothesis VISI : forall a, ImgBaseAGS.WINI regs0 n a -> aview im_segs (w_H W) mem' a <> None.
Hypothesis VOOM : val_mem im_segs (mrestrict (w_H W) mem') im_oom 1 1.
Hypothesis VUNW : val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0.
Hypothesis VRES : val_mem im_segs (mrestrict (w_H W) mem') (as_inst B + o_sec_reserved) 8 (st_sec_reserved S).
Hypothesis VNCH : val_mem im_segs (mrestrict (w_H W) mem') (as_inst B + o_sec_n) 8 (Z.of_nat (length (st_sec_arr S))).
Hypothesis VMTX : val_mem im_segs (mrestrict (w_H W) mem') (as_inst B + o_sec_mutex) 4 0.
Let M : ARmcf B ly S Hp (aview im_segs (w_H W) mem0) := proj1 HAR.
Let L : ALedger_cf im_segs ly S md0 := proj1 (proj2 HAR).
Let LY : layout_ok ly := amc_layout _ _ _ _ _ M.
Local Notation rd0 := (aview im_segs (w_H W) mem0).
Local Notation rd' := (aview im_segs (w_H W) mem').
Local Notation NJ a := (~ snull_junk ly regs0 n a).

(* Where things are: the symbol areas in the image window, the thread object outside it. *)
Lemma sn_area_img : forall r a, In r (asyms_areas B) -> in_zr a r -> in_zr a (ly_img ly).
Proof.
intros r a Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amc_syms _ _ _ _ _ M)) r Hr) as X.
apply Exists_exists in X as (r' & Hr' & [Z1 Z2]).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r' ltac:(apply in_app_iff; left; exact Hr')) as [I1 I2].
unfold in_zr in *. zl.
Qed.
Lemma sn_inst_img : forall a, as_inst B <= a < as_inst B + 3632 -> in_zr a (ly_img ly).
Proof. intros a Ha. apply (sn_area_img (as_inst B, 3632)); [unfold asyms_areas; cbn; tauto | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_oom_img : in_zr (as_oom_byte B) (ly_img ly).
Proof. apply (sn_area_img (as_oom_byte B, 1)); [unfold asyms_areas; cbn; tauto | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_T_img : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> ~ in_zr a (ly_img ly).
Proof. intros a Ha. apply (owned_not_img ly (ly_T ly, kThreadObjSize) a LY); [unfold owned_extents; cbn; tauto | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_bsl : as_inst B + 296 <= ImgBaseAGS.BSLv regs0 n /\ ImgBaseAGS.BSLv regs0 n + 8 <= as_inst B + 416.
Proof. rewrite <- Hinst. apply bsl_bounds. pose proof cf_malloc_max_bound. zl. Qed.
Lemma sn_oom_inst : ~ (as_inst B <= as_oom_byte B < as_inst B + 3632).
Proof.
intros X. pose proof (pw_ij zdisjoint (firstn 6 (asyms_areas B)) 0 4 (as_inst B, 3632) (as_oom_byte B, 1) AREAS_DISJ eq_refl eq_refl) as D.
unfold zdisjoint in D. cbn [fst snd] in D. zl.
Qed.
Lemma sn_junk_loc : forall a, snull_junk ly regs0 n a ->
  (ly_T ly + 2768 <= a < ly_T ly + 2912) \/ (as_inst B + 128 <= a < as_inst B + 728) \/ a = as_oom_byte B.
Proof. intros a Ha. pose proof sn_bsl as Bs. unfold snull_junk, o_sec_sorted, o_sec_stats, o_comb_stats in *. zl. Qed.

(* Outside the thread object and the image window nothing is junk. *)
Lemma sn_out : forall a, ~ (ly_T ly <= a < ly_T ly + kThreadObjSize) -> ~ in_zr a (ly_img ly) -> NJ a.
Proof.
intros a N1 N2 X. destruct (sn_junk_loc a X) as [Y|[Y|Y]].
- apply N1. unfold kThreadObjSize. zl.
- apply N2. apply sn_inst_img. zl.
- apply N2. subst a. exact sn_oom_img.
Qed.
(* An extent apart from the thread object and the image window. *)
Lemma sn_ext : forall e a, zdisjoint e (ly_T ly, kThreadObjSize) -> zdisjoint e (ly_img ly) -> in_zr a e -> NJ a.
Proof. intros e a D1 D2 Ha. apply sn_out; unfold zdisjoint, in_zr in *; cbn [fst snd] in *; zl. Qed.
Lemma sn_static : forall i j e, (i < j)%nat -> nth_error (static_extents ly) i = Some e ->
  forall e', nth_error (static_extents ly) j = Some e' -> zdisjoint e e'.
Proof.
intros i j e Hij He e' He'. apply (pw_ij zdisjoint (static_extents ly) i (j - i - 1) e e' (lo_disj ly LY) He).
replace (i + Datatypes.S (j - i - 1))%nat with j by zl. exact He'.
Qed.
Lemma zdj_sym : forall e e', zdisjoint e e' -> zdisjoint e' e.
Proof. intros e e' D. unfold zdisjoint in *. zl. Qed.
Local Ltac sdisj i j := first [ exact (sn_static i j _ ltac:(zl) eq_refl _ eq_refl)
  | apply zdj_sym; exact (sn_static i j _ ltac:(zl) eq_refl _ eq_refl) ].
Lemma sn_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> NJ a.
Proof. intros a Ha. apply (sn_ext (ly_prim ly, kPrimResvSize)); [sdisj 0%nat 2%nat | sdisj 0%nat 9%nat | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_Q : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> NJ a.
Proof. intros a Ha. apply (sn_ext (ly_Q ly, kPtrArrayResv)); [sdisj 1%nat 2%nat | sdisj 1%nat 9%nat | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_F : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> NJ a.
Proof. intros a Ha. apply (sn_ext (ly_F ly, kFakeStackSize)); [sdisj 2%nat 3%nat | sdisj 3%nat 9%nat | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> NJ a.
Proof. intros a Ha. apply (sn_ext (ly_NB ly, kNodesBlockSize)); [sdisj 2%nat 4%nat | sdisj 4%nat 9%nat | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_sec : forall e a, In e (sec_extents ly S) -> in_zr a e -> NJ a.
Proof.
intros e a He Ha. pose proof (proj2 (amc_placed _ _ _ _ _ M)) as PD.
apply (sn_ext e).
- exact (cfb_pairwise_app zdisjoint (sec_extents ly S) (static_extents ly) e (ly_T ly, kThreadObjSize) PD He
    ltac:(unfold static_extents, owned_extents; cbn; tauto)).
- exact (cfb_pairwise_app zdisjoint (sec_extents ly S) (static_extents ly) e (ly_img ly) PD He
    ltac:(unfold static_extents; apply in_or_app; right; cbn; tauto)).
- exact Ha.
Qed.
Lemma sn_chunk : forall k a, In k (st_chunks S) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k -> NJ a.
Proof.
intros k a Hk Ha. destruct (extent_zone_cf B ly S Hp _ k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
- apply sn_prim. zl.
- apply (sn_sec (m, len) a Hin). unfold in_zr, kPage in *. cbn [fst snd]. zl.
Qed.
(* The thread object outside its stats windows. *)
Lemma sn_T : forall a, (ly_T ly <= a < ly_T ly + 2768) \/ (ly_T ly + 2912 <= a < ly_T ly + kThreadObjSize) -> NJ a.
Proof.
intros a Ha X. assert (HT : ly_T ly <= a < ly_T ly + kThreadObjSize) by (unfold kThreadObjSize in *; zl).
pose proof (sn_T_img a HT) as NI. destruct (sn_junk_loc a X) as [Y|[Y|Y]].
- unfold kThreadObjSize in *. zl.
- apply NI. apply sn_inst_img. zl.
- apply NI. subst a. exact sn_oom_img.
Qed.
(* The instance object outside its written windows. *)
Lemma sn_inst : forall a, (as_inst B + 112 <= a < as_inst B + 128) \/ (as_inst B + 680 <= a < as_inst B + 688) \/
  (as_inst B + 728 <= a < as_inst B + 3632) -> NJ a.
Proof.
intros a Ha X. pose proof sn_bsl as Bs. pose proof sn_oom_inst as NO.
assert (II : in_zr a (ly_img ly)) by (apply sn_inst_img; zl).
unfold snull_junk in X. destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
1-3: exact (sn_T_img a ltac:(unfold kThreadObjSize; zl) II).
1-4: unfold o_sec_sorted, o_sec_stats, o_comb_stats in *; zl.
subst a. zl.
Qed.
(* The other symbol areas. *)
Lemma sn_area : forall r a, In r (asyms_areas B) -> zdisjoint r (as_inst B, 3632) -> zdisjoint r (as_oom_byte B, 1) ->
  in_zr a r -> NJ a.
Proof.
intros r a Hr D1 D2 Ha X. pose proof (sn_area_img r a Hr Ha) as II.
unfold zdisjoint, in_zr in *. cbn [fst snd] in *.
destruct (sn_junk_loc a X) as [Y|[Y|Y]].
- exact (sn_T_img a ltac:(unfold kThreadObjSize; zl) II).
- zl.
- subst a. zl.
Qed.
Local Ltac adisj i j := first [ exact (pw_ij zdisjoint (firstn 6 (asyms_areas B)) i j _ _ AREAS_DISJ eq_refl eq_refl)
  | apply zdj_sym; exact (pw_ij zdisjoint (firstn 6 (asyms_areas B)) i j _ _ AREAS_DISJ eq_refl eq_refl) ].
Lemma sn_depot : forall a, as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32 -> NJ a.
Proof. intros a Ha. apply (sn_area (as_depot B, 4 * 2 ^ 20 + 32)); [unfold asyms_areas; cbn; tauto | adisj 0%nat 0%nat | adisj 1%nat 3%nat | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_store : forall a, as_store B <= a < as_store B + 32 -> NJ a.
Proof. intros a Ha. apply (sn_area (as_store B, 32)); [unfold asyms_areas; cbn; tauto | adisj 0%nat 1%nat | adisj 2%nat 2%nat | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_ialloc : forall a, as_ialloc_lo B <= a < as_ialloc_hi B -> NJ a.
Proof. intros a Ha. apply (sn_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [unfold asyms_areas; cbn; tauto | adisj 0%nat 2%nat | adisj 3%nat 1%nat | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma sn_iflag : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> NJ a.
Proof. intros a Ha. apply (sn_area (as_ialloc_flag B, 2)); [unfold asyms_areas; cbn; tauto | adisj 0%nat 3%nat | adisj 4%nat 0%nat | unfold in_zr; cbn [fst snd]; zl]. Qed.
(* The shadow band. *)
Lemma sn_shadow : forall a, SHADOW_OFF <= a < kHighMemBeg -> NJ a.
Proof.
intros a Ha. apply sn_out.
- pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as [A1 A2].
  cbn [fst snd] in A1, A2. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. zl.
- pose proof (lo_img ly LY) as (J0 & J1 & J2 & _). unfold in_zr, kImgLo, kImgEnd, SHADOW_OFF in *. zl.
Qed.
Lemma sn_shadow_rng : forall lo len i, 0 <= lo -> 0 <= len -> lo + len <= kHighMemEnd -> 0 <= i < len / 8 ->
  SHADOW_OFF <= shadow_addr lo + i < kHighMemBeg.
Proof.
intros lo len i H0 H1 H2 Hi. unfold shadow_addr.
pose proof (Z.div_mod lo 8 ltac:(zl)) as D1. pose proof (Z.mod_pos_bound lo 8 ltac:(zl)) as M1.
pose proof (Z.div_mod len 8 ltac:(zl)) as D2. pose proof (Z.mod_pos_bound len 8 ltac:(zl)) as M2.
unfold SHADOW_OFF, kHighMemBeg, kHighMemEnd in *. zl.
Qed.

(* The arm's writes agree with the pre-state's bytes on every owned byte outside the junk set (AGic.AGX's twin): the
   stack window and errno are not the allocator's, and the counters, the mutex and the unwinding flag are written
   with the values the model's cells hold. *)
Lemma sn_AGO : forall a, aowned B ly S a -> NJ a -> rd' a = rd0 a.
Proof.
intros a Ho Hj.
pose proof (AR_owned_low_law_ok_cf im_segs B ly S Hp W mem0 md0 a HAR Ho) as Ra. pose proof alloc_ceiling_val as CV.
pose proof sn_bsl as Bs.
destruct (zr_dec (bv_unsigned (getr regs0 2) - ImgBaseAGS.AFSTACK) (bv_unsigned (getr regs0 2)) a) as [Hs|Hs].
{ exfalso. refine (AR_stack_law_ok_cf im_segs B ly S Hp W mem0 md0 a HAR _ Ho). unfold ImgBaseAGS.AFSTACK in *. zl. }
destruct (zr_dec (as_errno B) (as_errno B + 4) a) as [He|He].
{ exfalso. exact (YGcfInstErrno.errno_not_owned_cf B TS EIMG HIMG ERR_SEG ERR_NST ly S Hp W mem0 md0 a HAR He Ho). }
destruct (Z.eq_dec a (ly_T ly + t_unwinding)) as [Eu|Eu].
{ subst a. pose proof (vm_aview_g _ _ _ _ _ _ 0%nat VUNW ltac:(zl)) as X. rewrite Z.add_0_r in X. rewrite X.
  assert (C : cell_holds B ly rd0 (z1 (AT t_unwinding) 0)).
  { apply (ar_cell_cf Hp ly S W mem0 md0 HAR). unfold acells_cf. do 8 (apply in_or_app; right). unfold thread_cells. left. reflexivity. }
  unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C. specialize (C 0%nat ltac:(zl)). rewrite Z.add_0_r in C.
  rewrite C. reflexivity. }
destruct (zr_dec (as_inst B + o_sec_reserved) (as_inst B + o_sec_reserved + 8) a) as [Hr|Hr].
{ set (k := Z.to_nat (a - (as_inst B + o_sec_reserved))).
  assert (Ea : a = as_inst B + o_sec_reserved + Z.of_nat k) by (subst k; rewrite Z2Nat.id by zl; zl).
  assert (Hk : (k < 8)%nat) by (subst k; zl). clearbody k. rewrite Ea. rewrite (vm_aview_g _ _ _ _ _ _ k VRES Hk).
  assert (C : cell_holds B ly rd0 (c8 (AInst o_sec_reserved) (ANum (st_sec_reserved S)))).
  { apply (ar_cell_cf Hp ly S W mem0 md0 HAR). apply (ar_sec_in_cf ly S). unfold sec_cells. left. reflexivity. }
  unfold cell_holds in C. cbn [c_at c_val c_w c8 aeval] in C. rewrite (C k Hk). reflexivity. }
destruct (zr_dec (as_inst B + o_sec_n) (as_inst B + o_sec_n + 8) a) as [Hc|Hc].
{ set (k := Z.to_nat (a - (as_inst B + o_sec_n))).
  assert (Ea : a = as_inst B + o_sec_n + Z.of_nat k) by (subst k; rewrite Z2Nat.id by zl; zl).
  assert (Hk : (k < 8)%nat) by (subst k; zl). clearbody k. rewrite Ea. rewrite (vm_aview_g _ _ _ _ _ _ k VNCH Hk).
  assert (C : cell_holds B ly rd0 (z8 (AInst o_sec_n) (Z.of_nat (length (st_sec_arr S))))).
  { apply (ar_cell_cf Hp ly S W mem0 md0 HAR). apply (ar_sec_in_cf ly S). unfold sec_cells. right; left. reflexivity. }
  unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C. rewrite (C k Hk). reflexivity. }
destruct (zr_dec (as_inst B + o_sec_mutex) (as_inst B + o_sec_mutex + 4) a) as [Hm|Hm].
{ set (k := Z.to_nat (a - (as_inst B + o_sec_mutex))).
  assert (Ea : a = as_inst B + o_sec_mutex + Z.of_nat k) by (subst k; rewrite Z2Nat.id by zl; zl).
  assert (Hk : (k < 4)%nat) by (subst k; zl). clearbody k. rewrite Ea. rewrite (vm_aview_g _ _ _ _ _ _ k VMTX Hk), le_byte_zero.
  destruct k as [|k].
  - assert (C : cell_holds B ly rd0 (z1 (AInst o_sec_mutex) 0)).
    { apply (ar_cell_cf Hp ly S W mem0 md0 HAR). apply (ar_sec_in_cf ly S). unfold sec_cells. right; right; left. reflexivity. }
    unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C. rewrite (C 0%nat ltac:(zl)), le_byte_zero. reflexivity.
  - destruct (INST_CELLS ly (w_H W) mem0 LY (amc_tsd _ _ _ _ _ M) (amc_const _ _ _ _ _ M)) as (_ & _ & _ & _ & _ & _ & _ & C8).
    replace (as_inst B + o_sec_mutex + Z.of_nat (Datatypes.S k)) with (as_inst B + o_sec_mutex + 1 + Z.of_nat k) by zl.
    rewrite (vm_aview_g _ _ _ _ _ _ k C8 ltac:(zl)), le_byte_zero. reflexivity. }
apply aview_same_g. apply MEQ; rewrite w64_unsigned by (unfold alloc_ceiling in *; zl).
- intros [X|[X|X]]; [exact (Hs X) | |].
  + apply Hj. unfold ImgBaseAGS.WINT in X. unfold snull_junk. unfold t_unwinding in *. zl.
  + apply Hj. unfold ImgBaseAGS.WINI in X. rewrite Hinst in X.
    unfold snull_junk, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. zl.
- intros Eo. apply Hj. unfold snull_junk. rewrite SYM_OOM. zl.
- rewrite <- SYM_ERRNO. exact He.
Qed.

(* The cells' locations (AGic.cells_*'s twins): every cell byte of the model outside the junk set. *)
Definition sn_nj (c : acell) : Prop := forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> NJ (aeval B ly (c_at c) + k).
Lemma sn_rng : forall c (Z : Z -> Prop), (forall a, Z a -> NJ a) ->
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> Z (aeval B ly (c_at c) + k)) -> sn_nj c.
Proof. intros c Z HZ HR k Hk. exact (HZ _ (HR k Hk)). Qed.
Local Ltac rng Lm := apply (sn_rng _ _ Lm); intros kk Hkk; cbn [c_at c_w aeval aoff z1 z2 z4 z8 c1 c2 c4 c8 fst snd] in *;
  cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ] in Hkk.

Lemma sn_batches : forall bl, incl bl (all_batches S) -> Forall sn_nj (batch_cells bl).
Proof.
pose proof (amc_wf _ _ _ _ _ M) as WF.
induction bl as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
assert (LOC : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> NJ a).
{ pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; zl)) as CL.
  set (x := b_self b - region_off kBatchClass).
  assert (INB : In x (batch_offs S kBatchClass))
    by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
  pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
  pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
  pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; zl)) as MB.
  pose proof (region_in_prim ly kBatchClass LY ltac:(unfold kBatchClass; zl)) as (R1 & R2 & R3 & R4 & R5).
  assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
  assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; zl).
  apply Z.mod_divide in X2 as [q1 Hq1]; [|zl]. apply Z.mod_divide in AA as [q2 Hq2]; [|zl].
  assert (XA : x + 8192 <= rg_alloc_user (reg S kBatchClass)) by zl.
  intros a Ha. apply sn_prim. unfold kBatchBytes, kFreeArrayOffset in *. zl. }
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ WF)) b (Hincl b (or_introl eq_refl))) as [L1 L2].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split]]].
1-3: rng LOC; unfold batch_exp in *; cbn [aeval aoff] in *; unfold kBatchBytes; zl.
- apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
  rng LOC. unfold batch_exp in *. cbn [aeval aoff] in *. unfold kBatchBytes, kBatchSlots in *. zl.
- apply IH. intros y Hy. apply Hincl. right. exact Hy.
Qed.

Lemma sn_cells_loc : Forall sn_nj (acells_cf B ly S).
Proof.
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (lo_space_in ly LY) as [S1 S2]. pose proof (lo_high ly LY) as [H1 H2].
unfold acells_cf.
apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split;
[|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]]]]]].
- (* regions *)
  apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. eapply incl_Forall; [apply region_cells_cf_incl|].
  unfold region_cells. repeat (apply Forall_cons; [rng sn_prim; unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *; zl|]). apply Forall_nil.
- (* caches *)
  apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
  pose proof (wfc_classes _ _ _ _ _ WF c' ltac:(zl)) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC.
  assert (MC : max_cached c' <= 16) by (unfold max_cached; pose proof (Z.le_min_l 8 (1024 / class_size c')); zl).
  assert (LT : forall a, ly_T ly <= a < ly_T ly + 2768 -> NJ a) by (intros a Ha; apply sn_T; left; exact Ha).
  unfold cache_cells. destruct (st_cache_inited S).
  + destruct WC as [PM PL'].
    repeat (apply Forall_cons; [rng LT; unfold t_cache; zl|]).
    apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i v] & <- & Hiv). apply in_combine_l in Hiv. apply in_seq in Hiv.
    rng LT. unfold t_cache. zl.
  + repeat (apply Forall_cons; [rng LT; unfold t_cache; zl|]). apply Forall_nil.
- (* chunk headers *)
  apply Forall_flat_map'. intros k Hk.
  pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  pose proof (req_size_bounds (ck_req k) ltac:(zl)) as (Q1 & Q2 & Q3).
  assert (LOC : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> NJ a) by (intros a Ha; exact (sn_chunk k a Hk Ha)).
  assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
  { intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; zl. }
  assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
  { intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; zl. }
  assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
  clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
  + repeat (apply Forall_cons; [apply (sn_rng _ _ LOC); intros kk Hkk; cbn [c_at c_w z1 z2 z4 c1 c2 c4] in *;
      rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ] in Hkk; zl|]). apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
    assert (32 <= ck_rz k) by (apply Z.mod_divide in G6 as [q Hq]; [|zl]; zl).
    repeat (apply Forall_cons; [apply (sn_rng _ _ LOC); intros kk Hkk; cbn [c_at c_w z8 c8] in *;
      rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ] in Hkk; zl|]). apply Forall_nil.
- (* the secondary's cells *)
  pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as WR.
  assert (LI : forall a, (as_inst B + 112 <= a < as_inst B + 128) \/ (as_inst B + 680 <= a < as_inst B + 688) \/
    (as_inst B + 728 <= a < as_inst B + 3632) -> NJ a) by exact sn_inst.
  unfold sec_cells.
  apply Forall_cons; [rng LI; unfold o_sec_reserved; zl|]. apply Forall_cons; [rng LI; unfold o_sec_n; zl|].
  apply Forall_cons; [rng LI; unfold o_sec_mutex; zl|].
  apply Forall_app. split.
  + apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
    rng sn_Q. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl.
  + apply Forall_flat_map'. intros k Hk.
    pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
    destruct (ck_beg k) as [|o|r o|c' p'] eqn:Eb; try apply Forall_nil.
    destruct GG as (_ & _ & Gbase & Gext & Gin & _).
    pose proof (sec_map_size_page (ck_req k) ltac:(zl)) as SP.
    assert (LS : forall a, ly_sec ly r <= a < ly_sec ly r + sec_map_size (ck_req k) -> NJ a)
      by (intros a Ha; exact (sn_sec _ a Gin Ha)).
    repeat (apply Forall_cons; [rng LS; unfold kPage in *; zl|]). apply Forall_nil.
- (* the quarantine's cells *)
  assert (LI : forall a, as_inst B + 728 <= a < as_inst B + 3632 -> NJ a) by (intros a Ha; apply sn_inst; zl).
  assert (LT : forall a, ly_T ly <= a < ly_T ly + 2768 -> NJ a) by (intros a Ha; apply sn_T; left; exact Ha).
  unfold quar_cells, qc_cells.
  apply Forall_cons; [rng LI; unfold o_q_cmutex; zl|]. apply Forall_cons; [rng LI; unfold o_q_rmutex; zl|].
  apply Forall_app. split.
  + do 4 (apply Forall_cons; [rng LT; unfold t_qc; zl|]).
    apply sn_batches. intros b Hb. unfold all_batches. apply in_app_iff. left. exact Hb.
  + do 4 (apply Forall_cons; [rng LI; unfold o_q_size; zl|]).
    apply sn_batches. intros b Hb. unfold all_batches. apply in_app_iff. right. exact Hb.
- (* the fake stack's cells *)
  unfold fs_cells. apply Forall_cons; [rng sn_F; unfold kFakeStackSize; zl|]. apply Forall_cons; [rng sn_F; unfold kFakeStackSize; zl|].
  apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
  rng sn_F. unfold kFakeStackSize. zl.
- (* the depot's cells *)
  unfold depot_cells.
  apply Forall_cons; [rng sn_depot; unfold d_nuniq; zl|]. apply Forall_cons; [rng sn_depot; unfold d_map1; zl|].
  apply Forall_cons; [rng sn_store; unfold s_total; zl|]. apply Forall_cons; [rng sn_store; unfold s_block0; zl|]. apply Forall_nil.
- (* the internal allocator's cells *)
  pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ M)) as [I1 I2].
  unfold ialloc_cells.
  apply Forall_cons; [rng sn_iflag; zl|]. apply Forall_cons; [rng sn_iflag; zl|].
  apply Forall_cons; [rng sn_ialloc; zl|]. apply Forall_cons; [rng sn_ialloc; zl|]. apply Forall_nil.
- (* the thread's cell *)
  unfold thread_cells. apply Forall_cons; [|apply Forall_nil].
  apply (sn_rng _ _ sn_T). intros kk Hkk. cbn [c_at c_w aeval z1 c1] in *. cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ] in Hkk.
  right. unfold t_unwinding, kThreadObjSize. zl.
Qed.

Lemma sn_keep : forall c, cell_bytes_owned B ly S c -> sn_nj c -> cell_holds B ly rd0 c -> cell_holds B ly rd' c.
Proof.
intros c O NJc H. apply (cell_holds_agree_g B ly rd0); [|exact H].
intros k Hk. exact (sn_AGO _ (O k Hk) (NJc k Hk)).
Qed.

(* The view only gains: what was readable stays readable (the arm's windows are present or visible). *)
Lemma sn_VIS : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a0 HV0. set (a := bv_unsigned (Z_to_bv 64 a0)).
assert (Ra : 0 <= a < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
assert (Ex : Z_to_bv 64 a = Z_to_bv 64 a0) by (subst a; apply Z_to_bv_bv_unsigned).
assert (AV : forall (Hh : word -> bool) m, aview im_segs Hh m a0 = aview im_segs Hh m a)
  by (intros Hh m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
rewrite AV in HV0 |- *. clearbody a. clear Ex AV a0.
destruct (zr_dec (bv_unsigned (getr regs0 2) - ImgBaseAGS.AFSTACK) (bv_unsigned (getr regs0 2)) a) as [D1|D1];
  [apply apresent_view_g; apply PRS; exact D1|].
assert (DT : ImgBaseAGS.WINT ly a \/ ~ ImgBaseAGS.WINT ly a) by (unfold ImgBaseAGS.WINT; zl).
destruct DT as [D2|D2]; [apply apresent_view_g; apply PRW; exact D2|].
assert (DI : ImgBaseAGS.WINI regs0 n a \/ ~ ImgBaseAGS.WINI regs0 n a) by (unfold ImgBaseAGS.WINI; zl).
destruct DI as [D3|D3]; [exact (VISI a D3)|].
destruct (Z.eq_dec a im_oom) as [->|D4].
{ pose proof (vm_aview_g _ _ _ _ _ _ 0%nat VOOM ltac:(zl)) as X. rewrite Z.add_0_r in X. rewrite X. discriminate. }
destruct (zr_dec im_errno (im_errno + 4) a) as [D5|D5]; [apply ERRNO_VIS; rewrite SYM_ERRNO; exact D5|].
rewrite (aview_same_g im_segs (w_H W) mem0 mem' a); [exact HV0|].
apply MEQ; rewrite w64_unsigned by exact Ra; [|exact D4|exact D5].
unfold ImgBaseAGS.WINP. intros [X|[X|X]]; tauto.
Qed.

(* The shadow band's hidden bytes are not written. *)
Lemma sn_HK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem0 (w64 a).
Proof.
intros a Ha _.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as [A1 A2].
cbn [fst snd] in A1, A2. pose proof (lo_img ly LY) as (J0 & J1 & J2 & _). pose proof (lo_top ly LY) as TOP.
pose proof sn_bsl as Bs. pose proof sn_oom_img as OI.
destruct (EIMG B ly TS (IMGC ly S md0 L)) as [E1 E2].
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha.
apply MEQ; rewrite w64_unsigned by zl.
- unfold ImgBaseAGS.WINP, ImgBaseAGS.WINT, ImgBaseAGS.WINI. rewrite Hinst.
  assert (II : forall b, as_inst B <= b < as_inst B + 3632 -> in_zr b (ly_img ly)) by exact sn_inst_img.
  specialize (II (as_inst B)). unfold in_zr, kImgLo, kImgEnd, kHighMemBeg, kLowShadowBeg, kThreadObjSize, ImgBaseAGS.AFSTACK in *.
  unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats, t_unwinding in *.
  pose proof (II ltac:(zl)). zl.
- rewrite <- SYM_OOM. unfold in_zr, kImgLo, kImgEnd in *. zl.
- rewrite <- SYM_ERRNO. unfold kImgLo, kImgEnd in *. zl.
Qed.

(* The granules the shadow law reads are application bytes. *)
Lemma sn_ashadow_rng : forall g v, ashadow B ly S g = Some v -> 0 <= g /\ g + 8 <= kHighMemEnd.
Proof.
intros g v H. ceil. unfold ashadow in H.
assert (AC : ASAN_CEIL + 8 <= kHighMemEnd) by (unfold ASAN_CEIL, kHighMemEnd in *; zl).
destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg].
  pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & _). destruct G1 as [A1 _]. zl.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
  apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
  + apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
    pose proof (region_in_prim ly c LY ltac:(zl)) as (R1 & R2 & R3 & R4 & R5).
    pose proof (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) c ltac:(zl)) as CL.
    pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _].
    pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3.
    pose proof (mapped_bound_cf (as_universe B) 0 0 0 S c (amc_wf _ _ _ _ _ M) ltac:(zl)) as MB.
    unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kHighMemBeg, ASAN_CEIL in *.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; zl.
  + pose proof (proj1 (Forall_forall _ _) (proj1 (amc_placed _ _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3).
    cbn [fst snd] in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zl.
Qed.

(* The two machine cells (ARmcf's amc_exh_cell / amc_errb_cells) after the refusal arm's writes: the arm writes neither
   (the exhausted bytes are RegionInfo bytes of the primary space, the errbuf object is an image byte apart from the
   instance object and the out-of-memory byte); the bytes' ownership is ARmcf's amc_cells_owned. *)
Lemma sn_exh : exh_cell_cf B ly S rd'.
Proof.
pose proof (lo_space_in ly LY) as [S1 S2].
pose proof (YGcfImgRows.EXH_OFF_bound (proj1 (amc_cells_owned _ _ _ _ _ M))) as XB.
eapply (exh_cell_cf_frame B); [exact (amc_exh_cell _ _ _ _ _ M) | intros c; reflexivity |].
intros c Hc. cbn [aeval aoff].
apply sn_AGO.
- eapply own_rinfo_cf; [exact M |]. unfold kRegionInfoOff in *. zl.
- apply sn_prim. unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *. zl.
Qed.
Lemma sn_errb : errb_cells_cf B ly S rd'.
Proof.
eapply (errb_cells_cf_frame B);
  [exact (amc_errb_cells _ _ _ _ _ M) | reflexivity | reflexivity | reflexivity | reflexivity | | exact sn_VIS].
intros a Ha. destruct (ERRB_SEP_at B TS ERRB_SEP ly a LY (IMGC ly S md0 L) (amc_tsd _ _ _ _ _ M) Ha) as (N1 & N2 & _ & _ & _).
pose proof (proj1 (proj2 (amc_cells_owned _ _ _ _ _ M)) a Ha) as OS.
apply sn_AGO; [exact (own_static_cf B ly S Hp _ a M OS)|].
apply Exists_exists in OS as (r & Hr & Hin).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
assert (II : in_zr a (ly_img ly)) by (unfold in_zr in *; zl).
intros X. destruct (sn_junk_loc a X) as [Y|[Y|Y]].
- exact (sn_T_img a ltac:(unfold kThreadObjSize; zl) II).
- apply N1. zl.
- exact (N2 Y).
Qed.
(* Printf's two cells after the refusal arm: the arm writes neither (owned image bytes apart from the instance object
   and the out-of-memory byte). *)
Lemma sn_pf : pf_cells_cf B ly rd'.
Proof.
apply (pf_cells_move_cf B ly S Hp rd0 rd' (fun a => NJ a) M (amc_pf_owned _ _ _ _ _ M)); [exact sn_AGO | | exact (amc_pf_cells _ _ _ _ _ M)].
intros a Ha X. destruct (PF_SEP ly a LY (IMGC ly S md0 L) (amc_tsd _ _ _ _ _ M) Ha) as [N2 _].
destruct (proj1 (amc_pf_owned _ _ _ _ _ M) a Ha) as [OS NI].
apply Exists_exists in OS as (r & Hr & Hin).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
assert (II : in_zr a (ly_img ly)) by (unfold in_zr in *; zl).
destruct (sn_junk_loc a X) as [Y|[Y|Y]].
- exact (sn_T_img a ltac:(unfold kThreadObjSize; zl) II).
- apply NI. unfold kInstObjSize. zl.
- exact (N2 Y).
Qed.


Lemma sn_ARm : ARmcf B ly S Hp rd'.
Proof.
pose proof M as M0. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_tsd _ _ _ _ _ M) as TSD.
pose proof (IMGC ly S md0 L) as IMG.
pose proof (acells_owned_cf B ly S Hp _ M) as CO. pose proof (const_cells_owned_cf B ly S Hp _ M) as KO.
pose proof sn_cells_loc as CL.
destruct M0 as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg Xhp Xxs
  Xexh Xerr Xown Xpf Xpfo].
constructor; try assumption; [| | | | | | | | | | | exact sn_exh | exact sn_errb | exact sn_pf].
- apply Forall_forall. intros c Hc. apply sn_keep; [exact (proj1 (Forall_forall _ _) KO c Hc) | | exact (proj1 (Forall_forall _ _) Xconst c Hc)].
  intros k Hk. exact (CONST_NOT_JUNK ly regs0 n c k LY IMG TSD Hinst Hn Hc Hk).
- apply Forall_forall. intros c Hc. apply sn_keep; [exact (proj1 (Forall_forall _ _) CO c Hc) | exact (proj1 (Forall_forall _ _) CL c Hc) |
    exact (proj1 (Forall_forall _ _) Xcells c Hc)].
- intros c i v Hc Hi Hv k Hk.
  pose proof (wfc_classes _ _ _ _ _ Xwf c Hc) as CLc. pose proof (wrc_fa_len _ _ _ _ _ _ CLc) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CLc) as FB.
  pose proof (region_in_prim ly c LY Hc) as (R1 & R2 & _).
  rewrite sn_AGO; [exact (Xfa c i v Hc Hi Hv k Hk) | eapply own_fa_cf; [exact M | exact Hc | unfold kFreeArrayMax in *; zl] |].
  apply sn_prim. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. zl.
- intros cid pos Hc Hpos. pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
  rewrite sn_AGO; [exact (Xflags cid pos Hc Hpos) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low_cf; [exact M | zl] |].
  apply sn_F. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. zl.
- destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
  + intros b Hb. destruct (D1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk.
    rewrite sn_AGO; [exact (Hr k Hk) | eapply (own_area_cf B ly S Hp _ (as_depot B, 4 * 2 ^ 20 + 32)); [exact M | cbn; tauto | cbn; unfold d_tab_words in Hb; zl] |].
    apply sn_depot. unfold d_tab_words in Hb. zl.
  + intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
    assert (NB : depot_ids S <= 4097).
    { pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)). unfold depot_ids, DEPOT_MAX in *. zl. }
    assert (OR : forall k, 0 <= k < 16 -> aowned B ly S (ly_NB ly + 16 * id + k) /\ NJ (ly_NB ly + 16 * id + k)).
    { intros k Hk. split.
      - eapply (own_core_cf B ly S Hp _ (ly_NB ly, kNodesBlockSize)); [exact M | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; zl].
      - apply sn_NB. unfold kNodesBlockSize. zl. }
    split; intros k Hk.
    * destruct (OR (Z.of_nat k) ltac:(zl)) as [O1 O2]. rewrite sn_AGO; [exact (H2 k Hk) | exact O1 | exact O2].
    * destruct (OR (8 + Z.of_nat k) ltac:(zl)) as [O1 O2].
      replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by zl.
      rewrite sn_AGO; [| exact O1 | exact O2]. replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by zl.
      exact (H3 k Hk).
- intros g v Hg Hv0. rewrite sn_AGO; [exact (Xshadow g v Hg Hv0) | eapply ashadow_owned_cf; [exact M | exact Hv0] |].
  apply sn_shadow. pose proof (sn_ashadow_rng g v Hv0) as Rg. pose proof (sn_shadow_rng g 8 0 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)) as X.
  rewrite Z.add_0_r in X. exact X.
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. fold (shadow_addr (fst r)).
  change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
  rewrite sn_AGO; [exact (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) | eapply own_shadow_zero_cf; [exact M | exact Hr | exact Hi] |].
  apply sn_shadow. unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
  + pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). cbn [fst snd] in *.
    apply (sn_shadow_rng _ (ly_stk_hi ly - ly_stk_lo ly)); unfold kHighMemBeg in *; zl.
  + pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ Xsyms) r Hr) as (Z1 & Z2 & _ & _ & Z5).
    apply (sn_shadow_rng _ (snd r)); unfold kLowMemEnd, kHighMemEnd in *; zl.
- eapply Forall_range_vis_keep; [exact sn_VIS | assumption].
- eapply Forall_range_vis_keep; [exact sn_VIS | assumption].
- eapply Forall_range_vis_keep; [exact sn_VIS | assumption].
- apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
  rewrite sn_AGO; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi) |
    eapply (own_area_cf B ly S Hp _ (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M | cbn; tauto |];
    unfold ialloc_zero in Hr; cbn [fst snd]; destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zl |].
  apply sn_ialloc. unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zl.
Qed.

Lemma sn_ahs : ahs B ly S (w_H W) mem'.
Proof.
pose proof HAR as (_ & _ & _ & _ & HS).
eapply (ahs_transfer_cf im_segs B ly S Hp S (w_H W) mem0 mem');
  [ intros sg Hsg; eapply al_img_env_cf; [exact LY | exact L | exact Hsg] | exact M | exact HS | exact sn_VIS | exact sn_HK
  | intros a _ C; exact C | reflexivity | ].
intros g Hg HA HF _. apply sn_AGO; [eapply hfree_shadow_owned_cf; [exact M | exact Hg | exact HA | exact HF] |].
apply sn_shadow. destruct HA as [H0 HLH]. ceil.
rewrite <- (Z.add_0_r (shadow_addr g)).
apply (sn_shadow_rng g 8 0); unfold kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; zl.
Qed.

Lemma sn_ARcf : forall mat, ARcf im_segs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
intros mat. pose proof HAR as (_ & _ & BUD & MW & _).
split; [exact sn_ARm|]. split; [exact (ledger_wvb_cf ly S md0 mat L)|]. split; [exact BUD|]. split; [|exact sn_ahs].
apply (amwf_same md0); [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
Qed.

End n.

(* The refusal arm's post (AGif5.post_null_S). *)
Lemma post_null_cf : forall Hp inst ly S W mem0 md0 n tr regs0 regs' mem' mat,
  ARXq_cf B IOK Hp inst ly S W mem0 md0 -> rpre_cf B S n -> 64513 <= n < cf_malloc_max ->
  blocks_bytes S + n <= LIVE_MAX -> U_cf B tr S ->
  ims_wframe W ly regs0 mem0 tr -> getr regs0 11 = Z_to_bv 64 inst ->
  snull W ly regs0 mem0 inst n (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) 0 regs' mem' ->
  ARXq_cf B IOK Hp inst ly (set_nev (st_nev S + 1) S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
  qtight (set_nev (st_nev S + 1) S) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ AOX_cf B ly S a -> ~ ascratch B AFSTACK_G regs0 a ->
     aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem0 a) /\
  (forall x : word, ~ AOX_cf B ly S (bv_unsigned x) -> ~ AOX_cf B ly (set_nev (st_nev S + 1) S) (bv_unsigned x) ->
     ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) -> mem' x = mem0 x).
Proof.
intros Hp inst ly S W mem0 md0 n tr regs0 regs' mem' mat HX _ Nr _ _ WFR Hi11 SN.
pose proof (ARXq_cf_iok B IOK Hp inst ly S W mem0 md0 HX) as IOKi.
pose proof (IOK_inst inst IOKi) as EI.
pose proof (ARXq_cf_ARcf B IOK Hp inst ly S W mem0 md0 HX) as HAR.
pose proof (ARXq_cf_xsm B IOK Hp inst ly S W mem0 md0 HX) as XSM.
pose proof (ARXq_cf_qtight B IOK Hp inst ly S W mem0 md0 HX) as Q.
pose proof (AGif4.sn_MEQ _ _ _ _ _ _ _ _ _ _ _ SN) as MEQ. pose proof (AGif4.sn_PRS _ _ _ _ _ _ _ _ _ _ _ SN) as PRS.
pose proof (AGif4.sn_PRW _ _ _ _ _ _ _ _ _ _ _ SN) as PRW. pose proof (AGif4.sn_VISI _ _ _ _ _ _ _ _ _ _ _ SN) as VISI.
pose proof (AGif4.sn_Voom _ _ _ _ _ _ _ _ _ _ _ SN) as VOOM. pose proof (AGif4.sn_Vunw _ _ _ _ _ _ _ _ _ _ _ SN) as VUNW.
pose proof (AGif4.sn_Vres _ _ _ _ _ _ _ _ _ _ _ SN) as VRES. pose proof (AGif4.sn_Vnch _ _ _ _ _ _ _ _ _ _ _ SN) as VNCH.
pose proof (AGif4.sn_Vmtx _ _ _ _ _ _ _ _ _ _ _ SN) as VMTX. clear SN.
subst inst.
pose proof (aso_cells _ (amc_syms _ _ _ _ _ (proj1 HAR))) as AC.
assert (EI11 : bv_unsigned (getr regs0 11) = as_inst B) by (rewrite Hi11; apply w64_unsigned; unfold kLowMemEnd in AC; zl).
pose proof (WFRAME_SP W ly regs0 mem0 tr WFR) as HSP.
pose proof (sn_ARcf Hp ly S W mem0 mem' md0 regs0 n HAR EI11 HSP Nr MEQ PRS PRW VISI VOOM VUNW VRES VNCH VMTX mat) as ARF.
split.
{ apply ARXq_cf_start; [exact IOKi | exact (ARcf_tick_sec Hp ly S W mem' _ ARF) | | exact Q].
  exact (xs_mapped_cf_wvb ly S md0 (m_vm_lazy md0) mat XSM). }
split; [exact Q|].
pose proof (bsl_bounds regs0 n ltac:(pose proof cf_malloc_max_bound; zl)) as Bs. rewrite EI11 in Bs.
assert (OWN : forall a, ImgBaseAGS.WINT ly a \/ ImgBaseAGS.WINI regs0 n a \/ a = im_oom -> aowned B ly S a).
{ intros a [X|[X|X]].
  - apply (own_core_cf B ly S Hp _ (ly_T ly, kThreadObjSize) a (proj1 HAR)); [unfold core_extents; cbn; tauto|].
    cbn [fst snd]. unfold ImgBaseAGS.WINT, t_unwinding, kThreadObjSize in *. zl.
  - apply (own_area_cf B ly S Hp _ (as_inst B, 3632) a (proj1 HAR)); [unfold asyms_areas; cbn; tauto|].
    unfold ImgBaseAGS.WINI in X. rewrite EI11 in X. cbn [fst snd].
    unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. zl.
  - subst a. rewrite <- SYM_OOM.
    apply (own_area_cf B ly S Hp _ (as_oom_byte B, 1) (as_oom_byte B) (proj1 HAR)); [unfold asyms_areas; cbn; tauto | cbn [fst snd]; zl]. }
assert (RAW : forall a, 0 <= a < 2 ^ 64 -> ~ AOX_cf B ly S a -> ~ ascratch B AFSTACK_G regs0 a ->
  mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ra NO NS. apply MEQ; rewrite w64_unsigned by exact Ra.
  - intros [X|[X|X]].
    + apply NS. left. unfold spZ, AFSTACK_G. unfold ImgBaseAGS.AFSTACK in X. exact X.
    + apply NO. left. apply OWN. left. exact X.
    + apply NO. left. apply OWN. right; left. exact X.
  - intros X. apply NO. left. apply OWN. right; right. exact X.
  - intros X. apply NS. right. rewrite SYM_ERRNO. exact X. }
split; [intros a Ra NO NS; apply aview_same_g; exact (RAW a Ra NO NS)|].
intros x NO _ NS. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
rewrite <- (Z_to_bv_bv_unsigned 64 x). exact (RAW _ Rx NO NS).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The errno add-ons (AGif5E.v's twin).  The image facts are ErrnoApart / ErrnoApartS's Props, each discharged by    *)
(* the unit at its own image [cgif: ErrnoApartcgif / ErrnoApartScgif].                                              *)
Hypothesis EDZ : ErrnoApartS.errno_apart_dzone_s.
Hypothesis ESH : ErrnoApartS.errno_apart_shadow_s.
Hypothesis EZ3 : ErrnoApartS.errno_apart_zone3_s.
Hypothesis EINST : ErrnoApart.errno_apart_inst_ag.
Hypothesis EUNH : ErrnoApart.errno_unhidden.
(* The symbol table's instance object is in AGImg's instance window [cgif: AGif0cgif.inst_ok at TFIB_INST]. *)
Hypothesis INST_AG : ag_inst_ok (as_inst B).

(* ErrnoApartS.errno_apart_wini_s / errno_apart_win_s at the cf request bound (they state n <= MALLOC_MAX; below
   2 ^ 30 the by_size_log word is still inside the instance window, bsl_bounds). *)
Lemma errno_apart_wini_cf : forall (regs0 : bvmap 5 word) n a, ag_inst_ok (bv_unsigned (getr regs0 11)) ->
  64513 <= n < 2 ^ 30 -> ImgBaseAGS.WINI regs0 n a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros regs0 n a HO Hn Hw. apply (EINST B (bv_unsigned (getr regs0 11)) a TS HO).
pose proof (bsl_bounds regs0 n Hn) as Bs. unfold ImgBaseAGS.WINI in Hw.
unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in Hw. zl.
Qed.
Lemma errno_apart_win_cf : forall ly (regs0 : bvmap 5 word) n idx mb a, layout_ok ly -> im_img_cover ly ->
  ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) ->
  ag_inst_ok (bv_unsigned (getr regs0 11)) -> 64513 <= n < 2 ^ 30 -> 0 <= idx -> 0 <= mb ->
  ims_zone3 mb (ImgBaseAGS.MSv n) -> ImgBaseAGS.WIN ly regs0 n idx mb a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros ly regs0 n idx mb a LY IMG HSP HO Hn Hidx Hmb Hz Hw.
unfold ImgBaseAGS.WIN in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- refine (ErrnoApart.errno_apart_stack EIMG B ly _ _ a TS LY IMG _ Hw). zl.
- exact (ErrnoApartS.errno_apart_wint_s EIMG B ly a TS LY IMG Hw).
- exact (errno_apart_wini_cf regs0 n a HO Hn Hw).
- unfold ImgBaseAGS.WINM in Hw. destruct Hw as [Hw|[Hw|Hw]].
  + apply (ErrnoApart.errno_apart_Q EIMG B ly a TS LY IMG). unfold ImgBaseAGS.QSv in Hw. zl.
  + exact (EZ3 B mb (ImgBaseAGS.MSv n) a TS Hz Hw).
  + apply (ESH B a TS). unfold ImgBaseAGS.SMv in Hw. pose proof (Z.div_pos mb 8 Hmb ltac:(zl)). zl.
Qed.

(* ErrnoGS.aes_depot: the depot callee's raw frame (outside its stack window and the depot zone) keeps errno
   (AGif5E.errno_kept_depot_s_cgif's script). *)
Lemma depot_e_cf : forall Hp, ErrnoGS.aes_depot_t B (U_cf B) (ARXq_cf B IOK Hp) (dpost_cf B).
Proof.
intros Hp inst ly S W mem0 md0 tr Wy regs mem md buf HX HU MON MEQ PAD R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem0 md0 HX) as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (IMGC ly S md0 L) as IMG.
eapply SRr_mono;
  [exact (depot_cf Hp inst ly S W mem0 md0 tr Wy regs mem md buf HX HU MON MEQ PAD R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES)|].
intros W' c' _ [EW (z & regs' & mem' & mat & Ec & RP & FR & PR & DP)]. cbv beta.
split; [exact EW|]. exists z, regs', mem', mat.
split; [exact Ec|]. split; [exact RP|]. split; [exact FR|].
split; [|split; [exact PR | exact DP]].
intros i Hi. destruct (EIMG B ly TS IMG) as [E1 E2]. pose proof (lo_img ly LY) as (J0 & J1 & J2 & _).
assert (EB : bv_unsigned (Z_to_bv 64 (as_errno B + i)) = as_errno B + i) by (apply w64_unsigned; unfold kImgLo, kImgEnd in *; zl).
refine (FR (Z_to_bv 64 (as_errno B + i)) _ _); rewrite EB.
- intros Hs. exact (ErrnoApart.errno_apart_stack EIMG B ly _ _ (as_errno B + i) TS LY IMG SL Hs ltac:(zl)).
- intros Hd. exact (EDZ B ly (as_errno B + i) TS LY IMG Hd ltac:(zl)).
Qed.

(* The grant arm's machine post keeps errno (raw form; AGif5E.post_grant_errno_cgif). *)
Lemma post_grant_errno_cf : forall Hp inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem',
  ARXq_cf B IOK Hp inst ly S W mem0 md0 -> 64513 <= n < cf_malloc_max -> ims_wframe W ly regs0 mem0 tr ->
  getr regs0 11 = Z_to_bv 64 inst ->
  AGif4.skern grow W Wz md0 mdz ly mb (ImgBaseAGS.MSv n) (ImgBaseAGS.QSv ly (Z.of_nat (length (st_sec_arr S)))) ->
  AGif4.sfin W ly regs0 mem0 inst n tr (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) mb
    (fun zz m => dpost_cf B inst ly S W tr zz m) grow z Wz regs' mem' ->
  ErrnoG.errno_kept B mem0 mem'.
Proof.
intros Hp inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' HX Nr WFR Hi11 SK SFN.
pose proof (ARXq_cf_iok B IOK Hp inst ly S W mem0 md0 HX) as IOKi.
destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem0 md0 HX) as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (IMGC ly S md0 L) as IMG.
pose proof (AGif4.sf_MEQF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN) as MEQF.
pose proof (AGif4.sk_mbr _ _ _ _ _ _ _ _ _ SK) as Hmbr.
destruct (AGif4.sk_md _ _ _ _ _ _ _ _ _ SK) as (mat & matV & mat' & _ & GOK & _).
pose proof cf_malloc_max_bound as CMB.
pose proof (msv_facts n ltac:(zl)) as (MS1 & MS2 & MS3).
pose proof (apart_gen_cf Hp inst ly S W mem0 md0 mat (ImgBaseAGS.MSv n) (YG0d.w64 mb) HX ltac:(zl) MS2 GOK) as (ZN & _ & _).
assert (Umb : bv_unsigned (YG0d.w64 mb) = mb) by (apply w64_unsigned; exact Hmbr).
rewrite Umb in ZN.
pose proof (AGif2.sv_resb _ _ _ _ _ _ _ (view_cf Hp inst ly S W mem0 md0 HX)) as (RES & _).
pose proof (AGif2.sv_idx _ _ _ _ _ _ _ (view_cf Hp inst ly S W mem0 md0 HX)) as IDX.
pose proof (WFRAME_SP W ly regs0 mem0 tr WFR) as [HSP _].
pose proof (aso_cells _ (amc_syms _ _ _ _ _ M)) as AC.
assert (HO : ag_inst_ok (bv_unsigned (getr regs0 11))).
{ pose proof (IOK_inst inst IOKi) as EI. rewrite Hi11. rewrite w64_unsigned by (rewrite EI; unfold kLowMemEnd in *; zl).
  rewrite EI. exact INST_AG. }
intros i Hi. destruct (EIMG B ly TS IMG) as [E1 E2]. pose proof (lo_img ly LY) as (J0 & J1 & J2 & _).
assert (EB : bv_unsigned (Z_to_bv 64 (as_errno B + i)) = as_errno B + i) by (apply w64_unsigned; unfold kImgLo, kImgEnd in *; zl).
refine (MEQF (Z_to_bv 64 (as_errno B + i)) _ _ _); rewrite EB.
- intros Hw. exact (errno_apart_win_cf ly regs0 n (Z.of_nat (length (st_sec_arr S))) mb (as_errno B + i) LY IMG HSP HO
    ltac:(zl) ltac:(zl) ltac:(zl) ZN Hw ltac:(zl)).
- intros [_ Hq]. exact (ErrnoApartS.errno_apart_qr EIMG B ly (st_sec_reserved S) (as_errno B + i) TS LY IMG ltac:(zl) Hq ltac:(zl)).
- intros Hd. exact (ErrnoApartS.errno_apart_dx EIMG EDZ B ly (bv_unsigned (getr regs0 2)) (as_errno B + i) TS LY IMG HSP Hd ltac:(zl)).
Qed.

(* AIfaceS's add-ons at the cf instance (AGif5E.ifaceSE_cgif's twin). *)
Theorem ifaceSE_cf : forall Hp, ErrnoGS.AIfaceSE B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
intros Hp. constructor.
- exact (depot_e_cf Hp).
- intros inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' HX _ Nr _ _ WFR Hi11 _ SK SFN _.
  apply (ErrnoApart.errno_kept_v_of_raw EUNH B W Wz mem0 mem' TS).
  exact (post_grant_errno_cf Hp inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' HX Nr WFR Hi11 SK SFN).
- intros inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' HX _ Nr _ _ WFR Hi11 _ SK SFN _.
  exact (post_grant_errno_cf Hp inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' HX Nr WFR Hi11 SK SFN).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (b) the tree at a secondary size (AGif5.shape_S's twin).                                                          *)
Lemma shape_cf : forall n tr S, 64513 <= n < cf_malloc_max -> from_primary n = false ->
  malloc_cf n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) cf_pc_malloc_max ;;
                      ob <- sec_alloc n ;; ImgBaseAGS.malloc_K_t cf_pc_spin_shadow n tr ob) S.
Proof. intros n tr S _ FP. unfold malloc_cf, ImgBaseAGS.malloc_K_t. rewrite FP. reflexivity. Qed.

(* ifs_grant at the obstacle bound NOB = 2 ^ 29 <= cf_nob (cf_nob_lo). *)
Lemma grant_cf : forall Hp inst ly S W mem md mat sz, ARXq_cf B IOK Hp inst ly S W mem md -> 0 < sz <= ImgBaseAGS.NOB ->
  exists a, grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true.
Proof.
intros Hp inst ly S W mem md mat sz H Hsz. pose proof cf_nob_lo as NL.
apply (grant_w_cf Hp inst ly S W mem md mat sz H). unfold ImgBaseAGS.NOB in Hsz. zl.
Qed.

(* ifs_apart / ifs_apart_w: every size they ask is below 2 ^ 40. *)
Lemma apart_cf : forall Hp inst ly S W mem md mat sz (a : word), ARXq_cf B IOK Hp inst ly S W mem md ->
  0 < sz <= MALLOC_MAX + 4 * 4096 -> sz mod 4096 = 0 ->
  grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true ->
  ims_zone3 (bv_unsigned a) sz /\
  Forall (zdisjoint (bv_unsigned a, sz)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) /\
  (forall g, g mod 8 = 0 -> bv_unsigned a <= g -> g + 8 <= bv_unsigned a + sz ->
     mem (Z_to_bv 64 (shadow_addr g)) = Some (Z_to_bv 8 0)).
Proof. intros Hp inst ly S W mem md mat sz a H Hsz Hal HG. exact (apart_gen_cf Hp inst ly S W mem md mat sz a H ltac:(unfold MALLOC_MAX in Hsz; zl) Hal HG). Qed.
Lemma apart_w_cf : forall Hp, AGif4.ifs_apart_w (ARXq_cf B IOK Hp) cf_malloc_max.
Proof.
intros Hp inst ly S W mem md mat sz a H Hsz Hal HG. pose proof cf_malloc_max_bound as CB.
exact (apart_gen_cf Hp inst ly S W mem md mat sz a H ltac:(zl) Hal HG).
Qed.

(* ifs_room_w at the unit's room ROOMW: any ROOMW <= CF_HEAD (room_gen_cf); YGcfRoomCf.ROOMW_nmaxw_fits shows the least
   ROOMW YGcfMallocComposeE.nmaxw_cf_ok asks fits. *)
Lemma room_w_cf : forall Hp ROOMW, ROOMW <= CF_HEAD -> AGif4.ifs_room_w (ARXq_cf B IOK Hp) (rpre_cf B) ROOMW.
Proof. intros Hp ROOMW HR inst ly S W mem md n H (_ & _ & _ & HO). exact (room_gen_cf ROOMW Hp inst ly S W mem md H HO HR). Qed.

(* ================================================================================================================ *)
(* (e) The grant arm's post (AGif5.post_grant_S's twin): the model's final state, the ledger of the grown layout and *)
(*     ARcf of the final state (the twin of AGjy.AR_transport over the image-free write set below).                   *)

(* The block's sizes at a secondary request below 2 ^ 30 (AGif5.sizesK's model part). *)
Lemma sizes_cf : forall n, 64513 <= n < 2 ^ 30 ->
  needed_size n = ImgBaseAGS.NDv n /\ sec_map_size n = ImgBaseAGS.MSv n /\ req_size n = n /\ rz_size n = 2048 /\
  from_primary n = false.
Proof.
intros n Nr.
assert (RZ : rz_size n = 2048).
{ unfold rz_size, rz_log. rewrite (proj2 (Z.leb_gt n 48)), (proj2 (Z.leb_gt n 96)), (proj2 (Z.leb_gt n 448)), (proj2 (Z.leb_gt n 3968)),
  (proj2 (Z.leb_gt n 16128)), (proj2 (Z.leb_gt n 32256)), (proj2 (Z.leb_gt n 64512)) by zl. reflexivity. }
assert (RS : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); zl).
assert (R8 : rounded_size n = ImgBaseAGS.R8v n)
  by (unfold rounded_size, round_up, ImgBaseAGS.R8v; rewrite Z.max_l by zl; replace (n + 8 - 1) with (n + 7) by zl; reflexivity).
assert (FP : from_primary n = false).
{ unfold from_primary, needed_primary. rewrite R8, RZ. apply Z.leb_gt. unfold kMaxSize, ImgBaseAGS.R8v.
  pose proof (Z.div_mod (n + 7) 8 ltac:(zl)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zl)). zl. }
assert (ND : needed_size n = ImgBaseAGS.NDv n) by (unfold needed_size, needed_primary, ImgBaseAGS.NDv; rewrite FP, R8, RZ; zl).
assert (MS : sec_map_size n = ImgBaseAGS.MSv n).
{ unfold sec_map_size, round_up, ImgBaseAGS.MSv, kPage. rewrite ND.
  replace (ImgBaseAGS.NDv n + 4096 - 1) with (ImgBaseAGS.NDv n + 4095) by zl. reflexivity. }
repeat split; assumption.
Qed.

(* Wf_cf and qtight of the final state (AGif5.post_model's twin), from YG07cf.WfP_cf_add_sec over the tick and the
   depot's answer [z]: the map is granted, the pointer-array commit (when the array is full) is granted. *)
Lemma post_model_cf : forall S n tr z grow,
  universe_ok (as_universe B) -> Wf_cf (as_universe B) S -> 64513 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
  admits (as_universe B) tr S -> Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max ->
  (grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S) -> aok S (KDepot tr) z ->
  Wf_cf (as_universe B) (AGif4.SFSz S n tr z grow) /\ (qtight S -> qtight (AGif4.SFSz S n tr z grow)).
Proof.
intros S n tr z grow HU WF Nr Hlive Htr HSEC Hgrow AOK.
pose proof cf_malloc_max_bound as CB.
destruct (sizes_cf n ltac:(zl)) as (ND & MS & RS & RZ & FP).
pose proof (YG02cf.WfP_cf_tick' _ S WF) as W1.
assert (DD : depot_fits (as_universe B) (ImgBaseAGS.depF S tr z)).
{ unfold ImgBaseAGS.depF. destruct (Z.eqb_spec z 0) as [_|Hz]; [exact (wfc_depot _ _ _ _ _ WF)|].
  cbn [aok] in AOK. destruct AOK as [E|[_ Hmt]]; [contradiction|].
  exact (depot_put_fits _ S tr (wfc_depot _ _ _ _ _ WF) Htr Hmt). }
pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as WR.
assert (HRES : (ImgBaseAGS.resF S grow = st_sec_reserved (set_nev (st_nev S + 1) S) /\
                Z.of_nat (length (st_sec_arr (set_nev (st_nev S + 1) S))) < st_sec_reserved (set_nev (st_nev S + 1) S)) \/
  (ImgBaseAGS.resF S grow = st_sec_reserved (set_nev (st_nev S + 1) S) + kPtrArrayEntriesPerCommit /\
   Z.of_nat (length (st_sec_arr (set_nev (st_nev S + 1) S))) = st_sec_reserved (set_nev (st_nev S + 1) S))).
{ unfold ImgBaseAGS.resF. cbn [st_sec_reserved st_sec_arr set_nev].
  destruct grow; [right; split; [reflexivity | apply Hgrow; reflexivity] | left; split; [reflexivity|]].
  destruct (Z.eq_dec (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S)) as [E|E]; [apply Hgrow in E; discriminate E | zl]. }
pose proof (YG07cf.WfP_cf_add_sec _ 1 1 1 (set_nev (st_nev S + 1) S) n (ImgBaseAGS.depF S tr z) (ImgBaseAGS.resF S grow)
  W1 ltac:(zl) ltac:(zl) FP Hlive DD HSEC HRES) as W4.
cbv zeta in W4.
match type of W4 with WfP_cf _ _ _ _ ?X => assert (EX : X = AGif4.SFSz S n tr z grow) end.
{ unfold AGif4.SFSz, ImgBaseAGS.sfinal, ImgBaseAGS.KS, ImgBaseAGS.rS. rewrite <- MS, <- ND. destruct S; reflexivity. }
rewrite EX in W4. split.
- unfold Wf_cf. eapply WfP_cf_weaken; [exact W4 | zl | zl | zl].
- intros QT. apply (qtight_alloc_app S _ (ImgBaseAGS.KS S n)); [reflexivity | reflexivity | reflexivity | reflexivity | exact QT].
Qed.

(* The ledger of the grown layout: the anonymous map of the block (YG0j.ALedger_anon's twin over ALedger_cf, whose cover
   also allows the errbuf slot and whose eager bound also adds its capacity). *)
Lemma ALedger_anon_cf : forall ly S S' md (a nw : word) (r : nat) (av : Z),
  layout_ok ly -> Wf_cf (as_universe B) S -> sec_placed ly S -> amwf md -> ALedger_cf im_segs ly S md ->
  grant_ok_na_pin md a (bv_unsigned nw) = true -> 0 < bv_unsigned nw < 2 ^ 40 -> bv_unsigned nw mod 4096 = 0 ->
  (forall c, 1 <= c <= 31 -> reg S' c = reg S c) -> prim_committed S' = prim_committed S ->
  sec_extents (set_ly_sec ly r av) S' = sec_extents ly S ++ [(bv_unsigned a, bv_unsigned nw)] ->
  st_sec_reserved S' = st_sec_reserved S ->
  errb_zone (set_ly_sec ly r av) S' = errb_zone ly S -> errb_cap_cf S' = errb_cap_cf S ->
  ALedger_cf im_segs (set_ly_sec ly r av) S' (mmap_model a nw md).
Proof.
intros ly S S' md a nw r av LO W PL MW L G Hn Hal REG PC SE SR EZ EC.
pose proof (gf_facts im_segs _ ly S md a (bv_unsigned nw) LO W PL L Hn Hal G) as (FA1 & FA2 & FA3 & FA4).
set (md' := mmap_model a nw md).
assert (ELZ : lazy_zones (set_ly_sec ly r av) = lazy_zones ly) by reflexivity.
assert (EPM : perm_maps (set_ly_sec ly r av) = perm_maps ly) by reflexivity.
assert (EP : ly_prim (set_ly_sec ly r av) = ly_prim ly) by reflexivity.
assert (EQ : ly_Q (set_ly_sec ly r av) = ly_Q ly) by reflexivity.
assert (EI : ly_img (set_ly_sec ly r av) = ly_img ly) by reflexivity.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 nw) as Rn. unfold bv_modulus in Ra, Rn.
pose proof G as G'. unfold grant_ok_na_pin in G. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3].
apply andb_prop in G as [G1 G2].
assert (Hn64 : Z_to_bv 64 (bv_unsigned nw) = nw) by (apply w64_uw). rewrite Hn64 in G4.
assert (VM' : vm_maps (m_vmmaps md') = (a, nw) :: vm_maps (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (RES' : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (LIM' : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (ISP' : vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (TOP' : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by (unfold alloc_top; rewrite ISP'; reflexivity).
assert (NA' : vm_noaccess (m_vmmaps md') = vm_noaccess (m_vmmaps md)) by (subst md'; unfold mmap_model; mproj; reflexivity).
assert (LZ' : m_vm_lazy md' = m_vm_lazy md) by (subst md'; unfold mmap_model; mproj; reflexivity).
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
assert (MWF : YK0g.model_ivs_wf md).
{ destruct MW as [(W1 & W2 & W3 & _) _]. split; [|split; [|split]];
  [intros q Hq; exact (W1 q Hq) | intros q Hq; exact (W2 q Hq) | intros q Hq; exact (W3 q Hq) |].
  exact (ceil_top_init_sp_ok _ L13). }
assert (EG : eager_used md' = eager_used md + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(bv_unsigned a, bv_unsigned nw)]).
{ subst md'. apply eager_used_mmap_model; [exact MWF |]. ceil. unfold ASAN_CEIL in *. zl. }
assert (MONO1 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\
  rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c')) by (intros c' Hc'; rewrite (REG c' Hc'); zl).
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) by (intros c' Hc'; rewrite (REG c' Hc'); reflexivity).
constructor; rewrite ?ELZ, ?EPM, ?EP, ?EQ, ?EI, ?VM', ?RES', ?LIM', ?TOP', ?NA', ?LZ', ?SE, ?PC, ?SR, ?EZ, ?EC, ?EG; try assumption.
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|].
  + eapply Forall_impl; [|exact P1]. intros p (A & B0 & C). split; [exact A|].
    change (cut_ok (set_ly_sec ly r av) S' (fst p) /\ cut_ok (set_ly_sec ly r av) S' (fst p + snd p))
      with (cut_ok ly S' (fst p) /\ cut_ok ly S' (fst p + snd p)).
    split; apply (cut_ok_mono ly S S' MONO1); assumption.
  + intros x Hx. rewrite (P3 x Hx). change (prim_hole_at (set_ly_sec ly r av) S' x) with (prim_hole_at ly S' x).
    rewrite (prim_hole_at_same ly S S' HOLES x). tauto.
  + intros p. rewrite (P4 p). split.
    * intros (Hin & B1 & B2 & B3). split; [right; exact Hin | auto].
    * intros ([Heq|Hin] & B1 & B2 & B3); [| auto]. exfalso.
      pose proof (lo_high ly LO) as [HP1 HP2].
      assert (Ua : bv_unsigned a = fst p).
      { apply (f_equal fst) in Heq. cbn [fst wiv] in Heq. rewrite Heq. unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
        ceil; unfold bv_modulus, kHighMemBeg, kPrimResvSize, ASAN_CEIL in *. zl. }
      assert (PRIM : zdisjoint (bv_unsigned a, bv_unsigned nw) (ly_prim ly, kPrimResvSize)).
      { exact (proj1 (Forall_forall _ _) FA4 _ ltac:(apply in_app_iff; left; unfold static_extents, owned_extents; cbn; tauto)). }
      unfold zdisjoint in PRIM. cbn [fst snd] in PRIM. zl.
- right. exact L5.
- right. exact L6.
- intros e He. apply in_app_iff in He as [He|[<-|[]]]; [right; exact (L7 e He)|]. left. unfold wiv. cbn [fst snd]. rewrite !w64_uw. reflexivity.
- intros e [<-|He].
  + apply Exists_exists. exists (bv_unsigned a, bv_unsigned nw). split; [|cbn [fst snd]; zl].
    apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity.
  + apply Exists_exists. pose proof (L8 e He) as X. apply Exists_exists in X as (y & Hy & Hy'). exists y. split; [|exact Hy'].
    apply in_app_iff in Hy as [Hy|Hy]; [apply in_app_iff; left; exact Hy|]. apply in_app_iff. right.
    apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; apply in_app_iff; left; exact Hy | right; exact Hy].
- unfold eager_cf in L9 |- *. rewrite NA', LZ', SE, EZ, PC, SR, !esec_app. rewrite !esec_app in L9. zl.
- intros y Hy. right. exact (L10 y Hy).
- intros y Hy. right. exact (L11 y Hy).
- intros e y He Hy. apply in_app_iff in He as [He|[<-|[]]]; [exact (L12 e y He Hy)|].
  exact (proj1 (Forall_forall _ _) FA4 y ltac:(rewrite !in_app_iff; right; right; left; exact Hy)).
- exact (YGcfLazyMaps.lazy_in_maps_mmap_cf a nw md L16).
- intros e He. rewrite ?VM'. right. apply L17. unfold errb_zone in EZ. rewrite EZ in He. exact He.
Qed.

(* The pointer-array commit on the grow arm (YG0j.ALedger_qcommit' over ALedger_cf). *)
Lemma ALedger_qcommit_cf : forall ly S S' md md',
  layout_ok ly -> Forall (fun e => 4096 <= snd e < 2 ^ 64) (sec_extents ly S) -> sec_placed ly S -> xs_placed_cf ly S ->
  ALedger_cf im_segs ly S md ->
  vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) -> vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) ->
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) -> vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md) ->
  vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md) ->
  (forall x, ~ (ly_Q ly <= x < ly_Q ly + kPtrArrayResv) ->
     YK0g.covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
  eager_used md' <= eager_used md + 8 * kPtrArrayEntriesPerCommit ->
  (forall c, 1 <= c <= 31 -> reg S' c = reg S c) -> sec_extents ly S' = sec_extents ly S -> prim_committed S' = prim_committed S ->
  st_sec_reserved S' = st_sec_reserved S + kPtrArrayEntriesPerCommit ->
  errb_zone ly S' = errb_zone ly S -> errb_cap_cf S' = errb_cap_cf S ->
  (forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md')) lo n = true) ->
  YGcfLazyMaps.lazy_in_maps_cf md' ->
  ALedger_cf im_segs ly S' md'.
Proof.
intros ly S S' md md' LO W PL XP L VM RES LIM MMB ISP COV EG REG SE PC SR EZ EC NAF LZM.
pose proof (esec_same_on_secs' ly S md md' W PL (cov_same_on_secs_Q ly S md md' LO PL COV)) as ES.
(* the errbuf extent lies apart from the pointer array (xs_placed_cf), so the commit leaves its eager bytes alone *)
assert (EX : esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (errb_zone ly S) =
             esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (errb_zone ly S)).
{ unfold errb_zone. apply esec_ext.
  - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) XP e He) as (_ & EA & EC' & _).
    assert (E2 : 0 <= snd e).
    { unfold xs_cf in He. destruct (last_cap_idx (st_secs S) 0 None); [|destruct He].
      destruct He as [<-|[]]. cbn [snd]. apply errb_cap_cf_nonneg. }
    pose proof alloc_ceiling_lt as CL. unfold in_app in EA. zl.
  - intros e x He Hx. apply COV. intros Hq. pose proof (proj1 (Forall_forall _ _) XP e He) as (_ & _ & _ & D).
    pose proof (proj1 (Forall_forall _ _) D (ly_Q ly, kPtrArrayResv)
      ltac:(apply in_app_iff; right; apply in_app_iff; left; unfold static_extents, owned_extents; cbn; tauto)) as DQ.
    unfold zdisjoint in DQ. cbn [fst snd] in DQ. zl. }
assert (TOP : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md)) by (unfold alloc_top; rewrite ISP; reflexivity).
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
assert (MONO1 : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\
  rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c')) by (intros c' Hc'; rewrite (REG c' Hc'); zl).
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) by (intros c' Hc'; rewrite (REG c' Hc'); reflexivity).
constructor; rewrite ?RES, ?LIM, ?VM, ?SE, ?PC, ?SR, ?ES, ?TOP, ?EZ, ?EC; try assumption;
  try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|exact P4].
  + eapply Forall_impl; [|exact P1]. intros p (A & B0 & C). split; [exact A|]. split; apply (cut_ok_mono ly S S' MONO1); assumption.
  + intros x Hx. rewrite (P3 x Hx). rewrite (prim_hole_at_same ly S S' HOLES x). tauto.
- unfold eager_cf in L9 |- *. rewrite SE, EZ, PC, SR, !esec_app, ES, EX. rewrite !esec_app in L9.
  unfold kPtrArrayEntriesPerCommit in *. zl.
- intros x Hx. rewrite <- VM. exact (LZM x Hx).
- intros e He. rewrite ?VM. apply L17. unfold errb_zone in EZ. rewrite EZ in He. exact He.
Qed.

(* A range inside a map of the list is covered by it. *)
Lemma cov_of_in_wiv : forall l e x, In (wiv e) l -> 0 <= fst e -> 0 <= snd e -> fst e + snd e < 2 ^ 64 ->
  fst e <= x < fst e + snd e -> YK0g.covered l x = true.
Proof.
intros l e x Hin H1 H2 H3 Hx. unfold YK0g.covered. apply existsb_exists. exists (wiv e). split; [exact Hin|].
unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S, wiv. cbn [fst snd].
assert (U1 : bv_unsigned (YG0n.w64 (fst e)) = fst e) by (apply w64_unsigned; zl).
assert (U2 : bv_unsigned (YG0n.w64 (snd e)) = snd e) by (apply w64_unsigned; zl).
rewrite U1, U2. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; zl.
Qed.

Lemma apresent_same_g : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a E [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.
Lemma app_not_band : forall lo len a, in_app lo len -> lo <= a < lo + len -> ~ in_band_rw a.
Proof.
intros lo len a HA Ha HB. ceil. unfold in_app, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. zl.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* More of the unit's side, for the grant arm.                                                                       *)
(* The image's shadow base is the shadow offset [cgif: AGif4cgif.AImgS_cgif's ims_shb = 0x7fff8000 = SHADOW_OFF]. *)
Hypothesis SHB_EQ : ImgBaseAGS.SHBv = SHADOW_OFF.
(* Where StackDepotPut may write: the node and store blocks, and image bytes outside the instance object, the internal
   allocator and its flag [cgif: AGjm.DZONE, the image range [0x178148, 0x5c88d0) and the two blocks]. *)
Hypothesis DZ_LOC : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> ims_dzone ly a ->
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/
  (in_zr a (ly_img ly) /\ ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
   ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2)).
(* The write zone is a decidable set of addresses [cgif: AGjm.DZONE is three integer ranges]. *)
Hypothesis DZ_DEC : forall ly a, ims_dzone ly a \/ ~ ims_dzone ly a.
(* The const and junk tables are lists that do not read the layout and name no secondary slot [cgif: ts_const,
   ts_junk_ly, AGjy.CONSTlt / JUNKlt]. *)
Hypothesis CONST_LY : forall ly1 ly2, as_const B ly1 = as_const B ly2.
Hypothesis CONST_LT : forall ly nn, Forall (cell_lt nn) (as_const B ly).
Hypothesis JUNK_LY : forall ly1 ly2, as_junk B ly1 = as_junk B ly2.
Hypothesis JUNK_LT : forall ly nn, Forall (fun r => asec_lt nn (fst r)) (as_junk B ly).
(* No const byte lies in the pointer array, in the thread object's tail the allocator writes (its stats and the
   unwinding flag), or in an instance word the allocator writes; the mutex's three pad bytes are outside these words
   [cgif: Tfib_const's addresses, AGif5.const_cells_CZ]. *)
Definition gwj (ly : alayout) (a : Z) : Prop :=
  (ly_Q ly <= a < ly_Q ly + kPtrArrayResv) \/ (ly_T ly + 2768 <= a < ly_T ly + kThreadObjSize) \/
  (as_inst B + o_sec_reserved <= a < as_inst B + o_sec_sorted + 1) \/ (as_inst B + o_sec_stats <= a < as_inst B + o_sec_stats + 32) \/
  (as_inst B + 296 <= a < as_inst B + 416) \/ (as_inst B + o_sec_mutex <= a < as_inst B + o_sec_mutex + 1) \/
  (as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40).
Hypothesis CONST_APART : forall ly c k, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> In c (as_const B ly) ->
  0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ gwj ly (aeval B ly (c_at c) + k).
(* The depot write zone's image bytes are the allocator's static bytes [cgif: Tfib_owned_static's
   [0xa5ad0, 0x5c88d0) covers AGjm.DZONE's image range]. *)
Hypothesis DZ_OWN : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> ims_dzone ly a ->
  in_zr a (ly_img ly) -> Exists (in_zr a) (as_owned_static B).

Section gr.
Variables (Hp : list Z) (ly : alayout) (S : astate) (W : world im_segs) (mem0 : word -> option byte) (md0 : Model).
Variables (regs0 : bvmap 5 word) (n : Z) (tr : list Z) (mb : Z) (grow : bool) (z : Z).
Variables (Wz : world im_segs) (regs' : bvmap 5 word) (mem' memD : word -> option byte) (mat : list word).
Hypothesis HAR : ARcf im_segs B ly S Hp W mem0 md0.
Hypothesis Hinst : bv_unsigned (getr regs0 11) = as_inst B.
Hypothesis HSP : ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) <= ly_stk_hi ly.
Hypothesis Nr : 64513 <= n < cf_malloc_max.
Hypothesis Hgrow : grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S.
Hypothesis WFF : Wf_cf (as_universe B) (AGif4.SFSz S n tr z grow).
Hypothesis Hmbr : 0 <= mb < 2 ^ 64.
Hypothesis GOK : grant_ok_na_pin (with_vm_backing (m_vm_lazy md0) mat md0) (w64 mb) (ImgBaseAGS.MSv n) = true.
Hypothesis MON : forall x : word, w_H W x = false -> w_H Wz x = false.
Hypothesis DP : dpost_cf B (as_inst B) ly S W tr z memD.
Hypothesis PRD : forall a, ims_dzone ly a -> apresent (w_H Wz) mem0 a -> apresent (w_H Wz) memD a.
Hypothesis EQD : forall x : word, ims_dzone ly (bv_unsigned x) -> mem' x = memD x.
Hypothesis SFN : AGif4.sfin W ly regs0 mem0 (as_inst B) n tr (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) mb
  (fun zz m => dpost_cf B (as_inst B) ly S W tr zz m) grow z Wz regs' mem'.
Hypothesis XSM : xs_mapped_cf ly S md0.

Local Notation MSn := (ImgBaseAGS.MSv n).
Local Notation idx := (Z.of_nat (length (st_sec_arr S))).
Local Notation res := (st_sec_reserved S).
Local Notation lyF := (AGif4.lyFz ly S mb).
Local Notation SF := (AGif4.SFSz S n tr z grow).
Local Notation KSc := (ImgBaseAGS.KS S n).
Local Notation rS0 := (ImgBaseAGS.rS S).
Local Notation sp0 := (bv_unsigned (getr regs0 2)).
Local Notation SMn := (ImgBaseAGS.SMv mb).
Local Notation QSn := (ImgBaseAGS.QSv ly (Z.of_nat (length (st_sec_arr S)))).
Local Notation rd0 := (aview im_segs (w_H W) mem0).
Local Notation rd' := (aview im_segs (w_H Wz) mem').
Local Notation rdD := (aview im_segs (w_H Wz) memD).
Let M : ARmcf B ly S Hp rd0 := proj1 HAR.
Let L : ALedger_cf im_segs ly S md0 := proj1 (proj2 HAR).
Let LY : layout_ok ly := amc_layout _ _ _ _ _ M.
Let WF : Wf_cf (as_universe B) S := amc_wf _ _ _ _ _ M.
Let PL : sec_placed ly S := amc_placed _ _ _ _ _ M.
Let IMG : im_img_cover ly := IMGC ly S md0 L.
Let TSD : ly_tsd ly = as_tsd B := amc_tsd _ _ _ _ _ M.
Let LN : ALedger_cf im_segs ly S (with_vm_backing (m_vm_lazy md0) mat md0) := ledger_wvb_cf ly S md0 mat L.
Let MEQF := AGif4.sf_MEQF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let PRS := AGif4.sf_PRS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let PRmap := AGif4.sf_PRmap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let PRsh := AGif4.sf_PRsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let PRq := AGif4.sf_PRq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let PRW := AGif4.sf_PRW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let VISW := AGif4.sf_VISW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.

(* ---- sizes, the map's place ---- *)
Lemma g_sizes : needed_size n = ImgBaseAGS.NDv n /\ sec_map_size n = MSn /\ req_size n = n /\ rz_size n = 2048 /\
  from_primary n = false.
Proof. pose proof cf_malloc_max_bound. apply sizes_cf. zl. Qed.
Lemma g_ms : 73728 <= MSn <= 262147 * 4096 /\ MSn mod 4096 = 0 /\ n + 8192 <= MSn.
Proof. pose proof cf_malloc_max_bound. apply msv_facts. zl. Qed.
Lemma g_umb : bv_unsigned (w64 mb) = mb.
Proof. apply w64_unsigned. exact Hmbr. Qed.
Lemma g_facts : page_aligned mb /\ in_app mb MSn /\ mb + MSn <= ASAN_CEIL /\
  Forall (zdisjoint (mb, MSn)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps).
Proof.
pose proof g_ms as (M1 & M2 & _).
pose proof (gf_facts im_segs _ ly S _ (w64 mb) MSn LY WF PL LN ltac:(zl) M2 GOK) as X. rewrite g_umb in X. exact X.
Qed.
Lemma g_apart : Forall (zdisjoint (mb, MSn)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Proof.
pose proof g_ms as (M1 & M2 & _).
pose proof (gf_apart im_segs _ ly S _ (w64 mb) MSn LY WF PL LN ltac:(zl) M2 GOK) as X. rewrite g_umb in X. exact X.
Qed.
Lemma g_map_st : forall e, In e (static_extents ly) -> zdisjoint (mb, MSn) e.
Proof. intros e He. apply (proj1 (Forall_forall _ _) g_apart). apply in_app_iff. left. exact He. Qed.
Lemma g_map_sec : forall e, In e (sec_extents ly S) -> zdisjoint (mb, MSn) e.
Proof. intros e He. apply (proj1 (Forall_forall _ _) g_apart). rewrite !in_app_iff. right; right. exact He. Qed.
Lemma g_stat : forall i j e e', (i < j)%nat -> nth_error (static_extents ly) i = Some e ->
  nth_error (static_extents ly) j = Some e' -> zdisjoint e e'.
Proof.
intros i j e e' Hij He He'. apply (pw_ij zdisjoint (static_extents ly) i (j - i - 1) e e' (lo_disj ly LY) He).
replace (i + Datatypes.S (j - i - 1))%nat with j by zl. exact He'.
Qed.
Local Ltac gdisj i j := first [ exact (g_stat i j _ _ ltac:(zl) eq_refl eq_refl)
  | apply zdj_sym; exact (g_stat i j _ _ ltac:(zl) eq_refl eq_refl) ].
Lemma g_owned_app : forall e, In e (owned_extents ly) -> in_app (fst e) (snd e).
Proof. intros e He. exact (proj1 (Forall_forall _ _) (lo_app ly LY) e He). Qed.
Lemma g_SM : SMn = shadow_addr mb.
Proof. unfold ImgBaseAGS.SMv, shadow_addr. rewrite SHB_EQ. reflexivity. Qed.
Lemma g_res : idx <= res <= kPtrArrayEntriesPerCommit /\ res mod kPtrArrayEntriesPerCommit = 0.
Proof.
pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as WR. pose proof (wsc_reserved_al _ (wfc_secondary _ _ _ _ _ WF)) as [_ WA].
split; [unfold kPtrArrayEntriesPerCommit in *; zl | exact WA].
Qed.
Lemma g_msh_band : forall a, SMn <= a < SMn + MSn / 8 -> in_band_rw a.
Proof.
intros a Ha. rewrite g_SM in Ha. pose proof g_facts as (MA & MI & _). pose proof g_ms as (_ & M2 & _).
assert (M8 : mb mod 8 = 0) by (unfold page_aligned in MA; apply Z.mod_divide in MA as [q Hq]; [|zl]; rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by zl; apply Z_mod_mult).
apply Z.mod_divide in M8 as [q Hq]; [|zl].
replace a with (shadow_addr (mb + 8 * (a - shadow_addr mb))).
- apply (shadow_addr_in_band mb MSn). exact MI.
  pose proof (Z.div_mod MSn 8 ltac:(zl)). pose proof (Z.mod_pos_bound MSn 8 ltac:(zl)). zl.
- unfold shadow_addr in *. rewrite Hq in *. replace (q * 8 + 8 * (a - (SHADOW_OFF + q * 8 / 8))) with ((q + (a - (SHADOW_OFF + q * 8 / 8))) * 8) by zl.
  rewrite !Z.div_mul by zl. zl.
Qed.

(* ---- the grant arm's write set: what the walk writes outside the stack window ---- *)
Definition gXC (a : Z) : Prop :=
  ImgBaseAGS.WINT ly a \/ ImgBaseAGS.WINI regs0 n a \/ (QSn <= a < QSn + 8) \/ (mb <= a < mb + MSn) \/
  (SMn <= a < SMn + MSn / 8) \/ ims_dzone ly a \/ (grow = true /\ AGif4.QRz ly res a).

Lemma g_RX : forall m, rd_ext (aview im_segs (w_H W) m) (aview im_segs (w_H Wz) m).
Proof.
intros m. apply aview_ext; [apply w_Hoff|]. intros x Hx. destruct (w_H W x) eqn:E; [reflexivity|].
rewrite (MON x E) in Hx. discriminate Hx.
Qed.

Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ gXC a -> ~ (sp0 - ImgBaseAGS.AFSTACK <= a < sp0) ->
  forall v, rd0 a = Some v -> rd' a = Some v.
Proof.
intros a Ra NX NS v Hv.
assert (Hm : mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ apply MEQF; rewrite w64_unsigned by exact Ra.
  - intros Hw. unfold ImgBaseAGS.WIN, ImgBaseAGS.WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
    + exact (NS Hw).
    + apply NX. left. exact Hw.
    + apply NX. right; left. exact Hw.
    + apply NX. right; right; left. exact Hw.
    + apply NX. do 3 right; left. exact Hw.
    + apply NX. do 4 right; left. exact Hw.
  - intros [Hg Hq]. apply NX. do 6 right. exact (conj Hg Hq).
  - intros [Hs|Hd]; [apply NS; unfold ImgBaseAGS.DEP_STK, ImgBaseAGS.AFSTACK in *; zl | apply NX; do 5 right; left; exact Hd]. }
rewrite (aview_same_g im_segs (w_H Wz) mem0 mem' a Hm). exact (g_RX mem0 a v Hv).
Qed.
Lemma AGREED : forall a, 0 <= a < 2 ^ 64 -> ims_dzone ly a -> rd' a = rdD a.
Proof. intros a Ra Hd. apply aview_same_g. apply EQD. rewrite w64_unsigned by exact Ra. exact Hd. Qed.
Lemma AGX : forall a, aowned B ly S a -> ~ gXC a -> forall v, rd0 a = Some v -> rd' a = Some v.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok_cf im_segs B ly S Hp W mem0 md0 a HAR Ho) as Ra. pose proof alloc_ceiling_val as CV.
apply AGREE0; [unfold alloc_ceiling in *; zl | exact Hx |].
intros Hs. refine (AR_stack_law_ok_cf im_segs B ly S Hp W mem0 md0 a HAR _ Ho). unfold ImgBaseAGS.AFSTACK in *. zl.
Qed.

(* ---- where the write set is ---- *)
Lemma g_wint : forall a, ImgBaseAGS.WINT ly a -> ly_T ly + 2768 <= a < ly_T ly + 3169.
Proof. intros a Ha. unfold ImgBaseAGS.WINT, t_unwinding in Ha. zl. Qed.
Lemma g_wini : forall a, ImgBaseAGS.WINI regs0 n a -> as_inst B + 112 <= a < as_inst B + 728.
Proof.
intros a Ha. pose proof cf_malloc_max_bound. pose proof (bsl_bounds regs0 n ltac:(zl)) as Bs. rewrite Hinst in Bs.
unfold ImgBaseAGS.WINI in Ha. rewrite Hinst in Ha.
unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. zl.
Qed.
Lemma g_qs : forall a, QSn <= a < QSn + 8 -> ly_Q ly <= a < ly_Q ly + kPtrArrayResv.
Proof. intros a Ha. pose proof g_res as [R1 _]. unfold ImgBaseAGS.QSv, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl. Qed.
Lemma g_qr : forall a, AGif4.QRz ly res a -> ly_Q ly <= a < ly_Q ly + kPtrArrayResv.
Proof. intros a Ha. pose proof g_res as [R1 _]. unfold AGif4.QRz in Ha. zl. Qed.
Lemma g_inst_img : forall a, as_inst B <= a < as_inst B + 3632 -> in_zr a (ly_img ly).
Proof. intros a Ha. apply (sn_area_img Hp ly S W mem0 md0 HAR (as_inst B, 3632)); [unfold asyms_areas; cbn; tauto | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma g_img_range : forall a, in_zr a (ly_img ly) -> kImgLo <= a < kImgEnd.
Proof. intros a Ha. pose proof (lo_img ly LY) as (J0 & J1 & J2 & _). unfold in_zr in Ha. zl. Qed.

(* An address outside the thread object's written tail, the instance's written words, the pointer array, the map, the
   shadow band and the depot's write zone is outside the write set. *)
Lemma gX_out : forall a, ~ (ly_T ly + 2768 <= a < ly_T ly + 3169) -> ~ (as_inst B + 112 <= a < as_inst B + 728) ->
  ~ (ly_Q ly <= a < ly_Q ly + kPtrArrayResv) -> ~ (mb <= a < mb + MSn) -> ~ in_band_rw a -> ~ ims_dzone ly a -> ~ gXC a.
Proof.
intros a N1 N2 N3 N4 N5 N6 X. unfold gXC in X. destruct X as [X|[X|[X|[X|[X|[X|[_ X]]]]]]].
- exact (N1 (g_wint a X)).
- exact (N2 (g_wini a X)).
- exact (N3 (g_qs a X)).
- exact (N4 X).
- exact (N5 (g_msh_band a X)).
- exact (N6 X).
- exact (N3 (g_qr a X)).
Qed.
(* The depot's write zone at an address apart from the two blocks and outside the image, or inside the image in one of
   the excluded symbol areas. *)
Lemma g_ndz : forall a, ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) -> ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) ->
  (~ in_zr a (ly_img ly) \/ (as_inst B <= a < as_inst B + 3632) \/ (as_ialloc_lo B <= a < as_ialloc_hi B) \/
   (as_ialloc_flag B <= a < as_ialloc_flag B + 2)) -> ~ ims_dzone ly a.
Proof.
intros a N1 N2 N3 Hd. destruct (DZ_LOC ly a LY IMG TSD Hd) as [X|[X|(X1 & X2 & X3 & X4)]]; [exact (N1 X) | exact (N2 X) |].
destruct N3 as [N|[N|[N|N]]]; contradiction.
Qed.
(* An address of an extent of the static list (by index) apart from the thread object, the pointer array, the two
   blocks and the image, of the application range. *)
Lemma gX_ext : forall i e a, nth_error (static_extents ly) i = Some e -> (i = 0 \/ i = 3 \/ i = 6 \/ i = 7)%nat ->
  in_zr a e -> ~ gXC a.
Proof.
intros i e a He Hi Ha.
assert (D : forall j e', nth_error (static_extents ly) j = Some e' -> (j = 1 \/ j = 2 \/ j = 4 \/ j = 5 \/ j = 9)%nat -> zdisjoint e e').
{ intros j e' He' Hj. destruct (Nat.lt_ge_cases i j) as [Lt|Ge].
  - exact (g_stat i j e e' Lt He He').
  - apply zdj_sym. assert (j <> i) by (intros ->; zl). exact (g_stat j i e' e ltac:(zl) He' He). }
pose proof (D 1%nat _ eq_refl ltac:(zl)) as DQ. pose proof (D 2%nat _ eq_refl ltac:(zl)) as DT.
pose proof (D 4%nat _ eq_refl ltac:(zl)) as DNB. pose proof (D 5%nat _ eq_refl ltac:(zl)) as DSB.
pose proof (D 9%nat _ eq_refl ltac:(zl)) as DI.
assert (EO : In e (owned_extents ly)).
{ unfold static_extents in He. rewrite nth_error_app1 in He by (cbn; zl). exact (nth_error_In _ _ He). }
pose proof (g_owned_app e EO) as EA.
pose proof (g_map_st e ltac:(exact (nth_error_In _ _ He))) as DM.
pose proof (g_inst_img (as_inst B)) as II.
unfold zdisjoint, in_zr in *. cbn [fst snd] in *.
apply gX_out.
- unfold kThreadObjSize in DT. zl.
- intros X. specialize (II ltac:(zl)). pose proof (lo_img ly LY) as (J0 & J1 & J2 & _). pose proof (g_inst_img a ltac:(zl)) as IA.
  unfold in_zr in IA. zl.
- zl.
- zl.
- exact (app_not_band (fst e) (snd e) a EA Ha).
- apply g_ndz; [unfold kNodesBlockSize in *; zl | unfold kStoreBlockSize in *; zl | left; unfold in_zr; zl].
Qed.
Lemma gX_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ gXC a.
Proof. intros a Ha. apply (gX_ext 0 (ly_prim ly, kPrimResvSize)); [reflexivity | zl | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma gX_F : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> ~ gXC a.
Proof. intros a Ha. apply (gX_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | zl | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma gX_C : forall a, ly_C ly <= a < ly_C ly + 256 -> ~ gXC a.
Proof. intros a Ha. apply (gX_ext 6 (ly_C ly, 256)); [reflexivity | zl | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma gX_D : forall a, ly_D ly <= a < ly_D ly + 4096 -> ~ gXC a.
Proof. intros a Ha. apply (gX_ext 7 (ly_D ly, 4096)); [reflexivity | zl | unfold in_zr; cbn [fst snd]; zl]. Qed.
Lemma gX_sec : forall e a, In e (sec_extents ly S) -> in_zr a e -> ~ gXC a.
Proof.
intros e a He Ha. destruct PL as [PF PD]. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & EA & _).
assert (D : forall e', In e' (static_extents ly) -> zdisjoint e e')
  by (intros e' He'; exact (cfb_pairwise_app zdisjoint (sec_extents ly S) (static_extents ly) e e' PD He He')).
pose proof (D (ly_Q ly, kPtrArrayResv) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DQ.
pose proof (D (ly_T ly, kThreadObjSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DT.
pose proof (D (ly_NB ly, kNodesBlockSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DNB.
pose proof (D (ly_SB ly, kStoreBlockSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DSB.
pose proof (D (ly_img ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as DI.
pose proof (g_map_sec e He) as DM.
pose proof (g_inst_img (as_inst B)) as II.
unfold zdisjoint, in_zr in *. cbn [fst snd] in *.
apply gX_out.
- unfold kThreadObjSize in DT. zl.
- intros X. pose proof (g_inst_img a ltac:(zl)) as IA. unfold in_zr in IA. zl.
- zl.
- zl.
- exact (app_not_band (fst e) (snd e) a EA Ha).
- apply g_ndz; [unfold kNodesBlockSize in *; zl | unfold kStoreBlockSize in *; zl | left; unfold in_zr; zl].
Qed.
Lemma gX_T : forall a, ly_T ly <= a < ly_T ly + 2768 -> ~ gXC a.
Proof.
intros a Ha.
assert (D : forall j e', nth_error (static_extents ly) j = Some e' -> (j = 1 \/ j = 4 \/ j = 5 \/ j = 9)%nat ->
  zdisjoint (ly_T ly, kThreadObjSize) e').
{ intros j e' He' Hj. destruct (Nat.lt_ge_cases 2 j) as [Lt|Ge].
  - exact (g_stat 2 j _ e' Lt eq_refl He').
  - apply zdj_sym. assert (j <> 2%nat) by (intros ->; zl). exact (g_stat j 2 e' _ ltac:(zl) He' eq_refl). }
pose proof (D 1%nat _ eq_refl ltac:(zl)) as DQ. pose proof (D 4%nat _ eq_refl ltac:(zl)) as DNB.
pose proof (D 5%nat _ eq_refl ltac:(zl)) as DSB. pose proof (D 9%nat _ eq_refl ltac:(zl)) as DI.
pose proof (g_map_st (ly_T ly, kThreadObjSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DM.
pose proof (g_owned_app (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as EA.
unfold zdisjoint, in_zr in *. cbn [fst snd] in *.
apply gX_out.
- zl.
- intros X. pose proof (g_inst_img a ltac:(zl)) as IA. unfold in_zr in IA. unfold kThreadObjSize in *. zl.
- unfold kThreadObjSize in *. zl.
- unfold kThreadObjSize in *. zl.
- apply (app_not_band (ly_T ly) kThreadObjSize a EA). unfold kThreadObjSize. zl.
- apply g_ndz; [unfold kNodesBlockSize, kThreadObjSize in *; zl | unfold kStoreBlockSize, kThreadObjSize in *; zl | left; unfold in_zr, kThreadObjSize in *; zl].
Qed.
(* The image bytes of the instance object outside the words the walk writes, the internal allocator and its flag. *)
Lemma gX_imgx : forall a, in_zr a (ly_img ly) -> ~ (as_inst B + 112 <= a < as_inst B + 728) ->
  (as_inst B <= a < as_inst B + 3632) \/ (as_ialloc_lo B <= a < as_ialloc_hi B) \/ (as_ialloc_flag B <= a < as_ialloc_flag B + 2) ->
  ~ gXC a.
Proof.
intros a Ha N2 Hloc.
pose proof (g_stat 1 9 _ _ ltac:(zl) eq_refl eq_refl) as DQ. pose proof (g_stat 2 9 _ _ ltac:(zl) eq_refl eq_refl) as DT.
pose proof (g_stat 4 9 _ _ ltac:(zl) eq_refl eq_refl) as DNB. pose proof (g_stat 5 9 _ _ ltac:(zl) eq_refl eq_refl) as DSB.
pose proof (g_map_st (ly_img ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as DM.
pose proof (g_img_range a Ha) as IR.
cbn in DQ, DT, DNB, DSB. unfold zdisjoint, in_zr in *. cbn [fst snd] in *.
apply gX_out.
- unfold kThreadObjSize in *. zl.
- exact N2.
- zl.
- zl.
- intros HB. unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kHighShadowBeg in *. zl.
- apply g_ndz; [unfold kNodesBlockSize in *; zl | unfold kStoreBlockSize in *; zl | right; exact Hloc].
Qed.
Lemma gX_Q : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> ~ (QSn <= a < QSn + 8) -> ~ (grow = true /\ AGif4.QRz ly res a) ->
  ~ gXC a.
Proof.
intros a Ha N1 N2 X.
pose proof (g_stat 1 2 _ _ ltac:(zl) eq_refl eq_refl) as DT. pose proof (g_stat 1 4 _ _ ltac:(zl) eq_refl eq_refl) as DNB.
pose proof (g_stat 1 5 _ _ ltac:(zl) eq_refl eq_refl) as DSB. pose proof (g_stat 1 9 _ _ ltac:(zl) eq_refl eq_refl) as DI.
pose proof (g_map_st (ly_Q ly, kPtrArrayResv) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DM.
pose proof (g_owned_app (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as EA.
cbn in DT, DNB, DSB, DI. unfold zdisjoint in *. cbn [fst snd] in *.
unfold gXC in X. destruct X as [X|[X|[X|[X|[X|[X|X]]]]]].
- pose proof (g_wint a X). unfold kThreadObjSize in *. zl.
- pose proof (g_wini a X). pose proof (g_inst_img a ltac:(zl)) as IA. unfold in_zr in IA. zl.
- exact (N1 X).
- zl.
- exact (app_not_band (ly_Q ly) kPtrArrayResv a EA Ha (g_msh_band a X)).
- refine (g_ndz a _ _ _ X); [unfold kNodesBlockSize in *; zl | unfold kStoreBlockSize in *; zl | left; unfold in_zr; zl].
- exact (N2 X).
Qed.
Lemma gX_band : forall a, in_band_rw a -> ~ (SMn <= a < SMn + MSn / 8) -> ~ gXC a.
Proof.
intros a Ha N X.
pose proof (g_owned_app (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as EQ.
pose proof (g_owned_app (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as ET.
pose proof (g_owned_app (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as ENB.
pose proof (g_owned_app (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as ESB.
pose proof g_facts as (_ & MI & _).
cbn [fst snd] in *.
unfold gXC in X. destruct X as [X|[X|[X|[X|[X|[X|[_ X]]]]]]].
- apply (app_not_band _ _ a ET); [pose proof (g_wint a X); unfold kThreadObjSize; zl | exact Ha].
- pose proof (g_wini a X). pose proof (g_img_range a (g_inst_img a ltac:(zl))) as IR.
  unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kHighShadowBeg in *. zl.
- apply (app_not_band _ _ a EQ); [exact (g_qs a X) | exact Ha].
- exact (app_not_band _ _ a MI X Ha).
- exact (N X).
- destruct (DZ_LOC ly a LY IMG TSD X) as [Y|[Y|(Y & _)]].
  + exact (app_not_band _ _ a ENB Y Ha).
  + exact (app_not_band _ _ a ESB Y Ha).
  + pose proof (g_img_range a Y) as IR. unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kHighShadowBeg in *. zl.
- exact (app_not_band _ _ a EQ (g_qr a X) Ha).
Qed.


(* ---- the final state and the grown layout ---- *)
Lemma g_SF : (forall c, reg SF c = reg S c) /\ st_cache_inited SF = st_cache_inited S /\ (forall c, cache SF c = cache S c) /\
  frames SF = frames S /\ st_qthread SF = st_qthread S /\ st_qglobal SF = st_qglobal S /\ st_fs SF = st_fs S /\
  st_internal_inited SF = st_internal_inited S /\ st_sec_arr SF = st_sec_arr S ++ [rS0] /\
  st_sec_reserved SF = (if grow then res + kPtrArrayEntriesPerCommit else res) /\ st_depot SF = st_depot (depot_after z tr S) /\
  st_chunks SF = st_chunks S ++ [KSc] /\ st_secs SF = st_secs S ++ [mkSec MSn (ImgBaseAGS.NDv n) true] /\
  st_regions SF = st_regions S.
Proof.
unfold AGif4.SFSz, ImgBaseAGS.sfinal, ImgBaseAGS.resF, ImgBaseAGS.depF, reg, cache, frames. cbn.
repeat split; try reflexivity. unfold depot_after. destruct (z =? 0); reflexivity.
Qed.
Lemma g_le : layout_le (length (st_secs S)) ly lyF.
Proof. unfold AGif4.lyFz, ImgBaseAGS.rS. apply set_ly_sec_le. Qed.
Lemma g_lysec : ly_sec lyF rS0 = mb.
Proof. unfold AGif4.lyFz, set_ly_sec. cbn. rewrite PeanoNat.Nat.eqb_refl. reflexivity. Qed.
Lemma g_lyok : layout_ok lyF.
Proof. apply set_ly_sec_ok. exact LY. Qed.
Lemma g_static : static_extents lyF = static_extents ly /\ vis0_zones lyF = vis0_zones ly /\ core_extents lyF = core_extents ly /\
  owned_extents lyF = owned_extents ly.
Proof. unfold AGif4.lyFz, set_ly_sec, static_extents, vis0_zones, core_extents, owned_extents. cbn. repeat split; reflexivity. Qed.
Lemma g_lyeqs : ly_prim lyF = ly_prim ly /\ ly_space lyF = ly_space ly /\ ly_Q lyF = ly_Q ly /\ ly_T lyF = ly_T ly /\
  ly_C lyF = ly_C ly /\ ly_F lyF = ly_F ly /\ ly_NB lyF = ly_NB ly /\ ly_SB lyF = ly_SB ly /\ ly_top lyF = ly_top ly /\
  ly_stk_lo lyF = ly_stk_lo ly /\ ly_stk_hi lyF = ly_stk_hi ly /\ ly_tsd lyF = ly_tsd ly /\ ly_tr0 lyF = ly_tr0 ly /\
  ly_extra lyF = ly_extra ly /\ ly_D lyF = ly_D ly /\ ly_vis0 lyF = ly_vis0 ly /\ ly_img lyF = ly_img ly.
Proof. unfold AGif4.lyFz, set_ly_sec. cbn. repeat split; reflexivity. Qed.
Lemma g_KB : ck_beg KSc = PSec rS0 kPage. Proof. reflexivity. Qed.
Lemma g_KQ : ck_req KSc = n. Proof. reflexivity. Qed.
Lemma g_KN : ck_n KSc = n.
Proof. pose proof g_sizes as (_ & _ & RS & _). unfold ck_n. rewrite g_KQ. exact RS. Qed.
Lemma g_KST : ck_state KSc = CAllocated. Proof. reflexivity. Qed.
Lemma g_KR : ck_rz KSc = 2048.
Proof. pose proof g_sizes as (_ & _ & _ & RZ & _). unfold ck_rz. rewrite g_KQ. exact RZ. Qed.
Lemma g_SEF : sec_extents lyF SF = sec_extents ly S ++ [(mb, MSn)].
Proof.
pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof g_sizes as (ND & MS & RS & RZ & FP).
unfold sec_extents at 1. rewrite Rck, flat_map_app. pose proof (sec_extents_le_cf ly lyF S _ _ _ _ g_le WF) as SE.
unfold sec_extents in SE at 1. rewrite SE. cbn [flat_map]. rewrite g_KB. cbv beta iota. rewrite g_KQ, MS, g_lysec, app_nil_r. reflexivity.
Qed.
Lemma g_aeval : forall e, asec_lt (length (st_secs S)) e -> aeval B lyF e = aeval B ly e.
Proof. intros e He. exact (aeval_le B ly lyF _ g_le e He). Qed.
Lemma g_rS_not_in_arr : ~ In rS0 (st_sec_arr S).
Proof.
intros Hin. pose proof (proj1 (wsc_arr_live _ (wfc_secondary _ _ _ _ _ WF) rS0) Hin) as (sm & Hsm & _).
assert (LT : (rS0 < length (st_secs S))%nat) by (apply nth_error_Some; rewrite Hsm; discriminate).
unfold ImgBaseAGS.rS in LT. zl.
Qed.

(* ---- generic list facts (AGjy.v:386-446's, image-free) ---- *)
Lemma val_mem_cell_g : forall lyx (Hh : word -> bool) m c e, c_val c = AV e ->
  val_mem im_segs (mrestrict Hh m) (aeval B lyx (c_at c)) (c_w c) (aeval B lyx e) -> cell_holds B lyx (aview im_segs Hh m) c.
Proof. intros lyx Hh m c e Ev Hv. unfold cell_holds. rewrite Ev. intros k Hk. exact (vm_aview_g _ _ _ _ _ _ k Hv Hk). Qed.
Local Ltac vmc e := apply (val_mem_cell_g _ _ _ _ e); [reflexivity|].
Lemma flat_map_ext_in_g {X Y : Type} : forall (f g : X -> list Y) l, (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
intros f g l. induction l as [|a t IH]; intros H; [reflexivity|]. cbn [flat_map].
rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros b Hb. apply H. right. exact Hb.
Qed.
Lemma cell_ext1_g : forall lyx (rd1 rd2 : reader) c,
  (forall k v, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd1 (aeval B lyx (c_at c) + k) = Some v ->
     rd2 (aeval B lyx (c_at c) + k) = Some v) ->
  cell_holds B lyx rd1 c -> cell_holds B lyx rd2 c.
Proof.
intros lyx rd1 rd2 c Hx Hc. unfold cell_holds in *. destruct (c_val c) as [e|mk v].
- intros k Hk. apply Hx; [zl | exact (Hc k Hk)].
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm].
  rewrite <- (Z.add_0_r (aeval B lyx (c_at c))). apply Hx; [zl|]. rewrite Z.add_0_r. exact Hb.
Qed.
Lemma in_combine_seq_g : forall {X : Type} (l : list X) s i x, In (i, x) (combine (seq s (length l)) l) ->
  nth_error l (i - s) = Some x /\ (s <= i < s + length l)%nat.
Proof.
intros X l. induction l as [|y t IH]; intros s i x H; [destruct H|]. cbn [length seq combine] in H.
destruct H as [H|H].
- injection H as <- <-. rewrite Nat.sub_diag. cbn. split; [reflexivity | zl].
- destruct (IH _ _ _ H) as [E R]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) by zl. cbn [nth_error length]. split; [exact E | zl].
Qed.
Lemma combine_seq_in_g : forall {X : Type} (l : list X) s i x, nth_error l (i - s) = Some x -> (s <= i)%nat ->
  In (i, x) (combine (seq s (length l)) l).
Proof.
intros X l. induction l as [|y t IH]; intros s i x E Hs; [destruct (i - s)%nat; discriminate E|]. cbn [length seq combine].
destruct (Nat.eq_dec i s) as [->|Hne].
- rewrite Nat.sub_diag in E. cbn in E. injection E as <-. left. reflexivity.
- right. apply IH; [|zl]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) in E by zl. cbn in E. exact E.
Qed.
Lemma index_of_app_old_g : forall (l : list nat) (x r : nat) s, In r l -> index_of (l ++ [x]) r s = index_of l r s.
Proof.
induction l as [|y t IH]; intros x r s Hr; [destruct Hr|]. cbn [index_of app]. destruct (Nat.eqb y r) eqn:E; [reflexivity|].
destruct Hr as [->|Hr]; [rewrite Nat.eqb_refl in E; discriminate E|]. exact (IH x r (Datatypes.S s) Hr).
Qed.
Lemma index_of_app_new_g : forall (l : list nat) (x : nat) s, ~ In x l -> index_of (l ++ [x]) x s = Some (s + length l)%nat.
Proof.
induction l as [|y t IH]; intros x s Hx; cbn [index_of app length].
- rewrite Nat.eqb_refl, Nat.add_0_r. reflexivity.
- destruct (Nat.eqb_spec y x) as [E|E]; [exfalso; apply Hx; left; exact E|].
  rewrite (IH x (Datatypes.S s) ltac:(intros H; apply Hx; right; exact H)). f_equal. zl.
Qed.
Lemma find_chunk_at_app1_g : forall lyx l1 l2 g k, find_chunk_at B lyx l1 g = Some k -> find_chunk_at B lyx (l1 ++ l2) g = Some k.
Proof.
intros lyx l1 l2 g k. induction l1 as [|k1 t IH]; intros H; [discriminate H|]. cbn [find_chunk_at app] in *.
destruct ((ck_base B lyx k1 <=? g) && (g <? ck_base B lyx k1 + ck_extent k1)); [exact H | exact (IH H)].
Qed.
Lemma find_chunk_at_app2_g : forall lyx l1 l2 g, find_chunk_at B lyx l1 g = None ->
  find_chunk_at B lyx (l1 ++ l2) g = find_chunk_at B lyx l2 g.
Proof.
intros lyx l1 l2 g. induction l1 as [|k1 t IH]; intros H; [reflexivity|]. cbn [find_chunk_at app] in *.
destruct ((ck_base B lyx k1 <=? g) && (g <? ck_base B lyx k1 + ck_extent k1)); [discriminate H | exact (IH H)].
Qed.

(* ---- the model's old cells outside the write set keep their values ---- *)
Definition g_nx (c : acell) : Prop := forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ gXC (aeval B ly (c_at c) + k).
Lemma g_rng : forall c (Zp : Z -> Prop), (forall a, Zp a -> ~ gXC a) ->
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> Zp (aeval B ly (c_at c) + k)) -> g_nx c.
Proof. intros c Zp HZ HR k Hk. exact (HZ _ (HR k Hk)). Qed.
Local Ltac grng Lm := apply (g_rng _ _ Lm); intros kk Hkk; cbn [c_at c_w aeval aoff z1 z2 z4 z8 c1 c2 c4 c8 fst snd] in *;
  cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ] in Hkk.
Lemma g_keep : forall l, incl l (acells_cf B ly S) -> Forall g_nx l -> Forall (cell_holds B ly rd') l.
Proof.
intros l INC NX. pose proof (acells_owned_cf B ly S Hp _ M) as CO. apply Forall_forall. intros c Hc.
apply (cell_ext1_g ly rd0); [| exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) c (INC c Hc))].
intros k v Hk Hv. apply AGX; [exact (proj1 (Forall_forall _ _) CO c (INC c Hc) k Hk) | exact (proj1 (Forall_forall _ _) NX c Hc k Hk) | exact Hv].
Qed.

Lemma g_nx_batches : forall bl, incl bl (all_batches S) -> Forall g_nx (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
assert (LOC : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> ~ gXC a).
{ pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; zl)) as CL.
  set (x := b_self b - region_off kBatchClass).
  assert (INB : In x (batch_offs S kBatchClass))
    by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
  pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
  pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
  pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; zl)) as MB.
  pose proof (region_in_prim ly kBatchClass LY ltac:(unfold kBatchClass; zl)) as (R1 & R2 & R3 & R4 & R5).
  assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
  assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; zl).
  apply Z.mod_divide in X2 as [q1 Hq1]; [|zl]. apply Z.mod_divide in AA as [q2 Hq2]; [|zl].
  assert (XA : x + 8192 <= rg_alloc_user (reg S kBatchClass)) by zl.
  intros a Ha. apply gX_prim. unfold kBatchBytes, kFreeArrayOffset in *. zl. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split]]].
1-3: grng LOC; unfold batch_exp in *; cbn [aeval aoff] in *; unfold kBatchBytes; zl.
- apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ WF)) b (Hincl b (or_introl eq_refl))) as [L1 L2].
  grng LOC. unfold batch_exp in *. cbn [aeval aoff] in *. unfold kBatchBytes, kBatchSlots in *. zl.
- apply IH. intros y Hy. apply Hincl. right. exact Hy.
Qed.

Lemma g_cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf SF) (zseq 1 31)).
Proof.
pose proof g_SF as (Rreg & _). pose proof (lo_space_in ly LY) as [S1 S2].
replace (flat_map (region_cells_cf SF) (zseq 1 31)) with (flat_map (region_cells_cf S) (zseq 1 31))
  by (apply flat_map_ext; intros c; unfold region_cells_cf, region_cells; rewrite Rreg; reflexivity).
apply g_keep; [intros x Hx; unfold acells_cf; apply in_app_iff; left; exact Hx|].
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. eapply incl_Forall; [apply region_cells_cf_incl|].
unfold region_cells. repeat (apply Forall_cons; [grng gX_prim; unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *; zl|]). apply Forall_nil.
Qed.
Lemma g_cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells SF) (zseq 1 31)).
Proof.
pose proof g_SF as (_ & Rinit & Rcache & _).
replace (flat_map (cache_cells SF) (zseq 1 31)) with (flat_map (cache_cells S) (zseq 1 31))
  by (apply flat_map_ext; intros c; unfold cache_cells; rewrite Rinit, (Rcache c); reflexivity).
apply g_keep; [intros x Hx; unfold acells_cf; apply in_app_iff; right; apply in_app_iff; left; exact Hx|].
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
pose proof (wfc_classes _ _ _ _ _ WF c ltac:(zl)) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC.
assert (MC : max_cached c <= 16) by (unfold max_cached; pose proof (Z.le_min_l 8 (1024 / class_size c)); zl).
unfold cache_cells. destruct (st_cache_inited S).
- destruct WC as [PM PL'].
  repeat (apply Forall_cons; [grng gX_T; unfold t_cache; zl|]).
  apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i v] & <- & Hiv). apply in_combine_l in Hiv. apply in_seq in Hiv.
  grng gX_T. unfold t_cache. zl.
- repeat (apply Forall_cons; [grng gX_T; unfold t_cache; zl|]). apply Forall_nil.
Qed.
Lemma g_cells_chunks_old : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S)).
Proof.
apply g_keep; [intros x Hx; unfold acells_cf; do 2 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(zl)) as (Q1 & Q2 & Q3).
assert (LOC : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ gXC a).
{ intros a Ha. destruct (extent_zone_cf B ly S Hp _ k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
  - apply gX_prim. zl.
  - apply (gX_sec (m, len) a Hin). unfold in_zr, kPage in *. cbn [fst snd]. zl. }
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; zl. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; zl. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
- repeat (apply Forall_cons; [apply (g_rng _ _ LOC); intros kk Hkk; cbn [c_at c_w z1 z2 z4 c1 c2 c4] in *;
    rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ] in Hkk; zl|]). apply Forall_nil.
- destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
  assert (32 <= ck_rz k) by (apply Z.mod_divide in G6 as [q Hq]; [|zl]; zl).
  repeat (apply Forall_cons; [apply (g_rng _ _ LOC); intros kk Hkk; cbn [c_at c_w z8 c8] in *;
    rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ] in Hkk; zl|]). apply Forall_nil.
Qed.
Lemma g_cells_quar : Forall (cell_holds B ly rd') (quar_cells SF).
Proof.
pose proof g_SF as (_ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells SF) with (quar_cells S) by (unfold quar_cells; rewrite Rqt, Rqg; reflexivity).
apply g_keep; [intros x Hx; unfold acells_cf; do 4 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
assert (LI : forall a, as_inst B + 728 <= a < as_inst B + 3632 -> ~ gXC a).
{ intros a Ha. apply gX_imgx; [apply g_inst_img; zl | zl | left; zl]. }
assert (LT : forall a, ly_T ly <= a < ly_T ly + 2768 -> ~ gXC a) by exact gX_T.
unfold quar_cells, qc_cells.
apply Forall_cons; [grng LI; unfold o_q_cmutex; zl|]. apply Forall_cons; [grng LI; unfold o_q_rmutex; zl|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [grng LT; unfold t_qc; zl|]).
  apply g_nx_batches. intros b Hb. unfold all_batches. apply in_app_iff. left. exact Hb.
- do 4 (apply Forall_cons; [grng LI; unfold o_q_size; zl|]).
  apply g_nx_batches. intros b Hb. unfold all_batches. apply in_app_iff. right. exact Hb.
Qed.
Lemma g_cells_fs : Forall (cell_holds B ly rd') (fs_cells SF).
Proof.
pose proof g_SF as (_ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells SF) with (fs_cells S) by (unfold fs_cells; rewrite Rfs; reflexivity).
apply g_keep; [intros x Hx; unfold acells_cf; do 5 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
unfold fs_cells. apply Forall_cons; [grng gX_F; unfold kFakeStackSize; zl|]. apply Forall_cons; [grng gX_F; unfold kFakeStackSize; zl|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
grng gX_F. unfold kFakeStackSize. zl.
Qed.
Lemma g_cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B SF).
Proof.
pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B SF) with (ialloc_cells B S) by (unfold ialloc_cells; rewrite Rii; reflexivity).
apply g_keep; [intros x Hx; unfold acells_cf; do 7 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ M)) as [I1 I2].
assert (LA : forall a, as_ialloc_lo B <= a < as_ialloc_hi B -> ~ gXC a).
{ intros a Ha. apply gX_imgx; [| | right; left; exact Ha].
  - apply (sn_area_img Hp ly S W mem0 md0 HAR (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [unfold asyms_areas; cbn; tauto | unfold in_zr; cbn [fst snd]; zl].
  - intros X. pose proof (pw_ij zdisjoint (firstn 6 (asyms_areas B)) 0 2 _ _ AREAS_DISJ eq_refl eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. zl. }
assert (LF : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> ~ gXC a).
{ intros a Ha. apply gX_imgx; [| | right; right; exact Ha].
  - apply (sn_area_img Hp ly S W mem0 md0 HAR (as_ialloc_flag B, 2)); [unfold asyms_areas; cbn; tauto | unfold in_zr; cbn [fst snd]; zl].
  - intros X. pose proof (pw_ij zdisjoint (firstn 6 (asyms_areas B)) 0 3 _ _ AREAS_DISJ eq_refl eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. zl. }
unfold ialloc_cells.
apply Forall_cons; [grng LF; zl|]. apply Forall_cons; [grng LF; zl|].
apply Forall_cons; [grng LA; zl|]. apply Forall_cons; [grng LA; zl|]. apply Forall_nil.
Qed.

(* ---- the machine post's written values ---- *)
Let Vunw := AGif4.sf_Vunw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vres := AGif4.sf_Vres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vnch := AGif4.sf_Vnch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vmtx := AGif4.sf_Vmtx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vpad := AGif4.sf_Vpad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vslot := AGif4.sf_Vslot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vh0 := AGif4.sf_Vh0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vh8 := AGif4.sf_Vh8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vh16 := AGif4.sf_Vh16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vh24 := AGif4.sf_Vh24 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vmag := AGif4.sf_Vmag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vbk := AGif4.sf_Vbk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vst := AGif4.sf_Vst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vb1 := AGif4.sf_Vb1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vb2 := AGif4.sf_Vb2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vn := AGif4.sf_Vn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Lemma vm_eq : forall m a a' (w : nat) v v', a = a' -> v = v' -> val_mem im_segs m a' w v' -> val_mem im_segs m a w v.
Proof. intros m a a' w v v' -> -> H. exact H. Qed.

(* The new chunk's header cells (AGjy.cells_chunks_new). *)
Lemma g_cells_chunks_new : Forall (cell_holds B lyF rd') (chunk_cells KSc).
Proof.
assert (EV : forall d, aeval B lyF (ASec rS0 d) = mb + d) by (intros d; cbn [aeval]; rewrite g_lysec; reflexivity).
unfold chunk_cells, hdr_state. rewrite g_KR, g_KN, g_KST, g_KB. unfold kChunkHeaderSize. cbn [sptr_exp app Z.eqb aoff].
constructor. { vmc (ANum 2). cbn [c_at c_w z1 c1]. rewrite EV. cbn [aeval].
  eapply vm_eq; [| reflexivity | exact Vst]. unfold ImgBaseAGS.Uv, kPage. zl. }
constructor.
{ unfold cell_holds. cbn [c_at c_val c_w]. rewrite EV. exists 17. split; [|reflexivity].
  pose proof (vm_aview_g _ _ _ _ _ _ 0%nat Vb1 ltac:(zl)) as X. rewrite Z.add_0_r in X.
  replace (mb + (kPage + (2048 - 16) + 1)) with (ImgBaseAGS.Uv mb - 15) by (unfold ImgBaseAGS.Uv, kPage; zl). rewrite X. reflexivity. }
constructor. { vmc (ANum 0). cbn [c_at c_w z2 c2]. rewrite EV. cbn [aeval].
  eapply vm_eq; [| reflexivity | exact Vb2]. unfold ImgBaseAGS.Uv, kPage. zl. }
constructor. { vmc (ANum n). cbn [c_at c_w z4 c4]. rewrite EV. cbn [aeval].
  eapply vm_eq; [| reflexivity | exact Vn]. unfold ImgBaseAGS.Uv, kPage. zl. }
constructor. { vmc (ANum 0xCC6E96B9CC6E96B9). cbn [c_at c_w z8 c8]. rewrite EV. cbn [aeval].
  eapply vm_eq; [| reflexivity | exact Vmag]. unfold ImgBaseAGS.Kv, kPage. zl. }
constructor. { vmc (ASec rS0 (kPage + (2048 - 16))). cbn [c_at c_w c8]. rewrite !EV.
  eapply vm_eq; [| | exact Vbk]; unfold ImgBaseAGS.Kv, ImgBaseAGS.Uv, kPage; zl. }
apply Forall_nil.
Qed.

(* The secondary's cells of the final state (AGjy.cells_sec). *)
Lemma g_cells_sec_old_arr : Forall (cell_holds B ly rd')
  (map (fun ir => c8 (AQ (8 * Z.of_nat (fst ir))) (ASec (snd ir) 0)) (combine (seq 0 (length (st_sec_arr S))) (st_sec_arr S))).
Proof.
pose proof g_res as [HR _].
apply g_keep.
- intros x Hx. unfold acells_cf. do 3 (apply in_app_iff; right). apply in_app_iff. left. unfold sec_cells. do 3 right. apply in_app_iff. left. exact Hx.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  apply (g_rng _ (fun a => ly_Q ly <= a < ly_Q ly + 8 * idx)).
  + intros a Ha. apply gX_Q; [unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; zl | unfold ImgBaseAGS.QSv; zl |].
    intros [_ Hq]. unfold AGif4.QRz in Hq. zl.
  + intros kk Hkk. cbn [c_at c_w aeval c8 fst snd] in *. cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ] in Hkk. zl.
Qed.
Lemma g_cells_sec_old_hdr : Forall (cell_holds B ly rd') (flat_map (fun k => match ck_beg k with
  | PSec r _ => [ c8 (ASec r 0) (ASec r 0); z8 (ASec r 8) (sec_map_size (ck_req k)); z8 (ASec r 16) (needed_size (ck_req k));
                 z8 (ASec r 24) (index_ofZ (st_sec_arr S) r) ]
  | _ => [] end) (st_chunks S)).
Proof.
apply g_keep.
- intros x Hx. unfold acells_cf. do 3 (apply in_app_iff; right). apply in_app_iff. left. unfold sec_cells. do 3 right. apply in_app_iff. right. exact Hx.
- apply Forall_flat_map'. intros k Hk.
  pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k) as [|o|r o|c' p'] eqn:Eb; try apply Forall_nil.
  destruct GG as (_ & _ & Gbase & Gext & Gin & _).
  pose proof (sec_map_size_page (ck_req k) ltac:(zl)) as SP.
  assert (LS : forall a, ly_sec ly r <= a < ly_sec ly r + sec_map_size (ck_req k) -> ~ gXC a)
    by (intros a Ha; exact (gX_sec _ a Gin Ha)).
  repeat (apply Forall_cons; [grng LS; unfold kPage in *; zl|]). apply Forall_nil.
Qed.
Lemma g_cells_sec : Forall (cell_holds B lyF rd') (sec_cells SF).
Proof.
pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _ & Rck & _).
pose proof g_sizes as (ND & MS & RS & RZ & FP). pose proof g_lyeqs as (_ & _ & EQ & _).
unfold sec_cells. rewrite Rres, Rarr, Rck.
constructor. { vmc (ANum (if grow then res + kPtrArrayEntriesPerCommit else res)).
  cbn [c_at c_w c8 aeval]. exact Vres. }
constructor. { vmc (ANum (Z.of_nat (length (st_sec_arr S ++ [rS0])))).
  cbn [c_at c_w z8 c8 aeval]. eapply vm_eq; [reflexivity | | exact Vnch]. rewrite length_app. cbn [length]. zl. }
constructor. { vmc (ANum 0). cbn [c_at c_w z1 c1 aeval]. exact Vmtx. }
apply Forall_app. split.
- rewrite length_app. cbn [length]. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir).
  destruct (Nat.eq_dec i (length (st_sec_arr S))) as [->|Hne].
  + assert (Er : r = rS0).
    { replace (length (st_sec_arr S) + 1)%nat with (length (st_sec_arr S ++ [rS0])) in Hir by (rewrite length_app; reflexivity).
      destruct (in_combine_seq_g _ _ _ _ Hir) as [E _]. rewrite Nat.sub_0_r, nth_error_app2 in E by zl.
      rewrite Nat.sub_diag in E. cbn in E. injection E as <-. reflexivity. }
    subst r. vmc (ASec rS0 0). cbn [c_at c_w c8 aeval fst snd]. rewrite EQ, g_lysec, Z.add_0_r.
    exact Vslot.
  + assert (Hold : In (i, r) (combine (seq 0 (length (st_sec_arr S))) (st_sec_arr S))).
    { replace (length (st_sec_arr S) + 1)%nat with (length (st_sec_arr S ++ [rS0])) in Hir by (rewrite length_app; reflexivity).
      destruct (in_combine_seq_g _ _ _ _ Hir) as [E R]. rewrite length_app in R. cbn [length] in R. rewrite Nat.sub_0_r in E.
      rewrite nth_error_app1 in E by zl. apply combine_seq_in_g; [rewrite Nat.sub_0_r; exact E | zl]. }
    apply (cell_holds_le B ly lyF _ g_le rd');
      [| exact (proj1 (Forall_forall _ _) g_cells_sec_old_arr _ ltac:(apply in_map_iff; exists (i, r); split; [reflexivity | exact Hold]))].
    split; cbn; [exact I|]. apply in_combine_r in Hold.
    pose proof (proj1 (wsc_arr_live _ (wfc_secondary _ _ _ _ _ WF) r) Hold) as (sm & Hsm & _).
    apply nth_error_Some. rewrite Hsm. discriminate.
- rewrite flat_map_app. apply Forall_app. split.
  + apply (Forall_cell_holds_le B ly lyF _ g_le rd').
    * apply Forall_flat_map'. intros k Hk. pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
      destruct (ck_beg k) as [|o|r o|c' p]; try apply Forall_nil. destruct GG as (_ & _ & _ & _ & _ & _ & LT).
      repeat (apply Forall_cons; [split; cbn; first [exact LT | exact I]|]). apply Forall_nil.
    * apply Forall_flat_map'. intros k Hk.
      pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_flat_map _ _ _) g_cells_sec_old_hdr) k Hk) as HK. cbv beta in HK.
      pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
      destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try exact HK.
      assert (INr : In r (st_sec_arr S)).
      { apply (proj2 (wsc_arr_chunks _ (wfc_secondary _ _ _ _ _ WF) r)). exists k. split; [exact Hk|]. rewrite Eb.
        destruct GG as (-> & _). reflexivity. }
      unfold index_ofZ in *. rewrite (index_of_app_old_g _ _ _ 0 INr). exact HK.
  + cbn [flat_map app]. rewrite g_KB. cbv beta iota. rewrite app_nil_r. rewrite g_KQ, ND, MS.
    unfold index_ofZ. rewrite (index_of_app_new_g _ _ 0 g_rS_not_in_arr). cbn [Nat.add].
    assert (EV : forall d, aeval B lyF (ASec rS0 d) = mb + d) by (intros d; cbn [aeval]; rewrite g_lysec; reflexivity).
    constructor. { vmc (ASec rS0 0). cbn [c_at c_w c8]. rewrite !EV, Z.add_0_r. exact Vh0. }
    constructor. { vmc (ANum MSn). cbn [c_at c_w z8 c8]. rewrite EV. cbn [aeval]. exact Vh8. }
    constructor. { vmc (ANum (ImgBaseAGS.NDv n)). cbn [c_at c_w z8 c8]. rewrite EV. cbn [aeval]. exact Vh16. }
    constructor. { vmc (ANum (Z.of_nat (length (st_sec_arr S)))). cbn [c_at c_w z8 c8]. rewrite EV. cbn [aeval]. exact Vh24. }
    apply Forall_nil.
Qed.

(* The depot's facts at the final memory (AGjy.depot_final): the walk's depot post at memD, read through the
   depot's footprint, which the depot's write zone covers. *)
Lemma g_ids : depot_ids S <= 4097.
Proof.
pose proof (depot_len_bound _ _ (amc_universe _ _ _ _ _ M) (wfc_depot _ _ _ _ _ WF)). unfold depot_ids, DEPOT_MAX in *. zl.
Qed.
Lemma g_fp_range : forall a, CLdepot.depot_footprint B ly a -> 0 <= a < 2 ^ 64.
Proof.
pose proof (aso_cells _ (amc_syms _ _ _ _ _ M)) as AC.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as [N1 N2].
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as [S1 S2].
cbn [fst snd] in N1, N2, S1, S2. ceil.
intros a Ha. unfold CLdepot.depot_footprint, d_map1, kLowMemEnd, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zl.
Qed.
Lemma g_depot_final : CLdepot.depot_mem_ok B ly (depot_after z tr S) rd'.
Proof.
destruct DP as (_ & DEPD & _).
apply (dmo_agree_fp B ly _ rdD).
- pose proof g_ids. unfold depot_after. destruct (z =? 0); [zl|]. unfold depot_ids in *. cbn [st_depot set_depot].
  rewrite length_app. cbn [length]. zl.
- intros a Ha. apply AGREED; [exact (g_fp_range a Ha) | exact (DEP_FP ly a LY IMG TSD Ha)].
- exact (dmo_rdext B ly _ _ _ (g_RX memD) DEPD).
Qed.
Lemma g_cells_depot : Forall (cell_holds B ly rd') (depot_cells ly SF).
Proof.
pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
replace (depot_cells ly SF) with (depot_cells ly (depot_after z tr S))
  by (unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; reflexivity).
exact (proj1 g_depot_final).
Qed.
Lemma g_cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. constructor; [|apply Forall_nil].
vmc (ANum 0). cbn [c_at c_w z1 c1 aeval]. exact Vunw.
Qed.

(* ---- the const cells (AGjy.const_final) ---- *)
Lemma g_img_band : forall a, kImgLo <= a < kImgEnd -> ~ in_band_rw a.
Proof. intros a Ha HB. unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kHighShadowBeg in *. zl. Qed.
(* The shadow of an image range is in the low shadow band. *)
Lemma g_shimg : forall a lo len, kImgLo <= lo -> lo + len <= kImgEnd -> 0 <= len ->
  in_zr a (shadow_addr lo, (len + 7) / 8) -> in_band_rw a.
Proof.
intros a lo len L1 L2 L0 Ha. unfold in_zr, shadow_addr in *. cbn [fst snd] in Ha.
pose proof (Z.div_mod lo 8 ltac:(zl)). pose proof (Z.mod_pos_bound lo 8 ltac:(zl)).
pose proof (Z.div_mod (len + 7) 8 ltac:(zl)). pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(zl)).
unfold in_band_rw, kImgLo, kImgEnd, SHADOW_OFF, kLowShadowBeg, kLowShadowEnd in *. zl.
Qed.
Lemma g_core_nx : forall a, owned_core B ly a -> ~ gwj ly a -> ~ ims_dzone ly a ->
  ~ (as_inst B + o_sec_mutex + 1 <= a < as_inst B + o_sec_mutex + 4) -> ~ gXC a.
Proof.
intros a O NW ND NP X.
assert (NWI : ~ ImgBaseAGS.WINI regs0 n a).
{ intros Y. pose proof cf_malloc_max_bound. pose proof (bsl_bounds regs0 n ltac:(zl)) as Bs. rewrite Hinst in Bs.
  unfold ImgBaseAGS.WINI in Y. rewrite Hinst in Y. apply NW. unfold gwj.
  unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. zl. }
assert (NWT : ~ ImgBaseAGS.WINT ly a) by (intros Y; apply NW; unfold gwj; pose proof (g_wint a Y); unfold kThreadObjSize; zl).
assert (NQ : ~ (ly_Q ly <= a < ly_Q ly + kPtrArrayResv)) by (intros Y; apply NW; unfold gwj; left; exact Y).
pose proof g_facts as (MA & MI & _). pose proof g_ms as (_ & MS2 & _).
pose proof (g_map_st (ly_img ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as DMI.
pose proof (lo_img ly LY) as (J0 & J1 & J2 & J3).
(* the static owned areas are image ranges *)
assert (SI : forall r, In r (as_owned_static B) -> fst (ly_img ly) <= fst r /\ fst r + snd r <= fst (ly_img ly) + snd (ly_img ly) /\ 0 <= snd r).
{ intros r Hr. pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
  pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (_ & R3 & _). zl. }
assert (CORE : forall e, In e (core_extents ly) -> In e (owned_extents ly)) by (intros e He; unfold core_extents in He; unfold owned_extents; cbn in He |- *; tauto).
unfold gXC in X. destruct X as [Y|[Y|[Y|[Y|[Y|[Y|[_ Y]]]]]]].
- exact (NWT Y).
- exact (NWI Y).
- exact (NQ (g_qs a Y)).
- destruct O as [O|[O|O]].
  + apply Exists_exists in O as (r & Hr & Ha). pose proof (SI r Hr) as (R1 & R2 & R3).
    unfold zdisjoint, in_zr in *. cbn [fst snd] in *. zl.
  + apply Exists_exists in O as (e & He & Ha). pose proof (g_map_st e ltac:(unfold static_extents; apply in_app_iff; left; exact (CORE e He))) as D.
    unfold zdisjoint, in_zr in *. cbn [fst snd] in *. zl.
  + apply Exists_exists in O as (r & Hr & Ha). pose proof (SI r Hr) as (R1 & R2 & R3).
    pose proof (g_shimg a (fst r) (snd r) ltac:(zl) ltac:(zl) R3 Ha) as HB. exact (app_not_band mb MSn a MI Y HB).
- pose proof (g_msh_band a Y) as YB. destruct O as [O|[O|O]].
  + apply Exists_exists in O as (r & Hr & Ha). pose proof (SI r Hr) as (R1 & R2 & R3). unfold in_zr in Ha.
    exact (g_img_band a ltac:(zl) YB).
  + apply Exists_exists in O as (e & He & Ha). exact (app_not_band (fst e) (snd e) a (g_owned_app e (CORE e He)) Ha YB).
  + apply Exists_exists in O as (r & Hr & Ha). pose proof (SI r Hr) as (R1 & R2 & R3).
    rewrite g_SM in Y. unfold in_zr, shadow_addr in Ha, Y. cbn [fst snd] in Ha.
    unfold page_aligned in MA. apply Z.mod_divide in MA as [p Hpm]; [|zl]. apply Z.mod_divide in MS2 as [s Hsm]; [|zl].
    apply Z.mod_divide in J3 as [q Hqm]; [|zl].
    assert (Ep : mb / 8 = 512 * p) by (rewrite Hpm; replace (p * 4096) with ((512 * p) * 8) by zl; apply Z.div_mul; zl).
    assert (Es : MSn / 8 = 512 * s) by (rewrite Hsm; replace (s * 4096) with ((512 * s) * 8) by zl; apply Z.div_mul; zl).
    rewrite Ep, Es in Y.
    pose proof (Z.div_mod (fst r) 8 ltac:(zl)). pose proof (Z.mod_pos_bound (fst r) 8 ltac:(zl)).
    pose proof (Z.div_mod (snd r + 7) 8 ltac:(zl)). pose proof (Z.mod_pos_bound (snd r + 7) 8 ltac:(zl)).
    unfold zdisjoint in DMI. cbn [fst snd] in DMI. unfold kImgLo in J0. zl.
- exact (ND Y).
- exact (NQ (g_qr a Y)).
Qed.
Lemma cell_agree3_g : forall lyx (rd1 rd2 rd3 : reader) c,
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
     (forall v, rd1 (aeval B lyx (c_at c) + k) = Some v -> rd3 (aeval B lyx (c_at c) + k) = Some v) \/
     rd3 (aeval B lyx (c_at c) + k) = rd2 (aeval B lyx (c_at c) + k)) ->
  cell_holds B lyx rd1 c -> cell_holds B lyx rd2 c -> cell_holds B lyx rd3 c.
Proof.
intros lyx rd1 rd2 rd3 c He H1 H2. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. destruct (He (Z.of_nat k) ltac:(zl)) as [E|E]; [exact (E _ (H1 k Hk)) | rewrite E; exact (H2 k Hk)].
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
  destruct (He 0 ltac:(zl)) as [E|E]; rewrite Z.add_0_r in E; [exists b1; split; [exact (E _ Hb1) | exact Hm1] | exists b2; rewrite E; tauto].
Qed.
(* A const byte: it keeps its value, or it is in the depot's write zone (the depot's post at memD holds it). *)
Lemma g_const_byte : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  (forall v, rd0 (aeval B ly (c_at c) + k) = Some v -> rd' (aeval B ly (c_at c) + k) = Some v) \/
  rd' (aeval B ly (c_at c) + k) = rdD (aeval B ly (c_at c) + k).
Proof.
intros c k Hc Hk.
pose proof (proj1 (Forall_forall _ _) (amc_const_owned _ _ _ _ _ M) c Hc) as CO.
pose proof (proj1 (Forall_forall _ _) (const_cells_owned_cf B ly S Hp _ M) c Hc) as COW.
destruct (INST_CELLS ly (w_H W) mem0 LY TSD (amc_const _ _ _ _ _ M)) as (_ & _ & _ & _ & _ & _ & _ & C8).
set (a := aeval B ly (c_at c) + k).
assert (Ra : 0 <= a < 2 ^ 64).
{ pose proof (AR_owned_low_law_ok_cf im_segs B ly S Hp W mem0 md0 a HAR (COW k Hk)) as R.
  pose proof alloc_ceiling_val. unfold alloc_ceiling in *. zl. }
destruct (DZ_DEC ly a) as [D|D]; [right; exact (AGREED a Ra D)|left].
destruct (zr_dec (as_inst B + o_sec_mutex + 1) (as_inst B + o_sec_mutex + 4) a) as [P|P].
- intros v Hv.
  assert (Ea : a = as_inst B + o_sec_mutex + 1 + Z.of_nat (Z.to_nat (a - (as_inst B + o_sec_mutex + 1)))) by (rewrite Z2Nat.id by zl; zl).
  pose proof (vm_aview_g _ _ _ _ _ _ (Z.to_nat (a - (as_inst B + o_sec_mutex + 1))) C8 ltac:(zl)) as X. rewrite <- Ea, le_byte_zero in X.
  rewrite X in Hv. injection Hv as <-.
  replace a with (as_inst B + o_sec_mutex + (a - (as_inst B + o_sec_mutex))) by zl. apply Vpad. zl.
- apply (AGX a (COW k Hk)).
  apply g_core_nx; [exact (CO k Hk) | exact (CONST_APART ly c k LY IMG TSD Hc Hk) | exact D | exact P].
Qed.
Lemma g_const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
destruct DP as (_ & _ & CSTD).
apply Forall_forall. intros c Hc.
apply (cell_agree3_g ly rd0 rdD rd'); [| exact (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M) c Hc) |
  exact (proj1 (Forall_forall _ _) (Forall_cell_holds_ext B ly _ _ _ (g_RX memD) CSTD) c Hc)].
intros k Hk. exact (g_const_byte c k Hc Hk).
Qed.

(* ---- lifting the old cells to the grown layout: no old cell names the new slot (YFib.acells_lt over Wf_cf) ---- *)
Local Notation nS := (length (st_secs S)).
Lemma g_chunk_lt : forall k, In k (st_chunks S) -> match ck_beg k with PSec r _ => (r < nS)%nat | _ => True end.
Proof.
intros k Hk. pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k) as [|o|r o|c p]; try exact I. destruct GG as (_ & _ & _ & _ & _ & _ & LT). exact LT.
Qed.
Local Ltac cell_tac := unfold cell_lt; cbn [c_at c_val]; split; cbn; try exact I.
Lemma g_cells_lt : Forall (cell_lt nS) (acells_cf B ly S).
Proof.
unfold acells_cf.
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. eapply incl_Forall; [apply region_cells_cf_incl|].
  unfold region_cells. destruct (rg_mapped_user (reg S c) =? 0); repeat (apply Forall_cons; [cell_tac|]); apply Forall_nil. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold cache_cells.
  destruct (st_cache_inited S).
  - repeat (apply Forall_cons; [cell_tac|]). apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (io & <- & _). cell_tac.
  - repeat (apply Forall_cons; [cell_tac|]); apply Forall_nil. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (g_chunk_lt k Hk) as LT. unfold chunk_cells.
  apply Forall_app. split.
  - repeat (apply Forall_cons; [split; cbn [c_at c_val]; try exact I; repeat apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]).
    apply Forall_nil.
  - destruct (ck_rz k =? kChunkHeaderSize); [apply Forall_nil|].
    repeat (apply Forall_cons; [split; cbn [c_at c_val]; try exact I; repeat apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]).
    apply Forall_nil. }
apply Forall_app. split.
{ unfold sec_cells. apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|]. apply Forall_app. split.
  - apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i r] & <- & Hin). apply in_combine_r in Hin.
    pose proof (proj1 (wsc_arr_live _ (wfc_secondary _ _ _ _ _ WF) r) Hin) as (sm & Hsm & _).
    cell_tac. apply nth_error_Some. rewrite Hsm. discriminate.
  - apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (g_chunk_lt k Hk) as LT.
    destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. repeat (apply Forall_cons; [cell_tac; exact LT|]). apply Forall_nil. }
apply Forall_app. split.
{ unfold quar_cells. apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|].
  assert (ITEMS : forall k, In k (q_items S) -> match ck_hdr k with PSec r _ => (r < nS)%nat | _ => True end).
  { intros k Hk. pose proof (proj1 (Forall_forall _ _) (wq_items _ (wfc_quarantine _ _ _ _ _ WF)) k Hk) as [Hin _].
    unfold ck_hdr. pose proof (g_chunk_lt k Hin) as LT. destruct (ck_beg k); cbn; try exact I. exact LT. }
  assert (BATCH : forall bl, incl (flat_map b_items bl) (q_items S) -> Forall (cell_lt nS) (batch_cells bl)).
  { induction bl as [|b t IH]; intros INC; [apply Forall_nil|]. cbn [batch_cells].
    apply Forall_cons; [unfold cell_lt; cbn [c_at c_val]; split; [cbn; exact I|]; destruct t; cbn; exact I|].
    apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|]. apply Forall_app. split.
    - apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i k] & <- & Hin). apply in_combine_r in Hin.
      unfold cell_lt; cbn [c_at c_val fst snd]. split; [cbn; exact I|]. apply sptr_exp_lt. apply ITEMS. apply INC.
      cbn. apply in_app_iff. left. exact Hin.
    - apply IH. intros k Hk. apply INC. cbn. apply in_app_iff. right. exact Hk. }
  assert (QC : forall root q, asec_lt nS root -> (forall e, root <> ASh e) -> incl (flat_map b_items (qc_list q)) (q_items S) ->
    Forall (cell_lt nS) (qc_cells root q)).
  { intros root q Hr Hsh INC. unfold qc_cells.
    apply Forall_cons; [split; cbn [c_at c_val]; [exact Hr | cbn; exact I]|].
    apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | destruct (qc_list q); cbn; exact I]|].
    apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | destruct (rev (qc_list q)); cbn; exact I]|].
    apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | cbn; exact I]|].
    apply BATCH. exact INC. }
  apply Forall_app. split; apply QC; cbn; try exact I; try (intros e E; discriminate E);
    unfold q_items, all_batches; intros k Hk; rewrite flat_map_app; apply in_app_iff; [left | right]; exact Hk. }
apply Forall_app. split.
{ unfold fs_cells. apply Forall_cons; [cell_tac|]. apply Forall_cons; [cell_tac|].
  apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i h] & <- & _). cell_tac. }
apply Forall_app. split.
{ unfold depot_cells. repeat (apply Forall_cons; [cell_tac|]). apply Forall_nil. }
apply Forall_app. split.
{ unfold ialloc_cells. repeat (apply Forall_cons; [cell_tac|]); [destruct (st_internal_inited S); cbn; exact I | apply Forall_nil]. }
{ unfold thread_cells. apply Forall_cons; [cell_tac | apply Forall_nil]. }
Qed.

Lemma g_cells_final : Forall (cell_holds B lyF rd') (acells_cf B lyF SF).
Proof.
pose proof g_cells_lt as LT. unfold acells_cf in LT |- *.
pose proof g_lyeqs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E13 & _).
assert (LIFT : forall l, incl l (flat_map (region_cells_cf S) (zseq 1 31) ++ flat_map (cache_cells S) (zseq 1 31) ++
    flat_map chunk_cells (st_chunks S) ++ sec_cells S ++ quar_cells S ++ fs_cells S ++ depot_cells ly S ++ ialloc_cells B S ++
    thread_cells) ->
  Forall (cell_holds B ly rd') l -> Forall (cell_holds B lyF rd') l).
{ intros l INC H. apply (Forall_cell_holds_le B ly lyF _ g_le rd'); [exact (incl_Forall INC LT) | exact H]. }
pose proof g_SF as (Rreg & Rinit & Rcache & _ & Rqt & Rqg & Rfs & Rii & _ & _ & Rdep & Rck & _).
apply Forall_app; split.
{ apply LIFT; [| exact g_cells_regions]. intros x Hx. apply in_app_iff. left. apply in_flat_map in Hx as (c & Hc & Hx).
  apply in_flat_map. exists c. unfold region_cells_cf, region_cells in *. rewrite Rreg in Hx. exact (conj Hc Hx). }
apply Forall_app; split.
{ apply LIFT; [| exact g_cells_caches]. intros x Hx. apply in_app_iff; right. apply in_app_iff; left.
  apply in_flat_map in Hx as (c & Hc & Hx). apply in_flat_map. exists c. unfold cache_cells in *. rewrite Rinit, (Rcache c) in Hx.
  exact (conj Hc Hx). }
apply Forall_app; split.
{ rewrite Rck, flat_map_app. apply Forall_app; split.
  - apply LIFT; [| exact g_cells_chunks_old]. intros x Hx. do 2 (apply in_app_iff; right). apply in_app_iff; left. exact Hx.
  - cbn [flat_map]. rewrite app_nil_r. exact g_cells_chunks_new. }
apply Forall_app; split; [exact g_cells_sec|].
apply Forall_app; split.
{ apply LIFT; [| exact g_cells_quar]. intros x Hx. do 4 (apply in_app_iff; right). apply in_app_iff; left.
  unfold quar_cells in *. rewrite Rqt, Rqg in Hx. exact Hx. }
apply Forall_app; split.
{ apply LIFT; [| exact g_cells_fs]. intros x Hx. do 5 (apply in_app_iff; right). apply in_app_iff; left.
  unfold fs_cells in *. rewrite Rfs in Hx. exact Hx. }
apply Forall_app; split.
{ replace (depot_cells lyF SF) with (depot_cells ly SF) by (unfold depot_cells, depot_frames, depot_traces; rewrite E13; reflexivity).
  apply (Forall_cell_holds_le B ly lyF _ g_le rd'); [| exact g_cells_depot].
  unfold depot_cells. repeat (apply Forall_cons; [split; cbn; exact I|]). apply Forall_nil. }
apply Forall_app; split.
{ apply LIFT; [| exact g_cells_ialloc]. intros x Hx. do 7 (apply in_app_iff; right). apply in_app_iff; left.
  unfold ialloc_cells in *. rewrite Rii in Hx. exact Hx. }
apply LIFT; [| exact g_cells_thread]. intros x Hx. do 8 (apply in_app_iff; right). exact Hx.
Qed.

Lemma g_const_finalF : Forall (cell_holds B lyF rd') (as_const B lyF).
Proof. rewrite (CONST_LY lyF ly). exact (Forall_cell_holds_le B ly lyF _ g_le rd' _ (CONST_LT ly _) g_const_final). Qed.
Lemma g_const_ownedF : Forall (cell_owned B lyF) (as_const B lyF).
Proof.
rewrite (CONST_LY lyF ly). apply Forall_forall. intros c Hc k Hk.
pose proof (proj1 (Forall_forall _ _) (CONST_LT ly nS) c Hc) as [LTa _].
pose proof (proj1 (Forall_forall _ _) (amc_const_owned _ _ _ _ _ M) c Hc k Hk) as O.
rewrite (g_aeval _ LTa). pose proof g_static as (_ & _ & EC & _). unfold owned_core in *. rewrite EC. exact O.
Qed.
Lemma g_fa_final : fa_entries_ok lyF rd' SF.
Proof.
pose proof g_SF as (Rreg & _). pose proof g_lyeqs as (_ & E2 & _). intros c i vv Hc Hi HV k Hk. rewrite Rreg in Hi, HV.
unfold fa_base. rewrite E2. change (ly_space ly + region_off c + kFreeArrayOffset) with (fa_base ly c).
pose proof (wfc_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (region_in_prim ly c LY Hc) as (R1 & R2 & _).
apply AGX; [eapply own_fa_cf; [exact M | exact Hc | unfold kFreeArrayMax in *; zl] | | exact (amc_fa _ _ _ _ _ M c i vv Hc Hi HV k Hk)].
apply gX_prim. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. zl.
Qed.
Lemma g_flags_final : fs_flags_ok lyF rd' SF.
Proof.
pose proof g_SF as (_ & _ & _ & Rfr & _). pose proof g_lyeqs as (_ & _ & _ & _ & _ & E6 & _). intros cid pos Hc Hp'.
rewrite Rfr. unfold flag_addr. rewrite E6. pose proof (flag_off_bounds cid pos Hc Hp') as FB.
apply AGX; [unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low_cf; [exact M | zl] | | exact (amc_flags _ _ _ _ _ M cid pos Hc Hp')].
apply gX_F. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. zl.
Qed.
Lemma g_zero_final : Forall (range_zero B lyF rd') (ialloc_zero B).
Proof.
pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ M)) as [I1 I2].
apply Forall_forall. intros r Hr i Hi.
assert (EV : aeval B lyF (fst r) = aeval B ly (fst r)) by (unfold ialloc_zero in Hr; destruct Hr as [<-|[<-|[]]]; reflexivity). rewrite EV.
assert (LOC : as_ialloc_lo B <= aeval B ly (fst r) + i < as_ialloc_hi B)
  by (unfold ialloc_zero in Hr; destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zl).
apply AGX.
- eapply (own_area_cf B ly S Hp _ (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M | unfold asyms_areas; cbn; tauto | cbn [fst snd]; zl].
- apply gX_imgx; [| | right; left; exact LOC].
  + apply (sn_area_img Hp ly S W mem0 md0 HAR (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [unfold asyms_areas; cbn; tauto | unfold in_zr; cbn [fst snd]; zl].
  + intros X. pose proof (pw_ij zdisjoint (firstn 6 (asyms_areas B)) 0 2 _ _ AREAS_DISJ eq_refl eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. zl.
- exact (proj1 (Forall_forall _ _) (amc_zero _ _ _ _ _ M) r Hr i Hi).
Qed.
Lemma g_depot_okF : depot_ok B lyF rd' SF.
Proof.
pose proof g_depot_final as (_ & D2 & _). pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
pose proof g_lyeqs as (_ & _ & _ & _ & _ & _ & E7 & _ & _ & _ & _ & _ & E13 & _).
unfold depot_ok, depot_ids, depot_traces in *. rewrite E7, E13, Rdep. exact D2.
Qed.

(* ---- the view only gains (AGjy.PRES_MONO / VIS_MONO) ---- *)
Lemma g_PRES : forall u, 0 <= u < 2 ^ 64 -> ~ ImgBaseAGS.WINI regs0 n u -> apresent (w_H W) mem0 u -> apresent (w_H Wz) mem' u.
Proof.
intros u Ru NWI Hp0.
assert (HpW : apresent (w_H Wz) mem0 u) by (destruct Hp0 as [Hh Hb]; split; [exact (MON _ Hh) | exact Hb]).
destruct (DZ_DEC ly u) as [D|D].
{ apply (apresent_same_g _ memD); [apply EQD; rewrite w64_unsigned by exact Ru; exact D | exact (PRD u D HpW)]. }
destruct (zr_dec (sp0 - ImgBaseAGS.AFSTACK) sp0 u) as [D4|D4]; [apply PRS; exact D4|].
destruct (zr_dec mb (mb + MSn) u) as [D5|D5]; [apply PRmap; exact D5|].
destruct (zr_dec SMn (SMn + MSn / 8) u) as [D6|D6]; [apply PRsh; exact D6|].
destruct (zr_dec QSn (QSn + 8) u) as [D7|D7]; [apply PRW; right; exact D7|].
assert (DW : ImgBaseAGS.WINT ly u \/ ~ ImgBaseAGS.WINT ly u) by (unfold ImgBaseAGS.WINT; zl).
destruct DW as [D8|D8]; [apply PRW; left; exact D8|].
assert (DQ : AGif4.QRz ly res u \/ ~ AGif4.QRz ly res u) by (unfold AGif4.QRz; zl).
assert (NQR : ~ (grow = true /\ AGif4.QRz ly res u) \/ (grow = true /\ AGif4.QRz ly res u)).
{ destruct grow; [destruct DQ as [D9|D9]; [right; split; [reflexivity | exact D9] | left; intros [_ X]; exact (D9 X)] | left; intros [E _]; discriminate E]. }
destruct NQR as [NQR|[Eg D9]]; [|exact (PRq Eg u D9)].
apply (apresent_same_g _ mem0); [|exact HpW]. apply MEQF; rewrite w64_unsigned by exact Ru.
- unfold ImgBaseAGS.WIN, ImgBaseAGS.WINM. tauto.
- exact NQR.
- intros [Hs|Hd]; [apply D4; unfold ImgBaseAGS.DEP_STK, ImgBaseAGS.AFSTACK in *; zl | exact (D Hd)].
Qed.
Lemma g_VIS : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a0 HV0. set (a := bv_unsigned (Z_to_bv 64 a0)).
assert (Ra : 0 <= a < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
assert (Ex : Z_to_bv 64 a = Z_to_bv 64 a0) by (subst a; apply Z_to_bv_bv_unsigned).
assert (AV : forall (Hh : word -> bool) m, aview im_segs Hh m a0 = aview im_segs Hh m a)
  by (intros Hh m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
rewrite AV in HV0 |- *. clearbody a. clear Ex AV a0.
assert (DI : ImgBaseAGS.WINI regs0 n a \/ ~ ImgBaseAGS.WINI regs0 n a) by (unfold ImgBaseAGS.WINI; zl).
destruct DI as [HWI|NWI]; [exact (VISW a HWI)|].
unfold aview, mbyte in *.
destruct (seg_rom im_segs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H Wz) mem' (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp0 : apresent (w_H W) mem0 a).
  { unfold mrestrict in HV0. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [exfalso; apply HV0; reflexivity|].
    split; [reflexivity|]. destruct (mem0 (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply HV0; reflexivity]. }
  destruct (g_PRES a Ra NWI Hp0) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma g_apresent_vis : forall a, apresent (w_H Wz) mem' a -> rd' a <> None.
Proof. intros a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* ---- the junk, areas and client ranges (AGjy's vis_junk, vis_areas, vis_client) ---- *)
Lemma g_junk_lt : Forall (fun r => asec_lt nS (fst r)) (ajunk_cf B ly S).
Proof.
unfold ajunk_cf. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|].
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold region_junk_cf, region_junk.
  repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold cache_junk. apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (g_chunk_lt k Hk) as LT. unfold chunk_junk.
  repeat (apply Forall_app; split); try (destruct (ck_rz k =? kChunkHeaderSize)); try (destruct (ck_state k)); try apply Forall_nil;
  repeat (apply Forall_cons; [cbn [fst]; apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]); apply Forall_nil. }
apply Forall_app. split.
{ unfold sec_junk. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|].
  apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (g_chunk_lt k Hk) as LT.
  destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. apply Forall_cons; [cbn; exact LT | apply Forall_nil]. }
apply Forall_app. split.
{ unfold quar_junk. apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros b _. unfold batch_junk.
  apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ unfold thread_junk. repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split.
{ repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
exact (JUNK_LT ly nS).
Qed.
Lemma g_areas_lt : Forall (fun r => asec_lt nS (fst r)) (aareas S).
Proof.
unfold aareas. apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split. { apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (g_chunk_lt k Hk) as LT.
  destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. apply Forall_cons; [cbn; exact LT | apply Forall_nil]. }
repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil.
Qed.
Lemma g_client_lt : Forall (fun r => asec_lt nS (fst r)) (aclient S).
Proof.
unfold aclient. apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (g_chunk_lt k Hk) as LT. unfold chunk_user.
  destruct (ck_state k); [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil]. cbn [fst]. apply sptr_exp_lt.
  unfold ck_user. destruct (ck_beg k); cbn; try exact I. exact LT. }
apply Forall_app. split; apply Forall_forall; intros x Hx; apply in_map_iff in Hx as (cq & <- & _); cbn; exact I.
Qed.
Lemma g_vis_old : forall lst, incl lst (ajunk_cf B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) ->
  Forall (range_vis B lyF rd') lst.
Proof.
intros lst H. apply (Forall_range_vis_le B ly lyF _ g_le rd').
- destruct H as [H|[H|H]]; (eapply incl_Forall; [exact H|]); [exact g_junk_lt | exact g_areas_lt | exact g_client_lt].
- apply (Forall_range_vis_keep B ly rd0 rd' lst g_VIS).
  destruct H as [H|[H|H]]; (eapply incl_Forall; [exact H|]);
    [exact (amc_junk _ _ _ _ _ M) | exact (amc_areas _ _ _ _ _ M) | exact (amc_client _ _ _ _ _ M)].
Qed.
Lemma g_vis_map : forall e len, mb <= aeval B lyF e -> aeval B lyF e + len <= mb + MSn -> range_vis B lyF rd' (e, len).
Proof. intros e len H1 H2 i Hi. cbn [fst snd] in Hi |- *. apply g_apresent_vis. apply PRmap. zl. Qed.
Lemma g_resF : idx + 1 <= (if grow then res + kPtrArrayEntriesPerCommit else res) <= kPtrArrayEntriesPerCommit /\
  (grow = false -> idx < res).
Proof.
pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _).
pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WFF)) as WR. rewrite Rarr, Rres, length_app in WR. cbn [length] in WR.
pose proof g_res as [HRS _]. split; [unfold kPtrArrayEntriesPerCommit in *; zl|]. intros Hg.
destruct (Z.eq_dec idx res) as [E|NE]; [|zl]. exfalso. pose proof (proj2 Hgrow E) as Hg'. rewrite Hg in Hg'. discriminate Hg'.
Qed.
Lemma g_vis_junk : Forall (range_vis B lyF rd') (ajunk_cf B lyF SF).
Proof.
pose proof g_SF as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof g_sizes as (ND & MS & RS & RZ & FP). pose proof g_lyeqs as (_ & _ & EQ & _). pose proof g_ms as (MS1 & MS2 & MS3).
pose proof g_resF as [RF1 RF2]. pose proof g_res as [HRS _].
assert (EV2 : forall d d', aeval B lyF (aoff (ASec rS0 d) d') = mb + d + d') by (intros d d'; cbn [aeval aoff]; rewrite g_lysec; zl).
assert (OLD : forall x, In x (ajunk_cf B ly S) -> Forall (range_vis B lyF rd') [x])
  by (intros x Hx; apply g_vis_old; left; intros y [<-|[]]; exact Hx).
unfold ajunk_cf. rewrite Rck.
apply Forall_cons. { exact (proj1 (Forall_forall _ _) (OLD _ ltac:(unfold ajunk_cf; left; reflexivity)) _ (or_introl eq_refl)). }
apply Forall_cons. { exact (proj1 (Forall_forall _ _) (OLD _ ltac:(unfold ajunk_cf; right; left; reflexivity)) _ (or_introl eq_refl)). }
apply Forall_app; split; [apply g_vis_old; left; intros x Hx; unfold ajunk_cf; do 2 right; apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ replace (flat_map (cache_junk SF) (zseq 1 31)) with (flat_map (cache_junk S) (zseq 1 31))
    by (apply flat_map_ext; intros c; unfold cache_junk; rewrite Rinit, (Rcache c); reflexivity).
  apply g_vis_old. left. intros x Hx. unfold ajunk_cf. do 2 right. apply in_app_iff; right. apply in_app_iff; left. exact Hx. }
apply Forall_app; split.
{ rewrite flat_map_app. apply Forall_app; split.
  - apply g_vis_old. left. intros x Hx. unfold ajunk_cf. do 2 right. do 2 (apply in_app_iff; right). apply in_app_iff; left. exact Hx.
  - cbn [flat_map]. rewrite app_nil_r. unfold chunk_junk. rewrite g_KR, g_KN, g_KST, g_KB.
    assert (KE : ck_extent KSc = MSn - 4096) by (unfold ck_extent; rewrite g_KQ, FP, MS; unfold kPage; reflexivity).
    rewrite KE. unfold kChunkHeaderSize. cbn [sptr_exp app Z.eqb Pos.eqb].
    repeat (apply Forall_cons; [apply g_vis_map; rewrite EV2; unfold kPage; zl|]). apply Forall_nil. }
apply Forall_app; split.
{ unfold sec_junk. rewrite Rarr, Rres, Rck, flat_map_app, length_app. cbn [length].
  apply Forall_cons. { exact (proj1 (Forall_forall _ _) (OLD _ ltac:(unfold ajunk_cf; do 2 right; do 3 (apply in_app_iff; right); apply in_app_iff; left; unfold sec_junk; left; reflexivity)) _ (or_introl eq_refl)). }
  apply Forall_cons. { exact (proj1 (Forall_forall _ _) (OLD _ ltac:(unfold ajunk_cf; do 2 right; do 3 (apply in_app_iff; right); apply in_app_iff; left; unfold sec_junk; right; left; reflexivity)) _ (or_introl eq_refl)). }
  apply Forall_cons.
  { intros i Hi. cbn [fst snd aeval] in Hi |- *. rewrite EQ. replace (Z.of_nat (length (st_sec_arr S) + 1)) with (idx + 1) in Hi |- * by zl.
    destruct (Z_lt_le_dec (ly_Q ly + 8 * (idx + 1) + i) (ly_Q ly + 8 * res)) as [LO|HI].
    - pose proof (proj1 (Forall_forall _ _) (amc_junk _ _ _ _ _ M) (AQ (8 * Z.of_nat (length (st_sec_arr S))), 8 * (st_sec_reserved S - Z.of_nat (length (st_sec_arr S))))
        ltac:(unfold ajunk_cf; do 2 right; do 3 (apply in_app_iff; right); apply in_app_iff; left; unfold sec_junk; do 2 right; left; reflexivity)) as RV.
      specialize (RV (8 + i)). cbn [fst snd aeval] in RV. apply g_VIS.
      replace (ly_Q ly + 8 * (idx + 1) + i) with (ly_Q ly + 8 * idx + (8 + i)) by zl. apply RV. zl.
    - apply g_apresent_vis. destruct grow eqn:Eg; [| pose proof (RF2 eq_refl); exfalso; zl].
      apply (PRq eq_refl). unfold AGif4.QRz. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. zl. }
  apply Forall_app; split.
  - apply g_vis_old. left. intros x Hx. unfold ajunk_cf. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left.
    unfold sec_junk. do 3 right. exact Hx.
  - cbn [flat_map]. rewrite g_KB. cbv beta iota. rewrite app_nil_r. constructor; [|apply Forall_nil].
    apply g_vis_map; cbn [aeval]; rewrite g_lysec; unfold kPage; zl. }
apply Forall_app; split.
{ apply g_vis_old. left. intros x Hx. unfold ajunk_cf. do 2 right. do 4 (apply in_app_iff; right). apply in_app_iff; left.
  unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. exact Hx. }
apply Forall_app; split; [apply g_vis_old; left; intros x Hx; unfold ajunk_cf; do 2 right; do 5 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
apply Forall_app; split; [apply g_vis_old; left; intros x Hx; unfold ajunk_cf; do 2 right; do 6 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
rewrite (JUNK_LY lyF ly). apply g_vis_old. left. intros x Hx. unfold ajunk_cf. do 2 right. do 7 (apply in_app_iff; right). exact Hx.
Qed.
Lemma g_vis_areas : Forall (range_vis B lyF rd') (aareas SF).
Proof.
pose proof g_SF as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof g_sizes as (ND & MS & RS & RZ & FP). pose proof g_lyeqs as (_ & _ & EQ & _).
pose proof g_resF as [RF1 RF2]. pose proof g_res as [HRS _].
unfold aareas. rewrite Rres, Rck, flat_map_app.
apply Forall_app; split.
{ unfold reg in Rreg. rewrite (flat_map_ext_in_g _ (fun c => [(ASp (region_off c), rg_mapped_user (reg S c));
    (ASp (region_off c + kFreeArrayOffset), rg_mapped_fa (reg S c))]) (zseq 1 31)); [| intros c _; unfold reg; rewrite Rreg; reflexivity].
  apply g_vis_old. right; left. intros x Hx. unfold aareas. apply in_app_iff. left. exact Hx. }
apply Forall_cons.
{ intros i Hi. cbn [fst snd aeval] in Hi |- *. rewrite EQ.
  destruct (Z_lt_le_dec i (8 * res)) as [LO|HI].
  - pose proof (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M) (AQ 0, 8 * st_sec_reserved S) ltac:(unfold aareas; apply in_app_iff; right; left; reflexivity)) as RV.
    specialize (RV i). cbn [fst snd aeval] in RV. apply g_VIS. apply RV. zl.
  - apply g_apresent_vis. destruct grow eqn:Eg; [| exfalso; zl].
    apply (PRq eq_refl). unfold AGif4.QRz. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. zl. }
apply Forall_app; split.
{ apply Forall_app; split.
  - apply g_vis_old. right; left. intros x Hx. unfold aareas. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; left. exact Hx.
  - cbn [flat_map]. rewrite g_KB. cbv beta iota. rewrite g_KQ, MS, app_nil_r. constructor; [|apply Forall_nil].
    apply g_vis_map; cbn [aeval]; rewrite g_lysec; zl. }
apply g_vis_old. right; left. intros x Hx. unfold aareas. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; right. exact Hx.
Qed.
Lemma g_vis_client : Forall (range_vis B lyF rd') (aclient SF).
Proof.
pose proof g_SF as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof g_ms as (MS1 & MS2 & MS3).
unfold aclient. rewrite Rfr, Rck, flat_map_app.
apply Forall_app; split; [apply Forall_app; split|].
- apply g_vis_old. do 2 right. intros x Hx. unfold aclient. apply in_app_iff. left. exact Hx.
- cbn [flat_map]. rewrite app_nil_r. unfold chunk_user. rewrite g_KST, g_KN. unfold ck_user. rewrite g_KB, g_KR. cbn [padd sptr_exp].
  constructor; [|apply Forall_nil]. apply g_vis_map; cbn [aeval]; rewrite g_lysec; unfold kPage; zl.
- apply g_vis_old. do 2 right. intros x Hx. unfold aclient. apply in_app_iff. right. exact Hx.
Qed.

(* ---- the shadow (AGjy.shadow_final) ---- *)
Let Vsh := AGif4.sf_Vsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vzs := AGif4.sf_Vzs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Let Vpb := AGif4.sf_Vpb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN.
Lemma g_MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ gXC a -> ~ (sp0 - ImgBaseAGS.AFSTACK <= a < sp0) ->
  mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a).
Proof.
intros a Ra NX NS. apply MEQF; rewrite w64_unsigned by exact Ra.
- intros Hw. unfold ImgBaseAGS.WIN, ImgBaseAGS.WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
  + exact (NS Hw).
  + apply NX. left. exact Hw.
  + apply NX. right; left. exact Hw.
  + apply NX. right; right; left. exact Hw.
  + apply NX. do 3 right; left. exact Hw.
  + apply NX. do 4 right; left. exact Hw.
- intros [Hg Hq]. apply NX. do 6 right. exact (conj Hg Hq).
- intros [Hs|Hd]; [apply NS; unfold ImgBaseAGS.DEP_STK, ImgBaseAGS.AFSTACK in *; zl | apply NX; do 5 right; left; exact Hd].
Qed.
Lemma g_not_app_sh : forall lo len a, in_app lo len -> lo <= a < lo + len -> ~ (SHADOW_OFF <= a < kHighMemBeg).
Proof. intros lo len a HA Ha X. ceil. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zl. Qed.
Lemma gX_sh : forall a, SHADOW_OFF <= a < kHighMemBeg -> ~ (SMn <= a < SMn + MSn / 8) -> ~ gXC a.
Proof.
intros a Ha N X.
pose proof (g_owned_app (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as EQ.
pose proof (g_owned_app (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as ET.
pose proof (g_owned_app (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as ENB.
pose proof (g_owned_app (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as ESB.
pose proof g_facts as (_ & MI & _). cbn [fst snd] in EQ, ET, ENB, ESB.
unfold gXC in X. destruct X as [X|[X|[X|[X|[X|[X|[_ X]]]]]]].
- refine (g_not_app_sh _ _ a ET _ Ha). pose proof (g_wint a X). unfold kThreadObjSize. zl.
- pose proof (g_wini a X). pose proof (g_img_range a (g_inst_img a ltac:(zl))) as IR. unfold SHADOW_OFF, kImgLo, kImgEnd in *. zl.
- exact (g_not_app_sh _ _ a EQ (g_qs a X) Ha).
- exact (g_not_app_sh _ _ a MI X Ha).
- exact (N X).
- destruct (DZ_LOC ly a LY IMG TSD X) as [Y|[Y|(Y & _)]].
  + exact (g_not_app_sh _ _ a ENB Y Ha).
  + exact (g_not_app_sh _ _ a ESB Y Ha).
  + pose proof (g_img_range a Y) as IR. unfold SHADOW_OFF, kImgLo, kImgEnd in *. zl.
- exact (g_not_app_sh _ _ a EQ (g_qr a X) Ha).
Qed.
Lemma g_M8 : mb mod 8 = 0 /\ MSn mod 8 = 0.
Proof.
pose proof g_facts as (MA & _). pose proof g_ms as (_ & MS2 & _). unfold page_aligned in MA.
split; [apply Z.mod_divide in MA as [p Hp0]; [|zl] | apply Z.mod_divide in MS2 as [p Hp0]; [|zl]];
  rewrite Hp0; replace (p * 4096) with ((p * 512) * 8) by zl; apply Z_mod_mult.
Qed.
Lemma g_sh_sep : forall g, g mod 8 = 0 -> (g + 8 <= mb \/ mb + MSn <= g) -> ~ (SMn <= shadow_addr g < SMn + MSn / 8).
Proof.
intros g Hg HM. rewrite g_SM. pose proof g_M8 as [M8 MM8]. unfold shadow_addr.
apply Z.mod_divide in Hg as [q Hq]; [|zl]. apply Z.mod_divide in M8 as [p Hp0]; [|zl]. apply Z.mod_divide in MM8 as [u Hu]; [|zl].
rewrite Hq, Hp0, Hu in HM |- *. rewrite !Z.div_mul by zl. zl.
Qed.
Lemma g_sh_map : forall j, shadow_addr (mb + 8 * j) = SMn + j.
Proof.
intros j. rewrite g_SM. pose proof g_M8 as [M8 _]. apply Z.mod_divide in M8 as [p Hp0]; [|zl].
unfold shadow_addr. rewrite Hp0. replace (p * 8 + 8 * j) with ((p + j) * 8) by zl. rewrite !Z.div_mul by zl. zl.
Qed.
Lemma g_sh_vis : forall a, SMn <= a < SMn + MSn / 8 -> w_H Wz (Z_to_bv 64 a) = false.
Proof. intros a Ha. exact (proj1 (PRsh a Ha)). Qed.
Lemma g_rd_byte : forall a v, 0 <= v < 256 -> w_H Wz (Z_to_bv 64 a) = false -> mem' (Z_to_bv 64 a) = Some (Z_to_bv 8 v) -> rd' a = Some v.
Proof. intros a v Hv Hh Hm. unfold aview, mbyte, mrestrict. rewrite Hh, Hm. cbn [option_map]. rewrite u8_small by exact Hv. reflexivity. Qed.
Lemma g_ck_base_lyF : forall k, In k (st_chunks S) -> ck_base B lyF k = ck_base B ly k.
Proof.
intros k Hk. unfold ck_base. apply (sptr_addr_le B ly lyF nS _ g_le). exact (g_chunk_lt k Hk).
Qed.
Lemma g_find_lyF : forall g, find_chunk_at B lyF (st_chunks S) g = find_chunk_at B ly (st_chunks S) g.
Proof.
intros g. assert (GEN : forall l, incl l (st_chunks S) -> find_chunk_at B lyF l g = find_chunk_at B ly l g).
{ induction l as [|k t IH]; intros INC; [reflexivity|]. cbn [find_chunk_at].
  rewrite (g_ck_base_lyF k (INC k (or_introl eq_refl))). rewrite IH; [reflexivity|]. intros x Hx. apply INC. right. exact Hx. }
apply GEN. intros x Hx. exact Hx.
Qed.
Lemma g_ck_new : ck_base B lyF KSc = mb + 4096.
Proof. unfold ck_base, sptr_addr. rewrite g_KB. cbn [sptr_exp aeval]. rewrite g_lysec. reflexivity. Qed.
Lemma g_KE : ck_extent KSc = MSn - 4096.
Proof. pose proof g_sizes as (ND & MS & RS & RZ & FP). unfold ck_extent. rewrite g_KQ, FP, MS. reflexivity. Qed.
Lemma in_rangesb_app_g : forall g l1 l2, in_rangesb g (l1 ++ l2) = (in_rangesb g l1 || in_rangesb g l2)%bool.
Proof. intros g l1 l2. induction l1 as [|[lo len] t IH]; [reflexivity|]. cbn [in_rangesb app]. rewrite IH, Bool.orb_assoc. reflexivity. Qed.
Lemma g_FPR : fa_poison_ranges lyF SF = fa_poison_ranges ly S ++ [(mb, MSn)].
Proof.
pose proof g_SF as (Rreg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof g_lyeqs as (_ & E2 & _).
pose proof g_sizes as (ND & MS & RS & RZ & FP).
pose proof g_le as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E15).
unfold fa_poison_ranges. rewrite Rck, flat_map_app, <- app_assoc.
apply (f_equal2 (@app (Z * Z))).
- apply flat_map_ext. intros c. rewrite ?Rreg. unfold region_base, fa_base. rewrite ?E2. reflexivity.
- apply (f_equal2 (@app (Z * Z))).
  + apply flat_map_ext_in_g. intros k Hk. pose proof (g_chunk_lt k Hk) as LT. destruct (ck_beg k) as [|o|r o|c p]; try reflexivity.
    rewrite (E15 r LT). reflexivity.
  + cbn [flat_map]. rewrite g_KB. cbv beta iota. rewrite g_KQ, MS, g_lysec. reflexivity.
Qed.
Lemma g_in_head_map : forall g, mb <= g < mb + MSn -> in_head Hp g = false.
Proof.
intros g Hg. unfold in_head. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hpin & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M) p Hpin) as (k & Hk & Hst & Ep & Hh).
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
rewrite G4 in Ep. unfold ck_n in Hh.
destruct (extent_zone_cf B ly S Hp _ k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
- pose proof (g_map_st (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. zl.
- pose proof (g_map_sec (m, len) Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kPage in *. zl.
Qed.
Lemma g_old_sep : forall g v, g mod 8 = 0 -> ashadow B ly S g = Some v -> ~ (SMn <= shadow_addr g < SMn + MSn / 8).
Proof.
intros g v Hg8 A0. apply g_sh_sep; [exact Hg8|]. pose proof g_M8 as [M8 _].
assert (ZN : (ly_prim ly <= g < ly_prim ly + kPrimResvSize) \/ (exists m len, In (m, len) (sec_extents ly S) /\ m <= g < m + len))
  by (eapply YG0tcf.ashadow_app_zone_cf; [exact M | exact A0]).
apply Z.mod_divide in Hg8 as [q Hq]; [|zl]. apply Z.mod_divide in M8 as [p Hp0]; [|zl].
destruct ZN as [[X1 X2]|(m & len & Hin & X1 & X2)].
- pose proof (g_map_st (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. zl.
- pose proof (g_map_sec (m, len) Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. zl.
Qed.
Lemma g_shadow_final : shadow_ok_cf B lyF Hp rd' SF.
Proof.
pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof g_sizes as (ND & MS & RS & RZ & FP). pose proof g_ms as (MS1 & MS2 & MS3).
pose proof g_M8 as [M8 MM8]. pose proof cf_malloc_max_bound as CMB.
intros g vv Hg8 HV. unfold ashadow in HV. rewrite Rck in HV.
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- assert (F0' : find_chunk_at B lyF (st_chunks S) g = Some k0) by (rewrite g_find_lyF; exact F0).
  rewrite (find_chunk_at_app1_g lyF _ _ _ _ F0') in HV.
  pose proof F0 as F0c. apply find_chunk_at_In in F0c as [Hk0 Hg0]. rewrite (g_ck_base_lyF k0 Hk0) in HV.
  assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0; exact HV).
  apply AGX; [exact (ashadow_owned_cf B ly S Hp _ g vv M A0) | | exact (amc_shadow _ _ _ _ _ M g vv Hg8 A0)].
  apply gX_sh; [eapply YG0tcf.ashadow_low_cf; [exact M | exact A0] | exact (g_old_sep g vv Hg8 A0)].
- assert (F0' : find_chunk_at B lyF (st_chunks S) g = None) by (rewrite g_find_lyF; exact F0).
  rewrite (find_chunk_at_app2_g lyF _ _ _ F0') in HV. cbn [find_chunk_at] in HV.
  rewrite g_ck_new, g_KE in HV.
  pose proof (Z.div_mod MSn 8 ltac:(zl)) as DM8.
  destruct ((mb + 4096 <=? g) && (g <? mb + 4096 + (MSn - 4096))) eqn:CK.
  + apply andb_prop in CK as [CK1 CK2]. apply Z.leb_le in CK1. apply Z.ltb_lt in CK2.
    injection HV as HV'. rewrite g_ck_new in HV'. unfold chunk_granule in HV'. rewrite g_KR, g_KN, g_KST in HV'.
    change (2048 / 8) with 256 in HV'.
    rewrite (g_in_head_map g ltac:(zl)).
    set (j := (g - (mb + 4096)) / 8) in HV'.
    assert (Hgj : g = mb + 8 * (512 + j)).
    { subst j. pose proof (Z.div_mod (g - (mb + 4096)) 8 ltac:(zl)) as D1.
      pose proof M8 as M8'. apply Z.mod_divide in M8' as [p Hp0]; [|zl]. pose proof Hg8 as Hg8'. apply Z.mod_divide in Hg8' as [q Hq]; [|zl].
      assert ((g - (mb + 4096)) mod 8 = 0) by (rewrite Hq, Hp0; replace (q * 8 - (p * 8 + 4096)) with ((q - p - 512) * 8) by zl; apply Z_mod_mult).
      zl. }
    rewrite Hgj, g_sh_map.
    assert (Jhi : j < MSn / 8 - 512) by zl.
    assert (N8 : ImgBaseAGS.N8D n / 8 = n / 8) by (unfold ImgBaseAGS.N8D; apply Z.div_mul; zl).
    pose proof (Z.div_mod n 8 ltac:(zl)) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(zl)) as MB.
    pose proof (Z.div_mod (n + 7) 8 ltac:(zl)) as DM7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zl)) as MB7.
    assert (J0 : 0 <= j) by (subst j; apply Z.div_pos; zl).
    assert (VIS : w_H Wz (Z_to_bv 64 (SMn + (512 + j))) = false) by (apply g_sh_vis; zl).
    pose proof (g_msh_band (SMn + (512 + j)) ltac:(zl)) as BB.
    assert (R64 : 0 <= SMn + (512 + j) < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in BB; zl).
    revert HV'. destruct (Z.ltb_spec j 256) as [J1|J1]; intros HV'; cbn beta iota in HV'.
    * subst vv. apply g_rd_byte; [unfold shHeapLeftRz; zl | exact VIS |]. apply Vsh. rewrite w64_unsigned by exact R64. left. zl.
    * revert HV'. destruct (Z.ltb_spec j (256 + n / 8)) as [J2|J2]; intros HV'; cbn beta iota in HV'.
      -- subst vv. apply g_rd_byte; [unfold shAddressable; zl | exact VIS |]. apply Vzs. rewrite w64_unsigned by exact R64. rewrite N8. zl.
      -- revert HV'. destruct ((j =? 256 + n / 8) && negb (n mod 8 =? 0)) eqn:PJ; intros HV'; cbn beta iota in HV'.
         ++ apply andb_prop in PJ as [PJ1 PJ2]. apply Z.eqb_eq in PJ1. apply Bool.negb_true_iff in PJ2. apply Z.eqb_neq in PJ2. subst vv.
            pose proof (vm_aview_g _ _ _ _ _ _ 0%nat (Vpb PJ2) ltac:(zl)) as X. rewrite Z.add_0_r in X.
            assert (EP : ImgBaseAGS.PBv n mb = SMn + (512 + j)).
            { unfold ImgBaseAGS.PBv, ImgBaseAGS.SMv. rewrite SHB_EQ. pose proof M8 as M8'. apply Z.mod_divide in M8' as [p Hp0]; [|zl].
              unfold ImgBaseAGS.N8D. rewrite Hp0. replace (p * 8 + 6144 + n / 8 * 8) with ((p + 768 + n / 8) * 8) by zl.
              rewrite !Z.div_mul by zl. zl. }
            rewrite <- EP, X. f_equal. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
            rewrite Z.shiftr_0_r. rewrite Z.mod_mod by zl. apply Z.mod_small. zl.
         ++ subst vv. apply g_rd_byte; [unfold shHeapLeftRz; zl | exact VIS |]. apply Vsh. rewrite w64_unsigned by exact R64. right.
            unfold ImgBaseAGS.UEv, ImgBaseAGS.SMv in *. rewrite SHB_EQ in *.
            assert (EU : (mb + 6144 + ImgBaseAGS.R8v n) / 8 = mb / 8 + 768 + (n + 7) / 8).
            { pose proof M8 as M8'. apply Z.mod_divide in M8' as [p Hp0]; [|zl]. unfold ImgBaseAGS.R8v. rewrite Hp0.
              replace (p * 8 + 6144 + (n + 7) / 8 * 8) with ((p + 768 + (n + 7) / 8) * 8) by zl. rewrite !Z.div_mul by zl. reflexivity. }
            rewrite EU. apply Bool.andb_false_iff in PJ.
            destruct PJ as [PJ|PJ]; [apply Z.eqb_neq in PJ | apply Bool.negb_false_iff in PJ; apply Z.eqb_eq in PJ]; zl.
  + rewrite g_FPR, in_rangesb_app_g in HV.
    destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR.
    * cbn [orb] in HV. assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0, IR; exact HV).
      apply AGX; [exact (ashadow_owned_cf B ly S Hp _ g vv M A0) | | exact (amc_shadow _ _ _ _ _ M g vv Hg8 A0)].
      apply gX_sh; [eapply YG0tcf.ashadow_low_cf; [exact M | exact A0] | exact (g_old_sep g vv Hg8 A0)].
    * cbn [orb in_rangesb] in HV. rewrite Bool.orb_false_r in HV.
      destruct ((mb <=? g) && (g <? mb + MSn)) eqn:HIMr; [|discriminate HV]. injection HV as <-.
      apply andb_prop in HIMr as [IM1 IM2]. apply Z.leb_le in IM1. apply Z.ltb_lt in IM2.
      rewrite (g_in_head_map g ltac:(zl)).
      apply Bool.andb_false_iff in CK.
      assert (GH : g < mb + 4096) by (destruct CK as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; zl).
      set (j := (g - mb) / 8).
      assert (Hgj : g = mb + 8 * j).
      { subst j. pose proof (Z.div_mod (g - mb) 8 ltac:(zl)) as D1.
        pose proof M8 as M8'. apply Z.mod_divide in M8' as [p Hp0]; [|zl]. pose proof Hg8 as Hg8'. apply Z.mod_divide in Hg8' as [q Hq]; [|zl].
        assert ((g - mb) mod 8 = 0) by (rewrite Hq, Hp0; replace (q * 8 - p * 8) with ((q - p) * 8) by zl; apply Z_mod_mult).
        zl. }
      assert (J0 : 0 <= j) by (subst j; apply Z.div_pos; zl).
      rewrite Hgj, g_sh_map.
      pose proof (g_msh_band (SMn + j) ltac:(zl)) as BB.
      assert (R64 : 0 <= SMn + j < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in BB; zl).
      apply g_rd_byte; [unfold shHeapLeftRz; zl | apply g_sh_vis; zl |].
      apply Vsh. rewrite w64_unsigned by exact R64. left. zl.
Qed.

(* ---- the zero shadow (AGjy.zshadow_final) ---- *)
Lemma g_shz : forall lo len i, 0 <= lo -> 0 <= len -> lo + len <= kHighMemEnd -> 0 <= i < len / 8 ->
  SHADOW_OFF <= shadow_addr lo + i < kHighMemBeg.
Proof.
intros lo len i H0 H1 H2 Hi. clear - H0 H1 H2 Hi. unfold shadow_addr.
pose proof (Z.div_mod lo 8 ltac:(zl)). pose proof (Z.mod_pos_bound lo 8 ltac:(zl)).
pose proof (Z.div_mod len 8 ltac:(zl)). pose proof (Z.mod_pos_bound len 8 ltac:(zl)).
unfold SHADOW_OFF, kHighMemBeg, kHighMemEnd in *. zl.
Qed.
Lemma g_zshadow_final : zshadow_ok B lyF rd'.
Proof.
pose proof g_lyeqs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _).
assert (EZ : zero_shadow_ranges B lyF = zero_shadow_ranges B ly) by (unfold zero_shadow_ranges; rewrite E10, E11; reflexivity).
pose proof g_M8 as [M8 MM8].
unfold zshadow_ok. rewrite EZ. apply Forall_forall. intros r Hr i Hi.
change (shadow_of_addr SHADOW_OFF (fst r)) with (shadow_addr (fst r)).
pose proof (proj1 (Forall_forall _ _) (amc_zshadow _ _ _ _ _ M) r Hr i Hi) as Z0.
change (shadow_of_addr SHADOW_OFF (fst r)) with (shadow_addr (fst r)) in Z0.
apply (AGX _ (own_shadow_zero_cf B ly S Hp _ r i M Hr Hi)); [| exact Z0].
assert (RF : (fst r) mod 8 = 0 /\ 0 <= fst r /\ 0 <= snd r /\ zdisjoint (mb, MSn) r /\ fst r + snd r <= kHighMemEnd).
{ unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
  - pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). cbn [fst snd].
    pose proof (g_map_st (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as D.
    unfold page_aligned in T5. apply Z.mod_divide in T5 as [q Hq]; [|zl].
    split; [rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by zl; apply Z_mod_mult|].
    unfold zdisjoint in *. cbn [fst snd] in *. unfold kHighMemBeg, kHighMemEnd in *. zl.
  - pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ M)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
    pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; right; exact Hr)) as [S1 S2].
    pose proof (g_map_st (ly_img ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as D.
    split; [exact Z3|]. split; [exact Z1|]. split; [exact Z2|]. split; [|unfold kLowMemEnd, kHighMemEnd in *; zl].
    unfold zdisjoint in *. cbn [fst snd] in *. zl. }
destruct RF as (R1 & R2 & R3 & R4 & R5).
apply gX_sh; [exact (g_shz (fst r) (snd r) i R2 R3 R5 Hi)|].
rewrite g_SM. unfold shadow_addr. unfold zdisjoint in R4. cbn [fst snd] in R4.
apply Z.mod_divide in R1 as [q Hq]; [|zl]. apply Z.mod_divide in M8 as [p Hp0]; [|zl]. apply Z.mod_divide in MM8 as [u Hu]; [|zl].
pose proof (Z.div_mod (snd r) 8 ltac:(zl)). pose proof (Z.mod_pos_bound (snd r) 8 ltac:(zl)).
rewrite Hq, Hp0, Hu in R4 |- *. rewrite !Z.div_mul by zl. zl.
Qed.

(* ---- the placement of the grown layout ---- *)
Lemma g_SEF_any : forall g, sec_extents lyF (AGif4.SFSz S n tr z g) = sec_extents ly S ++ [(mb, MSn)].
Proof.
intros g. pose proof g_sizes as (ND & MS & RS & RZ & FP).
assert (Rck : st_chunks (AGif4.SFSz S n tr z g) = st_chunks S ++ [KSc]) by reflexivity.
unfold sec_extents at 1. rewrite Rck, flat_map_app. pose proof (sec_extents_le_cf ly lyF S _ _ _ _ g_le WF) as SE.
unfold sec_extents in SE at 1. rewrite SE. cbn [flat_map]. rewrite g_KB. cbv beta iota. rewrite g_KQ, MS, g_lysec, app_nil_r. reflexivity.
Qed.
Lemma g_placed_any : forall g, sec_placed lyF (AGif4.SFSz S n tr z g).
Proof.
intros g. pose proof PL as [PF PD]. pose proof g_facts as (MA & MI & MC & _). pose proof g_static as (ES & _).
unfold sec_placed. rewrite g_SEF_any, ES. split.
- apply Forall_app. split; [exact PF|]. constructor; [|apply Forall_nil]. cbn [fst snd]. split; [exact MA|]. split; [exact MI|].
  unfold ASAN_CEIL in MC. exact MC.
- apply YG0s.pairwise_app_inv in PD as (P1 & P2 & P3).
  rewrite <- app_assoc. apply YG0s.pairwise_app; [exact P1 | |].
  + apply YG0s.pairwise_app; [cbn; split; [apply Forall_nil | exact I] | exact P2 |].
    intros x y [<-|[]] Hy. exact (g_map_st y Hy).
  + intros x y Hx Hy. apply in_app_iff in Hy as [[<-|[]]|Hy]; [apply zdj_sym; exact (g_map_sec x Hx) | exact (P3 x y Hx Hy)].
Qed.
Lemma g_noncap : is_errb_cap (mkSec MSn (ImgBaseAGS.NDv n) true) = false.
Proof. pose proof g_sizes as (ND & _). rewrite <- ND. apply sec_entry_noncap. Qed.
Lemma g_secs_any : forall g, st_secs (AGif4.SFSz S n tr z g) = st_secs S ++ [mkSec MSn (ImgBaseAGS.NDv n) true].
Proof. reflexivity. Qed.
Lemma g_EC_any : forall g, errb_cap_cf (AGif4.SFSz S n tr z g) = errb_cap_cf S.
Proof.
intros g. unfold errb_cap_cf, errb_e. rewrite g_secs_any, filter_app. cbn [filter]. rewrite g_noncap, app_nil_r. reflexivity.
Qed.
Lemma g_EZ_any : forall g, errb_zone lyF (AGif4.SFSz S n tr z g) = errb_zone ly S.
Proof.
intros g. unfold errb_zone. rewrite (xs_cf_app_noncap lyF S _ _ (g_secs_any g) g_noncap). exact (xs_cf_layout ly lyF S g_le).
Qed.
Lemma g_xs_placed_any : forall g, xs_placed_cf lyF (AGif4.SFSz S n tr z g).
Proof.
intros g. pose proof (amc_xs_placed _ _ _ _ _ M) as XP. pose proof g_facts as (_ & _ & MC & _). pose proof alloc_ceiling_lt as CL.
apply (xs_placed_cf_sec_grow lyF S (AGif4.SFSz S n tr z g) (mkSec MSn (ImgBaseAGS.NDv n) true) (g_secs_any g) g_noncap);
  [| exact (xs_placed_cf_layout _ 0 0 0 ly lyF S WF g_le XP)].
intros z0 Hz0. rewrite g_SEF_any in Hz0. apply in_app_iff in Hz0 as [Hz0|[<-|[]]].
- left. rewrite (sec_extents_le_cf ly lyF S _ _ _ _ g_le WF). exact Hz0.
- right. rewrite (xs_cf_layout ly lyF S g_le).
  apply (xs_fresh_of_grant ly S (with_vm_backing (m_vm_lazy md0) mat md0) mb MSn XP
    (xs_mapped_cf_wvb ly S md0 (m_vm_lazy md0) mat XSM) GOK); [zl | pose proof g_ms; zl | unfold ASAN_CEIL in MC; zl].
Qed.

(* ---- the hidden-shadow facts (AGjy.ahs_final) ---- *)
Lemma g_stk_not_band : forall a, ~ (sp0 - ImgBaseAGS.AFSTACK <= a < sp0) \/ ~ in_band_rw a.
Proof.
intros a. destruct (zr_dec (sp0 - ImgBaseAGS.AFSTACK) sp0 a) as [D|D]; [right|left; exact D].
pose proof (lo_stk_ceil ly LY) as SC. ceil. intros HB. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, ImgBaseAGS.AFSTACK, ASAN_CEIL in *. zl.
Qed.
Lemma g_ahs : ahs B lyF SF (w_H Wz) mem'.
Proof.
pose proof HAR as (_ & _ & _ & _ & [HS0 HZ0]).
pose proof g_SF as (_ & _ & _ & Rfr & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof g_static as (ES & EV0 & _). pose proof g_lyeqs as (_ & _ & _ & _ & _ & E6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & E16 & _).
split.
- intros a Ha NC HV.
  assert (Ra : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; zl).
  assert (B0 : mem0 (w64 a) <> None).
  { apply (HS0 a Ha).
    - intros CL. apply NC. destruct CL as [(k & Hk & Hst & Hr) | (cq & Hcq & Hr)].
      + left. exists k. split; [rewrite Rck; apply in_app_iff; left; exact Hk | split; [exact Hst|]].
        unfold ck_user. rewrite (sptr_addr_le B ly lyF nS _ g_le); [exact Hr|].
        pose proof (g_chunk_lt k Hk) as LT. destruct (ck_beg k); cbn; try exact I. exact LT.
      + right. exists cq. split; [rewrite Rfr; exact Hcq|]. unfold frame_addr in Hr |- *. rewrite E6. exact Hr.
    - destruct HV as [Hh|Hv]; [left | right].
      + match goal with |- w_H W ?x = true => destruct (w_H W x) eqn:E; [reflexivity|] end. rewrite (MON _ E) in Hh. discriminate Hh.
      + unfold in_vis0 in Hv |- *. rewrite E16 in Hv. exact Hv. }
  destruct (zr_dec SMn (SMn + MSn / 8) a) as [D|D].
  + destruct (PRsh a D) as [_ [b Hb]]. unfold YG0n.w64. rewrite Hb. discriminate.
  + unfold YG0n.w64 in B0 |- *. rewrite (g_MEQ a Ra (gX_band a Ha D)); [exact B0|].
    destruct (g_stk_not_band a) as [X|X]; [exact X | exfalso; exact (X Ha)].
- intros g Hg Happ HF.
  unfold hfree in HF. rewrite g_SEF_any, ES, EV0 in HF. rewrite !app_assoc in HF. apply Forall_app in HF as [HF1 HF2].
  pose proof (Forall_inv HF2) as X. cbn [fst snd] in X.
  assert (HF0 : hfree ly S g) by (unfold hfree; rewrite !app_assoc; exact HF1).
  pose proof (shadow_addr_in_band g 8 0 Happ ltac:(zl)) as HB. rewrite Z.add_0_r in HB.
  assert (Ra : 0 <= shadow_addr g < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in HB; zl).
  rewrite <- (HZ0 g Hg Happ HF0). unfold YG0n.w64.
  apply g_MEQ; [exact Ra | apply gX_band; [exact HB | exact (g_sh_sep g Hg X)] |].
  destruct (g_stk_not_band (shadow_addr g)) as [Y|Y]; [exact Y | exfalso; exact (Y HB)].
Qed.

(* ---- the owned set at the pre-state and at the final state (AGif5.own_*g / NEWOWN) ---- *)
Lemma g_own_T : forall a, ImgBaseAGS.WINT ly a -> aowned B ly S a.
Proof.
intros a Ha. pose proof (g_wint a Ha).
apply (own_core_cf B ly S Hp _ (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; unfold kThreadObjSize; zl].
Qed.
Lemma g_own_I : forall a, ImgBaseAGS.WINI regs0 n a -> aowned B ly S a.
Proof.
intros a Ha. pose proof (g_wini a Ha).
apply (own_area_cf B ly S Hp _ (as_inst B, 3632) a M); [unfold asyms_areas; cbn; tauto | cbn [fst snd]; zl].
Qed.
Lemma g_own_Q : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> aowned B ly S a.
Proof. intros a Ha. apply (own_core_cf B ly S Hp _ (ly_Q ly, kPtrArrayResv) a M); [unfold core_extents; cbn; tauto | exact Ha]. Qed.
Lemma g_own_D : forall a, ims_dzone ly a -> aowned B ly S a.
Proof.
intros a Hd. destruct (DZ_LOC ly a LY IMG TSD Hd) as [X|[X|(X & _)]].
- apply (own_core_cf B ly S Hp _ (ly_NB ly, kNodesBlockSize) a M); [unfold core_extents; cbn; tauto | exact X].
- apply (own_core_cf B ly S Hp _ (ly_SB ly, kStoreBlockSize) a M); [unfold core_extents; cbn; tauto | exact X].
- apply (own_static_cf B ly S Hp _ a M). exact (DZ_OWN ly a LY IMG TSD Hd X).
Qed.
Lemma g_band_core : forall a, (SHADOW_OFF <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd) ->
  Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8))
    (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]).
Proof.
intros a Ha. apply Exists_exists. pose proof hm_zone_shadow as [E1 E2].
destruct Ha as [LO|HI].
- exists lm_zone. split; [repeat (apply in_app_iff; right); right; left; reflexivity|].
  unfold in_zr, lm_zone, shadow_addr. cbn [fst snd].
  change ((kLowMemEnd + 7) / 8) with 268431360. change (0 / 8) with 0. unfold SHADOW_OFF, kLowShadowEnd in *. zl.
- exists hm_zone. split; [repeat (apply in_app_iff; right); left; reflexivity|].
  unfold in_zr. cbn [fst snd] in *. rewrite E1. rewrite E1 in E2. zl.
Qed.
Lemma g_own_SH : forall a, SMn <= a < SMn + MSn / 8 -> aowned B ly S a.
Proof.
intros a Ha. pose proof (g_msh_band a Ha) as HB. pose proof g_M8 as [M8 MM8]. pose proof g_facts as (_ & MI & MC & _).
assert (A0 : SHADOW_OFF <= a) by (rewrite g_SM in Ha; unfold shadow_addr in Ha; pose proof (Z.div_pos mb 8 ltac:(zl) ltac:(zl)); zl).
split; [do 4 right; apply g_band_core; unfold in_band_rw in HB; zl|].
apply (nc_shadow_cf B ly S Hp _ a mb MSn M M8); [zl | ceil; unfold ASAN_CEIL, kHighMemEnd in *; zl | |].
- apply g_map_st. unfold static_extents, owned_extents. apply in_app_iff. left. cbn. tauto.
- rewrite <- g_SM. pose proof (Z.div_mod MSn 8 ltac:(zl)). pose proof (Z.div_mod (MSn + 7) 8 ltac:(zl)).
  pose proof (Z.mod_pos_bound (MSn + 7) 8 ltac:(zl)). zl.
Qed.
Lemma g_own_BAND : forall a, (SHADOW_OFF <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd) ->
  w_H W (Z_to_bv 64 a) = true -> aowned B ly S a.
Proof.
intros a Ha Hh. split; [do 4 right; apply g_band_core; exact Ha|].
assert (HB : in_band_rw a) by (unfold in_band_rw, SHADOW_OFF, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; zl).
intros C. apply (client_band_vis_cf B ly S Hp _ a M HB C). eapply YG0q.aview_band_hidden; [| exact HB | exact Hh].
intros sg Hsg. eapply al_img_env_cf; [exact LY | exact L | exact Hsg].
Qed.
Lemma g_newown : forall a, mb <= a < mb + MSn -> ~ (ImgBaseAGS.Uv mb <= a < ImgBaseAGS.Uv mb + n) -> aowned B lyF SF a.
Proof.
intros a Ha Hnu. pose proof g_SF as (_ & _ & _ & Rfr & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof g_lyeqs as (_ & _ & _ & _ & _ & E6 & _).
split.
- do 3 right. left. rewrite (g_SEF_any grow). apply Exists_exists. exists (mb, MSn).
  split; [apply in_app_iff; right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
- intros [(k & Hk & Hst & Hr)|(cq & Hcq & Hr)].
  + rewrite Rck in Hk. apply in_app_iff in Hk as [Hk|[<-|[]]].
    * unfold ck_user in Hr. rewrite (sptr_addr_le B ly lyF nS _ g_le) in Hr;
        [| pose proof (g_chunk_lt k Hk) as LT; destruct (ck_beg k); cbn; try exact I; exact LT].
      fold (ck_user k) in Hr. pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
      rewrite G4 in Hr. unfold ck_n in Hr.
      destruct (extent_zone_cf B ly S Hp _ k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
      -- pose proof (g_map_st (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
         unfold zdisjoint in D. cbn [fst snd] in D. zl.
      -- pose proof (g_map_sec (m, len) Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kPage in *. zl.
    * apply Hnu. unfold ck_user in Hr. rewrite g_KB, g_KR in Hr. rewrite g_KN in Hr. cbn [padd sptr_addr sptr_exp aeval] in Hr.
      rewrite g_lysec in Hr. unfold ImgBaseAGS.Uv. unfold kPage in Hr. zl.
  + rewrite Rfr in Hcq. destruct cq as [cid pos]. cbn [fst snd] in Hr.
    pose proof (frame_facts_cf B ly S Hp _ cid pos M Hcq) as (C1 & C2 & F1 & F2 & FA & P1 & P2 & P3 & P4 & _).
    pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(zl) ltac:(zl)).
    unfold frame_addr, in_zr in Hr. rewrite E6 in Hr. cbn [fst snd] in Hr.
    pose proof (g_map_st (ly_F ly, kFakeStackSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. pose proof g_facts as (_ & MI & _).
    destruct Hr as [Hr|Hr]; [unfold kFakeFramesOff in *; zl|].
    refine (g_not_app_sh mb MSn a MI Ha _).
    unfold in_app in F1. ceil. unfold shadow_addr in Hr.
    pose proof (Z.div_mod (ly_F ly + fs_frame_off cid pos) 8 ltac:(zl)). pose proof (Z.mod_pos_bound (ly_F ly + fs_frame_off cid pos) 8 ltac:(zl)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(zl)). pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(zl)).
    unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, ASAN_CEIL, kFakeFramesOff in *. zl.
Qed.

(* ---- the ledger of the grown layout at the kernel's model (AGif5.LED0 / LED1) ---- *)
Lemma nores50_g : mmap_noreserve_b (Z_to_bv 64 50) = false. Proof. reflexivity. Qed.
Lemma grant_piece_shape_g : forall (a k : word) md, let md' := grant_md false (Z_to_bv 64 50) a k md in
  vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) /\
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md) /\
  vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md).
Proof.
intros a k md. cbv zeta. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing.
rewrite nores50_g. cbn. destruct md as [fd [maps lazy mt] io fs pr lim tm]. cbn. destruct maps; cbn. repeat split; reflexivity.
Qed.
Lemma ite_res_g : forall (g : bool) (r : Z), 8 * (if g then r + kPtrArrayEntriesPerCommit else r) = 8 * r + (if g then 131072 else 0).
Proof. intros g r. destruct g; unfold kPtrArrayEntriesPerCommit; zl. Qed.
Lemma g_ledger : forall (g : bool) matV mat' mdz, (g = true -> idx = res) ->
  mdz = AGif4.sec_md g md0 mat matV mat' mb MSn QSn ->
  amwf (mmap_model (w64 mb) (w64 MSn) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
  (g = true -> eager_used mdz <= eager_used (mmap_model (w64 mb) (w64 MSn) (with_vm_backing (m_vm_lazy md0) mat md0)) + 131072) ->
  ALedger_cf im_segs lyF (AGif4.SFSz S n tr z g) mdz.
Proof.
intros g matV mat' mdz Hidx Emdz MW2 EG.
pose proof (proj1 (proj2 (proj2 (proj2 HAR)))) as MW0.
set (mdN := with_vm_backing (m_vm_lazy md0) mat md0) in *.
assert (MWN : amwf mdN) by (apply (amwf_same md0); [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW0]).
pose proof g_ms as (MS1 & MS2 & MS3). pose proof cf_malloc_max_bound as CMB.
assert (UMS : bv_unsigned (w64 MSn) = MSn) by (apply w64_unsigned; zl).
assert (L0 : ALedger_cf im_segs lyF (AGif4.SFSz S n tr z false) (mmap_model (w64 mb) (w64 MSn) mdN)).
{ apply (ALedger_anon_cf ly S (AGif4.SFSz S n tr z false) mdN (w64 mb) (w64 MSn) rS0 mb LY WF PL MWN LN).
  - rewrite UMS. exact GOK.
  - rewrite UMS. zl.
  - rewrite UMS. exact MS2.
  - intros c Hc. reflexivity.
  - reflexivity.
  - rewrite g_umb, UMS. exact (g_SEF_any false).
  - reflexivity.
  - exact (g_EZ_any false).
  - exact (g_EC_any false). }
destruct g.
- unfold AGif4.sec_md in Emdz. cbv zeta in Emdz. subst mdz.
  set (md2 := mmap_model (w64 mb) (w64 MSn) mdN) in *.
  set (mdV := with_vm_backing (m_vm_lazy md2) matV md2).
  set (md5 := grant_md false (Z_to_bv 64 50) (w64 QSn) (w64 131072) mdV).
  apply ALedger_same_cf with (md := md5); [| apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
  pose proof (grant_piece_shape_g (w64 QSn) (w64 131072) mdV) as (VM & RES & LIM & MMB & ISP). cbv zeta in VM, RES, LIM, MMB, ISP.
  assert (MWV : amwf mdV) by (apply (amwf_same md2); [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW2]).
  assert (LV : ALedger_cf im_segs lyF (AGif4.SFSz S n tr z false) mdV)
    by (apply ALedger_same_cf with (md := md2); [exact L0 | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb]).
  pose proof (Hidx eq_refl) as EIR. pose proof g_res as [HR1 HR2].
  pose proof (g_owned_app (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as EQA. cbn [fst snd] in EQA.
  assert (UQa : bv_unsigned (w64 QSn) = QSn).
  { apply w64_unsigned. unfold ImgBaseAGS.QSv. ceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl. }
  assert (UQb : bv_unsigned (w64 131072) = 131072) by (apply w64_unsigned; zl).
  apply (ALedger_qcommit_cf lyF (AGif4.SFSz S n tr z false) (AGif4.SFSz S n tr z true) mdV md5).
  + exact g_lyok.
  + rewrite g_SEF_any. apply Forall_app. split; [exact (sec_extents_sizes64P_cf (as_universe B) 0 0 0 ly S WF)|].
    constructor; [|constructor]. cbn [snd]. zl.
  + exact (g_placed_any false).
  + exact (g_xs_placed_any false).
  + exact LV.
  + exact VM.
  + exact RES.
  + exact LIM.
  + exact MMB.
  + exact ISP.
  + intros x Hx. destruct MWV as [(W1 & W2 & W3 & _ & W5) _].
    apply (YG0j.cov_grant_md false (Z_to_bv 64 50) (w64 QSn) (w64 131072) mdV x).
    * unfold YK0g.model_ivs_wf. split; [|split; [|split; [|exact W5]]]; intros q Hq; [exact (W1 q Hq) | exact (W2 q Hq) | exact (W3 q Hq)].
    * rewrite UQa, UQb. unfold ImgBaseAGS.QSv. ceil.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl.
    * rewrite UQa, UQb. intros Hin. apply Hx. pose proof g_lyeqs as (_ & _ & EQ & _). rewrite EQ.
      unfold ImgBaseAGS.QSv in Hin. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl.
  + pose proof (EG eq_refl) as E. rewrite eager_used_wvb in E. eapply Z.le_trans; [exact E|].
    unfold mdV. rewrite eager_used_wvb. unfold kPtrArrayEntriesPerCommit. zl.
  + intros c Hc. reflexivity.
  + rewrite !g_SEF_any. reflexivity.
  + reflexivity.
  + reflexivity.
  + rewrite !g_EZ_any. reflexivity.
  + rewrite !g_EC_any. reflexivity.
  + exact (YG0g.naf_grant_md false (Z_to_bv 64 50) mdV _ _ MWV).
  + destruct MWV as [(W1 & W2 & W3 & _ & W5) _].
    apply YGcfLazyMaps.lazy_in_maps_grant_fixed_cf.
    * exact (alc_lazy_in_maps _ _ _ _ LV).
    * intros q Hq. exact (W2 q Hq).
    * intros q Hq. exact (W3 q Hq).
    * rewrite UQa, UQb. unfold ImgBaseAGS.QSv. ceil.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl.
    * intros x Hx. rewrite UQa, UQb in Hx. pose proof (alc_Q _ _ _ _ LV) as HQ. pose proof g_lyeqs as (_ & _ & EQ & _).
      rewrite EQ in HQ. apply (cov_of_in_wiv _ _ x HQ); cbn [fst snd]; unfold ImgBaseAGS.QSv in Hx; ceil;
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kPtrArrayEntriesPerCommit in *; zl.
- unfold AGif4.sec_md in Emdz. cbv zeta in Emdz. subst mdz.
  apply ALedger_same_cf with (md := mmap_model (w64 mb) (w64 MSn) mdN); [exact L0 | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
Qed.

(* ---- the kernel's effect (AGif4.skern's fields), and ARcf of the final state (AGjy.AR_transport) ---- *)
Variables (mdz : Model) (matV mat' : list word).
Hypothesis EMDZ : mdz = AGif4.sec_md grow md0 mat matV mat' mb MSn QSn.
Hypothesis MW2 : amwf (mmap_model (w64 mb) (w64 MSn) (with_vm_backing (m_vm_lazy md0) mat md0)).
Hypothesis EGr : grow = true -> eager_used mdz <= eager_used (mmap_model (w64 mb) (w64 MSn) (with_vm_backing (m_vm_lazy md0) mat md0)) + 131072.
Hypothesis MWz : amwf mdz.
Hypothesis ABz : A_bytes (w_A Wz) = A_bytes (w_A W) + MSn + (AGif4.SHHI mb MSn - AGif4.SHLO mb) + (if grow then 131072 else 0).
Hypothesis INCz : forall i, In i (w_A W) -> In i (w_A Wz).
Hypothesis AMAPz : In (mb, mb + MSn) (w_A Wz).
Hypothesis AHULLz : In (AGif4.SHLO mb, AGif4.SHHI mb MSn) (w_A Wz).
Hypothesis OUTz : forall x : word, ~ (mb <= bv_unsigned x < mb + MSn) -> ~ (AGif4.SHLO mb <= bv_unsigned x < AGif4.SHHI mb MSn) ->
  ~ (grow = true /\ QSn <= bv_unsigned x < QSn + 131072) -> w_H Wz x = w_H W x.

Lemma g_SH_hull : AGif4.SHLO mb <= shadow_addr mb /\ shadow_addr mb + MSn / 8 <= AGif4.SHHI mb MSn /\
  AGif4.SHHI mb MSn - AGif4.SHLO mb <= MSn / 8 + 8192.
Proof.
unfold AGif4.SHLO, AGif4.SHHI.
pose proof (Z.div_mod (shadow_addr mb) 4096 ltac:(zl)) as D1. pose proof (Z.mod_pos_bound (shadow_addr mb) 4096 ltac:(zl)) as B1.
pose proof (Z.div_mod (shadow_addr mb + MSn / 8 + 4095) 4096 ltac:(zl)) as D2.
pose proof (Z.mod_pos_bound (shadow_addr mb + MSn / 8 + 4095) 4096 ltac:(zl)) as B2.
zl.
Qed.
Lemma g_sec_live : sec_live_bytes SF = sec_live_bytes S + MSn /\ sec_live_hulls SF = sec_live_hulls S + Z.max 0 (MSn / 8 + 8192).
Proof.
pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof g_sizes as (_ & MS & _).
assert (G1 : forall l a, fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) a l =
  fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 l + a).
{ intros l a. induction l as [|k t IH]; cbn [fold_right]; [zl|]. rewrite IH. destruct (ck_beg k); zl. }
assert (G2 : forall l a, fold_right (fun k acc => match ck_beg k with PSec _ _ => Z.max 0 (sec_map_size (ck_req k) / 8 + 8192) + acc | _ => acc end) a l =
  fold_right (fun k acc => match ck_beg k with PSec _ _ => Z.max 0 (sec_map_size (ck_req k) / 8 + 8192) + acc | _ => acc end) 0 l + a).
{ intros l a. induction l as [|k t IH]; cbn [fold_right]; [zl|]. rewrite IH. destruct (ck_beg k); zl. }
unfold sec_live_bytes, sec_live_hulls. rewrite Rck, !fold_right_app. cbn [fold_right]. rewrite !g_KB. cbv beta iota. rewrite !g_KQ, MS.
split; [rewrite G1 | rewrite G2]; zl.
Qed.
Lemma g_xsm : xs_mapped_cf lyF SF mdz.
Proof.
rewrite EMDZ. unfold AGif4.sec_md.
exact (xs_mapped_cf_sec_grant_chain ly S md0 lyF SF _ grow mat matV mat' mb MSn QSn (Z_to_bv 64 50) g_le (g_secs_any grow) g_noncap XSM).
Qed.

(* ---- the frame clauses (AGif5.frame_grant / frame_grant_raw) ---- *)
Lemma g_hull_band : forall a, AGif4.SHLO mb <= a < AGif4.SHHI mb MSn ->
  (SHADOW_OFF <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd).
Proof.
intros a Ha. pose proof g_facts as (_ & MI & MC & _). pose proof g_M8 as [M8 MM8]. ceil.
unfold AGif4.SHLO, AGif4.SHHI, shadow_addr in Ha.
pose proof (Z.div_mod mb 8 ltac:(zl)). pose proof (Z.div_mod MSn 8 ltac:(zl)).
pose proof (Z.div_mod (SHADOW_OFF + mb / 8) 4096 ltac:(zl)). pose proof (Z.mod_pos_bound (SHADOW_OFF + mb / 8) 4096 ltac:(zl)).
pose proof (Z.div_mod (SHADOW_OFF + mb / 8 + MSn / 8 + 4095) 4096 ltac:(zl)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + mb / 8 + MSn / 8 + 4095) 4096 ltac:(zl)).
unfold in_app, SHADOW_OFF, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. zl.
Qed.
Lemma g_frame_raw : forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B lyF SF (bv_unsigned x) ->
  ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) -> ~ (ImgBaseAGS.Uv mb <= bv_unsigned x < ImgBaseAGS.Uv mb + req_size n) ->
  mem' x = mem0 x.
Proof.
intros x NO NO' NS NE. pose proof g_sizes as (_ & _ & RS & _). rewrite RS in NE.
assert (NST : ~ (sp0 - ImgBaseAGS.AFSTACK <= bv_unsigned x < sp0))
  by (intros Hs; apply NS; left; unfold spZ, AFSTACK_G; unfold ImgBaseAGS.AFSTACK in Hs; exact Hs).
apply MEQF.
- intros Hw. unfold ImgBaseAGS.WIN, ImgBaseAGS.WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
  + exact (NST Hw).
  + exact (NO (g_own_T _ Hw)).
  + exact (NO (g_own_I _ Hw)).
  + exact (NO (g_own_Q _ (g_qs _ Hw))).
  + exact (NO' (g_newown _ Hw NE)).
  + exact (NO (g_own_SH _ Hw)).
- intros [_ Hq]. exact (NO (g_own_Q _ (g_qr _ Hq))).
- intros [Hs|Hd]; [apply NST; unfold ImgBaseAGS.DEP_STK, ImgBaseAGS.AFSTACK in *; zl | exact (NO (g_own_D _ Hd))].
Qed.
Lemma g_frame_view : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B lyF SF a ->
  ~ ascratch B AFSTACK_G regs0 a -> ~ (ImgBaseAGS.Uv mb <= a < ImgBaseAGS.Uv mb + req_size n) ->
  aview im_segs (w_H Wz) mem' a = aview im_segs (w_H W) mem0 a.
Proof.
intros a Ra NO NO' NS NE.
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply w64_unsigned; exact Ra).
assert (MEQa : mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)) by (apply g_frame_raw; rewrite Ux; assumption).
pose proof g_sizes as (_ & _ & RS & _). rewrite RS in NE.
destruct (w_H W (Z_to_bv 64 a)) eqn:EhW.
- destruct (w_H Wz (Z_to_bv 64 a)) eqn:EhZ.
  + unfold aview, mbyte, mrestrict. rewrite EhW, EhZ. reflexivity.
  + exfalso. destruct (zr_dec mb (mb + MSn) a) as [D1|D1]; [exact (NO' (g_newown a D1 NE))|].
    destruct (zr_dec (AGif4.SHLO mb) (AGif4.SHHI mb MSn) a) as [D2|D2].
    { apply NO. exact (g_own_BAND a (g_hull_band a D2) EhW). }
    destruct (zr_dec QSn (QSn + 131072) a) as [D3|D3].
    { apply NO. apply g_own_Q. pose proof g_res as [HR _]. unfold ImgBaseAGS.QSv, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl. }
    rewrite (OUTz (Z_to_bv 64 a)) in EhZ; [congruence | rewrite Ux; exact D1 | rewrite Ux; exact D2 | rewrite Ux; intros [_ X]; exact (D3 X)].
- pose proof (MON _ EhW) as EhZ. unfold aview, mbyte, mrestrict. rewrite EhW, EhZ, MEQa. reflexivity.
Qed.

(* ---- the two machine cells of ARX_cf at the grown layout (YGcfInstBase.exh_cell_cf / errb_cells_cf) ---- *)
(* A byte outside the write set, the stack window, the map, the shadow hull and the pointer-array commit reads the same
   at the post (OUTz keeps its visibility, the machine post its value). *)
Lemma g_eq_gen : forall a, 0 <= a < 2 ^ 64 -> ~ gXC a -> ~ (sp0 - ImgBaseAGS.AFSTACK <= a < sp0) ->
  ~ (mb <= a < mb + MSn) -> ~ (AGif4.SHLO mb <= a < AGif4.SHHI mb MSn) -> ~ (QSn <= a < QSn + 131072) -> rd' a = rd0 a.
Proof.
intros a Ra NX NS N1 N2 N3.
assert (HE : w_H Wz (Z_to_bv 64 a) = w_H W (Z_to_bv 64 a)).
{ apply OUTz; rewrite w64_unsigned by exact Ra; [exact N1 | exact N2 | intros [_ X]; exact (N3 X)]. }
unfold aview, mbyte, mrestrict. rewrite HE, (g_MEQ a Ra NX NS). reflexivity.
Qed.
Lemma g_eq_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> rd' a = rd0 a.
Proof.
intros a Ha.
pose proof (g_owned_app (ly_prim ly, kPrimResvSize) ltac:(unfold owned_extents; cbn; tauto)) as EA. cbn [fst snd] in EA.
pose proof (g_stat 0 1 _ _ ltac:(zl) eq_refl eq_refl) as DQ. pose proof (g_stat 0 8 _ _ ltac:(zl) eq_refl eq_refl) as DS.
pose proof (g_map_st (ly_prim ly, kPrimResvSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DM.
pose proof g_res as [HR _].
cbn in DQ, DS. unfold zdisjoint in DQ, DS, DM. cbn [fst snd] in DQ, DS, DM.
apply g_eq_gen.
- exact (owned_range ly (ly_prim ly, kPrimResvSize) a LY ltac:(unfold owned_extents; cbn; tauto) ltac:(unfold in_zr; cbn [fst snd]; zl)).
- exact (gX_prim a Ha).
- unfold ImgBaseAGS.AFSTACK in *. zl.
- zl.
- intros X. pose proof (g_hull_band a X) as HB. apply (app_not_band _ _ a EA Ha).
  unfold in_band_rw, SHADOW_OFF, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. zl.
- unfold ImgBaseAGS.QSv, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl.
Qed.
Lemma g_obj_eq : forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> rd' a = rd0 a.
Proof.
intros a Ha. destruct (ERRB_SEP_at B TS ERRB_SEP ly a LY IMG TSD Ha) as (N1 & N2 & N3 & N4 & N5).
pose proof (proj1 (proj2 (amc_cells_owned _ _ _ _ _ M)) a Ha) as OS. apply Exists_exists in OS as (r & Hr & Hin).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
assert (II : in_zr a (ly_img ly)) by (unfold in_zr in *; zl).
pose proof (g_img_range a II) as IR.
pose proof (g_stat 1 9 _ _ ltac:(zl) eq_refl eq_refl) as DQ. pose proof (g_stat 2 9 _ _ ltac:(zl) eq_refl eq_refl) as DT.
pose proof (g_stat 8 9 _ _ ltac:(zl) eq_refl eq_refl) as DS.
pose proof (g_map_st (ly_img ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as DM.
pose proof g_res as [HR _].
cbn in DQ, DT, DS. unfold zdisjoint, in_zr in DQ, DT, DS, DM, II. cbn [fst snd] in DQ, DT, DS, DM, II.
apply g_eq_gen.
- unfold kImgLo, kImgEnd in IR. zl.
- apply gX_out; [unfold kThreadObjSize in *; zl | zl | zl | zl | exact (g_img_band a IR) | exact N4].
- unfold ImgBaseAGS.AFSTACK in *. zl.
- zl.
- intros X. pose proof (g_hull_band a X).
  unfold SHADOW_OFF, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kImgLo, kImgEnd in *. zl.
- unfold ImgBaseAGS.QSv, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl.
Qed.
(* Printf's two cells keep their bytes at the grant arm's post (the errbuf object's script, g_obj_eq). *)
Lemma g_pf_eq : forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) -> rd' a = rd0 a.
Proof.
intros a Ha. destruct (PF_SEP ly a LY IMG TSD Ha) as [N2 N4].
destruct (proj1 (amc_pf_owned _ _ _ _ _ M) a Ha) as [OS NI]. apply Exists_exists in OS as (r & Hr & Hin).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
assert (II : in_zr a (ly_img ly)) by (unfold in_zr in *; zl).
pose proof (g_img_range a II) as IR.
pose proof (g_stat 1 9 _ _ ltac:(zl) eq_refl eq_refl) as DQ. pose proof (g_stat 2 9 _ _ ltac:(zl) eq_refl eq_refl) as DT.
pose proof (g_stat 8 9 _ _ ltac:(zl) eq_refl eq_refl) as DS.
pose proof (g_map_st (ly_img ly) ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as DM.
pose proof g_res as [HR _].
cbn in DQ, DT, DS. unfold zdisjoint, in_zr in DQ, DT, DS, DM, II. cbn [fst snd] in DQ, DT, DS, DM, II.
apply g_eq_gen.
- unfold kImgLo, kImgEnd in IR. zl.
- apply gX_out; [unfold kThreadObjSize in *; zl | unfold kInstObjSize in NI; zl | zl | zl | exact (g_img_band a IR) | exact N4].
- unfold ImgBaseAGS.AFSTACK in *. zl.
- zl.
- intros X. pose proof (g_hull_band a X).
  unfold SHADOW_OFF, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kImgLo, kImgEnd in *. zl.
- unfold ImgBaseAGS.QSv, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. zl.
Qed.
Lemma g_pf : pf_cells_cf B lyF rd'.
Proof. apply (pf_cells_frame_cf B lyF rd0 rd'); [exact g_pf_eq | exact (amc_pf_cells _ _ _ _ _ M)]. Qed.
Lemma g_exh : exh_cell_cf B lyF SF rd'.
Proof.
pose proof g_SF as (Rreg & _). pose proof g_lyeqs as (_ & E2 & _). pose proof (lo_space_in ly LY) as [S1 S2].
pose proof (YGcfImgRows.EXH_OFF_bound (proj1 (amc_cells_owned _ _ _ _ _ M))) as XB.
eapply (exh_cell_cf_frame B); [exact (amc_exh_cell _ _ _ _ _ M) | intros c; unfold exh_mem_cf; rewrite Rreg; reflexivity |].
intros c Hc. cbn [aeval aoff]. rewrite E2. apply g_eq_prim. unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *. zl.
Qed.
Lemma g_errb : errb_cells_cf B lyF SF rd'.
Proof.
pose proof g_sizes as (ND & _). pose proof g_le as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E15).
assert (NSZ : is_errb_sz (mkSec MSn (ImgBaseAGS.NDv n) true) = false).
{ unfold is_errb_sz. cbn [sm_size]. apply Z.eqb_neq. rewrite <- ND. pose proof (cfxm_needed_size_pos n). unfold ERRB_SZ_TAG. zl. }
eapply (errb_cells_cf_frame B); [exact (amc_errb_cells _ _ _ _ _ M) | | | exact (g_EC_any grow) | | exact g_obj_eq | exact g_VIS].
- unfold errb_mapped_cf. rewrite (g_secs_any grow), existsb_app. cbn [existsb]. rewrite g_noncap, Bool.orb_false_r. reflexivity.
- unfold errb_data_cf. rewrite (g_secs_any grow), cfx_last_cap_idx_app. cbn [last_cap_idx]. rewrite g_noncap.
  destruct (last_cap_idx (st_secs S) 0 None) as [i|] eqn:EL; [|reflexivity].
  pose proof (cfx_last_cap_idx_lt _ _ _ _ EL ltac:(intros k Hk; discriminate Hk)) as LT.
  rewrite (E15 i ltac:(zl)). reflexivity.
- rewrite !YGcfRoomStep.errb_size_first, (g_secs_any grow), YGcfRoomStep.first_sz_app_nsz by exact NSZ. reflexivity.
Qed.

(* ---- the model's relation at the final state (AGjy.ARm_final) ---- *)
Lemma g_ARm : ARmcf B lyF SF Hp rd'.
Proof.
pose proof g_lyeqs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E12 & _ & _ & _ & _ & EI).
pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _).
constructor.
- exact WFF.
- exact (amc_universe _ _ _ _ _ M).
- exact (amc_syms _ _ _ _ _ M).
- exact g_lyok.
- exact (g_placed_any grow).
- exact g_const_finalF.
- exact g_const_ownedF.
- exact g_cells_final.
- exact g_fa_final.
- exact g_flags_final.
- exact g_depot_okF.
- exact g_shadow_final.
- exact g_zshadow_final.
- exact g_vis_junk.
- exact g_vis_areas.
- exact g_vis_client.
- exact g_zero_final.
- rewrite E12. exact TSD.
- rewrite EI. exact (amc_static_img _ _ _ _ _ M).
- eapply Forall_impl; [|exact (amc_hp_live _ _ _ _ _ M)]. intros p (k & Hk & Hst & Ep & Hh).
  exists k. split; [rewrite Rck; apply in_app_iff; left; exact Hk|]. split; [exact Hst|]. split; [|exact Hh].
  rewrite Ep. unfold ck_user. symmetry. apply (sptr_addr_le B ly lyF nS _ g_le).
  pose proof (g_chunk_lt k Hk) as LT. destruct (ck_beg k); cbn; try exact I. exact LT.
- exact (g_xs_placed_any grow).
- exact g_exh.
- exact g_errb.
- exact (amc_cells_owned _ _ _ _ _ M).
- exact g_pf.
- exact (amc_pf_owned _ _ _ _ _ M).
Qed.

Lemma g_ARcf_post : ARcf im_segs B lyF SF Hp Wz mem' mdz.
Proof.
pose proof HAR as (_ & _ & [AB [PIN CB]] & _ & _).
split; [exact g_ARm|]. split; [exact (g_ledger grow matV mat' mdz (proj1 Hgrow) EMDZ MW2 EGr)|].
split; [|split; [exact MWz | exact g_ahs]].
split; [|split].
- pose proof g_SH_hull as (_ & _ & H3). pose proof g_sec_live as [SL SH]. pose proof g_ms as (MS1 & _).
  pose proof g_SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rres & _).
  assert (PC : prim_committed SF = prim_committed S) by reflexivity.
  assert (ND0 : 0 <= ImgBaseAGS.NDv n).
  { unfold ImgBaseAGS.NDv, ImgBaseAGS.R8v. pose proof (Z.div_pos (n + 7) 8 ltac:(zl) ltac:(zl)). zl. }
  pose proof (cf_hull_alloc S SF MSn (ImgBaseAGS.NDv n) ltac:(zl) ND0 (g_secs_any grow) SH) as CH.
  unfold abudget_cf in *. rewrite SL, (g_EC_any grow), Rres, ite_res_g, PC, ABz. zl.
- intros e He. rewrite (g_SEF_any grow) in He. apply in_app_iff in He as [He|[<-|[]]].
  + destruct (PIN e He) as [P1 P2]. split; apply INCz; assumption.
  + split; [exact AMAPz | exact AHULLz].
- apply (cls1_band_vis_layout_cf nS ly lyF); [exact g_le|]. apply (cls1_band_vis_hsub_cf ly (w_H W)); [|exact CB].
  intros x Hx. destruct (w_H W x) eqn:E; [reflexivity|]. rewrite (MON x E) in Hx. discriminate Hx.
Qed.
(* ---- the grant arm's post at the walk's instance ---- *)
Hypothesis HIOK : IOK (as_inst B).
Hypothesis HQT : qtight SF.
Lemma g_post : ARXq_cf B IOK Hp (as_inst B) lyF SF Wz mem' mdz /\ qtight SF /\ layout_le nS ly lyF /\
  sptr_addr B lyF (ck_user KSc) = ImgBaseAGS.Uv mb /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ AOX_cf B ly S a -> ~ AOX_cf B lyF SF a ->
     ~ ascratch B AFSTACK_G regs0 a -> ~ (ImgBaseAGS.Uv mb <= a < ImgBaseAGS.Uv mb + req_size n) ->
     aview im_segs (w_H Wz) mem' a = aview im_segs (w_H W) mem0 a) /\
  (forall x : word, ~ AOX_cf B ly S (bv_unsigned x) -> ~ AOX_cf B lyF SF (bv_unsigned x) ->
     ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) ->
     ~ (ImgBaseAGS.Uv mb <= bv_unsigned x < ImgBaseAGS.Uv mb + req_size n) -> mem' x = mem0 x).
Proof.
split; [apply ARXq_cf_start; [exact HIOK | exact g_ARcf_post | exact g_xsm | exact HQT]|].
split; [exact HQT|]. split; [exact g_le|].
split.
{ unfold ck_user. rewrite g_KB, g_KR. cbn [padd sptr_addr sptr_exp aeval]. rewrite g_lysec. unfold ImgBaseAGS.Uv, kPage. zl. }
split.
- intros a Ra NO NO' NS NE. apply g_frame_view; [exact Ra | intros X; apply NO; left; exact X | intros X; apply NO'; left; exact X | exact NS | exact NE].
- intros x NO NO' NS NE. apply g_frame_raw; [intros X; apply NO; left; exact X | intros X; apply NO'; left; exact X | exact NS | exact NE].
Qed.
End gr.

(* The grant arm's post (AGif5.post_grant_S). *)
Lemma post_grant_cf : forall Hp inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem',
  ARXq_cf B IOK Hp inst ly S W mem0 md0 -> rpre_cf B S n -> 64513 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
  U_cf B tr S -> ims_wframe W ly regs0 mem0 tr -> getr regs0 11 = w64 inst ->
  (grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S) ->
  AGif4.skern grow W Wz md0 mdz ly mb (ImgBaseAGS.MSv n) (ImgBaseAGS.QSv ly (Z.of_nat (length (st_sec_arr S)))) ->
  AGif4.sfin W ly regs0 mem0 inst n tr (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) mb
    (fun zz m => dpost_cf B inst ly S W tr zz m) grow z Wz regs' mem' ->
  aok S (KDepot tr) z ->
  ARXq_cf B IOK Hp inst (AGif4.lyFz ly S mb) (AGif4.SFSz S n tr z grow) Wz mem' mdz /\
  qtight (AGif4.SFSz S n tr z grow) /\
  layout_le (length (st_secs S)) ly (AGif4.lyFz ly S mb) /\
  sptr_addr B (AGif4.lyFz ly S mb) (ck_user (ImgBaseAGS.KS S n)) = ImgBaseAGS.Uv mb /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ AOX_cf B ly S a -> ~ AOX_cf B (AGif4.lyFz ly S mb) (AGif4.SFSz S n tr z grow) a ->
     ~ ascratch B AFSTACK_G regs0 a -> ~ (ImgBaseAGS.Uv mb <= a < ImgBaseAGS.Uv mb + req_size n) ->
     aview im_segs (w_H Wz) mem' a = aview im_segs (w_H W) mem0 a) /\
  (forall x : word, ~ AOX_cf B ly S (bv_unsigned x) -> ~ AOX_cf B (AGif4.lyFz ly S mb) (AGif4.SFSz S n tr z grow) (bv_unsigned x) ->
     ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) ->
     ~ (ImgBaseAGS.Uv mb <= bv_unsigned x < ImgBaseAGS.Uv mb + req_size n) -> mem' x = mem0 x).
Proof.
intros Hp inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' HX HRP Nr Hlive HU WFR Hi11 Hgrow SK SFN AOK.
pose proof (ARXq_cf_iok B IOK Hp inst ly S W mem0 md0 HX) as IOKi.
pose proof (IOK_inst inst IOKi) as EI. subst inst.
pose proof (ARXq_cf_ARcf B IOK Hp _ ly S W mem0 md0 HX) as HAR.
pose proof (ARXq_cf_xsm B IOK Hp _ ly S W mem0 md0 HX) as XSM.
pose proof (ARXq_cf_qtight B IOK Hp _ ly S W mem0 md0 HX) as Q.
destruct HRP as (UOK & WFS & ROOM & HULL).
pose proof (aso_cells _ (amc_syms _ _ _ _ _ (proj1 HAR))) as AC.
assert (EI11 : bv_unsigned (getr regs0 11) = as_inst B) by (rewrite Hi11; apply w64_unsigned; unfold kLowMemEnd in AC; zl).
pose proof (WFRAME_SP W ly regs0 mem0 tr WFR) as HSP.
destruct SK as [Hmbr (mat & matV & mat' & Emdz & GOK & MW2 & EGr) LEz IOz MWz MONz VISM VISH VISQ ABz INCz AMAPz AHULLz OUTz].
destruct (AGif4.sf_dep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SFN) as (memD & DPm & PRD & EQD). cbv beta in DPm.
pose proof (post_model_cf S n tr z grow UOK WFS Nr Hlive HU (proj1 ROOM) Hgrow AOK) as [WFF QTi].
pose proof (QTi Q) as QT'.
eapply g_post; eassumption.
Qed.

(* ================================================================================================================ *)
(* 2. The records.                                                                                                   *)

(* AGif4.AIfaceS at the cf instance (AGif5.iface_S_cgif's twin). *)
Theorem ifaceS_cf : forall Hp, AGif4.AIfaceS B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
intros Hp. constructor.
- intros inst ly S W mem md n H _ _. exact (view_cf Hp inst ly S W mem md H).
- exact shape_cf.
- exact (fresh_cf Hp).
- exact (depot_cf Hp).
- exact (mwf_cf Hp).
- exact (room_cf Hp).
- exact (ledger_fld_cf Hp).
- exact (grant_cf Hp).
- exact (apart_cf Hp).
- exact (oom_cf Hp).
- exact (post_null_cf Hp).
- exact (post_grant_cf Hp).
Qed.

(* AGif4.AIfaceSw at NMAXW := cf_malloc_max, NOBW := cf_nob and the caller's room ROOMW <= CF_HEAD (the room of record,
   room_gen_cf; at the least ROOMW nmaxw_cf_ok asks, YGcfRoomCf.ROOMW_nmaxw_fits discharges it). *)
Section w.
Variable ROOMW : Z.
Hypothesis HROOMW : ROOMW <= CF_HEAD.
Theorem ifaceSw_cf : forall Hp, AGif4.AIfaceSw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max cf_nob ROOMW.
Proof.
intros Hp. constructor; [exact (ifaceS_cf Hp) | exact (apart_w_cf Hp) | exact (grant_w_cf Hp) | exact (room_w_cf Hp ROOMW HROOMW)].
Qed.
End w.

End b.
End a.
