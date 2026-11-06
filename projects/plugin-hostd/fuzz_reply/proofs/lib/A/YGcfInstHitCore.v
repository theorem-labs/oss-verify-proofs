(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   The model and memory facts behind the cf hit interfaces (YGcfInstHit.v), over the cf relation YG0ncf.ARcf at the
   unit's segments ImgBase.im_segs, generic over CfImg / CfParams / AImg / AGImg.  The cf twin of c5 30a1993588f's
   AGiy.v (the hit view over ARm), AGix.v's owned set (hit_owned), AGjb.v (hit_owned_k) and AGif1.v's shape and uninit
   fields.  rule 24: no function proved (interface-instance discharge at a model relation; no machine walk is written).
   Every image fact enters as a named premise over the class fields; no numeral of any image; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AllocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG AGif0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CLdepot.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order. *)
Set Default Proof Using "All".

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* ================================================================================================================ *)
(* 0. Byte helpers over im_segs (YF0x's, over the class's segment list).                                            *)
Lemma In_combine_seq_last_h : forall (l0 : list Z) (x : Z) s, In ((s + length l0)%nat, x) (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
induction l0 as [|y l0 IH]; intros x s; cbn.
- left. f_equal. lia.
- right. replace (s + Datatypes.S (length l0))%nat with (Datatypes.S s + length l0)%nat by lia. apply IH.
Qed.

Lemma aview_same_h : forall (H : word -> bool) (mem mem' : word -> option byte) a,
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview im_segs H mem' a = aview im_segs H mem a.
Proof. intros H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma aview_byte_h : forall H mem a v, aview im_segs H mem a = Some v -> mbyte im_segs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte im_segs (mrestrict H mem) a) as [b|] eqn:E; cbn in Hv; [|discriminate].
injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* A byte off the image window that the view shows is present (the ledger puts every segment in the window). *)
Lemma vis_present_h : forall ly S md H mem a, ALedger_cf im_segs ly S md -> layout_ok ly -> 0 <= a < 2 ^ 64 ->
  ~ in_zr a (ly_img ly) -> aview im_segs H mem a <> None -> apresent H mem a.
Proof. intros ly S md H mem a L LO Ha Hi Hv. exact (aview_present_cf im_segs ly S md H mem a L Ha Hi Hv). Qed.

(* A byte at or above the image's end is off the image window. *)
Lemma not_img_high : forall ly a, layout_ok ly -> kImgEnd <= a -> ~ in_zr a (ly_img ly).
Proof. intros ly a LO Ha Hi. pose proof (lo_img _ LO) as (I1 & I2 & I3 & _). unfold in_zr in Hi. unfold kImgLo, kImgEnd in *. lia. Qed.

Lemma find_chunk_at_none_h : forall B ly lst g, (forall k, In k lst -> ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)) ->
  find_chunk_at B ly lst g = None.
Proof.
intros B ly. induction lst as [|k t IH]; intros g H; [reflexivity|]. cbn [find_chunk_at].
destruct (Z.leb_spec (ck_base B ly k) g); destruct (Z.ltb_spec g (ck_base B ly k + ck_extent k)); cbn [andb];
try (apply IH; intros k' Hk'; apply H; right; exact Hk').
exfalso. apply (H k (or_introl eq_refl)). lia.
Qed.

(* The redzone of a hit: AGif0n's RZ at the request's redzone class is the model's rz_size. *)
Lemma RZ_rz_size : forall n, ImgBaseAG.RZ (rz_log n) = rz_size n.
Proof.
intros n. unfold ImgBaseAG.RZ, rz_of, rz_size. rewrite Z.shiftl_mul_pow2 by (unfold rz_log; repeat (destruct (_ <=? _)); lia). lia.
Qed.

(* ================================================================================================================ *)
(* 1. The cached chunk at the top of the per-thread cache of class cl, over ARcf (AGiy.v's section h over ARmcf).    *)
Section v.
Variables (B : asyms) (ly : alayout) (S : astate) (Hp : list Z) (W : world im_segs) (mem0 : word -> option byte) (md0 : Model).
Variables (n cl cnt v : Z) (l : list Z) (off : Z).
Hypothesis HAR : ARcf im_segs B ly S Hp W mem0 md0.
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Local Notation rd0 := (aview im_segs (w_H W) mem0).
Local Notation m0 := (mrestrict (w_H W) mem0).
Local Notation Kv := (ImgBaseAG.Kv ly cl v).

Lemma vM : ARmcf B ly S Hp rd0.
Proof. exact (proj1 HAR). Qed.
Lemma vL : ALedger_cf im_segs ly S md0.
Proof. exact (proj1 (proj2 HAR)). Qed.
Lemma vLY : layout_ok ly.
Proof. exact (amc_layout _ _ _ _ _ vM). Qed.
Lemma vWF : Wf_cf (as_universe B) S.
Proof. exact (amc_wf _ _ _ _ _ vM). Qed.

Lemma cl_range : 1 <= cl <= 30.
Proof. pose proof (primary_geometry n Hn0 FP) as (G & _). rewrite Hcl_class. exact G. Qed.

Lemma cls_geom : 0 < class_size cl /\ class_size cl mod 32 = 0 /\ class_size cl <= kMaxSize /\ 2 <= max_cached cl <= 16.
Proof. pose proof cl_range as CR. pose proof (class_ok cl ltac:(lia)) as (K1 & K2 & K3 & K4 & _). repeat split; lia. Qed.

Lemma cls_wf : cls_ok_cf cl (reg S cl) (cache S cl) (st_cache_inited S) (chunk_offs S cl) (batch_offs S cl).
Proof. pose proof cl_range as CR. exact (wfc_classes _ _ _ _ _ vWF cl ltac:(lia)). Qed.

Lemma off_facts :
0 <= off /\ off + class_size cl <= rg_alloc_user (reg S cl) /\ off mod class_size cl = 0 /\ off mod 16 = 0 /\
rg_alloc_user (reg S cl) <= rg_mapped_user (reg S cl) <= kFreeArrayOffset /\
~ In off ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ (chunk_offs S cl ++ batch_offs S cl)) /\
1 <= cnt <= 16 /\ cnt = Z.of_nat (length l) + 1 /\ pc_max (cache S cl) = max_cached cl.
Proof.
pose proof cls_wf as CL. pose proof cls_geom as (K1 & K2 & K3 & K4). pose proof cl_range as CR.
pose proof (wrc_elems _ _ _ _ _ _ CL) as EL. pose proof (wrc_nodup _ _ _ _ _ _ CL) as ND. pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL.
pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. rewrite Hinited in WC. destruct WC as [WM WL].
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
rewrite Hcache in EL, ND, WL.
assert (IN : In off (fa_elems (class_size cl) (rg_free (reg S cl)) ++ (l ++ [off]) ++ chunk_offs S cl ++ batch_offs S cl)).
{ apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) EL off IN) as [O1 O2].
assert (XS : off + class_size cl <= rg_alloc_user (reg S cl)).
{ pose proof O2 as O2'. apply Z.mod_divide in O2' as [qx Hqx]; [|lia]. pose proof AA as AA'. apply Z.mod_divide in AA' as [qa Hqa]; [|lia].
  assert (Hq : qx < qa) by (apply (Z.mul_lt_mono_pos_r (class_size cl)); lia).
  pose proof (Z.mul_le_mono_nonneg_r (qx + 1) qa (class_size cl) ltac:(lia) ltac:(lia)). lia. }
assert (M16 : off mod 16 = 0).
{ apply Z.mod_divide in O2 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [q' Hq']; [|lia]. apply Z.mod_divide; [lia|]. exists (q * (q' * 2)). lia. }
rewrite length_app in Hcnt_def, WL. cbn [length] in Hcnt_def, WL.
assert (NI : ~ In off ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ (chunk_offs S cl ++ batch_offs S cl))).
{ apply NoDup_remove_2. replace ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ off :: chunk_offs S cl ++ batch_offs S cl)
  with (fa_elems (class_size cl) (rg_free (reg S cl)) ++ (l ++ [off]) ++ chunk_offs S cl ++ batch_offs S cl); [exact ND|].
  rewrite <- !app_assoc. reflexivity. }
split; [lia|]. split; [exact XS|]. split; [exact O2|]. split; [exact M16|]. split; [lia|]. split; [exact NI|].
split; [lia|]. split; [lia|]. exact WM.
Qed.

Lemma off32 : off mod 32 = 0.
Proof.
pose proof off_facts as (_ & _ & O3 & _). pose proof cls_geom as (K1 & K2 & _).
apply Z.mod_divide in O3 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [r Hr]; [|lia].
rewrite Hq, Hr. replace (q * (r * 32)) with ((q * r) * 32) by lia. apply Z_mod_mult.
Qed.

Lemma Kv_base : Kv = region_base ly cl + off.
Proof. unfold ImgBaseAG.Kv, region_base. pose proof cl_range. rewrite region_off_eq by lia. lia. Qed.

Lemma Kv_geom : kHighMemBeg <= Kv /\ Kv + class_size cl <= ASAN_CEIL /\ Kv mod 16 = 0 /\
ly_prim ly <= Kv /\ Kv + class_size cl <= ly_prim ly + kPrimResvSize /\ Kv + class_size cl <= region_base ly cl + kFreeArrayOffset.
Proof.
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _). pose proof (region_in_prim ly cl vLY ltac:(pose proof cl_range; lia)) as (R1 & R2 & R3 & R4 & R5).
rewrite Kv_base. unfold kFreeArrayOffset in *. split; [lia|]. split; [lia|]. split; [|lia].
apply Z.mod_divide in R3 as [q Hq]; [|lia]. apply Z.mod_divide in O4 as [q' Hq']; [|lia]. rewrite Hq, Hq'.
replace (q * 65536 + q' * 16) with ((q * 4096 + q') * 16) by lia. apply Z_mod_mult.
Qed.

Lemma Hcl' : 1 <= cl <= 31. Proof. pose proof cl_range. lia. Qed.
Lemma Hcnt' : 1 <= cnt <= 16. Proof. pose proof off_facts; tauto. Qed.
Lemma Hv' : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32.
Proof. pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof cls_geom as (K1 & _). unfold kFreeArrayOffset in O5. lia. Qed.
Lemma Hv2' : v mod 2 = 0.
Proof.
pose proof off32 as Mo. rewrite Hoff_def in Mo. apply Z.mod_divide in Mo as [q Hq]; [|lia].
replace v with (q * 2) by lia. apply Z_mod_mult.
Qed.

(* The cached chunk's extent is apart from every chunk of the state. *)
Lemma cached_vs_chunk : forall k, In k (st_chunks S) -> ck_base B ly k + ck_extent k <= Kv \/ Kv + class_size cl <= ck_base B ly k.
Proof.
intros k Hk. pose proof vM as M.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & NI & _). pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5 & V6). pose proof cls_geom as (K1 & _).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). unfold kFreeArrayOffset in C9.
  set (c' := prim_class o) in *. set (x' := o - region_off c') in *.
  rewrite C4, C5. rewrite Kv_base. unfold region_base.
  destruct (Z.eq_dec c' cl) as [E|NE].
  + rewrite E in *.
    assert (NEQ : x' <> off).
    { intros EQ. apply NI. apply in_app_iff. right. apply in_app_iff. left.
      pose proof (In_chunk_offs S k o Hk Eb) as IN. fold c' in IN. fold x' in IN. rewrite E, EQ in IN. exact IN. }
    apply Z.mod_divide in C7 as [q Hq]; [|lia]. apply Z.mod_divide in O3 as [q' Hq']; [|lia].
    assert (q <> q') by (intros ->; apply NEQ; lia).
    destruct (Z_lt_le_dec q q').
    * left. pose proof (Z.mul_le_mono_nonneg_r (q + 1) q' (class_size cl) ltac:(lia) ltac:(lia)). lia.
    * right. pose proof (Z.mul_le_mono_nonneg_r (q' + 1) q (class_size cl) ltac:(lia) ltac:(lia)). lia.
  + pose proof cl_range as CR. unfold kFreeArrayOffset in O5.
    rewrite !region_off_eq by lia.
    destruct (Z_lt_le_dec c' cl).
    * left. assert (c' * 2 ^ 32 + 2 ^ 32 <= cl * 2 ^ 32) by nia. lia.
    * right. assert (cl * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by nia. lia.
- destruct GG as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (amc_placed _ _ _ _ _ M) as [_ PD].
  pose proof (pairwise_In zdisjoint (sec_extents ly S ++ static_extents ly) (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize)
    (sec_extents ly S) (static_extents ly) eq_refl PD S5 ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite S3, S4. unfold kPage in *. lia.
Qed.

(* No hidden head reaches into the cached chunk: every head lies in a live chunk's extent (amc_hp_live). *)
Lemma not_in_head : forall g, Kv <= g < Kv + class_size cl -> in_head Hp g = false.
Proof.
intros g Hg. pose proof vM as M. unfold in_head.
destruct (existsb _ Hp) eqn:E; [|reflexivity]. exfalso.
apply existsb_exists in E as (p & Hpin & Hf). apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M) p Hpin) as (k & Hk & Hst & Hpk & Hhd).
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (cached_vs_chunk k Hk) as D. unfold ck_n in Hhd. lia.
Qed.

(* The cached chunk's granules carry the free poison 250 (it lies in its class's mapped user range, in no chunk). *)
Lemma shadow250 : forall g, g mod 8 = 0 -> Kv <= g < Kv + class_size cl -> rd0 (shadow_addr g) = Some 250.
Proof.
intros g Hg8 Hg. pose proof vM as M.
pose proof (amc_shadow _ _ _ _ _ M g 250 Hg8) as SH. rewrite (not_in_head g Hg) in SH. apply SH. unfold ashadow.
rewrite find_chunk_at_none_h.
2:{ intros k Hk. pose proof (cached_vs_chunk k Hk). lia. }
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _).
rewrite (in_rangesb_In g (fa_poison_ranges ly S) (region_base ly cl) (rg_mapped_user (reg S cl))); [reflexivity| |rewrite Kv_base in Hg; lia].
unfold fa_poison_ranges. apply in_app_iff. left. apply in_flat_map. exists cl. split; [apply YG0s.In_zseq; pose proof cl_range; lia|]. left. reflexivity.
Qed.

(* The shadow of the cached chunk lies in the high shadow band. *)
Lemma SK_range : SHADOW_OFF <= shadow_addr Kv /\ kHighShadowBeg <= shadow_addr Kv /\ shadow_addr Kv + class_size cl / 8 <= kHighMemBeg.
Proof.
pose proof Kv_geom as (V1 & V2 & V3 & _). pose proof cls_geom as (K1 & K2 & _). ceil.
unfold shadow_addr. pose proof (Z.div_mod Kv 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound Kv 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (class_size cl) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (class_size cl) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF, kHighShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma sh_granule : forall j, shadow_addr (Kv + 8 * j) = shadow_addr Kv + j.
Proof.
intros j. pose proof Kv_geom as (_ & _ & V3 & _). apply Z.mod_divide in V3 as [q Hq]; [|lia].
unfold shadow_addr. rewrite Hq. replace (q * 16 + 8 * j) with ((2 * q + j) * 8) by lia. replace (q * 16) with ((2 * q) * 8) by lia.
rewrite !Z.div_mul by lia. lia.
Qed.

Lemma shadow_present : forall s, shadow_addr Kv <= s < shadow_addr Kv + class_size cl / 8 -> rd0 s = Some 250 /\ apresent (w_H W) mem0 s.
Proof.
intros s Hs. pose proof Kv_geom as (V1 & V2 & V3 & _). pose proof cls_geom as (K1 & K2 & _). pose proof SK_range as (SK1 & SK2 & SK3).
assert (E : s = shadow_addr (Kv + 8 * (s - shadow_addr Kv))) by (rewrite sh_granule; lia).
assert (R : rd0 s = Some 250).
{ rewrite E. apply shadow250.
  - pose proof (Z.mod_divide Kv 16 ltac:(lia)) as [D _]. set (t := s - shadow_addr Kv). destruct (D V3) as [q Hq]. rewrite Hq.
    replace (q * 16 + 8 * t) with ((2 * q + t) * 8) by lia. apply Z_mod_mult.
  - pose proof (Z.div_mod (class_size cl) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (class_size cl) 8 ltac:(lia)) as M2. lia. }
split; [exact R|].
apply (vis_present_h ly S md0 (w_H W) mem0 s vL vLY); [unfold kHighMemBeg, SHADOW_OFF, kHighShadowBeg in *; lia | apply not_img_high; [exact vLY | unfold kImgEnd, SHADOW_OFF in *; lia] | rewrite R; discriminate].
Qed.

(* Every byte of a junk or area range off the image window is present. *)
Lemma vis_present : forall e len a, In (e, len) (ajunk_cf B ly S) \/ In (e, len) (aareas S) ->
  aeval B ly e <= a < aeval B ly e + len -> 0 <= a < 2 ^ 64 -> ~ in_zr a (ly_img ly) -> apresent (w_H W) mem0 a.
Proof.
intros e len a Hin Ha Hr Hi. pose proof vM as M.
assert (RV : range_vis B ly rd0 (e, len)).
{ destruct Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) (amc_junk _ _ _ _ _ M) _ Hin) | exact (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M) _ Hin)]. }
apply (vis_present_h ly S md0 (w_H W) mem0 a vL vLY Hr Hi).
specialize (RV (a - aeval B ly e) ltac:(cbn [snd]; lia)). cbn [fst] in RV. replace (aeval B ly e + (a - aeval B ly e)) with a in RV by lia. exact RV.
Qed.

(* The whole cached chunk is present. *)
Lemma chunk_present : forall a, Kv <= a < Kv + class_size cl -> apresent (w_H W) mem0 a.
Proof.
intros a Ha. pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _). pose proof Kv_geom as (V1 & V2 & _). pose proof cls_geom as (K1 & _).
pose proof Kv_base as KB.
apply (vis_present (ASp (region_off cl)) (rg_mapped_user (reg S cl))).
- right. unfold aareas. apply in_app_iff. left. apply in_flat_map. exists cl. split; [apply YG0s.In_zseq; pose proof cl_range; lia|]. left. reflexivity.
- cbn [aeval]. fold (region_base ly cl). lia.
- ceil. unfold kHighMemBeg in *. lia.
- apply not_img_high; [exact vLY | unfold kImgEnd, kHighMemBeg in *; lia].
Qed.

Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk_cf B ly S).
Proof. intros r Hr. unfold ajunk_cf. right. right. do 5 (apply in_or_app; right). apply in_or_app. left. exact Hr. Qed.

Lemma T_off : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> 0 <= a < 2 ^ 64 /\ ~ in_zr a (ly_img ly).
Proof.
intros a Ha. destruct (owned_extents_bound ly a vLY ltac:(apply Exists_exists; exists (ly_T ly, kThreadObjSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn [fst snd]; lia])) as (AA & _ & NI).
split; [|exact NI]. pose proof (app_addr_below_ceil a AA). ceil. lia.
Qed.

(* The thread's junk words (cache stats, stats) are present. *)
Lemma junk_present : forall a, ly_T ly + t_cache_stats <= a < ly_T ly + t_unwinding -> apresent (w_H W) mem0 a.
Proof.
intros a Ha. destruct (T_off a ltac:(unfold t_cache_stats, t_unwinding, kThreadObjSize in *; lia)) as [Ra NI].
destruct (Z_lt_le_dec a (ly_T ly + t_stats)) as [H1|H1].
- apply (vis_present (AT t_cache_stats) (t_stats - t_cache_stats)); [left; apply in_thread_junk; right; left; reflexivity | cbn [aeval]; unfold t_cache_stats, t_stats in *; lia | exact Ra | exact NI].
- apply (vis_present (AT t_stats) (t_unwinding - t_stats)); [left; apply in_thread_junk; right; right; left; reflexivity | cbn [aeval]; unfold t_stats, t_unwinding in *; lia | exact Ra | exact NI].
Qed.

Lemma cell_state : forall c e (w : nat) x, In c (acells_cf B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem im_segs m0 (aeval B ly e) w x.
Proof.
intros c e w x Hin ->. pose proof vM as M. apply (cell_holds_val_mem im_segs B ly (w_H W) mem0 e w (ANum x)).
exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) _ Hin).
Qed.

Lemma In_acells_cache : forall c, In c (cache_cells S cl) -> In c (acells_cf B ly S).
Proof.
intros c Hc. unfold acells_cf. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists cl.
split; [apply YG0s.In_zseq; pose proof cl_range; lia | exact Hc].
Qed.

Lemma cache_vals : val_mem im_segs m0 (ImgBaseAG.Pv ly cl) 4 cnt /\ val_mem im_segs m0 (ImgBaseAG.Pv ly cl + 8) 8 (class_size cl) /\
val_mem im_segs m0 (ImgBaseAG.PVv ly cl cnt) 4 v.
Proof.
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & NI & C1 & C2 & PM). pose proof cl_range as CR.
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * cl)) d) = ImgBaseAG.Pv ly cl + d) by (intros d; cbn; unfold ImgBaseAG.Pv; lia).
assert (EP0 : aeval B ly (AT (t_cache + 80 * cl)) = ImgBaseAG.Pv ly cl) by (cbn; unfold ImgBaseAG.Pv; lia).
unfold cache_cells in *.
split; [|split].
- rewrite <- EP0. eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; left; reflexivity|].
  rewrite Hcache, length_app. cbn [length]. unfold z4, c4. f_equal. f_equal. f_equal. lia.
- rewrite <- (EP 8). eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; right; left; reflexivity|].
  reflexivity.
- replace (ImgBaseAG.PVv ly cl cnt) with (aeval B ly (aoff (AT (t_cache + 80 * cl)) (16 + 4 * Z.of_nat (length l)))) by (rewrite EP; unfold ImgBaseAG.PVv; lia).
  eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; right; right|].
  + apply in_map_iff. exists (length l, off). split; [reflexivity|]. rewrite Hcache.
    rewrite length_app. cbn [length]. apply (In_combine_seq_last_h l off 0).
  + cbn [fst snd]. unfold z4, c4. f_equal. f_equal. f_equal. rewrite Hoff_def. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma unwinding_val : val_mem im_segs m0 (ly_T ly + t_unwinding) 1 0.
Proof.
replace (ly_T ly + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
eapply cell_state; [|reflexivity]. unfold acells_cf. do 8 (apply in_or_app; right). left. reflexivity.
Qed.

(* The hit-g view (AGif0n.hview), from ARcf and the unit's image facts. *)
Lemma hview_cf : forall inst,
  (forall ly' S' md', ALedger_cf im_segs ly' S' md' -> im_img_cover ly') -> as_tsd B = im_tsd -> ag_shadow = SHADOW_OFF ->
  val_mem im_segs m0 (inst + 0x20) 8 (ly_space ly) /\ val_mem im_segs m0 (inst + 0xe20) 8 0x10000000000 /\
  val_mem im_segs m0 (inst + 0xe28) 8 0x108000010 ->
  hview B W ly inst mem0 cl cnt v.
Proof.
intros inst HIMG HTSD HSHB HI. pose proof vM as M.
pose proof cache_vals as (C1 & C2 & C3).
constructor.
- exact vLY.
- exact (HIMG ly S md0 vL).
- rewrite (amc_tsd _ _ _ _ _ M). exact HTSD.
- exact Hcnt'.
- pose proof Hv' as [V0 V1]. pose proof Hv2' as V2. split; [exact V0|]. split; [exact V2|]. exact V1.
- exact (amc_const _ _ _ _ _ M).
- exact HI.
- exact (conj C1 (conj C2 C3)).
- exact unwinding_val.
- exact junk_present.
- exact chunk_present.
- intros s Hs. unfold ImgBaseAG.SKv, ImgBaseAG.SHBv in Hs. rewrite HSHB in Hs. fold (shadow_addr Kv) in Hs.
  destruct (shadow_present s Hs) as [R P]. split; [exact P|].
  intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. exact (aview_byte_h _ _ _ _ R).
Qed.

(* ================================================================================================================ *)
(* 2. The allocator memory a hit writes is owned (AGix.hit_owned / AGjb.hit_owned_k over ARmcf), for a chunk of    *)
(*    redzone [rz] and size [nn] with rz + nn inside the class size.                                                *)
Section o.
Variables (rz nn : Z).
Hypotheses (Hrz : 16 <= rz) (Hrz16 : rz mod 16 = 0) (Hnn : 0 <= nn) (Hfit : rz + nn <= class_size cl).
Hypothesis HSHB : ag_shadow = SHADOW_OFF.
Hypothesis HDZO : forall ly' a, ag_dzone ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).

Lemma own_K : forall b, Kv <= b < Kv + rz -> aowned B ly S b.
Proof.
intros b Hb. pose proof vM as M. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5 & _).
apply (own_prim_nonuser_cf B ly S Hp _ b M); [lia|]. intros k Hk _.
pose proof (cached_vs_chunk k Hk) as D. pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). lia.
Qed.

Lemma own_SH : forall y, 0 <= y < class_size cl -> aowned B ly S (ImgBaseAG.SHBv + (Kv + y) / 8).
Proof.
intros y Hy. pose proof vM as M. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5 & _).
unfold ImgBaseAG.SHBv. rewrite HSHB. fold (shadow_addr (Kv + y)). apply (own_shadow_prim_cf B ly S Hp _ _ M). lia.
Qed.

Lemma own_T : forall a, ImgBaseAG.WINT ly cl a -> aowned B ly S a.
Proof.
intros a Hw. pose proof vM as M. pose proof cl_range as CR.
apply (own_core_cf B ly S Hp _ (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd].
unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw. unfold kThreadObjSize, t_cache, t_stats, t_unwinding in *. lia.
Qed.

Lemma own_DZ : forall a, ag_dzone ly a -> aowned B ly S a.
Proof.
intros a Hd. pose proof vM as M. destruct (HDZO ly a Hd) as [Hs|[Hs|Hs]].
- exact (own_static_cf B ly S Hp _ a M Hs).
- apply (own_core_cf B ly S Hp _ (ly_NB ly, kNodesBlockSize) a M); [unfold core_extents; cbn; tauto | exact Hs].
- apply (own_core_cf B ly S Hp _ (ly_SB ly, kStoreBlockSize) a M); [unfold core_extents; cbn; tauto | exact Hs].
Qed.

(* The write set of a hit of redzone [rz] and size [nn]. *)
Lemma hit_owned_core : forall odd a,
  (odd = true -> nn mod 8 <> 0) ->
  ImgBaseAG.WINT ly cl a \/ ((Kv <= a < Kv + 16) \/ (Kv + rz - 16 <= a < Kv + rz)) \/
  (odd = true /\ ImgBaseAG.SHBv + (Kv + rz + nn / 8 * 8) / 8 <= a < ImgBaseAG.SHBv + (Kv + rz + nn / 8 * 8) / 8 + 1) \/
  ag_dzone ly a \/ (ImgBaseAG.SHBv + (Kv + rz) / 8 <= a < ImgBaseAG.SHBv + (Kv + rz) / 8 + nn / 8 * 8 / 8) ->
  aowned B ly S a.
Proof.
intros odd a Hodd Hw. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5 & _). pose proof cls_geom as (K1 & K2 & _).
destruct Hw as [Hw|[[Hw|Hw]|[[Ho Hw]|[Hw|Hw]]]].
- exact (own_T a Hw).
- apply own_K. lia.
- apply own_K. lia.
- assert (E : a = ImgBaseAG.SHBv + (Kv + rz + nn / 8 * 8) / 8) by lia. rewrite E.
  pose proof (Hodd Ho) as E8. pose proof (Z.div_mod nn 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as MB.
  replace (Kv + rz + nn / 8 * 8) with (Kv + (rz + nn / 8 * 8)) by lia. apply own_SH. lia.
- exact (own_DZ a Hw).
- assert (R8 : (8 | Kv + rz)).
  { apply Z.mod_divide in V3 as [q Hq]; [|lia]. apply Z.mod_divide in Hrz16 as [q' Hq']; [|lia]. exists (2 * q + 2 * q'). lia. }
  destruct R8 as [q Hq]. rewrite Hq, Z.div_mul in Hw by lia.
  pose proof (Z.div_mod nn 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as MB.
  rewrite Z.div_mul in Hw by lia.
  replace a with (ImgBaseAG.SHBv + (Kv + (rz + 8 * (a - ImgBaseAG.SHBv - q))) / 8).
  2:{ replace (Kv + (rz + 8 * (a - ImgBaseAG.SHBv - q))) with ((q + (a - ImgBaseAG.SHBv - q)) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  apply own_SH. lia.
Qed.

(* The g path's write set (AGif0n.hit_writes) is owned. *)
Lemma hit_owned_g : forall kz odd a, rz = ImgBaseAG.RZ kz -> nn = n ->
  (odd = true -> n mod 8 <> 0) -> hit_writes ly n cl v kz odd a -> aowned B ly S a.
Proof.
intros kz odd a Erz Enn Hodd Hw. rewrite <- Enn in Hodd. apply (hit_owned_core odd a Hodd).
unfold hit_writes, ImgBaseAG.PBW, ImgBaseAG.PBv, ImgBaseAG.SUv, ImgBaseAG.Uv, ImgBaseAG.N8D in Hw. rewrite <- Erz, <- Enn in Hw. exact Hw.
Qed.

(* The k path's write set (AGif0n.hit_writes_k) is owned. *)
Lemma hit_owned_k : forall odd a, rz = K6.RZ -> nn = K6.NPv n ->
  (odd = true -> K6.NPv n mod 8 <> 0) -> hit_writes_k ly n cl v odd a -> aowned B ly S a.
Proof.
intros odd a Erz Enn Hodd Hw. rewrite <- Enn in Hodd. apply (hit_owned_core odd a Hodd).
unfold hit_writes_k, K6.PBW, K6.PBv, K6.SUv, K6.Uv, K6.N8D in Hw. rewrite <- Erz, <- Enn in Hw.
change (K6.WINT ly cl a) with (ImgBaseAG.WINT ly cl a) in Hw. change (K6.Kv ly cl v) with Kv in Hw. exact Hw.
Qed.

End o.
End v.

(* ================================================================================================================ *)
(* 3. The model fields: the shape of malloc_cf on a hit (AGif1.shape_cgif) and the empty uninited cache.            *)
Lemma bind_cong_h {A R} : forall (m1 m2 : M A) (f : A -> M R) s, m1 s = m2 s -> bind m1 f s = bind m2 f s.
Proof. intros m1 m2 f s E. unfold bind. rewrite E. reflexivity. Qed.

(* On an inited, non-empty cache, cache_alloc_cf is the pop (its init and refill steps are no-ops). *)
Lemma cache_alloc_pop_cf : forall c S, st_cache_inited S = true -> pc_chunks (cache S c) <> [] -> cache_alloc_cf c S = pop_part c S.
Proof.
intros c S Hi Hne. unfold cache_alloc_cf, init_cache_if_needed, refill_if_empty_cf, pop_part, get_pc, bind, get, ret, put. cbn [ibind]. rewrite Hi. cbn [ibind].
change (znth pclass0 c (st_cache S)) with (cache S c). destruct (pc_chunks (cache S c)) as [|x t] eqn:E; [exfalso; apply Hne; reflexivity|].
cbn [ibind]. try change (znth pclass0 c (st_cache S)) with (cache S c). rewrite ?E. reflexivity.
Qed.

Lemma shape_cf : forall n tr S l off, 0 <= n -> from_primary n = true ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
malloc_cf n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) cf_pc_malloc_max ;; malloc_join_t cf_pc_spin_shadow n tr (chunk_class n)) S.
Proof.
intros n tr S l off Hn0 FP Hinited Hcache.
assert (Hne : pc_chunks (cache S (chunk_class n)) <> []) by (rewrite Hcache; destruct l; discriminate).
unfold malloc_cf, malloc_join_t. rewrite FP.
rewrite (bind_ret_l tick _ S tt (set_nev (st_nev S + 1) S) eq_refl).
rewrite (bind_ret_l tick _ S tt (set_nev (st_nev S + 1) S) eq_refl).
cbv beta.
destruct (n <? kMaxAllowedMalloc - kPage).
- rewrite (bind_ret_l (mcheck true cf_pc_malloc_max) _ (set_nev (st_nev S + 1) S) tt (set_nev (st_nev S + 1) S) eq_refl).
  rewrite (bind_ret_l (mcheck true cf_pc_malloc_max) _ (set_nev (st_nev S + 1) S) tt (set_nev (st_nev S + 1) S) eq_refl).
  cbv beta. unfold malloc_K_t. apply bind_cong_h. apply bind_cong_h. apply cache_alloc_pop_cf; [exact Hinited | exact Hne].
- reflexivity.
Qed.

(* An uninited per-thread cache is empty (Wf_cf's class invariant). *)
Lemma uninit_cf : forall U pp cc bb S c, WfP_cf U pp cc bb S -> 1 <= c <= 31 -> st_cache_inited S = false -> pc_chunks (cache S c) = [].
Proof.
intros U pp cc bb S c W Hc CI. pose proof (wrc_cache _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c Hc)) as WC.
rewrite CI in WC. cbv iota in WC. rewrite WC. reflexivity.
Qed.
End a.
