(* copy of proofs/cgif/cgif_file_fuzzer/lib/ErrnoApart.v@e8a7dd66acf2; do not edit. Only this line is added, and the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib is this unit's OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* errno lies apart from every zone the frame-generic Allocate / Deallocate walks frame out.

   ErrnoG.v states errno-kept posts.  An arm proves one from its frame clauses, which keep memory outside the zones the
   walk wrote; errno is kept when its 4 bytes [as_errno B, as_errno B + 4) lie outside every such zone.  This file
   states that ONCE per zone family, image-free; ErrnoApartcgif.v discharges each image fact ONCE for cgif_file.

   The zones, measured from every frame clause of AGif0n / AGif4 / DGif0 / DMiface / DMspec / DIfaceR:
   - stack windows [sp0 - k, sp0): ascratch (YG0d.v:214-215, used by DMspec.v:108, DIfaceR.v:54, AllocG / DeallocG),
     at_RETw / at_RETkw (AGif0n.v:88, :111, inside WIN), if_depot / if_depot_miss (AGif0n.v:191, :348), if_refill's
     premise (AGif0n.v:287, :290), rleaf (AGif0n.v:262-266), sfin (AGif4.v:87-88, inside WIN and DXz), ifs_depot
     (AGif4.v:261), di_depot (DGif0.v:293), dmem_c / dmem_m / dmem_n (DGif0.v:159, :183, :194), dmem_q (DMiface.v:119);
   - the thread object's cells (WINT of ImgBaseAG / K6 / ImgBaseAGS / DGgiC / DGgmC, qhdr) and among them the
     unwinding byte (also alone in if_refill's premise, AGif0n.v:290, and dmem_n, DGif0.v:194);
   - the depot zone: ag_dzone (AGif0n.v:86-88, :109-111, :192, :349), ims_dzone (AGif4.v:84-86, :88 via DXz, :262),
     dg_dzone (DGif0.v:157-159, :181-183, :294);
   - the internal allocator's zone dg_izone (DGif0.v:159, :183, :195);
   - the new primary block, its chunk header and its shadow (at_RETw / at_RETkw, AGif0n.v:88-90, :111-113);
   - the secondary map, its block, its shadow and the pointer array's slots (sfin, AGif4.v:87-89; ifs_post_grant,
     AGif4.v:313, :318); the instance's secondary windows WINI (AGif4.v:87 via WIN);
   - the freed block, its header words and its shadow, the last batch's cells (dmem_c / dmem_m, DGif0.v:159-160,
     :183-184; the post's E, DeallocG.v:115);
   - the quarantine's header words in the instance and the batch cells (dmem_q, DMiface.v:113-114, :119).
   AOX (the allocator's owned set) is not an image fact: an instance of the interface proves that errno is unowned.

   Image facts (Props, one per class field family; their cgif discharges are in ErrnoApartcgif.v):
   - [errno_in_img] (AImg): errno lies in the layout's image window.  With layout_ok it puts errno below kImgEnd and
     apart from every owned extent (the thread object, the pointer array, ...) and from the stack, so the stack, the
     thread-object, unwinding-byte, pointer-array and primary-heap families are LEMMAS below;
   - [errno_unhidden] (AImg): no world hides a byte of errno.  A view-form conclusion (ErrnoG.errno_kept_v) needs it
     besides the zone facts, because a callee's post gives only wle W W'; with it, errno kept on the raw memory is
     errno kept on the view in any two worlds (the lemma [errno_kept_v_of_raw]).  It is a Prop, not a lemma: the
     generic world law is w_Hoff (YA0n.v:20: a hidden byte lies in no loaded segment), so the lemma would need errno
     inside a loaded segment of im_segs, and no image-free fact gives that: errno_in_img places errno in the
     layout's image window, which has gaps between segments (ALedger's al_img only puts every segment inside the
     window, YG0n.v:311; al_imgcov covers the window by page-rounded reservations, YG0n.v:328);
   - [errno_apart_dzone_ag] / [errno_apart_dzone_d]: ag_dzone / dg_dzone;
   - [errno_apart_izone]: dg_izone;
   - [errno_apart_shadow_ag]: the shadow map above ImgBaseAG.SHBv;
   - [errno_apart_zone3_d]: an application zone (dg_zone3: a freed block's chunk);
   - [errno_apart_inst_ag] / [errno_apart_inst_d]: the allocator instance object [inst, inst + 3680) (ag_inst_ok /
     dg_inst_ok).
   Lemmas over the frames' own zone expressions (proved here from those Props and layout_ok): errno_apart_stack /
   _thread / _unw / _Q, the WINT copies (_wint_g / _k / _c / _m), the walks' windows (_win_g for at_RETw, _win_k for
   at_RETkw, _dwin_c / _dwin_m / _dwin_q for dmem_c / dmem_m / dmem_q), the blocks (_blk_g / _blk_k / _blk_d) and the
   shadows (_shd_g / _shd_k / _dshadow).
   Every premise is a fact the arms hold: im_syms B (cgif: TfibSyms B), layout_ok ly and im_img_cover ly (hview /
   mview / dview_n / sview), the stack bounds of the pre, the class and slot bounds of the view.

   Moved to ErrnoApartS.v, names and statements unchanged: the secondary path's family (sfin, ifs_depot,
   ifs_post_grant): the Props [errno_apart_dzone_s] (ims_dzone), [errno_apart_shadow_s] (above ImgBaseAGS.SHBv) and
   [errno_apart_zone3_s] (ims_zone3: a granted map), and the lemmas errno_apart_wint_s, errno_apart_dx,
   errno_apart_qr, errno_apart_blk_s, errno_apart_wini_s, errno_apart_win_s.  DXz and QRz are AGif4's, and AGif4's
   Require closure reaches YA08 / YA09 / YA0e, whose non-local Zify flag setting escapes Require (ErrnoApartS.v's
   header gives the consumer's fix).  This file's Require closure reaches none of AGif4, YA08, YA09, YA0e. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DGif0 ErrnoG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* A division by a positive constant, as two linear bounds (for lia). *)
Lemma div_bounds_e : forall x c, 0 < c -> c * (x / c) <= x < c * (x / c) + c.
Proof. intros x c Hc. pose proof (Z.div_mod x c ltac:(lia)). pose proof (Z.mod_pos_bound x c Hc). lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image window.                                                                                                *)

(* Image fact: errno's 4 bytes lie in the layout's image window. *)
Definition errno_in_img : Prop :=
forall B ly, im_syms B -> im_img_cover ly ->
fst (ly_img ly) <= as_errno B /\ as_errno B + 4 <= fst (ly_img ly) + snd (ly_img ly).

(* Image fact: no world hides a byte of errno (the hidden set w_H of a world over the image's segments). *)
Definition errno_unhidden : Prop :=
forall B (W : world im_segs) a, im_syms B -> as_errno B <= a < as_errno B + 4 -> w_H W (Z_to_bv 64 a) = false.

(* errno kept on the raw memory is errno kept on the view, in any two worlds. *)
Lemma errno_kept_v_of_raw : errno_unhidden -> forall B (W W' : world im_segs) mem mem', im_syms B ->
errno_kept B mem mem' -> errno_kept_v im_segs B W W' mem mem'.
Proof.
intros HU B W W' mem mem' TS E a Ha. unfold aview, mbyte, mrestrict. cbv beta.
rewrite (HU B W' a TS Ha), (HU B W a TS Ha).
pose proof (E (a - as_errno B) ltac:(lia)) as Ea. replace (as_errno B + (a - as_errno B)) with a in Ea by lia.
unfold w64 in Ea. rewrite Ea. reflexivity.
Qed.

Lemma errno_below_imgend : errno_in_img -> forall B ly, im_syms B -> layout_ok ly -> im_img_cover ly ->
as_errno B + 4 <= kImgEnd.
Proof.
intros HI B ly TS LY IMG. destruct (HI B ly TS IMG) as [_ E2]. pose proof (lo_img ly LY) as (L1 & _ & L3 & _). lia.
Qed.

(* Every byte at or above the image's end. *)
Lemma errno_apart_high : errno_in_img -> forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly ->
kImgEnd <= a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros HI B ly a TS LY IMG Ha. pose proof (errno_below_imgend HI B ly TS LY IMG). lia. Qed.

(* Every byte of an owned extent of the layout (the primary reserve, the pointer array, the thread object, the fake
   stack, the depot's nodes and store blocks, the context map, the depot table). *)
Lemma errno_apart_owned : errno_in_img -> forall B ly e a, im_syms B -> layout_ok ly -> im_img_cover ly ->
In e (owned_extents ly) -> fst e <= a < fst e + snd e -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly e a TS LY IMG He Ha. destruct (HI B ly TS IMG) as [E1 E2].
pose proof (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LY) He
  (or_intror (or_introl eq_refl))) as D.
unfold zdisjoint in D. lia.
Qed.

(* The layout's stack: every window [lo, hi) of it (the frames' [sp0 - k, sp0)). *)
Lemma errno_apart_stack : errno_in_img -> forall B ly lo hi a, im_syms B -> layout_ok ly -> im_img_cover ly ->
ly_stk_lo ly <= lo -> lo <= a < hi -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly lo hi a TS LY IMG L Ha. apply (errno_apart_high HI B ly a TS LY IMG).
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). unfold YG0f.kHighMemBeg, kImgEnd in *. lia.
Qed.

(* The thread object [T, T + kThreadObjSize). *)
Lemma errno_apart_thread : errno_in_img -> forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly ->
ly_T ly <= a < ly_T ly + kThreadObjSize -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly a TS LY IMG Ha.
exact (errno_apart_owned HI B ly (ly_T ly, kThreadObjSize) a TS LY IMG
  ltac:(unfold owned_extents; right; right; left; reflexivity) Ha).
Qed.

(* The thread's unwinding byte. *)
Lemma errno_apart_unw : errno_in_img -> forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly ->
ly_T ly + t_unwinding <= a < ly_T ly + t_unwinding + 1 -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly a TS LY IMG Ha. apply (errno_apart_thread HI B ly a TS LY IMG).
unfold t_unwinding, kThreadObjSize in *. lia.
Qed.

(* Every byte at or above the pointer array's base (the array lies above the image window: it is larger than the
   room below the image). *)
Lemma errno_apart_Q : errno_in_img -> forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly ->
ly_Q ly <= a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly a TS LY IMG Ha. destruct (HI B ly TS IMG) as [E1 E2].
assert (HQ : In (ly_Q ly, kPtrArrayResv) (owned_extents ly)) by (unfold owned_extents; right; left; reflexivity).
pose proof (pairwise_In zdisjoint (static_extents ly) _ (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LY) HQ
  (or_intror (or_introl eq_refl))) as D.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) _ HQ) as A. cbv beta in A. cbn [fst snd] in A, D.
pose proof (lo_img ly LY) as (L1 & _).
unfold zdisjoint, in_app in *. cbn [fst snd] in D. unfold kPtrArrayResv, kImgLo in *. lia.
Qed.

(* The primary heap lies above the image's end (it is in high memory). *)
Lemma ly_space_high : forall ly, layout_ok ly -> kImgEnd + 4096 <= ly_space ly.
Proof.
intros ly LY. pose proof (lo_high ly LY) as [H1 _]. pose proof (lo_space_in ly LY) as [S1 _].
unfold YG0f.kHighMemBeg, kImgEnd in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The primary path (AGImg): at_RETw (ImgBaseAG's g copies) and at_RETkw (the K6 copies).                           *)
Section g. Context {AG : AGImg}.

(* Image fact: the depot zone. *)
Definition errno_apart_dzone_ag : Prop :=
forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly -> ag_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4).
(* Image fact: the shadow map, at and above its offset. *)
Definition errno_apart_shadow_ag : Prop :=
forall B a, im_syms B -> ImgBaseAG.SHBv <= a -> ~ (as_errno B <= a < as_errno B + 4).
(* Image fact: the allocator instance object. *)
Definition errno_apart_inst_ag : Prop :=
forall B inst a, im_syms B -> ag_inst_ok inst -> inst <= a < inst + 3680 -> ~ (as_errno B <= a < as_errno B + 4).

Lemma errno_apart_wint_g : errno_in_img -> forall B ly cl a, im_syms B -> layout_ok ly -> im_img_cover ly ->
0 <= cl < kNumClasses -> ImgBaseAG.WINT ly cl a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly cl a TS LY IMG Hcl Hw. apply (errno_apart_thread HI B ly a TS LY IMG).
unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw.
unfold kThreadObjSize, t_cache, t_stats, t_unwinding, kNumClasses in *. lia.
Qed.
Lemma errno_apart_wint_k : errno_in_img -> forall B ly cl a, im_syms B -> layout_ok ly -> im_img_cover ly ->
0 <= cl < kNumClasses -> K6.WINT ly cl a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly cl a TS LY IMG Hcl Hw. apply (errno_apart_thread HI B ly a TS LY IMG).
unfold K6.WINT, K6.Pv, K6.SSLOTv in Hw.
unfold kThreadObjSize, t_cache, t_stats, t_unwinding, kNumClasses in *. lia.
Qed.

(* at_RETw's window WIN (AGif0n.v:88). *)
Lemma errno_apart_win_g : errno_in_img -> errno_apart_shadow_ag -> forall B ly regs0 n cl v kz odd a,
im_syms B -> layout_ok ly -> im_img_cover ly ->
ly_stk_lo ly + ImgBaseAG.AFSTACK <= bv_unsigned (getr regs0 2) ->
0 <= cl < kNumClasses -> 0 <= v -> 0 <= n ->
ImgBaseAG.WIN ly regs0 n cl v kz odd a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI HS B ly regs0 n cl v kz odd a TS LY IMG HSP Hcl Hv Hn Hw.
pose proof (ly_space_high ly LY) as SH. unfold kImgEnd in SH.
assert (C0 : 0 <= cl * 2 ^ 32) by (apply Z.mul_nonneg_nonneg; lia).
assert (R0 : 0 <= ImgBaseAG.RZ kz) by (unfold ImgBaseAG.RZ, ImgBaseAG.rz_of; pose proof (Z.pow_nonneg 2 kz ltac:(lia)); lia).
unfold ImgBaseAG.WIN in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- refine (errno_apart_stack HI B ly _ _ a TS LY IMG _ Hw). lia.
- exact (errno_apart_wint_g HI B ly cl a TS LY IMG Hcl Hw).
- apply (errno_apart_high HI B ly a TS LY IMG). unfold ImgBaseAG.Uv, ImgBaseAG.Kv in Hw. unfold kImgEnd. lia.
- destruct Hw as [_ Hw]. apply (HS B a TS).
  assert (N0 : 0 <= ImgBaseAG.N8D n) by (unfold ImgBaseAG.N8D; pose proof (Z.div_pos n 8 Hn ltac:(lia)); lia).
  assert (P0 : 0 <= (ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz + ImgBaseAG.N8D n) / 8).
  { apply Z.div_pos; [unfold ImgBaseAG.Kv; lia | lia]. }
  unfold ImgBaseAG.PBv in Hw. lia.
Qed.

(* at_RETkw's window K6.WIN (AGif0n.v:111). *)
Lemma errno_apart_win_k : errno_in_img -> errno_apart_shadow_ag -> forall B ly regs0 n cl v odd a,
im_syms B -> layout_ok ly -> im_img_cover ly ->
ly_stk_lo ly + ImgBaseAG.AFSTACK <= bv_unsigned (getr regs0 2) ->
0 <= cl < kNumClasses -> 0 <= v ->
K6.WIN ly regs0 n cl v odd a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI HS B ly regs0 n cl v odd a TS LY IMG HSP Hcl Hv Hw.
pose proof (ly_space_high ly LY) as SH. unfold kImgEnd in SH.
assert (C0 : 0 <= cl * 2 ^ 32) by (apply Z.mul_nonneg_nonneg; lia).
unfold K6.WIN in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- refine (errno_apart_stack HI B ly _ _ a TS LY IMG _ Hw). lia.
- exact (errno_apart_wint_k HI B ly cl a TS LY IMG Hcl Hw).
- apply (errno_apart_high HI B ly a TS LY IMG). unfold K6.Uv, K6.Kv, K6.RZ in Hw. unfold kImgEnd. lia.
- destruct Hw as [_ Hw]. apply (HS B a TS).
  assert (N0 : 0 <= K6.N8D n).
  { unfold K6.N8D, K6.NPv. pose proof (Z.div_pos (Z.max n 1) 8 ltac:(lia) ltac:(lia)); lia. }
  assert (P0 : 0 <= (K6.Kv ly cl v + K6.RZ + K6.N8D n) / 8).
  { apply Z.div_pos; [unfold K6.Kv, K6.RZ; lia | lia]. }
  unfold K6.PBv in Hw. lia.
Qed.

(* The new block (at_RETw's [Kv + RZ kz, + n), AGif0n.v:89). *)
Lemma errno_apart_blk_g : errno_in_img -> forall B ly n cl v kz a, im_syms B -> layout_ok ly -> im_img_cover ly ->
0 <= cl -> 0 <= v ->
ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz <= a < ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz + n ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly n cl v kz a TS LY IMG Hcl Hv Ha. apply (errno_apart_high HI B ly a TS LY IMG).
pose proof (ly_space_high ly LY) as SH.
assert (C0 : 0 <= cl * 2 ^ 32) by (apply Z.mul_nonneg_nonneg; lia).
assert (R0 : 0 <= ImgBaseAG.RZ kz) by (unfold ImgBaseAG.RZ, ImgBaseAG.rz_of; pose proof (Z.pow_nonneg 2 kz ltac:(lia)); lia).
unfold ImgBaseAG.Kv in Ha. lia.
Qed.
(* The new block (at_RETkw's [K6.Kv + K6.RZ, + K6.NPv n), AGif0n.v:112). *)
Lemma errno_apart_blk_k : errno_in_img -> forall B ly n cl v a, im_syms B -> layout_ok ly -> im_img_cover ly ->
0 <= cl -> 0 <= v ->
K6.Kv ly cl v + K6.RZ <= a < K6.Kv ly cl v + K6.RZ + K6.NPv n -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly n cl v a TS LY IMG Hcl Hv Ha. apply (errno_apart_high HI B ly a TS LY IMG).
pose proof (ly_space_high ly LY) as SH.
assert (C0 : 0 <= cl * 2 ^ 32) by (apply Z.mul_nonneg_nonneg; lia).
unfold K6.Kv, K6.RZ in Ha. lia.
Qed.

(* The new block's shadow (at_RETw's [SUv, + N8D n / 8), AGif0n.v:90). *)
Lemma errno_apart_shd_g : errno_apart_shadow_ag -> forall B ly n cl v kz a, im_syms B -> layout_ok ly ->
0 <= cl -> 0 <= v ->
ImgBaseAG.SUv ly cl v kz <= a < ImgBaseAG.SUv ly cl v kz + ImgBaseAG.N8D n / 8 -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HS B ly n cl v kz a TS LY Hcl Hv Ha. apply (HS B a TS).
pose proof (ly_space_high ly LY) as SH. unfold kImgEnd in SH.
assert (C0 : 0 <= cl * 2 ^ 32) by (apply Z.mul_nonneg_nonneg; lia).
assert (R0 : 0 <= ImgBaseAG.RZ kz) by (unfold ImgBaseAG.RZ, ImgBaseAG.rz_of; pose proof (Z.pow_nonneg 2 kz ltac:(lia)); lia).
assert (U0 : 0 <= ImgBaseAG.Uv ly cl v kz / 8) by (apply Z.div_pos; [unfold ImgBaseAG.Uv, ImgBaseAG.Kv; lia | lia]).
unfold ImgBaseAG.SUv in Ha. lia.
Qed.
(* The new block's shadow (at_RETkw's [K6.SUv, + K6.N8D n / 8), AGif0n.v:113). *)
Lemma errno_apart_shd_k : errno_apart_shadow_ag -> forall B ly n cl v a, im_syms B -> layout_ok ly ->
0 <= cl -> 0 <= v ->
K6.SUv ly cl v <= a < K6.SUv ly cl v + K6.N8D n / 8 -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HS B ly n cl v a TS LY Hcl Hv Ha. apply (HS B a TS).
pose proof (ly_space_high ly LY) as SH. unfold kImgEnd in SH.
assert (C0 : 0 <= cl * 2 ^ 32) by (apply Z.mul_nonneg_nonneg; lia).
assert (U0 : 0 <= K6.Uv ly cl v / 8) by (apply Z.div_pos; [unfold K6.Uv, K6.Kv, K6.RZ; lia | lia]).
unfold K6.SUv in Ha. lia.
Qed.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The Deallocate side (DImg): dmem_c / dmem_m / dmem_n (DGif0.v:155-198) and dmem_q (DMiface.v:117-126).          *)
Section d. Context {DI : DImg}.

(* Image fact: the depot zone. *)
Definition errno_apart_dzone_d : Prop :=
forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly -> dg_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4).
(* Image fact: the internal allocator's zone. *)
Definition errno_apart_izone : Prop :=
forall B a, im_syms B -> dg_izone a -> ~ (as_errno B <= a < as_errno B + 4).
(* Image fact: an application zone (the freed block's chunk: DGif0.dview's dv_zone, DGif0.v:140). *)
Definition errno_apart_zone3_d : Prop :=
forall B x sz a, im_syms B -> dg_zone3 x sz -> x <= a < x + sz -> ~ (as_errno B <= a < as_errno B + 4).
(* Image fact: the allocator instance object. *)
Definition errno_apart_inst_d : Prop :=
forall B inst a, im_syms B -> dg_inst_ok inst -> inst <= a < inst + 3680 -> ~ (as_errno B <= a < as_errno B + 4).

Lemma errno_apart_wint_c : errno_in_img -> forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly ->
DGgiC.WINT ly a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly a TS LY IMG Hw. apply (errno_apart_thread HI B ly a TS LY IMG).
unfold DGgiC.WINT in Hw. unfold kThreadObjSize, t_qc, t_stats, t_unwinding in *. lia.
Qed.
Lemma errno_apart_wint_m : errno_in_img -> forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly ->
DGgmC.WINT ly a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly a TS LY IMG Hw. apply (errno_apart_thread HI B ly a TS LY IMG).
unfold DGgmC.WINT in Hw. unfold kThreadObjSize, t_stats, t_unwinding in *. lia.
Qed.

(* dmem_c's window dwin_c (DGif0.v:159). *)
Lemma errno_apart_dwin_c : errno_in_img -> errno_apart_zone3_d -> forall B ly sp0 pa nn lastb a,
im_syms B -> layout_ok ly -> im_img_cover ly -> ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 ->
dg_zone3 (pa - 16) (DGgiC.N8v nn + 16) -> 1 <= nn -> ly_space ly <= DGgiC.Bv ly lastb ->
dwin_c ly sp0 pa lastb a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI HZ B ly sp0 pa nn lastb a TS LY IMG HSP Hz Hnn HB Hw.
unfold dwin_c in Hw. destruct Hw as [Hw|[Hw|Hw]].
- refine (errno_apart_stack HI B ly _ _ a TS LY IMG _ Hw). lia.
- exact (errno_apart_wint_c HI B ly a TS LY IMG Hw).
- assert (N8 : 8 <= DGgiC.N8v nn) by (unfold DGgiC.N8v; pose proof (div_bounds_e (nn + 7) 8 ltac:(lia)); lia).
  pose proof (ly_space_high ly LY) as SH.
  unfold DGgiC.WINB, DGgiC.SLOTv, DGgiC.BCv in Hw. destruct Hw as [Hw|[Hw|Hw]].
  + apply (HZ B _ _ a TS Hz). lia.
  + apply (HZ B _ _ a TS Hz). lia.
  + apply (errno_apart_high HI B ly a TS LY IMG). lia.
Qed.

(* dmem_m's window dwin_m (DGif0.v:183). *)
Lemma errno_apart_dwin_m : errno_in_img -> errno_apart_zone3_d -> forall B ly sp0 pa nn a,
im_syms B -> layout_ok ly -> im_img_cover ly -> ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 ->
dg_zone3 (pa - 16) (DGgiC.N8v nn + 16) -> 1 <= nn ->
dwin_m ly sp0 pa a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI HZ B ly sp0 pa nn a TS LY IMG HSP Hz Hnn Hw.
unfold dwin_m in Hw. destruct Hw as [Hw|[Hw|Hw]].
- refine (errno_apart_stack HI B ly _ _ a TS LY IMG _ Hw). lia.
- exact (errno_apart_wint_m HI B ly a TS LY IMG Hw).
- assert (N8 : 8 <= DGgiC.N8v nn) by (unfold DGgiC.N8v; pose proof (div_bounds_e (nn + 7) 8 ltac:(lia)); lia).
  unfold DGgmC.WINB in Hw. apply (HZ B _ _ a TS Hz). lia.
Qed.

(* The freed block's shadow dshadow (DGif0.v:160, :184). *)
Lemma errno_apart_dshadow : errno_in_img -> forall B ly pa nn a, im_syms B -> layout_ok ly -> im_img_cover ly ->
0 <= pa -> dshadow pa nn a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly pa nn a TS LY IMG Hp Hw. apply (errno_apart_high HI B ly a TS LY IMG).
unfold dshadow, DGgiC.SPv in Hw. pose proof (Z.div_pos pa 8 Hp ltac:(lia)). unfold SHADOW_OFF, kImgEnd in *. lia.
Qed.

(* The freed block (the Deallocate post's E, DeallocG.v:115 / :142). *)
Lemma errno_apart_blk_d : errno_apart_zone3_d -> forall B pa nn a, im_syms B ->
dg_zone3 (pa - 16) (DGgiC.N8v nn + 16) -> pa <= a < pa + nn -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HZ B pa nn a TS Hz Ha. apply (HZ B _ _ a TS Hz).
assert (nn <= DGgiC.N8v nn) by (unfold DGgiC.N8v; pose proof (div_bounds_e (nn + 7) 8 ltac:(lia)); lia). lia.
Qed.

(* dmem_q's window dwin_q (DMiface.v:119). *)
Lemma errno_apart_dwin_q : errno_in_img -> errno_apart_inst_d -> forall B inst ly sp0 X S' P a,
im_syms B -> layout_ok ly -> im_img_cover ly -> ly_stk_lo ly + YFeuC.DSTACK <= sp0 -> dg_inst_ok inst ->
(forall b, In b (all_batches X ++ all_batches S' ++ P) -> 0 <= b_self b) ->
dwin_q inst ly sp0 X S' P a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI HN B inst ly sp0 X S' P a TS LY IMG HSP HO HP Hw.
unfold dwin_q in Hw. destruct Hw as [Hw|[Hw|Hw]].
- refine (errno_apart_stack HI B ly _ _ a TS LY IMG _ Hw). lia.
- unfold qhdr in Hw. destruct Hw as [Hw|[Hw|Hw]].
  + apply (HN B inst a TS HO). unfold o_quar in Hw. lia.
  + apply (HN B inst a TS HO). unfold o_quar in Hw. lia.
  + apply (errno_apart_thread HI B ly a TS LY IMG). unfold t_qc, kThreadObjSize in *. lia.
- unfold bcellw in Hw. destruct Hw as (b & Hb & Hw). pose proof (HP b Hb) as H0.
  pose proof (ly_space_high ly LY) as SH. apply (errno_apart_high HI B ly a TS LY IMG). lia.
Qed.
End d.
End a.
