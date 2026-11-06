(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_identity_poll_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlIdentityPollBlock.v, with its module paths, module names and numbers changed; 724 of its 802 lines of code are new or changed and 345 lines of the source are left out. *)
(* fuzz_preset, S1 ALLOC-HEAP, image B' (asan-ubsan, #102 pin d663f82d): the walk of fuzz_strdup (alloc.c :108-116; 23
   slots of the whole-program listing lib/B/Listing_prog.v) against the batch-cut text tfuzz_strdup_specX (lib/A/PRH_FnAlloc.v
   blob 4d8aeba047e5 with PRH_Base.v ef7c8ca98529, the cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record):
   THE OUTCOME conjunct, and the LIVE premise guarded by cnt <> fail) with the
   room premise of form (a), mirroring S1Strdup's image-A walk lib/A/Prog/FuzzStrdup.v (same listing words; only the
   image numbers, the stack needs and the generated names differ),
   at preset's CfParams (lib/A/CfParamsPreset.v) and the allocator relation ARcf pa_segs B (YG0ncf.v), in cgif's
   per-function form (proofs/cgif/cgif_file_fuzzer/lib/A/AC9k.v; fuzz_grant's CtrlIdentityPollBlock.v on
   origin/cold/pg-prog): the runner is YC80x / YC1fPx over YCbqG's ajournal_x; the strlen wrapper goes through
   YGcallMxmn.v's aj_strlen_at_xrom (the read-only premise in the arodata_okP form fpre gives; the text PROVED by
   c-libc-stdio's lib/AU/PSstrRo.v), __asan_memcpy through YGcallMxmn.v's aj_intrin_at_xm, fuzz_malloc through its
   text by YCbqGcall.v's aj_call_x. The theorem at the instance: fuzz_strdup_holds_B_TfibB, B := lib/Reusable/YD2l.v
   TfibB, its TfibSyms by TfibB_syms.
   ON THE CUT: as the image-A walk, the guarded LIVE premise goes to fuzz_malloc's text as it is, fuzz_malloc's post is
   read BY NAME (sd_conj_pick), strdup's OUTCOME conjunct is fuzz_malloc's at n = len + 1, every journal is read
   through YCbqG.v's projections ajx_*, and the journal stays at the empty wild budget (no allocator call of its own).
   This file Requires no image-A file directly: S1ImgB.v gives its image facts.
   Numerals: the frame 32 (LENGTH, the listing's `addi sp, sp, -32`); slot offsets / return points 28, 40, 64 (DERIVED:
   4 * slot of the instruction after each call); atom indices 2, 32, 33, 37, 49, 53, 65 (DERIVED: the symbolic
   engine's numbering, CLOB's a0 is its 5th entry); 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (DERIVED: shadow and stack bounds);
   8, 16 (LENGTH: word, granule, alignment; 16 is also cf_head at CfParams_preset, read by `change`); 16432 / 16400
   (DERIVED: STK_fuzz_strdup / STK_fuzz_malloc at prh_img_B, checked by vm_compute);
   64 (LENGTH: GrantRo's hull margin). No ADDRESS literal: addresses are B_prog_sigma / B_prog_val of lib/B/PAImg_prog.v,
   PrhImg fields of lib/B/PRH_ImgB.v, or segment fields of the generated image, read by computation. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfStr YGcfStrX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc CfParamsPreset.
From OSSVerify.omx_clap_core.fuzz_preset.images Require AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSstrRo AImgShadowVisCfB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Notation CP := CfParams_preset.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
(* the symbolic state at fuzz_strdup's entry: its own frame of 32 bytes below the entry sp (atom 2), sp in the stack
   band astk_ok gives, no shadow entry (the function makes no instrumented access of its own) *)
Definition SD_Bx : sv := SOff 32 0.
Definition SD_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition sd_regions : smem := [ stack_region 32 ].
Definition sd_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
(* fuzz_strdup's entry, as a byte offset from the listing's base (DERIVED: the generated B_prog_sigma / B_prog_base) *)
Definition SD_PC : Z := B_prog_sigma AS_fuzz_strdup - B_prog_base.
Definition ss_sd : sstate := mkSS SD_PC sr_atoms sd_regions None sd_facts.
Definition sd_SH : list shent := [].
Definition SD_EI (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs []).

(* ---- address arithmetic (no state) ---- *)
Lemma sd_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma sd_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma sd_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
lia.
Qed.
(* the shadow bytes of an application range are outside it (in_app, below alloc_ceiling) *)
Lemma sd_shadow_out : forall p len x, in_app p len -> p + len <= alloc_ceiling -> p <= x < p + len ->
~ (p <= shadow_of_addr SHADOW_OFF x < p + len).
Proof.
intros p len x Happ Hc Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma sd_hull_out : forall p len x n s, in_app p len -> p + len <= alloc_ceiling -> p <= x -> 0 < n -> x + n <= p + len ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> ~ (p <= s < p + len).
Proof.
intros p len x n s Happ Hc Hx Hn Hxn Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as P1.
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
assert (P3 : (x + n - 1) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *. lia.
Qed.
(* cgif YCbq.v:1945 shadow_hull_vis_of_block, for any covering hull *)
Lemma sd_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
(* fuzz_grant GrantRo.v:82-100 ro_hull's arithmetic: the hull of a range at least 64 bytes inside [IMG_LO_B, IMG_TOP_B)
   (image B's hull, the pa_lo / pa_hi of PI_prog_B that kept_at states) is the shadow of image bytes *)
Lemma sd_hull_img : forall a n s, 0 < n -> IMG_LO_B + 64 <= a -> a + n + 64 <= IMG_TOP_B ->
shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
s = shadow_addr (8 * (s - SHADOW_OFF)) /\ IMG_LO_B <= 8 * (s - SHADOW_OFF) < IMG_TOP_B.
Proof.
intros a n s Hn Hlo Hhi Hs. unfold IMG_LO_B, IMG_TOP_B in *. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.

(* ---- the image (computed from the generated segments and PRH_Img.v; no number typed) ---- *)
Lemma sd_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* alloc.c's statics are image bytes below the low-memory end (they lie in the image's last, writable segment) *)
Lemma sd_pst_low : forall a, Exists (in_zr a) PST -> 0 <= a < kLowMemEnd.
Proof.
intros a Hx. unfold prh_pst in Hx.
cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
  pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B] in Hx.
unfold kLowMemEnd.
repeat (apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [unfold in_zr in Hx; cbn [fst snd] in Hx; lia |]).
apply Exists_nil in Hx; destruct Hx.
Qed.

(* ---- bytes ---- *)
Lemma sd_garr8_aview : forall (W : world SEGS) m p l j, garr8 SEGS (mrestrict (w_H W) m) p l -> (j < length l)%nat ->
aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.
Lemma sd_garr8_move : forall (W W' : world SEGS) m m' x d l, garr8 SEGS (mrestrict (w_H W) m) x l ->
(forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (d + Z.of_nat j) = aview SEGS (w_H W) m (x + Z.of_nat j)) ->
garr8 SEGS (mrestrict (w_H W') m') d l.
Proof.
intros W W' m m' x d l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte SEGS (mrestrict (w_H W') m') (d + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma sd_first_byte : forall (W : world SEGS) m p cs, cstr (PA := PA) W m p cs ->
first_byte SEGS W m p (Z.of_nat (length cs) + 1) 0 (Z.of_nat (length cs)).
Proof.
intros W m p cs [Hg Hnz]. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) cs 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (sd_garr8_aview W m p (cs ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _.
  rewrite (sd_garr8_aview W m p (cs ++ [0]) (length cs) Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma sd_src_ok : forall (W : world SEGS) regs m p l, garr8 SEGS (mrestrict (w_H W) m) p l ->
(forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
src_ok SEGS W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (sd_garr8_aview W m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.

(* the image hull [IMG_LO_B, IMG_TOP_B) is covered by the generated segments, without a gap *)
Ltac sd_zl_all :=
  repeat first
  [ match goal with |- context [Z.of_N (seg_base ?x)] =>
      let v := eval vm_compute in (Z.of_N (seg_base x)) in lazymatch v with Zpos _ => idtac | Z0 => idtac end;
      change (Z.of_N (seg_base x)) with v in * end
  | match goal with |- context [Z.of_N (seg_size ?x)] =>
      let v := eval vm_compute in (Z.of_N (seg_size x)) in lazymatch v with Zpos _ => idtac | Z0 => idtac end;
      change (Z.of_N (seg_size x)) with v in * end
  | match goal with H : context [Z.of_N (seg_base ?x)] |- _ =>
      let v := eval vm_compute in (Z.of_N (seg_base x)) in lazymatch v with Zpos _ => idtac | Z0 => idtac end;
      change (Z.of_N (seg_base x)) with v in * end ].
Lemma sd_img_cover : forall a, IMG_LO_B <= a < IMG_TOP_B -> in_img SEGS a.
Proof.
intros a Ha. unfold IMG_LO_B, IMG_TOP_B in Ha. change SEGS with rsegs.
assert (Hb : forall k, (k < 4)%nat -> In (nth k rsegs AsanUbsan.AsanUbsan_segment_000) rsegs) by (intros k Hk; apply nth_In; vm_compute; lia).
destruct (Z_lt_le_dec a (Z.of_N (seg_base (nth 1 rsegs AsanUbsan.AsanUbsan_segment_000)))) as [h1|h1];
[exists (nth 0 rsegs AsanUbsan.AsanUbsan_segment_000)
| destruct (Z_lt_le_dec a (Z.of_N (seg_base (nth 2 rsegs AsanUbsan.AsanUbsan_segment_000)))) as [h2|h2];
  [exists (nth 1 rsegs AsanUbsan.AsanUbsan_segment_000)
  | destruct (Z_lt_le_dec a (Z.of_N (seg_base (nth 3 rsegs AsanUbsan.AsanUbsan_segment_000)))) as [h3|h3];
    [exists (nth 2 rsegs AsanUbsan.AsanUbsan_segment_000) | exists (nth 3 rsegs AsanUbsan.AsanUbsan_segment_000)]]];
(split; [apply Hb; lia|]); sd_zl_all; lia.
Qed.

(* ---- the frame and the stack writes ---- *)
Lemma sd_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* cgif-pg CtrlIdentityPollBlock.v's ipb_awr / ipb_keep at fuzz_strdup's frame of 32 bytes *)
Ltac sd_awr rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
| cbn [YP09.r_wlo stack_region]; lia
| cbn [YP09.r_whi stack_region]; lia
| apply awr_ok_nil ].
Ltac sd_keep K H rg Wx HU :=
lazymatch type of K with
| frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (H : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg - 32 <= a < spZ rg) ->
aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
by (intros a Ha Hn; apply (sd_aview_of_frame Wx Ex rsx mA mB a K); [|exact Ha];
intros (r & Hin & Hr); vm_compute in Hin;
destruct Hin as [Hin | Hin]; [subst r | destruct Hin];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia);
rewrite HU in Hr; lia)
end.
(* the top-level conjuncts of a hypothesis (a syntactic `_ /\ _` only), then the goal BY ITS TYPE: the kit's ec_conj_split /
   ec_conj_pick (lib/AU/Prog/Ent102CallB.v of the kit's batch d6318e886fd9; the cut does not carry that file). fuzz_malloc's
   post is read through it, so a conjunct the kit adds to that post (the kit's outcome conjunct) cannot shift the others. *)
Ltac sd_conj_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Sc" in let H2 := fresh "Sc" in destruct H as [H1 H2]; sd_conj_split H1; sd_conj_split H2
  | _ => idtac
  end.
Ltac sd_conj_pick H := sd_conj_split H; assumption.

(* the strlen wrapper's entry: the listing's __wrap_strlen is CfImg_B's cf_pc_strlen, the pc of c-libc-stdio's row *)
Lemma sd_pc_strlen : SIGMA AS___wrap_strlen = @cf_pc_strlen CfImgB.CfImg_B.
Proof. vm_compute. reflexivity. Qed.

Section f.
Variable B : asyms.
(* STAND-IN for the unit's TFIB symbol binding of B at image B (owner a Theorem Labs lane); image binding, no state. DISCHARGED at the
   instance: fuzz_strdup_holds_B_TfibB (end of the file), by lib/Reusable/YD2l.v TfibB_syms *)
Hypothesis TS : YF0m.TfibSyms B.
#[local] Notation AR0 := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md).
(* the allocator relation of the S1 theorems: ARcf with the error-buffer extents placed (YGcallcf.v) *)
#[local] Notation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARc).
#[local] Notation PAP := (prh_alloc_post (cp := CP) (PI := prh_img_B) (PA := PA) B).
#[local] Notation LEDGER := (prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B).
(* the allocator's laws at ARcf: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), and AR_laws_x from them (YGcallcf.v) *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.
(* callee texts: fuzz_malloc's (the batch-cut text, PRH_FnAlloc.v blob 4d8aeba047e5: the room invariant room_live_cf at
   the allocator model's instance (lib/Reusable/YGcfRoomLive.v), the live-set bounds, the run position keyed on the
   call's own event, THE OUTCOME conjunct, the LIVE premise guarded by cnt <> fail, the m-form post) and
   __asan_memcpy's (with the memnorm keep, YGcallMxmn family 1; the row owners pay it) *)
Hypothesis FMALLOC : tfuzz_malloc_specX (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK.
Hypothesis AI : YGcallMxmn.aintrin_realizes_xm SEGS B AR0 OCpy (SIGMA AS___asan_memcpy).
(* the memcpy text lifted to ARcfx by YGcallMxmn.v's _conj lift at P := xs_placed_cf *)
Let AIx := YGcallMxmn.aintrin_realizes_xm_conj SEGS B AR0 (fun ly S => xs_placed_cf ly S) OCpy (SIGMA AS___asan_memcpy) AI.
(* the strlen wrapper's text in the read-only-premise form with the keep (YGcallMxmn.v family 1b, astrlen_realizes_xrom
   at ARcfx and image B's relro range), PROVED under TS: c-libc-stdio's lib/AU/PSstrRo.v ps_strlen_xrom_xs_B
   (on this #102 line B' blob 45e63604063e). It derives its row's rom_view from arodata_okP: every owned
   byte in image B's read-only segments is one of YF0m's const cells holding its image byte (romB_check), so ARcf's
   amc_const keeps it. The row is lib/AU/PSstrlen.v. *)
Let ASx : YGcallMxmn.astrlen_realizes_xrom SEGS B ARc RLO RHI (SIGMA AS___wrap_strlen) :=
  eq_rect_r (fun pc => YGcallMxmn.astrlen_realizes_xrom SEGS B ARc RLO RHI pc)
    (PSstrRo.ps_strlen_xrom_xs_B (cp := CP) B TS RLO RHI) sd_pc_strlen.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.

Lemma sd_entry : forall STK ly S Hp W regs mem md ch,
afn_pre_x SEGS B ARc STK ly S Hp W regs mem md ch -> 32 <= STK ->
st_ok_pi SEGS VAL (SD_EI regs) ss_sd (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + SD_PC)) mem (seg_rom SEGS)))
/\ sh_ok SEGS SD_Bx sd_SH (SD_EI regs) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch HPRE H32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := SD_EI regs) in *.
assert (E2 : ew E 2 = getr regs 2)
by (subst E; unfold SD_EI; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_sd. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold sd_regions, stack_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [sd_regions pairwise_disjoint all_disjoint]. exact (conj I I).
+ split; [|split; [exact I | exact I]].
cbn [sd_facts f_atoms atoms_ok].
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
- unfold sh_ok, sd_SH. apply Forall_nil.
Qed.

(* the read-only view survives any change above alloc_ceiling *)
Lemma sd_rod_kept : forall (W W' : world SEGS) m m', arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) m) ->
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W') m').
Proof.
intros W W' m m' H HA a Hro Hn He. pose proof (@pa_segs_low _ _ PA a (sd_ro_img a Hro)) as Hl.
pose proof asan_consts as (C1 & _ & _ & _ & C5). rewrite HA by lia. exact (H a Hro Hn He).
Qed.
Lemma sd_cstr_kept : forall (W W' : world SEGS) m m' p l, cstr_ok (PA := PA) W m p l ->
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
cstr_ok (PA := PA) W' m' p l.
Proof.
intros W W' m m' p l HC HA. pose proof HC as HC0. destruct HC as ((Hg & Hnz) & H4096 & Hceil & H32 & Hamr & HRA & HH & Hv).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [split; [|exact Hnz]|].
- apply (sd_garr8_move W W' m m' p p (l ++ [0]) Hg). intros j Hj. rewrite length_app in Hj. cbn in Hj. apply HA. lia.
- split; [exact H4096|]. split; [exact Hceil|]. split; [exact H32|]. split; [exact Hamr|]. split; [|split].
  + eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (sd_shadow_low x ltac:(lia)). apply HA. lia.
  + intros s0 Hs. pose proof (sd_hull_low p (Z.of_nat (length l) + 1) s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs).
    rewrite HA by lia. apply HH. exact Hs.
  + intros a Ha. rewrite HA by exact (PRH_Base.cstr_ok_tail_lt _ _ _ _ _ HC0 Ha). apply Hv. exact Ha.
Qed.

(* the ledger survives a memory change that misses the statics and every head word *)
Lemma sd_ledger_kept : forall ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own (C : Z -> Prop),
ARc ly S Hp W memX mdX -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
(forall a, 0 <= a < alloc_ceiling -> ~ C a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
(forall a, Exists (in_zr a) PST -> ~ C a) ->
(forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ C (a - 16 + i)) ->
LEDGER ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own C HAR HL HK HCs HCh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HL).
- intros a Ha. pose proof (sd_pst_low a Ha). apply HK; [lia | exact (HCs a Ha)].
- intros a k i Hin Hi. destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in *.
  destruct (alx_blocks SEGS B ARc LAWS ly S Hp W memX mdX (a - 16) (k + 16) HAR Hab) as (_ & H4096 & Hc & _).
  rewrite sd_req in Hc by lia. apply HK; [lia | exact (HCh a k i Hin Hi)].
- intros a k _ H. exact H.
- apply Permutation_refl.
Qed.

(* fuzz_malloc's three arms survive a memory change that misses the statics, the heads and the shadow, and that touches
   the new block's user bytes only on the success arm *)
Lemma sd_alloc_post_kept : forall n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem' mem'' memX mdX,
0 < n -> 0 <= as_errno B /\ as_errno B + 4 <= alloc_ceiling -> ARc ly' S' Hp' W' memX mdX ->
PAP n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem' ->
(forall a, 0 <= a < alloc_ceiling -> ~ (res <> 0 /\ res <= a < res + n) -> aview SEGS (w_H W') mem'' a = aview SEGS (w_H W') mem' a) ->
(res <> 0 -> exists l, Z.of_nat (length l) = n /\ bytes_at W' mem'' res l) ->
PAP n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem''.
Proof.
intros n ly S Hp W Lam peak cnt fail ran most own res ly' S' Hp' W' mem' mem'' memX mdX Hn Herr HAR HAP HK HBY.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold prh_alloc_post in *. change (@cf_head CfParams_preset) with 16 in *.
destruct HAP as [(H1 & H2 & H3 & H4 & HL) | [(H1 & H2 & H3 & H4 & H5 & Hrd & HL) |
  (H1 & H2 & H3 & H4 & H5 & H6 & HRA & HHU & Hby & HL)]].
- left. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  apply (sd_ledger_kept ly' S' Hp' W' mem' mem'' memX mdX _ _ _ _ _ _ _ (fun a => res <> 0 /\ res <= a < res + n) HAR HL HK);
  intros; lia.
- right; left. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [intros k Hk; rewrite HK; [exact (Hrd k Hk) | lia | lia]|].
  apply (sd_ledger_kept ly' S' Hp' W' mem' mem'' memX mdX _ _ _ _ _ _ _ (fun a => res <> 0 /\ res <= a < res + n) HAR HL HK);
  intros; lia.
- right; right.
  assert (Hin : In (res - 16, n + 16) (ablocks B ly' S')) by (rewrite H6; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks SEGS B ARc LAWS ly' S' Hp' W' memX mdX _ _ HAR Hin) as (_ & H4096 & Hc & Happ & _ & _).
  rewrite sd_req in Hc, Happ by lia.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  split; [|split; [|split]].
  + eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (sd_shadow_low x ltac:(lia)).
    apply HK; [lia|]. intros [_ Hx2]. apply (sd_shadow_out (res - 16) (n + 16) x Happ ltac:(lia) ltac:(lia)). lia.
  + intros Hn0 s0 Hs. pose proof (sd_hull_low res n s0 ltac:(lia) Hn0 ltac:(lia) Hs).
    rewrite HK; [apply HHU; [exact Hn0 | exact Hs] | lia |]. intros [_ Hx2].
    apply (sd_hull_out (res - 16) (n + 16) res n s0 Happ ltac:(lia) ltac:(lia) Hn0 ltac:(lia) Hs). lia.
  + apply HBY. lia.
  + apply (sd_ledger_kept ly' S' Hp' W' mem' mem'' memX mdX _ _ _ _ _ _ _ (fun a => res <> 0 /\ res <= a < res + n) HAR HL HK).
    * intros a Ha [_ Hr]. pose proof (pst_in_img_B a Ha) as Hi.
      apply (blk_img_x SEGS B ARc LAWS ly' S' Hp' W' memX mdX (res - 16) (n + 16) a HAR Hin); [rewrite sd_req by lia; lia | exact Hi].
    * intros a k i Hin' Hi [_ Hr]. destruct Hin' as [E | Hin'].
      { injection E as <- <-. lia. }
      destruct (prh_ledger_hblock B ly' S' Hp' W' mem' ((res, n) :: Lam) _ _ _ _ a k _ _ HL (or_intror Hin')) as (Hk0 & Hab & _).
      change (@cf_head CfParams_preset) with 16 in *.
      assert (Hne : (a - 16, k + 16) <> (res - 16, n + 16)).
      { intros E. injection E as Ea _. apply H4. apply in_map_iff. exists (a, k). split; [cbn [fst]; lia | exact Hin']. }
      pose proof (sep_blocks_x SEGS B ARc LAWS ly' S' Hp' W' memX mdX _ _ _ _ HAR Hab Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite !sd_req in Hd by lia. lia.
Qed.

(* the success arm's block is new: it was not in the entry's block list *)
Lemma sd_newblk : forall ly S ly' S' Hp' W' m' md' (x : Z * Z), ARc ly' S' Hp' W' m' md' -> 0 <= snd x ->
ablocks B ly' S' = ablocks B ly S ++ [x] -> ~ In x (ablocks B ly S).
Proof.
intros ly S ly' S' Hp' W' m' md' [p n] HAR Hn E Hin. cbn [snd] in Hn.
assert (Hin' : In (p, n) (ablocks B ly' S')) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARc LAWS ly' S' Hp' W' m' md' p n HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (pairwise_In2 zdisjoint _ (p, req_size n) (p, req_size n)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. pose proof (prh_req_size_pos n Hn). lia.
Qed.

(* the string's bytes survive fuzz_malloc's journal: in a live harness block (block clause), or read-only image bytes
   that are not runtime-owned (image clause; alloc.c's statics are not read-only, S1ImgB.v pst_not_ro_B) *)
Lemma sd_src_kept : forall STK sp0 ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 k Lam peak cnt fail ran most own s n,
AJ STK sp0 [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k ->
LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
(forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
((exists b m, In (b, m) Lam /\ b <= s /\ s + n <= b + m) \/
 (forall a, s <= a < s + n -> in_roP SEGS RLO RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\
    ~ (as_errno B <= a < as_errno B + 4))) ->
forall a, s <= a < s + n -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a.
Proof.
intros STK sp0 ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 k Lam peak cnt fail ran most own s n HJ HL Hbl HK a Ha.
pose proof (ajx_blk HJ) as F2. pose proof (ajx_img HJ) as F3.
destruct HK as [(b & m & Hin & Hb & Hm) | Hro].
- destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran b m most own HL Hin) as (Hm0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in *.
  replace a with (b - 16 + (a - (b - 16))) by lia.
  apply (F2 (b - 16) (m + 16) (a - (b - 16)) Hab (Hbl _ Hab)); [rewrite sd_req by lia; lia | apply inFP_nil].
- destruct (Hro a Ha) as (Hr & Hno & Her).
  apply F3; [exact (sd_ro_img a Hr) | exact Hno | exact Her | exact (fun Hx => pst_not_ro_B a Hx Hr) |].
  apply fp_spares_closed. exact sink_closed_nil.
Qed.

(* the string's shadow facts at a later state: a live hidden harness block (ARcf's shadow law, past the head), or a
   registered global (AR_zshadow_law_cf) with the image hull (AImgShadowVisCfB.img_shadow_vis_xs_B, from TS) *)
Lemma sd_src_shadow : forall lyc Sc Hpc Wc memc mdc Lam s n,
ARc lyc Sc Hpc Wc memc mdc -> 0 < n ->
(forall b m, In (b, m) Lam -> 0 <= m /\ In (b - 16, m + 16) (ablocks B lyc Sc) /\ In (b - 16) Hpc) ->
kept_at (PA := PA) B Lam s n ->
range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF s n /\ shadow_hull_vis (aview SEGS (w_H Wc) memc) s n.
Proof.
intros lyc Sc Hpc Wc memc mdc Lam s n HAR Hn HLam [(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & _) | (Hlo & Hhi & Hro)]].
- destruct (HLam b m Hin) as (Hm0 & Hab & Hhp).
  destruct (AR_shadow_law_ok_cf (cp := CP) SEGS B lyc Sc Hpc Wc memc mdc (b - 16) (m + 16) (proj1 HAR) Hab) as [Hbs Hhu].
  assert (Hsk : hd_skip (cp := CP) Hpc (b - 16) = 16).
  { unfold hd_skip. replace (existsb (Z.eqb (b - 16)) Hpc) with true; [reflexivity|]. symmetry.
    apply existsb_exists. exists (b - 16). split; [exact Hhp | apply Z.eqb_refl]. }
  rewrite Hsk in Hbs. rewrite sd_req in Hbs, Hhu by lia.
  split.
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + apply (sd_hull_sub _ (b - 16) (m + 16) s n Hhu); lia.
- destruct Hzs as (q & m & Hin & Hq & Hqm).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hin) as (Z1 & Z2 & Z3 & Z4 & Z5).
  cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
  pose proof (alc_zshadow SEGS B LAWS_cf lyc Sc Hpc Wc memc mdc (q, m) (proj1 HAR) ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
  cbn [fst snd] in Hz.
  split.
  + apply (range_addressable_sub (aview SEGS (w_H Wc) memc) SHADOW_OFF q m s n); [|exact Hq|exact Hqm].
    exact (zero_shadow_range (aview SEGS (w_H Wc) memc) SHADOW_OFF q m Z3 Z4 Hz).
  + intros s0 Hs. destruct (sd_hull_img s n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
    exact (AImgShadowVisCfB.img_shadow_vis_xs_B (ci := ci) (cp := CP) SEGS B TS lyc Sc Hpc Wc memc mdc _ HAR Hr).
- (* kept_img (route (a)): per granule, a zero-shadow granule (in_zs over its 8 bytes) or a const-shadow cell of
     as_const B, which every ARx state keeps (alx_const_cells) *)
  split.
  + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzg | (v & Hcell & Hv)]).
    * destruct Hzg as (q & m & Hin & Hq & Hqm).
      pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hin)
        as (Z1 & Z2 & Z3 & Z4 & Z5).
      cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
      pose proof (alc_zshadow SEGS B LAWS_cf lyc Sc Hpc Wc memc mdc (q, m) (proj1 HAR)
        ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
      cbn [fst snd] in Hz.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      exact (zero_shadow_range (aview SEGS (w_H Wc) memc) SHADOW_OFF q m Z3 Z4 Hz x ltac:(lia)).
    * pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARc LAWS lyc Sc Hpc Wc memc mdc HAR) _ (Hcell lyc))
        as Hc.
      unfold cell_holds, z1, c1 in Hc. cbn [c_at c_w c_val aeval] in Hc.
      specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      assert (Hb : YG0f.le_byte v 1 0 = v).
      { unfold YG0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
        replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
        change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
      exists v. split; [|exact Hv].
      change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). rewrite Hc, Hb. reflexivity.
  + intros s0 Hs. destruct (sd_hull_img s n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
    exact (AImgShadowVisCfB.img_shadow_vis_xs_B (ci := ci) (cp := CP) SEGS B TS lyc Sc Hpc Wc memc mdc _ HAR Hr).
Qed.

(* the string and the new block are apart: the string lies in another live harness block, or in image bytes, which
   no block holds *)
Lemma sd_src_disj : forall ly S Hp W mem ly2 S2 Hp2 W2 memX mdX Lam peak cnt fail ran most own res n s ns,
ARc ly2 S2 Hp2 W2 memX mdX -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
0 < n -> 0 < ns -> In (res - 16, n + 16) (ablocks B ly2 S2) -> ~ In (res - 16, n + 16) (ablocks B ly S) ->
(forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
((exists b m, In (b, m) Lam /\ b <= s /\ s + ns <= b + m) \/ (forall a, s <= a < s + ns -> in_img SEGS a)) ->
res + n <= s \/ s + ns <= res.
Proof.
intros ly S Hp W mem ly2 S2 Hp2 W2 memX mdX Lam peak cnt fail ran most own res n s ns HAR HL Hn Hns Hin Hnew Hbl
  [(b & m & Hb & Hbs & Hbm) | Himg].
- destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran b m most own HL Hb) as (Hm0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in *.
  assert (Hne : (b - 16, m + 16) <> (res - 16, n + 16)) by (intros E; rewrite E in Hab; exact (Hnew Hab)).
  pose proof (sep_blocks_x SEGS B ARc LAWS ly2 S2 Hp2 W2 memX mdX _ _ _ _ HAR (Hbl _ Hab) Hin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite !sd_req in Hd by lia. lia.
- destruct (Z_le_gt_dec (res + n) s) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (s + ns) res) as [h'|h']; [right; exact h'|].
  exfalso. destruct (Z_le_gt_dec res s) as [hc|hc].
  + assert (Hr : res - 16 <= s < res - 16 + req_size (n + 16)) by (rewrite sd_req by (clear - Hn; lia); clear - hc h; lia).
    assert (Hs : s <= s < s + ns) by (clear - Hns; lia).
    exact (blk_img_x SEGS B ARc LAWS ly2 S2 Hp2 W2 memX mdX (res - 16) (n + 16) s HAR Hin Hr (Himg s Hs)).
  + assert (Hr : res - 16 <= res < res - 16 + req_size (n + 16)) by (rewrite sd_req by (clear - Hn; lia); clear - hc h' Hn; lia).
    assert (Hs : s <= res < s + ns) by (clear - h' hc; lia).
    exact (blk_img_x SEGS B ARc LAWS ly2 S2 Hp2 W2 memX mdX (res - 16) (n + 16) res HAR Hin Hr (Himg res Hs)).
Qed.
(* the strlen rule's 8-byte slack past the string (YGcallMx's amem_range8): the string lies in a live harness block
   (application memory: low below the low shadow, or high at least a head past kHighMemBeg) or in the image (64
   bytes from either end, kept_at's in_zs arm); S1Strdup's sd_amr8 (lib/A/Prog/FuzzStrdup.v) at image B *)
Lemma sd_amr8 : forall ly S Hp W mem md Lam peak cnt fail ran most own s n,
ARc ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= n ->
kept_at (PA := PA) B Lam s n -> amem_range8 s n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own s n HAR HL Hn
  [(b & m & Hin & Hb & Hm) | [(_ & Hlo & Hhi & _) | (Hlo & Hhi & _)]];
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
- destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran b m most own HL Hin) as (Hm0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab.
  destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & Happ & _).
  rewrite sd_req in Happ by lia.
  unfold amem_range8, in_app, kLowShadowBeg, ASAN_CEIL in *. rewrite C3, C4, C5. lia.
- change (@pa_lo _ _ PA) with IMG_LO_B in *. change (@pa_hi _ _ PA) with IMG_TOP_B in *.
  unfold amem_range8, IMG_LO_B, IMG_TOP_B in *. rewrite C5. lia.
- change (@pa_lo _ _ PA) with IMG_LO_B in *. change (@pa_hi _ _ PA) with IMG_TOP_B in *.
  unfold amem_range8, IMG_LO_B, IMG_TOP_B in *. rewrite C5. lia.
Qed.

(* ---- the walk ---- *)
Theorem fuzz_strdup_holds_B :
  tfuzz_strdup_specX (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK.
Proof.
unfold tfuzz_strdup_specX, fpostm, fQmn.
intros ly S Hp W regs mem md ch s cs Lam peak cnt fail ran most own [HPRE [HROD [HSHI [HRAC HFRM]]]]
  HROOM HUNIV HSEC H24 HHUL H10 HCS HKEPT HMAX HLED HLIVE.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (pa_base_lo (PL := PL) (PI := PA)) as HBLO. change (@pa_lo _ _ PA) with IMG_LO_B in HBLO. unfold IMG_LO_B in HBLO.
pose proof (@pa_B_ok _ _ PA) as HBASE.
destruct (pal_env B PAL) as ((Herr0 & Herr4) & _ & _).
set (len := Z.of_nat (length cs)) in *.
pose proof HCS as ((Hg & Hnz) & Hs4096 & Hsceil & Hlen32 & Hamr & HRA & HHULL & Hvis8).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : @STK_fuzz_strdup prh_img_B = 16432) by (vm_compute; reflexivity).
assert (FFM : @STK_fuzz_malloc prh_img_B = 16400) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hh16 : @cf_head CfParams_preset = 16) by reflexivity.
assert (Herr : 0 <= as_errno B /\ as_errno B + 4 <= alloc_ceiling) by lia.
rewrite FFS in *.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hlen0 : 0 <= len) by (subst len; lia).
assert (HKB : (exists b m, In (b, m) Lam /\ b <= s /\ s + (len + 1) <= b + m) \/
  (forall a, s <= a < s + (len + 1) -> in_roP SEGS RLO RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\
     ~ (as_errno B <= a < as_errno B + 4))).
{ destruct HKEPT as [Hk | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]]; [left; exact Hk | right; exact Hro |].
  right. intros a Ha. destruct (Hro a Ha) as (H1 & H2 & H3 & _). auto. }
assert (Hhome : (exists b m, In (b, m) Lam /\ b <= s /\ s + (len + 1) <= b + m) \/ (forall a, s <= a < s + (len + 1) -> in_img SEGS a)).
{ destruct HKEPT as [Hk | [(_ & Hlo & Hhi & _) | (Hlo & Hhi & _)]]; [left; exact Hk | |];
  right; intros a Ha; apply sd_img_cover; change (@pa_lo _ _ PA) with IMG_LO_B in *;
  change (@pa_hi _ _ PA) with IMG_TOP_B in *; unfold IMG_LO_B, IMG_TOP_B in *; lia. }
destruct (sd_entry 16432 ly S Hp W regs mem md ch HPRE ltac:(lia)) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARc 16432 [] ly S Hp W regs mem md ch HPRE) as HJ.
remember (SD_EI regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold SD_EI; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n) by (intros n Hn; subst E; unfold SD_EI; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE EL.
pose (RUN := paj_run_x (SK := SK) (PL := PL) (PI := PA) B PST ARc LAWS).
(* the same runner carrying the memnorm keep from the entry memory (h-hpreset-7's carrier, YSRrMemnorm.v:40) *)
pose (RUNM := paj_run_x_inv (SK := SK) (PL := PL) (PI := PA) B PST ARc LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS))).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL) (PI := PA)).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_strdup)) with (Z_to_bv 64 (BASE + SD_PC)).
(* ---- slots 0-6: the frame, s0 = s, the strlen call ---- *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
paj_run_tok_x_inv RUNM HS HJ SHOK HPM SD_Bspan; [sd_awr regs Usp|].
clear HF HG. sd_keep HFr KA regs W Usp. clear HFr.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (2%bv : bv 5) Rsp1. prreg HS (1%bv : bv 5) Rra1.
prreg HS (3%bv : bv 5) Rgp1. prreg HS (4%bv : bv 5) Rtp1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HspT : spZ rT = spZ regs - 32) by (unfold spZ at 1; rewrite Rsp1, Usp; rewrite unsigned_lit_small by lia; lia);
  assert (KA' : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) mT a = aview SEGS (w_H W) mem a)
    by (intros a Ha; apply KA; lia);
  pose proof (sd_cstr_kept W W mem mT s cs HCS KA') as HCS1;
  pose proof (sd_rod_kept W W mem mT HROD KA') as HROD1
end.
destruct HCS1 as ((Hg1 & Hnz1) & _ & _ & _ & _ & HRA1 & HHULL1 & Hvis1).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (YGcallMxmn.aj_strlen_at_xrom (SK := SK) SEGS B PST ARc RLO RHI LAWS Hsegs (SIGMA AS___wrap_strlen) ASx W rT mT
    16432 (spZ regs) [] ly S Hp W mem md [] ly S Hp dT 0 s len (-32) _ HJ) end.
  - rewrite Ra0, E10. reflexivity.
  - lia.
  - exact Hlen0.
  - exact Hlen32.
  - lia.
  - rewrite HspT. lia.
  - reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rgp1, E3. exact Hgp.
  - rewrite Rtp1, E4. exact Htp.
  - exact Rra1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - exact (sd_first_byte W _ s cs (conj Hg1 Hnz1)).
  - replace (len + 1) with (Z.of_nat (length (cs ++ [0]))) by (rewrite length_app; cbn [length]; subst len; lia).
    apply (sd_src_ok W _ _ s (cs ++ [0]) Hg1).
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite HspT. lia.
  - intros a Ha. lia.
  - exact (sd_amr8 ly S Hp W mem md Lam peak cnt fail ran most own s (len + 1) HAR HLED ltac:(lia) HKEPT).
  - exact HRA1.
  - exact HHULL1.
  - exact Hvis1.
  - exact HROD1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hlen2 & Hfr2 & Hpres2 & Hmn2).
pose proof (fun H0 => Hmn2 (HPM H0)) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
pose proof (ajx_pres HJ2) as Hpres2J.
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|apply Forall_nil]. split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; lia.
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    apply (apresent_writable SEGS). apply Hpres2J. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 33 (map (getr regs2) CLOB)) as E1' eqn:HE1 in HSX.
assert (HIM1 : img_env VAL A_LIM E1') by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall n, (n < 33)%nat -> ew E1' n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
assert (E1a0 : ew E1' 37 = w64 len) by (rewrite HE1, <- Hlen2; reflexivity).
assert (HAE1 : env_agree 32 (Ereg regs []) E1') by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1' 2) = spZ regs) by (rewrite OLD1 by (cbv; lia); exact Usp).
assert (SHOK1 : sh_ok SEGS SD_Bx sd_SH E1' (mrestrict (w_H W) mem2)) by (unfold sh_ok, sd_SH; apply Forall_nil).
(* ---- slots 7-9: s1 = len + 1, a0 = s1, the fuzz_malloc call ---- *)
clear HS HJ SHOK. rename HSX into HS. rename HJ2 into HJ. rename SHOK1 into SHOK.
paj_run_tok_x_inv RUNM HS HJ SHOK HPM SD_Bspan; [sd_awr regs Usp1|].
clear HF HG. sd_keep HFr KB regs W Usp1. clear HFr.
prreg HS (2%bv : bv 5) P2. prreg HS (1%bv : bv 5) P1. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ =>
  assert (Ha0m : getr (ms_regs msq) 10 = w64 (len + 1))
    by (rewrite P10, E1a0; unfold w64; rewrite unsigned_lit_small by lia; reflexivity);
  assert (KAB : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem msq) a = aview SEGS (w_H W) mem a)
    by (intros a Ha; rewrite (KB a ltac:(lia) ltac:(lia)), (Hfr2 a ltac:(lia) ltac:(lia)); exact (KA' a Ha));
  (* fpre's caller-frame bound at the callee: its sp is the entry sp - 32 *)
  assert (HSH1 : spZ (ms_regs msq) + 64 <= ly_stk_hi ly)
    by (unfold spZ at 1; rewrite P2, Usp1; rewrite unsigned_lit_small by lia; lia);
  (* fpre's return-address ceiling at the callee: the jal's own return pc, a code address of the listing *)
  assert (HRAM : raZ (ms_regs msq) < YM05.alloc_ceiling)
    by (unfold raZ; rewrite P1;
        lazymatch goal with |- bv_unsigned (Z_to_bv 64 ?e) < _ => let v := eval vm_compute in e in change e with v end;
        rewrite unsigned_lit_small by lia; lia)
end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
  eapply (aj_call_x (SK := SK) SEGS B PST ARc LAWS Hsegs W E1' _ msq 16432 (spZ regs) [] ly S Hp W mem md [] ly S Hp mdq 0
    (@STK_fuzz_malloc prh_img_B) [] (-32) (ew E1' 2) _ [] _ HS eq_refl HJ) end.
  - exact (st_ok_restrict_reg SEGS (w_H W) E1' _ _ 2%bv HS).
  - reflexivity.
  - exact Usp1.
  - reflexivity.
  - lia.
  - rewrite FFM. lia.
  - rewrite FFM. lia.
  - rewrite P3, OLD1, E3 by (cbv; lia). exact Hgp.
  - rewrite P4, OLD1, E4 by (cbv; lia). exact Htp.
  - exact P1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite P8, OLD1, E10 by (cbv; lia). rewrite unsigned_lit_small by lia. lia.
  - (* the LIVE premise is passed as it is: strdup's guarded form `cnt <> fail -> ..` is fuzz_malloc's at n = len + 1;
       so is the hull budget: strdup's entry budget for HMal (len + 1 + cf_head) is fuzz_malloc's at n = len + 1 *)
    intros HPRE1.
    refine (FMALLOC ly S Hp W _ _ _ [] (len + 1) Lam peak cnt fail ran most own
      (conj HPRE1 (conj (sd_rod_kept W W mem _ HROD KAB) (conj HSH1 (conj HRAM HFRM))))
      HROOM HUNIV HSEC H24 HHUL Ha0m ltac:(lia) HMAX _ HLIVE).
    apply (sd_ledger_kept ly S Hp W mem _ mem md _ _ _ _ _ _ _ (fun _ => False) HAR HLED); [intros a Ha _; exact (KAB a Ha) | intros; tauto | intros; tauto].
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs3 & mem3 & md3 & k1 & -> & HJ3 & HJc & HP3 & (res & HMP) & Hmn3).
(* fuzz_malloc's post BY NAME (sd_conj_pick): its result register and its prh_alloc_post at n = len + 1. Its other
   conjuncts (room_live_cf, the two position arms, THE OUTCOME) are read the same way where strdup's post takes them. *)
assert (Hres : getr regs3 10 = w64 res) by sd_conj_pick HMP.
assert (HAP : PAP (len + 1) ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem3) by sd_conj_pick HMP.
pose proof (fun H0 => Hmn3 (HPM H0)) as HPM2. clear HPM Hmn3. rename HPM2 into HPM.
pose proof (ajx_ar HJ3) as HAR3. cbv beta in HAR3.
jafter_call_keep_pi HS 49%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. constructor; [|apply Forall_nil].
  eapply (region_kept_stack_sub_x (SK := SK) SEGS B PST ARc); [exact HJc | exact HJ3 | exact Usp1 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E1' 49 (map (getr regs3) CLOB)) as E3' eqn:HE3 in HS.
assert (HIM3 : img_env VAL A_LIM E3') by (rewrite HE3; apply img_env_havoc; [exact HIM1 | cbv; lia]).
assert (OLD3 : forall n, (n < 49)%nat -> ew E3' n = ew E1' n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (E3a0 : ew E3' 53 = w64 res) by (rewrite HE3, <- Hres; reflexivity).
assert (HAE3 : env_agree 32 (Ereg regs []) E3') by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3' 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp1).
assert (SHOK3 : sh_ok SEGS SD_Bx sd_SH E3' (mrestrict (w_H W2) mem3)) by (unfold sh_ok, sd_SH; apply Forall_nil).
pose proof HAP as HAPc. unfold prh_alloc_post in HAP. rewrite Hh16 in HAP.
assert (Rres : 0 <= res < 2 ^ 64).
{ destruct HAP as [(_ & -> & _) | [(_ & -> & _) | (_ & H1 & _ & _ & _ & Eab & _)]]; [lia | lia |].
  destruct (alx_blocks SEGS B ARc LAWS ly2 S2 Hp2 W2 mem3 md3 (res - 16) (len + 1 + 16) HAR3
    ltac:(rewrite Eab; apply in_or_app; right; left; reflexivity)) as (_ & H4096 & Hc & _).
  rewrite sd_req in Hc by lia. lia. }
(* ---- slots 10-11: s2 = a0, beqz ---- *)
pose proof HJ3 as HJ3c. clear HJ SHOK HJc. rename HJ3 into HJ. rename SHOK3 into SHOK.
paj_run_tok_x_inv RUNM HS HJ SHOK HPM SD_Bspan; [sd_awr regs Usp3|].
clear HF HG. sd_keep HFr KC regs W2 Usp3. clear HFr.
psrr_branch_tok RUN BR HS SHOK SD_Bspan.
- (* res = 0: return NULL *)
  rewrite branch_eq_U, (U_atom E3' 53 res E3a0 Rres), U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_eq in Hc. subst res.
  paj_run_tok_x_inv RUNM HS HJ SHOK HPM SD_Bspan; [sd_awr regs Usp3|].
  clear HF HG. sd_keep HFr KD regs W2 Usp3. clear HFr.
  prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold fpost, apost_base_x.
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp2, r, m, d, (0 + k1) end.
  split; [cbn [ms_regs]; rewrite R1, OLD3, OLD1, E1 by (cbv; lia); rewrite Hra; reflexivity|].
  split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARc LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HS); [exact HAE3 | vm_compute; reflexivity]|].
  split; [|exact HPM].
  exists 0. split; [cbn [ms_regs]; rewrite R10, E3a0; reflexivity|].
  (* room_live_cf S2, the hull use and the two position arms: fuzz_malloc's, at n = len + 1 (strdup's S' is
     malloc's S2, and the strlen call before it keeps the allocator state S) *)
  split; [sd_conj_pick HMP|]. split; [sd_conj_pick HMP|]. split; [sd_conj_pick HMP|]. split; [sd_conj_pick HMP|].
  (* THE OUTCOME: strdup returns malloc's res (here 0) and ends at malloc's S2, and its event is malloc's
     HMal (len + 1 + cf_head); so it is fuzz_malloc's outcome conjunct at n = len + 1 *)
  split; [sd_conj_pick HMP|]. split.
  + apply (sd_alloc_post_kept (len + 1) ly S Hp W Lam peak cnt fail ran most own 0 ly2 S2 Hp2 W2 mem3 _ mem3 md3 ltac:(lia) Herr HAR3 HAPc).
    * intros a Ha _. rewrite (KD a ltac:(lia) ltac:(lia)). exact (KC a ltac:(lia) ltac:(lia)).
    * intros Hne. exfalso. exact (Hne eq_refl).
  + intros Hne. exfalso. exact (Hne eq_refl).
- (* res <> 0: copy the string *)
  rewrite branch_eq_U, (U_atom E3' 53 res E3a0 Rres), U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_neq in Hc.
  destruct HAP as [(_ & Hr0 & _) | [(_ & Hr0 & _) |
    (Hcf & Hres16 & Hral & HnotLam & EHp2 & Eab & HRA3 & HHULL3 & Hby3 & HLED3)]];
    [exfalso; exact (Hc Hr0) | exfalso; exact (Hc Hr0) |].
  assert (Hin_new : In (res - 16, len + 1 + 16) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks SEGS B ARc LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ HAR3 Hin_new) as (_ & Hnb4096 & Hnbc & Hnapp & _ & _).
  rewrite sd_req in Hnbc, Hnapp by lia.
  pose proof (sd_newblk ly S ly2 S2 Hp2 W2 mem3 md3 (res - 16, len + 1 + 16) HAR3 ltac:(cbn [snd]; lia) Eab) as Hnew.
  assert (Hbl : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) by (intros x Hx; rewrite Eab; apply in_or_app; left; exact Hx).
  (* ---- slots 12-15: a0 = res, a1 = s, a2 = len + 1, __asan_memcpy ---- *)
  paj_run_tok_x_inv RUNM HS HJ SHOK HPM SD_Bspan; [sd_awr regs Usp3|].
  clear HF HG. sd_keep HFr KE regs W2 Usp3. clear HFr.
  pose proof (ajx_ar HJ) as HART. cbv beta in HART.
  pmkst HS.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
    assert (HspT4 : spZ rT = spZ regs - 32) by (unfold spZ at 1; rewrite Q2, OLD3, OLD1, Usp by (cbv; lia); rewrite unsigned_lit_small by lia; lia);
    assert (K3T : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W2) mT a = aview SEGS (w_H W2) mem3 a)
      by (intros a Ha; rewrite (KE a ltac:(lia) ltac:(lia)); exact (KC a ltac:(lia) ltac:(lia)));
    assert (Hsrc : forall a, s <= a < s + (len + 1) -> aview SEGS (w_H W2) mT a = aview SEGS (w_H W) mem a)
      by (intros a Ha; rewrite (K3T a ltac:(lia)); exact (sd_src_kept 16432 (spZ regs) ly S Hp W mem md ly2 S2 Hp2 W2 mem3 md3 (0 + k1)
            Lam peak cnt fail ran most own s (len + 1) HJ3c HLED Hbl HKB a Ha))
  end.
  assert (HLam : forall b m, In (b, m) Lam -> 0 <= m /\ In (b - 16, m + 16) (ablocks B ly2 S2) /\ In (b - 16) Hp2).
  { intros b m Hin. destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran b m most own HLED Hin) as (Hm0 & Hab & Hhp & _).
    rewrite Hh16 in Hab, Hhp. split; [exact Hm0|]. split; [exact (Hbl _ Hab)|]. rewrite EHp2. right. exact Hhp. }
  destruct (sd_src_shadow ly2 S2 Hp2 W2 _ _ Lam s (len + 1) HART ltac:(lia) HLam HKEPT) as [HRAs HHUs].
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
    eapply (YGcallMxmn.aj_intrin_at_xm (SK := SK) SEGS B PST ARc LAWS Hsegs OCpy (SIGMA AS___asan_memcpy) AIx W2 rT mT 16432 (spZ regs) []
      ly S Hp W mem md [] ly2 S2 Hp2 dT (0 + k1) res s (len + 1) (-32) _ HJ) end.
    - rewrite Q10, E3a0. reflexivity.
    - rewrite Q11, OLD3, OLD1, E10 by (cbv; lia). reflexivity.
    - rewrite Q12, OLD3, E1a0 by (cbv; lia). unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - lia.
    - lia.
    - lia.
    - rewrite HspT4. lia.
    - reflexivity.
    - lia.
    - rewrite Hes. lia.
    - rewrite Q3, OLD3, OLD1, E3 by (cbv; lia). exact Hgp.
    - rewrite Q4, OLD3, OLD1, E4 by (cbv; lia). exact Htp.
    - exact Q1.
    - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
    - intros a Ha. split; [|lia]. right; right; left. exists (res - 16), (len + 1 + 16).
      split; [exact Hin_new|]. split; [exact Hnew|]. rewrite sd_req by lia. lia.
    - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
    - eapply range_addressable_agree; [|exact HRA3]. intros x Hx. pose proof (sd_shadow_low x ltac:(lia)). apply K3T. lia.
    - intros Hn0 s0 Hs. pose proof (sd_hull_low res (len + 1) s0 ltac:(lia) Hn0 ltac:(lia) Hs).
      rewrite K3T by lia. apply HHULL3; [exact Hn0 | exact Hs].
    - split; [lia|]. split; [lia|]. split.
      { replace (len + 1) with (Z.of_nat (length (cs ++ [0]))) by (rewrite length_app; cbn [length]; subst len; lia).
        apply (sd_src_ok W2 _ _ s (cs ++ [0])).
        - apply (sd_garr8_move W W2 mem _ s s (cs ++ [0]) Hg). intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
          apply Hsrc. lia.
        - intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite HspT4. lia. }
      split; [exact (sd_src_disj ly S Hp W mem ly2 S2 Hp2 W2 _ _ Lam peak cnt fail ran most own res (len + 1) s (len + 1)
                HART HLED ltac:(lia) ltac:(lia) Hin_new Hnew Hbl Hhome)|].
      split; [unfold amem_range, YGcfStr.amem_range8 in *; lia|].
      split; [exact HRAs | intros _; exact HHUs]. }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Hcopy & Hfr5 & Hpres5 & Hmn5).
  pose proof (fun H0 => Hmn5 (HPM H0)) as HPM2. clear HPM Hmn5. rename HPM2 into HPM.
  cbv beta iota in Hcopy.
  pose proof (ajx_pres HJ5) as Hpres5J.
  jafter_call_keep_pi HS 65%nat regs5 (mrestrict (w_H W2) mem5) HP5 [0]%nat HSX.
  lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
  { constructor; [|apply Forall_nil]. split.
    - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp3 in Ha.
      apply (mbyte_of_aview SEGS). apply Hfr5; lia.
    - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp3 in Ha.
      apply (apresent_writable SEGS). apply Hpres5J. lia. }
  specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
  remember (havoc E3' 65 (map (getr regs5) CLOB)) as E5' eqn:HE5 in HSX.
  assert (HIM5 : img_env VAL A_LIM E5') by (rewrite HE5; apply img_env_havoc; [exact HIM3 | cbv; lia]).
  assert (OLD5 : forall n, (n < 65)%nat -> ew E5' n = ew E3' n) by (intros n Hn; rewrite HE5; apply ew_havoc_old; exact Hn).
  assert (HAE5 : env_agree 32 (Ereg regs []) E5') by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
  clear HE5.
  assert (Usp5 : bv_unsigned (ew E5' 2) = spZ regs) by (rewrite OLD5 by (cbv; lia); exact Usp3).
  assert (SHOK5 : sh_ok SEGS SD_Bx sd_SH E5' (mrestrict (w_H W2) mem5)) by (unfold sh_ok, sd_SH; apply Forall_nil).
  (* ---- slots 16-22: a0 = res, the frame back, ret ---- *)
  clear HS HJ SHOK. rename HSX into HS. rename HJ5 into HJ. rename SHOK5 into SHOK.
  paj_run_tok_x_inv RUNM HS HJ SHOK HPM SD_Bspan; [sd_awr regs Usp5|].
  clear HF HG. sd_keep HFr KF regs W2 Usp5. clear HFr.
  prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold fpost, apost_base_x.
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp2, r, m, d, (0 + k1) end.
  split; [cbn [ms_regs]; rewrite R1, OLD5, OLD3, OLD1, E1 by (cbv; lia); rewrite Hra; reflexivity|].
  split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARc LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HS); [exact HAE5 | vm_compute; reflexivity]|].
  split; [|exact HPM].
  exists res. split; [cbn [ms_regs]; rewrite R10, OLD5, E3a0 by (cbv; lia); reflexivity|].
  (* room_live_cf S2, the hull use and the two position arms: fuzz_malloc's, at n = len + 1 (strdup's S' is
     malloc's S2, and the strlen call before it keeps the allocator state S) *)
  split; [sd_conj_pick HMP|]. split; [sd_conj_pick HMP|]. split; [sd_conj_pick HMP|]. split; [sd_conj_pick HMP|].
  (* THE OUTCOME: strdup returns malloc's res and ends at malloc's S2, and its event is malloc's
     HMal (len + 1 + cf_head); so it is fuzz_malloc's outcome conjunct at n = len + 1 *)
  split; [sd_conj_pick HMP|]. split.
  + apply (sd_alloc_post_kept (len + 1) ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem3 _ mem3 md3 ltac:(lia) Herr HAR3 HAPc).
    * intros a Ha Hn. cbn [ms_mem].
      rewrite (KF a ltac:(lia) ltac:(lia)), (Hfr5 a ltac:(lia) ltac:(lia) ltac:(lia)), (KE a ltac:(lia) ltac:(lia)).
      exact (KC a ltac:(lia) ltac:(lia)).
    * intros _. exists (cs ++ [0]). split; [rewrite length_app; cbn [length]; lia|].
      cbn [ms_mem]. apply (sd_garr8_move W W2 mem _ s res (cs ++ [0]) Hg).
      intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
      rewrite (KF (res + Z.of_nat j) ltac:(lia) ltac:(lia)), (Hcopy (Z.of_nat j) ltac:(lia)).
      apply Hsrc. lia.
  + intros _. cbn [ms_mem]. apply (sd_garr8_move W W2 mem _ s res (cs ++ [0]) Hg). intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    rewrite (KF (res + Z.of_nat j) ltac:(lia) ltac:(lia)), (Hcopy (Z.of_nat j) ltac:(lia)).
    apply Hsrc. lia.
Qed.
End f.

(* THE INSTANCE: B := image B's generated binding TfibB (lib/Reusable/YD2l.v), TS discharged by YD2l.TfibB_syms. The
   callee texts FMALLOC and AI and the stand-in PAL stay premises, at TfibB. *)
Definition fuzz_strdup_holds_B_TfibB := fuzz_strdup_holds_B YD2l.TfibB YD2l.TfibB_syms.
End d.
