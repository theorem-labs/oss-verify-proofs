(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE3m.v, with its module paths and module names changed; 246 of its 289 lines of code are new or changed and 1491 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_fuzz_alloc_base.v at a working branch 0d38fb8ac64, relocated A->B by
   Theorem Labs tools over the unstripped twins, every image numeral re-derived by symbol / section / string
   content and checked by revcheck (reports in (internal path)). Imports: lib.Reusable kernel kept;
   the per-image root files from lib.ReusableB; fm's own per-image files from lib.B; FMupoison shared from lib.A. *)
(* fuzz/alloc.c walks at fm.asan addresses: the code table of alloc.c's four counters (0x81e24..0x81e74, 20 words),
   the read cell of an alloc.c static, and the close of a leaf that keeps memory (fpre -> fpost). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0s YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YB13 YF0m YF0x YE2y.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma fma_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma fma_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
unfold tfibsegs, AsanUbsan.M.loaded_segments in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.

(* alloc.c's four counters: 0x81e24 .. 0x81e74 (fm-fn-measure.md section 1, rows 13-16) *)
Definition tbl_fma : ctable := Eval vm_compute in build_table tfibsegs A_fuzz_alloc_live 20 TEmpty.
Lemma tbl_fma_eq : tbl_fma = build_table tfibsegs A_fuzz_alloc_live 20 TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_fma). Qed.
Lemma tbl_fma_ok : table_ok tfibsegs tbl_fma.
Proof. rewrite tbl_fma_eq. apply build_table_ok0. unfold A_fuzz_alloc_live. lia. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* an 8-byte static the walk reads (base None: absolute address), its value the env atom n *)
Definition fm_rcell (a : Z) (n : nat) : YP09.region :=
  YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SOff n 0))].

Lemma region_ok_fm_rcell : forall E (m : word -> option byte) a k v,
  val_mem tfibsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  region_ok tfibsegs E m (fm_rcell a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, fm_rcell.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E m 0 a 8 (SOff k 0) v); [| exact Hr | cbn; lia | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hr. f_equal. lia.
Qed.

(* the same cell, writable: alloc.c's statics live in fm.asan-ubsan's rw window 0x99000..0x5f7000 (YB13.v tfib_rw_window) *)
Definition fm_wcell (a : Z) (n : nat) : YP09.region :=
  YP09.mkRegion None a (a + 8) a (a + 8) [YP09.mkChunk a (CVal 8 (SOff n 0))].

Lemma fma_rw : forall (m : word -> option byte) a, 0x99000 <= a < 0x5f7000 -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold writable_at. apply YB13.tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha.
Qed.

Lemma region_ok_fm_wcell : forall E (m : word -> option byte) a k v,
  val_mem tfibsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  0x99000 <= a -> a + 8 <= 0x5f7000 ->
  region_ok tfibsegs E m (fm_wcell a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, fm_wcell.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; apply fma_rw; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E m 0 a 8 (SOff k 0) v); [| exact Hr | cbn; lia | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hr. f_equal. lia.
Qed.

(* reading an 8-byte cell back out of a symbolic state's regions (donor A/AE3m.v:491-517) *)
Definition find_chunk8 (rs : smem) (i : nat) (off : Z) : option sv :=
  match nth_error rs i with
  | Some r => match YP09.r_base r with
    | None => match List.find (fun c => YP09.c_off c =? off) (YP09.r_chunks r) with
      | Some (YP09.mkChunk _ (CVal n e)) => if (n =? 8)%N then Some e else None
      | _ => None end
    | Some _ => None end
  | None => None
  end.

Lemma val_mem_of_chunk8 : forall E (m : word -> option byte) (rs : smem) i off e v,
  mem_ok tfibsegs E m rs -> find_chunk8 rs i off = Some e ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs m off 8 v.
Proof.
intros E m rs i off e v (Hwf & Hrs & Hpd) Hf He Hv. unfold find_chunk8 in Hf.
destruct (nth_error rs i) as [r|] eqn:Hi; [|discriminate].
destruct (YP09.r_base r) as [b|] eqn:Hb; [discriminate|].
destruct (List.find (fun c => YP09.c_off c =? off) (YP09.r_chunks r)) as [[co cv]|] eqn:Hfd; [|discriminate].
destruct cv as [n e'| | |]; try discriminate. destruct (N.eqb_spec n 8) as [->|Hn]; [|discriminate].
injection Hf as ->.
apply find_some in Hfd as [Hin Hoff]. apply Z.eqb_eq in Hoff. cbn [YP09.c_off] in Hoff. subst co.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck.
rewrite <- (Z.add_0_l off). apply (val_of_chunk_ok tfibsegs E m 0 off 8 e v Hck He); cbn; lia.
Qed.

Lemma fma_in_img : forall a, 0x99000 <= a < 0x5f7000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (E : tfibsegs = [AsanUbsan_segment_000; AsanUbsan_segment_001; AsanUbsan_segment_002; AsanUbsan_segment_003]) by reflexivity.
destruct (Z.lt_ge_cases a 0x9b000).
- exists AsanUbsan_segment_002. split; [rewrite E; cbn; tauto | cbn; lia].
- exists AsanUbsan_segment_003. split; [rewrite E; cbn; tauto | cbn; lia].
Qed.

Lemma pairwise_cross : forall {X} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y HP Hx Hy; cbn in Hx; [destruct Hx|].
cbn in HP. destruct HP as [Hf Hp]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.

(* the four alloc.c statics are 8-byte cells of the read-write image below the shadow; a walk that writes one of
   them carries it in the journal footprint FM_PSTAT_FP (FMH_Base.v), which the image clause exempts *)
Lemma fm_pstat_range : forall g, In (g, g + 8) FM_PSTAT_FP -> 0x99000 <= g /\ g + 8 <= 0x5f7000.
Proof.
intros g Hg. cbv [FM_PSTAT_FP G_FAIL G_LIVE G_PEAK G_COUNT] in Hg. cbn in Hg.
destruct Hg as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

Lemma fm_pstat_inFP : forall g a, In (g, g + 8) FM_PSTAT_FP -> g <= a < g + 8 -> inFP FM_PSTAT_FP a.
Proof. intros g a Hg Ha. exists (g, g + 8). split; [exact Hg | cbn; lia]. Qed.

Lemma st_ok_mem_ok : forall E ss (H : word -> bool) ms,
  st_ok tfibsegs E ss (restrict H ms) -> mem_ok tfibsegs E (mrestrict H (ms_mem ms)) (ss_mem ss).
Proof. intros E ss H ms (_ & _ & _ & _ & _ & _ & _ & HM & _). exact HM. Qed.

(* a value read from memory survives a change that misses its bytes *)
Lemma val_mem_kept : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs H m' (a + i) = aview tfibsegs H m (a + i)) ->
  val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hv Hk k Hk2.
rewrite (mbyte_of_aview H H m m' (a + Z.of_nat k) (Hk (Z.of_nat k) ltac:(lia))).
exact (Hv k Hk2).
Qed.

Lemma aview_some_of_val_mem : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v i,
  val_mem tfibsegs (mrestrict H m) a n v -> 0 <= i < Z.of_nat n -> aview tfibsegs H m (a + i) <> None.
Proof.
intros H m a n v i Hv Hi. unfold aview.
rewrite <- (Z2Nat.id i ltac:(lia)). rewrite (Hv (Z.to_nat i) ltac:(lia)). discriminate.
Qed.

Variable B : asyms.
#[local] Notation LAWS := (AR_laws_ok tfibsegs B).

(* restated from lib/A/AD1k.v:148-170 (same proofs), so that this file does not import AD1k's driver chain *)
Lemma fma_img_not_owned : forall ly S (W : world tfibsegs) mem md a,
  AR tfibsegs B ly S W mem md -> YF0x.TFIB_IMG_LO <= a < YF0x.TFIB_IMG_END ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S W mem md a (M & L & _) Ha Hst [OW _]. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (YF0x.img_cover_of_ledger _ _ _ L) as [I1 I2]. unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct OW as [O|[O|[O|[O|O]]]].
- exact (Hst O).
- pose proof (owned_extents_bound ly a LO O) as (_ & _ & X). apply X. unfold in_zr. cbn [fst snd]. lia.
- pose proof (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O])) as (_ & _ & X).
  apply X. unfold in_zr. cbn [fst snd]. lia.
- pose proof (owned_sec_bound B ly S _ a M O) as (_ & _ & X). apply X. unfold in_zr. cbn [fst snd]. lia.
- pose proof (owned_shadow_bound B ly S _ a M O) as X. unfold SHADOW_OFF in X. lia.
Qed.

Lemma fma_not_owned_static : forall lo hi a, TfibSyms B ->
  forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) Tfib_owned_static = true -> lo <= a < hi ->
  ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros lo hi a TB Hc Ha HE. rewrite (ts_owned B TB) in HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
pose proof (proj1 (forallb_forall _ _) Hc r Hr) as Hb. cbn beta in Hb.
apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* alloc.c's statics are image bytes the runtime does not own (AF0m Tfib_owned_static) *)
Lemma fma_pstat_not_owned : TfibSyms B -> forall ly S (W : world tfibsegs) mem md g a,
  AR tfibsegs B ly S W mem md -> In (g, g + 8) FM_PSTAT_FP -> g <= a < g + 8 -> ~ aowned B ly S a.
Proof.
intros HB ly S W mem md g a HAR Hg Ha.
pose proof (fm_pstat_range g Hg) as [Hg1 Hg2].
apply (fma_img_not_owned ly S W mem md a HAR);
  [unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END; lia|].
cbv [FM_PSTAT_FP G_FAIL G_LIVE G_PEAK G_COUNT] in Hg. cbn in Hg.
destruct Hg as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; subst g.
- apply (fma_not_owned_static 0x9e260 0x9e268 a HB); [vm_compute; reflexivity | lia].
- apply (fma_not_owned_static 0x5d4700 0x5d4708 a HB); [vm_compute; reflexivity | lia].
- apply (fma_not_owned_static 0x5d4720 0x5d4728 a HB); [vm_compute; reflexivity | lia].
- apply (fma_not_owned_static 0x5d4740 0x5d4748 a HB); [vm_compute; reflexivity | lia].
Qed.

(* AR survives a write of one alloc.c static: the cell is not runtime-owned, is below the shadow band, and the
   bytes written stay visible *)
Lemma AR_write_static : TfibSyms B -> forall ly S (W : world tfibsegs) mem md mem' g,
  AR tfibsegs B ly S W mem md -> In (g, g + 8) FM_PSTAT_FP ->
  (forall x : word, ~ (g <= bv_unsigned x < g + 8) -> mem' x = mem x) ->
  (forall i, 0 <= i < 8 -> aview tfibsegs (w_H W) mem' (g + i) <> None) ->
  AR tfibsegs B ly S W mem' md.
Proof.
intros HB ly S W mem md mem' g HAR Hg Hraw Hvis.
pose proof (fm_pstat_range g Hg) as [Hg1 Hg2].
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (g <= a < g + 8) ->
  aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hc. apply aview_eq_of. unfold mrestrict. rewrite Hraw; [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hc. }
apply (al_frame _ _ LAWS ly S W mem md mem' md HAR).
- intros a Ha Ho. apply AV; [exact Ha|]. intros Hc.
  exact (fma_pstat_not_owned HB ly S W mem md g a HAR Hg Hc Ho).
- intros a Hv. rewrite (YE2y.aview_mod _ mem' a). rewrite (YE2y.aview_mod _ mem a) in Hv.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  set (a' := a mod 2 ^ 64) in *.
  destruct (Z_le_gt_dec g a') as [L1|L1]; [destruct (Z_lt_ge_dec a' (g + 8)) as [L2|L2]|].
  + replace a' with (g + (a' - g)) by lia. apply Hvis. lia.
  + rewrite AV by lia. exact Hv.
  + rewrite AV by lia. exact Hv.
- reflexivity.
- reflexivity.
- reflexivity.
- intros a Hb Hh. unfold YG0d.w64. apply Hraw.
  unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb.
  rewrite unsigned_lit_small by lia. lia.
Qed.

(* one alloc.c static written, the stack frame used, nothing else: the donor journal holds, because the static's
   8 bytes are in the journal footprint FM_PSTAT_FP that the image clause exempts. *)
Lemma ajournal_pstat1 : forall STK ly S (W : world tfibsegs) regs mem md ch mem' g,
  afn_pre tfibsegs B STK ly S W regs mem md ch ->
  In (g, g + 8) FM_PSTAT_FP ->
  AR tfibsegs B ly S W mem' md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> ~ (g <= a < g + 8) ->
     aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem' a) ->
  ajournal tfibsegs B STK (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W mem' md 0.
Proof.
intros STK ly S W regs mem md ch mem' g HPRE Hg HAR' Heq Hpres'.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HAR as (M & L & _).
pose proof (am_layout B ly S _ M) as HLY.
pose proof (lo_stk_ceil ly HLY) as LSC.
pose proof (YF0x.img_cover_of_ledger _ _ _ L) as [IC1 IC2]. unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in IC1, IC2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fm_pstat_range g Hg) as [Hg1 Hg2].
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
assert (HNOG : forall a, 4096 <= a < ASAN_CEIL -> ~ (spZ regs - STK <= a < spZ regs)).
{ intros a Ha Hs. unfold ASAN_CEIL in Ha. lia. }
assert (HGEX : forall a, ~ inFP FM_PSTAT_FP a -> ~ (g <= a < g + 8)).
{ intros a Hp Hgc. exact (Hp (fm_pstat_inFP g a Hg Hgc)). }
assert (HIMG : forall a, ~ in_img tfibsegs a -> ~ (g <= a < g + 8)).
{ intros a Hn Hgc. apply Hn. apply fma_in_img. lia. }
split; [exact HAR'|].
split; [apply layout_le_refl|].
split; [apply Nat.le_refl|].
split; [apply wle_refl|].
split; [apply aos_step_refl|].
split; [reflexivity|].
split; [lia|]. split; [lia|].
split.
{ intros a Ha Hs. apply Heq; [lia | exact Hs | intros Hgc; lia]. }
split.
{ intros p n i H1 H2 Hi Hnf.
  destruct (al_blocks _ _ LAWS ly S W mem' md p n HAR' H1) as (_ & H4096 & Hpc & Happ & _ & _).
  pose proof (app_addr_below_ceil (p + i) (in_app_addr p (req_size n) (p + i) Happ ltac:(lia))) as Hab.
  destruct (al_client_img _ _ LAWS ly S W mem' md (p + i) HAR'
    ltac:(left; exists p, n; split; [exact H1 | lia])) as [_ Hni].
  apply Heq; [unfold ASAN_CEIL in Hab; lia | exact (HNOG _ Hab) | exact (HIMG _ Hni)]. }
split.
{ intros a Hi Hns He Hps Hsp.
  pose proof (fma_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  apply Heq; [lia | intros Hs; lia | exact (HGEX _ Hps)]. }
split.
{ intros cid pos a Hin Hr Hnf.
  destruct (al_frames _ _ LAWS ly S W mem' md cid pos HAR' Hin) as (_ & Happ & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  assert (Hfa : 4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= ASAN_CEIL).
  { destruct Happ as [Hf0 [Hf1 | [Hf1 Hf2]]]; cbv [ASAN_CEIL kLowShadowBeg] in *; lia. }
  destruct Hr as [Hr | Hr].
  - unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    pose proof (app_addr_below_ceil a (in_app_addr (frame_addr ly cid pos) (fs_frame_bytes cid) a Happ ltac:(lia))) as Hab.
    destruct (al_client_img _ _ LAWS ly S W mem' md a HAR'
      ltac:(right; left; exists cid, pos; split; [exact Hin | lia])) as [_ Hni].
    apply Heq; [unfold ASAN_CEIL in Hab; lia | exact (HNOG _ Hab) | exact (HIMG _ Hni)].
  - unfold in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(cbv [ASAN_CEIL] in Hfa; lia)) as [Hs1 Hs2].
    assert (Hfb8 : 0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid).
    { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
    cbv [kLowMemEnd kHighShadowEnd ASAN_CEIL] in *.
    apply Heq; [lia | intros Hs; lia | intros Hgc; lia]. }
split.
{ intros p n i H1 H2 Hi. exfalso. exact (H2 H1). }
split; [exact Hpres'|].
split; [exact Hstk|].
split; [|exact HQT].
intros a Hex He.
pose proof (lo_extra ly HLY) as (_ & HEF & HED).
apply Exists_exists in Hex as (e & Hin & Hr). unfold in_zr in Hr.
pose proof (proj1 (Forall_forall _ _) HEF e Hin) as (_ & Hpos & H4096 & Hce & _).
assert (Hdisj : zdisjoint e (ly_img ly)).
{ apply (pairwise_cross zdisjoint (ly_extra ly) (static_extents ly) e (ly_img ly) HED Hin).
  unfold static_extents. apply in_or_app. right. right. left. reflexivity. }
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
apply Heq; [unfold ASAN_CEIL in Hce; lia | intros Hs; unfold ASAN_CEIL in Hce; lia | intros Hgc; lia].
Qed.
(* a leaf that changes no memory returns through fpost: journal from afn_pre, nothing allocated *)
Lemma fpost_keep : forall STK ly S (W : world tfibsegs) regs mem md ch regs' X
  (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  afn_pre tfibsegs B STK ly S W regs mem md ch ->
  aregs_preserved regs regs' ->
  Q ly S W regs' mem (with_vm_backing (m_vm_lazy md) X md) ->
  fpost tfibsegs B STK [] regs ly S W mem md 0 Q W
    (mkCfg (mkst regs' (getr regs 1) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) X md)).
Proof.
intros STK ly S W regs mem md ch regs' X Q HPRE HP HQ.
unfold fpost, apost_base.
exists ly, S, regs', mem, (with_vm_backing (m_vm_lazy md) X md).
split; [reflexivity|].
split; [eapply (ajournal_materialize tfibsegs B (AR_laws_ok tfibsegs B) fma_segs_low);
  exact (ajournal_init tfibsegs B STK [] ly S W regs mem md ch HPRE)|].
split; [exact HP | exact HQ].
Qed.

End c.
