(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (asan #102 pin 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4), the
   walk of same: memory facts, part A. A tree the kit's tsame_specX gives at the entry (prhex_tree: the representation, a
   home, the root's 56 bytes addressable) stays the same tree at every later point of the walk, read from the journal
   ajournal_x that runs from the entry to that point: the bytes of its footprint are kept (sma_foot_keep), so the
   representation holds over the current memory (sma_node_now), and the root's shadow is still addressable
   (sma_ra_now). The read-only image bytes keep their view (sma_ro_now): that arodata_okP is what the strcmp row's
   read-only-premise form asks for (YGcallMxmn.v aj_strcmp_at_xrom). Taken from the image-B' file lib/B/Prog/SameB_memA.v
   (a working branch e95b6ce78e87; the port of the old-A walk's lib/A/Prog/Wsame_memA.v at
   a working branch 9a0674f0b5f2 to the #102 kit: the ledger carries most / own, prh_pst lists
   seven statics), renamed smb_ -> sma_, at image A's PrhImg prh_img_A. No image constant, no address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import SameAp_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* every block a tree's footprint lists is a block of the block predicate (the harness blocks, at prh_lin Lam) *)
Lemma sma_D_lblk : forall segs (m : word -> option byte) (Lb : Z -> Z -> Prop) t p D,
  pj_nodeR segs m Lb p t D -> Forall (fun b => Lb (fst b) (snd b)) D.
Proof using.
intros segs m Lb t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros p D H; cbn [pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb).
- destruct Hb as (_ & _ & _ & _ & _ & ->). constructor.
- destruct Hb as (_ & _ & _ & _ & _ & ->). constructor.
- destruct Hb as (_ & _ & _ & _ & _ & ->). constructor.
- destruct Hb as (_ & _ & _ & _ & _ & k & (HL & _) & ->). constructor; [exact HL | constructor].
- destruct Hb as (_ & _ & _ & _ & k & (HL & _) & ->). constructor; [exact HL | constructor].
- destruct Hb as (_ & _ & _ & _ & Hcap & Di & -> & Hi). apply Forall_app. split.
  + destruct (Z.eqb_spec cap 0) as [C|C]; [constructor|].
    destruct Hcap as [(C0 & _)|(_ & HL)]; [lia|]. constructor; [exact HL | constructor].
  + clear Hcap. revert kids Di Hi. induction IH as [|u r Hu Hr IHr]; intros a Di Hi; cbn [pj_itemsR] in Hi.
    * subst Di. constructor.
    * destruct Hi as (D1 & D2 & -> & H1 & H2). apply Forall_app.
      split; [exact (Hu a D1 H1) | exact (IHr (a + 56) D2 H2)].
- destruct Hb as (_ & _ & _ & Hcap & Di & -> & Hi). apply Forall_app. split.
  + destruct (Z.eqb_spec cap 0) as [C|C]; [constructor|].
    destruct Hcap as [(C0 & _)|(_ & HL1 & HL2)]; [lia|].
    constructor; [exact HL1 | constructor; [exact HL2 | constructor]].
  + clear Hcap. revert kids keys Di Hi. induction IH as [|x r Hu Hr IHr]; intros a ka Di Hi.
    * cbn [pj_memsR] in Hi. subst Di. constructor.
    * destruct x as [nm u]. cbn [pj_memsR] in Hi.
      destruct Hi as (y & k & D1 & D2 & -> & _ & (HL & _) & H1 & H2). constructor; [exact HL|]. apply Forall_app.
      split; [exact (Hu a D1 H1) | exact (IHr (a + 56) (ka + 8) D2 H2)].
Qed.

(* two readers agree on the bytes of a value both read at the same width *)
Lemma sma_val_aview : forall segs (H H' : word -> bool) (mem mem' : word -> option byte) g n v x,
  val_mem segs (mrestrict H mem) g n v -> val_mem segs (mrestrict H' mem') g n v -> in_zr x (g, Z.of_nat n) ->
  aview segs H' mem' x = aview segs H mem x.
Proof using.
intros segs H H' mem mem' g n v x V V' Hx. unfold in_zr in Hx. cbn [fst snd] in Hx.
assert (Hk : (Z.to_nat (x - g) < n)%nat) by lia.
pose proof (V _ Hk) as E1. pose proof (V' _ Hk) as E2.
rewrite Z2Nat.id in E1, E2 by lia. replace (g + (x - g)) with x in E1, E2 by lia.
unfold aview. rewrite E1, E2. reflexivity.
Qed.

Lemma sma_in_zr_dec : forall a r, {in_zr a r} + {~ in_zr a r}.
Proof using.
intros a [lo len]. unfold in_zr. cbn [fst snd].
destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (lo + len)); [left; lia | right; lia] | right; lia].
Qed.

Context {L : ptable asym} {PA : PAImg L}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the allocator laws at the harness head length cf_head; field 14 (alx_hshadow) is the hidden-head block shadow law *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx cf_head.
(* the three allocator facts of lib/B/Prog/SameAp_walk.v's Section W (derived there from SMA_CF, ARx refining ARcf) *)
Hypothesis SMA_BMAX : forall ly S Hp (W : world pa_segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n < cf_malloc_max.
Hypothesis SMA_STK64 : forall ly S Hp (W : world pa_segs) mem md, ARx ly S Hp W mem md -> ly_stk_hi ly mod 64 = 0.
Hypothesis SMA_FR64 : forall ly S Hp (W : world pa_segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0.
Let HSL : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd := pa_segs_low.
Local Notation PST := (prh_pst (PI := prh_img_A)).

(* the footprint of a tree at the entry is kept by a journal from the entry that leaves the allocator blocks as they
   were; every byte of it lies outside the image, in [0, 2 ^ 64) *)
Lemma sma_foot_keep : forall STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 z,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_tree ly S Lam W regs mem p t D ->
  ajournal_x (SK := SK) pa_segs B PST ARx STK (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 ->
  ablocks B ly1 S1 = ablocks B ly S ->
  pj_footR p D z ->
  ~ in_img pa_segs z /\ 0 <= z < 2 ^ 64 /\ aview pa_segs (w_H W1) mem1 z = aview pa_segs (w_H W) mem z.
Proof using LAWS SMA_BMAX SMA_STK64 SMA_FR64.
intros STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 z HAR HL HT HJ HB Hz.
destruct HT as (Hn & Hh & _).
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & Hstk & Hblk & _ & Hfrm & _ & _ & Hastk & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* a byte of a harness block: the journal's live-block clause on its allocator block *)
assert (LAMK : forall b m, In (b, m) Lam -> b <= z < b + m ->
  ~ in_img pa_segs z /\ 0 <= z < 2 ^ 64 /\ aview pa_segs (w_H W1) mem1 z = aview pa_segs (w_H W) mem z).
{ intros b m Hin Hr. destruct HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk0 & _). cbn [fst snd] in *.
  pose proof (@cf_head_nonneg cp) as Hc0.
  destruct (alx_blocks pa_segs B ARx LAWS ly S Hp W mem md _ _ HAR Hblk0) as (_ & H4096 & Hcl & Happ & _).
  assert (Hmc : 0 <= m + cf_head) by lia. pose proof (req_size_pos (m + cf_head) Hmc) as [Hq1 Hq2].
  assert (Hzr : b - cf_head <= z < b - cf_head + req_size (m + cf_head)) by lia.
  split; [exact (blk_img_x pa_segs B ARx LAWS ly S Hp W mem md _ _ z HAR Hblk0 Hzr)|].
  split; [pose proof (app_addr_below_ceil z (in_app_addr _ _ z Happ Hzr)) as Ha; unfold ASAN_CEIL in Ha; lia|].
  assert (Hblk1 : In (b - cf_head, m + cf_head) (ablocks B ly1 S1)) by (rewrite HB; exact Hblk0).
  assert (Hi0 : 0 <= z - (b - cf_head) < req_size (m + cf_head)) by lia.
  pose proof (Hblk (b - cf_head) (m + cf_head) (z - (b - cf_head)) Hblk0 Hblk1 Hi0 (inFP_nil _)) as E.
  replace (b - cf_head + (z - (b - cf_head))) with z in E by lia. exact E. }
destruct Hz as [Hz | ([b m] & HbD & Hhold)].
- destruct Hh as [(b & m & Hin & Hb1 & Hb2) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
  + apply (LAMK b m Hin). lia.
  + destruct (frames_bounds_x pa_segs B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
    assert (Hzr : frame_addr ly cid pos <= z < frame_addr ly cid pos + fs_frame_bytes cid) by lia.
    split; [exact (frm_img_x pa_segs B ARx LAWS ly S Hp W mem md cid pos z HAR Hin Hzr)|].
    split; [pose proof (app_addr_below_ceil z (in_app_addr _ _ z Hfa Hzr)) as Ha; unfold ASAN_CEIL in Ha; lia|].
    apply (Hfrm cid pos z Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; exact Hzr | apply inFP_nil].
  + destruct Hastk as (_ & Hs0 & Hceil & Hlo & Hhi & H47 & _).
    split; [intros Hi; pose proof (pa_segs_low z Hi); lia|].
    split; [lia|].
    apply Hstk; lia.
- pose proof (sma_D_lblk _ _ _ _ _ _ Hn) as HF. rewrite Forall_forall in HF.
  specialize (HF (b, m) HbD). unfold prh_lin in HF. cbn [fst snd] in HF.
  unfold pj_holdsR in Hhold. cbn [fst snd] in Hhold. exact (LAMK b m HF Hhold).
Qed.

(* so the tree is the same tree over the memory of the later point *)
Lemma sma_node_now : forall STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_tree ly S Lam W regs mem p t D ->
  ajournal_x (SK := SK) pa_segs B PST ARx STK (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 ->
  ablocks B ly1 S1 = ablocks B ly S ->
  pj_nodeR pa_segs (mrestrict (w_H W1) mem1) (prh_lin Lam) p t D.
Proof using LAWS SMA_BMAX SMA_STK64 SMA_FR64.
intros STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 HAR HL HT HJ HB.
pose proof HT as (Hn & _ & _).
apply (pj_nodeR_frame pa_segs t _ _ _ p D Hn).
intros x Hx.
destruct (sma_foot_keep STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 x
  HAR HL HT HJ HB Hx) as (Hni & Hr & E).
exact (sma_agree_of_aview pa_segs (w_H W) (w_H W1) mem mem1 x Hr Hni E).
Qed.

(* and its root's 56 bytes are still addressable (a harness block: the hidden-head shadow law at the later state; a
   fake frame: the journal keeps the frame's shadow; the real stack: the stack's zero shadow at the later state) *)
Lemma sma_ra_now : forall STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_tree ly S Lam W regs mem p t D ->
  ajournal_x (SK := SK) pa_segs B PST ARx STK (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 ->
  ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  range_addressable (aview pa_segs (w_H W1) mem1) SHADOW_OFF p 56.
Proof using LAWS SMA_BMAX SMA_STK64 SMA_FR64.
intros STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 HAR HL HT HJ HB EHp.
destruct HT as (Hn & Hh & Hra & _).
pose proof HJ as (HAR1 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm & _ & _ & Hastk & _ & _).
subst Hp1.
destruct Hh as [(b & m & Hin & Hb1 & Hb2) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
- (* a harness block: the hidden-head shadow law at the later state *)
  destruct HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk0 & Hhp & _). cbn [fst snd] in *.
  pose proof (@cf_head_nonneg cp) as Hc0.
  assert (Hmc : 0 <= m + cf_head) by lia. pose proof (req_size_pos (m + cf_head) Hmc) as [Hq1 Hq2].
  assert (Hblk1 : In (b - cf_head, m + cf_head) (ablocks B ly1 S1)) by (rewrite HB; exact Hblk0).
  destruct (alx_hshadow pa_segs B ARx LAWS ly1 S1 Hp W1 mem1 md1 _ _ HAR1 Hblk1 Hhp) as [Hbs _].
  apply (sma_ra_of_bshadow _ _ _ _ _ Hbs); lia.
- (* a fake frame: the journal keeps the frame's shadow *)
  destruct (SMA_FR64 ly S Hp W mem md cid pos HAR Hin) as [F1 F2].
  apply (sma_ra_keep _ _ _ _ _ Hra). intros y Hy. unfold shadow_of_addr.
  apply (Hfrm cid pos (SHADOW_OFF + y / 8) Hin); [right | apply inFP_nil].
  unfold in_zr, shadow_addr. cbn [fst snd]. clear - F1 F2 Hf1 Hf2 Hy. Z.div_mod_to_equations. lia.
- (* the real stack: its zero shadow at the later state *)
  destruct Hastk as (_ & Hs0 & Hceil & Hlo & Hhi & H47 & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  apply sma_ra_zero. intros y Hy. unfold shadow_of_addr.
  apply (alx_zshadow_byte pa_segs B ARx LAWS ly1 S1 Hp W1 mem1 md1 y HAR1). rewrite Elo, Ehi. lia.
Qed.

(* the read-only image bytes keep their view: a byte of the program's statics PST holds the same value at both ends
   (the ledger, at the same Lam peak cnt fail ran most own: #102's seven statics), every other image byte is kept by the journal's image clause *)
Lemma sma_ro_now : forall STK sp0 ly S Hp W mem md Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 k1,
  arodata_okP pa_segs pa_relro_lo pa_relro_hi B (aview pa_segs (w_H W) mem) ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PI := prh_img_A) B ly1 S1 Hp1 W1 mem1 Lam peak cnt fail ran most own ->
  ajournal_x (SK := SK) pa_segs B PST ARx STK sp0 [] ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 ->
  arodata_okP pa_segs pa_relro_lo pa_relro_hi B (aview pa_segs (w_H W1) mem1).
Proof using LAWS SMA_BMAX SMA_STK64 SMA_FR64.
intros STK sp0 ly S Hp W mem md Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 k1 HRO HL HL1 HJ a Hro Ho He.
transitivity (aview pa_segs (w_H W) mem a); [|exact (HRO a Hro Ho He)].
destruct (Exists_dec (in_zr a) PST (sma_in_zr_dec a)) as [Hx | Hnx].
- (* a static of alloc.c: both ledgers read the same values there *)
  destruct HL as ((G1 & G2 & G3 & G4 & G5 & (G6 & _) & (G7 & _) & _) & _).
  destruct HL1 as ((G1' & G2' & G3' & G4' & G5' & (G6' & _) & (G7' & _) & _) & _).
  rewrite Exists_exists in Hx. destruct Hx as (r & Hr & Hx). unfold prh_pst in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
  + exact (sma_val_aview _ _ _ _ _ _ _ _ a G1 G1' Hx).
  + exact (sma_val_aview _ _ _ _ _ _ _ _ a G2 G2' Hx).
  + exact (sma_val_aview _ _ _ _ _ _ _ _ a G3 G3' Hx).
  + exact (sma_val_aview _ _ _ _ _ _ _ _ a G4 G4' Hx).
  + exact (sma_val_aview _ _ _ _ _ _ _ _ a G5 G5' Hx).
  + exact (sma_val_aview _ _ _ _ _ _ _ _ a G6 G6' Hx).
  + exact (sma_val_aview _ _ _ _ _ _ _ _ a G7 G7' Hx).
- (* any other read-only byte: the journal's image clause *)
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
  assert (Hi : in_img pa_segs a)
    by (destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)]).
  apply (Himg a Hi Ho He Hnx). apply fp_spares_closed. intros (r & Hin & _). destruct Hin.
Qed.

End m.
