(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1405 of its 1477 lines of code are new or changed and 442 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of tx_put on image A' (ASan build): segment S_GROW,
   from the cut TP_PC_GROW (+172, A' 0x84d98) to the cut TP_PC_FIT (+248) on a granted
   realloc, or TP_PC_NULL (+392) on a refused one.
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   PROVES tp_seg_GROW_holds : tp_seg_GROW_stmt B SK CTX0 (TxPut102A_Base.v): for the realloc wrapper's two callee
   texts at SIGMA AS___wrap_realloc (the primed keep row YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep at every
   headroom k and YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep, the statement's own binders) and every P with
   srr_inv_laws and srr_inv_call, tp_seg_GROW P (concluding SRr' segs RZ_cf).
   THE CODE (listing, the internal file tx_put.asan.new.s :45-63, byte offsets from the entry):
     +172 add s11,s10,s6 / +176 lbu a0,0(s11) / +180 bnez -> report_load8 (REFUTED: the record's shadow is
     addressable, prhtx_place) / +184 ld a0,0(s0) (b0) / +188 slli a1,a1,1 (2 * need) / +192 jal __wrap_realloc
     (ONE engine run +172 -> +192, then the call rule) / +196 beqz a0 -> +392 / +200 .. +244 the store check of t,
     sd a0,0(s0), the load checks of t + 8 and t + 16, ld / add / slli / addi (2 * (len0 + n + 1)), sd a0,0(s5)
     (tpg_tail: ONE run per arm) / +248 the FIT cut.
   THE CALL: cap0 > 0 -> YGcallRkKeep.aj_realloc_at_x_cfR_keep, the realloc rule over wle' segs RZ_cf with the
   memnorm keep in its leaf (headroom 0, the room RQ := qtight /\ ROOM_cf_k /\ cf_hull_adm, the hull admission from
   tp_img's tpi_hull_adm at the run position); cap0 = 0 -> YGcallRxKeep.aj_realloc_null_at_x_keep (text
   YGcallRxKeep.arealloc_null_realizes_x_cf_keep, model law TxPut102A_Rnull.realloc_null_model_law_x_cf 0), a malloc
   that frees nothing, at wle. Both leaves end in the memnorm keep, which carries P across the call (srr_inv_call). The
   run to the call is plain and is lifted ONCE, at the cut before the call (YGcfRhLift.ra_rh_of_SRr). The call's
   QMm_cf from room_live_cf (tp_pre), tpi_hull_ok and the carry's read-only view (YGcfAroBridge.arodata_ok_cf_of_P,
   with tpi_ro_reads_nw); the trace in the universe by TxPutCall102.tp_trace_universe from prhtx_trace.
   The call's own journal is rooted at the GROW cut (window ASTACK below the call's sp, footprint the old buffer), at
   wle' segs RZ_cf after the call; tpg_post_of_call composes it into tp_JR (ajournal_xw_subR) and tp_KR
   (cj_kept_transR / cj_kept_of_journalR) at wle'. The tail after the call runs over wle' (YC1fPx.paj_run_to_x_m_invR).
   AFTER THE CALL every carry comes from the call rule's own clauses (the journal, acall_kept_x, the leaf's frame),
   never from a whole-view keep: tpg_pst_after_call (the statics, from the leaf's frame), tpg_side_after_call (ledger,
   own, src_rd, prhtx_kept), tpg_blk_new / tpg_src_off_new (the new buffer), tpg_bytes_copy (the copy clause),
   tpg_inv_refused (the refused arm's buffer). The whole-view keeps of TxPutKeep102.v are used only across the two
   record stores after the call (high memory).
   THE RUN POSITION after the call is ONE lemma, tpg_pos_after_call (the text's restatement keyed on the run event is then
   a change of that lemma alone).
   SECTION HYPOTHESES: none. The callee texts are the statement's binders; the image facts are tp_img's fields;
   the allocator laws are AR_laws_ok_cf at YGcallcf's bridge (Let-bound, as FuzzFree.v).
   Numerals: 172 / 196 / 248 / 392 / 14288 (DERIVED offsets: the cuts, the return site, TP_OFF + 196), 8 / 16 / 24 /
   28 (LENGTH: record fields and its accessed bytes), 3 / 8 (the shadow shift and granule), register / atom numbers,
   4096 / 16 (LENGTH: lowest block, alignment), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (shadow span, stack band, word
   range). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YGcallRx YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRealloc ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm YCbqGcallW YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0lawscf YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require TxPutKeep102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102 TxPut102A_Base TxPut102A_Rnull.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallRkKeep YGcallRxKeep.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg A_prog_listing}.
(* the Base's three instances, by name, so every term here is the Base's syntactically *)
#[local] Existing Instances TP_PrhImg TP_PAListing TP_RL.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation RLO := (@pa_relro_lo _ _ PA).
#[local] Abbreviation RHI := (@pa_relro_hi _ _ PA).
(* the re-hiding move's zone and relation (the text's, PRH_FnTx.v) *)
#[local] Abbreviation RZc := YGcfRehidePost.RZ_cf.
#[local] Abbreviation RW := (wle' segs YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).

(* ---- the cf instance's laws (AR_laws_ok_cf at YGcallcf's bridge) ---- *)
Let LAWS_cf : AR_laws_cf segs B := AR_laws_ok_cf segs B.
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs segs B LAWS_cf.
Let WFL := ARx_wf_law_xs segs B.
Let XSL := ARx_xs_law_xs segs B.

(* the stack pointer at the call (the entry sp minus the frame), and the call's footprint: the old buffer *)
Definition tpg_spc (D : tp_in) : Z := tp_sp0 D - TP_FRAME.
Definition tpg_FP1 (D : tp_in) : list (Z * Z) :=
  if tp_cap0 D =? 0 then [] else ablocks_fp [(tp_b0 D, tp_cap0 D)].

Lemma tpg_STK : STK_tx_put = TP_FRAME + ASTACK.
Proof. vm_compute. reflexivity. Qed.

(* ---- WHAT THE CALL LEAVES (the post-call package; the cut predicates are assembled from it) ---- *)
(* every arm: the journal (at the call's wild-trace budget WS) and the keep from entry, Hp, the frame and the caller
   window kept, the read-only view *)
Definition tpg_post (D : tp_in) (W3 : world segs) (mem3 : word -> option byte)
  (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (k2 : Z)
  (WS : list (list Z)) : Prop :=
  tp_JR B SK RW D ly2 S2 (tp_Hp D) W2 mem2 md2 k2 WS /\ tp_KR B SK RW D ly2 S2 W2 mem2 md2 /\
  (forall a, tpg_spc D <= a < tp_sp0 D + tp_dw D -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) mem3 a) /\
  arodata_okP segs RLO RHI B (aview segs (w_H W2) mem2).
(* the granted arm: the new buffer (res, 2 * need) *)
Definition tpg_grown (D : tp_in) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
  (res : Z) : Prop :=
  tp_blk B D ly2 S2 W2 mem2 res (tp_req D) /\ bytes_at W2 mem2 res (tp_txt D) /\
  (forall a, tp_s D <= a < tp_s D + tp_n D -> ~ (res <= a < res + tp_req D)) /\
  prhtx_kept B (tp_Lam D) ly2 S2 (tp_s D) (tp_n D) /\
  prhtx_grow B (tp_ly D) (tp_S D) ly2 S2 (tp_b0 D) (tp_cap0 D) res (tp_req D) /\
  blocks_bytes S2 <= blocks_bytes (tp_S D) + tp_req D - tp_cap0 D /\
  tp_side B D ly2 S2 (tp_Hp D) W2 mem2 (tp_own D) /\ tp_pos D S2 0.

(* a plain keep (at wle) is one over every R that contains wle (only the world conjunct reads the relation) *)
Lemma tpg_kept_lift : forall (R : world segs -> world segs -> Prop), (forall W W', wle W W' -> R W W') ->
  forall STKf sp OR FPc lyc Sc (W : world segs) memc mdc ly2 S2 W2 mem2 md2,
  cj_kept (SK := SK) segs B prh_pst STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  cj_keptR (SK := SK) segs B prh_pst R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof.
intros R HR STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 (H1 & H2 & H3 & H4).
exact (conj H1 (conj H2 (conj (HR _ _ H3) H4))).
Qed.

(* ---- THE CALL'S BOOKKEEPING (pure; no engine) ---- *)
(* [GP1] the journal and the keep from entry across the call, the frame and the caller window kept, the read-only
   view: from the call's journal Jc rooted at the GROW cut (window ASTACK below the call's sp, footprint the old
   buffer) at the call's wild-trace budget WS1 (the batch kit realloc trace is wild: the rule posts it in the budget) and
   the carry at the GROW cut (budget []). The keep tp_K takes the call journal rebased at its own depot
   (YCbqGwild.ajournal_xw_rebase; cj_kept reads no depot) *)
Lemma tpg_post_of_call : forall D W3 mem3 md3 k ly2 S2 W2 mem2 md2 k1 WS1,
  tp_img B -> tp_pre B CTX0 D ->
  tp_J B SK D (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 k [] ->
  tp_K B SK D (tp_ly D) (tp_S D) W3 mem3 md3 ->
  arodata_okP segs RLO RHI B (aview segs (w_H W3) mem3) ->
  ajournal_xwR (SK := SK) segs B prh_pst (ARcfx B) RW ASTACK (tpg_spc D) (tpg_FP1 D)
    (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 [] ly2 S2 (tp_Hp D) W2 mem2 md2 k1 WS1 ->
  tpg_post D W3 mem3 ly2 S2 W2 mem2 md2 (k + k1) ([] ++ WS1).
Proof.
intros D W3 mem3 md3 k ly2 S2 W2 mem2 md2 k1 WS1 HI HP HJ HK HRO HC.
pose proof HP as (HFP & _ & _ & _ & _ & _ & _ & _ & HFW & _ & _ & _ & HINV & _).
destruct HFP as ((HAR0 & _) & _).
destruct HFW as (Hdw & _).
unfold tp_J in HJ.
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS3 & _).
pose proof HS3 as (_ & _ & _ & _ & _ & H47 & _ & Htop2 & Htop).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & C1 & _ & C3 & _ & _ & _ & HSC & _).
pose proof HSC as (_ & _ & Cceil & Cslo & _ & _ & _ & _ & _).
pose proof tpg_STK as EST.
assert (HAS : ASTACK = 16384) by reflexivity.
assert (HTF : TP_FRAME = 112) by reflexivity.
assert (HFP1 : forall a, inFP (tpg_FP1 D) a -> inFP (tp_FP D) a).
{ intros a (r & Hr & Hb). exists r. split; [|exact Hb]. unfold tp_FP, prhtx_fp. right. exact Hr. }
assert (Hsk : ~ YI16.sink_open_fp (tpg_FP1 D)).
{ unfold tpg_FP1. destruct (tp_cap0 D =? 0) eqn:Ec.
  - intros (r & Hr & _). destruct Hr.
  - apply sink_closed_ablocks_fp. constructor; [|constructor]. cbn [fst].
    destruct HINV as (_ & [(Hc0 & _) | (_ & _ & _ & _ & H4096 & _)]); [apply Z.eqb_neq in Ec; lia | lia]. }
assert (Hlo : tp_sp0 D + tp_dw D - (STK_tx_put + tp_dw D) <= tpg_spc D - ASTACK)
  by (unfold tpg_spc; rewrite EST; lia).
assert (Hhi : tpg_spc D <= tp_sp0 D + tp_dw D) by (unfold tpg_spc; lia).
unfold tpg_post. split.
{ pose proof (ajournal_xw_subR (SK := SK) segs B prh_pst (ARcfx B) LAWS (@pa_segs_low _ _ PA) RW (wle'_trans segs RZc)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ajournal_xwR_mono (SK := SK) segs B prh_pst (ARcfx B) (@wle segs) RW (wle_wle' segs RZc)
       _ _ _ _ _ (tp_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJ) HC Hlo Hhi) as HJ2.
  unfold tp_JR. apply HJ2. intros a Ha. left. exact (HFP1 a Ha). }
split.
{ unfold tp_KR. unfold tp_K in HK.
  pose proof (cj_kept_of_journalR (SK := SK) segs B prh_pst (ARcfx B) RW
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tp_OR D)
    (ajournal_xw_rebaseR (SK := SK) segs B prh_pst _ RW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as HK2.
  eapply (cj_kept_transR (SK := SK) segs B prh_pst (ARcfx B) LAWS RW (wle'_trans segs RZc));
    [exact (tpg_kept_lift RW (wle_wle' segs RZc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK) | exact HK2
    | exact HAR0 | exact HAR3 | | | | ].
  - assert (Hlo' : tp_sp0 D - STK_tx_put <= tpg_spc D - ASTACK) by (unfold tpg_spc; rewrite EST; lia).
    exact Hlo'.
  - unfold tpg_spc. lia.
  - intros a Ha. left. exact Ha.
  - intros a Ha. left. exact (HFP1 a Ha). }
split.
{ intros a Ha. apply C1; [unfold tpg_spc in *; lia | unfold tpg_spc in *; lia]. }
intros a Ha Ho He.
assert (Hi : in_img segs a).
{ destruct Ha as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
rewrite C3; [exact (HRO a Ha Ho He) | exact Hi | exact Ho | exact He | |].
- intros Hp. exact (tpi_pst_rw B HI a Hp Ha).
- apply fp_spares_closed. exact Hsk.
Qed.

(* an image byte is in no dead shadow a call re-hides (that set lies above kLowMemEnd) *)
Lemma tpg_img_not_dsn : forall ly S S' a, YGcfRehidePost.dead_shadow_new ly S S' a -> ~ in_img segs a.
Proof.
intros ly S S' a HD Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hl.
pose proof (YGcfRehidePost.dead_shadow_new_not_low ly S S' a HD) as Hn. lia.
Qed.

(* the statics after a call: the leaf's frame, which may except a set DS of no image byte (the re-hidden dead shadow) *)
Lemma tpg_pst_after_call : forall (W3 : world segs) mem3 ly S Hp md regs ly2 S2 Hp2 W2 mem2 md2 (E DS : Z -> Prop),
  tp_img B -> ARcfx B ly S Hp W3 mem3 md -> ARcfx B ly2 S2 Hp2 W2 mem2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly2 S2 a -> ~ ascratch B ASTACK regs a -> ~ E a ->
     ~ DS a -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) mem3 a) ->
  YM05.alloc_ceiling <= spZ regs - ASTACK ->
  (forall a, E a -> ~ in_img segs a) -> (forall a, DS a -> ~ in_img segs a) ->
  forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) mem3 a.
Proof.
intros W3 mem3 ly S Hp md regs ly2 S2 Hp2 W2 mem2 md2 E DS HI HAR HAR2 Hfr Hceil HE HDS a Ha.
pose proof (tpi_pst_img B HI a Ha) as Hi.
pose proof (@pa_segs_low _ _ PA a Hi) as Hl.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
apply Hfr.
- rewrite C5 in Hl. lia.
- intros Ho. apply (tpi_pst_owned B HI a Ha).
  exact (proj1 (alx_owned_image segs B (ARcfx B) LAWS ly S Hp W3 mem3 md a HAR Hi) Ho).
- intros Ho. apply (tpi_pst_owned B HI a Ha).
  exact (proj1 (alx_owned_image segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 a HAR2 Hi) Ho).
- intros [Hs | Herr]; [rewrite C5 in Hl; lia | exact (tpi_pst_errno B HI a Ha Herr)].
- intros HEa. exact (HE a HEa Hi).
- intros HDa. exact (HDS a HDa Hi).
Qed.

(* ---- [GP2] helpers ---- *)
(* the hull of a sub-range lies in the hull of the range (FuzzStrdup.v sd_hull_sub) *)
Lemma tpg_gp_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (YCbq.shadow_mono p d Hpd) as M1. pose proof (YCbq.shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* the hull of a range 64 bytes inside [lo, hi) is the shadow of bytes of [lo, hi) (FuzzStrdup.v sd_hull_img, over the
   instance's image bounds pa_lo / pa_hi since kept_at in the kit tree preset-tree-at-2026-10-29T17-47-10Z.tsv (sha256 9d6fcfaf6b8e; internal record)) *)
Lemma tpg_gp_hull_img : forall lo hi a n s, 0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ lo <= 8 * (s - SHADOW_OFF) < hi.
Proof.
intros lo hi a n s Hn Hlo Hhi Hs. unfold shadow_addr in *.
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

(* a byte of a 64-aligned frame has its shadow byte in the frame's shadow range *)
Lemma tpg_gp_frame_sh : forall fa fs x, fa mod 64 = 0 -> fs mod 64 = 0 -> fa <= x < fa + fs ->
  shadow_addr fa <= shadow_of_addr SHADOW_OFF x < shadow_addr fa + fs / 8.
Proof.
intros fa fs x H1 H2 Hx. unfold shadow_addr, shadow_of_addr.
pose proof (Z.div_mod fa 64 ltac:(lia)). pose proof (Z.div_mod fs 64 ltac:(lia)).
pose proof (Z.div_mod fa 8 ltac:(lia)). pose proof (Z.mod_pos_bound fa 8 ltac:(lia)).
pose proof (Z.div_mod fs 8 ltac:(lia)). pose proof (Z.mod_pos_bound fs 8 ltac:(lia)).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
lia.
Qed.

(* the shadow hull of a sub-range of a 64-aligned frame lies in the frame's shadow range *)
Lemma tpg_gp_frame_hull : forall fa fs p n y, fa mod 64 = 0 -> fs mod 64 = 0 -> fa <= p -> p + n <= fa + fs -> 0 < n ->
  shadow_addr p / 8 * 8 <= y < shadow_addr (p + n - 1) / 8 * 8 + 8 ->
  shadow_addr fa <= y < shadow_addr fa + fs / 8.
Proof.
intros fa fs p n y H1 H2 Hp Hpn Hn Hy.
apply Z.mod_divide in H1 as [A EA]; [|lia]. apply Z.mod_divide in H2 as [F EF]; [|lia]. subst fa fs.
pose proof (YCbq.shadow_mono (A * 64) p Hp) as M1.
pose proof (YCbq.shadow_mono (p + n - 1) (A * 64 + F * 64 - 1) ltac:(lia)) as M2.
assert (E1 : A * 64 / 8 = A * 8) by (symmetry; apply (Z.div_unique _ _ _ 0); lia).
assert (E2 : F * 64 / 8 = F * 8) by (symmetry; apply (Z.div_unique _ _ _ 0); lia).
assert (E3 : (A * 64 + F * 64 - 1) / 8 = A * 8 + F * 8 - 1) by (symmetry; apply (Z.div_unique _ _ _ 7); lia).
unfold shadow_addr in *. rewrite E1 in M1 |- *. rewrite E3 in M2. rewrite E2.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)).
unfold SHADOW_OFF in *. lia.
Qed.

(* bytes_at on a window whose view is unchanged *)
Lemma tpg_gp_bytes_keep : forall (W W' : world segs) mem mem' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  bytes_at W mem p l -> bytes_at W' mem' p l.
Proof.
intros W W' mem mem' p l Hk Hb. unfold bytes_at, garr8 in *. intros j Hj.
destruct (Hb j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept segs (w_H W) (w_H W') mem mem' _ 1 _); [|exact Hv].
intros k Hk1. apply Hk. lia.
Qed.

(* the ledger at a later state whose statics and harness heads read the same and whose blocks keep Lam's, Hp fixed *)
Lemma tpg_gp_ledger_keep : forall ly S Hp W mem ly' S' W' mem' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly' S') /\
     forall i, 0 <= i < 8 -> aview segs (w_H W') mem' (a - cf_head + i) = aview segs (w_H W) mem (a - cf_head + i)) ->
  prh_ledger B ly' S' Hp W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem ly' S' W' mem' Lam peak cnt fail ran most own (HG & HND & HF & HPm) Hs Hh.
assert (Hst : forall p n v, (forall k, 0 <= k < Z.of_nat n -> Exists (in_zr (p + k)) prh_pst) ->
  val_mem segs (rdW W mem) p n v -> val_mem segs (rdW W' mem') p n v).
{ intros p n v Hin Hv. apply (val_mem_kept segs (w_H W) (w_H W') mem mem' p n v); [|exact Hv].
  intros k Hk. apply Hs. exact (Hin k Hk). }
destruct HG as (G1 & G2 & G3 & G4 & G5 & [GM GMb] & [GO GOb] & G6).
split; [|split; [exact HND | split; [|exact HPm]]].
- split; [apply Hst; [|exact G1]; intros j Hj; unfold prh_pst;
    apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
  split; [apply Hst; [|exact G2]; intros j Hj; unfold prh_pst;
    do 1 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
  split; [apply Hst; [|exact G3]; intros j Hj; unfold prh_pst;
    do 2 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
  split; [apply Hst; [|exact G4]; intros j Hj; unfold prh_pst;
    do 3 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
  split; [apply Hst; [|exact G5]; intros j Hj; unfold prh_pst;
    do 4 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
  split; [split; [apply Hst; [|exact GM]; intros j Hj; unfold prh_pst;
    do 5 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact GMb]|].
  split; [split; [apply Hst; [|exact GO]; intros j Hj; unfold prh_pst;
    do 6 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact GOb]|].
  exact G6.
- rewrite Forall_forall in *. intros [a k] Hin. destruct (HF (a, k) Hin) as (Hk0 & Hab & Hhp & Hal & Hv).
  cbn [fst snd] in *. destruct (Hh a k Hin) as (Hab' & Hb8).
  split; [exact Hk0|]. split; [exact Hab'|]. split; [exact Hhp|]. split; [exact Hal|].
  apply (val_mem_kept segs (w_H W) (w_H W') mem mem' _ 8 _); [|exact Hv].
  intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply Hb8. lia.
Qed.

Lemma tpg_side_after_call : forall D W3 mem3 md3 k ly2 S2 W2 mem2 md2 k1 WS1,
  tp_img B -> tp_pre B CTX0 D ->
  tp_J B SK D (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 k [] ->
  tp_side B D (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 (tp_own D) ->
  prhtx_inv B (tp_Lam D) (tp_ly D) (tp_S D) W3 mem3 (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_txt D) ->
  ajournal_xwR (SK := SK) segs B prh_pst (ARcfx B) RW ASTACK (tpg_spc D) (tpg_FP1 D)
    (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 [] ly2 S2 (tp_Hp D) W2 mem2 md2 k1 WS1 ->
  (forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) mem3 a) ->
  room_live_cf S2 ->
  tp_side B D ly2 S2 (tp_Hp D) W2 mem2 (tp_own D) /\ prhtx_kept B (tp_Lam D) ly2 S2 (tp_s D) (tp_n D).
Proof.
intros D W3 mem3 md3 k ly2 S2 W2 mem2 md2 k1 WS1 HI HP HJ HSD HINV HC HPST HRL2.
pose proof (tpi_head_wide B HI) as HW. unfold prh_head_wide in HW.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & HKEPT & _).
destruct HSD as (HL3 & HSRC3 & _).
destruct HSRC3 as (Hb3 & H43 & Hce3 & Ham3 & Hra3 & Hhu3).
rewrite HLEN in Hce3, Ham3, Hra3, Hhu3.
unfold tp_J in HJ. pose proof HJ as (HAR3 & _).
destruct HC as (HAR2 & Hly & _ & _ & _ & Hfrs & _ & _ & F1 & F2 & F3 & F4 & Hgone & _ & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the old buffer's footprint misses every other block of the GROW cut *)
assert (HnFP : forall p m i, In (p, m) (ablocks B (tp_ly D) (tp_S D)) -> (tp_cap0 D <> 0 -> p <> tp_b0 D) ->
  0 <= i < req_size m -> ~ inFP (tpg_FP1 D) (p + i)).
{ intros p m i Hin Hne Hi (r & Hr & Hb). unfold tpg_FP1 in Hr. destruct (tp_cap0 D =? 0) eqn:Ec; [destruct Hr|].
  apply Z.eqb_neq in Ec. unfold ablocks_fp in Hr. cbn [map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hb.
  destruct HINV as (_ & [(Hc0 & _) | (_ & _ & Hb0in & _)]); [lia|].
  assert (Hne' : (tp_b0 D, tp_cap0 D) <> (p, m)) by (intros E; injection E as E1 _; exact (Hne Ec (eq_sym E1))).
  pose proof (sep_blocks_x segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ _ _ HAR3 Hb0in Hin Hne') as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* no harness block is the old buffer *)
assert (HLamNe : forall a k', In (a, k') (tp_Lam D) -> tp_cap0 D <> 0 -> a - cf_head <> tp_b0 D).
{ intros a k' Hin Hc.
  destruct HINV as (_ & [(Hc0 & _) | (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlam)]); [lia | exact (Hlam a k' Hin)]. }
(* a block of the GROW cut that is not the old buffer is live after the call (the journal's gone-block clause) *)
assert (Hlive : forall p m, In (p, m) (ablocks B (tp_ly D) (tp_S D)) -> (tp_cap0 D <> 0 -> p <> tp_b0 D) -> 0 <= m ->
  In (p, m) (ablocks B ly2 S2)).
{ intros p m Hin Hne Hm.
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, m) (ablocks B ly2 S2)) as [Hc|Hc];
    [exact Hc|].
  exfalso. pose proof (req_size_pos m Hm) as [Hr _].
  apply (HnFP p m 0 Hin Hne ltac:(lia)). exact (Hgone p m 0 Hin Hc ltac:(lia)). }
(* a harness block: live at both states, its base in Hp, its bytes kept *)
assert (HLamB : forall a k', In (a, k') (tp_Lam D) ->
  0 <= k' /\ In (a - cf_head, k' + cf_head) (ablocks B ly2 S2) /\ In (a - cf_head) (tp_Hp D) /\
  (forall i, 0 <= i < req_size (k' + cf_head) ->
     aview segs (w_H W2) mem2 (a - cf_head + i) = aview segs (w_H W3) mem3 (a - cf_head + i))).
{ intros a k' Hin.
  pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL3) as HFb. rewrite Forall_forall in HFb.
  destruct (HFb (a, k') Hin) as (Hk0 & Hab & Hhp & _). cbn [fst snd] in Hk0, Hab, Hhp.
  assert (Hab2 := Hlive _ _ Hab (HLamNe a k' Hin) ltac:(lia)).
  split; [exact Hk0|]. split; [exact Hab2|]. split; [exact Hhp|].
  intros i Hi. apply (F2 _ _ i Hab Hab2 Hi). exact (HnFP _ _ i Hab (HLamNe a k' Hin) Hi). }
(* the ledger *)
assert (HL2 : prh_ledger B ly2 S2 (tp_Hp D) W2 mem2 (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) (tp_own D)).
{ apply (tpg_gp_ledger_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL3 HPST).
  intros a k' Hin. destruct (HLamB a k' Hin) as (Hk0 & Hab2 & _ & Hkb). split; [exact Hab2|].
  intros i Hi. apply Hkb. assert (H0 : 0 <= k' + cf_head) by lia.
  pose proof (req_size_pos _ H0) as [_ Hr]. lia. }
(* the call's footprint opens no sink *)
assert (Hsk : ~ YI16.sink_open_fp (tpg_FP1 D)).
{ unfold tpg_FP1. destruct (tp_cap0 D =? 0) eqn:Ec.
  - intros (r & Hr & _). destruct Hr.
  - apply sink_closed_ablocks_fp. constructor; [|constructor]. cbn [fst].
    destruct HINV as (_ & [(Hc0 & _) | (_ & _ & _ & _ & H4096 & _)]); [apply Z.eqb_neq in Ec; lia | lia]. }
(* a read-only image byte (not runtime-owned, not errno) is kept: the journal's image clause (not PST: tpi_pst_rw) *)
assert (HimgK : forall a, in_roP segs RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) mem3 a).
{ intros a Ha Ho He.
  apply F3; [| exact Ho | exact He | intros Hp; exact (tpi_pst_rw B HI a Hp Ha) | apply fp_spares_closed; exact Hsk].
  destruct Ha as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
(* the source window: its bytes, its shadow, its hull at the post state, by prhtx_kept's four cases *)
assert (HKB : (forall a, tp_s D <= a < tp_s D + tp_n D -> aview segs (w_H W2) mem2 a = aview segs (w_H W3) mem3 a) /\
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (tp_s D) (tp_n D) /\
  (0 < tp_n D -> shadow_hull_vis (aview segs (w_H W2) mem2) (tp_s D) (tp_n D))).
{ destruct HKEPT as [[(b & m & Hin & Hbs & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] | (cid & pos & Hfr & Hrng)].
  - (* a harness block: bytes by the block clause, shadow and hull by alx_hshadow at the post state *)
    destruct (HLamB b m Hin) as (Hm0 & Hab2 & Hhp & Hkb).
    split.
    { intros a Ha. replace a with (b - cf_head + (a - (b - cf_head))) by lia. apply Hkb.
      assert (H0 : 0 <= m + cf_head) by lia. pose proof (req_size_pos _ H0) as [_ Hr]. lia. }
    destruct (Z_lt_le_dec 0 (tp_n D)) as [Hn | Hn]; [|split; [apply range_addressable_nil; lia | intros Hn'; lia]].
    destruct (alx_hshadow segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR2 Hab2 Hhp) as [Hbsh Hhu2].
    assert (Erq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
    rewrite Erq in Hbsh, Hhu2.
    replace (b - cf_head + cf_head) with b in Hbsh, Hhu2 by lia.
    replace (m + cf_head - cf_head) with m in Hbsh, Hhu2 by lia.
    split; [eapply block_shadow_range; [exact Hbsh | lia | lia]|].
    intros _. apply (tpg_gp_hull_sub _ b m (tp_s D) (tp_n D)); [apply Hhu2; lia | lia | lia | exact Hn].
  - (* a registered read-only global: bytes by the image clause, shadow zero (alx_zshadow), hull by tpi_img_shvis *)
    destruct Hzs as (q & mq & Hinq & Hq & Hqm).
    pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR2)))) (q, mq) Hinq)
      as (Z1 & Z2 & Z3 & Z4 & Z5).
    cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
    pose proof (alx_zshadow segs B (ARcfx B) LAWS _ _ _ _ _ _ (q, mq) HAR2
      ltac:(unfold zero_shadow_ranges; right; exact Hinq)) as Hz.
    cbn [fst snd] in Hz.
    split; [intros a Ha; destruct (Hro a Ha) as (Hr1 & Hr2 & Hr3); exact (HimgK a Hr1 Hr2 Hr3)|].
    split.
    + apply (range_addressable_sub _ SHADOW_OFF q mq); [|exact Hq | exact Hqm].
      exact (zero_shadow_range _ SHADOW_OFF q mq Z3 Z4 Hz).
    + intros Hn s0 Hs. destruct (tpg_gp_hull_img _ _ (tp_s D) (tp_n D) s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
      exact (tpi_img_shvis B HI _ _ _ _ _ _ _ (proj1 HAR2) Hr).
  - (* an image string (kept_img): bytes by the image clause, shadow per granule (zero range or const cell), hull *)
    split; [intros a Ha; destruct (Hro a Ha) as (Hr1 & Hr2 & Hr3 & _); exact (HimgK a Hr1 Hr2 Hr3)|].
    split.
    + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzg | (v & Hcell & Hv)]).
      * destruct Hzg as (q & mq & Hinq & Hq & Hqm).
        pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR2)))) (q, mq) Hinq)
          as (Z1 & Z2 & Z3 & Z4 & Z5).
        cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
        pose proof (alx_zshadow segs B (ARcfx B) LAWS _ _ _ _ _ _ (q, mq) HAR2
          ltac:(unfold zero_shadow_ranges; right; exact Hinq)) as Hz.
        cbn [fst snd] in Hz.
        pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
        exact (zero_shadow_range _ SHADOW_OFF q mq Z3 Z4 Hz x ltac:(lia)).
      * pose proof (proj1 (Forall_forall _ _) (alx_const_cells segs B (ARcfx B) LAWS _ _ _ _ _ _ HAR2) _ (Hcell ly2))
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
    + intros Hn s0 Hs. destruct (tpg_gp_hull_img _ _ (tp_s D) (tp_n D) s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
      exact (tpi_img_shvis B HI _ _ _ _ _ _ _ (proj1 HAR2) Hr).
  - (* a fake frame of the GROW cut: bytes and shadow by the journal's frame clause (the frame misses the old buffer) *)
    pose proof (YG0scf.frame_facts_cf B _ _ _ _ cid pos (proj1 (proj1 HAR3)) Hfr)
      as (_ & _ & _ & _ & HFal & _ & _ & Hoff & _ & Hfs64 & _).
    destruct (frames_bounds_x segs B (ARcfx B) LAWS _ _ _ _ _ _ cid pos HAR3 Hfr) as (Hf0 & Hfc & Hfapp).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
    assert (Hfa64 : frame_addr (tp_ly D) cid pos mod 64 = 0).
    { unfold frame_addr. apply (proj2 (Z.mod_divide _ 64 ltac:(lia))). apply Z.divide_add_r.
      - apply (Z.divide_trans _ 4096); [exists 64; reflexivity|].
        apply (proj1 (Z.mod_divide _ 4096 ltac:(lia))). exact HFal.
      - apply (proj1 (Z.mod_divide _ 64 ltac:(lia))). exact Hoff. }
    assert (HnF : forall a, (frame_addr (tp_ly D) cid pos <= a < frame_addr (tp_ly D) cid pos + fs_frame_bytes cid \/
        shadow_addr (frame_addr (tp_ly D) cid pos) <= a <
        shadow_addr (frame_addr (tp_ly D) cid pos) + fs_frame_bytes cid / 8) -> ~ inFP (tpg_FP1 D) a).
    { intros a Ha (r & Hr & Hb). unfold tpg_FP1 in Hr. destruct (tp_cap0 D =? 0) eqn:Ec; [destruct Hr|].
      apply Z.eqb_neq in Ec. unfold ablocks_fp in Hr. cbn [map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hb.
      destruct HINV as (_ & [(Hc0 & _) | (_ & _ & Hb0in & _)]); [lia|].
      destruct (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR3 Hb0in) as (_ & _ & _ & [Hh1 Hh2] & _).
      pose proof (sep_block_frame_x segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ cid pos HAR3 Hb0in Hfr) as Hd.
      pose proof (YCbq.shadow_addr_bounds (frame_addr (tp_ly D) cid pos) ltac:(rewrite C4; lia)) as SB1.
      pose proof (YCbq.shadow_addr_bounds (frame_addr (tp_ly D) cid pos + fs_frame_bytes cid) ltac:(rewrite C4; lia))
        as SB2.
      pose proof (YCbq.shadow_range_end (frame_addr (tp_ly D) cid pos) (fs_frame_bytes cid) Hfb0) as SB3.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      unfold in_app, kLowShadowBeg, ASAN_CEIL in Hh2. rewrite C2, C3, C5 in *.
      destruct Ha as [Ha | Ha]; lia. }
    assert (HKy : forall y, shadow_addr (frame_addr (tp_ly D) cid pos) <= y <
        shadow_addr (frame_addr (tp_ly D) cid pos) + fs_frame_bytes cid / 8 ->
        aview segs (w_H W2) mem2 y = aview segs (w_H W3) mem3 y).
    { intros y Hy. apply (F4 cid pos y Hfr); [right; unfold in_zr; cbn [fst snd]; exact Hy | apply HnF; right; exact Hy]. }
    split.
    { intros a Ha. pose proof (Hrng a Ha) as Hr. apply (F4 cid pos a Hfr); [left; exact Hr|].
      apply HnF; left. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact Hr. }
    destruct (Z_lt_le_dec 0 (tp_n D)) as [Hn | Hn]; [|split; [apply range_addressable_nil; lia | intros Hn'; lia]].
    assert (Hs1 : frame_addr (tp_ly D) cid pos <= tp_s D /\
      tp_s D + tp_n D <= frame_addr (tp_ly D) cid pos + fs_frame_bytes cid).
    { pose proof (Hrng (tp_s D) ltac:(lia)) as R1. pose proof (Hrng (tp_s D + tp_n D - 1) ltac:(lia)) as R2.
      unfold frame_rng, in_zr in R1, R2. cbn [fst snd] in R1, R2. lia. }
    split.
    + apply (range_addressable_agree (aview segs (w_H W3) mem3)); [|exact Hra3].
      intros x Hx. apply HKy. apply (tpg_gp_frame_sh _ _ x Hfa64 Hfs64). lia.
    + intros _ y Hy. rewrite HKy; [exact (Hhu3 Hn y Hy)|].
      exact (tpg_gp_frame_hull _ _ (tp_s D) (tp_n D) y Hfa64 Hfs64 ltac:(lia) ltac:(lia) Hn Hy). }
destruct HKB as (KB & KR & KH).
split.
- split; [exact HL2|]. split; [|exact HRL2].
  unfold src_rd. rewrite HLEN.
  split; [apply (tpg_gp_bytes_keep W3 W2 mem3 mem2); [rewrite HLEN; exact KB | exact Hb3]|].
  split; [exact H43|]. split; [exact Hce3|]. split; [exact Ham3|]. split; [exact KR | exact KH].
- destruct HKEPT as [Hk | (cid & pos & Hfr & Hrng)]; [left; exact Hk | right].
  exists cid, pos. split; [rewrite Hfrs; exact Hfr|].
  intros a Ha. pose proof (Hrng a Ha) as Hr. unfold frame_rng, in_zr in *. cbn [fst snd] in *.
  unfold frame_addr in *. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. exact Hr.
Qed.


(* [GB1] the new buffer's block facts at the post state: a fresh block of ablocks of a state whose ledger holds *)
Lemma tpg_blk_new : forall D ly2 S2 W2 mem2 md2 res,
  tp_pre B CTX0 D -> tp_cap0 D < tp_need D ->
  ARcfx B ly2 S2 (tp_Hp D) W2 mem2 md2 ->
  In (res, tp_req D) (ablocks B ly2 S2) -> ~ In (res, tp_req D) (ablocks B (tp_ly D) (tp_S D)) ->
  prh_ledger B ly2 S2 (tp_Hp D) W2 mem2 (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) (tp_own D) ->
  tp_blk B D ly2 S2 W2 mem2 res (tp_req D).
Proof.
intros D ly2 S2 W2 mem2 md2 res HPRE Hlt HAR Hin Hnot HL.
pose proof cf_head_nonneg as CH.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _ & _ & _ & _ & _ & _ & HL0 & _).
destruct HREC as (_ & _ & [Hc0 _] & _).
assert (Hneed : 1 <= tp_need D) by lia.
assert (Hrq0 : 0 < tp_req D) by (unfold tp_req; lia).
assert (Hrq : req_size (tp_req D) = tp_req D) by (unfold req_size; destruct (Z.eqb_spec (tp_req D) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly2 S2 (tp_Hp D) W2 mem2 md2 res (tp_req D) HAR Hin)
  as (_ & H4096 & _ & _ & Hpres & _).
rewrite Hrq in Hpres.
(* a Lam block is live at entry and at S2, so it is another block of S2 than the fresh one *)
assert (HLAM : forall a k, In (a, k) (tp_Lam D) ->
  zdisjoint (a - cf_head, req_size (k + cf_head)) (res, req_size (tp_req D)) /\ 0 <= k).
{ intros a k Hak.
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL) (a, k) Hak) as (Hk & Hb2 & _).
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL0) (a, k) Hak) as (_ & Hb0 & _).
  cbn [fst snd] in Hk, Hb2, Hb0.
  split; [|exact Hk].
  apply (sep_blocks_x _ _ _ LAWS ly2 S2 (tp_Hp D) W2 mem2 md2 _ _ _ _ HAR Hb2 Hin).
  intros E. rewrite E in Hb0. exact (Hnot Hb0). }
(* Hp is the Lam bases (the ledger at S2), so no head lies in the fresh block *)
assert (HHP : forall h, In h (tp_Hp D) -> ~ (res <= h < res + req_size (tp_req D))).
{ intros h Hh.
  pose proof (Permutation_in _ (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HL) Hh) as Hm.
  apply in_map_iff in Hm as ([a k] & Eh & Hak). cbn [fst] in Eh. subst h.
  destruct (HLAM a k Hak) as [Hd Hk].
  assert (Hkc : 0 <= k + cf_head) by lia.
  pose proof (req_size_bounds (k + cf_head) Hkc) as (_ & R1 & _).
  destruct Hd as [Hd | Hd]; cbn [fst snd] in Hd; lia. }
destruct (alx_shadow _ _ _ LAWS ly2 S2 (tp_Hp D) W2 mem2 md2 res (tp_req D) HAR Hin HHP) as [Hbs Hhull].
rewrite Hrq in Hbs, Hhull.
(* the margin below the ceiling and the memory range, from the chunk geometry (PresetCfnA.preset_lib_pre_pay8) *)
assert (Hc8 : res + tp_req D + 8 <= YM05.alloc_ceiling /\ amem_range res (tp_req D)).
{ destruct HAR as ((M & _) & _).
  apply YG0s.In_ablocks in Hin as (k & Hk & _ & Hu & Hr).
  pose proof (YG0scf.chunk_facts_cf B ly2 S2 (tp_Hp D) _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & G7 & G8 & GG).
  pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q1 & Q2 & _).
  pose proof (@ASAN_CEIL_range rc) as [CR _].
  unfold ASAN_CEIL in CR, G2.
  split.
  - destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct GG].
    + cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
      pose proof (YG0s.region_in_prim ly2 (prim_class off) (amc_layout _ _ _ _ _ M) ltac:(lia)) as (_ & _ & _ & _ & R5).
      unfold ASAN_CEIL in R5. unfold kFreeArrayOffset in Gal. lia.
    + destruct GG as (_ & Hfp & Gbase & Gext & _).
      pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (_ & SG2 & _ & [SG4 _] & _).
      pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [[RS _] _].
      unfold needed_primary in SG2. unfold ck_rz in *. unfold kPage in *. lia.
  - destruct G1 as [G1a [G1l | [G1h1 G1h2]]].
    + left. unfold kLowMemEnd, kLowShadowBeg in *. lia.
    + right. unfold kHighMemEnd, kHighMemBeg in *. lia. }
split; [exact Hrq0|]. split; [exact Hin|]. split; [exact H4096|].
split; [exact (proj1 Hc8)|]. split; [exact (proj2 Hc8)|].
split; [intros a Ha; apply (YCbq.apresent_writable segs); exact (proj1 (Hpres a ltac:(lia)))|].
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
split; [exact Hhull|].
intros a k Hak E. destruct (HLAM a k Hak) as [Hd Hk]. rewrite E, Hrq in Hd.
assert (Hkc : 0 <= k + cf_head) by lia.
pose proof (req_size_bounds (k + cf_head) Hkc) as (_ & R1 & _).
destruct Hd as [Hd | Hd]; cbn [fst snd] in Hd; lia.
Qed.

(* [GB2] the source window misses the new buffer *)
Lemma tpg_src_off_new : forall D ly2 S2 W2 mem2 md2 res,
  tp_pre B CTX0 D -> ARcfx B ly2 S2 (tp_Hp D) W2 mem2 md2 -> frames S2 = frames (tp_S D) ->
  In (res, tp_req D) (ablocks B ly2 S2) -> ~ In (res, tp_req D) (ablocks B (tp_ly D) (tp_S D)) ->
  prh_ledger B ly2 S2 (tp_Hp D) W2 mem2 (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) (tp_own D) ->
  prhtx_kept B (tp_Lam D) ly2 S2 (tp_s D) (tp_n D) ->
  forall a, tp_s D <= a < tp_s D + tp_n D -> ~ (res <= a < res + tp_req D).
Proof.
intros D ly2 S2 W2 mem2 md2 res HPRE HAR _ Hin Hnot HL HK a Ha Hr.
pose proof cf_head_nonneg as CH.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL0 & _).
assert (Hrs : tp_req D <= req_size (tp_req D)) by (unfold req_size; destruct (Z.eqb_spec (tp_req D) 0); lia).
(* a byte of the fresh block is no image byte (the client-image law) *)
assert (HNI : ~ in_img segs a).
{ refine (proj2 (alx_client_img _ _ _ LAWS ly2 S2 (tp_Hp D) W2 mem2 md2 a HAR _)).
  left. exists res, (tp_req D). split; [exact Hin | lia]. }
destruct HK as [[(b & m & Hbm & Hb & Hbn) | [(_ & _ & _ & HR) | (_ & _ & HR)]] | (cid & pos & Hf & Hfr)].
- (* a harness block: live at entry, so another block of S2 than the fresh one *)
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL) (b, m) Hbm) as (Hm & Hb2 & _).
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL0) (b, m) Hbm) as (_ & Hb0 & _).
  cbn [fst snd] in Hm, Hb2, Hb0.
  assert (Hne : (b - cf_head, m + cf_head) <> (res, tp_req D)) by (intros E; rewrite E in Hb0; exact (Hnot Hb0)).
  pose proof (sep_blocks_x _ _ _ LAWS ly2 S2 (tp_Hp D) W2 mem2 md2 _ _ _ _ HAR Hb2 Hin Hne) as Hd.
  assert (Hmc : 0 <= m + cf_head) by lia.
  pose proof (req_size_bounds (m + cf_head) Hmc) as (_ & _ & R2 & _).
  destruct Hd as [Hd | Hd]; cbn [fst snd] in Hd; lia.
- (* a registered read-only global: an image byte *)
  destruct (HR a Ha) as [Hro _]. apply HNI.
  destruct Hro as [(sg & Hsg & _ & Hsr) | Hrr];
    [exists sg; split; [exact Hsg | exact Hsr] | exact (@pa_relro_img _ _ PA a Hrr)].
- (* an image string: an image byte *)
  destruct (HR a Ha) as [Hro _]. apply HNI.
  destruct Hro as [(sg & Hsg & _ & Hsr) | Hrr];
    [exists sg; split; [exact Hsg | exact Hsr] | exact (@pa_relro_img _ _ PA a Hrr)].
- (* a fake frame of S2: disjoint from every block of S2 *)
  assert (Hfa : frame_addr ly2 cid pos <= a < frame_addr ly2 cid pos + fs_frame_bytes cid) by exact (Hfr a Ha).
  pose proof (sep_block_frame_x _ _ _ LAWS ly2 S2 (tp_Hp D) W2 mem2 md2 _ _ _ _ HAR Hin Hf) as Hd.
  destruct Hd as [Hd | Hd]; cbn [fst snd] in Hd; lia.
Qed.

(* [GR1] the refused arm: the old buffer's facts at the post state (its bytes kept by the call, nothing exempted) *)
(* bytes_at on a window whose view is unchanged *)
Lemma tpg_gr_bytes_keep : forall (W W' : world segs) mem mem' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  bytes_at W mem p l -> bytes_at W' mem' p l.
Proof.
intros W W' mem mem' p l Hk Hb. unfold bytes_at, garr8 in *. intros j Hj.
destruct (Hb j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept segs (w_H W) (w_H W') mem mem' _ 1 _); [|exact Hv].
intros k Hk1. apply Hk. lia.
Qed.

(* the hidden heads of a ledger lie outside a live block whose base is no harness head *)
Lemma tpg_gr_hp_apart : forall ly2 S2 Hp W2 mem2 md2 Lam peak cnt fail ran most own b cap,
  ARcfx B ly2 S2 Hp W2 mem2 md2 ->
  prh_ledger B ly2 S2 Hp W2 mem2 Lam peak cnt fail ran most own ->
  In (b, cap) (ablocks B ly2 S2) ->
  (forall a k, In (a, k) Lam -> a - cf_head <> b) ->
  forall h, In h Hp -> ~ (b <= h < b + req_size cap).
Proof.
intros ly2 S2 Hp W2 mem2 md2 Lam peak cnt fail ran most own b cap AR2 LG2 Hin Hlam h Hh.
pose proof (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ LG2) as HP.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hak). cbn [fst snd] in Eh. subst h.
pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ LG2) as HF.
rewrite Forall_forall in HF. destruct (HF (a, k) Hak) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
pose proof (Hlam a k Hak) as Hne.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp W2 mem2 md2 _ _ AR2 Hin) as (_ & _ & _ & _ & _ & Hpw).
assert (Hd : zdisjoint (a - cf_head, req_size (k + cf_head)) (b, req_size cap)).
{ apply (pairwise_zdisjoint_split _ _ _ Hpw). apply in_split_2.
  - exact (in_map (fun bb : Z * Z => (fst bb, req_size (snd bb))) _ _ Hab).
  - exact (in_map (fun bb : Z * Z => (fst bb, req_size (snd bb))) _ _ Hin).
  - intros E. injection E as E _. exact (Hne E). }
pose proof cf_head_nonneg as Hh0.
assert (Hkh : 0 <= k + cf_head) by (clear - Hk0 Hh0; lia).
destruct (req_size_pos (k + cf_head) Hkh) as [Hr1 _].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hr1 Hne. lia.
Qed.

(* [GR2] where the record lies, at any later state of the walk whose journal from entry holds *)
Lemma tpg_place_at : forall (R : world segs -> world segs -> Prop) D ly2 S2 W2 mem2 md2 k2 WS,
  tp_pre B CTX0 D -> tp_JR B SK R D ly2 S2 (tp_Hp D) W2 mem2 md2 k2 WS ->
  prhtx_place ly2 S2 W2 (tp_regs D) mem2 (tp_dw D) (tp_t D).
Proof.
intros R D ly2 S2 W2 mem2 md2 k2 WS PRE HJ.
destruct PRE as (HF & _ & _ & _ & _ & _ & _ & _ & HW & HPL & _).
destruct HF as ((_ & _ & _ & _ & _ & Hastk0 & _) & _).
destruct Hastk0 as (_ & HSTK0 & _).
destruct HPL as (Hal & Hlo & Hhi & _ & _).
unfold tp_JR, ajournal_xwR in HJ.
destruct HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hslo & Hshi & _).
destruct Hstk as (_ & _ & Hceil & Hslo0 & Hshi0 & _).
unfold tp_sp0 in *.
split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [intros a Ha; apply apresent_writable; apply Hpres; lia|].
intros x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (alx_zshadow_byte _ _ _ LAWS ly2 S2 (tp_Hp D) W2 mem2 md2 x HAR).
rewrite Hslo, Hshi. lia.
Qed.


(* the new buffer holds the old text: the realloc's copy clause on the first min (cap0, req) bytes *)
Lemma tpg_bytes_copy : forall (W3 W2 : world segs) mem3 mem2 b0 res (txt : list Z) n,
  bytes_at W3 mem3 b0 txt -> Z.of_nat (length txt) <= n ->
  (forall i, 0 <= i < n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W3) mem3 (b0 + i)) ->
  bytes_at W2 mem2 res txt.
Proof.
intros W3 W2 mem3 mem2 b0 res txt n H Hl HA j Hj.
destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA (Z.of_nat j) ltac:(lia)). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte segs (mrestrict (w_H W2) mem2) (res + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA;
  [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

Lemma tpg_cs_hi : forall r : bv 5, 18 <= bv_unsigned r <= 27 -> acallee_saved (bv_unsigned r).
Proof. intros r H. unfold acallee_saved. right. right. right. right. right. exact H. Qed.

(* ---- THE RUN POSITION after the call: ONE lemma (the text's position conjunct is restated here alone). The granted
   arm advances the position by the grow's event, tp_pre's guarded entry premise (f0 = 0 and cap0 < need hold at
   the GROW cut), at the call's admission (the trace is wild in the kit's text) (PresetRoomPosKeep.room_pos_keep_realloc /
   _realloc0, through TxPutCall102.tp_pos_after_grow / _grow0). The kit's text states the refused arm and marks it
   DEAD (PRH_FnTx.v:463-465; TxPut102A_Base.v:328-329): the realloc's NULL is refuted at the call (tpg_refute_null). *)
Lemma tpg_pos_after_call : forall D ly Hp W regs mem md ch tr trc q S2,
  tp_pre B CTX0 D -> tp_f0 D = 0 -> tp_cap0 D < tp_need D ->
  acall_pre_x segs B (ARcfx B) (QMm_cf segs B) ly (tp_S D) Hp W regs mem md ch -> admits (as_universe B) tr (tp_S D) ->
  ((tp_cap0 D = 0 /\ apath (realloc_null_tree_with malloc_cf free_cf (tp_req D) tr (tp_S D)) trc (q, S2)) \/
   (exists p, 0 < tp_cap0 D /\ sptr_addr B ly p = tp_b0 D /\ tp_b0 D <> 0 /\ In (p, tp_cap0 D) (blocks (tp_S D)) /\
      apath (realloc_tree_with malloc_cf free_cf p (tp_req D) tr (tp_S D)) trc (q, S2))) ->
  q <> PNull -> tp_pos D S2 0.
Proof.
intros D ly Hp W regs mem md ch tr trc q S2 HPRE Hf0 Hlt HPC Htr Hpath Hq.
pose proof HPRE as (_ & _ & HRL & HPOS & _ & _ & _ & _ & _ & _ & _ & HREC & _ & _ & _ & _ & _ & Hnb & _ & HEV & HLV & HRQ & _).
destruct HREC as (_ & _ & [Hc0 _] & _).
assert (Hr : 0 <= tp_req D < cf_malloc_max) by (unfold tp_req, tp_need in *; lia).
assert (Hl : blocks_bytes (tp_S D) + tp_req D <= LIVE_MAX) by (unfold tp_req, tp_need, LIVE_tx in *; lia).
split.
- intros _ _ _. pose proof (HEV Hf0 Hlt) as Hev. change (tp_len0 D + tp_n D + 1) with (tp_need D) in Hev.
  change (2 * tp_need D) with (tp_req D) in Hev.
  destruct Hpath as [(Hc & Hp0) | (p & Hc & Ep & Hb & Hin & Hp0)].
  + exact (tp_pos_after_grow0 B _ _ _ _ _ _ ly (tp_S D) Hp W regs mem md ch (tp_cap0 D) (tp_req D) tr trc q S2
      HPC Hc Hr Hl Htr Hp0 Hq HPOS Hev).
  + exact (tp_pos_after_grow B _ _ _ _ _ _ ly (tp_S D) Hp W regs mem md ch p (tp_b0 D) (tp_cap0 D) (tp_req D) tr trc q S2
      HPC HRL Hc Ep Hb Hin Hr Hl Htr Hp0 Hq HPOS Hev).
- intros Hn. exfalso. apply Hn. split; [exact Hf0|]. split; [reflexivity | exact Hlt].
Qed.

(* ---- THE REFUSED REALLOC IS REFUTED (DEAD-TXPUT): entered unfailed and growing, the grow's run event is a
   consumer event (the batch kit's consumer window, tp_k1pre, over this call's one event) at the run position of the entry
   state, so a NULL of the raw realloc - a real refusal, mt_refused at the call state - contradicts P8 through
   PRH_Refute.prh_refute_tx_put (the engine's granted paths). ---- *)
Lemma tpg_refute_null : forall D S2 n tr,
  tp_pre B CTX0 D -> tp_k1pre B D -> tp_f0 D = 0 -> tp_cap0 D < tp_need D ->
  Wf_cf (as_universe B) (tp_S D) -> mt_refused malloc_cf free_cf n tr (tp_S D) S2 -> False.
Proof.
intros D S2 n tr HPRE HK1 Hf0 Hneed HWF Href.
pose proof HPRE as (_ & _ & _ & HPOS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _ & _).
destruct HK1 as (_ & HCF).
pose proof (HCF Hf0) as Hc. rewrite (tp_evk_grow D Hneed) in Hc.
apply (PRH_Refute.prh_refute_tx_put (as_universe B) (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D) (tp_rp_i D) (tp_cap0 D)
  (tp_len0 D + tp_n D + 1) (tp_rp_H0 D) (tp_rp_hist D) (tp_S D) (HEV Hf0 Hneed) Hc HPOS HWF).
right. exists n, tr, S2. exact Href.
Qed.

(* the grow's budget: its one wild trace, within the batch-kit post's budget (one event per grow) *)
Lemma tpg_budget_grow : forall D tr, tp_cap0 D < tp_need D -> tp_budget D ([] ++ ([] ++ [tr])).
Proof. intros D tr Hn _. cbn [app]. unfold wbudget. rewrite (tp_evk_grow D Hn). apply wfresh_one. Qed.

(* ---- small facts the call arms use ---- *)
(* an address E names (an error-buffer extent, or a byte of a block of either state) is no image byte *)
Lemma tpg_E_img : forall ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 a,
  ARcfx B ly S Hp W mem md -> ARcfx B ly2 S2 Hp2 W2 mem2 md2 ->
  (Exists (in_zr a) (xs_cf ly S ++ xs_cf ly2 S2) \/
   (exists p n, (In (p, n) (blocks S) /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) \/
                (In (p, n) (blocks S2) /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n))) ->
  ~ in_img segs a.
Proof.
intros ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 a HAR HAR2 [Hx | (p & n & [(Hin & Hr) | (Hin & Hr)])] Hi.
- apply Exists_app in Hx as [Hx | Hx].
  + destruct (XSL ly S Hp W mem md a HAR Hx) as (_ & _ & Hni & _). exact (Hni Hi).
  + destruct (XSL ly2 S2 Hp2 W2 mem2 md2 a HAR2 Hx) as (_ & _ & Hni & _). exact (Hni Hi).
- apply (blk_img_x segs B (ARcfx B) LAWS ly S Hp W mem md (sptr_addr B ly p) n a HAR); [| lia | exact Hi].
  unfold ablocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hin].
- apply (blk_img_x segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 (sptr_addr B ly2 p) n a HAR2); [| lia | exact Hi].
  unfold ablocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hin].
Qed.

(* the block a call appends is no block of the list before it (blocks are pairwise separated) *)
Lemma tpg_fresh_new : forall ly S Hp W mem md l (b : Z * Z),
  ARcfx B ly S Hp W mem md -> 0 <= snd b -> ablocks B ly S = l ++ [b] -> ~ In b l.
Proof.
intros ly S Hp W mem md l b HAR Hb0 E Hin. apply in_split in Hin as (x1 & x2 & ->).
pose proof (@sep_blocks_pos_x rc segs B (ARcfx B) cf_head LAWS ly S Hp W mem md b b x1 x2 [] HAR
  ltac:(rewrite E, <- app_assoc; reflexivity)) as Hd.
destruct b as [p n]. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
cbn [snd] in Hb0.
assert (Hq : 1 <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
lia.
Qed.

Lemma tpg_bytes_nil : forall (W : world segs) mem p, bytes_at W mem p [].
Proof. intros W mem p j Hj. cbn [length] in Hj. lia. Qed.

(* ---- THE ENGINE STATES ---- *)
(* a fresh journal at a state: nothing happened yet (YCbqGcallW.ajournal_x_init_W's proof, at a given window) *)
Lemma tpg_jrefl : forall STK sp FP ly S Hp W mem md,
  ARcfx B ly S Hp W mem md -> astk_ok STK ly sp -> (forall a, sp - STK <= a < sp -> apresent (w_H W) mem a) ->
  qtight S ->
  ajournal_x (SK := SK) segs B prh_pst (ARcfx B) STK sp FP ly S Hp W mem md [] ly S Hp W mem md 0.
Proof.
intros STK sp FP ly S Hp W mem md HAR Hstk Hpres HQT.
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split; [apply aos_step_refl|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hpres|]. split; [exact Hstk|]. split; [intros; reflexivity|]. split; [exact HQT|].
(* the journal's wild-part budget (YCbqG.v's eighteenth conjunct since the P'' universe set): an unchanged depot *)
apply wild_part_same.
Qed.

(* a register file's sv may be replaced by another of the same value *)
Lemma tpg_regs_ok_set : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
specialize (Hr r'). unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.

(* the shadow address of a checked field, as the engine forms it: (x >> 3) + s6 *)
Definition tpg_sh (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 22 0).
(* the GROW cut's register file: every register its own atom but the record's field pointers and the shadow
   pointers the body keeps live (s3 = t + 8, s5 = t + 16, s7 / s9 their shadow cells, s10 = t >> 3) *)
Definition tpg_sr : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 19%bv (SOff 8 8)) 21%bv (SOff 8 16))
    23%bv (tpg_sh (SOff 8 8))) 25%bv (tpg_sh (SOff 8 16))) 26%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3)).
(* the record at t (atom 8): b, n, cap as atoms 32, 33, 34; window [0, w) *)
Definition tpg_rec (w : Z) : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 24 0 w
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
(* every bound a LITERAL (the engine decides by vm_compute): t on the stack below 2 ^ 47, 8-aligned; the shadow base;
   b0 below 2 ^ 47; len0, cap0 below the need bound *)
Definition tpg_facts : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 (2 ^ 47) 0); (33%nat, mkAF 0 (2 ^ 28) 0); (34%nat, mkAF 0 (2 ^ 28) 0)] [] [].
Definition tpg_ss0 : sstate := mkSS (TP_OFF + TP_PC_GROW) tpg_sr [tpg_rec 0] None tpg_facts.
Definition tpg_E (regs : bvmap 5 word) (xs : list Z) : env := @Eimg _ A_prog_listing PA (Ereg regs (map (Z_to_bv 64) xs)).
Definition TPG_Bx : sv := SOff 22 0.
Definition TPG_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma tpg_U_srl : forall E a s, 0 <= s < 64 -> U E (SAlu ALU_SRL a (SLit s)) = Z.shiftr (U E a) s.
Proof.
intros E a s Hs. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id s) by (unfold M64; lia).
replace (Z.land s 63) with s by (symmetry; change 63 with (Z.ones 6); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
apply zcanon_id. pose proof (U_range E a) as R. split; [apply Z.shiftr_nonneg; lia|].
rewrite Z.shiftr_div_pow2 by lia. apply (Z.le_lt_trans _ (U E a)); [apply Z.div_le_upper_bound; [lia|] | lia].
pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma tpg_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma tpg_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* the shadow pointer's value *)
Lemma tpg_U_sh : forall E x c v, U E (SOff x c) = v -> U E (SOff 22 0) = SHADOW_OFF -> 0 <= v < 2 ^ 47 ->
  U E (tpg_sh (SOff x c)) = SHADOW_OFF + v / 8.
Proof.
intros E x c v Hv Hb Hr. unfold tpg_sh. rewrite tpg_U_add, tpg_U_srl, Hv, Hb by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold SHADOW_OFF.
rewrite Z.add_comm. apply Z.mod_small. pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)).
assert (v / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* a register the run never wrote keeps the cut's value (its sv is the cut's, over atoms below the run's K) *)
Lemma tpg_reg_of_sv : forall E E' ss (H : word -> bool) ms regs sr (r : bv 5) k,
  st_ok segs E' ss (restrict H ms) -> env_agree k E E' -> regs_ok E sr regs ->
  sr_get (ss_regs ss) r = sr_get sr r -> sv_atoms_lt k (sr_get sr r) = true ->
  getr (ms_regs ms) r = getr regs r.
Proof.
intros E E' ss H ms regs sr r k HS HA HR E1 E2.
rewrite (st_ok_restrict_reg segs H E' ss ms r HS), E1, (sv_denot_agree k E E' _ HA E2). symmetry. exact (HR r).
Qed.

Lemma tpg_aview_present : forall (H : word -> bool) mem a, apresent H mem a -> aview segs H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* bytes of a prefix *)
Lemma tpg_bytes_prefix : forall (W : world segs) mem p l1 l2, bytes_at W mem p (l1 ++ l2) -> bytes_at W mem p l1.
Proof.
intros W mem p l1 l2 H. unfold bytes_at, garr8 in *. intros j Hj.
assert (Hj2 : (j < length (l1 ++ l2))%nat) by (rewrite length_app; lia).
destruct (H j Hj2) as [Hv Hr]. rewrite app_nth1 in Hv, Hr by exact Hj. split; [exact Hv | exact Hr].
Qed.

(* ---- the tail's own helpers ---- *)
(* the walk's keep from entry (tp_K) crosses a straight-line stretch at one allocator state that changes the view only
   on the written cells OR (SNULL's tpn_kept_ext without the PST cell) *)
Lemma tpg_gt_kept_ext : forall (R : world segs -> world segs -> Prop) STKf sp OR FPc lyc Sc (W : world segs) memc mdc
  ly2 S2 Hp2 W2 mem2 md2 mem2' md2',
  cj_keptR (SK := SK) segs B prh_pst R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  ARcfx B ly2 S2 Hp2 W2 mem2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inFP OR a -> aview segs (w_H W2) mem2' a = aview segs (w_H W2) mem2 a) ->
  same_but_materialized md2 md2' ->
  cj_keptR (SK := SK) segs B prh_pst R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2' md2'.
Proof.
intros R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 Hp2 W2 mem2 md2 mem2' md2'
  (Hly & Hsecs & Hwle & Hio & Hfrs & F1 & F2 & Hgone & F3 & F4 & F5) HAR Hk Hsame.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized; exact Hsame]|].
split; [exact Hfrs|].
split.
{ intros a Ha Hw Hq. rewrite (Hk a ltac:(lia) Hq). exact (F1 a Ha Hw Hq). }
split.
{ intros p m i H1 H2 Hi Hf Hq.
  pose proof (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR H2) as (_ & H4096 & Hc & _).
  rewrite (Hk (p + i) ltac:(lia) Hq). exact (F2 p m i H1 H2 Hi Hf Hq). }
split; [exact Hgone|].
split.
{ intros a Hi Hn He Hpst Hsp Hq. pose proof (@pa_segs_low _ _ PA a Hi) as Hal. rewrite C5 in Hal.
  rewrite (Hk a ltac:(lia) Hq). exact (F3 a Hi Hn He Hpst Hsp Hq). }
split.
{ intros cid pos a Hin Hr Hf Hq.
  assert (Efr : frame_addr ly2 cid pos = frame_addr lyc cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hin).
  destruct (frames_bounds_x segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR Hin2) as (Hf0 & Hfc & _).
  rewrite Efr in Hf0, Hfc.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  unfold frame_rng, in_zr, shadow_addr in Hr. cbn [fst snd] in Hr.
  rewrite (Hk a).
  - exact (F4 cid pos a Hin ltac:(unfold frame_rng, in_zr, shadow_addr; cbn [fst snd]; exact Hr) Hf Hq).
  - unfold SHADOW_OFF in Hr. destruct Hr as [Hr|Hr]; Z.div_mod_to_equations; lia.
  - exact Hq. }
intros a Hx He Hq.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (Hx2 : Exists (in_zr a) (ly_extra ly2)) by (rewrite Eextra; exact Hx).
pose proof (alx_extra segs B (ARcfx B) LAWS ly2 S2 Hp2 W2 mem2 md2 a HAR Hx2) as (_ & _ & _ & _ & _ & _ & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
rewrite (Hk a Ha64 Hq). exact (F5 a Hx He Hq).
Qed.

(* the granted arm's state at +196: a0 = res (atom 10, in [4096, 2 ^ 47], 16-aligned), s3 / s5 the record's fields
   t + 8 / t + 16, s7 / s9 / s11 the shadow cells of t + 8 / t + 16 / t; the record at t (atom 8) with the window
   [0, 24) and one chunk, len0 (atom 33) at 8 *)
Definition tpg_gt_srF : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 19%bv (SOff 8 8)) 21%bv (SOff 8 16))
    23%bv (tpg_sh (SOff 8 8))) 25%bv (tpg_sh (SOff 8 16))) 27%bv (tpg_sh (SOff 8 0)).
Definition tpg_gt_recF : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 24 0 24 [YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition tpg_gt_factsF : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (10%nat, mkAF 4096 (2 ^ 47) 4);
           (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 28) 0)] [] [].
Definition tpg_gt_ssF : sstate := mkSS (TP_OFF + 196) tpg_gt_srF [tpg_gt_recF] None tpg_gt_factsF.

(* a register the run never wrote keeps the start state's value (tpg_reg_of_sv at a straight-line run's end) *)
Lemma tpg_gt_reg_same : forall E E' ss (H : word -> bool) ms regs sr (r : bv 5) k,
  st_ok_pi segs VAL E' ss (restrict H ms) -> env_agree k E E' -> regs_ok E sr regs ->
  sr_get (ss_regs ss) r = sr_get sr r -> sv_atoms_lt k (sr_get sr r) = true -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E E' ss H ms regs sr r k HS HA HR E1 E2.
rewrite (st_ok_pi_restrict_reg H E' ss ms r HS), E1, (sv_denot_agree k E E' _ HA E2). symmetry. exact (HR r).
Qed.
Lemma tpg_gt_reg_all : forall E ss (H : word -> bool) ms regs,
  st_ok_pi segs VAL E ss (restrict H ms) -> regs_ok E (ss_regs ss) regs ->
  forall r, getr (ms_regs ms) r = getr regs r.
Proof. intros E ss H ms regs HS HR r. rewrite (st_ok_pi_restrict_reg H E ss ms r HS). symmetry. exact (HR r). Qed.
(* a chunk of a region at an atom base holds its value (SNULL's tpn_chunk_val) *)
Lemma tpg_gt_chunk_val : forall E m (j : nat) lo hi wlo whi cs off (w : N) e v,
  region_ok segs E m (YP09.mkRegion (Some j) lo hi wlo whi cs) -> In (YP09.mkChunk off (CVal w e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem segs m (bv_unsigned (ew E j) + off) (N.to_nat w) v.
Proof.
intros E m j lo hi wlo whi cs off w e v (_ & _ & _ & Hcs) Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck.
exact (val_of_chunk_ok segs E m _ off w e v Hck He Hv Hw).
Qed.
(* the `slli 1` the engine keeps as a shift *)
Lemma tpg_gt_U_sll1 : forall E a, U E a < 2 ^ 62 -> U E (SAlu ALU_SLL a (SLit 1)) = 2 * U E a.
Proof.
intros E a Ha. pose proof (U_range E a) as R. unfold M64 in R.
rewrite U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 1) by (unfold M64; lia). change (Z.land 1 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_1_r. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* the buffer's block facts below the ceiling cross a stretch that keeps the view and the memory there *)
Lemma tpg_gt_blk_keep : forall D ly S (W W' : world segs) mem mem' b c,
  tp_blk B D ly S W mem b c -> TxPutKeep102.tpk_alo W W' mem mem' -> TxPutKeep102.tpk_mlo W W' mem mem' ->
  tp_blk B D ly S W' mem' b c.
Proof.
intros D ly S W W' mem mem' b c (Hc & Hin & H4 & Hce & Ham & Hwr & Hra & Hhu & Hlam) KA KM.
pose proof (@YM05.alloc_ceiling_lt rc) as CL.
split; [exact Hc|]. split; [exact Hin|]. split; [exact H4|]. split; [exact Hce|]. split; [exact Ham|].
split; [intros a Ha; apply (TxPutKeep102.tpk_writable_lo W W' mem mem' a KM); [lia | exact (Hwr a Ha)]|].
split; [apply (TxPutKeep102.tpk_ra_keep (aview segs (w_H W) mem)); [|exact Hra]; intros x Hx; apply KA;
  apply TxPutKeep102.tpk_shadow_lo; lia|].
split; [apply (TxPutKeep102.tpk_hull_keep (aview segs (w_H W) mem)); [|exact Hhu]; intros s Hs; apply KA;
  exact (TxPutKeep102.tpk_hull_lo b c s ltac:(lia) ltac:(lia) ltac:(lia) Hs)|].
exact Hlam.
Qed.

(* ---- THE TAIL: from the realloc's return (+196) to the FIT cut, given what the granted call left (the batch kit's refused
   arm is DEAD: the GROW row refutes the realloc's NULL at the call, tpg_refute_null). The journal is at the call's budget WS; the run
   reads it rebased at the post-call depot and the FIT cut gets it back at WS (YCbqGwild rebase / unbase0) ---- *)
Lemma tpg_tail : forall (P : (word -> option byte) -> Prop) Q D W3 mem3 ly2 S2 W2 regs2 mem2 md2 k2 WS res,
  srr_inv_laws segs P -> tp_img B ->
  tp_k_FIT B SK CTX0 P Q D -> tp_budget D WS ->
  tp_pre B CTX0 D -> tp_f0 D = 0 -> tp_cap0 D < tp_need D ->
  tp_recat D W3 mem3 (tp_b0 D) (tp_len0 D) (tp_cap0 D) 0 -> tp_saved D W3 mem3 ->
  tp_kregs D regs2 -> spZ regs2 = tp_sp0 D - TP_FRAME -> tp_shregs D regs2 ->
  getr regs2 19 = w64 (tp_t D + 8) -> getr regs2 21 = w64 (tp_t D + 16) -> getr regs2 20 = w64 (tp_t D + 24) ->
  getr regs2 23 = w64 (SHADOW_OFF + (tp_t D + 8) / 8) -> getr regs2 25 = w64 (SHADOW_OFF + (tp_t D + 16) / 8) ->
  getr regs2 24 = w64 (SHADOW_OFF + (tp_t D + 24) / 8) -> getr regs2 26 = w64 (tp_t D / 8) ->
  getr regs2 27 = w64 (SHADOW_OFF + tp_t D / 8) -> getr regs2 10 = w64 res ->
  tpg_post D W3 mem3 ly2 S2 W2 mem2 md2 k2 WS -> P mem2 ->
  4096 <= res /\ res mod 16 = 0 /\ tpg_grown D ly2 S2 W2 mem2 res ->
  SRr' segs RZc W2 (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (TP_OFF + 196))) mem2 (YK11.seg_rom segs)) md2)
    (tp_QP P Q).
Proof.
intros P Q D W3 mem3 ly2 S2 W2 regs2 mem2 md2 k2 WS res PLAW HIMG KFIT HBUD HPRE Hf0 Hneed HREC3 HSV3 HKR HSP HSHR
  R19 R21 R20 R23 R25 R24 R26 R27 R10 HPOST HPM HARM.
pose proof HSHR as (R22 & R8 & R9 & R18).
pose proof HPRE as (HFP & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFWIN & HPLACE & HTRACE0 & HREC0 & HINV0
  & HSRC0 & HSLEN & HKEPT0 & HDISJ & HNEEDB & HLG0 & HEV0 & HLIVEB & HREQ & HHULL).
pose proof HFP as (HAFN & HROD0 & HSTKHI & HRAC).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & Hpres & Hch & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit0 & Hra280).
pose proof HREC3 as (Rb0 & Rl0 & Rc0 & Rf0 & Mb3 & Ml3 & Mc3 & Mf3).
pose proof HINV0 as (Hltxt & _).
pose proof HPOST as (HJ & HK & HWIN & HROD2).
pose proof HJ as (HAR2 & _).
pose proof (tpg_place_at _ D ly2 S2 W2 mem2 md2 k2 WS HPRE HJ) as HPL2.
pose proof HPL2 as (_ & _ & _ & HWR2 & HRA2).
pose proof (tpg_STK) as ESTK. assert (HAS : ASTACK = 16384) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (HCE & _). unfold ASAN_CEIL in HCE.
pose proof (@YM05.alloc_ceiling_lt rc) as CL.
unfold tp_sp0 in *. unfold TP_FRAME in *. rewrite ESTK in Hslo, Hbot. unfold TP_FRAME in *.
assert (Ht47 : 2 ^ 46 <= tp_t D /\ tp_t D + 28 <= 2 ^ 47) by lia.
assert (Hceilt : YM05.alloc_ceiling <= tp_t D) by lia.
assert (Hn0 : 0 <= tp_n D) by lia.
assert (Eneed : tp_need D = tp_len0 D + tp_n D + 1) by reflexivity.
assert (Ereq : tp_req D = 2 * (tp_len0 D + tp_n D + 1)) by reflexivity.
(* the record and the saved words lie in the window the call kept *)
assert (KW : forall a n v, tpg_spc D <= a -> a + Z.of_nat n <= spZ (tp_regs D) + tp_dw D ->
  val_mem segs (rdW W3 mem3) a n v -> val_mem segs (rdW W2 mem2) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_kept segs (w_H W3) (w_H W2) mem3 mem2 a n v); [|exact Hv].
  intros kk Hkk. apply HWIN. lia. }
assert (PSTOK : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B))
  by (intros a Ha; exact (conj (tpi_pst_img B HIMG a Ha) (tpi_pst_owned B HIMG a Ha))).
pose (RUNTO := @paj_run_to_x_m_invR fx rc SK A_prog_listing TP_PAListing PA B prh_pst (ARcfx B) _ LAWS PSTOK P PLAW
  RW (wle'_refl segs RZc) (wle'_trans segs RZc)).
destruct HARM as (Hr4 & Hr16 & HGR).
(* ---- the two stores, stop at +248 ---- *)
  pose proof HGR as (HBLK & HBY & HSD & HKP & HGROW & HBB & HSIDE & HPOSg).
  pose proof HBLK as (Hq0 & Hin2 & H4096 & Hce2 & Ham2 & Hwr2 & Hrab2 & Hhull2 & Hlam2).
  set (E := tpg_E regs2 [tp_b0 D; tp_len0 D; tp_cap0 D]).
  assert (HEI : img_env VAL A_LIM E) by (unfold E, tpg_E; apply Eimg_env).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r).
  { intros n r Hn. unfold E, tpg_E. pose proof (u5_range r) as Hr.
    rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ n r Hn). }
  assert (E33 : ew E 33 = Z_to_bv 64 (tp_len0 D)).
  { unfold E, tpg_E. rewrite !Eimg_low by (unfold A_TEXT; lia). reflexivity. }
  assert (U8 : forall c, 0 <= c <= 28 -> U E (SOff 8 c) = tp_t D + c).
  { intros c Hc. rewrite U_SOff, (ER 8%nat 8%bv eq_refl), R8. unfold w64. rewrite unsigned_lit_small by lia.
    apply zcanon_id. unfold M64. lia. }
  assert (UE8 : bv_unsigned (ew E 8) = tp_t D).
  { rewrite (ER 8%nat 8%bv eq_refl), R8. unfold w64. apply unsigned_lit_small. lia. }
  assert (U22 : U E (SOff 22 0) = SHADOW_OFF).
  { rewrite U_SOff, (ER 22%nat 22%bv eq_refl), R22. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
  assert (HRO : regs_ok E tpg_gt_srF regs2).
  { assert (RO0 : regs_ok E sr_atoms regs2) by exact (regs_ok_Eimg_Ereg regs2 _).
    unfold tpg_gt_srF.
    apply tpg_regs_ok_set; [apply tpg_regs_ok_set; [apply tpg_regs_ok_set; [apply tpg_regs_ok_set;
      [apply tpg_regs_ok_set; [exact RO0|] |] |] |] |].
    - rewrite R19. apply tpg_denot_U. apply U8. lia.
    - rewrite R21. apply tpg_denot_U. apply U8. lia.
    - rewrite R23. apply tpg_denot_U. apply tpg_U_sh; [apply U8; lia | exact U22 | lia].
    - rewrite R25. apply tpg_denot_U. apply tpg_U_sh; [apply U8; lia | exact U22 | lia].
    - rewrite R27. apply tpg_denot_U. apply tpg_U_sh; [rewrite (U8 0 ltac:(lia)); lia | exact U22 | lia]. }
  assert (HS : st_ok_pi segs VAL E tpg_gt_ssF
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 (BASE + (TP_OFF + 196))) mem2 (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold tpg_gt_ssF. apply pa_entry_st_ok_full.
    - exact HRO.
    - vm_compute. reflexivity.
    - constructor; [|constructor]. unfold region_ok, tpg_gt_recF.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UE8. split; [lia|]. split; [lia|]. split; [intros q Hq; apply HWR2; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (tp_t D) 8 8 (SOff 33 0) (tp_len0 D)); [| lia | lia |].
      + cbn [sv_denot]. rewrite E33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
      + apply (KW (tp_t D + 8) 8%nat (tp_len0 D)); [unfold tpg_spc, tp_sp0, TP_FRAME; lia | lia | exact Ml3].
    - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      unfold tpg_gt_factsF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (ER 8%nat 8%bv eq_refl), R8, (ER 10%nat 10%bv eq_refl), R10, (ER 22%nat 22%bv eq_refl), R22, E33.
      unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
      destruct Ht47 as [Ht47a Ht47b]. Z.div_mod_to_equations. lia. }
  assert (SHOK : sh_ok segs TPG_Bx [] E (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
  (* the run reads an empty-budget journal: the post-call one, rebased at its depot *)
  unfold tp_JR in HJ. pose proof HJ as HJw.
  pose proof (ajournal_xw_rebaseR (SK := SK) segs B prh_pst _ RW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJr.
  clear HJ. rename HJr into HJ.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM TPG_Bspan (TP_OFF + TP_PC_FIT).
  1-3: (* the three token checks (t, t + 8, t + 16): the record is addressable after the call (prhtx_place at the
          post state, tpg_place_at) *)
    cbn [ms_mem YK11.mkst]; change (rd_of segs (rdW W2 mem2)) with (aview segs (w_H W2) mem2);
    unfold TPG_Bx; rewrite U22, U8 by lia;
    apply (range_addressable_sub _ SHADOW_OFF (tp_t D) 28 _ 8 HRA2); lia.
  { (* the writes: the record's first 24 bytes, in the widened journal's window *)
    intros a (r & Hin & Ha). unfold tpg_gt_ssF in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | []]. unfold tpg_gt_recF in Ha.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UE8 in Ha.
    left. unfold awr_byte. left. unfold tp_sp0. rewrite ESTK. lia. }
  (* ---- at +248 ---- *)
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msE end.
  lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdq) _ => set (mdE := mdq) in * end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E' := Ex) in HS end.
  (* the run havocs the three shadow bytes it loads (atoms 512..514); the record's atoms are below them *)
  assert (AGF : env_agree 512 E E').
  { unfold E'. split; [intros n Hn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]. }
  assert (AGD : forall e, sv_atoms_lt 512 e = true -> sv_denot E' e = sv_denot E e)
    by (intros e He; exact (sv_denot_agree 512 E E' e AGF He)).
  lazymatch type of HS with st_ok_pi _ _ _ ?ssE _ =>
    assert (RF : forall r : bv 5, sr_get (ss_regs ssE) r = sr_get tpg_gt_srF r ->
        sv_atoms_lt 512 (sr_get tpg_gt_srF r) = true -> getr (ms_regs msE) r = getr regs2 r)
      by (intros r Hr Ha; exact (tpg_gt_reg_same E E' _ (w_H W2) msE regs2 tpg_gt_srF r 512 HS AGF HRO Hr Ha)) end.
  assert (F2 : getr (ms_regs msE) 2 = getr regs2 2) by (apply RF; vm_compute; reflexivity).
  assert (F3 : getr (ms_regs msE) 3 = getr regs2 3) by (apply RF; vm_compute; reflexivity).
  assert (F4 : getr (ms_regs msE) 4 = getr regs2 4) by (apply RF; vm_compute; reflexivity).
  assert (F8 : getr (ms_regs msE) 8 = getr regs2 8) by (apply RF; vm_compute; reflexivity).
  assert (F9 : getr (ms_regs msE) 9 = getr regs2 9) by (apply RF; vm_compute; reflexivity).
  assert (F18 : getr (ms_regs msE) 18 = getr regs2 18) by (apply RF; vm_compute; reflexivity).
  assert (F19 : getr (ms_regs msE) 19 = getr regs2 19) by (apply RF; vm_compute; reflexivity).
  assert (F21 : getr (ms_regs msE) 21 = getr regs2 21) by (apply RF; vm_compute; reflexivity).
  assert (F22 : getr (ms_regs msE) 22 = getr regs2 22) by (apply RF; vm_compute; reflexivity).
  assert (F23 : getr (ms_regs msE) 23 = getr regs2 23) by (apply RF; vm_compute; reflexivity).
  assert (F25 : getr (ms_regs msE) 25 = getr regs2 25) by (apply RF; vm_compute; reflexivity).
  assert (F26 : getr (ms_regs msE) 26 = getr regs2 26) by (apply RF; vm_compute; reflexivity).
  (* the three chunks the region holds: b1 = res at t, len0 at t + 8, cap1 = tp_req at t + 16 *)
  pose proof (st_ok_mem_ok segs _ _ _ HS) as (_ & HMO & _). cbn [ss_mem abs_ss setpc ms_mem restrict] in HMO.
  pose proof (Forall_inv HMO) as RG. clear HMO.
  assert (U9 : U E (SOff 9 0) = tp_n D).
  { rewrite U_SOff, (ER 9%nat 9%bv eq_refl), R9. unfold w64. rewrite unsigned_lit_small by lia.
    rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
  assert (U33 : U E (SOff 33 0) = tp_len0 D).
  { rewrite U_SOff, E33. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
  assert (DB : sv_denot E (SOff 10 0) = Z_to_bv 64 res).
  { apply tpg_denot_U. rewrite U_SOff, (ER 10%nat 10%bv eq_refl), R10. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
  assert (DL : sv_denot E (SOff 33 0) = Z_to_bv 64 (tp_len0 D)) by (apply tpg_denot_U; exact U33).
  assert (DC : sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 9 0) (SLit 1)) (SLit 2))
      (SAlu ALU_SLL (SOff 33 0) (SLit 1))) = Z_to_bv 64 (tp_req D)).
  { apply tpg_denot_U. rewrite tpg_U_add, tpg_U_add.
    rewrite (tpg_gt_U_sll1 E (SOff 9 0)) by (rewrite U9; lia).
    rewrite (tpg_gt_U_sll1 E (SOff 33 0)) by (rewrite U33; lia).
    rewrite U9, U33, U_SLit. rewrite (zcanon_id 2) by (unfold M64; lia).
    rewrite (Z.mod_small (2 * tp_n D + 2)) by lia. rewrite Ereq, Z.mod_small by lia. lia. }
  assert (UE8' : bv_unsigned (ew E' 8) = tp_t D) by (rewrite (proj1 AGF 8%nat ltac:(lia)); exact UE8).
  assert (DB' : sv_denot E' (SOff 10 0) = Z_to_bv 64 res) by (rewrite AGD by (vm_compute; reflexivity); exact DB).
  assert (DL' : sv_denot E' (SOff 33 0) = Z_to_bv 64 (tp_len0 D))
    by (rewrite AGD by (vm_compute; reflexivity); exact DL).
  assert (DC' : sv_denot E' (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 9 0) (SLit 1)) (SLit 2))
      (SAlu ALU_SLL (SOff 33 0) (SLit 1))) = Z_to_bv 64 (tp_req D))
    by (rewrite AGD by (vm_compute; reflexivity); exact DC).
  pose proof (tpg_gt_chunk_val _ _ 8%nat 0 24 0 24 _ 0 8 _ res RG ltac:(right; left; reflexivity) DB'
    ltac:(cbn; lia) ltac:(cbn; lia)) as VB.
  pose proof (tpg_gt_chunk_val _ _ 8%nat 0 24 0 24 _ 8 8 _ (tp_len0 D) RG ltac:(right; right; left; reflexivity) DL'
    ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
  pose proof (tpg_gt_chunk_val _ _ 8%nat 0 24 0 24 _ 16 8 _ (tp_req D) RG ltac:(left; reflexivity) DC'
    ltac:(cbn; lia) ltac:(cbn; lia)) as VC.
  rewrite UE8' in VB, VL, VC. rewrite Z.add_0_r in VB. change (N.to_nat 8) with 8%nat in VB, VL, VC.
  (* the memory after the run: the post-call state's but for the record's first 24 bytes *)
  assert (NW : forall a, ~ (tp_t D <= a < tp_t D + 24) -> ~ in_wrange E (ss_mem tpg_gt_ssF) a).
  { intros a H1 (r & Hin & Ha). unfold tpg_gt_ssF in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | []]. unfold tpg_gt_recF in Ha.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UE8 in Ha. lia. }
  assert (KM : TxPutKeep102.tpk_mlo W2 W2 mem2 (ms_mem msE)).
  { intros x Hx. apply HFr. apply NW. lia. }
  pose proof (TxPutKeep102.tpk_alo_of_mlo _ _ _ _ KM) as KA.
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 24) ->
    aview segs (w_H W2) (ms_mem msE) a = aview segs (w_H W2) mem2 a).
  { intros a Ha H1. apply TxPutKeep102.tpk_aview_of_m. apply HFr.
    rewrite TxPutKeep102.tpk_word_small by exact Ha. exact (NW a H1). }
  assert (KVM : forall a n v, val_mem segs (rdW W2 mem2) a n v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (a + Z.of_nat n <= tp_t D \/ tp_t D + 24 <= a) -> val_mem segs (rdW W2 (ms_mem msE)) a n v).
  { intros a n v Hv H0 H1 H2. apply (val_mem_kept segs (w_H W2) (w_H W2) mem2 (ms_mem msE) a n v); [|exact Hv].
    intros kk Hkk. apply KALL; lia. }
  assert (HBLKS : forall p n, In (p, n) (ablocks B ly2 S2) -> 4096 <= p /\ p + req_size n <= YM05.alloc_ceiling).
  { intros p n Hin. pose proof (alx_blocks segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ HAR2 Hin) as (_ & H4 & Hc & _).
    split; [exact H4 | exact Hc]. }
  (* ---- the continuation at +248 ---- *)
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?pc) _ _) _) _ =>
    replace pc with (tp_pc TP_PC_FIT) by (unfold tp_pc; rewrite TP_OFF_val; unfold TP_PC_FIT; lia) end.
  apply (KFIT ly2 S2 (tp_Hp D) W2 (ms_regs msE) (ms_mem msE) mdE k2 res (tp_req D)); [|exact HPM].
  exists WS. split; [exact HBUD|].
  split.
  { (* tp_carry *)
    split; [exact HPRE|].
    split; [unfold tp_JR; eapply (ajournal_xw_unbase0R (SK := SK) segs B prh_pst _ RW); [exact HJ | exact (ajxR_wild HJw)]|].
    split.
    { unfold tp_KR in HK |- *.
      apply (tpg_gt_kept_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK HAR2); [|apply same_but_materialized_wvb_any].
      intros a Ha Hor. apply KALL; [exact Ha|]. intros Hr. apply Hor.
      unfold tp_OR, tp_FP, prhtx_fp. exists (tp_t D, tp_t D + 28). split; [left; reflexivity | cbn [fst snd]; lia]. }
    split; [intros r Hr; cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; [rewrite F3 | rewrite F4];
      apply HKR; cbn; auto|].
    split; [unfold spZ; rewrite F2; exact HSP|].
    split.
    { unfold tp_saved, tp_sp0 in HSV3 |- *.
      destruct HSV3 as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (apply KVM; [eapply KW; [unfold tpg_spc, tp_sp0, TP_FRAME; lia | lia | eassumption] | lia | lia | lia]). }
    split; [reflexivity|].
    exact (TxPutKeep102.keep_arodata_okP B W2 W2 mem2 (ms_mem msE) HROD2 KA). }
  split; [unfold tp_shregs; rewrite F22, F8, F9, F18; exact HSHR|].
  split; [exact Hf0|].
  split; [rewrite F19; exact R19|]. split; [rewrite F21; exact R21|].
  split; [rewrite F23; exact R23|]. split; [rewrite F25; exact R25|]. split; [rewrite F26; exact R26|].
  split.
  { unfold tp_recat, prhtx_rec. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
    split; [exact VB|]. split; [exact VL|]. split; [exact VC|].
    apply KVM; [eapply KW; [unfold tpg_spc, tp_sp0, TP_FRAME; lia | lia | exact Mf3] | lia | lia | lia]. }
  split; [exact (tpg_gt_blk_keep D ly2 S2 W2 W2 mem2 (ms_mem msE) res (tp_req D) HBLK KA KM)|].
  split; [eapply TxPutKeep102.keep_bytes_at; [exact HBY | lia | lia | exact KA]|].
  split; [lia|].
  split; [exact HSD|].
  split; [exact HKP|].
  split; [right; split; [exact Hneed|]; split; [reflexivity|]; split; [exact HGROW | exact HBB]|].
  split; [|exact HPOSg].
  (* tp_side: the ledger, the own cell and the source window lie below the ceiling *)
  destruct HSIDE as (HLG2 & HSRC2 & HRL2).
  assert (HHL : forall a k, In (a, k) (tp_Lam D) -> 0 <= a - cf_head /\ a - cf_head + 8 <= YM05.alloc_ceiling)
    by exact (TxPutKeep102.tpk_heads_lo B _ _ _ _ _ _ _ _ _ _ _ _ HLG2 (tpi_head_wide B HIMG) HBLKS).
  split; [eapply TxPutKeep102.keep_prh_ledger; [exact HLG2 | exact KA | exact (tpi_pst_img B HIMG) | exact HHL]|].
  split; [eapply TxPutKeep102.keep_src_rd; [exact HSRC2 | exact KA] | exact HRL2].
Qed.


(* ---- the segment ---- *)
Theorem tp_seg_GROW_holds : tp_seg_GROW_stmt B SK CTX0.
Proof.
intros AREAL AREALN ARX_DEPOT P PLAW PCALL Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT HIMG KFIT HPM.
destruct HAT as (HK1 & HCAR & HSHR & Hf0 & Hneed & Ely3 & ES3 & R11 & R12 & R19 & R21 & R20 & R23 & R25 & R24 & R26
  & HREC & HINV & HTR & HSIDE).
subst ly3 S3.
pose proof HCAR as (HPRE & HJ & HK & HKR & HSP & HSV & EHp & HROD). subst Hp3.
pose proof HSHR as (R22 & R8 & R9 & R18).
pose proof HPRE as (HFP & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFWIN & HPLACE & HTRACE0 & HREC0 & HINV0
  & HSRC0 & HSLEN & HKEPT0 & HDISJ & HNEEDB & HLG0 & HEV0 & HLIVEB & HREQ & HHULL).
pose proof HFP as (HAFN & HROD0 & HSTKHI & HRAC).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & Hpres & Hch & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit & Hra28).
pose proof HREC as (Rb0 & Rl0 & Rc0 & Rf0 & Mb & Ml & Mc & Mf).
pose proof HINV as (Hltxt & Hinv).
pose proof (tpg_STK) as ESTK. assert (HAS : ASTACK = 16384) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (HCE & _). unfold ASAN_CEIL in HCE.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs. pose proof (@pa_B_ok _ _ PA) as HBASE.
unfold tp_sp0 in *. unfold TP_FRAME in *. rewrite ESTK in Hslo, Hbot. unfold TP_FRAME in *.
assert (Ht47 : 2 ^ 46 <= tp_t D /\ tp_t D + 28 <= 2 ^ 47) by lia.
assert (HtA : 0 <= tp_t D < 2 ^ 64) by lia.
assert (Hn0 : 0 <= tp_n D) by lia.
assert (Hb0r : 0 <= tp_b0 D <= 2 ^ 47)
  by (destruct Hinv as [(_ & Eb & _) | (_ & _ & _ & _ & _ & Hce8 & _)]; [lia | lia]).
unfold tp_need, tp_req in *.
(* the cut's symbolic state *)
set (E := tpg_E regs3 [tp_b0 D; tp_len0 D; tp_cap0 D]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, tpg_E; apply Eimg_env).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r).
{ intros n r Hn. unfold E, tpg_E. pose proof (u5_range r) as Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs3 _ n r Hn). }
assert (EX : ew E 32 = Z_to_bv 64 (tp_b0 D) /\ ew E 33 = Z_to_bv 64 (tp_len0 D) /\ ew E 34 = Z_to_bv 64 (tp_cap0 D)).
{ unfold E, tpg_E. rewrite !Eimg_low by (unfold A_TEXT; lia). repeat split. }
destruct EX as (E32 & E33 & E34).
assert (U8 : forall c, 0 <= c <= 28 -> U E (SOff 8 c) = tp_t D + c).
{ intros c Hc. rewrite U_SOff, (ER 8%nat 8%bv eq_refl), R8. unfold w64. rewrite unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia. }
assert (U22 : U E (SOff 22 0) = SHADOW_OFF).
{ rewrite U_SOff, (ER 22%nat 22%bv eq_refl), R22. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
assert (HRO : regs_ok E tpg_sr regs3).
{ assert (RO0 : regs_ok E sr_atoms regs3) by exact (regs_ok_Eimg_Ereg regs3 _).
  unfold tpg_sr.
  apply tpg_regs_ok_set; [apply tpg_regs_ok_set; [apply tpg_regs_ok_set; [apply tpg_regs_ok_set;
    [apply tpg_regs_ok_set; [exact RO0|] |] |] |] |].
  - rewrite R19. apply tpg_denot_U. apply U8. lia.
  - rewrite R21. apply tpg_denot_U. apply U8. lia.
  - rewrite R23. apply tpg_denot_U. apply tpg_U_sh; [apply U8; lia | exact U22 | lia].
  - rewrite R25. apply tpg_denot_U. apply tpg_U_sh; [apply U8; lia | exact U22 | lia].
  - rewrite R26. apply tpg_denot_U. rewrite tpg_U_srl, (U8 0 ltac:(lia)), Z.add_0_r by lia.
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
assert (HS : st_ok_pi segs VAL E tpg_ss0
  (restrict (w_H W3) (YK11.mkst regs3 (Z_to_bv 64 (BASE + (TP_OFF + TP_PC_GROW))) mem3 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold tpg_ss0. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, tpg_rec.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (ER 8%nat 8%bv eq_refl), R8. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (chunk_ok_val segs E _ (tp_t D) 0 8 (SOff 32 0) (tp_b0 D)); [| lia | lia |].
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
      * rewrite Z.add_0_r. exact Mb.
    + apply (chunk_ok_val segs E _ (tp_t D) 8 8 (SOff 33 0) (tp_len0 D)); [| lia | lia | exact Ml].
      cbn [sv_denot]. rewrite E33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    + apply (chunk_ok_val segs E _ (tp_t D) 16 8 (SOff 34 0) (tp_cap0 D)); [| lia | lia | exact Mc].
      cbn [sv_denot]. rewrite E34, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    unfold tpg_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ER 8%nat 8%bv eq_refl), R8, (ER 22%nat 22%bv eq_refl), R22, E32, E33, E34. unfold w64.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
    destruct Ht47 as [Ht47a Ht47b]. Z.div_mod_to_equations. lia. }
assert (SHOK : sh_ok segs TPG_Bx [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
(* the call's own journal, rooted at the GROW cut: window ASTACK below the call's sp, footprint the old buffer *)
pose proof HJ as (HARJ & HlyJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _ & _ & HQTJ & _).
assert (HJg : ajournal_x (SK := SK) segs B prh_pst (ARcfx B) ASTACK (tpg_spc D) (tpg_FP1 D)
  (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 [] (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 0).
{ apply tpg_jrefl; [exact HARJ | | | exact HQTJ].
  - unfold tpg_spc, tp_sp0, TP_FRAME. unfold astk_ok. rewrite HAS. repeat split; try lia.
    rewrite Zminus_mod, Hal16. reflexivity.
  - intros a Ha. apply HpresJ. unfold tpg_spc, tp_sp0, TP_FRAME in *. rewrite ESTK, HAS. unfold TP_FRAME. lia. }
pose (RUN := paj_run_x_inv (SK := SK) B prh_pst (ARcfx B) LAWS P PLAW).
(* the run to the call is plain: lifted ONCE here, at the cut before the call *)
apply (YGcfRhLift.ra_rh_of_SRr segs RZc).
unfold tp_cfg, tp_pc. rewrite <- Z.add_assoc.
pose proof (tpg_place_at (@wle segs) D (tp_ly D) (tp_S D) W3 mem3 md3 k [] HPRE HJ) as HPL3.
pose proof HPL3 as (_ & _ & _ & HWR3 & HRA3).
paj_run_tok_x_inv RUN HS HJg SHOK HPM TPG_Bspan.
{ cbn [ms_mem mkst]. change (rd_of segs (rdW W3 mem3)) with (aview segs (w_H W3) mem3).
  unfold TPG_Bx. rewrite U22, (U8 0 ltac:(lia)), Z.add_0_r.
  apply (range_addressable_sub _ SHADOW_OFF (tp_t D) 28 (tp_t D) 8 HRA3); lia. }
{ unfold tpg_ss0. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
(* ---- at the realloc wrapper's entry ---- *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msc end.
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EMc end.
clear HF HFr HG.
lazymatch type of HS with st_ok _ (ewset E 512 ?w0) _ _ => set (E' := ewset E 512 w0) in HS |- * end.
assert (AGc : env_agree 512 E E') by (unfold E'; apply env_agree_ewset).
assert (UA : forall n c, (n < 512)%nat -> U E' (SOff n c) = U E (SOff n c))
  by (intros n c Hn; unfold E'; rewrite !U_SOff, ew_ewset_other by lia; reflexivity).
lazymatch goal with H : img_env _ _ E' |- _ => rename H into HEIc | H : img_env _ _ (ewset E 512 _) |- _ => rename H into HEIc end.
(* the call's registers *)
assert (RK : forall ss (r : bv 5), st_ok segs E' ss (restrict (w_H W3) msc) ->
    sr_get (ss_regs ss) r = sr_get tpg_sr r -> sv_atoms_lt 512 (sr_get tpg_sr r) = true ->
    getr (ms_regs msc) r = getr regs3 r)
  by (intros ss r HSS E1 E2; exact (tpg_reg_of_sv E E' ss (w_H W3) msc regs3 tpg_sr r 512 HSS AGc HRO E1 E2)).
assert (Rc2 : getr (ms_regs msc) 2 = getr regs3 2) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc3 : getr (ms_regs msc) 3 = getr regs3 3) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc4 : getr (ms_regs msc) 4 = getr regs3 4) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc8 : getr (ms_regs msc) 8 = getr regs3 8) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc9 : getr (ms_regs msc) 9 = getr regs3 9) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc18 : getr (ms_regs msc) 18 = getr regs3 18) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc19 : getr (ms_regs msc) 19 = getr regs3 19) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc20 : getr (ms_regs msc) 20 = getr regs3 20) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc21 : getr (ms_regs msc) 21 = getr regs3 21) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc22 : getr (ms_regs msc) 22 = getr regs3 22) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc23 : getr (ms_regs msc) 23 = getr regs3 23) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc24 : getr (ms_regs msc) 24 = getr regs3 24) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc25 : getr (ms_regs msc) 25 = getr regs3 25) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc26 : getr (ms_regs msc) 26 = getr regs3 26) by (apply (RK _ _ HS); vm_compute; reflexivity).
assert (Rc27 : getr (ms_regs msc) 27 = w64 (SHADOW_OFF + tp_t D / 8)).
{ rewrite (st_ok_restrict_reg segs (w_H W3) E' _ msc 27%bv HS).
  change (sr_get _ 27%bv) with (tpg_sh (SOff 8 0)). apply tpg_denot_U.
  apply tpg_U_sh; [rewrite UA by lia; rewrite (U8 0 ltac:(lia)); lia | rewrite UA by lia; exact U22 | lia]. }
assert (Rc10 : getr (ms_regs msc) 10 = w64 (tp_b0 D)).
{ rewrite (st_ok_restrict_reg segs (w_H W3) E' _ msc 10%bv HS).
  change (sr_get _ 10%bv) with (SOff 32 0). apply tpg_denot_U.
  rewrite UA by lia. rewrite U_SOff, E32, unsigned_lit_small, Z.add_0_r by lia. apply zcanon_id. unfold M64. lia. }
assert (Rc11 : getr (ms_regs msc) 11 = w64 (tp_req D)).
{ rewrite (st_ok_restrict_reg segs (w_H W3) E' _ msc 11%bv HS).
  change (sr_get _ 11%bv) with (SAlu ALU_SLL (SOff 11 0) (SLit 1)). apply tpg_denot_U.
  rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite UA by lia.
  rewrite U_SOff, (ER 11%nat 11%bv eq_refl), R11. unfold w64. rewrite unsigned_lit_small by lia.
  unfold tp_req, tp_need. rewrite (zcanon_id (tp_len0 D + tp_n D + 1 + 0)) by (unfold M64; lia).
  rewrite (zcanon_id 1) by (unfold M64; lia). change (Z.land 1 63) with 1.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
assert (Rc1 : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + 14288)).
{ rewrite (st_ok_restrict_reg segs (w_H W3) E' _ msc 1%bv HS).
  change (sr_get _ 1%bv) with (SOff A_TEXT 14288). exact (codeptr_val E' 14288 HEIc). }
assert (Hraw14 : 0 <= BASE + 14288 < 2 ^ 64)
  by (rewrite (tpi_base B HIMG); unfold A_prog_base; lia).
assert (Hspc : spZ (ms_regs msc) = tpg_spc D) by (unfold spZ, tpg_spc, tp_sp0, TP_FRAME; rewrite Rc2; exact HSP).
pmkst HS. rewrite EMc in HJg |- *.
(* the call's chain and its trace in the universe *)
assert (Hrec3 : forall a, tp_t D <= a < tp_t D + 28 -> aview segs (w_H W3) mem3 a <> None).
{ intros a Ha. apply tpg_aview_present. apply HpresJ. rewrite ESTK, HAS. unfold tp_sp0. lia. }
assert (Hs0c : s0Z (ms_regs msc) = tp_t D).
{ unfold s0Z. rewrite Rc8, R8. unfold w64. apply unsigned_lit_small. lia. }
assert (Hrac : raZ (ms_regs msc) = BASE + 14288).
{ unfold raZ. rewrite Rc1. apply unsigned_lit_small. exact Hraw14. }
assert (Hrapi : raZ (ms_regs msc) = pi_ret_tx_realloc).
{ rewrite Hrac, (tpi_base B HIMG). vm_compute. reflexivity. }
assert (Hra4c : 4096 <= raZ (ms_regs msc)) by (rewrite Hrac, (tpi_base B HIMG); vm_compute; discriminate).
assert (Hspt : spZ (ms_regs msc) + 16 <= tp_t D).
{ rewrite Hspc. unfold tpg_spc, tp_sp0, TP_FRAME. lia. }
assert (Hceilt : YM05.alloc_ceiling <= tp_t D) by lia.
pose proof (YGcallcf.universe_ok_of_ARcf segs B _ _ _ _ _ _ (proj1 HARJ)) as HU.
destruct (tp_trace_universe B CTX0 (tp_ly D) W3 mem3 (tp_t D) (tp_ly D) W3 mem3 (ms_regs msc) HU HTR HUNIV
  ltac:(vm_compute; reflexivity) Hceilt Hs0c Hrapi Hra4c Hspt eq_refl (fun a _ _ => eq_refl) Hrec3)
  as (ch & Hchc & Htrc).
assert (HHO : cf_hull_ok (tp_S D)) by exact (tpi_hull_ok B HIMG _ _ _ _ _ _ _ HHULL HPOS).
assert (HRQ : qtight (tp_S D) /\ ROOM_cf_k (tp_S D) RK_realloc) by exact (tp_RQ_of_live (tp_S D) HRL HQTJ).
assert (Hraok : YK0s.ret_ok (Z_to_bv 64 (BASE + 14288))).
{ replace 14288 with (TP_OFF + 196) by (unfold TP_OFF, TP_SLOT; reflexivity).
  apply (ret_ok_codeptr_v (PI := PA)); [unfold TP_OFF, TP_SLOT; lia | vm_compute; reflexivity]. }
assert (Hlive2 : blocks_bytes (tp_S D) + tp_req D <= LIVE_MAX) by (unfold tp_req, tp_need, LIVE_tx in *; lia).
assert (Hreqr : 1 <= tp_req D < cf_malloc_max) by (unfold tp_req, tp_need in *; lia).
rewrite EMc in HPM.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdc := m) in * end.
(* the call's QMm_cf: the state part from room_live_cf and the hull, the read-only view from the carry's (the cf
   bounds are the listing's, tpi_relro_bounds) *)
assert (HQM : QMm_cf segs B (tp_S D) mem3).
{ pose proof (tpi_relro_bounds B HIMG) as (ERL & ERH & ETOP).
  apply (QMm_cf_of_room segs B (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 (proj1 HARJ) HQTJ
    (YGcfRoomLive.room_live_room _ HRL) HHO).
  apply (YGcfAroBridge.arodata_ok_cf_of_P segs B W3 mem3 (tpi_relro_seg B HIMG) (tpi_errno_relro B HIMG) ETOP
    (tpi_ro_reads_nw B HIMG)).
  rewrite <- ERL, <- ERH. exact HROD. }
assert (HKR3 : getr (ms_regs msc) 3 = w64 (as_gp B)) by (rewrite Rc3, (HKR 3%bv ltac:(left; reflexivity)); exact Hgp).
assert (HKR4 : getr (ms_regs msc) 4 = w64 (as_tp B))
  by (rewrite Rc4, (HKR 4%bv ltac:(right; left; reflexivity)); exact Htp).
assert (HRQ0 : qtight (tp_S D) /\ ROOM_cf_k (tp_S D) (RK_realloc + 0)) by exact HRQ.
assert (Hsp0c : spZ (ms_regs msc) = tpg_spc D + 0) by (rewrite Hspc; lia).
assert (Hceilc : YM05.alloc_ceiling <= spZ (ms_regs msc) - ASTACK).
{ rewrite Hspc. unfold tpg_spc, tp_sp0, TP_FRAME in *. rewrite HAS. lia. }
set (trq := call_trace (tp_ly D) cf_pc_realloc_ra0 (ms_regs msc) ch) in *.
(* the realloc rules and their model laws take the univcore admission at the call state. In the batch kit's text the call's
   trace is WILD (prhtx_trace: inU), and the text gives the room for this call's one wild trace (tp_k1pre's wild room,
   kr = tp_evk D = 1 for a grow), so the trace is admitted at the call state - the GROW cut's, tp_S D - by
   YCbqGwild.wild_room_admits, with the depot's NoDup from ARX_DEPOT (AR_laws_x's field 25 at ARcfx; the statement's
   binder, which the instance projects from the cf laws) *)
pose proof (proj1 HK1 Hf0) as Hroom. rewrite (tp_evk_grow D Hneed) in Hroom.
pose proof (YCbqGwild.wild_room_admits (as_universe B) [] 1 (tp_S D) trq (ARX_DEPOT _ _ _ _ _ _ HARJ) Hroom Htrc
  (or_intror Nat.lt_0_1)) as Hadm.
assert (Hr2 : 0 <= tp_req D < cf_malloc_max) by lia.
assert (Hq2 : 0 <= tp_req D) by lia.
(* the registers the continuation reads, through the call (aregs_preserved) *)
assert (RKEEP : forall regs2 (r : bv 5), aregs_preserved (ms_regs msc) regs2 -> acallee_saved (bv_unsigned r) ->
  getr regs2 r = getr (ms_regs msc) r).
{ intros regs2 r HP Hr. pose proof (HP (bv_unsigned r) Hr) as Er. rewrite Z_to_bv_bv_unsigned in Er. exact Er. }
destruct (Z.eq_dec (tp_cap0 D) 0) as [Hc0 | Hc0].
- (* cap0 = 0: realloc (NULL, 2 * need), YGcallRxKeep.v's null rule with the keep *)
  pose proof HINV as (Hltxt0 & [(_ & Eb0 & El0) | (Hc & _)]); [|lia].
  assert (Rc10' : getr (ms_regs msc) 10 = w64 0) by (rewrite Rc10, Eb0; reflexivity).
  assert (Hreq1 : 0 < tp_req D) by lia.
  eapply SRr_bind.
  { exact (YGcallRxKeep.aj_realloc_null_at_x_keep segs B prh_pst (ARcfx B) (QMm_cf segs B)
      (fun s _ _ => qtight s /\ ROOM_cf_k s (RK_realloc + 0)) malloc_cf cf_malloc_max free_cf
      (Wf_cf (as_universe B)) xs_cf LAWS (@pa_segs_low _ _ PA) (palc_env B (tpi_pal B HIMG)) OWNLOW WFL
      (realloc_null_model_law_x_cf B 0 HU) XSL _ _ (YGcallRxKeep.arealloc_null_realizes_x_cf_keep segs B _ AREALN)
      W3 (ms_regs msc) mem3 ASTACK (tpg_spc D) (tpg_FP1 D) (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 []
      (tp_ly D) (tp_S D) (tp_Hp D) mdc _ (tp_req D) 0 _ ch
      HJg Rc10' Rc11 Hreqr Hlive2 Hsp0c eq_refl ltac:(lia) ltac:(lia) HKR3 HKR4 Rc1 Hraok HQM HRQ0 Hchc Hadm). }
  intros W2 c2 HW2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPR & Ha0r & Hfr2 & HPREc & _ &
    (q & Eq & Hqn & (trc & Hpath & Hgf) & Hleaf) & HARM).
  (* the call's trace is WILD in the batch kit: it stays in the post journal's budget ([] ++ [trq]) *)
  pose proof Hleaf as Hleaf0.
  destruct Hleaf as (ly' & regs' & mem' & md' & Ec & HPC2 & Hr10' & Hqt' & _ & _ & _ & HMN).
  pose proof (f_equal (fun c => ms_mem (cfg_ms c)) Ec) as Em. unfold cfg_at in Em. cbn in Em. subst mem'.
  pose proof (PCALL mem3 mem2 HMN HPM) as HPM2.
  pose proof HPREc as (HARc & _).
  pose proof HPC2 as (HAR' & _ & _ & _ & _ & HFRM & _).
  (* the registers after the call *)
  assert (K2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs msc) r)
    by (intros r Hr; exact (RKEEP regs2 r HPR Hr)).
  assert (KR2 : tp_kregs D regs2).
  { intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]].
    - rewrite (K2 3%bv ltac:(vm_compute; right; left; reflexivity)), Rc3. exact (HKR 3%bv ltac:(left; reflexivity)).
    - rewrite (K2 4%bv ltac:(vm_compute; right; right; left; reflexivity)), Rc4.
      exact (HKR 4%bv ltac:(right; left; reflexivity)). }
  assert (SP2 : spZ regs2 = tp_sp0 D - TP_FRAME).
  { unfold spZ. rewrite (K2 2%bv ltac:(vm_compute; left; reflexivity)), Rc2. exact HSP. }
  assert (SH2 : tp_shregs D regs2).
  { unfold tp_shregs. rewrite (K2 22%bv (tpg_cs_hi 22%bv ltac:(split; vm_compute; discriminate))), (K2 8%bv ltac:(vm_compute; right; right; right; left; reflexivity)),
      (K2 9%bv ltac:(vm_compute; right; right; right; right; left; reflexivity)), (K2 18%bv (tpg_cs_hi 18%bv ltac:(split; vm_compute; discriminate))), Rc22, Rc8, Rc9, Rc18.
    exact HSHR. }
  assert (G19 : getr regs2 19 = w64 (tp_t D + 8)) by (rewrite (K2 19%bv (tpg_cs_hi 19%bv ltac:(split; vm_compute; discriminate))), Rc19; exact R19).
  assert (G21 : getr regs2 21 = w64 (tp_t D + 16)) by (rewrite (K2 21%bv (tpg_cs_hi 21%bv ltac:(split; vm_compute; discriminate))), Rc21; exact R21).
  assert (G20 : getr regs2 20 = w64 (tp_t D + 24)) by (rewrite (K2 20%bv (tpg_cs_hi 20%bv ltac:(split; vm_compute; discriminate))), Rc20; exact R20).
  assert (G23 : getr regs2 23 = w64 (SHADOW_OFF + (tp_t D + 8) / 8))
    by (rewrite (K2 23%bv (tpg_cs_hi 23%bv ltac:(split; vm_compute; discriminate))), Rc23; exact R23).
  assert (G25 : getr regs2 25 = w64 (SHADOW_OFF + (tp_t D + 16) / 8))
    by (rewrite (K2 25%bv (tpg_cs_hi 25%bv ltac:(split; vm_compute; discriminate))), Rc25; exact R25).
  assert (G24 : getr regs2 24 = w64 (SHADOW_OFF + (tp_t D + 24) / 8))
    by (rewrite (K2 24%bv (tpg_cs_hi 24%bv ltac:(split; vm_compute; discriminate))), Rc24; exact R24).
  assert (G26 : getr regs2 26 = w64 (tp_t D / 8)) by (rewrite (K2 26%bv (tpg_cs_hi 26%bv ltac:(split; vm_compute; discriminate))), Rc26; exact R26).
  assert (G27 : getr regs2 27 = w64 (SHADOW_OFF + tp_t D / 8)) by (rewrite (K2 27%bv (tpg_cs_hi 27%bv ltac:(split; vm_compute; discriminate))); exact Rc27).
  replace (BASE + 14288) with (BASE + (TP_OFF + 196)) by (unfold TP_OFF, TP_SLOT; reflexivity).
  pose proof (WFL _ _ _ _ _ _ HARc) as HWFc.
  destruct (realloc_null_model_law_x_cf B 0 HU (tp_S D) (tp_req D) trq HWFc HRQ0 Hreqr Hlive2 Hadm)
    as (_ & _ & _ & HMP & _).
  destruct (HMP trc (q, S2) Hpath) as (_ & _ & _ & HMB). cbn [fst snd] in HMB.
  pose proof (ajournal_xwR_mono (SK := SK) segs B prh_pst (ARcfx B) (@wle segs) RW (wle_wle' segs RZc)
    _ _ _ _ _ (tp_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HJ2R.
  pose proof (tpg_post_of_call D W3 mem3 md3 k ly2 S2 W2 mem2 md2 _ _ HIMG HPRE HJ HK HROD HJ2R) as HPOST.
  pose proof (tp_room_live_after0 B (tp_ly D) (tp_S D) (tp_Hp D) W3 (ms_regs msc) mem3 mdc ch (tp_req D) trq trc q S2
    HRL HLIVE HPREc Hpath) as HRL2.
  destruct HARM as [(Hr0 & Eab2 & Ebl2 & HKP2 & HERR2 & HOOM2 & HREF2) | (Hr4096 & Hr16 & Eab2 & HKP2)].
  + (* refused: REFUTED (the batch kit's consumer window: tpg_refute_null) *)
    exfalso. exact (tpg_refute_null D S2 (tp_req D) trq HPRE HK1 Hf0 Hneed HWFc HREF2).
  + (* granted *)
    assert (Hqnn : q <> PNull) by (intros Hq; apply Hqn in Hq; lia).
    assert (HinqS2 : In (q, tp_req D) (blocks S2)).
    { assert (Hbl : blocks S2 = blocks (tp_S D) ++ [(q, tp_req D)])
        by (destruct q; [exfalso; exact (Hqnn eq_refl) | exact HMB | exact HMB | exact HMB]).
      rewrite Hbl. apply in_or_app. right. left. reflexivity. }
    assert (HPSTK := tpg_pst_after_call W3 mem3 (tp_ly D) (tp_S D) (tp_Hp D) mdc (ms_regs msc) ly' S2 (tp_Hp D) W2 mem2
      md' _ (fun _ => False) HIMG HARc HAR' (fun a H1 H2 H3 H4 H5 _ => HFRM a H1 H2 H3 H4 H5) Hceilc
      (fun a Hx => tpg_E_img (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 mdc ly' S2 (tp_Hp D) W2 mem2 md' a HARc HAR'
         (match Hx with
          | or_introl (conj _ H1) => or_intror (ex_intro _ q (ex_intro _ (tp_req D) (or_intror (conj HinqS2 H1))))
          | or_intror H3 => or_introl H3
          end)) (fun a (Hf : False) _ => Hf)).
    destruct (tpg_side_after_call D W3 mem3 md3 k ly2 S2 W2 mem2 md2 _ _ HIMG HPRE HJ HSIDE HINV HJ2R HPSTK HRL2)
      as (HSIDE2 & HKEPT2).
    pose proof HSIDE2 as (HLG2 & _).
    pose proof (tpg_pos_after_call D (tp_ly D) (tp_Hp D) W3 (ms_regs msc) mem3 mdc ch trq trc q S2 HPRE Hf0 Hneed
      HPREc Hadm (or_introl (conj Hc0 Hpath)) Hqnn) as HPOS2.
    assert (Hnew : In (res, tp_req D) (ablocks B ly2 S2))
      by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
    assert (Hfresh : ~ In (res, tp_req D) (ablocks B (tp_ly D) (tp_S D)))
      by exact (tpg_fresh_new ly2 S2 (tp_Hp D) W2 mem2 md2 _ (res, tp_req D) (proj1 HJ2) Hq2 Eab2).
    destruct (tp_grow_blocks0 B (tp_ly D) (tp_S D) (tp_ly D) (tp_S D) ly2 S2 (tp_b0 D) (tp_cap0 D) res (tp_req D)
      eq_refl Hc0 Hreq1 Eab2) as (HGR & HBB).
    assert (Etxt : tp_txt D = []) by (destruct (tp_txt D); [reflexivity | cbn [length] in Hltxt0; lia]).
    apply SRr_ret. cbv beta.
    apply (tpg_tail P Q D W3 mem3 ly2 S2 W2 regs2 mem2 md2 _ _ res PLAW HIMG KFIT (tpg_budget_grow D trq Hneed) HPRE
      Hf0 Hneed HREC HSV KR2 SP2 SH2 G19 G21 G20 G23 G25 G24 G26 G27 Ha0r HPOST HPM2).
    split; [exact Hr4096|]. split; [exact Hr16|].
    split; [exact (tpg_blk_new D ly2 S2 W2 mem2 md2 res HPRE Hneed (proj1 HJ2) Hnew Hfresh HLG2)|].
    split; [rewrite Etxt; exact (tpg_bytes_nil W2 mem2 res)|].
    split; [exact (tpg_src_off_new D ly2 S2 W2 mem2 md2 res HPRE (proj1 HJ2) Hfr2 Hnew Hfresh HLG2 HKEPT2)|].
    split; [exact HKEPT2|]. split; [exact HGR|]. split; [exact HBB|].
    split; [exact HSIDE2 | exact HPOS2].
- (* cap0 > 0: the realloc of the live buffer, YGcallRkKeep.v's rule with the keep *)
  assert (Hcp : 0 < tp_cap0 D) by lia.
  pose proof HINV as (_ & [(Hc & _) | (_ & Hlc & Hin0 & Hby0 & Hb4096 & _ & _ & _ & _ & _ & HLamb)]); [lia|].
  assert (Hb0nz : tp_b0 D <> 0) by lia.
  assert (Hcreq : tp_cap0 D < tp_req D) by (unfold tp_req, tp_need in *; lia).
  assert (HFPc : In (tp_b0 D, tp_cap0 D) (ablocks B (tp_ly D) (tp_S D)) ->
    forall i, 0 <= i < req_size (tp_cap0 D) -> inFP (tpg_FP1 D) (tp_b0 D + i)).
  { intros _ i Hi. unfold tpg_FP1. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). cbn [ablocks_fp map fst snd].
    exists (tp_b0 D, tp_b0 D + req_size (tp_cap0 D)). split; [left; reflexivity | cbn [fst snd]; lia]. }
  (* the freed base is not hidden (YGcallRx's premise ~ In pa Hpc, since YGcallRx.v blob 929b45781ba3): Hp is the ledger's
     Lam heads (entry ledger HLG0 at the entry relation HAR0), and no Lam base is b0's head (HLamb) *)
  assert (Hhid0 : ~ In (tp_b0 D) (tp_Hp D)).
  { intros Hh. apply (tpg_gr_hp_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HLG0 Hin0 HLamb _ Hh).
    pose proof (req_size_pos (tp_cap0 D) ltac:(lia)) as [Hr _]. lia. }
  (* the realloc's hull admission at the run position (the grow's HRe event, tp_pre's guarded entry premise) *)
  assert (HADM : cf_hull_adm (tp_S D) (tp_req D)).
  { pose proof (HEV0 Hf0 Hneed) as Hev. rewrite (proj2 (Z.eqb_neq (tp_cap0 D) 0) Hc0) in Hev.
    exact (tpi_hull_adm B HIMG _ _ _ _ _ _ _ (tp_cap0 D) (tp_req D) HHULL HPOS Hev). }
  pose proof (ajournal_xwR_mono (SK := SK) segs B prh_pst (ARcfx B) (@wle segs) RW (wle_wle' segs RZc)
    _ _ _ _ _ (tp_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJg) as HJgR.
  (* the lift: from here the walk is at wle' segs RZ_cf *)
  apply SRr_ret. cbv beta. unfold SRr'.
  eapply (SRrG_bind segs RW (wle'_trans segs RZc)).
  { exact (YGcallRkKeep.aj_realloc_at_x_cfR_keep (SK := SK) segs B prh_pst LAWS (@pa_segs_low _ _ PA)
      (palc_env B (tpi_pal B HIMG))
      OWNLOW WFL XSL HU 0 (SIGMA AS___wrap_realloc) AREAL []
      W3 (ms_regs msc) mem3 ASTACK (tpg_spc D) (tpg_FP1 D) (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 md3 []
      (tp_ly D) (tp_S D) (tp_Hp D) mdc _ (tp_b0 D) (tp_cap0 D) (tp_req D) 0 _ ch
      HJgR Hin0 Hhid0 Rc10 Rc11 Hreqr Hlive2 Hsp0c eq_refl ltac:(lia) ltac:(lia) HKR3 HKR4 Rc1 Hraok HQM
      (conj (proj1 HRQ0) (conj (proj2 HRQ0) HADM)) Hchc Hadm HFPc). }
  intros W2 c2 HW2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPR & Ha0r & Hfr2 & HPREc & _ &
    (p & q & Ep & Hinp & Eq & Hqn & (trc & Hpath & Hgf) & Hleaf) & HARM).
  pose proof Hleaf as Hleaf0.
  destruct Hleaf as (ly' & regs' & mem' & md' & Ec & Hr10' & Hqt' & HLnull & HLsucc & _ & _ & HMN).
  pose proof (f_equal (fun c => ms_mem (cfg_ms c)) Ec) as Em. unfold cfg_at in Em. cbn in Em. subst mem'.
  pose proof (PCALL mem3 mem2 HMN HPM) as HPM2.
  pose proof HPREc as (HARc & _).
  (* the registers after the call *)
  assert (K2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs msc) r)
    by (intros r Hr; exact (RKEEP regs2 r HPR Hr)).
  assert (KR2 : tp_kregs D regs2).
  { intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]].
    - rewrite (K2 3%bv ltac:(vm_compute; right; left; reflexivity)), Rc3. exact (HKR 3%bv ltac:(left; reflexivity)).
    - rewrite (K2 4%bv ltac:(vm_compute; right; right; left; reflexivity)), Rc4.
      exact (HKR 4%bv ltac:(right; left; reflexivity)). }
  assert (SP2 : spZ regs2 = tp_sp0 D - TP_FRAME).
  { unfold spZ. rewrite (K2 2%bv ltac:(vm_compute; left; reflexivity)), Rc2. exact HSP. }
  assert (SH2 : tp_shregs D regs2).
  { unfold tp_shregs. rewrite (K2 22%bv (tpg_cs_hi 22%bv ltac:(split; vm_compute; discriminate))), (K2 8%bv ltac:(vm_compute; right; right; right; left; reflexivity)),
      (K2 9%bv ltac:(vm_compute; right; right; right; right; left; reflexivity)), (K2 18%bv (tpg_cs_hi 18%bv ltac:(split; vm_compute; discriminate))), Rc22, Rc8, Rc9, Rc18.
    exact HSHR. }
  assert (G19 : getr regs2 19 = w64 (tp_t D + 8)) by (rewrite (K2 19%bv (tpg_cs_hi 19%bv ltac:(split; vm_compute; discriminate))), Rc19; exact R19).
  assert (G21 : getr regs2 21 = w64 (tp_t D + 16)) by (rewrite (K2 21%bv (tpg_cs_hi 21%bv ltac:(split; vm_compute; discriminate))), Rc21; exact R21).
  assert (G20 : getr regs2 20 = w64 (tp_t D + 24)) by (rewrite (K2 20%bv (tpg_cs_hi 20%bv ltac:(split; vm_compute; discriminate))), Rc20; exact R20).
  assert (G23 : getr regs2 23 = w64 (SHADOW_OFF + (tp_t D + 8) / 8))
    by (rewrite (K2 23%bv (tpg_cs_hi 23%bv ltac:(split; vm_compute; discriminate))), Rc23; exact R23).
  assert (G25 : getr regs2 25 = w64 (SHADOW_OFF + (tp_t D + 16) / 8))
    by (rewrite (K2 25%bv (tpg_cs_hi 25%bv ltac:(split; vm_compute; discriminate))), Rc25; exact R25).
  assert (G24 : getr regs2 24 = w64 (SHADOW_OFF + (tp_t D + 24) / 8))
    by (rewrite (K2 24%bv (tpg_cs_hi 24%bv ltac:(split; vm_compute; discriminate))), Rc24; exact R24).
  assert (G26 : getr regs2 26 = w64 (tp_t D / 8)) by (rewrite (K2 26%bv (tpg_cs_hi 26%bv ltac:(split; vm_compute; discriminate))), Rc26; exact R26).
  assert (G27 : getr regs2 27 = w64 (SHADOW_OFF + tp_t D / 8)) by (rewrite (K2 27%bv (tpg_cs_hi 27%bv ltac:(split; vm_compute; discriminate))); exact Rc27).
  replace (BASE + 14288) with (BASE + (TP_OFF + 196)) by (unfold TP_OFF, TP_SLOT; reflexivity).
  (* the model's blocks after the call (the model law at the call: realloc_post_x on every path) *)
  pose proof (WFL _ _ _ _ _ _ HARc) as HWFc.
  destruct (realloc_model_law_x_cf B 0 HU (tp_S D) p (tp_cap0 D) (tp_req D) trq HWFc HRQ0 Hinp Hreqr Hlive2 Hadm)
    as (_ & _ & _ & HMP & _).
  destruct (HMP trc (q, S2) Hpath) as (_ & _ & _ & HMN0 & HMS). cbn [fst snd] in HMN0, HMS.
  destruct HARM as [(Hr0 & EHp2 & Eab2 & Ebl2 & HKP2 & HERR2 & HOOM2 & HREF2) |
                    (Hr4096 & Hr16 & EHp2 & (l1 & l2 & E1 & E2) & HCOPY & HKP2)].
  + (* refused: REFUTED (the batch kit's consumer window: tpg_refute_null) *)
    exfalso. exact (tpg_refute_null D S2 (tp_req D) trq HPRE HK1 Hf0 Hneed HWFc HREF2).
  + (* granted *)
    subst Hp2. rewrite (tp_hp_remove B _ _ _ _ _ _ _ _ _ _ _ _ (tp_b0 D) (proj1 HSIDE) HLamb) in HJ2.
    assert (Hqnn : q <> PNull) by (intros Hq; apply Hqn in Hq; lia).
    destruct (HLsucc Hqnn) as ((HPC2 & HXP2) & _).
    rewrite YGcfRehidePost.acall_post_cf_rh_unfold in HPC2.
    pose proof HPC2 as (HAR'0 & _ & _ & _ & _ & HFRM & _).
    pose proof (conj HAR'0 HXP2) as HAR'.
    destruct (HMS Hqnn) as (l1' & l2' & _ & Ebs2).
    assert (HinqS2 : In (q, tp_req D) (blocks S2))
      by (rewrite Ebs2; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (HPSTK := tpg_pst_after_call W3 mem3 (tp_ly D) (tp_S D) (tp_Hp D) mdc (ms_regs msc) ly' S2 _ W2 mem2
      md' _ (YGcfRehidePost.dead_shadow_new (tp_ly D) (tp_S D) S2) HIMG HARc HAR' HFRM Hceilc
      (fun a Hx => tpg_E_img (tp_ly D) (tp_S D) (tp_Hp D) W3 mem3 mdc ly' S2 _ W2 mem2 md' a HARc HAR'
         (match Hx with
          | or_introl H1 => or_intror (ex_intro _ q (ex_intro _ (tp_req D) (or_intror (conj HinqS2 H1))))
          | or_intror (or_introl H2) => or_intror (ex_intro _ p (ex_intro _ (tp_cap0 D) (or_introl (conj Hinp H2))))
          | or_intror (or_intror H3) => or_introl H3
          end)) (fun a HD => tpg_img_not_dsn _ _ _ a HD)).
    pose proof (tpg_post_of_call D W3 mem3 md3 k ly2 S2 W2 mem2 md2 _ _ HIMG HPRE HJ HK HROD HJ2) as HPOST.
    pose proof (tp_room_live_after B (tp_ly D) (tp_S D) (tp_Hp D) W3 (ms_regs msc) mem3 mdc ch p (tp_req D) trq trc q S2
      HRL HLIVE HPREc Hadm Hr2 Hlive2 Hpath) as HRL2.
    destruct (tpg_side_after_call D W3 mem3 md3 k ly2 S2 W2 mem2 md2 _ _ HIMG HPRE HJ HSIDE HINV HJ2 HPSTK HRL2)
      as (HSIDE2 & HKEPT2).
    pose proof HSIDE2 as (HLG2 & _).
    pose proof (tpg_pos_after_call D (tp_ly D) (tp_Hp D) W3 (ms_regs msc) mem3 mdc ch trq trc q S2 HPRE Hf0 Hneed
      HPREc Hadm (or_intror (ex_intro _ p (conj Hcp (conj Ep (conj Hb0nz (conj Hinp Hpath)))))) Hqnn) as HPOS2.
    assert (Hnew : In (res, tp_req D) (ablocks B ly2 S2))
      by (rewrite E2; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (Hfresh : ~ In (res, tp_req D) (ablocks B (tp_ly D) (tp_S D))).
    { rewrite E1. intros Hin. apply in_app_or in Hin as [Hin | [Heq | Hin]].
      - apply (tpg_fresh_new ly2 S2 (tp_Hp D) W2 mem2 md2 (l1 ++ l2) (res, tp_req D) (proj1 HJ2) Hq2
          ltac:(rewrite E2, app_assoc; reflexivity)). apply in_or_app. left. exact Hin.
      - injection Heq as _ Heq. lia.
      - apply (tpg_fresh_new ly2 S2 (tp_Hp D) W2 mem2 md2 (l1 ++ l2) (res, tp_req D) (proj1 HJ2) Hq2
          ltac:(rewrite E2, app_assoc; reflexivity)). apply in_or_app. right. exact Hin. }
    destruct (tp_grow_blocks B (tp_ly D) (tp_S D) (tp_ly D) (tp_S D) ly2 S2 (tp_b0 D) (tp_cap0 D) res (tp_req D) l1 l2
      eq_refl Hcp Hcreq E1 E2) as (HGR & HBB).
    apply (tpg_tail P Q D W3 mem3 ly2 S2 W2 regs2 mem2 md2 _ _ res PLAW HIMG KFIT (tpg_budget_grow D trq Hneed) HPRE
      Hf0 Hneed HREC HSV KR2 SP2 SH2 G19 G21 G20 G23 G25 G24 G26 G27 Ha0r HPOST HPM2).
    split; [exact Hr4096|]. split; [exact Hr16|].
    split; [exact (tpg_blk_new D ly2 S2 W2 mem2 md2 res HPRE Hneed (proj1 HJ2) Hnew Hfresh HLG2)|].
    split.
    { apply (tpg_bytes_copy W3 W2 mem3 mem2 (tp_b0 D) res (tp_txt D) (Z.min (tp_cap0 D) (tp_req D))
        (tpg_bytes_prefix W3 mem3 (tp_b0 D) (tp_txt D) [0] Hby0)); [|exact HCOPY].
      rewrite Hltxt. unfold tp_req, tp_need in *. lia. }
    split; [exact (tpg_src_off_new D ly2 S2 W2 mem2 md2 res HPRE (proj1 HJ2) Hfr2 Hnew Hfresh HLG2 HKEPT2)|].
    split; [exact HKEPT2|]. split; [exact HGR|]. split; [exact HBB|].
    split; [exact HSIDE2 | exact HPOS2].
Qed.

End g.

Print Assumptions tp_seg_GROW_holds.
