(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module names changed; 382 of its 438 lines of code are new or changed and 458 lines of the source are left out. *)
(* fuzz_preset, lane WalkRtt102.RttT: the IMAGE-GENERIC half of STRETCH T of the walk of round_trip_text on the
   #102 pins - the inlined rendered() between the cuts RT_PJW (entry + 304) and RT_TXE (entry + 388):
     __asan_memset (&t, 0, 32); tx_put (&t, "", 0); tx_value (&t, doc, pretty, 0); if (pretty) tx_put (&t, "\n", 1).
   The statement proved at image A' is Rtt102Cut.v's RTT_SEG_T (lib/A/Prog/Rtt102TA.v); this file holds what does not
   mention an image: the pure model arithmetic of the three tx calls, and the transport of the facts a cut carries
   across one caller-window call and across the memset.
   rule 24: no function proved (kind: segment lemma). The function-level gate is the text owner's, CLEARED for
   round_trip_text (proof-index round_trip_text, EXIT=0):
   the released hits are plain (lib/Prog) and ubsan (lib/U/Prog) only - no asan directory, no lib/A, no lib/B.
   Released plain files are cited for FUNCTIONAL CONTENT only, by name, never as proof.

   INPUTS OF RECORD: Rtt102Cut.v's header (pins A' asan 1be0f53d96cb9d6c, twin bff8519bbe3ea0e4; the kit's texts and
   a Theorem Labs lane's engine set at the batch kit's cut, the batch kit head 7cdbb61b5fa0; listings from
   the pins102 listing head; build route pins102, FACTS 8f3e7e1a07f1, PAU pau-preset-102). This file
   compiles unchanged on the cut (it names no text that changed there).

   THE MODEL. The rendering makes three tx calls whose appended pieces are, in order, "" (0 bytes),
   concat (WriterValue.wvpieces t p 0) and, when pretty, "\n". Their call sizes are PRH_FnCheck.ck_rtt_ns t p =
   [0] ++ TxModel.tv_calls t p 0 ++ (if p then [1] else []) and the text they leave is WriterValue.wdoc t p
   (rtt_t_wdoc). The buffer's capacity after a run of tx_put calls is TxModel.tx_capf, bounded by
   Z.max cap (2 * (len + zsum ns + 1)) (rtt_t_capf_le), so from the empty buffer it is at most
   PRH_FnCheck.TX_req t p (rtt_t_cap_req) - which is what Rtt102Cut.rtt_wblk asks and what makes the live-set and
   request bounds of every call close.

   NUMERALS. LENGTH: 0, 1, 2 (the three call sizes; the doubling of tx_put's grow), 8 / 16 / 24 / 28 / 32 (the
   record's fields, its accessed width, its size), 64 (the shadow granule's application span), 4096, 2 ^ 32 / 2 ^ 47
   / 2 ^ 64. DERIVED: none here - every offset is the image file's. WORD: none. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTreeVis YGcallHull YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos
PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterSpec WriterApp
PjWriteHyp TxModel TvSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnTx PRH_FnWriter PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Rtt102Cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* ================================================================================================= *)
(* ---- 1. THE MODEL: the three calls' sizes, the text they leave, the capacity they reach ---- *)

(* the document the rendering writes: the value's pieces, and a newline when pretty.
   (Plain lib/Prog/RttModel.v wdoc_split states the same equation; content cited, proof not.) *)
Lemma rtt_t_wdoc : forall t p,
  concat (WriterValue.wvpieces t p 0) ++ (if p then [10] else []) = WriterValue.wdoc t p.
Proof.
intros t p. unfold WriterValue.wdoc, WriterValue.wdpieces. rewrite concat_app.
destruct p; cbn [concat]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma rtt_t_zsum_nonneg : forall ns, Forall (fun x => 0 <= x) ns -> 0 <= TxModel.zsum ns.
Proof. intros ns H. induction H as [|x l Hx Hl IH]; cbn [TxModel.zsum]; lia. Qed.

Lemma rtt_t_plen_nonneg : forall P, Forall (fun x => 0 <= x) (TxModel.plen P).
Proof.
intros P. apply Forall_forall. intros y Hy. unfold TxModel.plen in Hy.
apply in_map_iff in Hy as (z & Hz & _). lia.
Qed.

(* the capacity a run of tx_put calls reaches, bounded without unfolding the run *)
Lemma rtt_t_capf_le : forall ns len cap, Forall (fun x => 0 <= x) ns -> 0 <= len ->
  TxModel.tx_capf len cap ns <= Z.max cap (2 * (len + TxModel.zsum ns + 1)).
Proof.
intros ns. induction ns as [|n r IH]; intros len cap HF Hlen; cbn [TxModel.tx_capf TxModel.zsum]; [lia|].
pose proof (Forall_inv HF) as Hn. cbv beta in Hn. pose proof (Forall_inv_tail HF) as Hr.
pose proof (rtt_t_zsum_nonneg r Hr) as Hz.
specialize (IH (len + n) (TxModel.tx_cap1 len cap n) Hr ltac:(lia)).
unfold TxModel.tx_cap1 in IH |- *. destruct (Z.leb_spec (len + n + 1) cap); lia.
Qed.

(* a run of tx_put calls never shrinks the buffer *)
Lemma rtt_t_capf_ge : forall ns len cap, 0 <= cap -> cap <= TxModel.tx_capf len cap ns.
Proof.
intros ns. induction ns as [|n r IH]; intros len cap Hc; cbn [TxModel.tx_capf]; [lia|].
assert (Hc1 : cap <= TxModel.tx_cap1 len cap n)
  by (unfold TxModel.tx_cap1; destruct (Z.leb_spec (len + n + 1) cap); lia).
pose proof (IH (len + n) (TxModel.tx_cap1 len cap n) ltac:(lia)). lia.
Qed.

(* the three calls' sizes are nonnegative *)
Lemma rtt_t_ns_nonneg : forall t p, Forall (fun x => 0 <= x) (ck_rtt_ns t p).
Proof.
intros t p. apply Forall_forall. intros y Hy. unfold ck_rtt_ns in Hy.
apply in_app_or in Hy as [Hy | Hy]; [cbn [In] in Hy; destruct Hy as [<-|[]]; lia|].
apply in_app_or in Hy as [Hy | Hy].
- exact (proj1 (Forall_forall _ _) (rtt_t_plen_nonneg (TxModel.tvp t p 0)) y Hy).
- destruct p; cbn [In] in Hy; [destruct Hy as [<-|[]]; lia | destruct Hy].
Qed.

(* the value's pieces, as a length (lib/Prog/TvSpec.v tvp_concat; content cited) *)
Lemma rtt_t_zsum_tv : forall t p d,
  TxModel.zsum (TxModel.tv_calls t p d) = Z.of_nat (length (concat (WriterValue.wvpieces t p d))).
Proof.
intros t p d. unfold TxModel.tv_calls. rewrite TxModel.zsum_plen, TvSpec.tvp_concat. reflexivity.
Qed.

(* the rendering's total: the three sizes sum to the document's length *)
Lemma rtt_t_txlen : forall t p, ck_tx_len t p = Z.of_nat (length (WriterValue.wdoc t p)).
Proof.
intros t p. rewrite <- (rtt_t_wdoc t p), length_app.
unfold ck_tx_len, ck_rtt_ns. rewrite !TxModel.zsum_app, rtt_t_zsum_tv.
destruct p; cbn [TxModel.zsum length]; lia.
Qed.

(* the capacity the whole rendering reaches is within rendered()'s request *)
Lemma rtt_t_cap_req : forall t p, TxModel.tx_capf 0 0 (ck_rtt_ns t p) <= TX_req t p.
Proof.
intros t p. pose proof (rtt_t_capf_le (ck_rtt_ns t p) 0 0 (rtt_t_ns_nonneg t p) ltac:(lia)) as H.
pose proof (rtt_t_zsum_nonneg _ (rtt_t_ns_nonneg t p)) as Hz.
unfold TX_req, ck_tx_len in *. lia.
Qed.

(* rendered()'s request is one of RQ_rtt's three (zmaxl's second entry) *)
Lemma rtt_t_req_rq : forall t p, TX_req t p <= RQ_rtt t p.
Proof. intros t p. unfold RQ_rtt, zmaxl. cbn [fold_right]. lia. Qed.

(* the reading's live set is nonnegative, so the rtt text's live bound leaves the writer and the rendering room *)
Lemma rtt_t_hpeak_nonneg : forall tr, 0 <= hpeakR tr.
Proof. intros [|e r]; cbn [hpeakR]; lia. Qed.

Lemma rtt_t_live_parse_nonneg {cp : CfParams} : forall tl, 0 <= PRH_FnPj.LIVE_pj_parse tl.
Proof.
intros tl. unfold PRH_FnPj.LIVE_pj_parse.
pose proof (rtt_t_hpeak_nonneg (PRH_FnPj.prhPj_ptrace tl)) as H1.
pose proof (@cf_head_nonneg cp) as H2.
pose proof (Nat2Z.is_nonneg (PjGrammar.calls (PRH_FnPj.prhPj_ptrace tl))) as H3.
assert (0 <= cf_head * (Z.of_nat (PjGrammar.calls (PRH_FnPj.prhPj_ptrace tl)) + 1))
  by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.

(* ---- the model's CAPACITY LIST (PresetReqAt.tx_caps / rcaps, the record blob 379c33e9e482) and the kit's
   tx_capf are the same run: the last capacity the rendering reaches is tx_capf from the empty buffer. RT_CMP's
   HFr event names `last (rcaps t p) 0`, so the cut's not-refused arm states cap by that name. ---- *)
Lemma rtt_t_last_indep : forall (l : list Z) (d d' : Z), l <> [] -> last l d = last l d'.
Proof.
intros l. induction l as [|x l IH]; intros d d' H; [exfalso; exact (H eq_refl)|].
destruct l as [|y l]; [reflexivity|]. cbn [last]. apply IH. discriminate.
Qed.

Lemma rtt_t_caps_last : forall ls n cap, last (PresetReqAt.tx_caps n cap ls) cap = TxModel.tx_capf n cap ls.
Proof.
intros ls. induction ls as [|k r IH]; intros n cap; [reflexivity|].
cbn [PresetReqAt.tx_caps TxModel.tx_capf]. unfold TxModel.tx_cap1.
destruct (Z.ltb_spec cap (n + k + 1)) as [L | L].
- rewrite (proj2 (Z.leb_gt _ _) L).
  replace (2 * (n + k + 1)) with ((n + k + 1) * 2) by lia.
  pose proof (IH (n + k) ((n + k + 1) * 2)) as IH'.
  destruct (PresetReqAt.tx_caps (n + k) ((n + k + 1) * 2) r) as [|c0 cr] eqn:E.
  + cbn [last] in IH' |- *. exact IH'.
  + rewrite <- IH'. transitivity (last (c0 :: cr) cap); [reflexivity|].
    apply rtt_t_last_indep. discriminate.
- rewrite (proj2 (Z.leb_le _ _) L). apply IH.
Qed.

(* the rendering's final capacity, in the model's words. EQKS is the kit's PRH_Supply.v tv_calls_tx_val (blob
   392e316eeb02), taken as an ARGUMENT: that file's Requires reach the red lib/Reusable/YCeh.v on the #102 pins *)
Lemma rtt_t_cap_rcaps : forall t p,
  TxModel.tv_calls t p 0 = PresetReqAt.tx_val p 0 t ->
  last (PresetReqAt.rcaps t p) 0 = TxModel.tx_capf 0 0 (ck_rtt_ns t p).
Proof.
intros t p EQKS. unfold PresetReqAt.rcaps, ck_rtt_ns. rewrite <- EQKS. cbn [app].
apply rtt_t_caps_last.
Qed.

(* the hull of a range at least 64 bytes inside the image is the shadow of image bytes (WalkS10's s10_hull_img,
   FuzzStrdup.v's sd_hull_img; restated here over this file's bounds) *)
Lemma rtt_t_hull_img : forall lo hi a n s, 4096 <= lo -> hi <= 2147483648 ->
  0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ lo <= 8 * (s - SHADOW_OFF) < hi.
Proof.
intros lo hi a n s Blo Bhi Hn Hlo Hhi Hs. unfold shadow_addr in *. unfold SHADOW_OFF in *.
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

(* one read-back byte of the view *)
Lemma rtt_t_val1_of_aview : forall segs0 (H : word -> bool) mem a v, aview segs0 H mem a = Some v ->
  val_mem segs0 (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros segs0 H mem a v E. unfold aview in E.
destruct (mbyte segs0 (mrestrict H mem) a) as [bb|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb.
f_equal. rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

(* ================================================================================================= *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the allocator's laws at the harness head length (the preset instance's cf_head) *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* the hidden head is at least one shadow granule wide (PRH_Base.v prh_head_wide; owner: the cf instance owner, discharged by
   the preset instance where cf_head = 16): a live harness block is never the empty request *)
Hypothesis HW : prh_head_wide.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* MARKED STAND-IN (owned by the kit, the image binding of B; WalkS10's ruling 2026-10-29): the zero-shadow ranges are
   granule-aligned (ARcf gives it by amc_syms / aso_zshadow, YG0f.v:191) *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* the image's bounds (implicit: A' passes YImgTop's IMG_LO / IMG_TOP, B' IMG_LO_B / IMG_TOP_B) *)
Context {IL IT : Z}.
(* the image's shadow is mapped at every ARx state (owner: the cf instance owner; see Rtt102TA.v's header for the discharge) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IL <= a < IT ->
  aview segs (w_H W) mem (shadow_addr a) <> None.

(* ---- a read-only IMAGE LITERAL handed to tx_put (route (a), kept_img): the image's read-only bytes give
   src_rd and prhtx_kept at ANY ARx state, from the read-only view alone (WalkS10's s10_src_img) ---- *)
Lemma rtt_t_src_img : forall ly S Hp W mem md Lam s src,
  4096 <= pa_lo -> pa_hi <= kLowMemEnd - 1 -> pa_lo + 64 <= pa_hi ->
  (forall a, pa_lo <= a < pa_hi -> IL <= a < IT) ->
  ARx ly S Hp W mem md -> arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  kept_img B s (Z.of_nat (length src)) -> (0 < length src)%nat ->
  (forall j, (j < length src)%nat ->
     option_map (fun bb : byte => bv_unsigned bb) (seg_rom segs (Z_to_bv 64 (s + Z.of_nat j))) = Some (nth j src 0)) ->
  src_rd W mem s src /\ PRH_FnTx.prhtx_kept B Lam ly S s (Z.of_nat (length src)).
Proof.
intros ly S Hp W mem md Lam s src BLO BHI BLH BIN HAR HRO HKI Hn Hrom.
pose proof HKI as (Hlo & Hhi & Hro).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof ASAN_CEIL_range as (CR1 & CR2). unfold ASAN_CEIL in CR1, CR2.
split; [|left; right; right; exact HKI].
unfold kLowMemEnd in BHI.
split; [|split; [lia|split; [lia|split; [unfold amem_range, kLowMemEnd; left; lia|split]]]].
- unfold bytes_at. intros j Hj.
  destruct (Hro (s + Z.of_nat j) ltac:(lia)) as (Hr & Hno & Her & _).
  pose proof (HRO _ Hr Hno Her) as E. rewrite (Hrom j Hj) in E.
  exact (rtt_t_val1_of_aview segs (w_H W) mem _ _ E).
- intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hc & Hv)]).
  + destruct Hzs as (qq & mm & Hin & Hq & Hqm).
    pose proof (proj1 (Forall_forall _ _) zs_aligned (qq, mm) Hin) as (Hq8 & Hm8). cbn [fst snd] in Hq8, Hm8.
    pose proof (alx_zshadow segs B ARx LAWS ly S Hp W mem md (qq, mm) HAR ltac:(right; exact Hin)) as Hz.
    cbn [fst snd] in Hz. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    exact (zero_shadow_range (aview segs (w_H W) mem) SHADOW_OFF qq mm Hq8 Hm8 Hz x ltac:(lia)).
  + pose proof (proj1 (Forall_forall _ _) (alx_const_cells segs B ARx LAWS ly S Hp W mem md HAR) _ (Hc ly)) as Hcell.
    unfold cell_holds, z1, c1 in Hcell. cbn [c_at c_w c_val aeval] in Hcell.
    specialize (Hcell 0%nat ltac:(lia)). rewrite Z.add_0_r in Hcell.
    exists v. split; [|unfold saddr_ok; lia].
    unfold shadow_of_addr. unfold shadow_addr in Hcell. rewrite Hcell. f_equal.
    unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r, (Z.mod_small v (2 ^ 8)) by lia. apply Z.mod_small. lia.
- intros Hn0 s0 Hs.
  assert (BHI2 : pa_hi <= 2147483648) by lia.
  assert (HL1 : pa_lo + 64 <= s) by lia.
  assert (HH1 : s + Z.of_nat (length src) + 64 <= pa_hi) by lia.
  destruct (rtt_t_hull_img pa_lo pa_hi s (Z.of_nat (length src)) s0 BLO BHI2 Hn0 HL1 HH1 Hs) as [E Hr].
  rewrite E. exact (img_shadow_vis_x ly S Hp W mem md _ HAR (BIN _ Hr)).
Qed.


(* ---- 2a. small arithmetic over the allocator's sizes ---- *)
Lemma rtt_t_req_pos : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma rtt_t_req_ge : forall z, 0 <= z -> z <= req_size z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.

Lemma rtt_t_aview_present : forall (H : word -> bool) mem a, apresent H mem a -> aview segs H mem a <> None.
Proof. intros H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* an eight-byte value in the view is the word the unwinder reads. (YCem.rdword_of_val_mem states this; that file
   is not cited because its Require closure reaches lib/Reusable/YCeh.v, which does not build on the #102 pins -
   YCeh.v:84-85 vm_computes image A's OLD segment table.) *)
Lemma rtt_t_rdword_of_vm : forall (H : word -> bool) mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v HV Hr.
pose proof (HV 0%nat ltac:(lia)) as M0. pose proof (HV 1%nat ltac:(lia)) as M1.
pose proof (HV 2%nat ltac:(lia)) as M2. pose proof (HV 3%nat ltac:(lia)) as M3.
pose proof (HV 4%nat ltac:(lia)) as M4. pose proof (HV 5%nat ltac:(lia)) as M5.
pose proof (HV 6%nat ltac:(lia)) as M6. pose proof (HV 7%nat ltac:(lia)) as M7.
change (Z.of_nat 0) with 0 in M0. change (Z.of_nat 1) with 1 in M1. change (Z.of_nat 2) with 2 in M2.
change (Z.of_nat 3) with 3 in M3. change (Z.of_nat 4) with 4 in M4. change (Z.of_nat 5) with 5 in M5.
change (Z.of_nat 6) with 6 in M6. change (Z.of_nat 7) with 7 in M7. rewrite Z.add_0_r in M0.
unfold rdword, aview. rewrite M0, M1, M2, M3, M4, M5, M6, M7. cbn [option_map].
f_equal.
assert (BR : forall k, bv_unsigned (Z_to_bv 8 (le_byte v 8 k)) = le_byte v 8 k).
{ intros k. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. unfold le_byte. apply Z.mod_pos_bound. lia. }
rewrite !BR. unfold le_byte. rewrite !(Z.mod_small v) by (cbn; lia).
rewrite !Z.shiftr_div_pow2 by lia. cbn [Z.of_nat Z.mul].
change (2 ^ 0) with 1. rewrite Z.div_1_r.
Z.div_mod_to_equations. lia.
Qed.

(* ---- 2b. the real stack's shadow: every byte of [ly_stk_lo, ly_stk_hi) reads 0 (field 13), so a range there is
   addressable, and its 64-byte hull is visible (YGcallHull.v) ---- *)
Lemma rtt_t_stk_ra : forall ly S Hp W mem md p n,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= p -> p + n <= ly_stk_hi ly ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n.
Proof.
intros ly S Hp W mem md p n HAR Hlo Hhi x Hx.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte segs B ARx LAWS ly S Hp W mem md x HAR ltac:(lia)).
Qed.

Lemma rtt_t_stk_hull : forall ly S Hp W mem md p n,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= p -> p + n <= ly_stk_hi ly ->
  shadow_hull_vis (aview segs (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md p n HAR Hlo Hhi.
exact (stack_hull_vis_x_lo segs B ARx LAWS ly S Hp W mem md p n HAR
  (alx_layout_ok segs B ARx LAWS ly S Hp W mem md HAR) Hlo Hhi).
Qed.

(* ---- 2c. the frame-pointer chain at a call made from round_trip_text's own frame: s0 is the function's entry sp,
   whose two words below it are the saved ra and the caller's s0 (rtt_saved's first two slots) ---- *)
Lemma rtt_t_achain_at : forall ly (rd rd' : reader) sp0 spc ra v ch,
  achain ly rd sp0 v ch -> ly_top ly <= 2 ^ 64 ->
  (forall a, sp0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  rdword rd' (sp0 - 8) = Some ra -> rdword rd' (sp0 - 16) = Some v ->
  4096 <= ra -> YM05.alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> spc + 16 <= sp0 ->
  exists ch1, achain ly rd' spc sp0 ch1.
Proof.
intros ly rd rd' sp0 spc ra v ch Hch Htop Hk H8 H16 Hra Hceil Hal Hsp.
destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, ra, v) :: ch).
  eapply achain_push;
    [exact Hch | exact Htop | exact Hk | exact H8 | exact H16 | exact Hra | exact Hceil | exact Hal | exact Hlt
     | exact Hsp].
- exists []. left. split; [right; left; lia | reflexivity].
Qed.

(* ---- 2d. the buffer moves of a run of tx_put calls compose (S10TxKit.v prhtx_grow_trans, restated) ---- *)
Lemma rtt_t_pairwise_perm : forall (X : Type) (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hs l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [pairwise]; intros H.
- exact H.
- destruct H as [Hx Hl]. split; [|exact (IH Hl)].
  rewrite Forall_forall in Hx |- *. intros z Hz. apply Hx. exact (Permutation_in _ (Permutation_sym P) Hz).
- destruct H as [Hy [Hx Hl]]. inversion Hy as [|u l0 Hyx Hyl]; subst.
  split; [constructor; [apply Hs; exact Hyx | exact Hx] | split; [exact Hyl | exact Hl]].
- exact (IH2 (IH1 H)).
Qed.

Lemma rtt_t_zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.

Lemma rtt_t_grow_trans : forall ly S ly1 S1 ly2 S2 b0 cap0 b1 cap1 b2 cap2,
  PRH_FnTx.prhtx_grow B ly S ly1 S1 b0 cap0 b1 cap1 ->
  PRH_FnTx.prhtx_grow B ly1 S1 ly2 S2 b1 cap1 b2 cap2 ->
  PRH_FnTx.prhtx_grow B ly S ly2 S2 b0 cap0 b2 cap2.
Proof.
intros ly S ly1 S1 ly2 S2 b0 cap0 b1 cap1 b2 cap2 G1 G2.
destruct G1 as [(E0 & E1 & Eb) | (Hlt1 & bl1 & bl2 & Hsh1 & P1)].
- subst b1 cap1. destruct G2 as [(E2 & E3 & Eb2) | (Hlt2 & cl1 & cl2 & Hsh2 & P2)].
  + left. split; [exact E2|]. split; [exact E3|]. rewrite Eb2. exact Eb.
  + right. split; [exact Hlt2|]. exists cl1, cl2. rewrite <- Eb. split; [exact Hsh2 | exact P2].
- destruct G2 as [(E2 & E3 & Eb2) | (Hlt2 & cl1 & cl2 & Hsh2 & P2)].
  + subst b2 cap2. right. split; [exact Hlt1|]. exists bl1, bl2. split; [exact Hsh1|].
    rewrite Eb2. exact P1.
  + right. split; [lia|]. exists bl1, bl2. split; [exact Hsh1|].
    assert (Hc1 : 0 < cap1) by (destruct Hsh1 as [(Hc0 & _) | (Hc0 & _)]; lia).
    destruct Hsh2 as [(Hz & _) | (_ & E2)]; [lia|].
    rewrite E2 in P1.
    assert (Pbc : Permutation (bl1 ++ bl2) (cl1 ++ cl2)).
    { apply (Permutation_cons_app_inv cl1 cl2 (a := (b1, cap1))). apply Permutation_sym. exact P1. }
    eapply Permutation_trans; [exact P2|]. apply perm_skip. apply Permutation_sym. exact Pbc.
Qed.

(* ---- 2e. the record's and the buffer's footprint ---- *)
Lemma rtt_t_fp_cases : forall t b cap a, inFP (PRH_FnTx.prhtx_fp t b cap) a ->
  (t <= a < t + 28) \/ (cap <> 0 /\ b <= a < b + req_size cap).
Proof.
intros t b cap a Hf. unfold PRH_FnTx.prhtx_fp in Hf.
apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [left; exact Hf|].
destruct (Z.eqb_spec cap 0) as [E | E]; [destruct (inFP_nil a Hf)|].
cbn [ablocks_fp map] in Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [|destruct (inFP_nil a Hf)].
right. split; [exact E | exact Hf].
Qed.

Lemma rtt_t_fp_closed : forall t b cap, 0 < t -> (cap <> 0 -> 0 < b) ->
  ~ YI16.sink_open_fp (PRH_FnTx.prhtx_fp t b cap).
Proof.
intros t b cap Ht Hb. apply sink_closed_pos. unfold PRH_FnTx.prhtx_fp.
constructor; [cbn [fst]; exact Ht|].
destruct (Z.eqb_spec cap 0) as [E|E]; [constructor|].
cbn [ablocks_fp map]. constructor; [cbn [fst]; exact (Hb E) | constructor].
Qed.

(* ---- 2f. the read-only view across a journal whose footprint never opens the sink (any world relation R: only the
   journal's image clause is read) ---- *)
Lemma rtt_t_rod_kept : forall {R : world segs -> world segs -> Prop} (STK sp0 : Z) FP ly S Hp W mem md own ly' S' Hp'
  W' mem' md' k,
  (forall a, Exists (in_zr a) (@prh_pst PI) -> ~ in_roP segs pa_relro_lo pa_relro_hi a) ->
  ajournal_xR (SK := SK) segs B (@prh_pst PI) ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') mem').
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HPSTro HJ Hsk H a Hro Hno Her.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite F3; [exact (H a Hro Hno Her) | | exact Hno | exact Her | exact (fun Hp2 => HPSTro a Hp2 Hro) |
  exact (fp_spares_closed FP a Hsk)].
destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
Qed.

(* ---- 2g. the document's blocks at a later state: the STATIC half of prhWriter_tree_vis does not move, its shadow
   half is the harness block's own (field 14 alx_hshadow) and its granule tail is field 15 (alx_blocks_tail).
   Same shape as WalkS10's s10_bvis_lam, for K0Writer's tree_vis instead of K0Tx's prhtx_bvis. ---- *)
Lemma rtt_t_tvis_lam : forall ly S Hp W mem md Lam peak cnt fail ran most own (W0 : world segs) mem0 Dt,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall bk, In bk Dt -> In bk Lam) ->
  PRH_FnWriter.prhWriter_tree_vis W0 mem0 Dt -> PRH_FnWriter.prhWriter_tree_vis W mem Dt.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own W0 mem0 Dt HAR HL HD HV a k Hin.
destruct (HV a k Hin) as (H4096 & Hk0 & Hgr & Hamr & _ & _ & _).
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL (HD (a, k) Hin))
  as (Hk & Hab & Hhp & H16 & _).
pose proof (@cf_head_nonneg cp) as Hh0. pose proof (@cf_head_al cp) as Hh8.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & _ & Hpres & _).
assert (Hrq : req_size (k + cf_head) = k + cf_head).
{ unfold req_size, prh_head_wide in *. destruct (Z.eqb_spec (k + cf_head) 0); lia. }
rewrite Hrq in Hpres.
split; [exact H4096|]. split; [exact Hk0|]. split; [exact Hgr|]. split; [exact Hamr|].
assert (Hga : (a + k + 7) / 8 * 8 <= a + k + 7) by (Z.div_mod_to_equations; lia).
assert (Hgb : a + k <= (a + k + 7) / 8 * 8) by (Z.div_mod_to_equations; lia).
destruct (Z.eq_dec k 0) as [Hk00 | Hkn].
- subst k. assert (Hea : (a + 0 + 7) / 8 * 8 = a) by (Z.div_mod_to_equations; lia).
  rewrite Hea. split; [apply range_addressable_nil; lia|].
  split; [intros Hc; lia|]. intros x Hx. lia.
- destruct (alx_hshadow segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab Hhp) as [Hbs Hhull].
  rewrite Hrq in Hbs, Hhull.
  replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia.
  replace (k + cf_head - cf_head) with k in Hbs, Hhull by lia.
  split; [exact (block_shadow_range (aview segs (w_H W) mem) SHADOW_OFF a k a k Hbs ltac:(lia) ltac:(lia))|].
  split; [intros _; apply Hhull; lia|].
  intros x Hx. destruct (Z_lt_le_dec x (a + k)) as [Hlt | Hge].
  + apply rtt_t_aview_present. exact (proj1 (Hpres x ltac:(lia))).
  + apply (alx_blocks_tail segs B ARx LAWS ly S Hp W mem md _ _ x HAR Hab).
    rewrite Hrq. replace (a - cf_head + (k + cf_head)) with (a + k) by lia. lia.
Qed.

(* ---- 2h. K0Tx's prhtx_bvis of the document's blocks, from K0Writer's tree_vis and the ledger's 16-alignment.
   NO PREMISE: the kit owner re-stated prhtx_bvis's ceiling and range as the GRANULE forms (PRH_FnTx.v, blob 0c2a85e733c9,
   the text owner's ruling on this lane's goal TX-BVIS, 2026-10-29), which is conjunct for conjunct what
   ck_tree_ok's prhWriter_tree_vis = YGcfTreeVis.tree_vis_cf supplies; the 8-aligned base comes from the
   ledger's 16-aligned harness block. ---- *)
Lemma rtt_t_bvis_of_tvis : forall ly S Hp W mem md Lam peak cnt fail ran most own Dt,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall bk, In bk Dt -> In bk Lam) ->
  PRH_FnWriter.prhWriter_tree_vis W mem Dt ->
  Forall (fun b => PRH_FnTx.prhtx_bvis W mem (fst b) (snd b)) Dt.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own Dt HAR HL HD HV.
apply Forall_forall. intros [a k] Hin. cbn [fst snd].
destruct (HV a k Hin) as (H4096 & Hk0 & Hgr & Hamr & HRA & HHU & HPR).
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL (HD (a, k) Hin))
  as (Hk & Hab & Hhp & H16 & _).
assert (Ha8 : a mod 8 = 0) by (Z.div_mod_to_equations; lia).
assert (Hea : a + (k + 7) / 8 * 8 = (a + k + 7) / 8 * 8) by (Z.div_mod_to_equations; lia).
assert (Hea2 : (a + k + 7) / 8 * 8 - a = (k + 7) / 8 * 8) by lia.
rewrite Hea2 in Hamr.
split; [exact H4096|]. split; [exact Ha8|]. split; [lia|]. split; [exact Hgr|].
split; [exact Hamr|]. split; [exact HRA|]. split; [exact HHU|].
intros x Hx. apply HPR. lia.
Qed.

(* ---- 2i. the tree at a later state, from the bytes of its footprint and the presence of the blocks it lies in ---- *)
Lemma rtt_t_node_keep : forall (W : world segs) mem (W' : world segs) mem' lb p tv Dt,
  pj_nodeR segs (rdW W mem) lb p tv Dt ->
  (forall x, pj_footR p Dt x -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  (forall x, pj_footR p Dt x -> writable_at segs (rdW W' mem') x) ->
  pj_nodeR segs (rdW W' mem') lb p tv Dt.
Proof.
intros W mem W' mem' lb p tv Dt HN HA HWr.
eapply (pj_nodeR_frame segs tv (rdW W mem) (rdW W' mem') lb p Dt HN).
intros x Hx. split; [exact (mbyte_of_aview segs (w_H W) (w_H W') mem mem' x (HA x Hx)) | intros _; exact (HWr x Hx)].
Qed.

(* ---- 2k. K0Reader's tree read with a LARGER block predicate (a node whose blocks are the entry's harness blocks is
   a node over the ledger's larger list): pj_nodeR is monotone in lblk, mirroring PRH_Reader.pj_nodeR_frame ---- *)
Lemma rtt_t_memsR_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop)
  l a ka D,
  (forall a k, lblk a k -> lblk' a k) ->
  (forall a u D1, In u (map snd l) -> P a u D1 -> P' a u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D HL HP H; cbn [pj_memsR] in H |- *;
  [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & (Hl & Hc) & H1 & H2). exists x, k, D1, D2.
split; [reflexivity|]. split; [exact Hx|]. split; [split; [exact (HL _ _ Hl) | exact Hc]|].
split; [apply HP; [left; reflexivity | exact H1]|].
apply IH; [exact HL | intros a' u' D' Hu; apply HP; right; exact Hu | exact H2].
Qed.

Lemma rtt_t_nodeR_lblk : forall t m (lblk lblk' : Z -> Z -> Prop) p D, (forall a k, lblk a k -> lblk' a k) ->
  pj_nodeR segs m lblk p t D -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D HL H; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [split; [exact (HL _ _ Hl) | exact Hc] | exact ED].
- destruct Hb as (E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [split; [exact (HL _ _ Hl) | exact Hc] | exact ED].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap | (Hc0 & Hk)]; [left; exact Hcap | right; split; [exact Hc0 | exact (HL _ _ Hk)]]|].
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil _ HP. rewrite Forall_forall in IH.
  exact (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HL HP).
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap | (Hc0 & Hk & Hy)];
    [left; exact Hcap | right; split; [exact Hc0 | split; [exact (HL _ _ Hk) | exact (HL _ _ Hy)]]]|].
  exists Di. split; [exact ED|].
  apply (rtt_t_memsR_lblk _ lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di HL);
    [|exact Hi].
  intros a u D1 Hu HPu. apply in_map_iff in Hu as (nu & Eu & Hnu). rewrite Forall_forall in IH.
  specialize (IH nu Hnu). rewrite Eu in IH. exact (IH m lblk lblk' a D1 HL HPu).
Qed.

(* ---- 2j. the rendering's capacity is at least the first put's grow, 2: the buffer exists at RT_TXE ---- *)
Lemma rtt_t_cap_pos : forall t p, 2 <= TxModel.tx_capf 0 0 (ck_rtt_ns t p).
Proof.
intros t p. unfold ck_rtt_ns. rewrite TxModel.tx_capf_app.
cbn [TxModel.zsum TxModel.tx_capf app].
assert (E : TxModel.tx_cap1 0 0 0 = 2) by reflexivity. rewrite E.
apply rtt_t_capf_ge. lia.
Qed.



End w.
