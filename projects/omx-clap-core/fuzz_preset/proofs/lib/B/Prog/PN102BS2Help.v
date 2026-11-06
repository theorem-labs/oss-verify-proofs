(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994): the SUPPORT LEMMAS of segment S2 of the walk of
   parse_noting (the B' twin of row N10-PNA; cut table lib/B/Prog/PN102BCuts.v; the segment lib/B/Prog/PN102BS2.v): registers across a
   write, the fake frame's geometry at ARcf, the out node's slot at pj_parse's call, the text's bytes, shadow and
   ceiling across a journal (the batch kit's `t0 + len < alloc_ceiling`, pn2_text_ceil, from AR_laws_x field 24), the grammar
   facts (the batch kit: a reading's requests are within RQ_pj_parse, pn2_reqs_le; no refusal when g_ran_out stays 0 under
   g_most, pn2_granted), and (section 4) the live requests and the reader's block sizes after a reading from its
   blocks. No function is proved here.
   rule 24: proves function parse_noting (fuzz_preset, image B') (preparation; proof-index 03:20Z: 0 named / 0 by
   address / 0 released; the rule-24 parse_noting check CONFIRM 03:25Z; PORT of a Theorem Labs lane's image-A' file of the same role,
   a working branch 41f83d5b57f8, at PI_prog_B / prh_img_B). This file: support lemmas of that
   walk only.
   TAKEN BY PATH (each restated under a pn2_ name, at the B' instance):
   - pn2_req, pn2_shadow_out, pn2_hull_sub, pn2_hull_img, pn2_ro_img, pn2_text_shadow (its kept_at arms):
     lib/A/Prog/FuzzStrdup.v sd_req / sd_shadow_out / sd_hull_sub / sd_hull_img / sd_ro_img / sd_src_shadow (this tree);
   - pn2_upd_other / pn2_upd_same, pn2_pw_cross, pn2_garr8_kept, pn2_hd_skip_out: a working branch
     b1bc025047ea lib/A/Prog/Ent102L2AHelp.v l2_getr_upd_other / l2_getr_upd_same, Ent102L6AfLem.v l6f_pw_cross /
     l6f_garr8_kept, Ent102CallA.v ec_hd_skip_out; pn2_mbyte_of_aview and pn2_hblk (prh_ledger_hblock's content, by
     the named projection prh_ledger_blocks): lib/A/Prog/S1Ledger.v prh_mbyte_of_aview / prh_ledger_hblock, restated
     because S1Ledger.v (and FuzzStrdup.v, which imports it) does not compile on this tree (prh_glob gained g_most /
     g_own_ran_out; S1Ledger.v:364).
   B' CHANGES to the A' file: the image bounds are IMG_LO_B / IMG_TOP_B (= PI_prog_B's pa_lo / pa_hi); the image's
   shadow cover is computed at the B' binding (YF0m.TfibSyms; lib/Reusable/YImgShadowCoverCf.v
   img_shadow_vis_cf_at_of_cover, as lib/B/Prog/Padded102B_Inst.v pd_imgvis_of_tfib does); section 4 is new (f97c's
   tparse_noting_specX states the live requests after the call; tpj_parse_specX states only the blocks, from which
   they follow by lib/Spec/PresetReqAtNoMiss.v parse_ok and the reader-event / lsz correspondence pn2_rd_lsz).
   NUMERALS: 8 (a word, a granule), 16 (cf_head at CfParams_preset, checked by change), 32 (the register file),
   56 (struct pj), 64 (a frame's alignment and GrantRo's hull margin), 4096 (a page), 2 ^ 20 / 2 ^ 44 / 2 ^ 64 (shadow
   and word ranges), 2147450880 / 268431360 (SHADOW_OFF and SHADOW_OFF / 8, checked by unfolding). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YG0scf YG0sshcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjReqBound.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
From stdpp Require list_basics.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PN102BCuts PN102BHelp PN102BKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Registers, arithmetic, grammar (no state). *)
Lemma pn2_upd_other : forall regs (rd r : bv 5) v, r <> rd -> getr (regupd regs rd v) r = getr regs r.
Proof. intros regs rd r v H. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact H. Qed.

Lemma pn2_upd_same : forall regs (rd : bv 5) v, bv_eqb rd 0 = false -> getr (regupd regs rd v) rd = v.
Proof. intros regs rd v H. unfold getr. rewrite H. apply regupd_same. Qed.

(* a callee-saved register r is not the register rd when r is not rd's number *)
Lemma pn2_cs_ne : forall r (rd : bv 5), acallee_saved r -> r <> bv_unsigned rd -> Z_to_bv 5 r <> rd.
Proof.
intros r rd Hr Hne E. subst rd. rewrite Z_to_bv_unsigned in Hne. unfold bv_wrap in Hne.
change (bv_modulus 5) with 32 in Hne. unfold acallee_saved in Hr. rewrite Z.mod_small in Hne by lia. lia.
Qed.

Lemma pn2_addi0 : forall x : word, v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma pn2_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.

Lemma pn2_mod64 : forall x y, x mod 4096 = 0 -> y mod 64 = 0 -> (x + y) mod 64 = 0.
Proof.
intros x y Hx Hy. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hy; [|lia].
destruct Hx as (a & ->). destruct Hy as (b & ->).
replace (a * 4096 + b * 64) with ((64 * a + b) * 64) by lia. apply Z_mod_mult.
Qed.

Lemma pn2_mod64_8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
intros x Hx. apply Z.mod_divide in Hx; [|lia]. destruct Hx as (a & ->).
replace (a * 64) with ((8 * a) * 8) by lia. apply Z_mod_mult.
Qed.

(* the shadow byte of an address of a granule-aligned range lies in the range's shadow *)
Lemma pn2_sh_in : forall fa fb x, fa mod 8 = 0 -> fb mod 8 = 0 -> 0 <= fa -> fa <= x < fa + fb ->
  shadow_addr fa <= shadow_of_addr SHADOW_OFF x < shadow_addr fa + fb / 8.
Proof.
intros fa fb x Ha Hb H0 Hx. unfold shadow_addr, shadow_of_addr.
apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
destruct Ha as (q & ->). destruct Hb as (r & ->). rewrite !Z.div_mul by lia.
assert (L1 : q <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (L2 : x / 8 < q + r) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

(* the 64-byte-granule hull of a range inside a 64-aligned range of 64-multiple length lies in its shadow *)
Lemma pn2_hull_in : forall fa fb d n s, fa mod 64 = 0 -> fb mod 64 = 0 -> 0 <= fa -> fa <= d -> 0 < n ->
  d + n <= fa + fb ->
  shadow_addr d / 8 * 8 <= s < shadow_addr (d + n - 1) / 8 * 8 + 8 ->
  shadow_addr fa <= s < shadow_addr fa + fb / 8.
Proof.
intros fa fb d n s Ha Hb H0 Hd Hn Hdn Hs. unfold shadow_addr in *.
apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
destruct Ha as (q & ->). destruct Hb as (r & ->).
replace (q * 64) with ((q * 8) * 8) in * by lia. replace (r * 64) with ((r * 8) * 8) in * by lia.
rewrite !Z.div_mul by lia.
assert (A1 : q * 8 <= d / 8) by (apply Z.div_le_lower_bound; lia).
assert (A2 : (d + n - 1) / 8 < q * 8 + r * 8) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF in *.
assert (A3 : 268431360 + q <= (2147450880 + d / 8) / 8) by (apply Z.div_le_lower_bound; lia).
assert (A4 : (2147450880 + (d + n - 1) / 8) / 8 < 268431360 + q + r) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

Lemma pn2_pw_cross : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) x y,
  YG0f.pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z t IH]; intros l2 x y H Hx Hy; [destruct Hx|].
cbn [app YG0f.pairwise] in H. destruct H as [Hf Ht].
destruct Hx as [<-|Hx].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Ht Hx Hy).
Qed.

Lemma pn2_hd_skip_out : forall (Hp : list Z) p, ~ In p Hp -> hd_skip (cp := CfParams_preset) Hp p = 0.
Proof.
intros Hp p Hn. unfold hd_skip.
destruct (existsb (Z.eqb p) Hp) eqn:E; [|reflexivity].
apply existsb_exists in E as (q & Hq & Eq). apply Z.eqb_eq in Eq. subst q. contradiction.
Qed.

(* an outcome refused among the calls a reading made: the reading fails *)
Lemma pn2_refused_none : forall (sd : list Z -> Z * Z) x ok res tr i,
  PjGrammar.jr_run sd x ok = (res, tr) -> (i < PjGrammar.calls tr)%nat -> nth i ok true = false -> res = None.
Proof.
intros sd x ok res tr i E Hi Hf.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls sd x)) as [Hu | (j & Hj & Hfj & Hu)].
- exfalso. pose proof (PjGrammar.G7_1 sd x ok Hu) as E1. rewrite E in E1. injection E1 as E2 E3.
  assert (Hc : PjGrammar.calls tr = PjGrammar.ncalls sd x) by (rewrite E3; reflexivity).
  rewrite Hc in Hi. rewrite (Hu i Hi) in Hf. discriminate Hf.
- pose proof (PjGrammar.G7_2 sd x ok j Hj Hfj Hu) as (Hn & _). rewrite E in Hn. exact Hn.
Qed.

(* g_ran_out set by the reading (the batch kit's prh_oks, #102's refusal rule): some call it made was refused, so the reading
   fails *)
Lemma pn2_ran_none : forall (sd : list Z -> Z * Z) x ok res tr cnt fail ns most ran',
  PjGrammar.jr_run sd x ok = (res, tr) -> prh_oks ok cnt fail (PjGrammar.calls tr) ns most 0 ran' -> ran' <> 0 ->
  res = None.
Proof.
intros sd x ok res tr cnt fail ns most ran' E (_ & H2 & _) Hr.
destruct H2 as [H2 | (_ & i & Hi & Href & _)]; [lia|].
unfold prh_refused in Href. apply andb_true_iff in Href as (Hf & _). apply negb_true_iff in Hf.
exact (pn2_refused_none sd x ok res tr i E Hi Hf).
Qed.

(* g_ran_out left at 0 while every request was within g_most: no call was refused (the batch kit's prh_granted) *)
Lemma pn2_granted : forall ok cnt fail k ns most ran', prh_oks ok cnt fail k ns most 0 ran' -> ran' = 0 ->
  (forall i, (i < k)%nat -> nth i ns 0 <= most) -> prh_granted ok cnt fail k.
Proof.
intros ok cnt fail k ns most ran' (_ & _ & H3) H0 Hns i Hi Hf.
destruct (Z.eq_dec (cnt + Z.of_nat i) fail) as [E|E]; [exact E|].
assert (Href : prh_refused ok cnt fail i = true).
{ unfold prh_refused. rewrite Hf. cbn [negb andb]. apply negb_true_iff. apply Z.eqb_neq. exact E. }
pose proof (H3 i Hi Href (Hns i Hi)). lia.
Qed.

(* prh_ev_reqs filters with stdpp's base.filter (PRH_Base.v); on a list of events it is List.filter (the laws are
   stdpp.list_basics.list.filter_cons_True / _False, as lane PItemsB's PItems_ledk1.v pik1_reqs_len reads them) *)
Lemma pn2_filter_list : forall (t : list PjGrammar.ev), filter PjGrammar.is_call t = List.filter PjGrammar.is_call t.
Proof.
induction t as [|e r IH]; [reflexivity|].
destruct (PjGrammar.is_call e) eqn:E.
- rewrite list_basics.list.filter_cons_True.
  + cbn [List.filter]. rewrite E, IH. reflexivity.
  + rewrite E. first [exact I | reflexivity].
- rewrite list_basics.list.filter_cons_False.
  + cbn [List.filter]. rewrite E, IH. reflexivity.
  + rewrite E. first [intros H; exact H | intros H; discriminate H | (cbn; intros H; exact H)].
Qed.

(* an entry of prh_ev_reqs is 0 (past the end) or the request of an event of the trace *)
Lemma pn2_nth_reqs : forall (t : list PjGrammar.ev) i,
  nth i (prh_ev_reqs t) 0 = 0 \/ exists e, In e t /\ nth i (prh_ev_reqs t) 0 = PjReqBound.ev_req e.
Proof.
intros t i. unfold prh_ev_reqs. rewrite pn2_filter_list.
destruct (Nat.lt_ge_cases i (length (List.filter PjGrammar.is_call t))) as [Hi|Hi].
- right. exists (nth i (List.filter PjGrammar.is_call t) (PjGrammar.EFree 0)). split.
  + pose proof (nth_In (List.filter PjGrammar.is_call t) (PjGrammar.EFree 0) Hi) as Hn.
    apply List.filter_In in Hn. exact (proj1 Hn).
  + exact (map_nth PjReqBound.ev_req (List.filter PjGrammar.is_call t) (PjGrammar.EFree 0) i).
- left. apply nth_overflow. rewrite length_map. exact Hi.
Qed.

(* the largest request of a trace bounds each of its events' sizes, and is not negative *)
Lemma pn2_maxreq_ge : forall (t : list PjGrammar.ev) e, In e t -> Z.of_nat (PjGrammar.esize e) <= PRH_Charge.prh_maxreq t.
Proof.
intros t. unfold PRH_Charge.prh_maxreq. induction t as [|e0 t IH]; intros e He; [destruct He|].
cbn [map fold_right]. destruct He as [<- | He]; [lia|]. specialize (IH e He). lia.
Qed.
Lemma pn2_maxreq_nonneg : forall (t : list PjGrammar.ev), 0 <= PRH_Charge.prh_maxreq t.
Proof. intros t. unfold PRH_Charge.prh_maxreq. induction t as [|e t IH]; cbn [map fold_right]; lia. Qed.

(* EVERY REQUEST OF A READING IS AT MOST RQ_pj_parse (the largest request of the all-granted reading): up to its
   first refusal a reading's trace is the granted one's, and the refused call asks the granted one's size
   (PjGrammar.G7_1 / G7_3, the agreement of jr_value) *)
Lemma pn2_reqs_le : forall tb ok res tr, PjGrammar.jr_run ReaderRes.jr_strtod tb ok = (res, tr) ->
  forall i, nth i (prh_ev_reqs tr) 0 <= PRH_FnPj.RQ_pj_parse tb.
Proof.
intros tb ok res tr Hjr i.
(* the granted trace prhPj_ptrace tb is at prh_jr_strtod, convertible to ReaderRes.jr_strtod: read it at the latter *)
assert (Hsz : forall e, In e (snd (PjGrammar.jr_run ReaderRes.jr_strtod tb [])) ->
  Z.of_nat (PjGrammar.esize e) <= PRH_FnPj.RQ_pj_parse tb).
{ intros e He. exact (pn2_maxreq_ge (PRH_FnPj.prhPj_ptrace tb) e He). }
assert (Hev : forall e, In e tr -> PjReqBound.ev_req e <= PRH_FnPj.RQ_pj_parse tb).
{ intros e He.
  destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls ReaderRes.jr_strtod tb)) as [Hu | (j & Hj & Hf & Hu)].
  - pose proof (PjGrammar.G7_1 ReaderRes.jr_strtod tb ok Hu) as E. rewrite Hjr in E.
    injection E as _ Et. subst tr. pose proof (PjReqBound.ev_req_le_esize e) as H1. pose proof (Hsz e He). lia.
  - destruct (PjGrammar.G7_3 ReaderRes.jr_strtod tb ok j Hj Hf Hu) as (P & E & rest & Etr & Eg & _ & _).
    rewrite Hjr in Etr. cbn [snd] in Etr. subst tr.
    apply in_app_or in He as [He | [<- | []]].
    + pose proof (PjReqBound.ev_req_le_esize e) as H1.
      assert (Hg : In e (snd (PjGrammar.jr_run ReaderRes.jr_strtod tb []))) by (rewrite Eg; apply in_or_app; left; exact He).
      pose proof (Hsz e Hg). lia.
    + cbn [PjReqBound.ev_req].
      assert (Hg : In E (snd (PjGrammar.jr_run ReaderRes.jr_strtod tb [])))
        by (rewrite Eg; apply in_or_app; right; left; reflexivity).
      exact (Hsz E Hg). }
destruct (pn2_nth_reqs tr i) as [-> | (e & He & ->)].
- unfold PRH_FnPj.RQ_pj_parse. apply pn2_maxreq_nonneg.
- exact (Hev e He).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The B' instance. *)
Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_B rc).
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation RLO := (@pa_relro_lo rc B_prog_listing PA).
#[local] Abbreviation RHI := (@pa_relro_hi rc B_prog_listing PA).
#[local] Abbreviation PST := (@prh_pst prh_img_B).
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).

Lemma pn2_LAWS : AR_laws_x SEGS B ARc (@cf_head CP).
Proof. exact (AR_laws_x_xs (cp := CP) SEGS B (AR_laws_ok_cf (cp := CP) SEGS B)). Qed.

Lemma pn2_mbyte_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  aview SEGS H' m' a = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a = mbyte SEGS (mrestrict H m) a.
Proof.
intros H H' m m' a. unfold aview.
destruct (mbyte SEGS (mrestrict H' m') a) as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
cbn [option_map]; intros E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma pn2_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H' m' (base + i) = aview SEGS H m (base + i)) ->
  garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H' m') base l.
Proof.
intros H H' m m' base l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros q Hq. replace q with 0%nat by lia. rewrite <- (Hv 0%nat ltac:(lia)).
apply pn2_mbyte_of_aview.
replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) by lia.
apply Hk. lia.
Qed.

Lemma pn2_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* the shadow bytes of an application range are outside it *)
Lemma pn2_shadow_out : forall p len x, in_app p len -> p + len <= YM05.alloc_ceiling -> p <= x < p + len ->
  ~ (p <= shadow_of_addr SHADOW_OFF x < p + len).
Proof.
intros p len x Happ Hc Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 <= YM05.alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (YM05.alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

Lemma pn2_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

Lemma pn2_hull_img : forall a n s, 0 < n -> IMG_LO_B + 64 <= a -> a + n + 64 <= IMG_TOP_B ->
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

(* a harness block of the ledger: its allocator block and its hidden head *)
Lemma pn2_hblk : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own a k,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - 16, k + 16) (ablocks B ly S) /\ In (a - 16) Hp.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin.
pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) (a, k) Hin)
  as (Hk & Hab & Hhp & _).
cbn [fst snd] in *. change (@cf_head CfParams_preset) with 16 in *.
split; [exact Hk|]. split; [exact Hab | exact Hhp].
Qed.

(* THE FAKE FRAME at ARcf: 64-aligned, 64-multiple long, application memory below the ceiling, present and not owned,
   off the image, its shadow bytes present (ARx_frames_law, ARx_sep_law, YG0scf.v frame_facts_cf) *)
Lemma pn2_frame_geom : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARc ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\
  in_app (frame_addr ly cid pos) (fs_frame_bytes cid) /\
  4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= YM05.alloc_ceiling /\
  (forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
     apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ in_img SEGS a) /\
  (forall i, 0 <= i < fs_frame_bytes cid / 8 -> apresent (w_H W) mem (shadow_addr (frame_addr ly cid pos) + i)).
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (alx_frames SEGS B ARc pn2_LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Happ & Hfp & Hsp).
destruct (alx_sep SEGS B ARc pn2_LAWS ly S Hp W mem md HAR) as (_ & Hfor).
rewrite Forall_forall in Hfor. destruct (Hfor (cid, pos) Hin) as (Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
destruct (frame_facts_cf B ly S Hp _ cid pos (proj1 (proj1 HAR)) Hin)
  as (_ & _ & _ & _ & FA & _ & _ & O3 & O4 & O5 & _).
split; [unfold frame_addr; unfold page_aligned in FA; apply pn2_mod64; assumption|].
split; [exact O5|]. split; [exact O4|]. split; [exact Happ|]. split; [exact Hlo|]. split; [exact Hhi|].
split.
- intros a Ha. destruct (Hfp a Ha) as (P & O). split; [exact P|]. split; [exact O|].
  exact (frm_img_x SEGS B ARc pn2_LAWS ly S Hp W mem md cid pos a HAR Hin Ha).
- intros i Hi. exact (proj1 (Hsp i Hi)).
Qed.

(* a live block and a live fake frame share no byte *)
Lemma pn2_blk_frame : forall ly S Hp (W : world SEGS) mem md b m cid pos,
  ARc ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  zdisjoint (b, req_size m) (frame_addr ly cid pos, fs_frame_bytes cid).
Proof.
intros ly S Hp W mem md b m cid pos HAR Hb Hf.
destruct (alx_sep SEGS B ARc pn2_LAWS ly S Hp W mem md HAR) as (Hpw & _).
exact (pn2_pw_cross zdisjoint _ _ _ _ Hpw
  (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (b, m) Hb)
  (in_map (fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos) Hf)).
Qed.

(* a harness block of the ledger and a live fake frame share no byte *)
Lemma pn2_lam_frame : forall ly S Hp (W : world SEGS) mem md (Wl : world SEGS) meml Lam peak cnt fail ran most own
  a k cid pos,
  ARc ly S Hp W mem md -> prh_ledger B ly S Hp Wl meml Lam peak cnt fail ran most own -> In (a, k) Lam ->
  In (cid, pos) (frames S) ->
  a + k <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= a - 16.
Proof.
intros ly S Hp W mem md Wl meml Lam peak cnt fail ran most own a k cid pos HAR HL Hin Hf.
destruct (pn2_hblk ly S Hp Wl meml Lam peak cnt fail ran most own a k HL Hin) as (Hk & Hab & _).
pose proof (pn2_blk_frame ly S Hp W mem md _ _ cid pos HAR Hab Hf) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite pn2_req in D by lia. lia.
Qed.

(* a text at its home and a live fake frame share no byte *)
Lemma pn2_home_frame : forall ly S Hp (W : world SEGS) mem md (Wl : world SEGS) meml Lam peak cnt fail ran most own
  text len cid pos,
  ARc ly S Hp W mem md -> prh_ledger B ly S Hp Wl meml Lam peak cnt fail ran most own ->
  prhReader_home B ly S Hp Lam text len -> 0 < len -> In (cid, pos) (frames S) ->
  text + len <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= text.
Proof.
intros ly S Hp W mem md Wl meml Lam peak cnt fail ran most own text len cid pos HAR HL Hh Hlen Hin.
assert (IMGCASE : (forall a, text <= a < text + len -> in_img SEGS a) ->
  text + len <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= text).
{ intros Himg. destruct (Z_le_gt_dec (text + len) (frame_addr ly cid pos)) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (frame_addr ly cid pos + fs_frame_bytes cid) text) as [h'|h']; [right; exact h'|]. exfalso.
  destruct (pn2_frame_geom ly S Hp W mem md cid pos HAR Hin) as (_ & _ & H64 & _).
  destruct (Z_le_gt_dec text (frame_addr ly cid pos)) as [hc|hc].
  - assert (Ha1 : frame_addr ly cid pos <= frame_addr ly cid pos < frame_addr ly cid pos + fs_frame_bytes cid)
      by (clear - H64; lia).
    assert (Ha2 : text <= frame_addr ly cid pos < text + len) by (clear - h hc; lia).
    exact (frm_img_x SEGS B ARc pn2_LAWS ly S Hp W mem md cid pos _ HAR Hin Ha1 (Himg _ Ha2)).
  - assert (Ha1 : frame_addr ly cid pos <= text < frame_addr ly cid pos + fs_frame_bytes cid)
      by (clear - h' hc; lia).
    assert (Ha2 : text <= text < text + len) by (clear - Hlen; lia).
    exact (frm_img_x SEGS B ARc pn2_LAWS ly S Hp W mem md cid pos _ HAR Hin Ha1 (Himg _ Ha2)). }
assert (BLK : forall b m, In (b, m) (ablocks B ly S) -> b <= text -> text + len <= b + req_size m ->
  text + len <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= text).
{ intros b m Hb H1 H2. pose proof (pn2_blk_frame ly S Hp W mem md b m cid pos HAR Hb Hin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia. }
destruct Hh as [[(b & m & Hb & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hb & _ & H1 & H2)].
- destruct (pn2_hblk ly S Hp Wl meml Lam peak cnt fail ran most own b m HL Hb) as (Hm & Hab & _).
  apply (BLK _ _ Hab); [lia|]. rewrite pn2_req by lia. lia.
- apply IMGCASE. intros a Ha. destruct (Hro a Ha) as (Hr & _). exact (pn2_ro_img a Hr).
- apply IMGCASE. intros a Ha. destruct (Hro a Ha) as (Hr & _). exact (pn2_ro_img a Hr).
- apply (BLK _ _ Hb); [lia|]. assert (Hm : 0 <= m) by lia. pose proof (req_size_pos m Hm). lia.
Qed.

(* THE TEXT'S BYTES across a journal (at any budget WS, over any world relation Rj: pj_parse's own journal is at
   wle' segs RZ_cf): a harness block or a live block kept by the block clause (off FP), read-only image bytes by the
   image clause. pn2_text_kept is its instance at wle. *)
Lemma pn2_text_keptR : forall (Rj : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp (W : world SEGS) mem md own
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k WS (Wl : world SEGS) meml Lam peak cnt fail ran most own0 text len,
  ajournal_xwR (SK := SK) SEGS B PST ARc Rj STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k WS ->
  prh_ledger B ly S Hp Wl meml Lam peak cnt fail ran most own0 ->
  ~ YI16.sink_open_fp FP ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  prhReader_home B ly S Hp Lam text len ->
  (forall a, text <= a < text + len -> ~ inFP FP a) ->
  forall a, text <= a < text + len -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a.
Proof.
intros Rj STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k WS Wl meml Lam peak cnt fail ran most own0 text len
  HJ HL Hs0 Hbl Hh Hfp a Ha.
pose proof (ajxR_blk HJ) as G2. pose proof (ajxR_img HJ) as G3.
assert (IMG : in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros Hr Hno Her.
  apply G3; [exact (pn2_ro_img a Hr) | exact Hno | exact Her | exact (fun Hx => pn_pst_not_ro a Hx Hr) |].
  exact (fp_spares_closed FP a Hs0). }
destruct Hh as [[(b & m & Hb & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hb & _ & H1 & H2)].
- destruct (pn2_hblk ly S Hp Wl meml Lam peak cnt fail ran most own0 b m HL Hb) as (Hm & Hab & _).
  replace a with (b - 16 + (a - (b - 16))) by lia.
  apply (G2 (b - 16) (m + 16) (a - (b - 16)) Hab (Hbl _ Hab)); [rewrite pn2_req by lia; lia |].
  replace (b - 16 + (a - (b - 16))) with a by lia. exact (Hfp a Ha).
- destruct (Hro a Ha) as (Hr & Hno & Her). exact (IMG Hr Hno Her).
- destruct (Hro a Ha) as (Hr & Hno & Her & _). exact (IMG Hr Hno Her).
- assert (Hm : 0 <= m) by lia. pose proof (req_size_pos m Hm) as (_ & Hrq).
  replace a with (b + (a - b)) by lia.
  apply (G2 b m (a - b) Hb (Hbl _ Hb)); [lia |].
  replace (b + (a - b)) with a by lia. exact (Hfp a Ha).
Qed.
Lemma pn2_text_kept : forall STK sp0 FP ly S Hp (W : world SEGS) mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k WS
  (Wl : world SEGS) meml Lam peak cnt fail ran most own0 text len,
  ajournal_xw (SK := SK) SEGS B PST ARc STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k WS ->
  prh_ledger B ly S Hp Wl meml Lam peak cnt fail ran most own0 ->
  ~ YI16.sink_open_fp FP ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  prhReader_home B ly S Hp Lam text len ->
  (forall a, text <= a < text + len -> ~ inFP FP a) ->
  forall a, text <= a < text + len -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a.
Proof. exact (pn2_text_keptR (@wle SEGS)). Qed.

(* THE OUT NODE'S SLOT at pj_parse's call: the struct parse_noting's caller placed in a fake frame live at
   parse_noting's entry (ck_out_ok), at a later state of parse_noting's journal (FP the node): the frame is still
   live (frames kept), present (writable), not owned (layout law), below the callee's window; its shadow bytes are
   the frame's, off FP, kept by the frames clause (range_addressable) and present (the 64-byte hull) *)
Lemma pn2_doc_slot : forall STK0 sp0 ly0 S0 Hp0 (W0 : world SEGS) mem0 md0 ly Hp (W : world SEGS) mem md k
  regs0 regs Lam doc STK1,
  ajournal_x (SK := SK) SEGS B PST ARc STK0 sp0 [(doc, doc + 56)] ly0 S0 Hp0 W0 mem0 md0 [] ly S0 Hp W mem md k ->
  ARc ly0 S0 Hp0 W0 mem0 md0 ->
  ck_out_ok B STK0 ly0 S0 W0 regs0 mem0 doc 56 -> doc mod 8 = 0 ->
  sp0 - STK0 <= spZ regs - STK1 ->
  prhPj_slot B STK1 0 ly S0 Lam W regs mem doc.
Proof.
intros STK0 sp0 ly0 S0 Hp0 W0 mem0 md0 ly Hp W mem md k regs0 regs Lam doc STK1 HJ HAR0 (Hfr & Hwd) Hd8 Hwin.
destruct Hfr as (cid & pos & Hin & Hf1 & Hf2).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_frm HJ) as G4.
pose proof (ajx_stk HJ) as Hstk.
destruct (alx_layout SEGS B ARc pn2_LAWS ly0 S0 Hp0 W0 mem0 md0 ly HAR0 Hly) as (_ & Efa & Eown).
pose proof (Efa cid pos) as Efa1.
destruct Hwd as (Hd0 & Hdc & Hamr & Hwr & Hra & Hhv).
destruct (pn2_frame_geom ly0 S0 Hp0 W0 mem0 md0 cid pos HAR0 Hin) as (A64 & B64 & B64' & Happ0 & A4096 & Aceil & _ & _).
destruct (pn2_frame_geom ly S0 Hp W mem md cid pos HAR Hin) as (_ & _ & _ & _ & _ & _ & Fp & Fsh).
rewrite Efa1 in Fp, Fsh.
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
unfold prhPj_slot.
split; [lia|].
split; [right; right; left; exists cid, pos; split; [exact Hin|]; rewrite Efa1; lia|].
split; [split; [exact Hd8|]; intros x Hx; apply (apresent_writable SEGS); exact (proj1 (Fp x ltac:(lia)))|].
split; [exact Hamr|].
split; [intros a Ha; split; [intros Ho; apply Eown in Ho; exact (proj1 (proj2 (Hwr a Ha)) Ho) | lia]|].
split.
- eapply range_addressable_agree; [|exact Hra]. intros x Hx.
  apply (G4 cid pos _ Hin).
  + right. unfold in_zr. cbn [fst snd].
    exact (pn2_sh_in _ _ x (pn2_mod64_8 _ A64) (pn2_mod64_8 _ B64) ltac:(lia) ltac:(lia)).
  + intros Hf. apply (proj1 (inFP_cons _ _ _ _)) in Hf. destruct Hf as [Hf | Hf]; [|exact (inFP_nil _ Hf)].
    apply (pn2_shadow_out _ _ x Happ0 Aceil ltac:(lia)). lia.
- intros s Hs. apply (aview_some_of_apresent SEGS).
  pose proof (pn2_hull_in _ _ doc 56 s A64 B64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hr.
  replace s with (shadow_addr (frame_addr ly0 cid pos) + (s - shadow_addr (frame_addr ly0 cid pos))) by lia.
  apply Fsh. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE TEXT'S SHADOW at any ARcf state, from its home: a live hidden harness block (ARcf's shadow law past the
      head), a registered global (the zero-shadow law, the image hull), an image string under route (a) (the
      const-shadow cells), or a live block whose base is not a hidden head (the shadow law at hd_skip 0). The image
      hull needs the image's shadow mapped: at B' the cover check of the B' generated lists (YF0m's Tfib_zero_shadow /
      Tfib_const_shadow) over [IMG_LO_B, IMG_TOP_B), by vm_compute, with YImgShadowCoverCf.v
      img_shadow_vis_cf_at_of_cover at the binding TB (lib/B/Prog/Padded102B_Inst.v pd_imgvis_of_tfib's proof). *)
Lemma pn2_img_cover_B : img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow IMG_LO_B IMG_TOP_B = true.
Proof. vm_compute. reflexivity. Qed.

(* THE TEXT ENDS BELOW THE CEILING (the batch kit's tpj_parse_specX entry premise `t0 + len < YM05.alloc_ceiling`, PRH_FnPj.v:618),
   from the text's home: a harness block of the ledger (its allocator block (a - 16, k + 16)) or a live block whose base
   is not a hidden head ends at least 8 below the ceiling by AR_laws_x field 24 (YCbqG.v alx_blocks_ceil8,
   ARx_blocks_ceil8_law); a registered read-only global lies in the image, below IMG_TOP_B, far below the ceiling *)
Lemma pn2_text_ceil : forall lyc Sc Hpc (Wc : world SEGS) memc mdc (Wl : world SEGS) meml Lam peak cnt fail ran
  most own s n,
  ARc lyc Sc Hpc Wc memc mdc ->
  prh_ledger B lyc Sc Hpc Wl meml Lam peak cnt fail ran most own ->
  prhReader_home B lyc Sc Hpc Lam s n -> s + n < YM05.alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc memc mdc Wl meml Lam peak cnt fail ran most own s n HAR HL
  [[(b & m & Hin & Hb & Hm) | [(_ & _ & Hhi & _) | (_ & Hhi & _)]] | (b & m & Hin & _ & Hb & Hm)];
  pose proof (@ASAN_CEIL_range rc) as [[HC0 HC1] _]; unfold ASAN_CEIL in HC0, HC1.
- destruct (pn2_hblk lyc Sc Hpc Wl meml Lam peak cnt fail ran most own b m HL Hin) as (Hm0 & Hab & _).
  pose proof (alx_blocks_ceil8 SEGS B ARc pn2_LAWS lyc Sc Hpc Wc memc mdc (b - 16) (m + 16) HAR Hab) as Hc.
  rewrite pn2_req in Hc by lia. lia.
- assert (Hhi' : s + n + 64 <= IMG_TOP_B) by exact Hhi. unfold IMG_TOP_B in Hhi'. lia.
- assert (Hhi' : s + n + 64 <= IMG_TOP_B) by exact Hhi. unfold IMG_TOP_B in Hhi'. lia.
- pose proof (alx_blocks_ceil8 SEGS B ARc pn2_LAWS lyc Sc Hpc Wc memc mdc b m HAR Hin) as Hc.
  unfold req_size in Hc. destruct (Z.eqb_spec m 0); lia.
Qed.

Section TB.
Hypothesis TB : YF0m.TfibSyms B.

Lemma pn2_img_vis : forall ly S Hp (W : world SEGS) mem md a, ARcf (cp := CP) SEGS B ly S Hp W mem md ->
  IMG_LO_B <= a < IMG_TOP_B -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a HAR Ha.
refine (img_shadow_vis_cf_at_of_cover (cp := CP) _ B YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow IMG_LO_B IMG_TOP_B
  pn2_img_cover_B _ _ ly S Hp W mem md a HAR Ha).
- rewrite (YF0m.ts_zsh B TB). apply incl_refl.
- intros ly0. rewrite (YF0m.ts_const B TB). unfold YF0m.Tfib_const. apply incl_appr, incl_appr, incl_refl.
Qed.

Lemma pn2_text_shadow : forall lyc Sc Hpc (Wc : world SEGS) memc mdc (Wl : world SEGS) meml Lam peak cnt fail ran
  most own s n,
  ARc lyc Sc Hpc Wc memc mdc -> 0 < n ->
  prh_ledger B lyc Sc Hpc Wl meml Lam peak cnt fail ran most own ->
  prhReader_home B lyc Sc Hpc Lam s n ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF s n /\ shadow_hull_vis (aview SEGS (w_H Wc) memc) s n.
Proof.
intros lyc Sc Hpc Wc memc mdc Wl meml Lam peak cnt fail ran most own s n HAR Hn HL
  [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & _) | (Hlo & Hhi & Hro)]] | (b & m & Hin & Hnhp & Hb & Hm)].
- destruct (pn2_hblk lyc Sc Hpc Wl meml Lam peak cnt fail ran most own b m HL Hin) as (Hm0 & Hab & Hhp).
  destruct (AR_shadow_law_ok_cf (cp := CP) SEGS B lyc Sc Hpc Wc memc mdc (b - 16) (m + 16) (proj1 HAR) Hab)
    as [Hbs Hhu].
  assert (Hsk : hd_skip (cp := CP) Hpc (b - 16) = 16).
  { unfold hd_skip. replace (existsb (Z.eqb (b - 16)) Hpc) with true; [reflexivity|]. symmetry.
    apply existsb_exists. exists (b - 16). split; [exact Hhp | apply Z.eqb_refl]. }
  rewrite Hsk in Hbs. rewrite pn2_req in Hbs, Hhu by lia.
  split.
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + apply (pn2_hull_sub _ (b - 16) (m + 16) s n Hhu); lia.
- destruct Hzs as (q & m & Hin & Hq & Hqm).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hin)
    as (Z1 & Z2 & Z3 & Z4 & Z5).
  cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
  pose proof (alc_zshadow SEGS B (AR_laws_ok_cf (cp := CP) SEGS B) lyc Sc Hpc Wc memc mdc (q, m) (proj1 HAR)
    ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
  cbn [fst snd] in Hz.
  split.
  + apply (range_addressable_sub (aview SEGS (w_H Wc) memc) SHADOW_OFF q m s n); [|exact Hq|exact Hqm].
    exact (zero_shadow_range (aview SEGS (w_H Wc) memc) SHADOW_OFF q m Z3 Z4 Hz).
  + intros s0 Hs. destruct (pn2_hull_img s n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
    exact (pn2_img_vis lyc Sc Hpc Wc memc mdc _ (proj1 HAR) Hr).
- split.
  + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzg | (v & Hcell & Hv)]).
    * destruct Hzg as (q & m & Hin & Hq & Hqm).
      pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hin)
        as (Z1 & Z2 & Z3 & Z4 & Z5).
      cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
      pose proof (alc_zshadow SEGS B (AR_laws_ok_cf (cp := CP) SEGS B) lyc Sc Hpc Wc memc mdc (q, m) (proj1 HAR)
        ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
      cbn [fst snd] in Hz.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      exact (zero_shadow_range (aview SEGS (w_H Wc) memc) SHADOW_OFF q m Z3 Z4 Hz x ltac:(lia)).
    * pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARc pn2_LAWS lyc Sc Hpc Wc memc mdc HAR) _
        (Hcell lyc)) as Hc.
      unfold cell_holds, z1, c1 in Hc. cbn [c_at c_w c_val aeval] in Hc.
      specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      assert (Hb : YG0f.le_byte v 1 0 = v).
      { unfold YG0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
        replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
        change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
      exists v. split; [|exact Hv].
      change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). rewrite Hc, Hb. reflexivity.
  + intros s0 Hs. destruct (pn2_hull_img s n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
    exact (pn2_img_vis lyc Sc Hpc Wc memc mdc _ (proj1 HAR) Hr).
- assert (Hm0 : 0 < m) by lia.
  destruct (AR_shadow_law_ok_cf (cp := CP) SEGS B lyc Sc Hpc Wc memc mdc b m (proj1 HAR) Hin) as [Hbs Hhu].
  rewrite (pn2_hd_skip_out Hpc b Hnhp) in Hbs. rewrite pn2_req in Hbs, Hhu by lia.
  rewrite Z.add_0_r, Z.sub_0_r in Hbs.
  split; [eapply block_shadow_range; [exact Hbs | lia | lia] | apply (pn2_hull_sub _ b m s n Hhu); lia].
Qed.

(* THE TEXT at a later state of a journal (src_rd): its bytes kept off FP, its range as before, its shadow re-derived
   at the later state from its home there *)
Lemma pn2_src_kept : forall STK sp0 FP ly0 S0 Hp0 (W0 : world SEGS) mem0 md0 own ly S Hp (W : world SEGS) mem md k
  Lam peak cnt fail ran most own0 text tb,
  ajournal_x (SK := SK) SEGS B PST ARc STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran most own0 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own0 ->
  ~ YI16.sink_open_fp FP ->
  (forall x, In x (ablocks B ly0 S0) -> In x (ablocks B ly S)) ->
  prhReader_home B ly0 S0 Hp0 Lam text (Z.of_nat (length tb)) ->
  prhReader_home B ly S Hp Lam text (Z.of_nat (length tb)) ->
  (forall a, text <= a < text + Z.of_nat (length tb) -> ~ inFP FP a) ->
  src_rd W0 mem0 text tb -> src_rd W mem text tb.
Proof.
intros STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k Lam peak cnt fail ran most own0 text tb
  HJ HL0 HL Hs0 Hbl Hh0 Hh Hfp (Hby & H4096 & Hc & Hamr & Hra & Hhv).
pose proof (ajx_ar HJ) as HAR.
split.
{ unfold bytes_at in *. apply (pn2_garr8_kept (w_H W0) (w_H W) mem0 mem text tb); [|exact Hby].
  intros i Hi.
  exact (pn2_text_kept STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k [] W0 mem0 Lam peak cnt fail ran most
    own0 text _ HJ HL0 Hs0 Hbl Hh0 Hfp (text + i) ltac:(lia)). }
split; [exact H4096|]. split; [exact Hc|]. split; [exact Hamr|].
destruct (Z_lt_le_dec 0 (Z.of_nat (length tb))) as [Hn|Hn].
- destruct (pn2_text_shadow ly S Hp W mem md W mem Lam peak cnt fail ran most own0 text _ HAR Hn HL Hh) as (R1 & R2).
  split; [exact R1 | intros _; exact R2].
- split; [apply range_addressable_nil; lia | intros H0; lia].
Qed.
End TB.
End H.

(* ---------------------------------------------------------------------- *)
(* 4. THE LIVE REQUESTS and THE READER'S BLOCK SIZES after a reading (tparse_noting_specX's live-set clause and, in the batch kit,
      its Some-arm rd_blocks clause; tpj_parse_specX states the blocks only). The requests a reader trace leaves live
      are its lsz sizes plus the allocator's head (pn2_rd_lsz: every rd_hev event moves the live list as lsz_ev moves
      the size list, through the head); the model's events of a reading net to those requests when it accepts and to
      nothing when it refuses (PresetReqAtNoMiss.v parse_ok); the room's live requests are the second components of
      the allocator's blocks; and rd_blocks of the reader's trace is the harness blocks' sizes plus HEAD
      (pn2_rd_blocks). *)
#[local] Notation pn2_hd := (fun n : nat => Z.of_nat n + PresetReqAt.HEAD).

Lemma pn2_rm1_map : forall (m : nat) (s : list nat),
  PresetReqAt.rm1 (Z.of_nat m + PresetReqAt.HEAD) (map pn2_hd s) = map pn2_hd (rm1nR m s).
Proof.
intros m s. induction s as [|x r IH]; [reflexivity|].
cbn [map PresetReqAt.rm1 rm1nR].
destruct (Nat.eqb x m) eqn:E.
- apply Nat.eqb_eq in E. subst x. rewrite Z.eqb_refl. reflexivity.
- apply Nat.eqb_neq in E.
  replace (Z.of_nat x + PresetReqAt.HEAD =? Z.of_nat m + PresetReqAt.HEAD) with false
    by (symmetry; apply Z.eqb_neq; lia).
  cbn [map]. rewrite IH. reflexivity.
Qed.

Lemma pn2_hlive_lsz : forall tr s,
  PresetReqAt.hlive_from (map pn2_hd s) (PresetReqAt.rd_hevs tr) = map pn2_hd (fold_left lsz_evR tr s).
Proof.
induction tr as [|e tr IH]; intros s; [reflexivity|].
change (PresetReqAt.rd_hevs (e :: tr)) with (PresetReqAt.rd_hev e ++ PresetReqAt.rd_hevs tr).
rewrite PresetReqAt.hlive_from_app. cbn [fold_left]. rewrite <- IH. f_equal.
destruct e as [n | [|m] n | n | n]; cbn [PresetReqAt.rd_hev lsz_evR PresetReqAt.hlive_from fold_left PresetReqAt.hstep map];
  try reflexivity.
- f_equal. exact (pn2_rm1_map (S m) s).
- exact (pn2_rm1_map n s).
Qed.

Lemma pn2_rd_lsz : forall tr, PresetReqAt.rd_blocks tr = map pn2_hd (lszR tr).
Proof. intros tr. unfold PresetReqAt.rd_blocks, PresetReqAt.hlive, lszR. exact (pn2_hlive_lsz tr []). Qed.

Lemma pn2_live_ablocks : forall (B : asyms) ly S,
  PresetRoom.rs_live (YGcfRoom.room_of_cf S) = map snd (ablocks B ly S).
Proof. intros B ly S. unfold YGcfRoom.room_of_cf, ablocks. cbn [PresetRoom.rs_live]. rewrite map_map. reflexivity. Qed.

(* a refused reading: the blocks are back, and the model's events net to nothing *)
Lemma pn2_live_none : forall (B : asyms) (sm : list Z -> Z * Z) tb ok tr ly S ly' S',
  PjGrammar.jr_run sm tb ok = (None, tr) ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.parse_evs sm tb ok)).
Proof.
intros B sm tb ok tr ly S ly' S' E Hab.
rewrite (proj2 (PresetReqAtNoMiss.parse_ok sm tb ok _)). unfold PresetReqAtNoMiss.pacc. rewrite E. cbn [fst app].
rewrite (pn2_live_ablocks B ly' S'), (pn2_live_ablocks B ly S). apply Permutation_map. exact Hab.
Qed.

(* an accepted reading: the blocks gain the harness blocks D (their allocator blocks, head included), whose sizes are
   the trace's lsz, and the model's events net to the trace's live requests *)
Lemma pn2_live_some : forall (B : asyms) (sm : list Z -> Z * Z) tb ok t tr ly S ly' S'
  (D : list (Z * Z)),
  PjGrammar.jr_run sm tb ok = (Some t, tr) ->
  Permutation (map snd D) (map Z.of_nat (lszR tr)) ->
  Permutation (ablocks B ly' S') (prhPj_hbl (cp := CfParams_preset) D ++ ablocks B ly S) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.parse_evs sm tb ok)).
Proof.
intros B sm tb ok t tr ly S ly' S' D E HD Hab.
rewrite (proj2 (PresetReqAtNoMiss.parse_ok sm tb ok _)). unfold PresetReqAtNoMiss.pacc. rewrite E. cbn [fst].
unfold PresetReqAt.rtr. rewrite E. cbn [snd]. rewrite pn2_rd_lsz.
rewrite (pn2_live_ablocks B ly' S'), (pn2_live_ablocks B ly S).
eapply Permutation_trans; [apply Permutation_map; exact Hab|].
rewrite map_app. apply Permutation_app_tail.
unfold prhPj_hbl. rewrite map_map. cbn [snd]. change (@cf_head CfParams_preset) with 16.
replace (map (fun x : Z * Z => snd x + 16) D) with (map (fun z => z + 16) (map snd D)) by (rewrite map_map; reflexivity).
replace (map pn2_hd (lszR tr)) with (map (fun z => z + 16) (map Z.of_nat (lszR tr)))
  by (rewrite map_map; reflexivity).
apply Permutation_map. exact HD.
Qed.

(* the kit's Some-arm block sizes: the harness blocks' sizes plus the head are the reader's own rd_blocks (CFHEAD-16:
   at cf_head = HEAD), from pj_parse's `Permutation (map snd D) (map Z.of_nat (lszR tr))` *)
Lemma pn2_rd_blocks : forall (sm : list Z -> Z * Z) tb ok res tr (D : list (Z * Z)) (h : Z),
  PjGrammar.jr_run sm tb ok = (res, tr) ->
  Permutation (map snd D) (map Z.of_nat (lszR tr)) -> h = PresetReqAt.HEAD ->
  Permutation (map (fun b => snd b + h) D) (PresetReqAt.rd_blocks (PresetReqAt.rtr sm ok tb)).
Proof.
intros sm tb ok res tr D h E HD ->.
unfold PresetReqAt.rtr. rewrite E. cbn [snd]. rewrite pn2_rd_lsz.
replace (map (fun b : Z * Z => snd b + PresetReqAt.HEAD) D) with (map (fun z => z + PresetReqAt.HEAD) (map snd D))
  by (rewrite map_map; reflexivity).
replace (map pn2_hd (lszR tr)) with (map (fun z => z + PresetReqAt.HEAD) (map Z.of_nat (lszR tr)))
  by (rewrite map_map; reflexivity).
apply Permutation_map. exact HD.
Qed.
