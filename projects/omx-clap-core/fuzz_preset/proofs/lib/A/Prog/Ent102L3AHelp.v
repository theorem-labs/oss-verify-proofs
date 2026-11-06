(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L3AHelp.v, with its module paths changed; 169 of its 650 lines of code are new or changed and 148 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, PIN sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): the SUPPORT
   LEMMAS of segment L3 of LLVMFuzzerTestOneInput (entry 0x815e0), listing +0x178 .. +0x1b8, for the segment proof
   lib/A/Prog/Ent102L3A.v. No function is proved here: the call rule of a callee TEXT at this body's call sites, the
   caller's frame / document / payload across a call, and pure list / byte facts.
   STATEMENT read: lib/A/Ent102CutsA.v (ec_ARx, ec_invR, ec_journal_rebaseR, ec_journal_unbaseR, ec_inv_wk_growR,
   ec_frame, ec_saved, ec_own, ec_doc_state, ec_doc, ec_pre, ec_frame_shadow, EC_FRAME_BYTES, EC_SAVE, LLVMF_FS_CLASS,
   LLVMF_STK).
   THE FREE MOVE (fuzz_preset #102, Step 2): segment L3 runs after check_no_overread, the first callee that frees a
   live block, so its cuts carry ec_invR at WLE' = YA0nH.wle' segs RZ_cf and its lane is SRrG at WLE' (SRr' segs
   RZ_cf). Every journal of the call rule and of the call site below is at WLE' (YCbqG.ajournal_xR / ajournal_xwR); a
   plain callee (post at wle) is lifted into it by YA0nH.SRr_SRr' and YCbqG.apost_base_x_R_lift; a run of plain steps
   (SRr) by l3h_lift.
   LISTING: lib/A/Listing_prog.v (blob 1ab147923c5d) through the PAListing PL_102_A of lib/A/Ent102PLA.v (blob
   a55fa7414ddf); lib/A/PAImg_prog.v is not loaded, no vm_compute on pa_val / pa_sigma.
   THE KIT TEXTS: lib/A/PRH_Base.v (fpre, fpostm, fpostFm, prh_ledger and its named projections; S1Ledger.v's
   prh_ledger_hblock), lib/A/PRH_Reader.v (pj_nodeR_frame, pj_zeroR_frame, pj_fdR), lib/A/PRH_FnCheck.v (ck_obj_home,
   ck_tree_ok), lib/A/PRH_FnEx.v (prhex_inblk).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L3 (reuse search: proof-index LLVMFuzzerTestOneInput
   exit=0, seg_L3_A / seg_L3_stmt / the segment addresses: no proof anywhere,
   the lane's internal file rule24-LL3.txt; NEW walk on the #102 pins). This file: support lemmas of
   that segment only.
   USED FROM THE SHARED FILES (Required, not restated): lib/A/Prog/Ent102L6AfLem.v (blob b1539d7c1884: l6f_LAWS,
   l6f_geom, l6f_img_bounds, l6f_slot_img, l6f_garr8_kept, l6f_shadow_zero, l6f_rd64_kept, l6f_land_neg32,
   l6f_nodup_pw) and lib/A/Prog/Ent102CallA.v (blob ee3e7a0cd978: ec_chain_at, ec_inv_ledgerR).
   TAKEN BY PATH (each restated under an l3h_ name):
   - l3h_call / l3h_callF / l3h_shadow_off / l3h_keep: lib/A/Prog/Ent102L2AHelp.v l2_call / l2_callF /
     l2_shadow_off / l2_keep (blob 02a40d4f6b38: Ent102L2AHelp.v (sha256 315d8bdd524b; internal record));
   - l3h_pw_head / l3h_nodup_app / l3h_fk_trans and the payload argument of l3h_inblk: lib/B/Prog/EntS3B.v
     es3_pw_head / es3_nodup_app / es3_fk_trans / es3_pay_not_hd (as in EntS3B.v (sha256 c51e7f77f4c2; internal record)), over this interface.
   NUMERALS: 144 / 128 / 120 / 104 / 88 / 56 / 32 / 16 / 8 are LENGTHs (EC_SAVE + 16, the frame, its flag-pointer slot,
   the saved block, the doc's end, struct pj, the doc's offset and the frame alignment, the shadow bytes, the word);
   2 ^ 26 / 2 ^ 40 / 2 ^ 47 / 2 ^ 62 / 2 ^ 64 / 4096 and the ASan band constants are the engine's range facts. No
   ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive YGcfTreeVis YO0f YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnEx PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102L6AfLem Ent102CallA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Pure facts. *)
(* the float registers fs0-fs11 kept, transitively *)
Lemma l3h_fk_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma l3h_pw_nodup : forall {X} (R : X -> X -> Prop) l,
  YG0f.pairwise R l -> (forall x, In x l -> ~ R x x) -> List.NoDup l.
Proof.
intros X R l. induction l as [|x t IH]; intros Hp Hirr; [constructor|]. destruct Hp as [Hf Hp]. constructor.
- intros Hin. apply (Hirr x (or_introl eq_refl)). exact (proj1 (Forall_forall _ _) Hf x Hin).
- apply IH; [exact Hp | intros y Hy; apply Hirr; right; exact Hy].
Qed.
Lemma l3h_nodup_map_inj : forall {X Y} (f : X -> Y) l x y,
  List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
intros X Y f l. induction l as [|z t IH]; intros x y Hnd Hx Hy Hf; [destruct Hx|].
cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hni Hnd'].
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- reflexivity.
- exfalso. apply Hni. rewrite Hf. apply in_map. exact Hy.
- exfalso. apply Hni. rewrite <- Hf. apply in_map. exact Hx.
- apply IH; assumption.
Qed.
Lemma l3h_pw_in2 : forall {X} (R : X -> X -> Prop) l a b,
  YG0f.pairwise R l -> In a l -> In b l -> a <> b -> R a b \/ R b a.
Proof.
intros X R l. induction l as [|z t IH]; intros a b P Ha Hb Ne; [destruct Ha|]. destruct P as [F P].
destruct Ha as [<-|Ha]; destruct Hb as [<-|Hb].
- exfalso. apply Ne. reflexivity.
- left. exact (proj1 (Forall_forall _ _) F b Hb).
- right. exact (proj1 (Forall_forall _ _) F a Ha).
- apply IH; assumption.
Qed.
(* two blocks of one block list that start at the same address are the same block *)
Lemma l3h_pw_head : forall l x y,
  YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> In x l -> In y l ->
  fst x = fst y -> (forall b, In b l -> 0 <= snd b) -> x = y.
Proof.
intros l x y Hp Hx Hy Hf Hall.
pose proof (Hall x Hx) as Hx0. pose proof (Hall y Hy) as Hy0.
assert (Hr : forall b : Z * Z, 0 <= snd b -> 0 < req_size (snd b)).
{ intros b Hb. unfold req_size. destruct (Z.eqb_spec (snd b) 0); lia. }
assert (Hnd : List.NoDup (map (fun b => (fst b, req_size (snd b))) l)).
{ apply (l3h_pw_nodup zdisjoint _ Hp). intros z Hz Hd. apply in_map_iff in Hz as (b & <- & Hb).
  pose proof (Hr b (Hall b Hb)) as Rb.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
destruct (Z.eq_dec (req_size (snd x)) (req_size (snd y))) as [Er|Ner].
- apply (l3h_nodup_map_inj (fun b => (fst b, req_size (snd b))) l x y Hnd Hx Hy). cbn beta. rewrite Hf, Er.
  reflexivity.
- exfalso. pose proof (Hr x Hx0) as Rx. pose proof (Hr y Hy0) as Ry.
  assert (Hne : (fst x, req_size (snd x)) <> (fst y, req_size (snd y))) by (intros E; injection E as _ E2; exact (Ner E2)).
  destruct (l3h_pw_in2 zdisjoint _ _ _ Hp (in_map (fun b => (fst b, req_size (snd b))) l x Hx)
    (in_map (fun b => (fst b, req_size (snd b))) l y Hy) Hne) as [Hd|Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; rewrite Hf in Hd; lia.
Qed.
Lemma l3h_nodup_app : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|].
cbn [app] in Hnd. apply NoDup_cons_iff in Hnd as [Hni Hnd].
destruct H1 as [<-|H1]; [apply Hni; apply in_or_app; right; exact H2 | exact (IH l2 x Hnd H1 H2)].
Qed.

(* a zero byte array names zero at every width inside it *)
Lemma l3h_lebyte0 : forall w k, YO0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity. Qed.

(* the frame's shadow bytes lie off the frame *)
Section G. Context {rc : YM05.RunCeil}.
Lemma l3h_shadow_off : forall fk, in_app fk EC_FRAME_BYTES -> 4096 <= fk ->
  shadow_addr fk + 16 <= fk \/ fk + EC_FRAME_BYTES <= shadow_addr fk.
Proof.
intros fk Gapp G4096. pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hq0 : 0 <= fk / 8) by (apply Z.div_pos; lia).
assert (Hq8 : 8 * (fk / 8) <= fk) by (apply Z.mul_div_le; lia).
assert (Esh : shadow_addr fk = SHADOW_OFF + fk / 8) by reflexivity.
rewrite Esh. unfold EC_FRAME_BYTES in *.
destruct Gapp as (_ & [Hlow | (Hhigh & _)]); [right | left];
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia.
Qed.
End G.

(* ---------------------------------------------------------------------- *)
(* 4. THE CALL RULE: a callee's TEXT applied at its entry, from a caller state its journal describes (afn_pre_x_atR
      builds the callee's pre, the text runs to its apost_base_x / apost_base_xFR, ajournal_x_subR composes the two
      journals), all at WLE' (the cut file's world relation after a free). *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* the world relation after a free (lib/A/Ent102CutsA.v's WLE') *)
#[local] Notation WLE' := (wle' segs (@YGcfRehidePost.RZ_cf rc)).

(* a run of plain steps (SRr, at wle) inside a lane at WLE' *)
Lemma l3h_lift : forall (W : world segs) c (R : world segs -> config -> Prop),
  SRr segs W c (fun W' c' => SRrG segs WLE' W' c' R) -> SRrG segs WLE' W c R.
Proof.
intros W c R H.
eapply (SRrG_bind segs WLE' (wle'_trans segs _)); [exact (SRr_SRr' segs (@YGcfRehidePost.RZ_cf rc) W c _ H)|].
intros W' c' _ HR. exact HR.
Qed.

Lemma l3h_call : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  STK1 FP1 (o : Z) ch (f : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xR (SK := SK) segs B PST ARx WLE' STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRr segs W (cfg_at segs f regs mem md)
       (apost_base_x (SK := SK) segs B PST ARx STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1, WLE' W W2 ->
     ajournal_xR (SK := SK) segs B PST ARx WLE' STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     ajournal_xR (SK := SK) segs B PST ARx WLE' STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG segs WLE' W2 (mkCfg (@YK11.mkst fx regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRrG segs WLE' W (cfg_at segs f regs mem md) R.
Proof.
intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k STK1 FP1 o ch f Q R
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch Hcallee HF HK.
eapply (SRrG_bind segs WLE' (wle'_trans segs _)).
{ apply (SRr_SRr' segs (@YGcfRehidePost.RZ_cf rc)). apply Hcallee.
  exact (afn_pre_x_atR segs B PST ARx WLE' STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k regs STK1 o ch
    HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch). }
intros W2 c2 Hle HP0.
apply (apost_base_x_R_lift segs B PST ARx WLE' (wle_wle' segs _)) in HP0.
destruct HP0 as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
rewrite Hsp in HJ1.
apply (HK W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle); [|exact HJ1 | exact HP | exact HQ].
change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARx LAWS segs_low WLE' (wle'_trans segs _));
  [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

Lemma l3h_callF : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  STK1 FP1 (o : Z) ch (f : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xR (SK := SK) segs B PST ARx WLE' STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRr' segs (@YGcfRehidePost.RZ_cf rc) W (cfg_at segs f regs mem md)
       (apost_base_xFR (SK := SK) segs B PST ARx WLE' STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (fx' : YK11.FPState) (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1, WLE' W W2 ->
     YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' ->
     ajournal_xR (SK := SK) segs B PST ARx WLE' STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     ajournal_xR (SK := SK) segs B PST ARx WLE' STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG segs WLE' W2 (mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRrG segs WLE' W (cfg_at segs f regs mem md) R.
Proof.
intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k STK1 FP1 o ch f Q R
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch Hcallee HF HK.
eapply (SRrG_bind segs WLE' (wle'_trans segs _)).
{ apply Hcallee.
  exact (afn_pre_x_atR segs B PST ARx WLE' STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k regs STK1 o ch
    HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch). }
intros W2 c2 Hle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HP & HQ).
rewrite Hsp in HJ1.
apply (HK fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HFZ HFK); [|exact HJ1 | exact HP | exact HQ].
change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARx LAWS segs_low WLE' (wle'_trans segs _));
  [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End C.

(* ---------------------------------------------------------------------- *)
(* 5. THE CALLER'S FRAME ACROSS A CALL: the saved block (above the callee's sp), the fake frame's flag word and its
      sixteen shadow bytes are kept by the callee's journal, so ec_own and ec_frame hold after the call. The journals
      are at any world relation Rel: no conjunct read here is the world conjunct. *)
Section K. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {SK : YI16.sink_head}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable PST : list (Z * Z).
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).

Lemma l3h_keep : forall (Rel : world SEGS -> world SEGS -> Prop) (E : ecx (L := A_prog_listing) (PA := PA)) fk ly S Hp
  (W : world SEGS) mem md own k WSj STK1 A FP1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  ajournal_xwR (SK := SK) SEGS B PST ARc Rel LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WSj ->
  frames (e_S E) = [] ->
  ec_own fk ly W mem own -> ec_frame E fk W mem ->
  ajournal_xR (SK := SK) SEGS B PST ARc Rel STK1 A FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  A <= e_sp0 E - EC_SAVE ->
  (forall a, inFP FP1 a -> fk <= a < fk + EC_FRAME_BYTES - 8) ->
  ec_own fk ly2 W2 mem2 own /\ ec_frame E fk W2 mem2.
Proof.
intros Rel E fk ly S Hp W mem md own k WSj STK1 A FP1 ly2 S2 Hp2 W2 mem2 md2 k1 HJ Hfr0 HOWN HFRM HJ1 HA HFP.
destruct HOWN as (pos & Hown & Hfkeq & Hfk0 & Hflagw).
destruct HFRM as (Hsaved & Hshv & Hal32).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ1 as (HAR2 & Hly1 & _ & _ & _ & _ & _ & _ & G1 & _ & _ & G4 & _).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, Hfr0, Hown; left; reflexivity).
destruct HAR as (HARcf & _).
destruct (l6f_geom B ly S Hp W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & Gapp & Gfr & Gsh).
assert (HFB : fs_frame_bytes LLVMF_FS_CLASS = 128) by (vm_compute; reflexivity).
assert (HFB8 : fs_frame_bytes LLVMF_FS_CLASS / 8 = 16) by (vm_compute; reflexivity).
assert (EF : ly_F ly2 = ly_F ly) by (destruct Hly1 as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (Efa : frame_addr ly2 LLVMF_FS_CLASS pos = frame_addr ly LLVMF_FS_CLASS pos)
  by (unfold frame_addr; rewrite EF; reflexivity).
assert (Efl : flag_addr ly2 LLVMF_FS_CLASS pos = flag_addr ly LLVMF_FS_CLASS pos)
  by (unfold flag_addr; rewrite EF; reflexivity).
pose proof (l3h_shadow_off fk Gapp G4096) as Hsep.
unfold EC_FRAME_BYTES, EC_SAVE, LLVMF_STK in *.
assert (KF : forall a, fk <= a < fk + 128 -> ~ inFP FP1 a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. apply (G4 LLVMF_FS_CLASS pos a Hin); [|exact Hn].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq, HFB. lia. }
assert (KS : forall i, 0 <= i < 16 ->
  aview SEGS (w_H W2) mem2 (shadow_addr fk + i) = aview SEGS (w_H W) mem (shadow_addr fk + i)).
{ intros i Hi. apply (G4 LLVMF_FS_CLASS pos _ Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite <- Hfkeq, HFB8. lia.
  - intros Hf. apply HFP in Hf. lia. }
assert (KT : forall a, e_sp0 E - 104 <= a < e_sp0 E -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply G1; [lia | lia]. }
split.
- exists pos. split; [exact Hown|]. split; [rewrite Efa; exact Hfkeq|]. split; [exact Hfk0|].
  rewrite Efl. unfold EC_FRAME_BYTES. apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hflagw].
  intros i Hi. apply KF; [clear - Hi; lia|]. intros Hf. apply HFP in Hf. clear - Hf Hi. lia.
- split; [|split; [|exact Hal32]].
  + unfold ec_saved in *.
    destruct Hsaved as (S1 & S2' & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
    repeat split; (apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [intros i Hi; apply KT; lia | assumption]).
  + apply (l6f_garr8_kept (w_H W) (w_H W2) mem mem2); [|exact Hshv].
    intros i Hi. change (length ec_frame_shadow) with 16%nat in Hi. apply KS. lia.
Qed.
End K.

(* ---------------------------------------------------------------------- *)
(* 7. THE LANE'S STATE ACROSS A CALL: the call rule at a call site of this body, the cut's invariant (ec_invR at WLE'),
      frame and document after a callee with an empty footprint that keeps the blocks and the ledger, the document's
      home and the payload as check_as_written reads them. *)
Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
#[local] Notation ECX := (@ecx rc A_prog_listing PA).
(* the world relation after a free (lib/A/Ent102CutsA.v's WLE'): segment L3's cuts carry ec_invR at it *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).
#[local] Notation INV := (ec_invR (fx := fx) (cp := cp) (PI := PI) (RL := RL) (L := A_prog_listing) (PA := PA)
  B SK EC_RA EC_EMPTY EC_SIO WLE').
#[local] Notation IMG := (ec_img (L := A_prog_listing) (PA := PA) B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO
  EC_SIO_IMG).

(* the materialization of the model keeps the invariant *)
Lemma l3h_inv_mat : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk X,
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  INV E fk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) own Lam peak cnt ran k os_c i_c wk.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk X ((WSj & HJ & HWB) & HR). split; [|exact HR].
(* the cut file's one no-call step (Ent102CutsA.v ec_inv_wk_growR) at the same bound *)
exact (ec_inv_wk_growR (cp := cp) (PI := PI) (L := A_prog_listing) (PA := PA) B SK WLE' (l6f_LAWS B)
  E own ly S Hp W mem md k WSj wk wk X HJ HWB (Nat.le_refl wk)).
Qed.

(* a wider spent budget keeps the invariant (cut_pno's ec_wk_pno to cut_caw's ec_wk_caw: check_as_written spends
   prh_wk F_check_as_written) *)
Lemma l3h_inv_wk : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk wk',
  (wk <= wk')%nat ->
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk'.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk wk' Hle ((WSj & HJ & HWB) & HR).
split; [|exact HR]. exists WSj. split; [exact HJ|]. unfold YCbqGwild.wbudget in *. lia.
Qed.

(* the stack geometry of a cut: sp0, A = (sp0 - 128) & -32 *)
Lemma l3h_geo : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk,
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  YM05.alloc_ceiling + LLVMF_STK <= e_sp0 E <= 2 ^ 47 /\ e_sp0 E mod 16 = 0 /\
  e_sp0 E - 144 <= e_A E <= e_sp0 E - 128 /\ e_A E mod 32 = 0.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk HI.
destruct HI as ((WSj & HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : LLVMF_STK = 32768) by reflexivity.
assert (EA : e_A E = (e_sp0 E - 128) / 32 * 32).
{ unfold e_A, ec_A, EC_SAVE. apply l6f_land_neg32. pose proof YCbq.asan_consts as (C1 & _). lia. }
split; [lia|]. split; [exact Hal16|].
split.
- rewrite EA.
  pose proof (Z.div_mod (e_sp0 E - 128) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (e_sp0 E - 128) 32 ltac:(lia)) as D2. lia.
- rewrite EA. apply Z.mod_mul. lia.
Qed.

(* THE CALL SITE: a text in the plain m-form (its post at wle, lifted into WLE' by l3h_call), called at sp = A with
   s0 = sp0 and ra the listing slot BASE + r; the lane and every journal at WLE' *)
Lemma l3h_site : forall (fy : YK11.FPState) (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k
  os_c i_c wk
  (regsc : bvmap 5 word) (r STK1 f : Z)
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world SEGS -> config -> Prop),
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ec_frame E fk W mem ->
  getr regsc 2 = w64 (e_A E) -> getr regsc 8 = w64 (e_sp0 E) ->
  getr regsc 3 = getr (e_regs E) 3 -> getr regsc 4 = getr (e_regs E) 4 ->
  (* FRM0-ENTRY (fpre's last conjunct, PRH_Base.v (sha256 da55cb740765; internal record)): the rounding mode is 0 at the call; ec_at gives it *)
  YK0o.frm_zero (@YK11.fp_csr fy) ->
  getr regsc 1 = Z_to_bv 64 (BASE + r) -> 0 <= r < 2 ^ 40 -> r mod 2 = 0 ->
  plookup (@pl_tpi _ PL_102_A) r <> None ->
  0 <= STK1 -> STK1 + 144 <= LLVMF_STK ->
  (forall ch, fpre B ARc STK1 ly S Hp W regsc mem md ch ->
     SRr SEGS W (cfg_at (fx := fy) SEGS f regsc mem md)
       (fpostm (fx := fy) B ARc SK STK1 [] regsc ly S Hp W mem md Q)) ->
  (forall (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2 k1, WLE' W W2 ->
     (exists WS2, ajournal_xwR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E)
       (e_mem E) (e_md E) own ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS2 /\ YCbqGwild.wbudget [] wk WS2) ->
     ajournal_xR (SK := SK) SEGS B PST ARc WLE' STK1 (e_sp0 E + (e_A E - e_sp0 E)) [] ly S Hp W mem md [] ly2 S2 Hp2
       W2 mem2 md2 k1 ->
     aregs_preserved regsc regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
     SRrG SEGS WLE' W2 (mkCfg (@YK11.mkst fy regs2 (Z_to_bv 64 (BASE + r)) mem2 (YK11.seg_rom SEGS)) md2) R) ->
  SRrG SEGS WLE' W (mkCfg (@YK11.mkst fy regsc (Z_to_bv 64 f) mem (YK11.seg_rom SEGS)) md) R.
Proof.
intros fy E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk regsc r STK1 f Q R HI HF R2 R8 R3 R4 HFZy R1 Hr Hr2 Hpl
  Hs0 Hs1 Hcallee HK.
destruct (l3h_geo E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk HI) as (Rsp & Hal16 & HAb & HA32).
pose proof HI as ((WSj & HJ & HWB) & _ & _ & _ & HRO & _ & _ & _ & HPRE & _).
(* the budget-free call rule under the cut file's rebase / unbase at WLE' (Ent102CutsA.v ec_journal_rebaseR /
   _unbaseR) *)
pose proof (ec_journal_rebaseR (cp := cp) (PI := PI) (L := A_prog_listing) (PA := PA) B SK WLE' _ _ _ _ _ _ _ _ _ _ HJ)
  as HJr.
pose proof HPRE as (HPREX & HS0E & _).
pose proof HPREX as (_ & _ & Hra40 & Hgp0 & Htp0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HF as (Hsaved & _ & _). pose proof Hsaved as (Sra & S8 & _).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
assert (WS : LLVMF_STK = 32768) by reflexivity.
assert (HSPC : spZ regsc = e_sp0 E + (e_A E - e_sp0 E)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HS0C : s0Z regsc = e_sp0 E).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (HO16 : (e_A E - e_sp0 E) mod 16 = 0).
{ pose proof (Z.div_mod (e_A E) 32 ltac:(lia)) as D1. rewrite HA32 in D1.
  pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)) as D2. rewrite Hal16 in D2.
  replace (e_A E - e_sp0 E) with ((2 * (e_A E / 32) - e_sp0 E / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
destruct (plookup (@pl_tpi _ PL_102_A) r) as [e|] eqn:Hpl'; [|exfalso; exact (Hpl eq_refl)].
pose proof (l6f_img_bounds B ly S Hp W mem md (BASE + r) HAR (l6f_slot_img (PA := PA) r e Hr Hpl')) as HRIMG.
unfold kImgLo, kImgEnd in HRIMG.
assert (HRAW : YK0s.ret_ok (getr regsc 1)) by (rewrite R1; exact (ret_ok_codeptr_v (PI := PA) r Hr Hr2)).
assert (HRA4 : 4096 <= raZ regsc) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; lia).
assert (HRAC : raZ regsc < YM05.alloc_ceiling) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; lia).
assert (HGP : getr regsc 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp0).
assert (HTP : getr regsc 4 = w64 (as_tp B)) by (rewrite R4; exact Htp0).
assert (Hsp8 : e_sp0 E mod 8 = 0).
{ pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)) as D2. rewrite Hal16 in D2.
  replace (e_sp0 E) with ((2 * (e_sp0 E / 16)) * 8) by lia. apply Z.mod_mul. lia. }
destruct (ec_chain_at ly (aview SEGS (w_H W) mem) (spZ regsc) (e_sp0 E) (raZ (e_regs E))
  (bv_unsigned (getr (e_regs E) 8)) Sra S8 (u64_range _) (u64_range _) HS0E Hra40 ltac:(lia) Hsp8
  ltac:(rewrite Etop; lia) ltac:(rewrite HSPC; lia)) as (ch & Hch & _).
rewrite <- HS0C in Hch.
change (mkCfg (@YK11.mkst fy regsc (Z_to_bv 64 f) mem (YK11.seg_rom SEGS)) md)
  with (cfg_at (fx := fy) SEGS f regsc mem md).
apply (l3h_call (fx := fy) (SK := SK) SEGS B PST ARc (l6f_LAWS B) (@pa_segs_low rc A_prog_listing PA) W regsc mem md
  LLVMF_STK (e_sp0 E) [] (e_ly E) (set_depot (st_depot S) (e_S E)) [] (e_W E) (e_mem E) (e_md E) own ly S Hp k STK1 []
  (e_A E - e_sp0 E) ch f (fQmn mem Q) R HJr HSPC HO16 ltac:(lia) Hs0 ltac:(lia) HRAW HRA4 HGP HTP Hch).
- intros HPRE1. specialize (Hcallee ch). unfold fpostm, fpost in Hcallee. apply Hcallee.
  split; [exact HPRE1|]. split; [exact HRO|]. split; [rewrite HSPC, Eshi; lia | exact (conj HRAC HFZy)].
- intros a Ha. exfalso. exact (inFP_nil a Ha).
- intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HJc HJ1 HP (HQ & HMN). rewrite R1.
  refine (HK W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle _ HJ1 HP HQ HMN).
  exists WSj. split; [|exact HWB].
  exact (ec_journal_unbaseR (cp := cp) (PI := PI) (L := A_prog_listing) (PA := PA) B SK WLE'
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJc).
Qed.

(* the same for a text in the float m-form (a callee that reaches musl strtod): its text concludes SRr' segs RZ_cf
   (= SRrG at WLE') with fpostFm, whose base is apost_base_xFR at WLE' (lib/A/PRH_Base.v fpostF) *)
Lemma l3h_siteF : forall (fy : YK11.FPState) (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k
  os_c i_c wk
  (regsc : bvmap 5 word) (r STK1 f : Z)
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world SEGS -> config -> Prop),
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ec_frame E fk W mem ->
  getr regsc 2 = w64 (e_A E) -> getr regsc 8 = w64 (e_sp0 E) ->
  getr regsc 3 = getr (e_regs E) 3 -> getr regsc 4 = getr (e_regs E) 4 ->
  (* FRM0-ENTRY (fpre's last conjunct, PRH_Base.v (sha256 da55cb740765; internal record)): the rounding mode is 0 at the call; ec_at gives it *)
  YK0o.frm_zero (@YK11.fp_csr fy) ->
  getr regsc 1 = Z_to_bv 64 (BASE + r) -> 0 <= r < 2 ^ 40 -> r mod 2 = 0 ->
  plookup (@pl_tpi _ PL_102_A) r <> None ->
  0 <= STK1 -> STK1 + 144 <= LLVMF_STK ->
  (forall ch, fpre B ARc STK1 ly S Hp W regsc mem md ch ->
     SRr' SEGS (@YGcfRehidePost.RZ_cf rc) W (cfg_at (fx := fy) SEGS f regsc mem md)
       (fpostFm (fx := fy) B ARc SK STK1 [] regsc ly S Hp W mem md Q)) ->
  (forall (fz : YK11.FPState) (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2 k1, WLE' W W2 ->
     YK0o.frm_zero (@YK11.fp_csr fz) -> fregs_kept_x fy fz ->
     (exists WS2, ajournal_xwR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E)
       (e_mem E) (e_md E) own ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS2 /\ YCbqGwild.wbudget [] wk WS2) ->
     ajournal_xR (SK := SK) SEGS B PST ARc WLE' STK1 (e_sp0 E + (e_A E - e_sp0 E)) [] ly S Hp W mem md [] ly2 S2 Hp2
       W2 mem2 md2 k1 ->
     aregs_preserved regsc regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
     SRrG SEGS WLE' W2 (mkCfg (@YK11.mkst fz regs2 (Z_to_bv 64 (BASE + r)) mem2 (YK11.seg_rom SEGS)) md2) R) ->
  SRrG SEGS WLE' W (mkCfg (@YK11.mkst fy regsc (Z_to_bv 64 f) mem (YK11.seg_rom SEGS)) md) R.
Proof.
intros fy E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk regsc r STK1 f Q R HI HF R2 R8 R3 R4 HFZy R1 Hr Hr2 Hpl
  Hs0 Hs1 Hcallee HK.
destruct (l3h_geo E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk HI) as (Rsp & Hal16 & HAb & HA32).
pose proof HI as ((WSj & HJ & HWB) & _ & _ & _ & HRO & _ & _ & _ & HPRE & _).
(* the budget-free call rule under the cut file's rebase / unbase at WLE' (Ent102CutsA.v ec_journal_rebaseR /
   _unbaseR) *)
pose proof (ec_journal_rebaseR (cp := cp) (PI := PI) (L := A_prog_listing) (PA := PA) B SK WLE' _ _ _ _ _ _ _ _ _ _ HJ)
  as HJr.
pose proof HPRE as (HPREX & HS0E & _).
pose proof HPREX as (_ & _ & Hra40 & Hgp0 & Htp0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HF as (Hsaved & _ & _). pose proof Hsaved as (Sra & S8 & _).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
assert (WS : LLVMF_STK = 32768) by reflexivity.
assert (HSPC : spZ regsc = e_sp0 E + (e_A E - e_sp0 E)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HS0C : s0Z regsc = e_sp0 E).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (HO16 : (e_A E - e_sp0 E) mod 16 = 0).
{ pose proof (Z.div_mod (e_A E) 32 ltac:(lia)) as D1. rewrite HA32 in D1.
  pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)) as D2. rewrite Hal16 in D2.
  replace (e_A E - e_sp0 E) with ((2 * (e_A E / 32) - e_sp0 E / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
destruct (plookup (@pl_tpi _ PL_102_A) r) as [e|] eqn:Hpl'; [|exfalso; exact (Hpl eq_refl)].
pose proof (l6f_img_bounds B ly S Hp W mem md (BASE + r) HAR (l6f_slot_img (PA := PA) r e Hr Hpl')) as HRIMG.
unfold kImgLo, kImgEnd in HRIMG.
assert (HRAW : YK0s.ret_ok (getr regsc 1)) by (rewrite R1; exact (ret_ok_codeptr_v (PI := PA) r Hr Hr2)).
assert (HRA4 : 4096 <= raZ regsc) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; lia).
assert (HRAC : raZ regsc < YM05.alloc_ceiling) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; lia).
assert (HGP : getr regsc 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp0).
assert (HTP : getr regsc 4 = w64 (as_tp B)) by (rewrite R4; exact Htp0).
assert (Hsp8 : e_sp0 E mod 8 = 0).
{ pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)) as D2. rewrite Hal16 in D2.
  replace (e_sp0 E) with ((2 * (e_sp0 E / 16)) * 8) by lia. apply Z.mod_mul. lia. }
destruct (ec_chain_at ly (aview SEGS (w_H W) mem) (spZ regsc) (e_sp0 E) (raZ (e_regs E))
  (bv_unsigned (getr (e_regs E) 8)) Sra S8 (u64_range _) (u64_range _) HS0E Hra40 ltac:(lia) Hsp8
  ltac:(rewrite Etop; lia) ltac:(rewrite HSPC; lia)) as (ch & Hch & _).
rewrite <- HS0C in Hch.
change (mkCfg (@YK11.mkst fy regsc (Z_to_bv 64 f) mem (YK11.seg_rom SEGS)) md)
  with (cfg_at (fx := fy) SEGS f regsc mem md).
apply (l3h_callF (fx := fy) (SK := SK) SEGS B PST ARc (l6f_LAWS B) (@pa_segs_low rc A_prog_listing PA) W regsc mem md
  LLVMF_STK (e_sp0 E) [] (e_ly E) (set_depot (st_depot S) (e_S E)) [] (e_W E) (e_mem E) (e_md E) own ly S Hp k STK1 []
  (e_A E - e_sp0 E) ch f (fQmn mem Q) R HJr HSPC HO16 ltac:(lia) Hs0 ltac:(lia) HRAW HRA4 HGP HTP Hch).
- intros HPRE1. specialize (Hcallee ch). unfold fpostFm, fpostF in Hcallee. apply Hcallee.
  split; [exact HPRE1|]. split; [exact HRO|]. split; [rewrite HSPC, Eshi; lia | exact (conj HRAC HFZy)].
- intros a Ha. exfalso. exact (inFP_nil a Ha).
- intros fz W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HFZ HFK HJc HJ1 HP (HQ & HMN). rewrite R1.
  refine (HK fz W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HFZ HFK _ HJ1 HP HQ HMN).
  exists WSj. split; [|exact HWB].
  exact (ec_journal_unbaseR (cp := cp) (PI := PI) (L := A_prog_listing) (PA := PA) B SK WLE'
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJc).
Qed.

(* AFTER A CALL with an empty footprint that keeps the blocks and the ledger: the cut's invariant, the frame, the
   document and the live bytes (both journals at WLE') *)
Lemma l3h_core_after : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk res D
  os2 i2
  STK1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  IMG ->
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ec_frame E fk W mem ->
  ec_doc_state fk W mem Lam res D ->
  (* the tree's free order (the cut file's ec_pjf, the kit's no-DW batch): kept like the document, over its footprint *)
  ec_pjf_res E fk W mem Lam res D ->
  (exists WS2, ajournal_xwR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
    (e_md E) own ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS2 /\ YCbqGwild.wbudget [] wk WS2) ->
  ajournal_xR (SK := SK) SEGS B PST ARc WLE' STK1 (e_sp0 E + (e_A E - e_sp0 E)) [] ly S Hp W mem md [] ly2 S2 Hp2 W2
    mem2 md2 k1 ->
  ablocks B ly2 S2 = ablocks B ly S ->
  (exists most own, prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak cnt SIZE_MAX ran most own) ->
  room_live_cf S2 ->
  (exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os2 i2 (e_H0 E) hist S2) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  INV E fk ly2 S2 Hp2 W2 mem2 md2 own Lam peak cnt ran (k + k1) os2 i2 wk /\ ec_frame E fk W2 mem2 /\
  ec_doc_state fk W2 mem2 Lam res D /\ ec_pjf_res E fk W2 mem2 Lam res D /\ blocks_bytes S2 = blocks_bytes S.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk res D os2 i2 STK1 ly2 S2 Hp2 W2 mem2 md2 k1
  HIMG HI HF HDS HPJ (WSc & HJc & HWBc) HJ1 Eab HL2 HRL2 HRP2 HMN2.
pose proof (ei_sio B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG HIMG) as Hsio.
pose proof (ei_sio_frame B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG HIMG) as Hsioframe.
pose proof (ei_pst_ro B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG HIMG) as Hpstro.
destruct (l3h_geo E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk HI) as (Rsp & Hal16 & HAb & HA32).
destruct (ec_inv_ledgerR (fx := fx) (cp := cp) (PI := PI) (RL := RL) B SK EC_RA EC_EMPTY EC_SIO HI)
  as (most0 & own0 & HLED).
destruct HI as ((WSj & HJ & HWB) & HOWN & _ & HSIO & HRO & HLIVE & HROOM & HCNT & HPRE & HPAY & HPERM & HBYTES & HMN).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & HNC & _ & _ & HfrE & _).
(* ec_pre's read-only bytes and stdio state at entry, BY NAME (ec_pre grows) *)
assert (HRO0 : arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) B
  (aview SEGS (w_H (e_W E)) (e_mem E))) by (unfold ec_pre in HPRE; ec_conj_pick HPRE).
assert (HSIO0 : EC_SIO (aview SEGS (w_H (e_W E)) (e_mem E))) by (unfold ec_pre in HPRE; ec_conj_pick HPRE).
destruct (l3h_keep (SK := SK) B PST WLE' E fk ly S Hp W mem md own k WSj STK1 (e_sp0 E + (e_A E - e_sp0 E)) []
  ly2 S2 Hp2 W2 mem2 md2 k1 HJ HfrE HOWN HF HJ1) as (HOWN2 & HF2).
{ unfold EC_SAVE. lia. }
{ intros a Ha. exfalso. exact (inFP_nil a Ha). }
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2c & F3c & _).
pose proof HJ1 as (HAR2 & Hly1 & _ & _ & _ & Hfrs1 & _ & _ & _ & G2 & _ & G4 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
split.
{ split; [exists WSc; split; [exact HJc | exact HWBc]|].
  split; [exact HOWN2|].
  split; [exact HL2|].
  split.
  { apply (Hsioframe (aview SEGS (w_H (e_W E)) (e_mem E)) (aview SEGS (w_H W2) mem2)); [|exact HSIO0].
    intros a Ha. destruct (Hsio a Ha) as ((Ho & He) & Hi & Hnp).
    apply F3c; [exact Hi | exact Ho | exact He | exact Hnp | apply fp_spares_closed; exact sink_closed_nil]. }
  split.
  { intros a Hro Ho He.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr];
      [exists s; split; [exact Hs | lia] | exact (@pa_relro_img rc A_prog_listing PA a Hr)]. }
    assert (Hsp : fp_spares (SK := SK) [] a) by (apply fp_spares_closed; exact sink_closed_nil).
    rewrite (F3c a Hi Ho He (fun Hp' => Hpstro a Hp' Hro) Hsp).
    exact (HRO0 a Hro Ho He). }
  split; [exact HRL2|].
  split; [exact HRP2|].
  split; [exact HCNT|].
  split; [exact HPRE|].
  split; [rewrite Eab; exact HPAY|].
  split; [rewrite Eab; exact HPERM|].
  split.
  { intros i Hi. destruct HNC as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
    destruct HPAY as [Hn0' | Hinp']; [lia|].
    pose proof (req_size_pos (e_n E) ltac:(lia)) as (_ & Hrq).
    apply (F2c (e_p E) (e_n E) i Hinp); [rewrite Eab; exact Hinp' | lia |].
    intros (r0 & Hr0 & _). destruct Hr0. }
  exact (HMN2 HMN). }
split; [exact HF2|].
cut (ec_doc_state fk W2 mem2 Lam res D /\ ec_pjf_res E fk W2 mem2 Lam res D).
{ intros (HDS2' & HPJ2'). split; [exact HDS2'|]. split; [exact HPJ2'|].
  rewrite (prh_blocks_bytes_ablocks B ly2 S2), Eab, <- (prh_blocks_bytes_ablocks B ly S). reflexivity. }
destruct HOWN as (pos & Hown & Hfkeq & Hfk0 & _).
  assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, HfrE, Hown; left; reflexivity).
  pose proof Hly1 as (_ & _ & _ & _ & _ & EF & _).
  assert (Hfa2 : frame_addr ly2 LLVMF_FS_CLASS pos = frame_addr ly LLVMF_FS_CLASS pos)
    by (unfold frame_addr; rewrite EF; reflexivity).
  assert (Hin2 : In (LLVMF_FS_CLASS, pos) (frames S2)) by (rewrite Hfrs1; exact Hin).
  pose proof HAR2 as (HAR2cf & _).
  destruct (l6f_geom B ly2 S2 Hp2 W2 mem2 md2 pos fk HAR2cf Hin2 ltac:(rewrite Hfa2; exact Hfkeq))
    as (_ & _ & _ & _ & Gfr2 & _).
  assert (KD : forall x, ec_doc fk <= x < ec_doc fk + 56 ->
    mbyte SEGS (mrestrict (w_H W2) mem2) x = mbyte SEGS (mrestrict (w_H W) mem) x /\
    (writable_at SEGS (mrestrict (w_H W) mem) x -> writable_at SEGS (mrestrict (w_H W2) mem2) x)).
  { intros x Hx. unfold ec_doc in Hx. split.
    - apply prh_mbyte_of_aview. apply (G4 LLVMF_FS_CLASS pos x Hin); [|exact (inFP_nil x)].
      left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq.
      change (fs_frame_bytes LLVMF_FS_CLASS) with 128. lia.
    - intros _. apply (apresent_writable SEGS). exact (proj1 (Gfr2 x ltac:(unfold EC_FRAME_BYTES; lia))). }
  assert (KB : forall a0 k0 x, In (a0, k0) Lam -> a0 <= x < a0 + k0 ->
    mbyte SEGS (mrestrict (w_H W2) mem2) x = mbyte SEGS (mrestrict (w_H W) mem) x /\
    (writable_at SEGS (mrestrict (w_H W) mem) x -> writable_at SEGS (mrestrict (w_H W2) mem2) x)).
  { intros a0 k0 x HinL Hx.
    pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt SIZE_MAX ran a0 k0 _ _ HLED HinL) as (Hk0 & Hb & _).
    assert (Hb2 : In (a0 - cf_head, k0 + cf_head) (ablocks B ly2 S2)) by (rewrite Eab; exact Hb).
    pose proof cf_head_nonneg as C0.
    assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
    split.
    - apply prh_mbyte_of_aview.
      replace x with (a0 - cf_head + (x - (a0 - cf_head))) by lia.
      apply (G2 (a0 - cf_head) (k0 + cf_head) (x - (a0 - cf_head)) Hb Hb2); [lia | exact (inFP_nil _)].
    - intros _. apply (apresent_writable SEGS).
      pose proof (AR_blocks_law_ok_cf SEGS B ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2cf Hb2) as (_ & _ & _ & _ & Hpr & _).
      exact (proj1 (Hpr x ltac:(lia))). }
  unfold ec_doc_state in HDS |- *. unfold ec_pjf_res in HPJ |- *. destruct res as [t|].
  + destruct HDS as (HPLD & Hnode).
    (* the footprint of the tree at &doc keeps its bytes and writability: the document's node and its free order *)
    assert (HAG : pj_agreeR SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (pj_footR (ec_doc fk) D)).
    { intros x [Hx | ((a0 & k0) & HinD & Hx)].
      * exact (KD x Hx).
      * unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
        exact (KB a0 k0 x (Permutation_in _ (Permutation_sym HPLD) HinD) Hx). }
    split; [split; [exact HPLD|]; eapply pj_nodeR_frame; [exact Hnode | exact HAG]|].
    unfold ec_pjf in HPJ |- *. intros n Hdn. destruct (HPJ n Hdn) as (F & HF0 & HFeq).
    exists F. split; [|exact HFeq].
    eapply PRH_PjOrder.pj_foR_frame; [exact HF0| |exact HAG].
    intros a0 k0 Ha. exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HF0 a0 k0 Ha).
  + destruct HDS as (HL0 & HD0 & Hz). split; [|exact I]. split; [exact HL0|]. split; [exact HD0|].
    eapply pj_zeroR_frame; [exact Hz|]. intros x Hx. exact (proj1 (KD x Hx)).
Qed.

(* the document node's home: 8-aligned, inside this call's own fake frame, addressable (shadow bytes 4 .. 10) *)
Lemma l3h_doc_home : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk,
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ec_frame E fk W mem ->
  ck_obj_home ly S W mem (ec_doc fk).
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk HI HF.
destruct HI as ((WSj & HJ & _) & HOWN & _ & _ & _ & _ & _ & _ & HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HfrE & _).
destruct HOWN as (pos & Hown & Hfkeq & Hfk0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HF as (_ & Hshv & Hal32).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, HfrE, Hown; left; reflexivity).
pose proof HAR as (HARcf & _).
destruct (l6f_geom B ly S Hp W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & Gapp & _ & Gsh).
assert (Hfk32 : fk = 32 * (fk / 32))
  by (pose proof (Z.div_mod fk 32 ltac:(lia)) as D0; rewrite Gal in D0; lia).
unfold ck_obj_home, ec_doc.
split.
{ rewrite Hfk32. replace (32 * (fk / 32) + 32) with ((4 * (fk / 32) + 4) * 8) by lia. apply Z.mod_mul. lia. }
split.
{ exists LLVMF_FS_CLASS, pos. split; [exact Hin|]. rewrite <- Hfkeq.
  change (fs_frame_bytes LLVMF_FS_CLASS) with 128. lia. }
intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (shadow_addr fk + (x / 8 - fk / 8)) by (unfold shadow_addr; lia).
apply (l6f_shadow_zero (PA := PA) (w_H W) mem (shadow_addr fk) Hshv).
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D2. lia.
Qed.

(* THE PAYLOAD AT n > 0: inside a live block whose base is not a hidden head (es3_pay_not_hd's argument) *)
Lemma l3h_inblk : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk,
  INV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> 0 < e_n E ->
  PRH_FnEx.prhex_inblk B ly S Hp (e_p E) (e_n E).
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk HI Hn0.
destruct (ec_inv_ledgerR (fx := fx) (cp := cp) (PI := PI) (RL := RL) B SK EC_RA EC_EMPTY EC_SIO HI)
  as (most0 & own0 & HLED).
destruct HI as ((WSj & HJ & _) & _ & _ & _ & _ & _ & _ & _ & HPRE & HNC & HPERM & _).
pose proof HJ as (HAR & _). pose proof HAR as (HARcf & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & HPN & _).
destruct HPN as [(Hz & _) | (_ & Hin0)]; [lia|].
destruct HNC as [Hz | Hin]; [lia|].
pose proof (AR_blocks_law_ok_cf SEGS B ly S Hp W mem md _ _ HARcf Hin) as (_ & _ & _ & _ & _ & Hpw & _).
pose proof (prh_ablocks_nonneg_cf B ly S Hp W mem md HARcf) as Hnn.
exists (e_p E), (e_n E). split; [exact Hin|]. split; [lia|]. split; [lia|].
intros Hh. exfalso.
pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt SIZE_MAX ran most0 own0 HLED) as HH.
apply (Permutation_in _ HH) in Hh. apply in_map_iff in Hh as ((a & k0) & Ea & HinL). cbn [fst] in Ea.
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt SIZE_MAX ran a k0 _ _ HLED HinL) as (Hk0 & Hb & _).
rewrite Ea in Hb.
assert (Eb : (e_p E, k0 + cf_head) = (e_p E, e_n E)).
{ apply (l3h_pw_head (ablocks B ly S)); [exact Hpw | exact Hb | exact Hin | reflexivity |].
  intros b Hb'. exact (proj1 (Forall_forall _ _) Hnn b Hb'). }
assert (HND : List.NoDup (ablocks B ly S)) by exact (l6f_nodup_pw _ Hnn Hpw).
pose proof (Permutation_NoDup HPERM HND) as HND2.
apply (l3h_nodup_app _ _ (e_p E, e_n E) HND2); [|exact Hin0].
rewrite <- Eb. unfold ck_hblks. rewrite <- Ea.
exact (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Lam (a, k0) HinL).
Qed.

(* THE PAYLOAD AT n = 0: the empty input at the registered datum EC_EMPTY (ei_empty) *)
Lemma l3h_src0 : forall (W : world SEGS) mem,
  YImgTop.IMG_LO + 64 <= EC_EMPTY /\ EC_EMPTY + 64 <= YImgTop.IMG_TOP ->
  src_rd W mem EC_EMPTY [].
Proof.
intros W mem (H1 & H2). unfold YImgTop.IMG_LO in H1. unfold YImgTop.IMG_TOP in H2.
pose proof YCbq.asan_consts as (C1 & _).
unfold src_rd. cbn [length Z.of_nat].
split; [intros j Hj; cbn [length] in Hj; lia|].
split; [lia|]. split; [lia|].
split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
split; [apply range_addressable_nil; lia | intros H; lia].
Qed.
End L.
