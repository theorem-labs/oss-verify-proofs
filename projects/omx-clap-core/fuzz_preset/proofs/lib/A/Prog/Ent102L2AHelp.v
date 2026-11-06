(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): the SUPPORT LEMMAS of segment L2 of
   LLVMFuzzerTestOneInput (entry 0x815e0), listing +0x14c .. +0x174 (the `bnez a0` after check_no_overread, the r = 1
   arm to EXIT, the calls of fuzz_alloc_live, fuzz_alloc_count, fuzz_alloc_peak_reset and parse_noting), for the
   segment proof lib/A/Prog/Ent102L2A.v. No function is proved here: register and byte facts (section 1: a written
   register, a trace's held bytes, the harness blocks' allocator bytes, the document's shadow at fk + 32), the call
   rules of a callee TEXT over YCbqG's journal (l2_call / l2_callF at the empty budget, l2_callbF for a budgeted float
   callee under a caller at a wild budget: afn_pre_x_at_w, ajournal_xw_sub) and the keep of the caller's frame across
   a call (l2_keep, at any wild budget). Each of the four is stated over a WORLD RELATION Rel (suffix R: l2_callR,
   l2_callFR, l2_callbFR, l2_keepR; YA0nH.SRrG and YCbqG's R journals), because segment L2 runs after check_no_overread's
   frees at wle' segs RZ_cf; the plain name is the R form at wle. l2_lift_call reads a plain accessor text at any Rel
   containing wle. An empty-budget callee under a wild caller goes through Ent102CutsA's shared
   ec_journal_rebase(R) / ec_journal_unbase(R) (in Ent102L2A.v). The step rules, the frame geometry and the byte keeps
   are lib/A/Prog/Ent102L6AfLem.v's (written against blob a37e0dc13d12).
   STATEMENT read: lib/A/Ent102CutsA.v (ec_ARx, ec_frame_shadow, EC_FRAME_BYTES, LLVMF_FS_CLASS, ec_own, ec_frame,
   ec_saved, ec_doc).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L2 (reuse search: the released-proof index by name
   LLVMFuzzerTestOneInput exit 0, by address 0x815e0 exit 4; check CONFIRM 14:51Z: no released ASan proof, NEW walk).
   This file: support lemmas of that segment only.
   NUMERALS: 128 / 120 / 104 / 56 / 32 / 16 / 8 are LENGTHs (the frame, its flag-pointer slot, the saved block, the
   document, its offset in the fake frame, the shadow bytes, the word); 4 .. 10 are the document's shadow bytes in
   ec_frame_shadow; 268431360 * 8 is SHADOW_OFF (checked by reflexivity); 2 ^ 64 is the word range; kLowShadowBeg /
   kHighMemBeg / SHADOW_OFF are ASan constants. No ADDRESS. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA PRH_Base Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102L6AfLem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Registers across a write: the written one reads the new value, every other keeps its value. *)
Lemma l2_getr_upd_other : forall regs (rd r : bv 5) v, r <> rd -> getr (regupd regs rd v) r = getr regs r.
Proof. intros regs rd r v H. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact H. Qed.

Lemma l2_getr_upd_same : forall regs (rd : bv 5) v, bv_eqb rd 0 = false -> getr (regupd regs rd v) rd = v.
Proof. intros regs rd v H. unfold getr. rewrite H. apply regupd_same. Qed.

(* a callee-saved register is not ra *)
Lemma l2_cs_ne1 : forall r, acallee_saved r -> Z_to_bv 5 r <> 1%bv.
Proof.
intros r Hr E. apply (f_equal (@bv_unsigned 5)) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
change (bv_modulus 5) with 32 in E. change (bv_unsigned (1%bv : bv 5)) with 1 in E.
unfold acallee_saved in Hr. rewrite Z.mod_small in E by lia. lia.
Qed.

(* the bytes a trace holds at its end are at most its peak *)
Lemma l2_held_hpeak : forall tr, PjGrammar.held tr <= ReaderRes.hpeak tr.
Proof. induction tr as [|e r IH]; cbn [PjGrammar.held ReaderRes.hpeak]; lia. Qed.

(* the allocator bytes of harness blocks: each user size plus the head *)
Section HB. Context {cp : CfParams}.
Lemma l2_bsum_hblks : forall D, bsum (ck_hblks D) = Ledger.lsum D + cf_head * Z.of_nat (length D).
Proof.
induction D as [|[a k] D IH]; [unfold ck_hblks; cbn; lia|].
unfold ck_hblks in *. cbn [map]. rewrite bsum_cons. cbn [snd fst]. rewrite IH.
cbn [Ledger.lsum length snd]. rewrite Nat2Z.inj_succ. lia.
Qed.
End HB.

(* ---------------------------------------------------------------------- *)
(* 2. THE CALL RULE: a callee's TEXT applied at its entry, from a caller state its journal describes. This is
      lib/Reusable/YCbqGcall.v aj_call_x_sp / aj_call_xF_sp's proof without the symbolic state (the caller's state
      here is concrete): afn_pre_x_at builds the callee's pre from the caller's journal, the text runs to its
      apost_base_x(F), and ajournal_x_sub composes the two journals. OVER A WORLD RELATION Rel (the free move: segment L2
      runs at wle' segs RZ_cf, after check_no_overread's frees, YA0nH.SRrG): the caller's journal, the callee's post
      and the conclusion are at Rel (YCbqG.ajournal_xR / ajournal_xwR / apost_base_xR, YCbqGwild.apost_base_xbFR); Rel
      transitive composes them (YCbqG.ajournal_x_subR / ajournal_xw_subR). Each plain name is its R form at wle. *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

Section CR.
Variable Rel : world segs -> world segs -> Prop.
Hypothesis Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3.

(* A CALLEE WHOSE TEXT DOES NOT FREE (the accessors fuzz_alloc_live / _count / _peak_reset): its plain SRr and its
   post at wle read at any Rel containing wle (YA0nH.SRr_SRrG, YCbqG.apost_base_x_R_lift) *)
Lemma l2_lift_call : (forall W W', wle W W' -> Rel W W') ->
  forall (W : world segs) c STK FP regs ly S Hp (W0 : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  SRr segs W c (apost_base_x (SK := SK) segs B PST ARx STK FP regs ly S Hp W0 mem md Q) ->
  SRrG segs Rel W c (apost_base_xR (SK := SK) segs B PST ARx Rel STK FP regs ly S Hp W0 mem md Q).
Proof.
intros Rel_wle W c STK FP regs ly S Hp W0 mem md Q H.
eapply SRrG_mono; [exact (SRr_SRrG segs Rel Rel_wle W c _ H)|].
intros W' c' _ HQ. exact (YCbqG.apost_base_x_R_lift segs B PST ARx Rel Rel_wle _ _ _ _ _ _ _ _ _ _ _ _ HQ).
Qed.

Lemma l2_callR : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  STK1 FP1 (o : Z) ch (f : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xR (SK := SK) segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRrG segs Rel W (cfg_at segs f regs mem md)
       (apost_base_xR (SK := SK) segs B PST ARx Rel STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1, Rel W W2 ->
     ajournal_xR (SK := SK) segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     ajournal_xR (SK := SK) segs B PST ARx Rel STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG segs Rel W2 (mkCfg (@YK11.mkst fx regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRrG segs Rel W (cfg_at segs f regs mem md) R.
Proof.
intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k STK1 FP1 o ch f Q R
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch Hcallee HF HK.
eapply (SRrG_bind segs Rel Rel_trans).
{ apply Hcallee.
  exact (afn_pre_x_atR segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k regs STK1 o ch
    HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch). }
intros W2 c2 Hle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
rewrite Hsp in HJ1.
apply (HK W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle); [|exact HJ1 | exact HP | exact HQ].
change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARx LAWS segs_low Rel Rel_trans); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

Lemma l2_callFR : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  STK1 FP1 (o : Z) ch (f : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xR (SK := SK) segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRrG segs Rel W (cfg_at segs f regs mem md)
       (apost_base_xFR (SK := SK) segs B PST ARx Rel STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (fx' : YK11.FPState) (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1, Rel W W2 ->
     YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' ->
     ajournal_xR (SK := SK) segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     ajournal_xR (SK := SK) segs B PST ARx Rel STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG segs Rel W2 (mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRrG segs Rel W (cfg_at segs f regs mem md) R.
Proof.
intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k STK1 FP1 o ch f Q R
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch Hcallee HF HK.
eapply (SRrG_bind segs Rel Rel_trans).
{ apply Hcallee.
  exact (afn_pre_x_atR segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k regs STK1 o ch
    HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch). }
intros W2 c2 Hle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HP & HQ).
rewrite Hsp in HJ1.
apply (HK fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HFZ HFK); [|exact HJ1 | exact HP | exact HQ].
change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARx LAWS segs_low Rel Rel_trans); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* A BUDGETED float callee (apost_base_xbFR P, parse_noting): afn_pre_x_at_wR, the text, YCbqG's ajournal_xw_subR -
   the caller's journal after the call is at WS0 ++ WS1 with P WS1 *)
Lemma l2_callbFR : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  WS0 STK1 FP1 (o : Z) ch (f : Z) (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xwR (SK := SK) segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k WS0 ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRrG segs Rel W (cfg_at segs f regs mem md)
       (YCbqGwild.apost_base_xbFR (SK := SK) segs B PST ARx Rel P STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (fx' : YK11.FPState) (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1, Rel W W2 ->
     YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' -> P WS1 ->
     ajournal_xwR (SK := SK) segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1)
       (WS0 ++ WS1) ->
     ajournal_xwR (SK := SK) segs B PST ARx Rel STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG segs Rel W2 (mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRrG segs Rel W (cfg_at segs f regs mem md) R.
Proof.
intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k WS0 STK1 FP1 o ch f P Q R
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch Hcallee HF HK.
eapply (SRrG_bind segs Rel Rel_trans).
{ apply Hcallee.
  exact (YCbqGwild.afn_pre_x_at_wR segs B PST ARx Rel STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k WS0
    regs STK1 o ch HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch). }
intros W2 c2 Hle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP & HQ).
rewrite Hsp in HJ1.
apply (HK fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 WS1 Hle HFZ HFK HPW); [|exact HJ1 | exact HP | exact HQ].
change own with ([] ++ own).
eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low Rel Rel_trans); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End CR.

(* the plain call rules: the R forms at wle *)
Lemma l2_call : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  STK1 FP1 (o : Z) ch (f : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRr segs W (cfg_at segs f regs mem md)
       (apost_base_x (SK := SK) segs B PST ARx STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1, wle W W2 ->
     ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     ajournal_x (SK := SK) segs B PST ARx STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRr segs W (cfg_at segs f regs mem md) R.
Proof. exact (l2_callR (@wle segs) (wle_trans segs)). Qed.

Lemma l2_callF : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  STK1 FP1 (o : Z) ch (f : Z)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRr segs W (cfg_at segs f regs mem md)
       (apost_base_xF (SK := SK) segs B PST ARx STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (fx' : YK11.FPState) (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1, wle W W2 ->
     YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' ->
     ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     ajournal_x (SK := SK) segs B PST ARx STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRr segs W2 (mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRr segs W (cfg_at segs f regs mem md) R.
Proof. exact (l2_callFR (@wle segs) (wle_trans segs)). Qed.

Lemma l2_callbF : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp k
  WS0 STK1 FP1 (o : Z) ch (f : Z) (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> config -> Prop),
  ajournal_xw (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k WS0 ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
  (afn_pre_x segs B ARx STK1 ly S Hp W regs mem md ch ->
     SRr segs W (cfg_at segs f regs mem md)
       (YCbqGwild.apost_base_xbF (SK := SK) segs B PST ARx P STK1 FP1 regs ly S Hp W mem md Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly0 S0 own ly S ->
  (forall (fx' : YK11.FPState) (W2 : world segs) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1, wle W W2 ->
     YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' -> P WS1 ->
     ajournal_xw (SK := SK) segs B PST ARx STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1)
       (WS0 ++ WS1) ->
     ajournal_xw (SK := SK) segs B PST ARx STK1 (sp0 + o) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
     aregs_preserved regs regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRr segs W2 (mkCfg (@YK11.mkst fx' regs2 (getr regs 1) mem2 (YK11.seg_rom segs)) md2) R) ->
  SRr segs W (cfg_at segs f regs mem md) R.
Proof. exact (l2_callbFR (@wle segs) (wle_trans segs)). Qed.
End C.

(* ---------------------------------------------------------------------- *)
(* 3. THE CALLER'S FRAME ACROSS A CALL: the saved block (above the callee's sp), the fake frame's flag word and its
      sixteen shadow bytes (a frame live at the callee's entry, off the callee's footprint) are kept by the callee's
      journal, so ec_own and ec_frame hold after the call. *)
Section K. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {SK : YI16.sink_head}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable PST : list (Z * Z).
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).

(* the frame's shadow bytes lie off the frame (in_app; as Ent102L6AEnt.v l6_entry_ok's HSHsep) *)
Lemma l2_shadow_off : forall fk, in_app fk EC_FRAME_BYTES -> 4096 <= fk ->
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

(* over a world relation Rel (both journals at Rel: only their world conjunct reads it, and this proof does not read
   that conjunct); l2_keep is its instance at wle *)
Lemma l2_keepR : forall (Rel : world SEGS -> world SEGS -> Prop) (E : ecx (L := A_prog_listing) (PA := PA)) fk ly S Hp
  (W : world SEGS) mem md own k WS STK1 A FP1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 WS1,
  ajournal_xwR (SK := SK) SEGS B PST ARc Rel LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E)
    own ly S Hp W mem md k WS ->
  frames (e_S E) = [] ->
  ec_own fk ly W mem own -> ec_frame E fk W mem ->
  ajournal_xwR (SK := SK) SEGS B PST ARc Rel STK1 A FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  A <= e_sp0 E - EC_SAVE ->
  (forall a, inFP FP1 a -> fk <= a < fk + EC_FRAME_BYTES - 8) ->
  ec_own fk ly2 W2 mem2 own /\ ec_frame E fk W2 mem2.
Proof.
intros Rel E fk ly S Hp W mem md own k WS STK1 A FP1 ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HJ Hfr0 HOWN HFRM HJ1 HA HFP.
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
pose proof (l2_shadow_off fk Gapp G4096) as Hsep.
unfold EC_FRAME_BYTES, EC_SAVE, LLVMF_STK in *.
(* the frame's own bytes off the footprint, and its sixteen shadow bytes, are kept *)
assert (KF : forall a, fk <= a < fk + 128 -> ~ inFP FP1 a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. apply (G4 LLVMF_FS_CLASS pos a Hin); [|exact Hn].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq, HFB. lia. }
assert (KS : forall i, 0 <= i < 16 ->
  aview SEGS (w_H W2) mem2 (shadow_addr fk + i) = aview SEGS (w_H W) mem (shadow_addr fk + i)).
{ intros i Hi. apply (G4 LLVMF_FS_CLASS pos _ Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite <- Hfkeq, HFB8. lia.
  - intros Hf. apply HFP in Hf. lia. }
(* the saved block is above the callee's sp and above the ceiling *)
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
Lemma l2_keep : forall (E : ecx (L := A_prog_listing) (PA := PA)) fk ly S Hp (W : world SEGS) mem md own k WS
  STK1 A FP1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 WS1,
  ajournal_xw (SK := SK) SEGS B PST ARc LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  frames (e_S E) = [] ->
  ec_own fk ly W mem own -> ec_frame E fk W mem ->
  ajournal_xw (SK := SK) SEGS B PST ARc STK1 A FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  A <= e_sp0 E - EC_SAVE ->
  (forall a, inFP FP1 a -> fk <= a < fk + EC_FRAME_BYTES - 8) ->
  ec_own fk ly2 W2 mem2 own /\ ec_frame E fk W2 mem2.
Proof. exact (l2_keepR (@wle SEGS)). Qed.

(* two byte strings stated at one address read the same view there *)
Lemma l2_garr8_eq : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H' m') base l ->
  forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H' m' (base + i) = aview SEGS H m (base + i).
Proof.
intros H H' m m' base l G1 G2 i Hi.
destruct (G1 (Z.to_nat i) ltac:(lia)) as [V1 _]. destruct (G2 (Z.to_nat i) ltac:(lia)) as [V2 _].
specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)).
replace (base + i) with (base + Z.of_nat (Z.to_nat i) + Z.of_nat 0) by lia.
unfold aview. rewrite V1, V2. reflexivity.
Qed.

(* a granule-rounded address *)
Lemma l2_div8 : forall c d, 0 <= d < 8 -> (c * 8 + d) / 8 * 8 = c * 8.
Proof. intros c d Hd. rewrite Z.div_add_l by lia. rewrite (Z.div_small d 8 Hd). lia. Qed.

(* the document's 56 bytes at fk + 32 are addressable (their shadow bytes 4 .. 10 of the frame read 0) and their
   shadow hull lies in the frame's 16 present shadow bytes *)
Lemma l2_doc_shadow : forall (H : word -> bool) (m : word -> option byte) fk,
  fk mod 32 = 0 -> 0 <= fk ->
  garr8 SEGS (mrestrict H m) (shadow_addr fk) ec_frame_shadow ->
  (forall i, 0 <= i < 16 -> apresent H m (shadow_addr fk + i)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF (fk + 32) 56 /\ shadow_hull_vis (aview SEGS H m) (fk + 32) 56.
Proof.
intros H m fk Hal Hfk Hsh Hpr.
pose proof (proj1 (Z.mod_divide _ 32 ltac:(lia)) Hal) as (q & Hq).
assert (E8 : fk / 8 = 4 * q) by (rewrite Hq; replace (q * 32) with ((4 * q) * 8) by lia; apply Z.div_mul; lia).
assert (Esh : shadow_addr fk = SHADOW_OFF + 4 * q) by (unfold shadow_addr; rewrite E8; reflexivity).
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Ex : x / 8 = 4 * q + (x - fk) / 8).
  { rewrite Hq. replace x with ((x - q * 32) + (4 * q) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  assert (Hj : 4 <= (x - fk) / 8 <= 10).
  { split; [apply Z.div_le_lower_bound; lia|].
    assert ((x - fk) / 8 < 11) by (apply Z.div_lt_upper_bound; lia). lia. }
  unfold shadow_of_addr. rewrite Ex.
  replace (SHADOW_OFF + (4 * q + (x - fk) / 8)) with (shadow_addr fk + (x - fk) / 8) by (rewrite Esh; lia).
  exact (l6f_shadow_zero H m (shadow_addr fk) Hsh ((x - fk) / 8) Hj).
- intros s Hs. unfold shadow_addr in Hs.
  assert (E1 : (fk + 32) / 8 = 4 * q + 4).
  { rewrite Hq. replace (q * 32 + 32) with ((4 * q + 4) * 8) by lia. apply Z.div_mul. lia. }
  assert (E2 : (fk + 32 + 56 - 1) / 8 = 4 * q + 10).
  { rewrite Hq. replace (q * 32 + 32 + 56 - 1) with (7 + (4 * q + 10) * 8) by lia. rewrite Z.div_add by lia.
    reflexivity. }
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod q 2 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Mq.
  assert (HSO : SHADOW_OFF = 268431360 * 8) by reflexivity.
  assert (Hb : q mod 2 = 0 \/ q mod 2 = 1) by lia.
  assert (L : SHADOW_OFF + 4 * q <= (SHADOW_OFF + (4 * q + 4)) / 8 * 8 /\
              (SHADOW_OFF + (4 * q + 10)) / 8 * 8 + 8 <= SHADOW_OFF + 4 * q + 16).
  { rewrite HSO. destruct Hb as [B0|B1].
    - rewrite B0 in Dq.
      replace (268431360 * 8 + (4 * q + 4)) with ((268431360 + q / 2) * 8 + 4) by lia.
      replace (268431360 * 8 + (4 * q + 10)) with ((268431360 + q / 2 + 1) * 8 + 2) by lia.
      rewrite !l2_div8 by lia. lia.
    - rewrite B1 in Dq.
      replace (268431360 * 8 + (4 * q + 4)) with ((268431360 + q / 2 + 1) * 8 + 0) by lia.
      replace (268431360 * 8 + (4 * q + 10)) with ((268431360 + q / 2 + 1) * 8 + 6) by lia.
      rewrite !l2_div8 by lia. lia. }
  apply (YCbq.aview_some_of_apresent SEGS).
  replace s with (shadow_addr fk + (s - shadow_addr fk)) by lia. apply Hpr. rewrite Esh. lia.
Qed.
End K.

Print Assumptions l2_lift_call.
Print Assumptions l2_callR.
Print Assumptions l2_callFR.
Print Assumptions l2_callbFR.
Print Assumptions l2_keepR.
