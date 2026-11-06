(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/MemnormLoc.v (commit ce1a656b52b7, file sha256 6fda8ba66b7e) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormLoc.v (commit 30a1993588f, c5 + memnorm; file sha256 6501a76bde7b) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/MemnormLoc.v (commit d2dafa219c1, file sha256 55a52bb067f0) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* Theorem Labs, 2026-10 (task MEMNORM, callee add-ons): location lemmas for the memnorm keeps of the cgif_file
   Allocate / Deallocate callee walks (brief, the internal file CALLEE-BRIEF.md, measurement, the internal file callee-frames.md).
   rule 24: no function proved (kind: image / location lemmas).

   A callee walk's own writes have a window frame `mem' x = mem x` outside its window D; MemnormT.memnorm_frame turns
   that frame into the keep `memnorm mem -> memnorm mem'` once every byte of D is MemnormT.mn_safe (not read-only, below
   TASK_SIZE).  This file gives:
   - [memnorm_keep_refl] / [memnorm_keep_trans]: keeps chain (a nested callee's `_em` keep between two window keeps);
     the image-free lemmas live in MemnormLocG.v (with mn_safe_noseg / mn_safe_wseg / memnorm_keep_window(2)); the
     two are restated here under their old names, by MemnormLocG's proofs;
   - [mn_safe_zone3] (a zone3 extent below ASAN_CEIL: off the image, YF0x zone3_off_img; ASAN_CEIL < TASK_SIZE,
     YG0f.v:15) and [mn_safe_ceil] (at or above kImgEnd, below ASAN_CEIL: tfibsegs has no segment there);
   - the four D windows the callee arms weaken to "owned" (the internal file callee-frames.md), each as [*_D_safe] (every byte of D is
     mn_safe) and [*_D_keep] (the window frame gives the keep), with the arguments of the D_owned lemma beside which a
     hand adds the keep:
     YFf4.D (Recycle secondary, plumbingR; YFf4.D_owned :1131), from YFf4.D_cases :275, YFf4.HIGH :233, YFf4.LST :258,
       YFf4.geom :220;
     YFf1.D (Enqueue, room; YFf1.D_owned :663), from YFf1.D_cases :204, YFf1.HIGH :188;
     YFf2.D (Enqueue, hit; YFf2.D_owned :866, which also takes k), from YFf2.D_cases :335, YFf2.HIGH :316;
     YFey.D (Drain transfer; YFey.D_owned :744, plus TfibSyms for the instance cells), from YFey.D_cases :244,
       YFey.HIGH :225.
   The window -> keep step for any other window W is MemnormT.memnorm_frame (MemnormT.v:71) with W's own location
   facts (e.g. YFg0.WIN_zone, YFgs.WIN_zone, YFkm.XC_where, YFhm.TABW_range, YFg8.MAP_facts) and the helpers here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFeu YFew YFf4 YFf1 YFf2 YFey.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitG MemnormSafecgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormLocG.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Keeps chain.                                                                                                     *)
Lemma memnorm_keep_refl : forall segs (m : word -> option byte), MemnormT.memnorm_keep segs m m.
Proof. exact MemnormLocG.memnorm_keep_refl. Qed.

Lemma memnorm_keep_trans : forall segs (m1 m2 m3 : word -> option byte),
  MemnormT.memnorm_keep segs m1 m2 -> MemnormT.memnorm_keep segs m2 m3 -> MemnormT.memnorm_keep segs m1 m3.
Proof. exact MemnormLocG.memnorm_keep_trans. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Two location helpers at cgif.                                                                                    *)
Lemma mn_safe_zone3 : forall lo len (x : word), zone3 lo len -> lo <= bv_unsigned x < lo + len -> lo + len <= ASAN_CEIL ->
  MemnormT.mn_safe tfibsegs x.
Proof.
intros lo len x Z Hx Hc. pose proof (zone3_off_img lo len _ Z Hx) as O. pose proof ASAN_CEIL_range as [CR _].
apply MemnormSafecgif.mn_safe_offimg; unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE in *; lia.
Qed.

Lemma mn_safe_ceil : forall x : word, kImgEnd <= bv_unsigned x < ASAN_CEIL -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hx. pose proof ASAN_CEIL_range as [CR _]. apply MemnormHitG.mn_safe_high. unfold TASK_SIZE. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* YFf4.D (the Recycle secondary path's window, YFf4.v:78-87).                                                      *)
Lemma YFf4_D_safe : forall (B : asyms) (TB : TfibSyms B) (ly : alayout) (X : astate) (rd : reader) (M : ARm B ly X rd)
  (k : chunk) (r : nat) (o : Z) (sm : secmap) (i : nat),
  In k (st_chunks X) -> ck_state k = CQuarantined -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
  nth_error (st_sec_arr X) i = Some r ->
  forall sp : Z, ly_stk_lo ly + YFeu.KSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall x : word, YFf4.D B ly X k r i sp (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros B TB ly X rd M k r o sm i Hk Hst Hb Hsm Hi sp Hsp IMG x Hd.
pose proof (YFf4.HIGH B TB ly X rd M IMG)
  as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22).
pose proof (YFf4.geom B ly X rd M k r o Hk Hb IMG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof (YFf4.LST B ly X rd M k r o sm i Hk Hb Hsm Hi IMG) as (y & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
destruct (YFf4.D_cases B TB ly X rd M k r o i Hk Hb Hi sp Hsp IMG _ Hd) as [C|[C|[C|[C|[C|[C|C]]]]]].
- apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
- destruct C as [_ C]. unfold YFf4.DI in C. rewrite H22 in C. apply MemnormSafecgif.mn_safe_rw.
  unfold TFIB_INST, TASK_SIZE in *. lia.
- destruct C as [C _]. exact (mn_safe_zone3 _ _ x H5 C H6).
- destruct C as [C _]. exact (mn_safe_zone3 _ _ x H3 C H4).
- destruct C as [C _]. apply (mn_safe_zone3 _ _ x Y4); [lia | exact Y5].
- destruct C as [C _]. apply MemnormSafecgif.mn_safe_offimg; unfold kLowShadowBeg, kHighMemBeg, TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE in *; lia.
- destruct C as [C _]. exact (mn_safe_zone3 _ _ x G1 C G2).
Qed.

Lemma YFf4_D_keep : forall (B : asyms) (TB : TfibSyms B) (ly : alayout) (X : astate) (rd : reader) (M : ARm B ly X rd)
  (k : chunk) (r : nat) (o : Z) (sm : secmap) (i : nat),
  In k (st_chunks X) -> ck_state k = CQuarantined -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
  nth_error (st_sec_arr X) i = Some r ->
  forall sp : Z, ly_stk_lo ly + YFeu.KSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall mem mem' : word -> option byte,
  (forall x : word, ~ YFf4.D B ly X k r i sp (bv_unsigned x) -> mem' x = mem x) -> MemnormT.memnorm_keep tfibsegs mem mem'.
Proof.
intros B TB ly X rd M k r o sm i Hk Hst Hb Hsm Hi sp Hsp IMG mem mem' F.
apply (MemnormT.memnorm_frame tfibsegs (YFf4.D B ly X k r i sp) mem mem'); [|exact F].
intros x Hx. exact (YFf4_D_safe B TB ly X rd M k r o sm i Hk Hst Hb Hsm Hi sp Hsp IMG x Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* YFf1.D (Enqueue with room in the last batch, YFf1.v:40-43).                                                     *)
Lemma YFf1_D_safe : forall (B : asyms) (ly : alayout) (X : astate) (rd : reader) (M : ARm B ly X rd)
  (lb : batch) (initr : list batch),
  rev (qc_list (st_qthread X)) = lb :: initr -> Z.of_nat (length (b_items lb)) < kBatchSlots ->
  forall sp : Z, ly_stk_lo ly + YFew.QSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall x : word, YFf1.D ly lb sp (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros B ly X rd M lb initr Hrev Hroom sp Hsp IMG x Hd.
pose proof (YFf1.HIGH B ly X rd M lb initr Hrev Hroom sp Hsp IMG)
  as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
pose proof ASAN_CEIL_range as [CR _].
destruct (YFf1.D_cases B ly X rd M lb initr Hrev Hroom sp Hsp IMG _ Hd) as [C|[C|C]].
- destruct C as [C _]. exact (mn_safe_zone3 _ _ x H3 C H4).
- destruct C as [C _]. apply mn_safe_ceil. unfold kHighMemBeg, kImgEnd in *. lia.
- apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

Lemma YFf1_D_keep : forall (B : asyms) (ly : alayout) (X : astate) (rd : reader) (M : ARm B ly X rd)
  (lb : batch) (initr : list batch),
  rev (qc_list (st_qthread X)) = lb :: initr -> Z.of_nat (length (b_items lb)) < kBatchSlots ->
  forall sp : Z, ly_stk_lo ly + YFew.QSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall mem mem' : word -> option byte,
  (forall x : word, ~ YFf1.D ly lb sp (bv_unsigned x) -> mem' x = mem x) -> MemnormT.memnorm_keep tfibsegs mem mem'.
Proof.
intros B ly X rd M lb initr Hrev Hroom sp Hsp IMG mem mem' F.
apply (MemnormT.memnorm_frame tfibsegs (YFf1.D ly lb sp) mem mem'); [|exact F].
intros x Hx. exact (YFf1_D_safe B ly X rd M lb initr Hrev Hroom sp Hsp IMG x Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* YFf2.D (Enqueue that opens a new batch, YFf2.v:72-77).                                                          *)
Lemma YFf2_D_safe : forall (B : asyms) (ly : alayout) (X : astate) (rd : reader) (M : ARm B ly X rd),
  st_cache_inited X = true -> forall l : list Z, pc_chunks (cache X kBatchClass) = l -> l <> [] ->
  forall sp : Z, ly_stk_lo ly + YFew.QSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall x : word, YFf2.D ly X l sp (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros B ly X rd M Hci l Hl Hlne sp Hsp IMG x Hd.
pose proof (YFf2.HIGH B ly X rd M Hci l Hl Hlne sp Hsp IMG)
  as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof ASAN_CEIL_range as [CR _].
destruct (YFf2.D_cases B ly X rd M Hci l Hl Hlne sp Hsp IMG _ Hd) as [C|[C|[C|C]]].
- destruct C as [C _]. exact (mn_safe_zone3 _ _ x H3 C H4).
- destruct C as [C _]. apply mn_safe_ceil. unfold kHighMemBeg, kImgEnd in *. lia.
- destruct C as (lb & initr & Hr & C). destruct (H11 lb initr Hr) as [Q1 Q2]. apply mn_safe_ceil.
  unfold kBatchBytes, kHighMemBeg, kImgEnd in *. lia.
- apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

Lemma YFf2_D_keep : forall (B : asyms) (ly : alayout) (X : astate) (rd : reader) (M : ARm B ly X rd),
  st_cache_inited X = true -> forall l : list Z, pc_chunks (cache X kBatchClass) = l -> l <> [] ->
  forall sp : Z, ly_stk_lo ly + YFew.QSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall mem mem' : word -> option byte,
  (forall x : word, ~ YFf2.D ly X l sp (bv_unsigned x) -> mem' x = mem x) -> MemnormT.memnorm_keep tfibsegs mem mem'.
Proof.
intros B ly X rd M Hci l Hl Hlne sp Hsp IMG mem mem' F.
apply (MemnormT.memnorm_frame tfibsegs (YFf2.D ly X l sp) mem mem'); [|exact F].
intros x Hx. exact (YFf2_D_safe B ly X rd M Hci l Hl Hlne sp Hsp IMG x Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* YFey.D (the Drain's transfer, YFey.v:45-50).                                                                    *)
Lemma YFey_D_safe : forall (B : asyms) (TB : TfibSyms B) (ly : alayout) (X : astate) (rd : reader) (M : ARm B ly X rd)
  (P R : list batch),
  qc_list (st_qglobal X) ++ qc_list (st_qthread X) = P ++ R ->
  forall sp : Z, ly_stk_lo ly + YFeu.DSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall x : word, YFey.D B ly X P sp (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros B TB ly X rd M P R HL sp Hsp IMG x Hd.
pose proof (YFey.HIGH B ly X rd M sp Hsp IMG)
  as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof ASAN_CEIL_range as [CR _].
destruct (YFey.D_cases B ly X rd M P R HL sp Hsp IMG _ Hd) as [C|[C|[C|C]]].
- destruct C as [C _]. exact (mn_safe_zone3 _ _ x H3 C H4).
- destruct C as [C _]. rewrite (ts_inst _ TB) in C. apply MemnormSafecgif.mn_safe_rw.
  unfold TFIB_INST, o_q_cmutex, o_q_bytes, TASK_SIZE in *. lia.
- destruct C as (b2 & Hb2 & C & _). destruct (H9 b2 Hb2) as [A1 A2]. apply mn_safe_ceil.
  unfold kBatchBytes, kHighMemBeg, kImgEnd in *. lia.
- apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

Lemma YFey_D_keep : forall (B : asyms) (TB : TfibSyms B) (ly : alayout) (X : astate) (rd : reader) (M : ARm B ly X rd)
  (P R : list batch),
  qc_list (st_qglobal X) ++ qc_list (st_qthread X) = P ++ R ->
  forall sp : Z, ly_stk_lo ly + YFeu.DSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall mem mem' : word -> option byte,
  (forall x : word, ~ YFey.D B ly X P sp (bv_unsigned x) -> mem' x = mem x) -> MemnormT.memnorm_keep tfibsegs mem mem'.
Proof.
intros B TB ly X rd M P R HL sp Hsp IMG mem mem' F.
apply (MemnormT.memnorm_frame tfibsegs (YFey.D B ly X P sp) mem mem'); [|exact F].
intros x Hx. exact (YFey_D_safe B TB ly X rd M P R HL sp Hsp IMG x Hx).
Qed.
End a.
