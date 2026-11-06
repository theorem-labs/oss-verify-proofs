(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v; 174 of its 208 lines of code are new or changed and 1271 lines of the source are left out. *)
(* text_of (fuzz_link.asan 0x87dc0) on image A: the cuts of the walk past the TABLE cut of lib/A/Prog/text_ofDefs.v,
   and the facts the segments share.

   The cuts (listing (internal path) (internal record, sha256 1c4fdcbb52aa)):
   - THE U16 CUT (+0x1a8): the selector byte b0 has bit 7 set; adv = min (c1, 3) bytes of the input are consumed
     (the cursor stands at c0 + adv, c1 - adv); a6 = b1 and a1 = b2 (the bytes at c0 + 1, c0 + 2 when consumed, else
     0); *own is 0.
   - THE MALLOC CUT (wrapper_malloc's entry, ra = 0x87ff0): n = min (v mod 320, c1 - adv) more bytes consumed;
     k <= n is the length the code copies: the first NUL of the n bytes, or n; a0 = k + 1, s1 = k, s2 = c0 + adv.
   Every cut before the malloc keeps the call's world, layout and allocator state (`to_core`).

   `to_happ`: the cursor and *own are application memory (amem_range; text_of_apre states it,
   `to_pre_happ`). The code checks them with the ASan shadow
   (+0x3c .. +0x264), and the token runner's shadow entries need their bytes outside the shadow span (YCbn.v
   shent_ok, app_apart).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 link_aaddr link_amem link_ajkit LinkWalk LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c text_ofDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition TO_CUT_U16 : Z := AF_text_of + 0x1a8.     (* lbu a3,0(a4) after the u16's bytes *)
Definition TO_MAL_RA : Z := AF_text_of + 0x230.      (* the return address of wrapper_malloc *)
Lemma TO_MAL_RA_pin : 0x821cc + TO_MAL_RA = TEXT_OF_MALLOC_RA. Proof. reflexivity. Qed.

(* the byte i of a list, as a number (0 past its end) *)
Definition bz (l : list byte) (i : nat) : Z := bv_unsigned (nth i l (Z_to_bv 8 0)).
Lemma bz_rng : forall l i, 0 <= bz l i < 256.
Proof. intros l i. unfold bz. pose proof (bv_unsigned_in_range 8 (nth i l (Z_to_bv 8 0))) as H. exact H. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).

(* the cursor and *own in application memory *)
Definition to_happ (cx : tocx) : Prop := amem_range (to_p cx) 16 /\ amem_range (to_o cx) 8.

(* what every cut before the malloc holds *)
Definition to_core (cx : tocx) (ms3 : machine_state) (md3 : Model) : Prop :=
  let regs := to_regs cx in
  let R := ms_regs ms3 in
  let m3 := rdW (to_W cx) (ms_mem ms3) in
  let rd3 := aview SEGS (w_H (to_W cx)) (ms_mem ms3) in
  let sp := to_sp cx in
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
    (to_lyc cx) (to_Sc cx) (to_W cx) (ms_mem ms3) md3 (to_k cx) /\
  m_fds md3 = m_fds (to_mdc cx) /\ m_fs md3 = m_fs (to_mdc cx) /\
  getr R 2 = w64 (sp - TO_FRAME) /\ getr R 8 = w64 (to_o cx) /\ getr R 20 = w64 SHADOW_OFF /\
  (forall r, In r TO_UNTOUCHED -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  (forall j, (j < 7)%nat ->
     rdword rd3 (sp - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 (nth j TO_SAVED 0))))) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TEXT_OF_AK <= a < sp) -> ~ to_E cx a ->
     rd3 a = aview SEGS (w_H (to_W cx)) (to_memc cx) a) /\
  (forall a, apresent (w_H (to_W cx)) (to_memc cx) a -> apresent (w_H (to_W cx)) (ms_mem ms3) a) /\
  (forall a, sp - TEXT_OF_AK <= a < sp -> apresent (w_H (to_W cx)) (ms_mem ms3) a) /\
  abuf SEGS m3 (to_p cx) 16 /\ au64_at SEGS m3 (to_o cx) 0 /\ abuf SEGS m3 (to_o cx) 8.

(* the cursor and the input at the call *)
Definition to_inp (cx : tocx) (c0 c1 : Z) (inp : list byte) : Prop :=
  au64_at SEGS (to_m0 cx) (to_p cx) c0 /\ au64_at SEGS (to_m0 cx) (to_p cx + 8) c1 /\
  0 <= c0 < 2 ^ 64 /\ 0 <= c1 < 2 ^ 64 /\
  abytes SEGS (to_m0 cx) c0 inp /\ Z.of_nat (length inp) = c1.

(* ---- THE U16 CUT (+0x1a8) ---- *)
Definition to_gi_u16 (cx : tocx) (ms3 : machine_state) (md3 : Model) : Prop :=
  let R := ms_regs ms3 in
  let m3 := rdW (to_W cx) (ms_mem ms3) in
  exists c0 c1 inp adv,
  ms_pc_val ms3 = w64 (BASE + TO_CUT_U16) /\
  to_core cx ms3 md3 /\
  to_inp cx c0 c1 inp /\
  1 <= adv <= 3 /\ adv <= c1 /\ (adv < 3 -> adv = c1) /\
  (* b0's bit 7 *)
  128 <= bz inp 0 /\
  getr R 10 = w64 (to_p cx + 8) /\ getr R 12 = w64 (to_p cx) /\
  getr R 14 = w64 (SHADOW_OFF + (to_p cx + 8) / 8) /\ getr R 15 = w64 (SHADOW_OFF + to_p cx / 8) /\
  getr R 21 = w64 (SHADOW_OFF + to_o cx / 8) /\
  getr R 16 = w64 (if 2 <=? adv then bz inp 1 else 0) /\
  getr R 11 = w64 (if adv =? 3 then bz inp 2 else 0) /\
  au64_at SEGS m3 (to_p cx) (c0 + adv) /\ au64_at SEGS m3 (to_p cx + 8) (c1 - adv).

(* ---- THE MALLOC CUT (wrapper_malloc's entry) ---- *)
Definition to_gi_mal (cx : tocx) (ms3 : machine_state) (md3 : Model) : Prop :=
  let R := ms_regs ms3 in
  let m3 := rdW (to_W cx) (ms_mem ms3) in
  exists c0 c1 inp adv n k,
  ms_pc_val ms3 = w64 (pa_sigma LS___interceptor_trampoline_malloc) /\
  getr R 1 = w64 (BASE + TO_MAL_RA) /\
  to_core cx ms3 md3 /\
  to_inp cx c0 c1 inp /\
  1 <= adv <= 3 /\ adv + n <= c1 /\ 0 <= k <= n /\ n <= 319 /\
  ~ In (zb 0) (firstn (Z.to_nat k) (skipn (Z.to_nat adv) inp)) /\
  getr R 10 = w64 (k + 1) /\ getr R 9 = w64 k /\ getr R 18 = w64 (c0 + adv) /\
  getr R 21 = w64 (SHADOW_OFF + to_o cx / 8) /\
  au64_at SEGS m3 (to_p cx) (c0 + adv + n) /\ au64_at SEGS m3 (to_p cx + 8) (c1 - adv - n).

Definition to_u16_obl : Prop := to_from SK B MT CTX to_gi_u16.
Definition to_mal_obl : Prop := to_from SK B MT CTX to_gi_mal.

Hypothesis LAWS : AR_laws SEGS B.

(* ---- the contract's premises by name ---- *)
Lemma to_pre_jc : forall cx, to_pre SK B MT CTX cx ->
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
    (to_lyc cx) (to_Sc cx) (to_W cx) (to_memc cx) (to_mdc cx) (to_k cx).
Proof. intros cx (HA & _). unfold apre in HA. tauto. Qed.

Lemma to_pre_gx : forall cx, to_pre SK B MT CTX cx -> gx_ok SEGS B (to_G cx).
Proof. intros cx (HA & _). unfold apre in HA. tauto. Qed.

Lemma to_pre_aro : forall cx, to_pre SK B MT CTX cx ->
  arodata_okP SEGS (to_rlo cx) (to_rhi cx) B (aview SEGS (w_H (to_W cx)) (to_memc cx)).
Proof. intros cx (HA & _). unfold apre in HA. tauto. Qed.

Lemma to_pre_P : forall cx, to_pre SK B MT CTX cx ->
  text_of_apre SEGS (to_rlo cx) (to_rhi cx) B (to_regs cx) (to_m0 cx).
Proof. intros cx (_ & _ & _ & _ & _ & _ & _ & HP). exact HP. Qed.

Lemma to_pre_happ : forall cx, to_pre SK B MT CTX cx -> to_happ cx.
Proof.
  intros cx HPX. pose proof (to_pre_P cx HPX) as (c0 & c1 & inp & _ & _ & _ & _ & _ & _ & _ & Hp & _ & _ & _ & Ho & _).
  split; [exact Hp | exact Ho].
Qed.

(* *own's shadow hull, visible at the call (a conjunct of text_of_apre) *)
Lemma to_pre_ho : forall cx, to_pre SK B MT CTX cx -> shadow_hull_vis (ard SEGS (to_m0 cx)) (to_o cx) 8.
Proof.
  intros cx HPX.
  pose proof (to_pre_P cx HPX) as (c0 & c1 & inp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hho & _).
  exact Hho.
Qed.

(* the call's window lies in high memory, at or above the allocator's ceiling *)
Lemma to_win : forall cx, to_pre SK B MT CTX cx ->
  alloc_ceiling <= to_sp cx - TEXT_OF_AK /\ to_sp cx <= 2 ^ 47 /\ to_sp cx mod 16 = 0 /\
  to_sp0 cx - to_STK cx <= to_sp cx - TEXT_OF_AK /\ to_sp cx <= to_sp0 cx.
Proof.
  intros cx HPX. pose proof HPX as ((HJ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _) & _).
  pose proof (aj_window_bounds SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hceil & H47 & HSTK & HXO).
  unfold to_sp. repeat split; lia.
Qed.

(* a byte at or above the ceiling outside the window, or below kLowMemEnd, is outside the window *)
Lemma to_low_not_win : forall cx a, to_pre SK B MT CTX cx -> a < 0x7fff7f800000 ->
  ~ (to_sp cx - TEXT_OF_AK <= a < to_sp cx).
Proof.
  intros cx a HPX Ha. pose proof (to_win cx HPX) as (W1 & _).
  pose proof asan_consts as ((C1a & C1b) & _ & _ & _ & C5). lia.
Qed.

(* a byte of the write set is application memory (given to_happ) *)
Lemma to_E_app : forall cx a, to_happ cx -> to_E cx a -> a < kLowMemEnd \/ kHighMemBeg <= a < kHighMemEnd.
Proof.
  intros cx a (Hp & Ho) (r & Hin & Hr). unfold to_wr, text_of_awr in Hin.
  unfold amem_range, to_p, to_o in *. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; lia.
Qed.

(* a low-shadow byte is outside the write set *)
Lemma to_E_not_shadow : forall cx a, to_happ cx -> SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> ~ to_E cx a.
Proof.
  intros cx a HH Ha HE. destruct (to_E_app cx a HH HE) as [H | H];
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5); unfold SHADOW_OFF in *; lia.
Qed.

(* ---- the table at a cut before the malloc ---- *)
Lemma to_table_part : forall cx (ms3 : machine_state),
  to_pre SK B MT CTX cx -> to_happ cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (to_sp cx - TEXT_OF_AK <= a < to_sp cx) -> ~ to_E cx a ->
     aview SEGS (w_H (to_W cx)) (ms_mem ms3) a = aview SEGS (w_H (to_W cx)) (to_memc cx) a) ->
  range_addressable (aview SEGS (w_H (to_W cx)) (ms_mem ms3)) SHADOW_OFF LA_TEXTS (8 * TEXTS_N) /\
  (forall i, 0 <= i < TEXTS_N -> exists q s,
     au64_at SEGS (to_m0 cx) (LA_TEXTS + 8 * i) q /\
     au64_at SEGS (rdW (to_W cx) (ms_mem ms3)) (LA_TEXTS + 8 * i) q /\ 0 < q < 2 ^ 64 /\
     acstr_at SEGS (rdW (to_W cx) (ms_mem ms3)) q s /\ Z.of_nat (length s) < 320 /\
     text_of_ro SEGS (to_rlo cx) (to_rhi cx) B q (Z.of_nat (length s) + 1)).
Proof.
  intros cx ms3 HPX HH UN.
  pose proof (to_pre_P cx HPX) as HP.
  destruct HP as (c0 & c1 & inp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HRT & HAPT & HAOT & HENT & _).
  pose proof (to_pre_aro cx HPX) as HRO.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : forall a, 0 <= a < kLowMemEnd -> ~ to_E cx a ->
     mbyte SEGS (rdW (to_W cx) (ms_mem ms3)) a = mbyte SEGS (to_m0 cx) a).
  { intros a Ha HE. apply (mbyte_of_aview_eq SEGS _ _ _ _ a a).
    apply UN; [lia | exact (to_low_not_win cx a HPX ltac:(lia)) | exact HE]. }
  assert (HnE : forall a n, (apart (to_p cx) 16 a n) -> apart (to_o cx) 8 a n ->
            forall x, a <= x < a + n -> ~ to_E cx x).
  { intros a n H1 H2 x Hx (r & Hin & Hr). unfold to_wr, text_of_awr in Hin. unfold apart, to_p, to_o in *.
    destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; lia. }
  split.
  - intros x Hx. destruct (HRT x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
    rewrite UN; [exact Hv | | | ].
    + unfold shadow_of_addr, LA_TEXTS, TEXTS_N, SHADOW_OFF in *. lia.
    + apply (to_low_not_win cx _ HPX). unfold shadow_of_addr, LA_TEXTS, TEXTS_N, SHADOW_OFF in *. lia.
    + apply (to_E_not_shadow cx _ HH). unfold shadow_of_addr, LA_TEXTS, TEXTS_N, SHADOW_OFF in *. lia.
  - intros i Hi. destruct (HENT i Hi) as (q & s & Hq & Hq64 & Hs & Hsl & Hro & Hap & Hao).
    exists q, s.
    split; [exact Hq|].
    split.
    { intros j Hj. rewrite HK; [exact (Hq j Hj) | unfold LA_TEXTS, TEXTS_N in *; lia |].
      apply (HnE LA_TEXTS (8 * TEXTS_N) HAPT HAOT). unfold TEXTS_N in *. lia. }
    split; [exact Hq64|].
    split.
    { destruct Hs as ((Hs0 & Hs1 & Hsb) & Hnz). split; [|exact Hnz].
      split; [exact Hs0|]. split; [exact Hs1|].
      intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
      assert (Hjr : 0 <= Z.of_nat j < Z.of_nat (length s) + 1) by lia.
      destruct (Hro (Z.of_nat j) Hjr) as (Hin & Hns & Herr).
      (* the byte is visible at the call, so read-only image, so low memory *)
      assert (Hv : aview SEGS (w_H (to_W cx)) (to_memc cx) (q + Z.of_nat j) <> None).
      { unfold aview. change (mrestrict (w_H (to_W cx)) (to_memc cx)) with (to_m0 cx).
        rewrite (Hsb j ltac:(rewrite length_app; cbn [length]; lia)).
        rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia). cbn. discriminate. }
      rewrite (HRO _ Hin Hns Herr) in Hv.
      assert (Himg : in_img SEGS (q + Z.of_nat j)).
      { apply (seg_rom_in_img SEGS); [rewrite length_app in Hs1; cbn [length] in Hs1; lia|].
        intros E0. rewrite E0 in Hv. exact (Hv eq_refl). }
      pose proof (pa_segs_low _ Himg) as Hlow.
      rewrite HK; [exact (Hsb j ltac:(rewrite length_app; cbn [length]; lia)) | lia |].
      apply (HnE q (Z.of_nat (length s) + 1) Hap Hao). lia. }
    split; [exact Hsl | exact Hro].
Qed.

End b.
End a.
