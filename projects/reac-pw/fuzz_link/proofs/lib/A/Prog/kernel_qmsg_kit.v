(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 471 of its 522 lines of code are new or changed and 1254 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the kit of kernel's queueing steps (the queueing and raw segments of kernel's walk,
   lib/A/Prog/kernel_qmsg.v and kernel_raw*.v): what a chunk's queueing needs beside kernel_defs.v, kernel_kit.v and
   kernel_msg0_kit.v.
   - g_nl at a cut: the shadow facts of a range of g_nl (kq_gnl_ra: the read set's shadow, moved to the cut by
     kernel_kit.v kn_rd_saddr; the hull by LinkWalkShadow.v img_sh_eq: g_nl is an image object); g_nl's bytes as one
     list at any memory (kq_anlk: writable at any memory by KernImg's ki_gnl_wseg); kgnl after a step that writes
     only chunk bytes (kq_gnl_keep) or also n_chunks := j + 1 and chunk_len[j] := v (kq_gnl_next);
   - the cut after a step that writes g_nl (kq_kat_g: kernel_kit.v's part lemmas, kgnl given);
   - F's shadow after meta_fill_<v> on w1's or w2's 0x202 shadow bytes (kq_kshadow_w1 / _w2) and the cut after it
     (kq_land_mf);
   - the two calls as lemmas over kernel's facts: meta_fill_<v> on 0x202 bytes of F's shadow (kq_call_mf, LinkWalkSide.v
     aj_gx_set_shadow_at) and checked_memcpy of a buffer of F into chunk j of g_nl (kq_call_gcpy, link_ajkit.v
     aj_gx_intrin_at; the destination bytes are kernel's write set, allowed by apre's ajw and writable by
     ki_gnl_wseg; the source is F's, present and outside the callee's window).
   Section hypotheses: LAWS, LV (g_nl's atom), TB (the read set's shadow at a cut), KI (g_nl's writability), AMEMCPY.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* every lemma of the Section below takes all its hypotheses (one calling convention for the lanes) *)
Set Default Proof Using "All".
Open Scope Z_scope.

(* the shadow base atom and the shadow band of the runs (link-a/plan/PLAN.md (internal record, sha256 2ce66196196e)) *)
Definition kq_Bx : sv := SOff 20 0.
Definition kq_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* a region list with no writable window: no byte in a writable range, and a run over it keeps the memory *)
Lemma kq_no_wrange : forall E rs a,
  in_wrange E rs a -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> False.
Proof.
  intros E rs a (r & Hin & Hr) Hrs. rewrite forallb_forall in Hrs. specialize (Hrs r Hin).
  apply Z.leb_le in Hrs. lia.
Qed.

Lemma kq_mem_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> m' = m.
Proof.
  intros E rs m m' Hfr Hrs. apply functional_extensionality. intros x. apply Hfr.
  intros Hx. exact (kq_no_wrange E rs _ Hx Hrs).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.                                (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                              (* kernel_img_syms at the image *)
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.   (* checked_memcpy: AE2q.v asan_memcpy_realizes *)
Hypothesis LV : LinkVals.

(* the env of a run's start: the registers, then the extra atoms from 32 on; g_nl is the image object A_OBJ 2 *)
Lemma kq_E_32 : forall (ms : machine_state) x rest,
  ew (Eimg (Ereg (ms_regs ms) (w64 x :: rest))) 32%nat = w64 x.
Proof. intros ms x rest. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ms_regs ms) (w64 x :: rest) 0). Qed.

Lemma kq_E_243 : forall E, ew (Eimg E) 243%nat = Z_to_bv 64 LA_G_NL.
Proof.
  intros E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 243%nat with (A_OBJ 2).
  rewrite (lv_obj LV 2%nat) by (unfold link_nobj; lia). change (link_obj 2) with 6146752. reflexivity.
Qed.

Lemma kq_U243 : forall E, bv_unsigned (ew (Eimg E) 243%nat) = LA_G_NL.
Proof. intros E. rewrite kq_E_243. apply unsigned_lit_small. unfold LA_G_NL. lia. Qed.

(* g_nl's chunk area, its counters and its chunk lengths are kernel's write set *)
Lemma kq_kE_gnl : forall (cx : kcx) a, LA_G_NL <= a < LA_G_NL + NK_OPEN -> kE cx a.
Proof.
  intros cx a Ha. exists (LA_G_NL + NK_CHUNK, LA_G_NL + NK_OPEN). split.
  - unfold kernel_awr. cbn [In]. left. reflexivity.
  - cbn [fst snd]. unfold NK_CHUNK. lia.
Qed.

(* a present byte is visible *)
Lemma kq_aview_some : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* a visible byte stays visible when the restricted memory grows *)
Lemma kq_aview_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview SEGS H m a <> None -> aview SEGS H m' a <> None.
Proof.
  intros H m m' a Hg Hv. unfold aview, mbyte in *. specialize (Hg (Z_to_bv 64 a)).
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E1;
    destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|] eqn:E2; cbn in Hv |- *;
    try discriminate; try exact Hv.
  exfalso. apply Hg; [discriminate | reflexivity].
Qed.

(* a step that writes nothing: no byte meets the empty set *)
Lemma kq_miss0 : forall (cx : kcx) fpos sl n,
  kslots_okb sl = true -> kX_miss cx fpos sl n (fun _ => False).
Proof.
  intros cx fpos sl n Hok. unfold kX_miss.
  split; [intros a _ H; exact H|].
  split; [intros ov Hov; split; [exact (kslots_okb_spec sl Hok ov Hov) | intros a _ H; exact H]|].
  repeat split; intros a _ H; exact H.
Qed.

(* ---- g_nl at a cut ---- *)

(* the shadow facts of a range of g_nl: addressable (the read set's, kn_rd_saddr) and its hull visible (an image
   object's shadow is visible at every AR state, img_sh_eq) *)
Lemma kq_gnl_ra : forall cx fpos k2 ly3 S3 W3 ms3 md3 d n,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  LA_G_NL <= d -> d + n <= LA_G_NL + NK_SIZE -> 0 <= n ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF d n /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) d n.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 d n HB HJ HJB HKK Hd1 Hd2 Hn.
  pose proof HB as (_ & _ & HKP & _). destruct HKP as (kbs & _ & _ & Hra & _).
  split.
  - apply ra_of_saddr. intros x Hx.
    apply (kn_rd_saddr SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 x HB HJ HJB HKK).
    + right. right. left. lia.
    + apply (saddr_of_ra _ LA_G_NL NK_SIZE x); [|lia]. rewrite <- ard_aview. exact Hra.
  - intros s Hs. pose proof HJ as HAR3. apply ajournal_gx_AR in HAR3. pose proof HAR3 as (M3 & _).
    assert (Hsx : SHADOW_OFF + 0x2000 <= s < SHADOW_OFF + 0xca800)
      by (unfold shadow_addr, LA_G_NL, NK_SIZE, SHADOW_OFF in *; lia).
    destruct (img_sh_eq B TB ly3 S3 _ ly3 S3 _ s M3 M3 Hsx) as [_ Hne]. exact Hne.
Qed.

(* g_nl's bytes at any memory where each is visible: one list, writable by KernImg *)
Lemma kq_anlk : forall (W4 : world SEGS) (m4 : word -> option byte),
  (forall i, 0 <= i < NK_SIZE -> aview SEGS (w_H W4) m4 (LA_G_NL + i) <> None) ->
  anlk_at SEGS (rdW W4 m4) LA_G_NL (abytes_of SEGS (rdW W4 m4) LA_G_NL (Z.to_nat NK_SIZE)).
Proof.
  intros W4 m4 Hv.
  assert (HL : length (abytes_of SEGS (rdW W4 m4) LA_G_NL (Z.to_nat NK_SIZE)) = Z.to_nat NK_SIZE)
    by apply abytes_of_length.
  split; [split|].
  - apply abytes_of_abytes; [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE; lia |].
    intros i Hi. specialize (Hv (Z.of_nat i) ltac:(unfold NK_SIZE in *; lia)).
    unfold aview in Hv.
    destruct (mbyte SEGS (mrestrict (w_H W4) m4) (LA_G_NL + Z.of_nat i)) as [b|];
      [exists b; reflexivity | exfalso; apply Hv; reflexivity].
  - rewrite HL. intros i Hi.
    apply (writable_at_of_wseg SEGS _ LA_G_NL NK_SIZE);
      [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE; lia | exact (ki_gnl_wseg _ _ KI) |].
    unfold NK_SIZE in *. lia.
  - rewrite HL. unfold NK_SIZE. lia.
Qed.

(* a byte of that list the step did not change is the old list's *)
Lemma kq_nth_same : forall (W3 W4 : world SEGS) m3 m4 kbs3 (i : nat),
  abytes SEGS (rdW W3 m3) LA_G_NL kbs3 -> (i < length kbs3)%nat -> length kbs3 = Z.to_nat NK_SIZE ->
  aview SEGS (w_H W4) m4 (LA_G_NL + Z.of_nat i) = aview SEGS (w_H W3) m3 (LA_G_NL + Z.of_nat i) ->
  nth_error (abytes_of SEGS (rdW W4 m4) LA_G_NL (Z.to_nat NK_SIZE)) i = nth_error kbs3 i.
Proof.
  intros W3 W4 m3 m4 kbs3 i (_ & _ & Hb) Hi Hl Hv.
  pose proof (Hb i Hi) as Hbi.
  destruct (nth_error kbs3 i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  apply abytes_of_nth; [lia|].
  rewrite (kn_mbyte_of_aview SEGS (w_H W3) (w_H W4) m3 m4 _ _ Hv). exact Hbi.
Qed.

(* every byte of g_nl is visible at a cut *)
Lemma kq_gnl_vis : forall cx (W3 : world SEGS) ms3 g, kgnl_at cx W3 ms3 g ->
  forall i, 0 <= i < NK_SIZE -> aview SEGS (w_H W3) (ms_mem ms3) (LA_G_NL + i) <> None.
Proof.
  intros cx W3 ms3 g HG i Hi.
  assert (H : exists bs, abytes SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs /\ Z.of_nat (length bs) = NK_SIZE).
  { destruct g as [j|]; cbn [kgnl_at] in HG.
    - destruct HG as (kbs3 & ((HAB & _) & HAL) & _). exists kbs3. split; assumption.
    - destruct HG as ((HAB & _) & HAL). exists (k_kbs cx). split; assumption. }
  destruct H as (bs & (_ & _ & Hb) & Hl).
  pose proof (Hb (Z.to_nat i) ltac:(lia)) as Hbi. rewrite Z2Nat.id in Hbi by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  unfold aview. rewrite Hbi. cbn. discriminate.
Qed.

(* g_nl after a step that wrote, from NK_CHUNK_LEN on, at most n_chunks and chunk_len[j]: the new counter is j (no
   chunk queued) or j + 1 with chunk_len[j] = v in 0..4096 (chunk j queued) *)
Lemma kq_gnl_next : forall cx (W3 : world SEGS) ms3 ms4 j j' v,
  kgnl_at cx W3 ms3 (Some j) -> 0 <= j < 64 ->
  (j' = j \/ (j' = j + 1 /\ 0 <= v <= NL_CHUNK_MAX)) ->
  (forall i, 0 <= i < NK_SIZE -> aview SEGS (w_H W3) (ms_mem ms4) (LA_G_NL + i) <> None) ->
  (forall i, NK_CHUNK_LEN <= i < NK_SIZE -> ~ (NK_CHUNK_LEN + 8 * j <= i < NK_CHUNK_LEN + 8 * j + 8) ->
     ~ (NK_N_CHUNKS <= i < NK_N_CHUNKS + 4) ->
     aview SEGS (w_H W3) (ms_mem ms4) (LA_G_NL + i) = aview SEGS (w_H W3) (ms_mem ms3) (LA_G_NL + i)) ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + NK_N_CHUNKS) 4 j' ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (LA_G_NL + (NK_CHUNK_LEN + 8 * j)) 8 v ->
  kgnl_at cx W3 ms4 (Some j').
Proof.
  intros cx W3 ms3 ms4 j j' v HG Hj Hj' Hv4 UNg Hn4 Hc4.
  cbn [kgnl_at] in HG |- *. destruct HG as (kbs3 & ((HAB & _) & HAL) & HK).
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
  assert (Hjr : j <= j' <= j + 1) by (destruct Hj' as [-> | (-> & _)]; lia).
  pose proof (kq_anlk W3 (ms_mem ms4) Hv4) as HN4.
  set (kbs4 := abytes_of SEGS (rdW W3 (ms_mem ms4)) LA_G_NL (Z.to_nat NK_SIZE)) in *.
  assert (HL4 : length kbs4 = Z.to_nat NK_SIZE) by apply abytes_of_length.
  assert (HL3 : length kbs3 = Z.to_nat NK_SIZE) by (unfold NK_SIZE in *; lia).
  assert (SAME : forall i : nat, NK_CHUNK_LEN <= Z.of_nat i < NK_SIZE ->
            ~ (NK_CHUNK_LEN + 8 * j <= Z.of_nat i < NK_CHUNK_LEN + 8 * j + 8) ->
            ~ (NK_N_CHUNKS <= Z.of_nat i < NK_N_CHUNKS + 4) ->
            nth_error kbs4 i = nth_error kbs3 i).
  { intros i H1 H2 H3. apply (kq_nth_same W3 W3 (ms_mem ms3) (ms_mem ms4) kbs3 i HAB);
      [unfold NK_SIZE in *; lia | exact HL3 |].
    apply UNg; [exact H1 | exact H2 | exact H3]. }
  assert (RD : forall off n, NK_CHUNK_LEN <= off -> 0 <= n -> off + n <= NK_SIZE ->
            (forall i, off <= i < off + n -> ~ (NK_CHUNK_LEN + 8 * j <= i < NK_CHUNK_LEN + 8 * j + 8) /\
               ~ (NK_N_CHUNKS <= i < NK_N_CHUNKS + 4)) ->
            rdn kbs4 off n = rdn kbs3 off n).
  { intros off n H1 H2 H3 H4.
    apply rdn_agree; [unfold NK_CHUNK_LEN in *; lia | exact H2 | rewrite HL3; unfold NK_SIZE in *; lia
                     | rewrite HL4; unfold NK_SIZE in *; lia |].
    intros k Hk.
    assert (Hk' : off <= Z.of_nat (Z.to_nat off + k) < off + n) by (unfold NK_CHUNK_LEN in *; lia).
    destruct (H4 _ Hk') as (H5 & H6).
    apply SAME; [unfold NK_CHUNK_LEN, NK_SIZE in *; lia | exact H5 | exact H6]. }
  exists kbs4. split; [exact HN4|].
  unfold kgnl. split; [rewrite HL4; unfold NK_SIZE; lia|].
  split.
  { rewrite <- K2. apply lw_list_ext; [rewrite !length_skipn, HL4, HL3; reflexivity|].
    intros k Hk. rewrite length_skipn, HL4 in Hk. rewrite !lw_nth_error_skipn.
    apply SAME; unfold NK_CHUNK_LEN, NK_SIZE, NK_OPEN, NK_N_CHUNKS in *; lia. }
  split.
  { unfold nk_n_chunks, fld_u32. change (rdn kbs4 NK_N_CHUNKS 4) with (rdn kbs4 NK_N_CHUNKS (Z.of_nat 4)).
    apply rdn_of_vals; [unfold NK_N_CHUNKS; lia | rewrite HL4; unfold NK_N_CHUNKS, NK_SIZE; lia | cbn; clear Hj'; lia |].
    intros k Hk. apply abytes_of_val; [unfold NK_N_CHUNKS, NK_SIZE; lia | unfold NK_N_CHUNKS; lia | exact Hk | exact Hn4]. }
  assert (R4 : forall off, NK_N_CHUNKS + 4 <= off -> off + 4 <= NK_SIZE -> rdn kbs4 off 4 = rdn kbs3 off 4).
  { intros off H1 H2. apply RD; [unfold NK_N_CHUNKS, NK_CHUNK_LEN in *; lia | lia | exact H2 |].
    intros i Hi. unfold NK_N_CHUNKS, NK_CHUNK_LEN in *. split; lia. }
  unfold nk_next, nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32 in *.
  rewrite (R4 NK_NEXT) by (unfold NK_NEXT, NK_N_CHUNKS, NK_SIZE; lia).
  rewrite (R4 NK_END_ERRNO) by (unfold NK_END_ERRNO, NK_N_CHUNKS, NK_SIZE; lia).
  rewrite (R4 NK_SOCKET_ERRNO) by (unfold NK_SOCKET_ERRNO, NK_N_CHUNKS, NK_SIZE; lia).
  rewrite (R4 NK_SEND_ERRNO) by (unfold NK_SEND_ERRNO, NK_N_CHUNKS, NK_SIZE; lia).
  split; [exact K4|]. split; [exact K5|]. split; [exact K6|]. split; [exact K7|].
  intros i Hi. unfold fld_u64 in *.
  destruct (Z.lt_ge_cases i j) as [Hij | Hij].
  - rewrite (RD (NK_CHUNK_LEN + 8 * i) 8); [exact (K8 i ltac:(lia)) | lia | lia | unfold NK_CHUNK_LEN, NK_SIZE; lia |].
    intros q Hq. unfold NK_N_CHUNKS, NK_CHUNK_LEN in *. split; lia.
  - assert (Hji : i = j /\ 0 <= v <= NL_CHUNK_MAX) by (destruct Hj' as [-> | (-> & Hv)]; [lia | split; [lia | exact Hv]]).
    destruct Hji as (-> & Hv).
    change (rdn kbs4 (NK_CHUNK_LEN + 8 * j) 8) with (rdn kbs4 (NK_CHUNK_LEN + 8 * j) (Z.of_nat 8)).
    rewrite (rdn_of_vals kbs4 (NK_CHUNK_LEN + 8 * j) 8 v);
      [exact Hv | unfold NK_CHUNK_LEN; lia | rewrite HL4; unfold NK_CHUNK_LEN, NK_SIZE; lia
      | unfold NL_CHUNK_MAX in Hv; cbn; lia |].
    intros k Hk. apply abytes_of_val; [unfold NK_CHUNK_LEN, NK_SIZE; lia | unfold NK_CHUNK_LEN; lia | exact Hk | exact Hc4].
Qed.

(* g_nl after a step that wrote only chunk bytes (below NK_CHUNK_LEN) *)
Lemma kq_gnl_keep : forall cx (W3 : world SEGS) ms3 ms4 j,
  kgnl_at cx W3 ms3 (Some j) -> 0 <= j < 64 ->
  (forall i, 0 <= i < NK_SIZE -> aview SEGS (w_H W3) (ms_mem ms4) (LA_G_NL + i) <> None) ->
  (forall i, NK_CHUNK_LEN <= i < NK_SIZE ->
     aview SEGS (w_H W3) (ms_mem ms4) (LA_G_NL + i) = aview SEGS (w_H W3) (ms_mem ms3) (LA_G_NL + i)) ->
  kgnl_at cx W3 ms4 (Some j).
Proof.
  intros cx W3 ms3 ms4 j HG Hj Hv UN.
  pose proof HG as HG'. cbn [kgnl_at] in HG'. destruct HG' as (kbs3 & ((HAB & _) & HAL) & HK).
  assert (HL3 : (Z.to_nat NK_N_CHUNKS + 4 <= length kbs3)%nat) by (unfold NK_N_CHUNKS, NK_SIZE in *; lia).
  assert (HL3' : (Z.to_nat (NK_CHUNK_LEN + 8 * j) + 8 <= length kbs3)%nat)
    by (unfold NK_CHUNK_LEN, NK_SIZE in *; lia).
  apply (kq_gnl_next cx W3 ms3 ms4 j j (rdn kbs3 (NK_CHUNK_LEN + 8 * j) 8) HG Hj (or_introl eq_refl) Hv).
  - intros i H1 _ _. exact (UN i H1).
  - apply (kn_val_mem_move W3 (ms_mem ms3) (ms_mem ms4)).
    + destruct HK as (_ & _ & K3 & _). rewrite <- K3. unfold nk_n_chunks, fld_u32.
      exact (val_mem_u32 SEGS _ _ _ NK_N_CHUNKS HAB ltac:(unfold NK_N_CHUNKS; lia) HL3).
    + intros i Hi. rewrite <- !Z.add_assoc. apply UN.
      unfold NK_N_CHUNKS, NK_CHUNK_LEN, NK_SIZE. lia.
  - apply (kn_val_mem_move W3 (ms_mem ms3) (ms_mem ms4)).
    + exact (val_mem_u64 SEGS _ _ _ (NK_CHUNK_LEN + 8 * j) HAB ltac:(unfold NK_CHUNK_LEN; lia) HL3').
    + intros i Hi. rewrite <- !Z.add_assoc. apply UN.
      unfold NK_CHUNK_LEN, NK_SIZE. lia.
Qed.

(* ---- the cut after a step that also wrote g_nl: the part lemmas of kernel_kit.v, g_nl given ---- *)
Lemma kq_kat_g : forall (Xo Xg : Z -> Prop) cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' g'
    W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> (length sh <= 2048)%nat ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Xo a -> ~ Xg a ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, Xo a -> kX_in cx fpos a) ->
  kX_miss cx fpos sl' (Z.of_nat (length sh)) Xo ->
  (forall a, Xg a -> LA_G_NL <= a < LA_G_NL + NK_OPEN) ->
  kgnl_at cx W4 ms4 g' ->
  kat B cx fpos pc' rl' sl' sh live adv g' k2 ly3 S3 W4 ms4 md4.
Proof.
  intros Xo Xg cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' g' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hsh Hfds Hfs UN0 HP HXin HXm HXg HGN'.
  destruct HXm as (Msv & Msl & Mhd & Mfl & Msh & Mcu & Mgn & Mla).
  destruct HK as (_ & _ & _ & HSAV & HFR & HSH & HSL & HJB & HKEPT & HCUR & _ & HLA).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof (kn_apre SK B cx HB) as (Agnl & _).
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity.
  rewrite kn_fsb8 in F2, F5. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => Xo a \/ Xg a) a ->
            aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hx. apply UN0; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; exact H]. }
  assert (NG : forall a, Xg a -> ~ (LA_G_NL <= a < LA_G_NL + NK_OPEN) -> False) by (intros a H1 H2; exact (H2 (HXg a H1))).
  unfold kat.
  refine (conj HMS (conj HR0 (conj HRL (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj HGN' _))))))))))).
  - apply (ksaved_frame SK B (fun a => Xo a \/ Xg a) cx W3 ms3 W4 ms4 HB UN); [|exact HSAV].
    intros a Ha [Hx | Hx]; [exact (Msv a Ha Hx)|]. apply (NG a Hx). unfold LA_G_NL, NK_OPEN. rewrite HK8 in S1. lia.
  - apply (kframe_frame B LAWS (fun a => Xo a \/ Xg a) cx fpos live k2 ly3 S3 md3 W3 ms3 W4 ms4 HJB UN HP);
      [| |exact HFR].
    + intros a Ha [Hx | Hx]; [exact (Mhd a Ha Hx)|]. apply (NG a Hx). unfold LA_G_NL, NK_OPEN. lia.
    + intros a Ha [Hx | Hx]; [exact (Mfl a Ha Hx)|]. apply (NG a Hx). rewrite kn_fsb8 in Ha. unfold LA_G_NL, NK_OPEN. lia.
  - apply (kshadow_frame B LAWS (fun a => Xo a \/ Xg a) cx fpos sh k2 ly3 S3 md3 W3 ms3 W4 ms4 HJB UN Hsh);
      [|exact HSH].
    intros a Ha [Hx | Hx]; [exact (Msh a Ha Hx)|]. apply (NG a Hx).
    unfold LA_G_NL, NK_OPEN, kHighMemBeg, SHADOW_OFF in *. lia.
  - apply (kslots_frame SK B (fun a => Xo a \/ Xg a) cx sl sl' W3 ms3 W4 ms4 HB UN Hsl); [|exact HSL].
    intros ov Hov. destruct (Msl ov Hov) as (Ho & Hn). split; [exact Ho|].
    intros a Ha [Hx | Hx]; [exact (Hn a Ha Hx)|]. apply (NG a Hx). unfold LA_G_NL, NK_OPEN. rewrite HK8 in S1. lia.
  - exact (kjbk_md B cx fpos k2 ly3 S3 md3 md4 HJB Hfds Hfs).
  - apply (kkept_frame SK B LAWS (fun a => Xo a \/ Xg a) cx fpos k2 ly3 S3 md3 W3 ms3 W4 ms4 HB HJB UN HP);
      [|exact HKEPT].
    intros a [Hx | Hx]; [exact (HXin a Hx)|]. left. exact (kq_kE_gnl cx a (HXg a Hx)).
  - apply (kcursor_frame SK B LAWS (fun a => Xo a \/ Xg a) cx adv W3 ms3 W4 ms4 HB UN HP); [|exact HCUR].
    intros a Ha [Hx | Hx]; [exact (Mcu a Ha Hx)|]. apply (NG a Hx). unfold apart_gnl in Agnl.
    unfold NK_SIZE, NK_OPEN in *. lia.
  - apply (kla_frame (fun a => Xo a \/ Xg a) W3 ms3 W4 ms4 UN HP); [|exact HLA].
    intros a Ha [Hx | Hx]; [exact (Mla a Ha Hx)|]. apply (NG a Hx).
    unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE, LA_G_NL, NK_OPEN in *. lia.
Qed.

(* ---- F's shadow after meta_fill_<v> on w1's / w2's 0x202 shadow bytes ---- *)
Lemma kq_kshadow_w2 : forall cx fpos W3 ms3 ms' s1v s2v r v,
  kshadow cx fpos W3 ms3 (kfsh s1v s2v r) ->
  (forall i, 0 <= i < 0x448 -> ~ (0x226 <= i < 0x428) ->
     aview SEGS (w_H W3) (ms_mem ms') (kFSH cx fpos + i) = aview SEGS (w_H W3) (ms_mem ms3) (kFSH cx fpos + i)) ->
  (forall i, 0 <= i < 0x202 -> aview SEGS (w_H W3) (ms_mem ms') (kFSH cx fpos + 0x226 + i) = Some v) ->
  kshadow cx fpos W3 ms' (kfsh s1v v r).
Proof.
  intros cx fpos W3 ms3 ms' s1v s2v r v Hsh Hk H0 i Hi. rewrite kfsh_length in Hi.
  rewrite kn_kfsh_nth.
  destruct (Nat.ltb_spec i 0x226) as [Hq1|Hq1].
  - rewrite Hk by lia. rewrite (Hsh i ltac:(rewrite kfsh_length; lia)). rewrite kn_kfsh_nth.
    destruct (Nat.ltb_spec i 4); [reflexivity|]. destruct (Nat.ltb_spec i 0x206); [reflexivity|].
    destruct (Nat.ltb_spec i 0x226); [reflexivity | lia].
  - destruct (Nat.ltb_spec i 4); [lia|]. destruct (Nat.ltb_spec i 0x206); [lia|].
    destruct (Nat.ltb_spec i 0x428) as [Hq2|Hq2].
    + replace (kFSH cx fpos + Z.of_nat i) with (kFSH cx fpos + 0x226 + (Z.of_nat i - 0x226)) by lia.
      apply H0. lia.
    + rewrite Hk by lia. rewrite (Hsh i ltac:(rewrite kfsh_length; lia)). rewrite kn_kfsh_nth.
      destruct (Nat.ltb_spec i 4); [lia|]. destruct (Nat.ltb_spec i 0x206); [lia|].
      destruct (Nat.ltb_spec i 0x226); [lia|]. destruct (Nat.ltb_spec i 0x428); [lia | reflexivity].
Qed.

Lemma kq_kshadow_w1 : forall cx fpos W3 ms3 ms' s1v s2v r v,
  kshadow cx fpos W3 ms3 (kfsh s1v s2v r) ->
  (forall i, 0 <= i < 0x448 -> ~ (4 <= i < 0x206) ->
     aview SEGS (w_H W3) (ms_mem ms') (kFSH cx fpos + i) = aview SEGS (w_H W3) (ms_mem ms3) (kFSH cx fpos + i)) ->
  (forall i, 0 <= i < 0x202 -> aview SEGS (w_H W3) (ms_mem ms') (kFSH cx fpos + 4 + i) = Some v) ->
  kshadow cx fpos W3 ms' (kfsh v s2v r).
Proof.
  intros cx fpos W3 ms3 ms' s1v s2v r v Hsh Hk H0 i Hi. rewrite kfsh_length in Hi.
  rewrite kn_kfsh_nth.
  destruct (Nat.ltb_spec i 4) as [Hq1|Hq1].
  - rewrite Hk by lia. rewrite (Hsh i ltac:(rewrite kfsh_length; lia)). rewrite kn_kfsh_nth.
    destruct (Nat.ltb_spec i 4); [reflexivity | lia].
  - destruct (Nat.ltb_spec i 0x206) as [Hq2|Hq2].
    + replace (kFSH cx fpos + Z.of_nat i) with (kFSH cx fpos + 4 + (Z.of_nat i - 4)) by lia.
      apply H0. lia.
    + rewrite Hk by lia. rewrite (Hsh i ltac:(rewrite kfsh_length; lia)). rewrite kn_kfsh_nth.
      destruct (Nat.ltb_spec i 4); [lia|]. destruct (Nat.ltb_spec i 0x206); [lia | reflexivity].
Qed.

(* the cut after meta_fill_<v> on 0x202 shadow bytes of F from shadow(F) + lo: the new F shadow given *)
Lemma kq_land_mf : forall lo cx fpos pc rl sl sh sh' adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl',
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 ->
  kslots_okb sl = true -> 0 <= lo -> lo + 0x202 <= 2048 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (kFSH cx fpos + lo <= a < kFSH cx fpos + lo + 0x202) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  kshadow cx fpos W3 ms' sh' ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' ->
  kat B cx fpos pc' rl' sl sh' true adv g k2 ly3 S3 W3 ms' md'.
Proof.
  intros lo cx fpos pc rl sl sh sh' adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' HB HK Hok Hlo Hhi UN HP HSH' Hfds Hfs
    Hkms Hr0 Hrl.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _).
  set (X := fun a => kFSH cx fpos + lo <= a < kFSH cx fpos + lo + 0x202).
  assert (HK0 : kat B cx fpos pc rl sl [] true adv g k2 ly3 S3 W3 ms3 md3).
  { apply (km_kat_sh B cx fpos pc rl sl sh [] true adv g k2 ly3 S3 W3 ms3 md3 HK). intros i Hi. cbn in Hi. lia. }
  apply (km_kat_sh B cx fpos pc' rl' sl [] sh' true adv g k2 ly3 S3 W3 ms' md'); [|exact HSH'].
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  destruct (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (F1 & F2 & F3 & F4).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity.
  assert (HCU : forall a, ka0 cx <= a < ka0 cx + 16 -> a < kLowMemEnd \/ kHighMemBeg <= a).
  { intros a Ha. assert (Hx : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (left; unfold ka0 in Ha; exact Ha).
    destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB Hx) as (_ & L2 & _). exact L2. }
  apply (kat_frame SK B LAWS X cx fpos pc rl sl [] true adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl W3 ms' md'
    HB HK0 Hkms Hr0 Hrl (incl_refl sl) ltac:(cbn; lia) Hfds Hfs UN HP).
  - intros a Ha. right. right. left. unfold X in Ha. rewrite kn_fsb8. change (16384 / 8) with 2048. lia.
  - unfold kX_miss, X. rewrite kn_fsb8. cbn [length Z.of_nat].
    unfold kHighMemBeg, kLowShadowBeg, kLowMemEnd, SHADOW_OFF in *. rewrite HK8 in S1.
    split; [intros a Ha Hx; lia|].
    split.
    { intros ov Hov. pose proof (kslots_okb_spec sl Hok ov Hov) as Ho. split; [exact Ho|]. intros a Ha Hx. lia. }
    split; [intros a Ha Hx; lia|].
    split; [intros a Ha Hx; lia|].
    split; [intros a Ha Hx; lia|].
    split; [intros a Ha Hx; destruct (HCU a Ha); lia|].
    split; [intros a Ha Hx; unfold LA_G_NL, NK_SIZE in Ha; lia|].
    intros a Ha Hx; unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in Ha; lia.
Qed.

(* ---- THE TWO CALLS over kernel's facts ---- *)

(* meta_fill_<v>(shadow(F) + lo, 0x202) from s1 (LinkWalkSide.v aj_gx_set_shadow_at) *)
Lemma kq_call_mf : forall pc v, aset_shadow_realizes pa_segs B pc v ->
  forall cx fpos k2 ly3 S3 W3 mm md3 (rg : bvmap 5 word) raw lo (Q : world SEGS -> config -> Prop),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md3 k2 ->
  0 <= lo -> lo + 0x202 <= 2048 ->
  getr rg 10 = w64 (kFSH cx fpos + lo) -> getr rg 11 = w64 0x202 -> getr rg 2 = w64 (ksp1 cx) ->
  getr rg 3 = getr (k_regs cx) 3 -> getr rg 4 = getr (k_regs cx) 4 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mem2 md2 k2 ->
     aregs_preserved rg regs2 ->
     (forall i, 0 <= i < 0x202 -> aview SEGS (w_H W3) mem2 (kFSH cx fpos + lo + i) = Some v) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (kFSH cx fpos + lo <= a < kFSH cx fpos + lo + 0x202) ->
        aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mm a) ->
     (forall a, apresent (w_H W3) mm a -> apresent (w_H W3) mem2 a) ->
     same_but_materialized md3 md2 ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 pc) mm (seg_rom SEGS)) md3) Q.
Proof.
  intros pc v AS cx fpos k2 ly3 S3 W3 mm md3 rg raw lo Q HB HJ Hlo Hhi R10 R11 R2 R3 R4 R1 Hraw CONT.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _ & _ & _ & Hgp & Htp & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp : spZ rg = ksp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (HFA : shadow_addr (frame_addr ly3 KN_CID fpos) = kFSH cx fpos)
    by (rewrite (km_fa SK B cx fpos k2 ly3 S3 W3 mm md3 HB HJ); reflexivity).
  eapply SRr_bind.
  - eapply (aj_gx_set_shadow_at SK SEGS B LAWS pa_segs_low pc v AS (k_G cx) (k_XO cx) (k_OUT cx) W3 rg mm
      (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) _ ly3 S3 md3 k2
      KN_CID fpos (kFSH cx fpos + lo) 0x202 raw HGok HJ);
    [ left; reflexivity | exact R10 | exact R11 | lia | rewrite HFA; lia
    | rewrite HFA, kn_fsb8; change (16384 / 8) with 2048; lia
    | rewrite Hsp; lia | rewrite Hsp, HES; rewrite HK8 in S6; lia | rewrite Hsp; lia
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | exact Hraw ].
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H00 & Hkeep & Hpres & Hsbm).
    exact (CONT regs2 mem2 md2 HJ2 HP2 H00 Hkeep Hpres Hsbm).
Qed.

(* the hull of a range of F's buffers: F's shadow bytes are present (kframe) *)
Lemma kq_fbuf_hull : forall cx fpos k2 ly3 S3 md3 W3 ms3 lo n,
  kjbk B cx fpos k2 ly3 S3 md3 -> kframe cx fpos true W3 ms3 ->
  24 <= lo -> lo + n <= KN_FSZ -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) (kF cx fpos + lo) n.
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 lo n HJB HFR Hlo Hhi Hn s Hs.
  destruct HFR as (_ & _ & _ & _ & _ & Hpsh).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & _).
  apply kq_aview_some. apply Hpsh. rewrite kn_fsb8. change (16384 / 8) with 2048.
  unfold kFSH, shadow_of_addr, shadow_addr, KN_FSZ, SHADOW_OFF in *. lia.
Qed.

(* checked_memcpy(g_nl + 4096 j, x, n) from s1 (link_ajkit.v aj_gx_intrin_at): the source x lies in F *)
Lemma kq_call_gcpy : forall cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 (rg : bvmap 5 word) raw j n x
    (Q : world SEGS -> config -> Prop),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 ->
  0 <= j < 64 -> 0 <= n <= 4096 ->
  kF cx fpos + 24 <= x -> x + n <= kF cx fpos + KN_FSZ ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF x n ->
  getr rg 10 = w64 (LA_G_NL + 4096 * j) -> getr rg 11 = w64 x -> getr rg 12 = w64 n -> getr rg 2 = w64 (ksp1 cx) ->
  getr rg 3 = getr (k_regs cx) 3 -> getr rg 4 = getr (k_regs cx) 4 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mem2 md2 k2 ->
     aregs_preserved rg regs2 ->
     (forall i, 0 <= i < n ->
        aview SEGS (w_H W3) mem2 (LA_G_NL + 4096 * j + i) = aview SEGS (w_H W3) (ms_mem ms3) (x + i)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (LA_G_NL + 4096 * j <= a < LA_G_NL + 4096 * j + n) ->
        ~ (ksp1 cx - ESTACK <= a < ksp1 cx) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) mem2 a) ->
     same_but_materialized md3 md2 ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 0x52d78) (ms_mem ms3) (seg_rom SEGS)) md3) Q.
Proof.
  intros cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 rg raw j n x Q HB HJ HK Hj Hn Hx1 Hx2 HRAx
    R10 R11 R12 R2 R3 R4 R1 Hraw CONT.
  pose proof HK as (_ & _ & _ & _ & HFR & _ & _ & HJB & HKK & _).
  pose proof HB as (HPRE & _).
  pose proof HPRE as (_ & HGok & _ & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & Hajw & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  rewrite kn_fsb8 in F2, F3, F5.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5.
  assert (Hsp : spZ rg = ksp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  pose proof HJB as (_ & _ & HPERM & _).
  assert (AJW : forall a, kE cx a -> ajw B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
            (k_ly cx) (k_S cx) ly3 S3 ((KN_CID, fpos) :: k_own cx) a).
  { intros a Ha. eapply ajw_mono; [exact (Hajw a Ha) | | |].
    - intros b m Hin. exact (Permutation_in _ (Permutation_sym HPERM) Hin).
    - intros y Hy. right. exact Hy.
    - intros c q. exact (km_fa SK B cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ c q). }
  destruct (kq_gnl_ra cx fpos k2 ly3 S3 W3 ms3 md3 (LA_G_NL + 4096 * j) n HB HJ HJB HKK ltac:(lia)
              ltac:(unfold NK_SIZE; lia) ltac:(lia)) as (HRAd & HHd).
  unfold KN_FSZ in Hx2.
  eapply SRr_bind.
  - eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OCpy 0x52d78 AMEMCPY (k_G cx) (k_XO cx) (k_OUT cx) W3 rg
      (ms_mem ms3) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) _ ly3 S3 md3 k2
      (LA_G_NL + 4096 * j) x n raw HGok HJ R10 R11 R12);
    [ lia | unfold LA_G_NL; lia | unfold LA_G_NL; lia
    | rewrite Hsp; lia | rewrite Hsp, HES; rewrite HK8 in S6; lia | rewrite Hsp; lia
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | exact Hraw
    | | | exact HRAd | intros _; exact HHd | ].
    + intros a Ha. assert (HE : kE cx a) by (apply kq_kE_gnl; unfold NK_OPEN; lia).
      destruct (AJW a HE) as [(H1 & H2) | [H1 | H1]].
      * left. split; [exact H1|]. split; [exact H2|]. rewrite Hsp, HES. rewrite HK8 in S1. unfold LA_G_NL in Ha. lia.
      * right. left. split; [exact H1|].
        apply (writable_at_of_wseg SEGS _ LA_G_NL NK_SIZE);
          [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE; lia | exact (ki_gnl_wseg _ _ KI) | unfold NK_SIZE; lia].
      * right. right. exact H1.
    + unfold amem_range. left. unfold kLowMemEnd, LA_G_NL. lia.
    + split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - apply kq_aview_some. destruct HFR as (_ & _ & _ & _ & Hpf & _). apply Hpf. rewrite kn_fsb8. lia.
        - rewrite Hsp, HES. rewrite HK8 in S6. lia. }
      split; [unfold LA_G_NL in *; lia|].
      split; [unfold amem_range, kLowMemEnd, kHighMemEnd; unfold kHighMemBeg in *; lia|].
      split; [exact HRAx|].
      intros Hn0.
      pose proof (kq_fbuf_hull cx fpos k2 ly3 S3 md3 W3 ms3 (x - kF cx fpos) n HJB HFR ltac:(lia)
                    ltac:(unfold KN_FSZ; lia) Hn0) as HH.
      replace (kF cx fpos + (x - kF cx fpos)) with x in HH by lia. exact HH.
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Hfr & Hpres & Hsbm).
    apply (CONT regs2 mem2 md2 HJ2 HP2); [| | exact Hpres | exact Hsbm].
    + intros i Hi. exact (Hset i Hi).
    + intros a Ha Hd Hw. apply Hfr; [exact Ha | exact Hd | rewrite Hsp; exact Hw].
Qed.

End b.
End a.
