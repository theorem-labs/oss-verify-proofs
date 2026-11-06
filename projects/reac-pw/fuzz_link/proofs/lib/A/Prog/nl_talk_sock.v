(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 2133 of its 2182 lines of code are new or changed and 260 lines of the source are left out. *)
(* nl_talk on image A (fuzz_link.asan 0x88974; listing (internal path) (internal record, sha256 628c2741aace)):
   the SOCKET phase of the walk, from the cut NT_sock (+0x1a0) to NT_mf0_ra (+0x1ec) or NT_tail (+0x4f8).

   The code, in order (offsets from 0x88974):
     +0x1a0..+0x1ac  a1 := 0x80003, a0 := 16, a2 := 0;  +0x1b0 jal fuzz_socket (0x821cc)
     +0x1b4          bltz a0 -> +0x2cc (the socket failure arm)
     +0x1b8..+0x1c4  s6 := a0, a1 := s11 (req), a2 := s10 (len), a3 := 0;  +0x1c8 jal fuzz_send (0x82290)
     +0x1cc          bltz a0 -> +0x2ec (the send failure arm)
     +0x1d0..+0x1e4  sd s4, 0x20(s1); s10 := s2 + 0x20; a1 := 2048; sd s3, 0x18(s1); a0 := s3
     +0x1e8          jal meta_fill_00 (0x55e74): the 2048 shadow bytes of the 16384-byte buffer become 0; NT_mf0_ra
     the socket failure arm:
     +0x2cc          jal ___errno_location (0x90a7c)
     +0x2d0..+0x2dc  the instrumented check of the 4-byte load of errno (+0x570..+0x57c: the slow test, then
                     errpath_load4 0x5a45c, which is not reached: errno's shadow is 0 at every AR state)
     +0x2e0..+0x2e8  a0 := lw errno; s11 := -a0 (negw); j NT_tail
     the send failure arm:
     +0x2ec          jal ___errno_location
     +0x2f0..+0x2fc  the same check (+0x580..+0x58c, errpath_load4 not reached)
     +0x300..+0x308  s3 := lw errno; a0 := s6; jal fuzz_close (0x8267c)
     +0x30c..+0x310  s11 := -s3 (negw); j NT_tail

   The phase lemma is `nt_sock : forall POST, nt_from SK B POST (nt_recv_inv B) -> nt_from SK B POST (nt_tail_inv B) ->
   nt_from SK B POST (nt_sock_inv B)` (lib/A/Prog/nl_talk_defs.v). Each run between two calls is a symbolic run of
   LinkWalk.v at link's listing, seated afresh from the machine state at the cut (no memory region but the spill slots
   and errno), and each callee contract is applied under SRr_bind on the journal the phase holds.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkPi LinkWalkSide LinkWalkZsh LinkWalkWseg LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkErrno PaJournalFs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c nl_talk_kit nl_talk_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_socket_c fuzz_send_c fuzz_close_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AB1h AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. Image computations (at tfibsegs; the walk reaches them through HSEGS)
   ========================================================================== *)

(* (the writability of a writable segment's byte is LinkWalkWseg.v's wseg_writable_tfib) *)

(* g_nl lies in one segment of the image *)
Lemma nts_gnl_seg_b : existsb (fun s => (Z.of_N (seg_base s) <=? LA_G_NL) &&
    (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) AB1v.tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nts_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> in_img AB1v.tfibsegs a.
Proof.
  intros a Ha. pose proof nts_gnl_seg_b as H. apply existsb_exists in H as (s & Hs & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hs | lia].
Qed.

(* the relro window [PCAP_RLO, PCAP_RHI) lies in one segment of the image *)
Lemma nts_relro_seg_b : existsb (fun s => (Z.of_N (seg_base s) <=? PCAP_RLO) &&
    (PCAP_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) AB1v.tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nts_relro_tfib : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img AB1v.tfibsegs a.
Proof.
  intros a Ha. pose proof nts_relro_seg_b as H. apply existsb_exists in H as (s & Hs & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hs | lia].
Qed.

(* an image byte off the read-only set lies in a writable segment, so it is writable at every memory *)
Lemma nts_img_rw_writable : forall rlo rhi a (m : word -> option byte),
  in_img AB1v.tfibsegs a -> ~ in_roP AB1v.tfibsegs rlo rhi a -> writable_at AB1v.tfibsegs m a.
Proof.
  intros rlo rhi a m (s & Hs & Hr) Hro. apply wseg_writable_tfib.
  exists s. split; [exact Hs|]. split; [|exact Hr].
  destruct (seg_writable s) eqn:Hw; [reflexivity|].
  exfalso. apply Hro. left. exists s. split; [exact Hs|]. split; [exact Hw | exact Hr].
Qed.

(* ==========================================================================
   1. Small facts about machine states, runs and bytes
   ========================================================================== *)

Lemma nts_frame_of_nil : forall E (m m' : word -> option byte), frame_of E [] m m' -> m' = m.
Proof. intros E m m' H. apply functional_extensionality. intros x. apply H. intros (r & Hr & _). destruct Hr. Qed.

Lemma nts_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  assert (H0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma nts_slice_agree : forall (bs bs' : list byte) off n,
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length bs) -> off + n <= Z.of_nat (length bs') ->
  (forall k, (k < Z.to_nat n)%nat -> nth_error bs' (Z.to_nat off + k) = nth_error bs (Z.to_nat off + k)) ->
  slice bs' off n = slice bs off n.
Proof.
  intros bs bs' off n Hoff Hn Hl Hl' H. apply lw_list_ext.
  - rewrite !lw_slice_length by lia. reflexivity.
  - intros k Hk. rewrite lw_slice_length in Hk by lia. rewrite !lw_slice_nth by lia. exact (H k Hk).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Lemma nts_ms_eta : forall {PI : PAImg link_listing} pc (ms : machine_state), nt_shape pc ms ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (pa_val A_TEXT + pc)) (ms_mem ms) (seg_rom pa_segs).
Proof.
  intros PI pc ms (Hpc & Hrv & Hsv & Hrom & Hfr & Hcsr).
  destruct ms as [regs fregs pcv svc resv fcsr mem rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *.
  subst. unfold w64, mkst. reflexivity.
Qed.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.

Lemma nts_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof. intros a Ha. rewrite HSEGS. exact (nts_relro_tfib a Ha). Qed.
Hypothesis FSO : fuzz_socket_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis FSE : fuzz_send_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis FCL : fuzz_close_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis ERRNO : aerrno_location_realizes SEGS B (pa_sigma LS____errno_location).
Hypothesis MF00 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_00) 0.

(* ---- seating a symbolic state at a cut ---- *)
Lemma nts_seat : forall pc (ms : machine_state) (W : world SEGS) ext rs G,
  nt_shape pc ms -> regions_wf rs = true ->
  Forall (region_ok SEGS (Eimg (Ereg (ms_regs ms) ext)) (mrestrict (w_H W) (ms_mem ms))) rs ->
  pairwise_disjoint (Eimg (Ereg (ms_regs ms) ext)) rs ->
  facts_ok (Eimg (Ereg (ms_regs ms) ext)) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) ext)) (mkSS pc sr_atoms rs None G) (restrict (w_H W) ms).
Proof.
  intros pc ms W ext rs G Hsh Hwf Hrs Hd Hf.
  assert (Hms' : restrict (w_H W) ms =
    mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)).
  { pose proof (nts_ms_eta pc ms Hsh) as Hms. rewrite Hms at 1. reflexivity. }
  rewrite Hms'. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hrs | exact Hd | exact Hf].
Qed.

(* the same with the shadow base register s5 pinned to its value, so that the engine sees the instrumented check's
   shadow address as (a >> 3) + SHADOW_OFF *)
Definition nts_regs5 : list sv := sr_set sr_atoms 21 (SLit 0x7fff8000).

Lemma nts_seat5 : forall pc (ms : machine_state) (W : world SEGS) ext rs G,
  nt_shape pc ms -> getr (ms_regs ms) 21 = Z_to_bv 64 0x7fff8000 -> regions_wf rs = true ->
  Forall (region_ok SEGS (Eimg (Ereg (ms_regs ms) ext)) (mrestrict (w_H W) (ms_mem ms))) rs ->
  pairwise_disjoint (Eimg (Ereg (ms_regs ms) ext)) rs ->
  facts_ok (Eimg (Ereg (ms_regs ms) ext)) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) ext)) (mkSS pc nts_regs5 rs None G) (restrict (w_H W) ms).
Proof.
  intros pc ms W ext rs G Hsh H21 Hwf Hrs Hd Hf.
  assert (Hms' : restrict (w_H W) ms =
    mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)).
  { pose proof (nts_ms_eta pc ms Hsh) as Hms. rewrite Hms at 1. reflexivity. }
  rewrite Hms'. apply pa_entry_st_ok_full; [| exact Hwf | exact Hrs | exact Hd | exact Hf].
  unfold nts_regs5. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | | cbn [sv_denot]; exact H21].
  intros H0. apply (f_equal bv_unsigned) in H0. cbv in H0. discriminate H0.
Qed.

(* the extra atoms of a seat, by index *)
Lemma nts_ew_reg : forall regs ext n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs ext)) n = getr regs r.
Proof.
  intros regs ext n r Hn. pose proof (u5_range r) as R.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs ext n r Hn).
Qed.

Lemma nts_ew_ext : forall regs ext j, (32 + j < A_TEXT)%nat ->
  ew (Eimg (Ereg regs ext)) (32 + j) = nth j ext (Z_to_bv 64 0).
Proof. intros regs ext j Hj. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.

(* ==========================================================================
   2. The geometry of the call, from nt_base
   ========================================================================== *)

Lemma nts_geo : forall cx, nt_base SK B cx ->
  spZ (n_regs cx) mod 16 = 0 /\
  n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NL_TALK_AK /\ spZ (n_regs cx) <= n_sp0 cx /\
  alloc_ceiling <= n_sp0 cx - n_STK cx /\ n_sp0 cx + n_XO cx <= 2 ^ 47 /\ 0 <= n_XO cx /\ 0 <= n_STK cx /\
  spZ (n_regs cx) - 208 <= n_sp1 cx <= spZ (n_regs cx) - 192 /\ n_sp1 cx mod 32 = 0 /\ n_sp1 cx mod 16 = 0.
Proof.
  intros cx HB. destruct HB as (HA & _).
  destruct HA as (HJ & _ & _ & _ & _ & _ & _ & H16 & Hlo & Hhi & _).
  pose proof (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hr1 & Hr2 & Hr3 & Hr4).
  destruct HJ as (HSTK & HXO & _).
  rewrite NL_TALK_AK_val in *. pose proof alloc_ceiling_val as Hac.
  assert (Hc : 0 <= spZ (n_regs cx) - NL_TALK_AFRAME) by (unfold NL_TALK_AFRAME; lia).
  destruct (nt_sp1_range (spZ (n_regs cx)) Hc H16) as (S1 & S2 & S3).
  unfold n_sp1. unfold NL_TALK_AFRAME in S1.
  repeat split; try lia; assumption.
Qed.

(* ==========================================================================
   3. g_nl's bytes across a step that writes some of its fields
   ========================================================================== *)

Lemma nts_anlk_unique : forall m g b1 b2, anlk_at SEGS m g b1 -> anlk_at SEGS m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 [[(_ & _ & H1) _] L1] [[(_ & _ & H2) _] L2].
  apply lw_list_ext; [lia|].
  intros k Hk. rewrite <- (H1 k Hk). apply H2. lia.
Qed.

(* bs' is bs but for the bytes [lo, hi) *)
Definition nts_gsame (lo hi : Z) (bs bs' : list byte) : Prop :=
  length bs' = length bs /\
  forall k, (k < length bs)%nat -> ~ (lo <= Z.of_nat k < hi) -> nth_error bs' k = nth_error bs k.

Lemma nts_gsame_of : forall (m m' : word -> option byte) bs bs' lo hi,
  anlk_at SEGS m LA_G_NL bs -> anlk_at SEGS m' LA_G_NL bs' ->
  (forall i, 0 <= i < NK_SIZE -> ~ (lo <= i < hi) -> mbyte SEGS m' (LA_G_NL + i) = mbyte SEGS m (LA_G_NL + i)) ->
  nts_gsame lo hi bs bs'.
Proof.
  intros m m' bs bs' lo hi [[(_ & _ & Hb) _] HL] [[(_ & _ & Hb') _] HL'] Hk.
  split; [lia|]. intros k Hlt Hn.
  rewrite <- (Hb' k ltac:(lia)), <- (Hb k ltac:(lia)). apply Hk; lia.
Qed.

Lemma nts_gsame_trans : forall lo hi lo' hi' b1 b2 b3,
  nts_gsame lo hi b1 b2 -> nts_gsame lo' hi' b2 b3 -> lo <= lo' -> hi' <= hi -> nts_gsame lo hi b1 b3.
Proof.
  intros lo hi lo' hi' b1 b2 b3 (L1 & H1) (L2 & H2) Hl Hh. split; [lia|].
  intros k Hk Hn. rewrite (H2 k ltac:(lia) ltac:(lia)). exact (H1 k Hk Hn).
Qed.

Lemma nts_gsame_slice : forall lo hi bs bs' off n, nts_gsame lo hi bs bs' ->
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length bs) -> (off + n <= lo \/ hi <= off) ->
  slice bs' off n = slice bs off n.
Proof.
  intros lo hi bs bs' off n (L & H) H0 H1 H2 H3.
  apply nts_slice_agree; [lia | lia | lia | lia |].
  intros k Hk. apply H; lia.
Qed.

Lemma nts_gsame_rdn : forall lo hi bs bs' off n, nts_gsame lo hi bs bs' ->
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length bs) -> (off + n <= lo \/ hi <= off) ->
  rdn bs' off n = rdn bs off n.
Proof. intros lo hi bs bs' off n Hs H0 H1 H2 H3. unfold rdn. rewrite (nts_gsame_slice lo hi bs bs' off n); auto. Qed.

(* the fields below socket_errno and above n_sent: the chunk queue, the cursor, end_errno and the interface count *)
Lemma nts_gsame_fields : forall lo hi bs bs', nlk_wf bs -> Z.of_nat (length bs) = NK_SIZE ->
  nts_gsame lo hi bs bs' -> NK_SOCKET_ERRNO <= lo -> hi <= NK_N_SENT + 4 ->
  nk_chunks bs' = nk_chunks bs /\ nk_n_chunks bs' = nk_n_chunks bs /\ nk_next bs' = nk_next bs /\
  nk_end_errno bs' = nk_end_errno bs /\ nk_n_if bs' = nk_n_if bs /\
  (forall i, 0 <= i < nk_n_chunks bs -> fld_u64 bs' (NK_CHUNK_LEN + 8 * i) = fld_u64 bs (NK_CHUNK_LEN + 8 * i)).
Proof.
  intros lo hi bs bs' WF HL Hs Hlo Hhi.
  pose proof WF as (Wn & _).
  unfold NK_SIZE, NK_SOCKET_ERRNO, NK_N_SENT in *.
  split.
  { apply (nt_nk_chunks_keep bs bs' WF). apply (nts_gsame_slice lo hi); unfold NK_NEXT; lia || exact Hs. }
  split.
  { unfold nk_n_chunks, fld_u32. apply (nts_gsame_rdn lo hi); unfold NK_N_CHUNKS; lia || exact Hs. }
  split.
  { unfold nk_next, fld_u32. apply (nts_gsame_rdn lo hi); unfold NK_NEXT; lia || exact Hs. }
  split.
  { unfold nk_end_errno, fld_u32. apply (nts_gsame_rdn lo hi); unfold NK_END_ERRNO; lia || exact Hs. }
  split.
  { unfold nk_n_if, fld_u32. apply (nts_gsame_rdn lo hi); unfold NK_N_IF; lia || exact Hs. }
  intros i Hi. unfold fld_u64. unfold NL_CHUNKS in Wn.
  apply (nts_gsame_rdn lo hi); unfold NK_CHUNK_LEN; lia || exact Hs.
Qed.

(* the request ring, when the window stops below it *)
Lemma nts_gsame_sent : forall lo hi bs bs', nlk_wf bs -> Z.of_nat (length bs) = NK_SIZE ->
  nts_gsame lo hi bs bs' -> hi <= NK_SENT ->
  nk_sent bs' = nk_sent bs /\ nk_n_sent bs' = nk_n_sent bs /\
  (forall i, 0 <= i < nk_n_sent bs -> fld_u64 bs' (NK_SENT_LEN + 8 * i) = fld_u64 bs (NK_SENT_LEN + 8 * i)).
Proof.
  intros lo hi bs bs' WF HL Hs Hhi.
  pose proof WF as (_ & _ & Wn & _).
  unfold NK_SIZE, NK_SENT in *.
  split.
  { apply (nt_nk_sent_keep bs bs' WF). apply (nts_gsame_slice lo hi); unfold NK_SENT, NK_N_SENT; lia || exact Hs. }
  split.
  { unfold nk_n_sent, fld_u32. apply (nts_gsame_rdn lo hi); unfold NK_N_SENT; lia || exact Hs. }
  intros i Hi. unfold fld_u64. unfold NL_SENT_MAX in Wn.
  apply (nts_gsame_rdn lo hi); unfold NK_SENT_LEN; lia || exact Hs.
Qed.

Lemma nts_anlk_len : forall m g bs, anlk_at SEGS m g bs -> Z.of_nat (length bs) = NK_SIZE.
Proof. intros m g bs [_ HL]. exact HL. Qed.

(* ==========================================================================
   4. What every cut of the phase carries, and how it crosses a step
   ========================================================================== *)

(* The bytes of the caller's memory the phase reads back: the saved registers, the spill slots, the class-9
   frame and its shadow. *)
Definition nts_foot (cx : ntcx) (fp a : Z) : Prop :=
  (spZ (n_regs cx) - 104 <= a < spZ (n_regs cx)) \/ (n_sp1 cx + 48 <= a < n_sp1 cx + NT_SPILL) \/
  (nF cx fp <= a < nF cx fp + fs_frame_bytes NT_CID) \/
  (nSH cx fp <= a < nSH cx fp + fs_frame_bytes NT_CID / 8).

(* what the bytes of nts_foot say *)
Definition nts_stat (cx : ntcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (v : Z) : Prop :=
  nt_saved cx W3 ms3 /\ nt_header cx fp W3 ms3 /\ nt_slots0 cx fp W3 ms3 /\ nt_frame_shadow cx fp v W3 ms3.

(* the journal's bookkeeping, the kept clause and the buffers *)
Definition nts_dyn (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) (E : Z -> Prop) : Prop :=
  nt_jbk B cx fp k2 ly3 S3 md3 /\ nt_kept B cx E fp W3 (ms_mem ms3) /\
  nt_bufs_same cx (rdW W3 (ms_mem ms3)) /\ abuf SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) NT_BUFLEN /\
  (forall a, E a -> LA_G_NL + NK_SOCKET_ERRNO <= a < LA_G_NL + NK_N_SENT + 4).

Definition nts_body (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) (E : Z -> Prop) (v : Z) : Prop :=
  nt_regs cx fp ms3 /\
  getr (ms_regs ms3) 20 = w64 (nF cx fp) /\ getr (ms_regs ms3) 23 = w64 (n_aliasn cx) /\
  getr (ms_regs ms3) 25 = w64 (n_alias cx) /\
  nts_stat cx fp W3 ms3 v /\ nts_dyn cx fp k2 ly3 S3 W3 ms3 md3 E.

(* the facts every step lemma reads off nt_base, the cut's journal and nt_jbk *)
Lemma nts_frame : forall cx fp k2 ly3 S3 (W3 : world SEGS) mem3 md3,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  nt_jbk B cx fp k2 ly3 S3 md3 ->
  In (NT_CID, fp) (frames S3) /\ frame_addr ly3 NT_CID fp = nF cx fp /\
  4096 <= nF cx fp /\ nF cx fp + fs_frame_bytes NT_CID <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\
  nSH cx fp = shadow_addr (nF cx fp) /\ fs_frame_bytes NT_CID = 32768 /\
  in_app (nF cx fp) (fs_frame_bytes NT_CID) /\ AR SEGS B ly3 S3 W3 mem3 md3.
Proof.
  intros cx fp k2 ly3 S3 W3 mem3 md3 HB HJ HK.
  destruct HK as (_ & _ & _ & Hfr & _ & Hfa & _).
  assert (HAR : AR SEGS B ly3 S3 W3 mem3 md3).
  { destruct HJ as (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi). }
  assert (Hin : In (NT_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (Efa : frame_addr ly3 NT_CID fp = nF cx fp) by (unfold nF; apply Hfa).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 NT_CID fp HAR Hin) as (H1 & H2 & H4).
  destruct (frame_al64 SEGS B ly3 S3 W3 mem3 md3 NT_CID fp HAR Hin) as (H3 & _ & _).
  rewrite Efa in H1, H2, H3, H4.
  exact (conj Hin (conj Efa (conj H1 (conj H2 (conj H3 (conj eq_refl (conj eq_refl (conj H4 HAR)))))))).
Qed.

(* A byte of the contract's write set (an `ajw` byte of the caller's journal) that a callee does not write is kept
   by the callee's `akept`: every clause of `ajw` falls in one of `akept`'s. *)
Lemma nts_ajw_kept : forall cx fp k2 ly3 S3 (W3 : world SEGS) m3 md3 (W4 : world SEGS) m4 slo shi
    (Ec : Z -> Prop) a,
  nt_base SK B cx ->
  nt_jbk B cx fp k2 ly3 S3 md3 ->
  akept SEGS B ly3 S3 W3 m3 W4 m4 slo shi Ec ->
  shi <= n_sp0 cx ->
  ajw B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_lyc cx) (n_Sc cx) (n_own cx) a ->
  ~ (slo <= a < shi) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ Ec a ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a.
Proof.
  intros cx fp k2 ly3 S3 W3 m3 md3 W4 m4 slo shi Ec a HB HK HKc Hshi Hw Hwin Herr HnE.
  destruct HK as (_ & Hperm & _ & Hfr & _ & Hfa & _).
  destruct HKc as (K1 & K2 & K3 & K4 & _).
  destruct HB as (HA & _). destruct HA as (HJc & HGX & _).
  pose proof (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Hr1 & Hr2 & Hr3 & Hr4).
  pose proof HJc as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hbl : forall b m, In (b, m) (ablocks B (n_lyc cx) (n_Sc cx)) -> In (b, m) (ablocks B ly3 S3))
    by (intros b m Hin; apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
  assert (H47 : 2 ^ 47 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  destruct Hw as [(Haw & Hno) | [HGa | (HO & Hout)]].
  - destruct Haw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hin & Hr)]]].
    + apply K1; [lia | exact Hwin | exact HnE].
    + replace a with (b + (a - b)) by lia. apply (K2 b n (a - b) (Hbl b n Hin)); [lia|].
      replace (b + (a - b)) with a by lia. exact HnE.
    + replace a with (b + (a - b)) by lia. apply (K2 b n (a - b) (Hbl b n Hin)); [lia|].
      replace (b + (a - b)) with a by lia. exact HnE.
    + assert (Hcq : In (c, q) (frames S3)) by (rewrite Hfr; right; rewrite Hfrs; apply in_or_app; left; exact Hin).
      apply (K4 c q a Hcq); [|exact HnE].
      unfold frame_rng. cbn [fst snd]. rewrite (Hfa c q). exact Hr.
  - apply K3; [exact (proj1 (HGX a HGa)) | exact (proj2 (HGX a HGa)) | exact Herr | exact HnE].
  - apply K1; [lia | lia | exact HnE].
Qed.

(* ... and a byte of the write set is writable at every later state of the journal *)
Lemma nts_ajw_writable : forall cx fp k2 ly4 S4 (W4 : world SEGS) m4 md4 a,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly4 S4 W4 m4 md4 k2 ->
  Permutation (ablocks B ly4 S4) (ablocks B (n_lyc cx) (n_Sc cx)) ->
  (forall c p, frame_addr ly4 c p = frame_addr (n_lyc cx) c p) ->
  ajw B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_lyc cx) (n_Sc cx) (n_own cx) a ->
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a ->
  writable_at SEGS (rdW W4 m4) a.
Proof.
  intros cx fp k2 ly4 S4 W4 m4 md4 a HB HJ4 Hperm Hfa Hw Hro.
  destruct HB as (HA & _). destruct HA as (HJc & HGX & _).
  pose proof HJ4 as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  assert (Hbl : forall b m, In (b, m) (ablocks B (n_lyc cx) (n_Sc cx)) -> In (b, m) (ablocks B ly4 S4))
    by (intros b m Hin; apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
  destruct Hw as [(Haw & Hno) | [HGa | (HO & Hout)]].
  - destruct Haw as [Hs | Haw].
    + apply (apresent_writable SEGS). apply Hpres. lia.
    + apply (apresent_writable SEGS).
      refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)).
      destruct Haw as [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | (c & q & Hin & Hr)]].
      * right; left. split; [exact Hf|]. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
      * right; right; left. exists b, n. split; [exact (Hbl b n Hin)|]. split; [exact Hn0 | exact Hr].
      * right; right; right. exists c, q. split; [right; exact Hin|]. rewrite !Hfa. exact Hr.
  - pose proof (HGX a HGa) as (Hi & _).
    assert (HW : forall m, writable_at SEGS m a)
      by (intros m; rewrite HSEGS in Hi, Hro |- *; exact (nts_img_rw_writable PCAP_RLO PCAP_RHI a m Hi Hro)).
    apply HW.
  - apply (apresent_writable SEGS). apply Hpres. lia.
Qed.

(* arodata_okP across a step that changes no read-only byte the reader may see *)
Lemma nts_aro_eq : forall (rd rd' : reader),
  (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> rd' a = rd a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd -> arodata_okP SEGS PCAP_RLO PCAP_RHI B rd'.
Proof. intros rd rd' H HR a Hro Hns Herr. rewrite (H a Hro Hns Herr). exact (HR a Hro Hns Herr). Qed.

Lemma nts_roP_img : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (nts_relro_img a Hr)].
Qed.

(* the caller's two buffers, from the bytes and the writability of their ranges *)
Lemma nts_bufs_keep : forall cx (m3 m4 : word -> option byte),
  nt_bufs_same cx m3 ->
  (forall a, n_kind cx <> 0 -> n_kind cx <= a < n_kind cx + n_kindn cx -> mbyte SEGS m4 a = mbyte SEGS m3 a) ->
  (forall a, n_alias cx <> 0 -> n_alias cx <= a < n_alias cx + n_aliasn cx -> mbyte SEGS m4 a = mbyte SEGS m3 a) ->
  (forall a, n_kind cx <> 0 -> n_kind cx <= a < n_kind cx + n_kindn cx -> writable_at SEGS m4 a) ->
  (forall a, n_alias cx <> 0 -> n_alias cx <= a < n_alias cx + n_aliasn cx -> writable_at SEGS m4 a) ->
  nt_bufs_same cx m4.
Proof.
  intros cx m3 m4 (B1 & B2 & B3 & B4) Mk Ma Wk Wa.
  split; [|split; [|split]].
  - intros Hk s Hs Hc. destruct (B1 Hk s Hs Hc) as ((H0 & H1 & Hb) & Hn).
    split; [|exact Hn]. split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). rewrite length_app in Hi. cbn [length] in Hi.
    apply Mk; [exact Hk | lia].
  - intros Hk s Hs Hc. destruct (B2 Hk s Hs Hc) as ((H0 & H1 & Hb) & Hn).
    split; [|exact Hn]. split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). rewrite length_app in Hi. cbn [length] in Hi.
    apply Ma; [exact Hk | lia].
  - intros Hk H1. destruct (B3 Hk H1) as (junk & Hl & (H0 & H2 & Hb) & Hw).
    exists junk. split; [exact Hl|]. split.
    + split; [exact H0|]. split; [exact H2|]. intros i Hi. rewrite <- (Hb i Hi). apply Mk; [exact Hk | lia].
    + intros i Hi. apply Wk; [exact Hk | lia].
  - intros Hk H1. destruct (B4 Hk H1) as (junk & Hl & (H0 & H2 & Hb) & Hw).
    exists junk. split; [exact Hl|]. split.
    + split; [exact H0|]. split; [exact H2|]. intros i Hi. rewrite <- (Hb i Hi). apply Ma; [exact Hk | lia].
    + intros i Hi. apply Wa; [exact Hk | lia].
Qed.

(* a buffer in the class-9 frame, from the bytes and the writability of its range *)
Lemma nts_abuf_keep : forall (m3 m4 : word -> option byte) p n,
  abuf SEGS m3 p n ->
  (forall a, p <= a < p + n -> mbyte SEGS m4 a = mbyte SEGS m3 a) ->
  (forall a, p <= a < p + n -> writable_at SEGS m4 a) ->
  abuf SEGS m4 p n.
Proof.
  intros m3 m4 p n (junk & Hl & (H0 & H2 & Hb) & Hw) M Wr.
  exists junk. split; [exact Hl|]. split.
  - split; [exact H0|]. split; [exact H2|]. intros i Hi. rewrite <- (Hb i Hi). apply M. lia.
  - intros i Hi. apply Wr. lia.
Qed.

(* the nl_talk write-set facts of the two buffers, read off nt_base *)
Lemma nts_buf_facts : forall cx, nt_base SK B cx ->
  (n_kind cx <> 0 -> forall a, n_kind cx <= a < n_kind cx + n_kindn cx ->
     ajw B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
       (n_lyc cx) (n_Sc cx) (n_own cx) a /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\
     ~ (as_errno B <= a < as_errno B + 4) /\ ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE) /\
     ~ (spZ (n_regs cx) - NL_TALK_AK <= a < spZ (n_regs cx)) /\
     (0 <= a < kLowMemEnd \/ kHighMemBeg <= a < kHighMemEnd)) /\
  (n_alias cx <> 0 -> forall a, n_alias cx <= a < n_alias cx + n_aliasn cx ->
     ajw B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
       (n_lyc cx) (n_Sc cx) (n_own cx) a /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\
     ~ (as_errno B <= a < as_errno B + 4) /\ ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE) /\
     ~ (spZ (n_regs cx) - NL_TALK_AK <= a < spZ (n_regs cx)) /\
     (0 <= a < kLowMemEnd \/ kHighMemBeg <= a < kHighMemEnd)).
Proof.
  intros cx HB. pose proof HB as (HA & _ & HP & _).
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & Hnro).
  destruct HP as (kbs & req & HNLK & HWF & HOPEN & HOC & HCC & HRA & HHV & HERR & HRQ & HRL & HLEN
                  & HMR & HRAQ & HHVQ & HFRQ & HGQ & HBK & HBA & HEK & HEA & HKA & HKF & HAF & HCK & HCA).
  split.
  - intros Hk a Ha.
    assert (Hfp : inFP (n_Wr cx) a).
    { exists (aivl (n_kind cx) (n_kindn cx)). split; [right; left; reflexivity|].
      unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec (n_kind cx) 0); [contradiction | lia]. }
    split; [exact (Hajw a Hfp)|]. split; [exact (Hnro a Hfp)|].
    destruct (HKF Hk) as (Hkf & Hkg). unfold apart_frame, apart_gnl in Hkf, Hkg.
    specialize (HEK Hk). unfold apart in HEK.
    assert (Hmr : amem_range (n_kind cx) (n_kindn cx))
      by (unfold n_kind, n_kindn in *; exact (proj1 (HCK Hk ltac:(lia)))).
    unfold amem_range in Hmr.
    assert (H0 : 0 <= n_kind cx) by (unfold n_kind, aarg, argZ; apply bv_unsigned_in_range).
    split; [unfold n_kind, n_kindn in *; lia|]. split; [unfold n_kind, n_kindn in *; lia|].
    split; [unfold n_kind, n_kindn in *; lia|]. lia.
  - intros Hk a Ha.
    assert (Hfp : inFP (n_Wr cx) a).
    { exists (aivl (n_alias cx) (n_aliasn cx)). split; [right; right; left; reflexivity|].
      unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec (n_alias cx) 0); [contradiction | lia]. }
    split; [exact (Hajw a Hfp)|]. split; [exact (Hnro a Hfp)|].
    destruct (HAF Hk) as (Hkf & Hkg). unfold apart_frame, apart_gnl in Hkf, Hkg.
    specialize (HEA Hk). unfold apart in HEA.
    assert (Hmr : amem_range (n_alias cx) (n_aliasn cx))
      by (unfold n_alias, n_aliasn in *; exact (proj1 (HCA Hk ltac:(lia)))).
    unfold amem_range in Hmr.
    assert (H0 : 0 <= n_alias cx) by (unfold n_alias, aarg, argZ; apply bv_unsigned_in_range).
    split; [unfold n_alias, n_aliasn in *; lia|]. split; [unfold n_alias, n_aliasn in *; lia|].
    split; [unfold n_alias, n_aliasn in *; lia|]. lia.
Qed.

(* the g_nl part of the write set, read off nt_base *)
Lemma nts_gnl_facts : forall cx, nt_base SK B cx -> forall a, LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 ->
  ajw B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_lyc cx) (n_Sc cx) (n_own cx) a /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ n_E cx a.
Proof.
  intros cx HB a Ha. pose proof HB as (HA & _).
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & Hnro).
  assert (Hfp : inFP (n_Wr cx) a) by (exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4); split; [left; reflexivity | cbn [fst snd]; lia]).
  split; [exact (Hajw a Hfp)|]. split; [exact (Hnro a Hfp) | exact Hfp].
Qed.

Lemma nts_at_keep : forall (W W' : world SEGS) ms ms' a v,
  (forall i, 0 <= i < 8 -> aview SEGS (w_H W') (ms_mem ms') (a + i) = aview SEGS (w_H W) (ms_mem ms) (a + i)) ->
  nt_at W ms a v -> nt_at W' ms' a v.
Proof. intros W W' ms ms' a v H Ha. unfold nt_at in *. rewrite (nts_rdword_ext _ _ a H). exact Ha. Qed.

Lemma nts_stat_keep : forall cx fp (W W' : world SEGS) ms ms' v,
  (forall a, nts_foot cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  nts_stat cx fp W ms v -> nts_stat cx fp W' ms' v.
Proof.
  intros cx fp W W' ms ms' v H (Hsv & Hhd & Hsl & Hsh).
  assert (FB : fs_frame_bytes NT_CID = 32768) by reflexivity.
  unfold nts_foot in H. rewrite FB in H. change (32768 / 8) with 4096 in H. unfold NT_SPILL in H.
  split; [|split; [|split]].
  - destruct Hsv as (Hra & Hs). split.
    + apply (nts_at_keep W W' ms ms'); [|exact Hra]. intros i Hi. apply H. left. lia.
    + intros j Hj. apply (nts_at_keep W W' ms ms'); [|exact (Hs j Hj)]. intros i Hi. apply H. left. lia.
  - destruct Hhd as (H1 & H2 & H3 & H4). rewrite FB in H4.
    split; [|split; [|split]];
      (apply (nts_at_keep W W' ms ms'); [intros i Hi; apply H; right; right; left; lia | assumption]).
  - destruct Hsl as (H1 & H2 & H3).
    split; [|split];
      (apply (nts_at_keep W W' ms ms');
       [intros i Hi; apply H; right; left; unfold NS_KIND, NS_KINDN, NS_F; lia | assumption]).
  - destruct Hsh as (H1 & H2 & H3).
    split; [|split]; intros i Hi.
    + rewrite H by (right; right; right; lia). exact (H1 i Hi).
    + rewrite H by (right; right; right; lia). exact (H2 i Hi).
    + rewrite H by (right; right; right; lia). exact (H3 i Hi).
Qed.

(* a byte of the class-9 frame is writable at every state of the journal that owns it *)
Lemma nts_own_frame_writable : forall cx fp k2 ly4 S4 (W4 : world SEGS) m4 md4 a,
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly4 S4 W4 m4 md4 k2 ->
  (forall c p, frame_addr ly4 c p = frame_addr (n_lyc cx) c p) ->
  nF cx fp <= a < nF cx fp + fs_frame_bytes NT_CID ->
  writable_at SEGS (rdW W4 m4) a.
Proof.
  intros cx fp k2 ly4 S4 W4 m4 md4 a HJ4 Hfa Ha. pose proof HJ4 as (_ & _ & (memS & HJi & _) & _).
  apply (apresent_writable SEGS).
  refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)).
  right; right; right. exists NT_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite Hfa. unfold nF in Ha. exact Ha.
Qed.

(* nts_dyn across an own callee (fuzz_socket, fuzz_send, fuzz_close), and the foot it keeps *)
Lemma nts_dyn_call : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 (E : Z -> Prop)
    (rg : bvmap 5 word) (mdc : Model) Kc (Ec : Z -> Prop) ly4 S4 (W4 : world SEGS) ms4 md4,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  nts_dyn cx fp k2 ly3 S3 W3 ms3 md3 E ->
  spZ rg = n_sp1 cx -> 0 <= Kc <= 4144 ->
  m_fds mdc = m_fds md3 -> m_fs mdc = m_fs md3 ->
  (forall a, Ec a -> LA_G_NL + NK_SOCKET_ERRNO <= a < LA_G_NL + NK_N_SENT + 4) ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly4 S4 W4 (ms_mem ms4) md4 k2 ->
  frames S4 = frames S3 -> m_fds md4 = m_fds mdc -> m_fs md4 = m_fs mdc ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W4 (ms_mem ms4) (spZ rg - Kc) (spZ rg) Ec ->
  S4 = set_fs (st_fs S4) S3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  nts_dyn cx fp k2 ly4 S4 W4 ms4 md4 (fun a => E a \/ Ec a) /\
  (forall a, nts_foot cx fp a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 E rg mdc Kc Ec ly4 S4 W4 ms4 md4 HB HJ3 HD Hsp HKc Hfd0 Hfs0 HEc HJ4
    Hfr4 Hfd4 Hfs4 HK4 Hset4 Hperm4.
  destruct HD as (HJB & HKP & HBS & HAB & HER).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  destruct (nts_frame cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ3 HJB)
    as (Hin & Efa & F4096 & Fceil & F64 & ESH & EFB & Fapp & HAR3).
  pose proof HJB as (Hk2 & Hperm3 & Hset3 & Hfr3 & Hnin & Hfa3 & Hwit & Hfd3 & Hfs3).
  pose proof alloc_ceiling_val as Hac. pose proof NL_TALK_AK_val as HAKv.
  pose proof HK4 as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (HEc' : forall a, Ec a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4)
    by (intros a Ha; apply HEc in Ha; unfold NK_SOCKET_ERRNO in Ha; lia).
  assert (Hgimg : forall a, Ec a -> in_img SEGS a).
  { intros a Ha. apply HEc' in Ha. rewrite HSEGS. apply nts_gnl_img. unfold NK_N_SENT, NK_SIZE in *. lia. }
  pose proof (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low) as AFA.
  assert (Hfa4 : forall c p, frame_addr ly4 c p = frame_addr (n_lyc cx) c p).
  { intros c p. pose proof HB as (HA & _). destruct HA as (HJc & _).
    destruct (AFA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c p HJ4) as (E4 & _).
    destruct (AFA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c p HJc) as (E0 & _).
    rewrite E4, E0. reflexivity. }
  assert (Hperm : Permutation (ablocks B ly4 S4) (ablocks B (n_lyc cx) (n_Sc cx)))
    by exact (Permutation_trans Hperm4 Hperm3).
  (* the foot *)
  assert (Hfoot : forall a, nts_foot cx fp a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. unfold nts_foot in Ha. rewrite EFB in Ha. change (32768 / 8) with 4096 in Ha.
    unfold NT_SPILL in Ha.
    destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    - apply K1; [lia | lia |]. intros HE. apply HEc' in HE. unfold LA_G_NL, NK_N_SENT in HE. lia.
    - apply K1; [lia | lia |]. intros HE. apply HEc' in HE. unfold LA_G_NL, NK_N_SENT in HE. lia.
    - apply (K4 NT_CID fp a Hin).
      + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa, EFB. lia.
      + intros HE. apply (frm_img SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 NT_CID fp a HAR3 Hin);
          [rewrite Efa, EFB; lia | exact (Hgimg a HE)].
    - apply (K4 NT_CID fp a Hin).
      + right. unfold in_zr. cbn [fst snd]. rewrite Efa, EFB, <- ESH. change (32768 / 8) with 4096. lia.
      + intros HE. apply HEc' in HE. rewrite ESH in Ha. unfold shadow_addr, SHADOW_OFF, LA_G_NL, NK_N_SENT in *. lia. }
  split; [|exact Hfoot].
  pose proof HKP as (HKc' & HRO & HEn).
  split.
  { (* nt_jbk *)
    split; [exact Hk2|]. split; [exact Hperm|].
    split; [exact (set_fs_trans S3 S4 (n_Sc cx) Hset3 Hset4)|].
    split; [rewrite Hfr4; exact Hfr3|]. split; [exact Hnin|]. split; [exact Hfa4|]. split; [exact Hwit|].
    split; [rewrite Hfd4, Hfd0; exact Hfd3 | rewrite Hfs4, Hfs0; exact Hfs3]. }
  split.
  { (* nt_kept *)
    split; [|split].
    - eapply (akept_trans_ly SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) ly3 S3 W3
        (ms_mem ms3) W4 (ms_mem ms4) (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (spZ rg - Kc) (spZ rg)
        _ Ec _ ltac:(lia) ltac:(lia) HKc' HK4).
      + lia.
      + lia.
      + intros b m Hb. apply (Permutation_in _ (Permutation_sym Hperm3)). exact Hb.
      + intros f Hf. rewrite Hfr3. right. exact Hf.
      + exact Hfa3.
      + intros a [H|H]; [left; left; exact H | right; exact H].
      + intros a H. left. right. exact H.
    - apply (nts_aro_eq (aview SEGS (w_H W3) (ms_mem ms3))); [|exact HRO].
      intros a Hro Hns Herr. apply K3; [exact (nts_roP_img a Hro) | exact Hns | exact Herr |].
      intros HE. apply HEc' in HE. exact (proj1 (proj2 (nts_gnl_facts cx HB a HE)) Hro).
    - intros a [H|H]; [exact (HEn a H) | exact (proj2 (proj2 (nts_gnl_facts cx HB a (HEc' a H))))]. }
  destruct (nts_buf_facts cx HB) as (BK & BA).
  split.
  { apply (nts_bufs_keep cx (rdW W3 (ms_mem ms3)) (rdW W4 (ms_mem ms4)) HBS).
    - intros a Hk Ha. apply (mbyte_of_aview SEGS). destruct (BK Hk a Ha) as (Hw & Hro & Herr & Hng & Hnw & _).
      apply (nts_ajw_kept cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 W4 (ms_mem ms4) (spZ rg - Kc) (spZ rg) Ec a HB HJB HK4
        ltac:(lia) Hw); [lia | exact Herr |].
      intros HE. apply HEc' in HE. unfold NK_N_SENT, NK_SIZE in *. lia.
    - intros a Hk Ha. apply (mbyte_of_aview SEGS). destruct (BA Hk a Ha) as (Hw & Hro & Herr & Hng & Hnw & _).
      apply (nts_ajw_kept cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 W4 (ms_mem ms4) (spZ rg - Kc) (spZ rg) Ec a HB HJB HK4
        ltac:(lia) Hw); [lia | exact Herr |].
      intros HE. apply HEc' in HE. unfold NK_N_SENT, NK_SIZE in *. lia.
    - intros a Hk Ha. destruct (BK Hk a Ha) as (Hw & Hro & _).
      exact (nts_ajw_writable cx fp k2 ly4 S4 W4 (ms_mem ms4) md4 a HB HJ4 Hperm Hfa4 Hw Hro).
    - intros a Hk Ha. destruct (BA Hk a Ha) as (Hw & Hro & _).
      exact (nts_ajw_writable cx fp k2 ly4 S4 W4 (ms_mem ms4) md4 a HB HJ4 Hperm Hfa4 Hw Hro). }
  split.
  { apply (nts_abuf_keep (rdW W3 (ms_mem ms3)) (rdW W4 (ms_mem ms4)) (nBUF cx fp) NT_BUFLEN HAB).
    - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfoot. right; right; left.
      unfold nBUF, NT_BUFOFF, NT_BUFLEN in *. rewrite EFB. lia.
    - intros a Ha. apply (nts_own_frame_writable cx fp k2 ly4 S4 W4 (ms_mem ms4) md4 a HJ4 Hfa4).
      unfold nBUF, NT_BUFOFF, NT_BUFLEN in *. rewrite EFB. lia. }
  intros a [H|H]; [exact (HER a H) | exact (HEc a H)].
Qed.

(* nts_dyn across a step of the phase itself or of a runtime callee: the layout and the allocator state stay, and
   the step writes only bytes of the stack window above s1 or of the frame's shadow *)
Lemma nts_dyn_step : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 (E : Z -> Prop) ms4 md4 (X : Z -> Prop),
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms4) md4 k2 ->
  nts_dyn cx fp k2 ly3 S3 W3 ms3 md3 E ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms4) a) ->
  (forall a, X a -> (n_sp1 cx <= a < spZ (n_regs cx)) \/ (nSH cx fp <= a < nSH cx fp + fs_frame_bytes NT_CID / 8)) ->
  nts_dyn cx fp k2 ly3 S3 W3 ms4 md4 E.
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 E ms4 md4 X HB HJ3 HJ4 HD Hfd Hfs HX HP HXin.
  destruct HD as (HJB & HKP & HBS & HAB & HER).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  destruct (nts_frame cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ3 HJB)
    as (Hin & Efa & F4096 & Fceil & F64 & ESH & EFB & Fapp & HAR3).
  pose proof HJB as (Hk2 & Hperm3 & Hset3 & Hfr3 & Hnin & Hfa3 & Hwit & Hfd3 & Hfs3).
  pose proof alloc_ceiling_val as Hac. pose proof NL_TALK_AK_val as HAKv.
  rewrite EFB in HXin. change (32768 / 8) with 4096 in HXin.
  (* X misses the image and the frame's bytes *)
  assert (HXimg : forall a, X a -> SHADOW_OFF <= a).
  { intros a Ha. destruct (HXin a Ha) as [H|H]; [unfold SHADOW_OFF; lia|]. rewrite ESH in H. unfold shadow_addr in H. lia. }
  assert (HXF : forall a, X a -> ~ (nF cx fp <= a < nF cx fp + 32768)).
  { intros a Ha Hf. destruct (HXin a Ha) as [H|H]; [lia|]. rewrite ESH in H. unfold shadow_addr in H.
    unfold in_app in Fapp. rewrite EFB in Fapp. unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> mbyte SEGS (rdW W3 (ms_mem ms4)) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a)
    by (intros a Ha Hn; apply (mbyte_of_aview SEGS); exact (HX a Ha Hn)).
  pose proof HKP as (HKc & HRO & HEn).
  split.
  { destruct HJB as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9).
    repeat (split; [assumption|]). split; [rewrite Hfd; exact J8 | rewrite Hfs; exact J9]. }
  split.
  { split; [|split].
    - pose proof HB as (HA & _). destruct HA as (HJc & _).
      assert (HARc : AR SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx))
        by (destruct HJc as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
      apply (akept_step SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) W3
        (ms_mem ms3) W3 (ms_mem ms4) (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) _ _ X HARc ltac:(lia) ltac:(lia)
        HKc HX HP).
      + intros a H. exact H.
      + intros a Ha. destruct (HXin a Ha) as [H|H]; [right; lia|].
        left. right. right. left. unfold in_zr. cbn [fst snd].
        change (frame_addr (n_lyc cx) NT_CID fp) with (nF cx fp). rewrite <- ESH.
        change (fs_frame_bytes NT_CID / 8) with 4096. exact H.
    - apply (nts_aro_eq (aview SEGS (w_H W3) (ms_mem ms3))); [|exact HRO].
      intros a Hro Hns Herr. apply HX.
      + pose proof (pa_segs_low a (nts_roP_img a Hro)). unfold kLowMemEnd in *. lia.
      + intros HXa. pose proof (HXimg a HXa). pose proof (pa_segs_low a (nts_roP_img a Hro)).
        unfold kLowMemEnd, SHADOW_OFF in *. lia.
    - exact HEn. }
  destruct (nts_buf_facts cx HB) as (BK & BA).
  assert (Hbuf : forall a, (0 <= a < kLowMemEnd \/ kHighMemBeg <= a < kHighMemEnd) ->
            ~ (spZ (n_regs cx) - 8448 <= a < spZ (n_regs cx)) -> ~ X a).
  { intros a Hap Hnw HXa. destruct (HXin a HXa) as [H|H]; [lia|]. rewrite ESH in H. unfold shadow_addr in H.
    unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
  split.
  { apply (nts_bufs_keep cx (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) HBS).
    - intros a Hk Ha. destruct (BK Hk a Ha) as (Hw & Hro & Herr & Hng & Hnw & Hap).
      apply Hkeep; [| exact (Hbuf a Hap Hnw)]. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hap. lia.
    - intros a Hk Ha. destruct (BA Hk a Ha) as (Hw & Hro & Herr & Hng & Hnw & Hap).
      apply Hkeep; [| exact (Hbuf a Hap Hnw)]. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hap. lia.
    - intros a Hk Ha. destruct (BK Hk a Ha) as (Hw & Hro & _).
      exact (nts_ajw_writable cx fp k2 ly3 S3 W3 (ms_mem ms4) md4 a HB HJ4 Hperm3 Hfa3 Hw Hro).
    - intros a Hk Ha. destruct (BA Hk a Ha) as (Hw & Hro & _).
      exact (nts_ajw_writable cx fp k2 ly3 S3 W3 (ms_mem ms4) md4 a HB HJ4 Hperm3 Hfa3 Hw Hro). }
  split.
  { apply (nts_abuf_keep (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) (nBUF cx fp) NT_BUFLEN HAB).
    - intros a Ha. unfold nBUF, NT_BUFOFF, NT_BUFLEN in Ha. apply Hkeep; [unfold in_app in Fapp; rewrite EFB in Fapp; unfold ASAN_CEIL in *; lia|].
      intros HXa. apply (HXF a HXa). lia.
    - intros a Ha. apply (nts_own_frame_writable cx fp k2 ly3 S3 W3 (ms_mem ms4) md4 a HJ4 Hfa3).
      unfold nBUF, NT_BUFOFF, NT_BUFLEN in *. rewrite EFB. lia. }
  exact HER.
Qed.

(* ==========================================================================
   5. At a callee's call site
   ========================================================================== *)

Lemma nts_ajw_mono : forall G XO OUT STK sp0 FP ly S lyc Sc own lyc' Sc' own' a,
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc' Sc')) ->
  (forall x, In x own -> In x own') ->
  (forall c q, frame_addr lyc' c q = frame_addr lyc c q) ->
  ajw B G XO OUT STK sp0 FP ly S lyc' Sc' own' a.
Proof.
  intros G XO OUT STK sp0 FP ly S lyc Sc own lyc' Sc' own' a Hw Hbl Hown Hfa.
  destruct Hw as [(Haw & Hno) | [HGa | Hout]]; [left | right; left; exact HGa | right; right; exact Hout].
  split; [|exact Hno].
  destruct Haw as [Hs | [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | (c & q & Hin & Hr)]]].
  - left. exact Hs.
  - right; left. split; [exact Hf|]. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
  - right; right; left. exists b, n. split; [exact (Hbl b n Hin)|]. split; [exact Hn0 | exact Hr].
  - right; right; right. exists c, q. split; [exact (Hown _ Hin)|]. rewrite !Hfa. exact Hr.
Qed.

Lemma nts_wvb : forall md mat, m_fds (with_vm_backing (m_vm_lazy md) mat md) = m_fds md /\
  m_fs (with_vm_backing (m_vm_lazy md) mat md) = m_fs md.
Proof. intros [fd [maps lazy mt] io fs proc lim tm] mat. split; reflexivity. Qed.

Lemma nts_ap_trans : forall r1 r2 r3 : bvmap 5 word, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* the registers of nts_body across anything that keeps the callee-saved registers *)
Lemma nts_rg_keep : forall cx fp (ms ms' : machine_state), aregs_preserved (ms_regs ms) (ms_regs ms') ->
  nt_regs cx fp ms -> getr (ms_regs ms) 20 = w64 (nF cx fp) -> getr (ms_regs ms) 23 = w64 (n_aliasn cx) ->
  getr (ms_regs ms) 25 = w64 (n_alias cx) ->
  nt_regs cx fp ms' /\ getr (ms_regs ms') 20 = w64 (nF cx fp) /\ getr (ms_regs ms') 23 = w64 (n_aliasn cx) /\
  getr (ms_regs ms') 25 = w64 (n_alias cx).
Proof.
  intros cx fp ms ms' HP (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4) R20 R23 R25.
  assert (P : forall r : Z, acallee_saved r -> getr (ms_regs ms') (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
    by exact HP.
  split; [|split; [|split]].
  - split; [rewrite <- R2; exact (P 2 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- R8; exact (P 8 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- R9; exact (P 9 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- R18; exact (P 18 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- R21; exact (P 21 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- R24; exact (P 24 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- R3; exact (P 3 ltac:(unfold acallee_saved; lia))|].
    rewrite <- R4; exact (P 4 ltac:(unfold acallee_saved; lia)).
  - rewrite <- R20; exact (P 20 ltac:(unfold acallee_saved; lia)).
  - rewrite <- R23; exact (P 23 ltac:(unfold acallee_saved; lia)).
  - rewrite <- R25; exact (P 25 ltac:(unfold acallee_saved; lia)).
Qed.

(* what nl_talk's Pre says of g_nl's list, errno and the request *)
Lemma nts_pre : forall cx, nt_base SK B cx ->
  nlk_wf (n_kbs cx) /\ nk_open (n_kbs cx) = 0 /\ nk_opened (n_kbs cx) + 1 < 2 ^ 31 /\
  nk_closed (n_kbs cx) + 1 < 2 ^ 31 /\
  as_errno B = as_tp B - 164 /\ apart_frame (n_regs cx) NL_TALK_AK (as_errno B) 4 /\
  apart_gnl LA_G_NL (as_errno B) 4 /\
  0 <= n_len cx <= NL_SENT_LEN /\ amem_range (n_req cx) (n_len cx) /\
  range_addressable (ard SEGS (n_m cx)) SHADOW_OFF (n_req cx) (n_len cx) /\
  (0 < n_len cx -> shadow_hull_vis (ard SEGS (n_m cx)) (n_req cx) (n_len cx)) /\
  apart_frame (n_regs cx) NL_TALK_AK (n_req cx) (n_len cx) /\ apart_gnl LA_G_NL (n_req cx) (n_len cx).
Proof.
  intros cx HB. pose proof HB as (_ & _ & HP & HNK & _).
  destruct HP as (kbs & req & HNLK & HWF & HOPEN & HOC & HCC & HRA & HHV & HERR & HRQ & HRL & HLEN
                  & HMR & HRAQ & HHVQ & HFRQ & HGQ & HBK & HBA & HEK & HEA & HKA & HKF & HAF & HCK & HCA).
  rewrite (nts_anlk_unique _ _ _ _ HNK HNLK).
  destruct HERR as (He1 & _ & _ & He4 & He5).
  unfold n_req, n_len.
  exact (conj HWF (conj HOPEN (conj HOC (conj HCC (conj He1 (conj He4 (conj He5 (conj HLEN (conj HMR
    (conj HRAQ (conj HHVQ (conj HFRQ HGQ)))))))))))).
Qed.

(* errno at any AR state of the walk: the facts each callee's Pre asks of it *)
Lemma nts_errno_pre : forall cx ly S (W : world SEGS) m md (rg : bvmap 5 word) K,
  nt_base SK B cx -> AR SEGS B ly S W m md -> spZ rg = n_sp1 cx -> 0 <= K <= 4144 ->
  as_errno B = as_tp B - 164 /\ awrange SEGS (rdW W m) (as_errno B) 4 /\
  range_addressable (ard SEGS (rdW W m)) SHADOW_OFF (as_errno B) 4 /\
  apart_frame rg K (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4.
Proof.
  intros cx ly S W m md rg K HB HAR Hsp HK.
  destruct (nts_pre cx HB) as (_ & _ & _ & _ & He1 & He4 & He5 & _).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  pose proof NL_TALK_AK_val as HAKv.
  split; [exact He1|]. split.
  { intros i Hi. assert (HW : forall m', writable_at SEGS m' (as_errno B + i)).
    { intros m'. rewrite (AF0m.ts_errno B TB), HSEGS. apply wseg_writable_tfib_rng.
      unfold AF0m.TFIB_ERRNO. lia. }
    apply HW. }
  split; [exact (proj1 (zsh_errno_ard B TB SEGS ly S W m md HAR))|].
  split; [|exact He5]. unfold apart_frame in *. rewrite Hsp. lia.
Qed.

(* the premises every own callee of the phase takes (K <= 4144, EV 0, SIDE [], a write set inside g_nl), at a
   call made with sp = s1 from a cut whose journal holds *)
Lemma nts_apre : forall cx fp k2 ly3 S3 (W3 : world SEGS) m3 md3 mdc (rg : bvmap 5 word) K (Wr : list (Z * Z)) retk,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 m3 mdc k2 ->
  nt_jbk B cx fp k2 ly3 S3 md3 ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) m3) ->
  getr rg 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr rg 2 = w64 (n_sp1 cx) -> getr rg 3 = getr (n_regs cx) 3 -> getr rg 4 = getr (n_regs cx) 4 ->
  0 <= K <= 4144 ->
  (forall a, inFP Wr a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) ->
  apre SK SEGS PCAP_RLO PCAP_RHI B K 0 [] Wr (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx)
    (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 m3 mdc k2 rg.
Proof.
  intros cx fp k2 ly3 S3 W3 m3 md3 mdc rg K Wr retk HB HJ HJB HRO R1 Hrk Hrk2 R2 R3 R4 HK HWr.
  pose proof HB as (HA & _).
  destruct HA as (HJc & HGX & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hev & _ & _ & _).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  pose proof HJB as (Hk2 & Hperm3 & _ & Hfr3 & _ & Hfa3 & _).
  pose proof NL_TALK_AK_val as HAKv. pose proof pa_B_ok as (HB0 & HB1 & HB2).
  pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
  assert (Hsp : spZ rg = n_sp1 cx).
  { unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. pose proof alloc_ceiling_val. lia. }
  split; [exact HJ|]. split; [exact HGX|]. split; [exact HRO|].
  split; [rewrite R1; apply ret_ok_codeptr_v; assumption|].
  split; [unfold raZ; rewrite R1, unsigned_lit_small by lia; lia|].
  split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
  split; [rewrite Hsp; exact Gs16|]. split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
  split; [subst k2; rewrite Z.add_0_r in *; exact Hev|].
  split; [constructor|].
  split.
  - intros a Ha. pose proof (HWr a Ha) as Hg. destruct (nts_gnl_facts cx HB a Hg) as (Hw & _ & _).
    apply (nts_ajw_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hw).
    + intros b m Hb. apply (Permutation_in _ (Permutation_sym Hperm3)). exact Hb.
    + intros x Hx. right. exact Hx.
    + exact Hfa3.
  - intros a Ha. exact (proj1 (proj2 (nts_gnl_facts cx HB a (HWr a Ha)))).
Qed.

(* the stack row of any state of a journal is its start's *)
Lemma nts_row_eq : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ly_stk_lo lyc = ly_stk_lo ly /\ ly_stk_hi lyc = ly_stk_hi ly.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (_ & _ & (memS & HJ & _) & _).
  destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  split; assumption.
Qed.

(* the class-9 slot is a real slot *)
Lemma nts_pos : forall cx fp k2 ly3 S3 (W3 : world SEGS) mem3 md3,
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  In (NT_CID, fp) (frames S3) -> 0 <= fp < fs_frames NT_CID.
Proof.
  intros cx fp k2 ly3 S3 W3 mem3 md3 HJ Hin.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). destruct HJi as ((M & _) & _).
  destruct (frame_facts B ly3 S3 _ NT_CID fp M Hin) as (_ & H & _). exact H.
Qed.

(* the union of the callees' write sets in g_nl, the exception set of every cut after fuzz_socket *)
Definition nts_EW (a : Z) : Prop := LA_G_NL + NK_SOCKET_ERRNO <= a < LA_G_NL + NK_N_SENT + 4.

Lemma nts_dyn_mono : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 (E : Z -> Prop),
  nt_base SK B cx -> nts_dyn cx fp k2 ly3 S3 W3 ms3 md3 E -> (forall a, E a -> nts_EW a) ->
  nts_dyn cx fp k2 ly3 S3 W3 ms3 md3 nts_EW.
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 E HB (HJB & (HK & HRO & HEn) & HBS & HAB & HER) HE.
  split; [exact HJB|]. split; [|split; [exact HBS | split; [exact HAB|]]].
  - split; [|split; [exact HRO|]].
    + apply (akept_mono SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK).
      intros a [H|H]; [left; exact (HE a H) | right; exact H].
    + intros a Ha. apply (nts_gnl_facts cx HB a). unfold nts_EW, NK_SOCKET_ERRNO in Ha. lia.
  - intros a Ha. exact Ha.
Qed.

(* the caller's request at a cut: its bytes, its shadow, and its place for the read set of fuzz_send *)
Lemma nts_req : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  nts_dyn cx fp k2 ly3 S3 W3 ms3 md3 nts_EW ->
  abytes SEGS (rdW W3 (ms_mem ms3)) (n_req cx) (n_reqb cx) /\
  range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF (n_req cx) (n_len cx) /\
  (0 < n_len cx -> shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms3))) (n_req cx) (n_len cx)) /\
  (forall slo shi a, spZ (n_regs cx) - NL_TALK_AK <= slo -> shi <= spZ (n_regs cx) ->
     n_req cx <= a < n_req cx + n_len cx -> akb SEGS B ly3 S3 slo shi a).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 (HJB & (HK & _ & _) & _).
  pose proof HB as (HA & HRD & _ & _ & HRQ & HRL & _).
  pose proof HA as (HJc & _).
  destruct (nts_pre cx HB) as (_ & _ & _ & _ & _ & _ & _ & HLEN & HMR & HRAQ & HHVQ & HFRQ & HGQ).
  destruct (nts_frame cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ3 HJB)
    as (Hin & Efa & F4096 & Fceil & F64 & ESH & EFB & Fapp & HAR3).
  pose proof HJB as (Hk2 & Hperm3 & Hset3 & Hfr3 & Hnin & Hfa3 & _).
  pose proof (nts_pos cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HJ3 Hin) as Hfp.
  assert (HARc : AR SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx))
    by (destruct HJc as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
  assert (Hakb : forall a, n_req cx <= a < n_req cx + n_len cx ->
            akb SEGS B (n_lyc cx) (n_Sc cx) (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) a)
    by (intros a Ha; apply HRD; exact Ha).
  assert (HnE : forall a, n_req cx <= a < n_req cx + n_len cx -> ~ (nts_EW a \/ aside_rng (n_lyc cx) NT_CID fp a)).
  { intros a Ha [H|H].
    - unfold apart_gnl, nts_EW, NK_SOCKET_ERRNO, NK_N_SENT, NK_SIZE in *. lia.
    - exact (akb_not_side SK SEGS B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NT_CID fp a HJc
        ltac:(unfold NT_CID; lia) Hfp Hnin (Hakb a Ha) H). }
  assert (Hkeep : forall a, n_req cx <= a < n_req cx + n_len cx ->
            aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (n_W cx)) (n_memc cx) a)
    by (intros a Ha; exact (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc HK
          (Hakb a Ha) (HnE a Ha))).
  destruct (nts_row_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (E3lo & E3hi).
  destruct (nts_row_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Eclo & Echi).
  split.
  { destruct HRQ as (H0 & H1 & Hb). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). apply (mbyte_of_aview SEGS). apply Hkeep.
    unfold n_len, n_req in *. lia. }
  assert (HSH : 0 < n_len cx ->
    range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (n_req cx) (n_len cx) /\
    shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) (n_req cx) (n_len cx)).
  { intros Hn. apply (shadow_transport_akb SEGS B LAWS TB pa_img_range (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx)
      (n_mdc cx) ly3 S3 W3 (ms_mem ms3) md3 (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx))
      (fun a => nts_EW a \/ aside_rng (n_lyc cx) NT_CID fp a) (n_req cx) (n_len cx) HARc HAR3); try lia.
    - intros b m Hb. apply (Permutation_in _ (Permutation_sym Hperm3)). exact Hb.
    - exact HK.
    - apply fmiss_or.
      + apply (fmiss_app SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ HARc).
        intros a Ha. left. unfold nts_EW, LA_G_NL, NK_N_SENT, kLowMemEnd in *. lia.
      + exact (fmiss_side SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
          NT_CID fp HARc ltac:(unfold NT_CID; lia) Hfp Hnin).
    - exact Hakb.
    - exact HRAQ.
    - exact (HHVQ Hn). }
  split.
  { destruct (Z_lt_le_dec 0 (n_len cx)) as [Hn|Hn]; [exact (proj1 (HSH Hn))|]. intros x Hx. lia. }
  split; [intros Hn; exact (proj2 (HSH Hn))|].
  intros slo shi a Hslo Hshi Ha.
  destruct (Hakb a Ha) as [(H1 & H2) | [(b & m & Hb & Hr) | [H3 | (c & q & Hcq & Hr)]]].
  - left. rewrite E3lo, E3hi, <- Eclo, <- Echi. split; [exact H1 | lia].
  - right; left. exists b, m. split; [apply (Permutation_in _ (Permutation_sym Hperm3)); exact Hb | exact Hr].
  - right; right; left. exact H3.
  - right; right; right. exists c, q. split; [rewrite Hfr3; right; exact Hcq|].
    unfold frame_rng in *. cbn [fst snd] in *. rewrite Hfa3. exact Hr.
Qed.

(* ==========================================================================
   6. The runs
   ========================================================================== *)

Definition nts_SB : Z := 0x7fff8000.
Definition nts_Bx : sv := SOff 21 0.          (* s5 holds the shadow base at every cut of the phase *)
Definition nts_span : Z * Z := (nts_SB, nts_SB + 2 ^ 44 - 1).
(* errno, read through a0 (the 4-byte region of atom 10; its value is the extra atom 33) *)
Definition nts_ERR : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition nts_fe : list (nat * afact) :=
  [(10%nat, mkAF 4096 (nts_SB - 4) 2); (33%nat, mkAF 1 (2 ^ 31 - 1) 0); (21%nat, mkAF nts_SB nts_SB 0)].
Definition nts_SHE : list shent := [mkSHE 10 0 4].

Lemma nts_frame_of_ro : forall E rs (m m' : word -> option byte),
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> frame_of E rs m m' -> m' = m.
Proof.
  intros E rs m m' Hro H. apply functional_extensionality. intros x. apply H.
  intros (r & Hin & Hr). pose proof (Hro r Hin). lia.
Qed.

Lemma nts_neg : forall E n e, ew E n = Z_to_bv 64 e -> 0 <= e < 2 ^ 63 ->
  sv_denot E (SAlu ALU_SUB (SLit 0) (SOff n 0)) = w64 (- e).
Proof.
  intros E n e Hn He. rewrite denot_lit_U, U_SAlu, U_SLit, (U_atom E n e Hn) by lia.
  unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. cbn [zalu_raw].
  unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_0_l by lia. rewrite Z.mod_mod by lia. f_equal; lia.
Qed.

Lemma nts_kept_nE : forall cx fp (W : world SEGS) m, nt_base SK B cx ->
  nt_kept B cx nts_EW fp W m -> nt_kept B cx (n_E cx) fp W m.
Proof.
  intros cx fp W m HB (HK & HRO & HEn). split; [|split; [exact HRO | intros a Ha; exact Ha]].
  apply (akept_mono SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK).
  intros a [H|H]; [left; exact (HEn a H) | right; exact H].
Qed.

(* the registers of the body a run leaves alone *)
Lemma nts_rg_of : forall cx fp (ms ms' : machine_state),
  (forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  nt_regs cx fp ms -> getr (ms_regs ms) 20 = w64 (nF cx fp) -> getr (ms_regs ms) 23 = w64 (n_aliasn cx) ->
  getr (ms_regs ms) 25 = w64 (n_alias cx) ->
  nt_regs cx fp ms' /\ getr (ms_regs ms') 20 = w64 (nF cx fp) /\ getr (ms_regs ms') 23 = w64 (n_aliasn cx) /\
  getr (ms_regs ms') 25 = w64 (n_alias cx).
Proof.
  intros cx fp ms ms' HP (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4) R20 R23 R25.
  split; [|split; [|split]].
  - split; [rewrite <- R2; apply HP; cbn; tauto|].
    split; [rewrite <- R8; apply HP; cbn; tauto|].
    split; [rewrite <- R9; apply HP; cbn; tauto|].
    split; [rewrite <- R18; apply HP; cbn; tauto|].
    split; [rewrite <- R21; apply HP; cbn; tauto|].
    split; [rewrite <- R24; apply HP; cbn; tauto|].
    split; [rewrite <- R3; apply HP; cbn; tauto|].
    rewrite <- R4; apply HP; cbn; tauto.
  - rewrite <- R20; apply HP; cbn; tauto.
  - rewrite <- R23; apply HP; cbn; tauto.
  - rewrite <- R25; apply HP; cbn; tauto.
Qed.

Ltac nts_awr_ro :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* a register the run left alone, at the end of a run from a seat over Eimg (Ereg regs ext) *)
Ltac nts_kreg HS HEdef :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr (ms_regs _) ?rr = _ =>
        let Q := fresh "Q" in prreg HS rr Q; rewrite Q, HEdef; apply nts_ew_reg; reflexivity end |]);
  try destruct Hr.

(* ==========================================================================
   7. The calls, and g_nl's fields across them
   ========================================================================== *)

Lemma nts_vals : BASE = 0x821cc /\ pa_sigma LS_fuzz_socket = FUZZ_SOCKET_A /\ pa_sigma LS_fuzz_send = FUZZ_SEND_A /\
  pa_sigma LS_fuzz_close = FUZZ_CLOSE_A.
Proof.
  split; [exact (lv_text LV)|].
  split; [|split]; rewrite (lv_sigma LV); reflexivity.
Qed.

Lemma nts_owned_gnl_b : forallb (fun r => (LA_G_NL + NK_SIZE <=? fst r) || (fst r + snd r <=? LA_G_NL))
  AF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nts_gnl_not_owned : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
  intros a Ha HE. rewrite (AF0m.ts_owned B TB) in HE. apply Exists_exists in HE as (r & Hr & Hin).
  pose proof nts_owned_gnl_b as H. rewrite forallb_forall in H. specialize (H r Hr).
  destruct r as [b n]. unfold in_zr in Hin. cbn [fst snd] in *.
  apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* g_nl's bytes across a callee whose write set lies in [g + lo, g + hi) *)
Lemma nts_gnl_kept : forall cx ly3 S3 (W3 : world SEGS) m3 (W4 : world SEGS) m4 slo shi (Ec : Z -> Prop) lo hi bs bs',
  nt_base SK B cx ->
  akept SEGS B ly3 S3 W3 m3 W4 m4 slo shi Ec ->
  (forall a, Ec a -> LA_G_NL + lo <= a < LA_G_NL + hi) ->
  anlk_at SEGS (rdW W3 m3) LA_G_NL bs -> anlk_at SEGS (rdW W4 m4) LA_G_NL bs' ->
  nts_gsame lo hi bs bs'.
Proof.
  intros cx ly3 S3 W3 m3 W4 m4 slo shi Ec lo hi bs bs' HB HK HEc H1 H2.
  destruct (nts_pre cx HB) as (_ & _ & _ & _ & _ & _ & HEg & _).
  apply (nts_gsame_of _ _ _ _ _ _ H1 H2). intros i Hi Hn.
  apply (mbyte_of_aview SEGS). destruct HK as (_ & _ & K3 & _).
  apply K3.
  - rewrite HSEGS. apply nts_gnl_img. lia.
  - apply nts_gnl_not_owned. lia.
  - unfold apart_gnl in HEg. lia.
  - intros HE. apply HEc in HE. lia.
Qed.

Lemma nts_gsame_widen : forall lo hi lo' hi' bs bs', nts_gsame lo hi bs bs' -> lo' <= lo -> hi <= hi' ->
  nts_gsame lo' hi' bs bs'.
Proof. intros lo hi lo' hi' bs bs' (L & H) H1 H2. split; [exact L|]. intros k Hk Hn. apply H; [exact Hk | lia]. Qed.

Lemma nts_gsame_u32 : forall lo hi bs bs' off, nts_gsame lo hi bs bs' -> Z.of_nat (length bs) = NK_SIZE ->
  0 <= off -> off + 4 <= NK_SIZE -> (off + 4 <= lo \/ hi <= off) -> fld_u32 bs' off = fld_u32 bs off.
Proof. intros lo hi bs bs' off Hs HL H0 H1 H2. unfold fld_u32. apply (nts_gsame_rdn lo hi); [exact Hs | lia | lia | lia | exact H2]. Qed.

(* ---- an own callee (an aleaf contract) at a call site of the phase ---- *)
Lemma nts_call : forall pc Kc Pre Wr Post,
  aleaf SK SEGS PCAP_RLO PCAP_RHI B pc Kc 0 [] Pre Wr Post ->
  forall cx fp k2 ly3 S3 (W3 : world SEGS) mem3 mdc md3 (rg : bvmap 5 word) retk (Q : world SEGS -> config -> Prop),
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mem3 mdc k2 ->
  nt_jbk B cx fp k2 ly3 S3 md3 ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) mem3) ->
  getr rg 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr rg 2 = w64 (n_sp1 cx) -> getr rg 3 = getr (n_regs cx) 3 -> getr rg 4 = getr (n_regs cx) 4 ->
  0 <= Kc <= 4144 ->
  (forall a, inFP (Wr rg (rdW W3 mem3)) a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) ->
  Pre rg (rdW W3 mem3) ->
  (forall ly4 S4 (W4 : world SEGS) rg2 mem4 md4,
     ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
       (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly4 S4 W4 mem4 md4 k2 ->
     aregs_preserved rg rg2 -> frames S4 = frames S3 -> m_fds md4 = m_fds mdc -> m_fs md4 = m_fs mdc ->
     akept SEGS B ly3 S3 W3 mem3 W4 mem4 (spZ rg - Kc) (spZ rg) (fun a => inFP (Wr rg (rdW W3 mem3)) a) ->
     S4 = set_fs (st_fs S4) S3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
     Post rg (rdW W3 mem3) rg2 (rdW W4 mem4) ->
     SRr SEGS W4 (mkCfg (mkst rg2 (Z_to_bv 64 (BASE + retk)) mem4 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 pc) mem3 (seg_rom SEGS)) mdc) Q.
Proof.
  intros pc Kc Pre Wr Post CT cx fp k2 ly3 S3 W3 mem3 mdc md3 rg retk Q HB HJ HJB HRO R1 Hrk Hrk2 R2 R3 R4 HK HWr HPre K.
  change (mkCfg (mkst rg (Z_to_bv 64 pc) mem3 (seg_rom SEGS)) mdc) with (cfg_at SEGS pc rg mem3 mdc).
  eapply SRr_bind.
  { apply CT; [|exact HPre].
    exact (nts_apre cx fp k2 ly3 S3 W3 mem3 md3 mdc rg Kc _ retk HB HJ HJB HRO R1 Hrk Hrk2 R2 R3 R4 HK HWr). }
  cbv beta. intros W4 c4 _ (ly4 & S4 & rg2 & mem4 & md4 & -> & HJ4 & HP & Hfr & Hfd & Hfs & HK4 & _ & Hset & Hperm & HPost).
  rewrite Z.add_0_r in HJ4. rewrite R1.
  exact (K ly4 S4 W4 rg2 mem4 md4 HJ4 HP Hfr Hfd Hfs HK4 Hset Hperm HPost).
Qed.

(* ... and one with a read set (aleaf_rd) *)
Lemma nts_call_rd : forall pc Kc Pre Rd Wr Post,
  aleaf_rd SK SEGS PCAP_RLO PCAP_RHI B pc Kc 0 [] Pre Rd Wr Post ->
  forall cx fp k2 ly3 S3 (W3 : world SEGS) mem3 mdc md3 (rg : bvmap 5 word) retk (Q : world SEGS -> config -> Prop),
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mem3 mdc k2 ->
  nt_jbk B cx fp k2 ly3 S3 md3 ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) mem3) ->
  getr rg 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr rg 2 = w64 (n_sp1 cx) -> getr rg 3 = getr (n_regs cx) 3 -> getr rg 4 = getr (n_regs cx) 4 ->
  0 <= Kc <= 4144 ->
  (forall a, inFP (Wr rg (rdW W3 mem3)) a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) ->
  (forall a, Rd rg (rdW W3 mem3) a -> akb SEGS B ly3 S3 (spZ rg - Kc) (spZ rg) a) ->
  Pre rg (rdW W3 mem3) ->
  (forall ly4 S4 (W4 : world SEGS) rg2 mem4 md4,
     ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
       (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly4 S4 W4 mem4 md4 k2 ->
     aregs_preserved rg rg2 -> frames S4 = frames S3 -> m_fds md4 = m_fds mdc -> m_fs md4 = m_fs mdc ->
     akept SEGS B ly3 S3 W3 mem3 W4 mem4 (spZ rg - Kc) (spZ rg) (fun a => inFP (Wr rg (rdW W3 mem3)) a) ->
     S4 = set_fs (st_fs S4) S3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
     Post rg (rdW W3 mem3) rg2 (rdW W4 mem4) ->
     SRr SEGS W4 (mkCfg (mkst rg2 (Z_to_bv 64 (BASE + retk)) mem4 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 pc) mem3 (seg_rom SEGS)) mdc) Q.
Proof.
  intros pc Kc Pre Rd Wr Post CT cx fp k2 ly3 S3 W3 mem3 mdc md3 rg retk Q HB HJ HJB HRO R1 Hrk Hrk2 R2 R3 R4 HK HWr
    HRd HPre K.
  change (mkCfg (mkst rg (Z_to_bv 64 pc) mem3 (seg_rom SEGS)) mdc) with (cfg_at SEGS pc rg mem3 mdc).
  eapply SRr_bind.
  { apply CT; [| exact HRd | exact HPre].
    exact (nts_apre cx fp k2 ly3 S3 W3 mem3 md3 mdc rg Kc _ retk HB HJ HJB HRO R1 Hrk Hrk2 R2 R3 R4 HK HWr). }
  cbv beta. intros W4 c4 _ (ly4 & S4 & rg2 & mem4 & md4 & -> & HJ4 & HP & Hfr & Hfd & Hfs & HK4 & _ & Hset & Hperm & HPost).
  rewrite Z.add_0_r in HJ4. rewrite R1.
  exact (K ly4 S4 W4 rg2 mem4 md4 HJ4 HP Hfr Hfd Hfs HK4 Hset Hperm HPost).
Qed.

(* ---- ___errno_location at a call site of the phase ---- *)
Lemma nts_call_errno : forall cx fp k2 ly3 S3 (W3 : world SEGS) mem3 mdc (rg : bvmap 5 word) retk
    (Q : world SEGS -> config -> Prop),
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mem3 mdc k2 ->
  getr rg 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr rg 2 = w64 (n_sp1 cx) -> getr rg 4 = getr (n_regs cx) 4 ->
  (forall rg2 md4, same_but_materialized mdc md4 ->
     ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
       (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md4 k2 ->
     getr rg2 10 = w64 (as_errno B) ->
     (forall r, 1 <= r < 32 -> r <> 10 -> getr rg2 (Z_to_bv 5 r) = getr rg (Z_to_bv 5 r)) ->
     SRr SEGS W3 (mkCfg (mkst rg2 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 (pa_sigma LS____errno_location)) mem3 (seg_rom SEGS)) mdc) Q.
Proof.
  intros cx fp k2 ly3 S3 W3 mem3 mdc rg retk Q HB HJ R1 Hrk Hrk2 R2 R4 K.
  pose proof HB as (HA & _).
  destruct HA as (HJc & HGX & _ & _ & _ & Hgp & Htp & _).
  destruct (nts_pre cx HB) as (_ & _ & _ & _ & He1 & _).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  pose proof NL_TALK_AK_val as HAKv. pose proof alloc_ceiling_val as Hac.
  pose proof pa_B_ok as (HB0 & HB1 & HB2).
  pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
  assert (Hsp : spZ rg = n_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  destruct (nts_row_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Elo & Ehi).
  eapply SRr_bind.
  { apply (aj_gx_errno_at SK SEGS B LAWS pa_segs_low (pa_sigma LS____errno_location) ERRNO (n_G cx) (n_XO cx)
      (n_OUT cx) W3 rg mem3 (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      ((NT_CID, fp) :: n_own cx) ly3 S3 mdc k2 (Z_to_bv 64 (BASE + retk)) HGX HJ); [rewrite Hsp; lia | rewrite Hsp; lia | exact R1 |].
    apply ret_ok_codeptr_v; lia. }
  cbv beta. intros W4 c4 _ (-> & rg2 & mem2 & md2 & -> & HJ2 & Hsm & H10 & Hr & Hm).
  assert (Em : mem2 = mem3) by (apply functional_extensionality; exact Hm). subst mem2.
  apply (K rg2 md2 Hsm HJ2); [| exact Hr].
  rewrite H10, R4, Htp. pose proof (AF0m.ts_tp B TB) as Htp'. unfold AF0m.TFIB_TP in Htp'.
  unfold w64. rewrite unsigned_lit_small by (rewrite Htp'; lia). rewrite He1. reflexivity.
Qed.

(* nts_body to a state with the same memory, the body's registers and the same fds and fs *)
Lemma nts_body_move : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms md (E : Z -> Prop) v ms' md',
  nts_body cx fp k2 ly3 S3 W3 ms md E v ->
  (forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  ms_mem ms' = ms_mem ms -> m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  nts_body cx fp k2 ly3 S3 W3 ms' md' E v.
Proof.
  intros cx fp k2 ly3 S3 W3 ms md E v ms' md' (Hrg & R20 & R23 & R25 & Hst & HD) Hregs Hm Hfd Hfs.
  destruct (nts_rg_of cx fp ms ms' Hregs Hrg R20 R23 R25) as (Hrg' & R20' & R23' & R25').
  split; [exact Hrg'|]. split; [exact R20'|]. split; [exact R23'|]. split; [exact R25'|].
  split; [exact (nts_stat_keep cx fp W3 W3 ms ms' v ltac:(intros a _; rewrite Hm; reflexivity) Hst)|].
  destruct HD as ((J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9) & HKP & HBS & HAB & HER).
  split; [|split; [rewrite Hm; exact HKP | split; [rewrite Hm; exact HBS | split; [rewrite Hm; exact HAB | exact HER]]]].
  repeat (split; [assumption|]). split; [rewrite Hfd; exact J8 | rewrite Hfs; exact J9].
Qed.

(* the same across a call that keeps the callee-saved registers *)
Lemma nts_body_call_regs : forall (ms ms' : machine_state),
  aregs_preserved (ms_regs ms) (ms_regs ms') ->
  forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms') r = getr (ms_regs ms) r.
Proof.
  intros ms ms' HP r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ ?rr = _ =>
        let z := eval vm_compute in (bv_unsigned rr) in apply (HP z); unfold acallee_saved; lia end |]).
  destruct Hr.
Qed.

Lemma nts_regs_trans : forall (r1 r2 r3 : bvmap 5 word),
  (forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr r2 r = getr r1 r) ->
  (forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr r3 r = getr r2 r) ->
  forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr r3 r = getr r1 r.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma nts_body_mono : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms md (E : Z -> Prop) v,
  nt_base SK B cx -> nts_body cx fp k2 ly3 S3 W3 ms md E v -> (forall a, E a -> nts_EW a) ->
  nts_body cx fp k2 ly3 S3 W3 ms md nts_EW v.
Proof.
  intros cx fp k2 ly3 S3 W3 ms md E v HB (H1 & H2 & H3 & H4 & H5 & HD) HE.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (nts_dyn_mono cx fp k2 ly3 S3 W3 ms md E HB HD HE)))))).
Qed.

(* nts_body across an own callee called with sp = s1 *)
Lemma nts_body_call : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms md v Kc (Ec : Z -> Prop) ly4 S4 (W4 : world SEGS)
    ms4 md4,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  nts_body cx fp k2 ly3 S3 W3 ms md nts_EW v ->
  0 <= Kc <= 4144 -> (forall a, Ec a -> nts_EW a) ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly4 S4 W4 (ms_mem ms4) md4 k2 ->
  aregs_preserved (ms_regs ms) (ms_regs ms4) -> frames S4 = frames S3 -> m_fds md4 = m_fds md -> m_fs md4 = m_fs md ->
  akept SEGS B ly3 S3 W3 (ms_mem ms) W4 (ms_mem ms4) (spZ (ms_regs ms) - Kc) (spZ (ms_regs ms)) Ec ->
  S4 = set_fs (st_fs S4) S3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  nts_body cx fp k2 ly4 S4 W4 ms4 md4 nts_EW v.
Proof.
  intros cx fp k2 ly3 S3 W3 ms md v Kc Ec ly4 S4 W4 ms4 md4 HB HJ HBD HKc HEc HJ4 HP Hfr Hfd Hfs HK Hset Hperm.
  destruct HBD as (Hrg & R20 & R23 & R25 & Hst & HD).
  pose proof Hrg as (R2 & _).
  pose proof alloc_ceiling_val as Hac. pose proof NL_TALK_AK_val as HAKv.
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  assert (Hsp : spZ (ms_regs ms) = n_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  destruct (nts_dyn_call cx fp k2 ly3 S3 W3 ms md nts_EW (ms_regs ms) md Kc Ec ly4 S4 W4 ms4 md4 HB HJ HD Hsp HKc
    eq_refl eq_refl HEc HJ4 Hfr Hfd Hfs HK Hset Hperm) as (HD4 & Hfoot).
  destruct (nts_rg_of cx fp ms ms4 (nts_body_call_regs ms ms4 HP) Hrg R20 R23 R25) as (Hrg' & R20' & R23' & R25').
  split; [exact Hrg'|]. split; [exact R20'|]. split; [exact R23'|]. split; [exact R25'|].
  split; [exact (nts_stat_keep cx fp W3 W4 ms ms4 v Hfoot Hst)|].
  apply (nts_dyn_mono cx fp k2 ly4 S4 W4 ms4 md4 _ HB HD4). intros a [H|H]; [exact H | exact (HEc a H)].
Qed.

(* ==========================================================================
   8. g_nl's model fields along the three paths
   ========================================================================== *)

Lemma nts_kbs : forall cx, nt_base SK B cx ->
  nlk_wf (n_kbs cx) /\ Z.of_nat (length (n_kbs cx)) = NK_SIZE /\ nk_open (n_kbs cx) = 0 /\
  nk_opened (n_kbs cx) + 1 < 2 ^ 31 /\ nk_closed (n_kbs cx) + 1 < 2 ^ 31.
Proof.
  intros cx HB. destruct (nts_pre cx HB) as (HWF & HOP & HOC & HCC & _).
  pose proof HB as (_ & _ & _ & HNK & _).
  exact (conj HWF (conj (nts_anlk_len _ _ _ HNK) (conj HOP (conj HOC HCC)))).
Qed.

Lemma nts_K0 : forall cx, k_sock (n_K0 cx) = nk_socket_errno (n_kbs cx) /\ k_send (n_K0 cx) = nk_send_errno (n_kbs cx) /\
  k_chunks (n_K0 cx) = nk_chunks (n_kbs cx) /\ k_next (n_K0 cx) = Z.to_nat (nk_next (n_kbs cx)) /\
  k_end (n_K0 cx) = nk_end_errno (n_kbs cx).
Proof. intros cx. repeat split; reflexivity. Qed.

(* after fuzz_socket succeeded *)
Definition nts_g1 (cx : ntcx) (bs : list byte) : Prop :=
  Z.of_nat (length bs) = NK_SIZE /\ nlk_wf bs /\ nts_gsame NK_SOCKET_ERRNO (NK_MISUSE + 4) (n_kbs cx) bs /\
  nk_socket_errno bs = 0 /\ nk_send_errno bs = nk_send_errno (n_kbs cx) /\
  nk_end_errno bs = nk_end_errno (n_kbs cx) /\ nk_open bs = 1 /\ nk_opened bs = nk_opened (n_kbs cx) + 1 /\
  nk_closed bs = nk_closed (n_kbs cx) /\ nk_misuse bs = nk_misuse (n_kbs cx).

(* after fuzz_socket succeeded and fuzz_send failed *)
Definition nts_g2f (cx : ntcx) (bs : list byte) : Prop :=
  Z.of_nat (length bs) = NK_SIZE /\ nlk_wf bs /\ nts_gsame NK_SOCKET_ERRNO (NK_N_SENT + 4) (n_kbs cx) bs /\
  nk_socket_errno bs = 0 /\ nk_send_errno bs = 0 /\
  nk_end_errno bs = nk_end_errno (n_kbs cx) /\ nk_open bs = 1 /\ nk_opened bs = nk_opened (n_kbs cx) + 1 /\
  nk_closed bs = nk_closed (n_kbs cx) /\ nk_misuse bs = nk_misuse (n_kbs cx) /\ nk_sent bs = nk_sent (n_kbs cx).

Lemma nts_g_sock_fail : forall cx bs, nt_base SK B cx -> nk_socket_errno (n_kbs cx) <> 0 ->
  Z.of_nat (length bs) = NK_SIZE -> nlk_wf bs -> nts_gsame NK_SOCKET_ERRNO (NK_MISUSE + 4) (n_kbs cx) bs ->
  nk_send_errno bs = nk_send_errno (n_kbs cx) -> nk_end_errno bs = nk_end_errno (n_kbs cx) ->
  nk_closed bs = nk_closed (n_kbs cx) -> nk_socket_errno bs = 0 -> nk_open bs = nk_open (n_kbs cx) ->
  nk_opened bs = nk_opened (n_kbs cx) -> nk_misuse bs = nk_misuse (n_kbs cx) ->
  nt_gnl_fin cx bs.
Proof.
  intros cx bs HB Hse HL WF Hs Fsd Fend Fcl Fso Fop Fopd Fmis.
  destruct (nts_kbs cx HB) as (WF0 & HL0 & HOP & _).
  pose proof WF0 as (_ & (Wn0 & _) & _).
  destruct (nts_gsame_fields _ _ _ _ WF0 HL0 Hs ltac:(lia) ltac:(unfold NK_MISUSE, NK_N_SENT; lia))
    as (Fch & Fnch & Fnx & Fe & Fif & _).
  destruct (nts_gsame_sent _ _ _ _ WF0 HL0 Hs ltac:(unfold NK_MISUSE, NK_SENT; lia)) as (Fsn & _).
  destruct (nt_talk_sock (n_K0 cx) ltac:(rewrite (proj1 (nts_K0 cx)); exact Hse)) as (_ & _ & Ta & To).
  destruct (nts_K0 cx) as (Ks & Kd & Kc & Kn & Ke).
  split; [exact WF|]. split; [exact Fch|]. split; [exact Fend|]. split; [exact Fif|]. split; [exact Fso|].
  split; [rewrite Ta; cbn [k_send]; rewrite Kd; exact Fsd|].
  split; [rewrite Ta; cbn [k_next]; rewrite Kn, Z2Nat.id by lia; exact Fnx|].
  split; [rewrite To; exact Fsn|].
  split; [exact (nt_nk_sent_len bs WF)|].
  split; [rewrite Fop; exact HOP|]. split; [exact Fmis|]. split; [lia|].
  split; [intros _; exact Fopd | intros H; contradiction].
Qed.

Lemma nts_g_sock_ok : forall cx bs, nt_base SK B cx ->
  Z.of_nat (length bs) = NK_SIZE -> nlk_wf bs -> nts_gsame NK_SOCKET_ERRNO (NK_MISUSE + 4) (n_kbs cx) bs ->
  nk_send_errno bs = nk_send_errno (n_kbs cx) -> nk_end_errno bs = nk_end_errno (n_kbs cx) ->
  nk_closed bs = nk_closed (n_kbs cx) -> nk_socket_errno bs = 0 -> nk_open bs = 1 ->
  nk_opened bs = nk_opened (n_kbs cx) + 1 ->
  nk_misuse bs = (if nk_open (n_kbs cx) =? 0 then nk_misuse (n_kbs cx) else 1) ->
  nts_g1 cx bs.
Proof.
  intros cx bs HB HL WF Hs Fsd Fend Fcl Fso Fop Fopd Fmis.
  destruct (nts_kbs cx HB) as (_ & _ & HOP & _). rewrite HOP in Fmis. cbn in Fmis.
  repeat (split; [assumption|]). exact Fmis.
Qed.

Lemma nts_g_send_fail : forall cx bs1 bs, nt_base SK B cx -> nts_g1 cx bs1 ->
  Z.of_nat (length bs) = NK_SIZE -> nlk_wf bs -> nts_gsame NK_SEND_ERRNO (NK_N_SENT + 4) bs1 bs ->
  nk_socket_errno bs = nk_socket_errno bs1 -> nk_end_errno bs = nk_end_errno bs1 ->
  nk_open bs = nk_open bs1 -> nk_opened bs = nk_opened bs1 -> nk_closed bs = nk_closed bs1 ->
  nk_misuse bs = nk_misuse bs1 -> nk_send_errno bs = 0 -> nk_sent bs = nk_sent bs1 ->
  nts_g2f cx bs.
Proof.
  intros cx bs1 bs HB (HL1 & WF1 & Hs1 & S1 & D1 & E1 & O1 & P1 & C1 & M1) HL WF Hs Fso Fend Fop Fopd Fcl Fmis Fsd Fsn.
  destruct (nts_kbs cx HB) as (WF0 & HL0 & _).
  destruct (nts_gsame_sent _ _ _ _ WF0 HL0 Hs1 ltac:(unfold NK_MISUSE, NK_SENT; lia)) as (Fsn1 & _).
  split; [exact HL|]. split; [exact WF|].
  split; [apply (nts_gsame_trans NK_SOCKET_ERRNO (NK_N_SENT + 4) NK_SEND_ERRNO (NK_N_SENT + 4) _ bs1 _);
          [apply (nts_gsame_widen _ _ _ _ _ _ Hs1); unfold NK_MISUSE, NK_N_SENT; lia | exact Hs
          | unfold NK_SOCKET_ERRNO, NK_SEND_ERRNO; lia | lia]|].
  split; [rewrite Fso; exact S1|]. split; [exact Fsd|]. split; [rewrite Fend; exact E1|].
  split; [rewrite Fop; exact O1|]. split; [rewrite Fopd; exact P1|]. split; [rewrite Fcl; exact C1|].
  split; [rewrite Fmis; exact M1|]. rewrite Fsn; exact Fsn1.
Qed.

Lemma nts_g_send_ok : forall cx bs1 bs, nt_base SK B cx -> nts_g1 cx bs1 ->
  Z.of_nat (length bs) = NK_SIZE -> nlk_wf bs -> nts_gsame NK_SEND_ERRNO (NK_N_SENT + 4) bs1 bs ->
  nk_socket_errno bs = nk_socket_errno bs1 -> nk_end_errno bs = nk_end_errno bs1 ->
  nk_open bs = nk_open bs1 -> nk_opened bs = nk_opened bs1 -> nk_closed bs = nk_closed bs1 ->
  nk_misuse bs = nk_misuse bs1 -> nk_send_errno bs = 0 ->
  nk_sent bs = owe (nk_sent bs1) (n_reqb cx) -> nk_n_sent bs = Z.of_nat (length (owe (nk_sent bs1) (n_reqb cx))) ->
  nt_gnl_open cx bs true (Z.of_nat (k_next (n_K0 cx))).
Proof.
  intros cx bs1 bs HB (HL1 & WF1 & Hs1 & S1 & D1 & E1 & O1 & P1 & C1 & M1) HL WF Hs Fso Fend Fop Fopd Fcl Fmis Fsd
    Fsn Fnsn.
  destruct (nts_kbs cx HB) as (WF0 & HL0 & _).
  pose proof WF0 as (_ & (Wn0 & _) & _).
  assert (Hs2 : nts_gsame NK_SOCKET_ERRNO (NK_N_SENT + 4) (n_kbs cx) bs).
  { apply (nts_gsame_trans NK_SOCKET_ERRNO (NK_N_SENT + 4) NK_SEND_ERRNO (NK_N_SENT + 4) _ bs1 _);
      [apply (nts_gsame_widen _ _ _ _ _ _ Hs1); unfold NK_MISUSE, NK_N_SENT; lia | exact Hs
      | unfold NK_SOCKET_ERRNO, NK_SEND_ERRNO; lia | lia]. }
  destruct (nts_gsame_fields _ _ _ _ WF0 HL0 Hs2 ltac:(lia) ltac:(lia)) as (Fch & Fnch & Fnx & Fe & Fif & _).
  destruct (nts_gsame_sent _ _ _ _ WF0 HL0 Hs1 ltac:(unfold NK_MISUSE, NK_SENT; lia)) as (Fsn1 & _).
  destruct (nts_K0 cx) as (Ks & Kd & Kc & Kn & Ke).
  split; [exact WF|]. split; [exact Fch|]. split; [exact Fnch|]. split; [exact Fe|]. split; [exact Fif|].
  split; [rewrite Fso; exact S1|]. split; [exact Fsd|]. split; [rewrite Fop; exact O1|].
  split; [rewrite Fmis; exact M1|]. split; [rewrite Fopd; exact P1|]. split; [rewrite Fcl; exact C1|].
  split; [rewrite Kn, Z2Nat.id by lia; exact Fnx|].
  split; [rewrite Fsn, Fsn1; reflexivity|].
  rewrite Fnsn, Fsn, Fsn1. reflexivity.
Qed.

Lemma nts_g_close : forall cx bs2 bs, nt_base SK B cx -> nts_g2f cx bs2 ->
  nk_socket_errno (n_kbs cx) = 0 -> nk_send_errno (n_kbs cx) <> 0 ->
  Z.of_nat (length bs) = NK_SIZE -> nlk_wf bs -> nts_gsame NK_OPEN (NK_MISUSE + 4) bs2 bs ->
  nk_open bs = 0 -> nk_opened bs = nk_opened bs2 -> nk_closed bs = nk_closed bs2 + 1 -> nk_misuse bs = nk_misuse bs2 ->
  nt_gnl_fin cx bs.
Proof.
  intros cx bs2 bs HB (HL2 & WF2 & Hs2 & S2 & D2 & E2 & O2 & P2 & C2 & M2 & N2) Hse Hsd HL WF Hs Fop Fopd Fcl Fmis.
  destruct (nts_kbs cx HB) as (WF0 & HL0 & _).
  pose proof WF0 as (_ & (Wn0 & _) & _).
  assert (Hs3 : nts_gsame NK_SOCKET_ERRNO (NK_N_SENT + 4) (n_kbs cx) bs).
  { apply (nts_gsame_trans NK_SOCKET_ERRNO (NK_N_SENT + 4) NK_OPEN (NK_MISUSE + 4) _ bs2 _ Hs2 Hs);
      unfold NK_SOCKET_ERRNO, NK_OPEN, NK_MISUSE, NK_N_SENT; lia. }
  destruct (nts_gsame_fields _ _ _ _ WF0 HL0 Hs3 ltac:(lia) ltac:(lia)) as (Fch & Fnch & Fnx & Fe & Fif & _).
  destruct (nts_gsame_sent _ _ _ _ WF2 HL2 Hs ltac:(unfold NK_MISUSE, NK_SENT; lia)) as (Fsn & _).
  assert (Fso : nk_socket_errno bs = 0).
  { unfold nk_socket_errno. rewrite (nts_gsame_u32 _ _ _ _ NK_SOCKET_ERRNO Hs HL2); [exact S2 | | | ];
      unfold NK_SOCKET_ERRNO, NK_OPEN, NK_SIZE; lia. }
  assert (Fsd : nk_send_errno bs = 0).
  { unfold nk_send_errno. rewrite (nts_gsame_u32 _ _ _ _ NK_SEND_ERRNO Hs HL2); [exact D2 | | | ];
      unfold NK_SEND_ERRNO, NK_OPEN, NK_SIZE; lia. }
  destruct (nt_talk_send (n_K0 cx) ltac:(rewrite (proj1 (nts_K0 cx)); exact Hse)
    ltac:(rewrite (proj1 (proj2 (nts_K0 cx))); exact Hsd)) as (_ & _ & Ta & To).
  destruct (nts_K0 cx) as (Ks & Kd & Kc & Kn & Ke).
  split; [exact WF|]. split; [exact Fch|]. split; [exact Fe|]. split; [exact Fif|]. split; [exact Fso|].
  split; [rewrite Ta; exact Fsd|].
  split; [rewrite Ta; cbn [k_next]; rewrite Kn, Z2Nat.id by lia; exact Fnx|].
  split; [rewrite To, Fsn; exact N2|].
  split; [exact (nt_nk_sent_len bs WF)|].
  split; [exact Fop|]. split; [rewrite Fmis; exact M2|]. split; [lia|].
  split; [intros H; contradiction | intros _; lia].
Qed.

(* the foot of nts_stat without the frame's shadow, which meta_fill_00 rewrites *)
Definition nts_foot0 (cx : ntcx) (fp a : Z) : Prop :=
  (spZ (n_regs cx) - 104 <= a < spZ (n_regs cx)) \/ (n_sp1 cx + 48 <= a < n_sp1 cx + NT_SPILL) \/
  (nF cx fp <= a < nF cx fp + fs_frame_bytes NT_CID).

Lemma nts_stat0_keep : forall cx fp (W W' : world SEGS) ms ms',
  (forall a, nts_foot0 cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  nt_saved cx W ms /\ nt_header cx fp W ms /\ nt_slots0 cx fp W ms ->
  nt_saved cx W' ms' /\ nt_header cx fp W' ms' /\ nt_slots0 cx fp W' ms'.
Proof.
  intros cx fp W W' ms ms' H (Hsv & Hhd & Hsl).
  assert (FB : fs_frame_bytes NT_CID = 32768) by reflexivity.
  unfold nts_foot0 in H. rewrite FB in H. unfold NT_SPILL in H.
  split; [|split].
  - destruct Hsv as (Hra & Hs). split.
    + apply (nts_at_keep W W' ms ms'); [|exact Hra]. intros i Hi. apply H. left. lia.
    + intros j Hj. apply (nts_at_keep W W' ms ms'); [|exact (Hs j Hj)]. intros i Hi. apply H. left. lia.
  - destruct Hhd as (H1 & H2 & H3 & H4). rewrite FB in H4.
    split; [|split; [|split]];
      (apply (nts_at_keep W W' ms ms'); [intros i Hi; apply H; right; right; lia | assumption]).
  - destruct Hsl as (H1 & H2 & H3).
    split; [|split];
      (apply (nts_at_keep W W' ms ms');
       [intros i Hi; apply H; right; left; unfold NS_KIND, NS_KINDN, NS_F; lia | assumption]).
Qed.

Lemma nts_anlk_keep : forall (m m' : word -> option byte) bs,
  anlk_at SEGS m LA_G_NL bs ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> mbyte SEGS m' a = mbyte SEGS m a) ->
  anlk_at SEGS m' LA_G_NL bs.
Proof.
  intros m m' bs [[(H0 & H1 & Hb) Hw] HL] Hm. split; [|exact HL]. split.
  - split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (Hb i Hi). apply Hm. unfold NK_SIZE in *. lia.
  - intros i Hi. assert (HW : forall m0, writable_at SEGS m0 (LA_G_NL + i))
      by (intros m0; rewrite HSEGS; apply LA_G_NL_writable; unfold NK_SIZE in *; lia).
    apply HW.
Qed.

Lemma nts_present_grows : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Hg (Hh & b & Hb). split; [exact Hh|].
  specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg. rewrite Hh in Hg.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
  exfalso. apply Hg; [rewrite Hb; discriminate | reflexivity].
Qed.

Lemma nts_aview_frame : forall E rs (m m' : word -> option byte) H a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs m m' H a Hf Ha Hn. unfold aview, mbyte, mrestrict.
  rewrite (Hf (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma nts_bt_neg : branch_taken BC_LT (w64 (-1)) (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nts_bt_nonneg : forall x, 0 <= x < 2 ^ 63 -> branch_taken BC_LT (w64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. unfold w64. rewrite YO0c.branch_lt, !unsigned_lit_small by lia.
  rewrite !YO0b.s64_small by lia. apply Z.ltb_ge. lia.
Qed.

Section w.
Variable POST : ntcx -> world SEGS -> config -> Prop.
Hypothesis NREC : nt_from SK B POST (nt_recv_inv B).
Hypothesis NTAIL : nt_from SK B POST (nt_tail_inv B).

(* ---- the socket failure arm, from +0x2d0 (___errno_location returned) to NT_tail ---- *)
Lemma nts_SF : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 bs,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_shape (AF_nl_talk + 0x2d0) ms3 ->
  nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ->
  getr (ms_regs ms3) 10 = w64 (as_errno B) ->
  nk_socket_errno (n_kbs cx) <> 0 ->
  au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (nk_socket_errno (n_kbs cx)) ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs -> nt_gnl_fin cx bs ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 bs HB HJ HFR Hsh HBD R10 Hse Herr HNK HFIN.
  pose proof (nts_pre cx HB) as (HWF & _).
  pose proof HWF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Wse & _).
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  pose proof NL_TALK_AK_val as HAKv. pose proof alloc_ceiling_val as Hac.
  assert (HAR3 : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3)
    by (destruct HJ as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
  assert (Hsp3 : spZ (ms_regs ms3) = n_sp1 cx).
  { destruct HBD as ((R2 & _) & _). unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
  destruct (nts_errno_pre cx ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) 0 HB HAR3 Hsp3 ltac:(lia))
    as (He1 & He2 & He3 & _).
  pose proof (AF0m.ts_errno B TB) as Hte. unfold AF0m.TFIB_ERRNO in Hte.
  set (e := nk_socket_errno (n_kbs cx)) in *.
  assert (He : 0 < e < 2 ^ 31) by lia.
  pose proof HBD as (Hrg & R20 & R23 & R25 & Hst & HD).
  pose proof Hrg as (_ & _ & _ & _ & R21 & _).
  remember (Eimg (Ereg (ms_regs ms3) [w64 0; w64 e])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10 = Z_to_bv 64 (as_errno B)) by (subst E; rewrite (nts_ew_reg _ _ 10 10%bv eq_refl); exact R10).
  assert (E21 : ew E 21 = Z_to_bv 64 nts_SB) by (subst E; rewrite (nts_ew_reg _ _ 21 21%bv eq_refl); exact R21).
  assert (E33 : ew E 33 = Z_to_bv 64 e) by (subst E; exact (nts_ew_ext _ _ 1 ltac:(unfold A_TEXT; lia))).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x2d0) sr_atoms [nts_ERR] None (mkFacts nts_fe [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | | |]; rewrite <- HEdef.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, nts_ERR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E10, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (as_errno B) 0 4 (SOff 33 0) e);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Herr.
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [|split; exact I]. cbn [nts_fe f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E10, E21, E33, !unsigned_lit_small by (unfold nts_SB; lia).
      unfold nts_SB. rewrite Hte.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity]. }
  assert (SHOK : sh_ok SEGS nts_Bx nts_SHE E (mrestrict (w_H W3) (ms_mem ms3))).
  { apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart, nts_Bx. cbn [she_m she_lo she_hi].
    rewrite (U_atom E 21 nts_SB E21) by (unfold nts_SB; lia). rewrite (U_atom E 10 (as_errno B) E10) by lia.
    split.
    - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of SEGS). exact He3.
    - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. unfold nts_SB. lia. }
  pose proof (paj_run_to_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  paj_run_to_tok RUNTO HS HJ SHOK nts_span (AF_nl_talk + 0x4f8); [nts_awr_ro |].
  pose proof (nts_frame_of_ro _ [nts_ERR] _ _ ltac:(intros r [<-|[]]; cbn; lia) HF) as HFm.
  clear HF HFr HG.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms) r = getr (ms_regs ms3) r)
    by nts_kreg HS HEdef.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as Q27.
  lazymatch type of Q27 with _ = sv_denot _ ?ev =>
    let ev' := eval vm_compute in ev in change ev with ev' in Q27 end.
  cbn [ms_regs restrict mkst] in Q27.
  lazymatch type of Q27 with _ = sv_denot ?E2 _ =>
    rewrite (nts_neg E2 33 e ltac:(cbn [ew ewset Nat.eqb]; exact E33) ltac:(lia)) in Q27 end.
  destruct (nt_talk_sock (n_K0 cx) Hse) as (Trc & Tat & _ & _).
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
    apply (NTAIL cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
  unfold nt_tail_inv.
  destruct (nts_rg_of cx fp ms3 ms Hregs Hrg R20 R23 R25) as (Hrg' & R20' & _ & _).
  destruct (nts_stat_keep cx fp W3 W3 ms3 ms 0xf8 ltac:(intros a _; rewrite HFm; reflexivity) Hst)
    as (Hsv' & Hhd' & _ & _).
  destruct HD as (HJB & HKP & HBS & HAB & HER).
  cbn [ms_mem ms_regs mkst].
  split; [repeat split; reflexivity|]. split; [exact Hrg'|]. split; [exact Hsv'|]. split; [exact Hhd'|].
  split; [exact R20'|].
  split; [rewrite Q27, Trc; reflexivity|].
  split.
  { destruct HJB as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9).
    repeat (split; [assumption|]).
    exact J9. }
  split; [rewrite HFm; exact (nts_kept_nE cx fp W3 _ HB HKP)|].
  split; [exists bs; split; [rewrite HFm; exact HNK | exact HFIN]|].
  rewrite HFm. apply nt_bufs_same_fin; [exact Tat | exact HBS].
Qed.

(* ---- the socket failure arm from +0x2cc: the call of ___errno_location, then nts_SF ---- *)
Lemma nts_SF0 : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 bs,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_shape (AF_nl_talk + 0x2cc) ms3 ->
  nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ->
  nk_socket_errno (n_kbs cx) <> 0 ->
  au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (nk_socket_errno (n_kbs cx)) ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs -> nt_gnl_fin cx bs ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 bs HB HJ HFR Hsh HBD Hse Herr HNK HFIN.
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _).
  pose proof HBD as (Hrg & _).
  pose proof Hrg as (R2 & _ & _ & _ & _ & _ & _ & R4).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x2cc) sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | apply Forall_nil | | ].
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS nts_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof (paj_run_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  paj_run_tok RUN HS HJ SHOK nts_span; [nts_awr_ro |].
  pose proof (nts_frame_of_nil _ _ _ HF) as HFm. clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nts_kreg HS HEdef.
  prreg HS (1%bv : bv 5) R1.
  apply (nts_call_errno cx fp k2 ly3 S3 W3 (ms_mem ms1) _ (ms_regs ms1) (AF_nl_talk + 0x2d0) (POST cx) HB HJ);
    [ rewrite R1; reflexivity | unfold AF_nl_talk; lia | reflexivity
    | rewrite (Hregs 2%bv ltac:(cbn; tauto)); exact R2 | rewrite (Hregs 4%bv ltac:(cbn; tauto)); exact R4 |].
  intros rg2 md4 Hsm HJ4 H10 Hr.
  assert (HP2 : aregs_preserved (ms_regs ms1) rg2) by (intros r Hr'; apply Hr; unfold acallee_saved in Hr'; lia).
  pose proof (same_but_materialized_fs _ _ Hsm) as (Hfd4 & Hfs4).
  apply (nts_SF cx fp k2 ly3 S3 W3 (mkst rg2 (Z_to_bv 64 (BASE + (AF_nl_talk + 0x2d0))) (ms_mem ms1) (seg_rom SEGS))
    md4 bs HB HJ4 HFR).
  - repeat split; reflexivity.
  - apply (nts_body_move cx fp k2 ly3 S3 W3 ms1 (with_vm_backing (m_vm_lazy md3) mat md3) nts_EW 0xf8 _ md4).
    + apply (nts_body_move cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ms1 _ HBD Hregs HFm);
        [exact (proj1 (nts_wvb md3 mat)) | exact (proj2 (nts_wvb md3 mat))].
    + exact (nts_body_call_regs ms1 (mkst rg2 (Z_to_bv 64 (BASE + (AF_nl_talk + 0x2d0))) (ms_mem ms1) (seg_rom SEGS)) HP2).
    + reflexivity.
    + exact Hfd4.
    + exact Hfs4.
  - exact H10.
  - exact Hse.
  - cbn [ms_mem mkst]. rewrite HFm. exact Herr.
  - cbn [ms_mem mkst]. rewrite HFm. exact HNK.
  - exact HFIN.
Qed.

(* ---- the send failure arm, from +0x30c (fuzz_close returned) to NT_tail ---- *)
Lemma nts_EF2 : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 bs,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_shape (AF_nl_talk + 0x30c) ms3 ->
  nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ->
  getr (ms_regs ms3) 19 = w64 (nk_send_errno (n_kbs cx)) ->
  nk_socket_errno (n_kbs cx) = 0 -> nk_send_errno (n_kbs cx) <> 0 ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs -> nt_gnl_fin cx bs ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 bs HB HJ HFR Hsh HBD R19 Hso Hsd HNK HFIN.
  destruct (nts_kbs cx HB) as (HWF & _).
  pose proof HWF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wsd & _).
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _).
  set (e := nk_send_errno (n_kbs cx)) in *.
  assert (He : 0 < e < 2 ^ 31) by lia.
  pose proof HBD as (Hrg & R20 & R23 & R25 & Hst & HD).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E19 : ew E 19 = Z_to_bv 64 e) by (subst E; rewrite (nts_ew_reg _ _ 19 19%bv eq_refl); exact R19).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x30c) sr_atoms [] None
                 (mkFacts [(19%nat, mkAF 1 (2 ^ 31 - 1) 0)] [] [])) (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | apply Forall_nil | |]; rewrite <- HEdef.
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E19, unsigned_lit_small by lia.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity]. }
  assert (SHOK : sh_ok SEGS nts_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof (paj_run_to_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  paj_run_to_tok RUNTO HS HJ SHOK nts_span (AF_nl_talk + 0x4f8); [nts_awr_ro |].
  pose proof (nts_frame_of_nil _ _ _ HF) as HFm. clear HF HFr HG.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms) r = getr (ms_regs ms3) r)
    by nts_kreg HS HEdef.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as Q27.
  lazymatch type of Q27 with _ = sv_denot _ ?ev =>
    let ev' := eval vm_compute in ev in change ev with ev' in Q27 end.
  cbn [ms_regs restrict mkst] in Q27.
  lazymatch type of Q27 with _ = sv_denot ?E2 _ =>
    rewrite (nts_neg E2 19 e ltac:(cbn [ew ewset Nat.eqb]; exact E19) ltac:(lia)) in Q27 end.
  destruct (nt_talk_send (n_K0 cx) ltac:(rewrite (proj1 (nts_K0 cx)); exact Hso)
    ltac:(rewrite (proj1 (proj2 (nts_K0 cx))); exact Hsd)) as (Trc & Tat & _ & _).
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
    apply (NTAIL cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
  unfold nt_tail_inv.
  destruct (nts_rg_of cx fp ms3 ms Hregs Hrg R20 R23 R25) as (Hrg' & R20' & _ & _).
  destruct (nts_stat_keep cx fp W3 W3 ms3 ms 0xf8 ltac:(intros a _; rewrite HFm; reflexivity) Hst)
    as (Hsv' & Hhd' & _ & _).
  destruct HD as (HJB & HKP & HBS & HAB & HER).
  cbn [ms_mem ms_regs mkst].
  split; [repeat split; reflexivity|]. split; [exact Hrg'|]. split; [exact Hsv'|]. split; [exact Hhd'|].
  split; [exact R20'|].
  split; [rewrite Q27, Trc; reflexivity|].
  split.
  { destruct HJB as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9).
    repeat (split; [assumption|]). exact J9. }
  split; [rewrite HFm; exact (nts_kept_nE cx fp W3 _ HB HKP)|].
  split; [exists bs; split; [rewrite HFm; exact HNK | exact HFIN]|].
  rewrite HFm. apply nt_bufs_same_fin; [exact Tat | exact HBS].
Qed.

(* ---- the send failure arm from +0x2f0 (___errno_location returned): errno into s3, then fuzz_close ---- *)
Lemma nts_EF1 : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 bs,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_shape (AF_nl_talk + 0x2f0) ms3 ->
  nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ->
  getr (ms_regs ms3) 10 = w64 (as_errno B) -> getr (ms_regs ms3) 22 = w64 NL_FD ->
  nk_socket_errno (n_kbs cx) = 0 -> nk_send_errno (n_kbs cx) <> 0 ->
  au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (nk_send_errno (n_kbs cx)) ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs -> nts_g2f cx bs ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 bs HB HJ HFR Hsh HBD R10 R22 Hso Hsd Herr HNK HG2.
  destruct (nts_kbs cx HB) as (HWF & HL0 & HOP & HOC & HCC).
  pose proof HWF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wsd & _).
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  pose proof NL_TALK_AK_val as HAKv. pose proof alloc_ceiling_val as Hac.
  assert (HAR3 : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3)
    by (destruct HJ as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
  assert (Hsp3 : spZ (ms_regs ms3) = n_sp1 cx).
  { destruct HBD as ((R2 & _) & _). unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
  destruct (nts_errno_pre cx ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) 0 HB HAR3 Hsp3 ltac:(lia))
    as (He1 & He2 & He3 & _).
  pose proof (AF0m.ts_errno B TB) as Hte. unfold AF0m.TFIB_ERRNO in Hte.
  set (e := nk_send_errno (n_kbs cx)) in *.
  assert (He : 0 < e < 2 ^ 31) by lia.
  pose proof HBD as (Hrg & R20 & R23 & R25 & Hst & HD).
  pose proof Hrg as (R2 & _ & _ & _ & R21 & _ & R3 & R4).
  remember (Eimg (Ereg (ms_regs ms3) [w64 0; w64 e])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10 = Z_to_bv 64 (as_errno B)) by (subst E; rewrite (nts_ew_reg _ _ 10 10%bv eq_refl); exact R10).
  assert (E21 : ew E 21 = Z_to_bv 64 nts_SB) by (subst E; rewrite (nts_ew_reg _ _ 21 21%bv eq_refl); exact R21).
  assert (E33 : ew E 33 = Z_to_bv 64 e) by (subst E; exact (nts_ew_ext _ _ 1 ltac:(unfold A_TEXT; lia))).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x2f0) sr_atoms [nts_ERR] None (mkFacts nts_fe [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | | |]; rewrite <- HEdef.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, nts_ERR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E10, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (as_errno B) 0 4 (SOff 33 0) e);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Herr.
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [|split; exact I]. cbn [nts_fe f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E10, E21, E33, !unsigned_lit_small by (unfold nts_SB; lia).
      unfold nts_SB. rewrite Hte.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity]. }
  assert (SHOK : sh_ok SEGS nts_Bx nts_SHE E (mrestrict (w_H W3) (ms_mem ms3))).
  { apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart, nts_Bx. cbn [she_m she_lo she_hi].
    rewrite (U_atom E 21 nts_SB E21) by (unfold nts_SB; lia). rewrite (U_atom E 10 (as_errno B) E10) by lia.
    split.
    - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of SEGS). exact He3.
    - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. unfold nts_SB. lia. }
  pose proof (paj_run_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  paj_run_tok RUN HS HJ SHOK nts_span; [nts_awr_ro |].
  pose proof (nts_frame_of_ro _ [nts_ERR] _ _ ltac:(intros r [<-|[]]; cbn; lia) HF) as HFm.
  clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nts_kreg HS HEdef.
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
  rewrite E33 in Q19. rewrite HEdef, (nts_ew_reg _ _ 22 22%bv eq_refl), R22 in Q10.
  destruct HD as (HJB & HKP & HBS & HAB & HER).
  pose proof HKP as (_ & HRO & _).
  pose proof HG2 as (HL2 & WF2 & Hs2 & S2 & D2 & E2 & O2 & P2 & C2 & M2 & N2).
  assert (HBD1 : nts_body cx fp k2 ly3 S3 W3 ms1 (with_vm_backing (m_vm_lazy md3) mat md3) nts_EW 0xf8).
  { apply (nts_body_move cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ms1 _ HBD Hregs HFm);
      [exact (proj1 (nts_wvb md3 mat)) | exact (proj2 (nts_wvb md3 mat))]. }
  assert (A0 : aarg (ms_regs ms1) 0 = NL_FD).
  { unfold aarg, argZ. assert (X : getr (ms_regs ms1) (Z_to_bv 5 (10 + 0)) = w64 NL_FD) by exact Q10.
    rewrite X. unfold w64, NL_FD. apply unsigned_lit_small. lia. }
  rewrite (proj2 (proj2 (proj2 nts_vals))).
  apply (nts_call FUZZ_CLOSE_A FUZZ_CLOSE_AK _ _ _ FCL cx fp k2 ly3 S3 W3
    (ms_mem ms1) _ md3 (ms_regs ms1) (AF_nl_talk + 0x30c) (POST cx) HB HJ HJB ltac:(rewrite HFm; exact HRO));
    [ rewrite R1; reflexivity | unfold AF_nl_talk; lia | reflexivity
    | rewrite (Hregs 2%bv ltac:(cbn; tauto)); exact R2 | rewrite (Hregs 3%bv ltac:(cbn; tauto)); exact R3
    | rewrite (Hregs 4%bv ltac:(cbn; tauto)); exact R4 | unfold FUZZ_CLOSE_AK; lia
    | intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr; unfold NK_OPEN, NK_MISUSE, NK_N_SENT in *; lia
    | exists bs; split; [rewrite HFm; exact HNK|]; split; [exact WF2 | rewrite C2; lia] |].
  intros ly4 S4 W4 rg2 mem4 md4 HJ4 HP Hfr4 Hfd4 Hfs4 HK4 Hset4 Hperm4 HPost.
  destruct (HPost bs ltac:(rewrite HFm; exact HNK)) as (bs3 & HNK3 & WF3 & _ & Fop & Fopd & Fcl & Fmis).
  rewrite A0, O2 in Fmis. cbn in Fmis.
  assert (Hs3 : nts_gsame NK_OPEN (NK_MISUSE + 4) bs bs3).
  { apply (nts_gnl_kept cx ly3 S3 W3 (ms_mem ms1) W4 mem4 _ _ _ NK_OPEN (NK_MISUSE + 4) bs bs3 HB HK4);
      [intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr; lia | rewrite HFm; exact HNK | exact HNK3]. }
  apply (nts_EF2 cx fp k2 ly4 S4 W4 (mkst rg2 (Z_to_bv 64 (BASE + (AF_nl_talk + 0x30c))) mem4 (seg_rom SEGS)) md4 bs3
    HB HJ4 ltac:(rewrite Hfr4; exact HFR)).
  - repeat split; reflexivity.
  - apply (nts_body_call cx fp k2 ly3 S3 W3 ms1 _ 0xf8 FUZZ_CLOSE_AK
      (fun a => inFP (fuzz_close_awr (ms_regs ms1) (rdW W3 (ms_mem ms1))) a) ly4 S4 W4 _ md4 HB HJ HBD1
      ltac:(unfold FUZZ_CLOSE_AK; lia)); [| exact HJ4 | exact HP | exact Hfr4 | exact Hfd4 | exact Hfs4 | exact HK4
      | exact Hset4 | exact Hperm4].
    intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr. unfold nts_EW, NK_OPEN, NK_SOCKET_ERRNO, NK_MISUSE, NK_N_SENT in *. lia.
  - cbn [ms_regs mkst]. exact (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) Q19).
  - exact Hso.
  - exact Hsd.
  - exact HNK3.
  - exact (nts_g_close cx bs bs3 HB HG2 Hso Hsd (nts_anlk_len _ _ _ HNK3) WF3 Hs3 Fop Fopd Fcl Fmis).
Qed.

(* ---- the send failure arm from +0x2ec: the call of ___errno_location, then nts_EF1 ---- *)
Lemma nts_EF0 : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 bs,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_shape (AF_nl_talk + 0x2ec) ms3 ->
  nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ->
  getr (ms_regs ms3) 22 = w64 NL_FD ->
  nk_socket_errno (n_kbs cx) = 0 -> nk_send_errno (n_kbs cx) <> 0 ->
  au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (nk_send_errno (n_kbs cx)) ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs -> nts_g2f cx bs ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 bs HB HJ HFR Hsh HBD R22 Hso Hsd Herr HNK HG2.
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _).
  pose proof HBD as (Hrg & _).
  pose proof Hrg as (R2 & _ & _ & _ & _ & _ & _ & R4).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x2ec) sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | apply Forall_nil | | ].
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS nts_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof (paj_run_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  paj_run_tok RUN HS HJ SHOK nts_span; [nts_awr_ro |].
  pose proof (nts_frame_of_nil _ _ _ HF) as HFm. clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nts_kreg HS HEdef.
  assert (R22' : getr (ms_regs ms1) 22 = getr (ms_regs ms3) 22)
    by (prreg HS (22%bv : bv 5) Q; rewrite Q, HEdef; apply nts_ew_reg; reflexivity).
  prreg HS (1%bv : bv 5) R1.
  apply (nts_call_errno cx fp k2 ly3 S3 W3 (ms_mem ms1) _ (ms_regs ms1) (AF_nl_talk + 0x2f0) (POST cx) HB HJ);
    [ rewrite R1; reflexivity | unfold AF_nl_talk; lia | reflexivity
    | rewrite (Hregs 2%bv ltac:(cbn; tauto)); exact R2 | rewrite (Hregs 4%bv ltac:(cbn; tauto)); exact R4 |].
  intros rg2 md4 Hsm HJ4 H10 Hr.
  assert (HP2 : aregs_preserved (ms_regs ms1) rg2) by (intros r Hr'; apply Hr; unfold acallee_saved in Hr'; lia).
  pose proof (same_but_materialized_fs _ _ Hsm) as (Hfd4 & Hfs4).
  apply (nts_EF1 cx fp k2 ly3 S3 W3 (mkst rg2 (Z_to_bv 64 (BASE + (AF_nl_talk + 0x2f0))) (ms_mem ms1) (seg_rom SEGS))
    md4 bs HB HJ4 HFR).
  - repeat split; reflexivity.
  - apply (nts_body_move cx fp k2 ly3 S3 W3 ms1 (with_vm_backing (m_vm_lazy md3) mat md3) nts_EW 0xf8 _ md4).
    + apply (nts_body_move cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ms1 _ HBD Hregs HFm);
        [exact (proj1 (nts_wvb md3 mat)) | exact (proj2 (nts_wvb md3 mat))].
    + exact (nts_body_call_regs ms1 (mkst rg2 (Z_to_bv 64 (BASE + (AF_nl_talk + 0x2f0))) (ms_mem ms1) (seg_rom SEGS)) HP2).
    + reflexivity.
    + exact Hfd4.
    + exact Hfs4.
  - exact H10.
  - cbn [ms_regs mkst]. rewrite <- R22. rewrite <- R22'. exact (HP2 22 ltac:(unfold acallee_saved; lia)).
  - exact Hso.
  - exact Hsd.
  - cbn [ms_mem mkst]. rewrite HFm. exact Herr.
  - cbn [ms_mem mkst]. rewrite HFm. exact HNK.
  - exact HG2.
Qed.

(* the spill slots [s1 + 24, s1 + 40) of +0x1d0 / +0x1e0, written through s1 (atom 9) *)
Definition nts_SPILL : YP09.region := YP09.mkRegion (Some 9%nat) 0 88 24 40 [].
Definition nts_f0 : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, mkAF nts_SB nts_SB 0)].

(* ---- the receive set-up, from +0x1d0 (fuzz_send succeeded): the two spills, s10 := the buffer, and
   meta_fill_00 of the buffer's 2048 shadow bytes, to NT_mf0_ra ---- *)
Lemma nts_R : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 bs,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_shape (AF_nl_talk + 0x1d0) ms3 ->
  nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ->
  getr (ms_regs ms3) 19 = w64 (nSH cx fp + 4) -> getr (ms_regs ms3) 22 = w64 NL_FD ->
  nk_socket_errno (n_kbs cx) = 0 -> nk_send_errno (n_kbs cx) = 0 ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs -> nt_gnl_open cx bs true (Z.of_nat (k_next (n_K0 cx))) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 bs HB HJ HFR Hsh HBD R19 R22 Hso Hsd HNK HGO.
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _ & _ & _ & Hgp & Htp & _).
  pose proof pa_B_ok as (HB0 & HB1 & HB2).
  pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
  pose proof HJ as HJ3.
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  pose proof NL_TALK_AK_val as HAKv. pose proof alloc_ceiling_val as Hac.
  pose proof HBD as (Hrg & R20 & R23 & R25 & Hst & HD).
  pose proof HD as (HJB & _).
  destruct (nts_frame cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ HJB)
    as (Hin9 & Efa & F4096 & Fceil & F64 & ESH & EFB & Fapp & HAR3).
  pose proof Hrg as (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4).
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E2 : ew E 2 = Z_to_bv 64 (n_sp1 cx)) by (subst E; rewrite (nts_ew_reg _ _ 2 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 (n_sp1 cx)) by (subst E; rewrite (nts_ew_reg _ _ 9 9%bv eq_refl); exact R9).
  assert (E21 : ew E 21 = Z_to_bv 64 nts_SB) by (subst E; rewrite (nts_ew_reg _ _ 21 21%bv eq_refl); exact R21).
  assert (E18 : ew E 18 = Z_to_bv 64 (nF cx fp)) by (subst E; rewrite (nts_ew_reg _ _ 18 18%bv eq_refl); exact R18).
  assert (E19 : ew E 19 = Z_to_bv 64 (nSH cx fp + 4)) by (subst E; rewrite (nts_ew_reg _ _ 19 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 (nF cx fp)) by (subst E; rewrite (nts_ew_reg _ _ 20 20%bv eq_refl); exact R20).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x1d0) sr_atoms [nts_SPILL] None (mkFacts nts_f0 [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | | |]; rewrite <- HEdef.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, nts_SPILL.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [|split; exact I]. cbn [nts_f0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E21, !unsigned_lit_small by (unfold nts_SB; lia).
      unfold nts_SB.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity]. }
  assert (SHOK : sh_ok SEGS nts_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof (paj_run_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  paj_run_tok RUN HS HJ SHOK nts_span;
    [ apply awr_ok_x_cons; [| apply awr_ok_x_nil];
      intros a Ha; unfold nts_SPILL in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite E9, unsigned_lit_small in Ha by lia;
      left; split; [unfold awr_byte; left; lia | lia] |].
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
  (* the two spills, read off the region's chunks *)
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
  pose proof (region_ok_chunk SEGS _ _ _ (YP09.mkChunk 24 (CVal 8 (SOff 19 0))) HR0 ltac:(left; reflexivity)) as HC24.
  pose proof (region_ok_chunk SEGS _ _ _ (YP09.mkChunk 32 (CVal 8 (SOff 20 0))) HR0 ltac:(right; left; reflexivity))
    as HC32.
  pose proof (val_of_chunk_any SEGS _ _ _ _ _ _ HC24 ltac:(lia)) as V24.
  pose proof (val_of_chunk_any SEGS _ _ _ _ _ _ HC32 ltac:(lia)) as V32.
  clear HR0 HC24 HC32.
  cbn [base_val YP09.r_base ms_mem restrict mkst] in V24, V32.
  change (N.to_nat 8) with 8%nat in V24, V32. change (8 * Z.of_N 8) with 64 in V24, V32.
  rewrite E9, unsigned_lit_small in V24, V32 by lia.
  assert (D19 : sv_denot E (SOff 19 0) = Z_to_bv 64 (nSH cx fp + 4))
    by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E19).
  assert (D20 : sv_denot E (SOff 20 0) = Z_to_bv 64 (nF cx fp))
    by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E20).
  rewrite D19, unsigned_lit_small, Z.mod_small in V24 by (rewrite ESH; unfold shadow_addr, SHADOW_OFF; lia).
  rewrite D20, unsigned_lit_small, Z.mod_small in V32 by lia.
  assert (S24 : nt_at W3 ms1 (n_sp1 cx + NS_SH4) (nSH cx fp + 4)).
  { unfold nt_at, NS_SH4. apply (rdword_of_val_mem SEGS); [exact V24 | rewrite ESH; unfold shadow_addr, SHADOW_OFF; lia]. }
  assert (S32 : nt_at W3 ms1 (n_sp1 cx + NS_FK) (nF cx fp)).
  { unfold nt_at, NS_FK. apply (rdword_of_val_mem SEGS); [exact V32 | lia]. }
  clear V24 V32 D19 D20.
  (* the bytes the run left alone *)
  assert (Hspill : forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx + 24 <= a < n_sp1 cx + 40) ->
            aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hn. apply (nts_aview_frame _ _ _ _ _ _ HF Ha).
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
    unfold nts_SPILL in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    rewrite E9, unsigned_lit_small in Hr by lia. lia. }
  pose proof HG as HGm. clear HF HFr HG.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nts_kreg HS HEdef.
  assert (Hx : forall r : bv 5, In r [19;22]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r) by nts_kreg HS HEdef.
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (26%bv : bv 5) Q26.
  rewrite E19 in Q10. rewrite E18, unsigned_lit_small in Q26 by lia.
  assert (Usp1 : spZ (ms_regs ms1) = n_sp1 cx).
  { unfold spZ. rewrite (Hregs 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  eapply SRr_bind.
  { apply (aj_gx_set_shadow_at SK SEGS B LAWS pa_segs_low (pa_sigma LS___asan_set_shadow_00) 0 MF00 (n_G cx) (n_XO cx)
      (n_OUT cx) W3 (ms_regs ms1) (ms_mem ms1) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx)
      (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 _ k2 NT_CID fp (nSH cx fp + 4) 2048
      (Z_to_bv 64 (BASE + (AF_nl_talk + 0x1ec))) HGX HJ (or_introl eq_refl)).
    - exact Q10.
    - exact Q11.
    - lia.
    - rewrite Efa, <- ESH. lia.
    - rewrite Efa, <- ESH, EFB. change (32768 / 8) with 4096. lia.
    - rewrite Usp1. exact Gs16.
    - rewrite Usp1. unfold ESTACK. lia.
    - rewrite Usp1. lia.
    - rewrite (Hregs 3%bv ltac:(cbn; tauto)), R3. exact Hgp.
    - rewrite (Hregs 4%bv ltac:(cbn; tauto)), R4. exact Htp.
    - rewrite R1. reflexivity.
    - apply ret_ok_codeptr_v; unfold AF_nl_talk; lia. }
  cbv beta. intros W4 c4 _ (-> & rg2 & mem2 & md2 & -> & HJ2 & HP2 & Hv0 & Hkeep & Hpr & Hsm).
  pose proof (same_but_materialized_fs _ _ Hsm) as (Hfd2 & Hfs2).
  set (MS := mkst rg2 (Z_to_bv 64 (BASE + (AF_nl_talk + 0x1ec))) mem2 (seg_rom SEGS)).
  (* what the run and meta_fill_00 wrote: the two spills and the 2048 shadow bytes *)
  assert (Hall : forall a, 0 <= a < 2 ^ 64 ->
            ~ ((n_sp1 cx + 24 <= a < n_sp1 cx + 40) \/ (nSH cx fp + 4 <= a < nSH cx fp + 4 + 2048)) ->
            aview SEGS (w_H W3) (ms_mem MS) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hn. unfold MS; cbn [ms_mem mkst]. rewrite (Hkeep a Ha) by tauto. apply Hspill; [exact Ha | tauto]. }
  assert (Hsh_app : forall a, nF cx fp <= a < nF cx fp + 32768 -> ~ (nSH cx fp + 4 <= a < nSH cx fp + 4 + 2048)).
  { intros a Ha Hs. rewrite ESH in Hs. unfold in_app in Fapp. rewrite EFB in Fapp. unfold shadow_addr in Hs.
    unfold ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
  assert (HD2 : nts_dyn cx fp k2 ly3 S3 W3 MS md2 nts_EW).
  { apply (nts_dyn_step cx fp k2 ly3 S3 W3 ms3 md3 nts_EW MS md2
      (fun a => (n_sp1 cx + 24 <= a < n_sp1 cx + 40) \/ (nSH cx fp + 4 <= a < nSH cx fp + 4 + 2048)) HB HJ3 HJ2 HD).
    - rewrite Hfd2. exact (proj1 (nts_wvb md3 mat)).
    - rewrite Hfs2. exact (proj2 (nts_wvb md3 mat)).
    - exact Hall.
    - intros a _ Hp. unfold MS; cbn [ms_mem mkst]. apply Hpr. exact (nts_present_grows _ _ _ _ HGm Hp).
    - intros a [Ha | Ha]; [left; lia | right; rewrite EFB; change (32768 / 8) with 4096; lia]. }
  destruct HD2 as (HJB2 & HKP2 & HBS2 & HAB2 & _).
  destruct (nts_rg_of cx fp ms3 ms1 Hregs Hrg R20 R23 R25) as (Hrg1 & R20a & R23a & R25a).
  destruct (nts_rg_of cx fp ms1 MS (nts_body_call_regs ms1 MS HP2) Hrg1 R20a R23a R25a) as (Hrg' & R20' & R23' & R25').
  destruct Hst as (Hsv & Hhd & Hsl & Hsh1 & Hsh2 & Hsh3).
  assert (Hst0 : nt_saved cx W3 MS /\ nt_header cx fp W3 MS /\ nt_slots0 cx fp W3 MS).
  { apply (nts_stat0_keep cx fp W3 W3 ms3 MS); [|exact (conj Hsv (conj Hhd Hsl))].
    intros a Ha. unfold nts_foot0 in Ha. rewrite EFB in Ha. unfold NT_SPILL in Ha.
    apply Hall; [unfold in_app in Fapp; rewrite EFB in Fapp; unfold ASAN_CEIL in *; lia|].
    intros [Hs | Hs]; [lia|].
    destruct Ha as [Ha | [Ha | Ha]]; [| | exact (Hsh_app a Ha Hs)];
      rewrite ESH in Hs; unfold shadow_addr, SHADOW_OFF in Hs; lia. }
  destruct Hst0 as (Hsv' & Hhd' & Hsl').
  assert (Hsp_keep : forall a, n_sp1 cx + 24 <= a < n_sp1 cx + 40 -> forall i, 0 <= i < 8 -> a + i < n_sp1 cx + 40 ->
            aview SEGS (w_H W3) (ms_mem MS) (a + i) = aview SEGS (w_H W3) (ms_mem ms1) (a + i)).
  { intros a Ha i Hi Hai. unfold MS; cbn [ms_mem mkst]. apply Hkeep; [lia|].
    rewrite ESH. unfold shadow_addr, SHADOW_OFF. lia. }
  pose proof (nts_K0 cx) as (Ks & Kd & _).
  pose proof (nt_talk_loop (n_K0 cx) ltac:(rewrite Ks; exact Hso) ltac:(rewrite Kd; exact Hsd)) as TLp.
  cbv zeta in TLp. destruct TLp as (_ & _ & _ & To).
  apply (NREC cx fp k2 ly3 S3 W3 MS md2 HB HJ2 HFR).
  unfold nt_recv_inv.
  split; [repeat split; reflexivity|].
  split; [exact Hrg'|]. split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hsl'|].
  split.
  { apply (nts_at_keep W3 W3 ms1 MS); [|exact S24]. intros i Hi.
    apply (Hsp_keep (n_sp1 cx + NS_SH4)); unfold NS_SH4; lia. }
  split.
  { apply (nts_at_keep W3 W3 ms1 MS); [|exact S32]. intros i Hi.
    apply (Hsp_keep (n_sp1 cx + NS_FK)); unfold NS_FK; lia. }
  split; [exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) (eq_trans (Hx 19%bv ltac:(cbn; tauto)) R19))|].
  split; [exact R20'|].
  split; [exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) (eq_trans (Hx 22%bv ltac:(cbn; tauto)) R22))|].
  split; [exact R23'|]. split; [exact R25'|].
  split.
  { exact (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) Q26). }
  split.
  { split; [|split]; intros i Hi.
    - rewrite Hall; [exact (Hsh1 i Hi) | rewrite ESH; unfold shadow_addr, SHADOW_OFF; lia |].
      intros [Hs | Hs]; [rewrite ESH in Hs; unfold shadow_addr, SHADOW_OFF in Hs; lia | lia].
    - unfold MS; cbn [ms_mem mkst]. exact (Hv0 i Hi).
    - rewrite Hall; [exact (Hsh3 i Hi) | rewrite ESH; unfold shadow_addr, SHADOW_OFF; lia |].
      intros [Hs | Hs]; [rewrite ESH in Hs; unfold shadow_addr, SHADOW_OFF in Hs; lia | lia]. }
  split; [exact HJB2|]. split; [exact (nts_kept_nE cx fp W3 _ HB HKP2)|].
  split.
  { exists bs. split; [|exact HGO].
    apply (nts_anlk_keep (rdW W3 (ms_mem ms3)) _ bs HNK). intros a Ha. apply (mbyte_of_aview SEGS).
    apply Hall; [unfold NK_SIZE, LA_G_NL in *; lia|].
    intros [Hs | Hs]; [unfold NK_SIZE, LA_G_NL in *; lia|].
    rewrite ESH in Hs; unfold shadow_addr, SHADOW_OFF, NK_SIZE, LA_G_NL in *; lia. }
  split; [exact To|]. split; [exact HBS2 | exact HAB2].
Qed.

Lemma nts_D0 : forall E, sv_denot E (SLit 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* ---- +0x1cc, fuzz_send returned: `bltz a0` to the send failure arm, else the receive set-up ---- *)
Lemma nts_C2 : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 bs,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_shape (AF_nl_talk + 0x1cc) ms3 ->
  nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ->
  getr (ms_regs ms3) 19 = w64 (nSH cx fp + 4) -> getr (ms_regs ms3) 22 = w64 NL_FD ->
  nk_socket_errno (n_kbs cx) = 0 ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs ->
  (nk_send_errno (n_kbs cx) <> 0 -> getr (ms_regs ms3) 10 = w64 (-1) /\
     au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (nk_send_errno (n_kbs cx)) /\ nts_g2f cx bs) ->
  (nk_send_errno (n_kbs cx) = 0 -> getr (ms_regs ms3) 10 = w64 (n_len cx) /\
     nt_gnl_open cx bs true (Z.of_nat (k_next (n_K0 cx)))) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 bs HB HJ HFR Hsh HBD R19 R22 Hso HNK Hfail Hok.
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _).
  destruct (nts_pre cx HB) as (_ & _ & _ & _ & _ & _ & _ & HLEN & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (D10 : sv_denot E (SOff 10 0) = getr (ms_regs ms3) 10)
    by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; subst E; apply nts_ew_reg; reflexivity).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x1cc) sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | apply Forall_nil | | ].
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS nts_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof (paj_run_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  pose proof (paj_run_to_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  psrr_branch_tok RUN BR HS SHOK nts_span; rewrite D10, nts_D0 in Hc.
  - destruct (Z.eq_dec (nk_send_errno (n_kbs cx)) 0) as [Hz | Hnz].
    + destruct (Hok Hz) as (R10 & _). rewrite R10, nts_bt_nonneg in Hc by (unfold NL_SENT_LEN in HLEN; lia).
      discriminate Hc.
    + destruct (Hfail Hnz) as (_ & Herr & HG2).
      paj_run_to_tok RUNTO HS HJ SHOK nts_span (AF_nl_talk + 0x2ec); [nts_awr_ro |].
      pose proof (nts_frame_of_nil _ _ _ HF) as HFm. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms) r = getr (ms_regs ms3) r)
        by nts_kreg HS HEdef.
      assert (R22' : getr (ms_regs ms) 22 = getr (ms_regs ms3) 22)
        by (prreg HS (22%bv : bv 5) Q; rewrite Q, HEdef; apply nts_ew_reg; reflexivity).
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (nts_EF0 cx fp k2 ly3 S3 W3 MS MD bs HB HJ HFR) end.
      * repeat split; reflexivity.
      * apply (nts_body_move cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 _ _ HBD Hregs HFm);
          [exact (proj1 (nts_wvb md3 mat)) | exact (proj2 (nts_wvb md3 mat))].
      * cbn [ms_regs mkst]. rewrite R22'. exact R22.
      * exact Hso.
      * exact Hnz.
      * cbn [ms_mem mkst]. rewrite HFm. exact Herr.
      * cbn [ms_mem mkst]. rewrite HFm. exact HNK.
      * exact HG2.
  - destruct (Z.eq_dec (nk_send_errno (n_kbs cx)) 0) as [Hz | Hnz].
    + destruct (Hok Hz) as (_ & HGO).
      paj_run_to_tok RUNTO HS HJ SHOK nts_span (AF_nl_talk + 0x1d0); [nts_awr_ro |].
      pose proof (nts_frame_of_nil _ _ _ HF) as HFm. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms) r = getr (ms_regs ms3) r)
        by nts_kreg HS HEdef.
      assert (Hx : forall r : bv 5, In r [19;22]%bv -> getr (ms_regs ms) r = getr (ms_regs ms3) r) by nts_kreg HS HEdef.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (nts_R cx fp k2 ly3 S3 W3 MS MD bs HB HJ HFR) end.
      * repeat split; reflexivity.
      * apply (nts_body_move cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 _ _ HBD Hregs HFm);
          [exact (proj1 (nts_wvb md3 mat)) | exact (proj2 (nts_wvb md3 mat))].
      * cbn [ms_regs mkst]. rewrite (Hx 19%bv ltac:(cbn; tauto)). exact R19.
      * cbn [ms_regs mkst]. rewrite (Hx 22%bv ltac:(cbn; tauto)). exact R22.
      * exact Hso.
      * exact Hz.
      * cbn [ms_mem mkst]. rewrite HFm. exact HNK.
      * exact HGO.
    + destruct (Hfail Hnz) as (R10 & _). rewrite R10, nts_bt_neg in Hc. discriminate Hc.
Qed.

(* ---- +0x1b4, fuzz_socket returned: `bltz a0` to the socket failure arm, else s6 := a0 and fuzz_send ---- *)
Lemma nts_C1 : forall cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 bs,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_shape (AF_nl_talk + 0x1b4) ms3 ->
  nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ->
  getr (ms_regs ms3) 19 = w64 (nSH cx fp + 4) -> getr (ms_regs ms3) 26 = w64 (n_len cx) ->
  getr (ms_regs ms3) 27 = w64 (n_req cx) ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs ->
  (nk_socket_errno (n_kbs cx) <> 0 -> getr (ms_regs ms3) 10 = w64 (-1) /\
     au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (nk_socket_errno (n_kbs cx)) /\ nt_gnl_fin cx bs) ->
  (nk_socket_errno (n_kbs cx) = 0 -> getr (ms_regs ms3) 10 = w64 NL_FD /\ nts_g1 cx bs) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 bs HB HJ HFR Hsh HBD R19 R26 R27 HNK Hfail Hok.
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  pose proof NL_TALK_AK_val as HAKv. pose proof alloc_ceiling_val as Hac.
  pose proof pa_B_ok as (HB0 & HB1 & HB2).
  pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
  pose proof HBD as (Hrg & R20 & R23 & R25 & Hst & HD).
  pose proof HD as (HJB & HKP & _).
  pose proof HKP as (_ & HRO & _).
  pose proof Hrg as (R2 & _ & _ & _ & _ & _ & R3 & R4).
  destruct (nts_pre cx HB) as (_ & _ & _ & _ & _ & _ & _ & HLEN & HMR & _ & _ & HFRQ & HGQ).
  pose proof HB as (_ & _ & _ & _ & _ & HRL & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (D10 : sv_denot E (SOff 10 0) = getr (ms_regs ms3) 10)
    by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; subst E; apply nts_ew_reg; reflexivity).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x1b4) sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | apply Forall_nil | | ].
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS nts_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof (paj_run_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  pose proof (paj_run_to_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  psrr_branch_tok RUN BR HS SHOK nts_span; rewrite D10, nts_D0 in Hc.
  - destruct (Z.eq_dec (nk_socket_errno (n_kbs cx)) 0) as [Hz | Hnz].
    + destruct (Hok Hz) as (R10 & _). rewrite R10, nts_bt_nonneg in Hc by (unfold NL_FD; lia). discriminate Hc.
    + destruct (Hfail Hnz) as (_ & Herr & HFIN).
      paj_run_to_tok RUNTO HS HJ SHOK nts_span (AF_nl_talk + 0x2cc); [nts_awr_ro |].
      pose proof (nts_frame_of_nil _ _ _ HF) as HFm. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms) r = getr (ms_regs ms3) r)
        by nts_kreg HS HEdef.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (nts_SF0 cx fp k2 ly3 S3 W3 MS MD bs HB HJ HFR) end.
      * repeat split; reflexivity.
      * apply (nts_body_move cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 _ _ HBD Hregs HFm);
          [exact (proj1 (nts_wvb md3 mat)) | exact (proj2 (nts_wvb md3 mat))].
      * exact Hnz.
      * cbn [ms_mem mkst]. rewrite HFm. exact Herr.
      * cbn [ms_mem mkst]. rewrite HFm. exact HNK.
      * exact HFIN.
  - destruct (Z.eq_dec (nk_socket_errno (n_kbs cx)) 0) as [Hz | Hnz].
    + destruct (Hok Hz) as (R10 & HG1).
      pose proof HG1 as (HL1 & WF1 & Hs1 & S1 & D1 & E1 & O1 & P1 & C1 & M1).
      paj_run_tok RUN HS HJ SHOK nts_span; [nts_awr_ro |].
      pose proof (nts_frame_of_nil _ _ _ HF) as HFm. clear HF HFr HG.
      lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
        by nts_kreg HS HEdef.
      assert (Hx : forall r : bv 5, In r [19]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r) by nts_kreg HS HEdef.
      prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
      prreg HS (12%bv : bv 5) Q12. prreg HS (22%bv : bv 5) Q22.
      rewrite HEdef, (nts_ew_reg _ _ 10 10%bv eq_refl), R10 in Q10, Q22.
      rewrite HEdef, (nts_ew_reg _ _ 27 27%bv eq_refl), R27 in Q11.
      rewrite HEdef, (nts_ew_reg _ _ 26 26%bv eq_refl), R26 in Q12.
      assert (HBD1 : nts_body cx fp k2 ly3 S3 W3 ms1 (with_vm_backing (m_vm_lazy md3) mat md3) nts_EW 0xf8).
      { apply (nts_body_move cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ms1 _ HBD Hregs HFm);
          [exact (proj1 (nts_wvb md3 mat)) | exact (proj2 (nts_wvb md3 mat))]. }
      pose proof HBD1 as (_ & _ & _ & _ & _ & HD1).
      assert (HAR1 : AR SEGS B ly3 S3 W3 (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat md3))
        by (destruct HJ as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
      assert (Usp1 : spZ (ms_regs ms1) = n_sp1 cx).
      { unfold spZ. rewrite (Hregs 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
      assert (Hreq : 0 <= n_req cx < 2 ^ 64) by (unfold n_req, aarg, argZ; apply bv_unsigned_in_range).
      assert (Hlen : 0 <= n_len cx < 2 ^ 64) by (unfold n_len, aarg, argZ; apply bv_unsigned_in_range).
      assert (A0 : aarg (ms_regs ms1) 0 = NL_FD).
      { unfold aarg, argZ. assert (X : getr (ms_regs ms1) (Z_to_bv 5 (10 + 0)) = w64 NL_FD) by exact Q10.
        rewrite X. unfold w64, NL_FD. apply unsigned_lit_small. lia. }
      assert (A1 : aarg (ms_regs ms1) 1 = n_req cx).
      { unfold aarg, argZ. assert (X : getr (ms_regs ms1) (Z_to_bv 5 (10 + 1)) = w64 (n_req cx)) by exact Q11.
        rewrite X. unfold w64. apply unsigned_lit_small. lia. }
      assert (A2 : aarg (ms_regs ms1) 2 = n_len cx).
      { unfold aarg, argZ. assert (X : getr (ms_regs ms1) (Z_to_bv 5 (10 + 2)) = w64 (n_len cx)) by exact Q12.
        rewrite X. unfold w64. apply unsigned_lit_small. lia. }
      destruct (nts_req cx fp k2 ly3 S3 W3 ms1 _ HB HJ HD1) as (Q1 & Q2 & Q3 & Q4).
      destruct (nts_errno_pre cx ly3 S3 W3 (ms_mem ms1) _ (ms_regs ms1) FUZZ_SEND_AK HB HAR1 Usp1
        ltac:(unfold FUZZ_SEND_AK, FUZZ_SEND_AFRAME, ESTACK; lia)) as (He1 & He2 & He3 & He4 & He5).
      destruct (zsh_gnl_ard B TB SEGS ly3 S3 W3 (ms_mem ms1) _ HAR1) as (Zg1 & Zg2).
      rewrite (proj1 (proj2 (proj2 nts_vals))).
      apply (nts_call_rd FUZZ_SEND_A FUZZ_SEND_AK _ _ _ _ FSE cx fp k2 ly3 S3 W3 (ms_mem ms1) _ md3 (ms_regs ms1)
        (AF_nl_talk + 0x1cc) (POST cx) HB HJ HJB ltac:(rewrite HFm; exact HRO));
        [ rewrite R1; reflexivity | unfold AF_nl_talk; lia | reflexivity
        | rewrite (Hregs 2%bv ltac:(cbn; tauto)); exact R2 | rewrite (Hregs 3%bv ltac:(cbn; tauto)); exact R3
        | rewrite (Hregs 4%bv ltac:(cbn; tauto)); exact R4 | unfold FUZZ_SEND_AK, FUZZ_SEND_AFRAME, ESTACK; lia
        | intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr; unfold NK_SEND_ERRNO, NK_N_SENT in *; lia
        | | |].
      * intros a Ha. unfold fuzz_send_ard, rd_ivl in Ha. rewrite A1, A2 in Ha. rewrite Usp1.
        apply Q4; [unfold FUZZ_SEND_AK, FUZZ_SEND_AFRAME, ESTACK; lia | lia | exact Ha].
      * unfold fuzz_send_apre. exists bs, (n_reqb cx). rewrite A1, A2.
        split; [rewrite HFm; exact HNK|]. split; [exact WF1|]. split; [exact Zg1|]. split; [exact Zg2|].
        split; [exact He1|]. split; [exact He2|]. split; [exact He3|]. split; [exact He4|]. split; [exact He5|].
        split; [exact Q1|]. split; [exact HRL|]. split; [exact HLEN|]. split; [exact HMR|].
        split; [exact Q2|]. split; [exact Q3|]. split; [exact HGQ|].
        unfold apart_frame in *. rewrite Usp1. unfold FUZZ_SEND_AK, FUZZ_SEND_AFRAME, ESTACK. lia.
      * intros ly4 S4 W4 rg2 mem4 md4 HJ4 HP Hfr4 Hfd4 Hfs4 HK4 Hset4 Hperm4 HPost.
        destruct (HPost bs (n_reqb cx) ltac:(rewrite HFm; exact HNK) ltac:(rewrite A1; exact Q1)
          ltac:(rewrite A2; exact HRL)) as (bs2 & HNK2 & WF2 & Fso & Fend & Fop & Fopd & Fcl & Fmis & Hsf & Hsk).
        rewrite A0, O1 in Fmis. cbn in Fmis.
        assert (Hs2 : nts_gsame NK_SEND_ERRNO (NK_N_SENT + 4) bs bs2).
        { apply (nts_gnl_kept cx ly3 S3 W3 (ms_mem ms1) W4 mem4 _ _ _ NK_SEND_ERRNO (NK_N_SENT + 4) bs bs2 HB HK4);
            [intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr; lia | rewrite HFm; exact HNK | exact HNK2]. }
        lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
          apply (nts_C2 cx fp k2 ly4 S4 W4 MS MD bs2 HB HJ4 ltac:(rewrite Hfr4; exact HFR)) end.
        -- repeat split; reflexivity.
        -- apply (nts_body_call cx fp k2 ly3 S3 W3 ms1 _ 0xf8 FUZZ_SEND_AK
             (fun a => inFP (fuzz_send_awr (ms_regs ms1) (rdW W3 (ms_mem ms1))) a) ly4 S4 W4 _ md4 HB HJ HBD1
             ltac:(unfold FUZZ_SEND_AK, FUZZ_SEND_AFRAME, ESTACK; lia));
             [| exact HJ4 | exact HP | exact Hfr4 | exact Hfd4 | exact Hfs4 | exact HK4 | exact Hset4 | exact Hperm4].
           intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr.
           unfold nts_EW, NK_SEND_ERRNO, NK_SOCKET_ERRNO, NK_N_SENT in *. lia.
        -- cbn [ms_regs mkst]. exact (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) (eq_trans (Hx 19%bv ltac:(cbn; tauto)) R19)).
        -- cbn [ms_regs mkst]. exact (eq_trans (HP 22 ltac:(unfold acallee_saved; lia)) Q22).
        -- exact Hz.
        -- exact HNK2.
        -- intros Hnz2. rewrite <- D1 in Hnz2.
           destruct (Hsf Hnz2) as (R10' & Sd2 & Herr2 & Nn2 & Ns2).
           split; [exact R10'|]. split; [rewrite <- D1; exact Herr2|].
           exact (nts_g_send_fail cx bs bs2 HB HG1 (nts_anlk_len _ _ _ HNK2) WF2 Hs2 Fso Fend Fop Fopd Fcl Fmis Sd2 Ns2).
        -- intros Hz2. rewrite <- D1 in Hz2.
           destruct (Hsk Hz2) as (R10' & Sd2 & Sn2 & Nn2).
           split; [cbn [ms_regs mkst]; rewrite R10'; exact Q12|].
           exact (nts_g_send_ok cx bs bs2 HB HG1 (nts_anlk_len _ _ _ HNK2) WF2 Hs2 Fso Fend Fop Fopd Fcl Fmis Sd2 Sn2 Nn2).
    + destruct (Hfail Hnz) as (R10 & _). rewrite R10, nts_bt_neg in Hc. discriminate Hc.
Qed.

(* ---- NT_sock (+0x1a0): a1 := 0x80003, a0 := 16, a2 := 0 and fuzz_socket ---- *)
Lemma nts_S0 : nt_from SK B POST (nt_sock_inv B).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (Hsh & Hrg & Hsv & Hhd & Hsl & R19 & R20 & R23 & R25 & R26 & R27 & Hfs & HJB & HKP & HNK & HRQ
                  & HBS & HAB).
  assert (HBD : nts_body cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8).
  { split; [exact Hrg|]. split; [exact R20|]. split; [exact R23|]. split; [exact R25|].
    split; [exact (conj Hsv (conj Hhd (conj Hsl Hfs)))|].
    apply (nts_dyn_mono cx fp k2 ly3 S3 W3 ms3 md3 (fun _ => False) HB); [|intros a []].
    exact (conj HJB (conj HKP (conj HBS (conj HAB (fun a (H : False) => False_ind _ H))))). }
  pose proof HB as (HA & _). destruct HA as (HJc & HGX & _).
  destruct (nts_geo cx HB) as (G16 & Gwlo & Gwhi & Gceil & G47 & GXO & GSTK & Gs1 & Gs32 & Gs16).
  pose proof NL_TALK_AK_val as HAKv. pose proof alloc_ceiling_val as Hac.
  pose proof pa_B_ok as (HB0 & HB1 & HB2).
  pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
  pose proof HKP as (_ & HRO & _).
  pose proof Hrg as (R2 & _ & _ & _ & _ & _ & R3 & R4).
  destruct (nts_kbs cx HB) as (WF0 & HL0 & HOP & HOC & HCC).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_nl_talk + 0x1a0) sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite HEdef. apply nts_seat; [exact Hsh | vm_compute; reflexivity | apply Forall_nil | | ].
    - unfold pairwise_disjoint. cbn. tauto.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS nts_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof (paj_run_x (PL := PL_link) SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  paj_run_tok RUN HS HJ SHOK nts_span; [nts_awr_ro |].
  pose proof (nts_frame_of_nil _ _ _ HF) as HFm. clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r [2;3;4;8;9;18;20;21;23;24;25]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nts_kreg HS HEdef.
  assert (Hx : forall r : bv 5, In r [19;26;27]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms3) r) by nts_kreg HS HEdef.
  prreg HS (1%bv : bv 5) R1.
  assert (HBD1 : nts_body cx fp k2 ly3 S3 W3 ms1 (with_vm_backing (m_vm_lazy md3) mat md3) nts_EW 0xf8).
  { apply (nts_body_move cx fp k2 ly3 S3 W3 ms3 md3 nts_EW 0xf8 ms1 _ HBD Hregs HFm);
      [exact (proj1 (nts_wvb md3 mat)) | exact (proj2 (nts_wvb md3 mat))]. }
  assert (HAR1 : AR SEGS B ly3 S3 W3 (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat md3))
    by (destruct HJ as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
  assert (Usp1 : spZ (ms_regs ms1) = n_sp1 cx).
  { unfold spZ. rewrite (Hregs 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  destruct (nts_errno_pre cx ly3 S3 W3 (ms_mem ms1) _ (ms_regs ms1) FUZZ_SOCKET_AK HB HAR1 Usp1
    ltac:(unfold FUZZ_SOCKET_AK; lia)) as (He1 & He2 & He3 & He4 & He5).
  rewrite (proj1 (proj2 nts_vals)).
  apply (nts_call FUZZ_SOCKET_A FUZZ_SOCKET_AK _ _ _ FSO cx fp k2 ly3 S3 W3 (ms_mem ms1) _ md3 (ms_regs ms1)
    (AF_nl_talk + 0x1b4) (POST cx) HB HJ HJB ltac:(rewrite HFm; exact HRO));
    [ rewrite R1; reflexivity | unfold AF_nl_talk; lia | reflexivity
    | rewrite (Hregs 2%bv ltac:(cbn; tauto)); exact R2 | rewrite (Hregs 3%bv ltac:(cbn; tauto)); exact R3
    | rewrite (Hregs 4%bv ltac:(cbn; tauto)); exact R4 | unfold FUZZ_SOCKET_AK; lia
    | intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr; unfold NK_SOCKET_ERRNO, NK_MISUSE, NK_N_SENT in *; lia
    | |].
  - unfold fuzz_socket_apre. exists (n_kbs cx).
    split; [rewrite HFm; exact HNK|]. split; [exact WF0|]. split; [exact HOC|].
    split; [exact He1|]. split; [exact He2|]. split; [exact He3|]. split; [exact He4 | exact He5].
  - intros ly4 S4 W4 rg2 mem4 md4 HJ4 HP Hfr4 Hfd4 Hfs4 HK4 Hset4 Hperm4 HPost.
    destruct (HPost (n_kbs cx) ltac:(rewrite HFm; exact HNK)) as (bs1 & HNK1 & WF1 & Fsd & Fend & Fcl & Hsf & Hsk).
    assert (Hs1 : nts_gsame NK_SOCKET_ERRNO (NK_MISUSE + 4) (n_kbs cx) bs1).
    { apply (nts_gnl_kept cx ly3 S3 W3 (ms_mem ms1) W4 mem4 _ _ _ NK_SOCKET_ERRNO (NK_MISUSE + 4) _ bs1 HB HK4);
        [intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr; lia | rewrite HFm; exact HNK | exact HNK1]. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
      apply (nts_C1 cx fp k2 ly4 S4 W4 MS MD bs1 HB HJ4 ltac:(rewrite Hfr4; exact HFR)) end.
    + repeat split; reflexivity.
    + apply (nts_body_call cx fp k2 ly3 S3 W3 ms1 _ 0xf8 FUZZ_SOCKET_AK
        (fun a => inFP (fuzz_socket_awr (ms_regs ms1) (rdW W3 (ms_mem ms1))) a) ly4 S4 W4 _ md4 HB HJ HBD1
        ltac:(unfold FUZZ_SOCKET_AK; lia));
        [| exact HJ4 | exact HP | exact Hfr4 | exact Hfd4 | exact Hfs4 | exact HK4 | exact Hset4 | exact Hperm4].
      intros a (r & [<- | []] & Hr); cbn [fst snd] in Hr.
      unfold nts_EW, NK_SOCKET_ERRNO, NK_MISUSE, NK_N_SENT in *. lia.
    + cbn [ms_regs mkst]. exact (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) (eq_trans (Hx 19%bv ltac:(cbn; tauto)) R19)).
    + cbn [ms_regs mkst]. exact (eq_trans (HP 26 ltac:(unfold acallee_saved; lia)) (eq_trans (Hx 26%bv ltac:(cbn; tauto)) R26)).
    + cbn [ms_regs mkst]. exact (eq_trans (HP 27 ltac:(unfold acallee_saved; lia)) (eq_trans (Hx 27%bv ltac:(cbn; tauto)) R27)).
    + exact HNK1.
    + intros Hnz. destruct (Hsf Hnz) as (R10' & So1 & Herr1 & Op1 & Opd1 & Mis1).
      split; [exact R10'|]. split; [exact Herr1|].
      exact (nts_g_sock_fail cx bs1 HB Hnz (nts_anlk_len _ _ _ HNK1) WF1 Hs1 Fsd Fend Fcl So1 Op1 Opd1 Mis1).
    + intros Hz. destruct (Hsk Hz) as (R10' & So1 & Op1 & Opd1 & Mis1).
      split; [exact R10'|].
      exact (nts_g_sock_ok cx bs1 HB (nts_anlk_len _ _ _ HNK1) WF1 Hs1 Fsd Fend Fcl So1 Op1 Opd1 Mis1).
Qed.

End w.

(* THE PHASE: NT_sock to NT_mf0_ra (nt_recv_inv) or to NT_tail (nt_tail_inv) *)
Lemma nt_sock : forall POST,
  nt_from SK B POST (nt_recv_inv B) -> nt_from SK B POST (nt_tail_inv B) -> nt_from SK B POST (nt_sock_inv B).
Proof. intros POST NREC NTAIL. exact (nts_S0 POST NREC NTAIL). Qed.

End b.
End a.

About nt_sock.
Print Assumptions nt_sock.
