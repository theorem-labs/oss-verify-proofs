(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths, module names and numbers changed; 1300 of its 1492 lines of code are new or changed and 739 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v (ge_seat / ge_land) to libreac/fuzz_pcap's pcap_source_next: the region list, the atoms, the spill slots and the frame (class 0, its header and flag word) are this function's; nx_land0 / nx_land, the struct's region, the shadow entry, the first-seat environment and the kept-relation step are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapSourceNextSeat.v, with its module names changed; 373 of its 472 lines of code are new or changed and 1393 lines of the source are left out. *)
(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the landing step NP_empty
   (0x81b00) -> NP_loop (0x81998), shared by the two phases that reach it: PcapSourceNextHdrB.v's KEmpty arm (the
   record's incl is 0, `beqz s9` 0x81a2c taken) and PcapSourceNextSkip.v's KBig end (the last chunk of an oversize
   record was read, `bnez s9` 0x81afc not taken).

   THE CODE (four instructions):
     0x81b00  ff800513  addi a0,zero,-8
     0x81b04  00a98223  sb   a0,4(s3)      the shadow bytes 4, 5 of the frame (`ph`, F + 32 .. F + 47)
     0x81b08  00a982a3  sb   a0,5(s3)      go out of scope again: NSH_ph becomes NSH_entry
     0x81b0c  e8dff06f  j    0x81998       NP_loop, the head of the record loop
   Nothing else is written: no register but a0, no byte of the caller's.

   THE PROOF. The phase's state at NP_empty (nx_empty_inv) is seated as the engine's symbolic state
   with PcapSourceNextSeat.v's nx_seat (standard registers nx_sr, shadow NSH_ph with the write window
   [4, 6), no extra region), run to NP_loop (paj_run_to_sh), and landed with nx_land_by (the shadow
   literals NE_VS) and nx_kept_step (the caller's kept relation). The rest of the middle state (the
   struct, its shadow, the stream, the buffer, the timestamp cell) is carried over the run by the
   bytes the run may write (ne_wr: the stack window and the frame's 8 shadow bytes), with the
   geometry lemmas ported from a Theorem Labs lane's PcapSourceNextHdrB.v (hb_geo .. hb_mid_step, without the
   struct's 16-byte window that phase writes).

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017df0462bf382b3211837851bf801e792673b1cee0797cdca2a; capstone 5 disassembly
   of 0x81af0 .. 0x81b10). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05 PcapImgEnd.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PaStep PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC1g YC1h YC4b YC88 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceNextSeatG
  PcapSourceNextSeat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The seat at NP_empty: the standard registers, every spill slot, the frame's shadow NSH_ph with
   the bytes 4 and 5 writable (0x81b04, 0x81b08), no frame chunk and no extra region. *)
Definition ne_ss : sstate := nx_ss NP_empty nx_sr true NSH_ph 4 6 0 [] [] nx_facts0.

(* The frame's shadow after the run, as the literals the engine stores: a0 = -8 (0x81b00) into the
   bytes 4 and 5; each is 0xf8 mod 256, so the shadow is NSH_entry again. *)
Definition NE_VS : list Z := [241; 241; 241; 241; 18446744073709551608; 18446744073709551608; 243; 243].

(* Two class-0-aligned frames whose ranges are apart have shadow ranges apart (PcapSourceNextHdrB.v's
   hb_shadow_apart). *)
Lemma ne_shadow_apart : forall F G n a, F mod 64 = 0 -> G mod 8 = 0 -> n mod 8 = 0 ->
  0 <= F -> 0 <= G -> 0 <= n -> (F + 64 <= G \/ G + n <= F) ->
  SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8 ->
  SHADOW_OFF + G / 8 <= a < SHADOW_OFF + G / 8 + n / 8 -> False.
Proof. intros F G n a HF HG Hn H0 H1 H2 Hd Ha Hb. Z.div_mod_to_equations. lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* THE ENTRY PREDICATE AT NP_empty (0x81b00). The record that ends here is empty (KEmpty) or an
   oversize record read to its end (KBig); either way the record loop goes on at the file position q
   the producer names, with lh the last non-empty record header seen. R is the top's measure of the
   record loop (nx_loop_at): the producer proves R cx q from its own nx_next_ok. The frame's shadow
   is NSH_ph (`ph` in scope since 0x81998). The registers the next turn needs besides nx_mid's are
   s4 = buf, s5 = ps, s7 = cap and s10 = F + 32 (a Theorem Labs lane fixed this shape). *)
Definition nx_empty_inv (R : ncx -> Z -> Prop) (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : Z) (lh : option Z), R cx q /\
    nx_mid B MT KS cx fp NP_empty NSH_ph (nx_E cx) q (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx)
      k2 ly3 S3 W3 ms3 md3 /\
    getr (ms_regs ms3) 20 = w64 (n_buf cx) /\ getr (ms_regs ms3) 21 = w64 (n_ps cx) /\
    getr (ms_regs ms3) 23 = w64 (n_cap cx) /\ getr (ms_regs ms3) 26 = w64 (nF cx fp + NO_PH) /\
    nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh.

(* The bytes the run may write: its stack window (the spill slots are in it) and the frame's shadow. *)
Definition ne_wr (cx : ncx) (fp : Z) (a : Z) : Prop :=
  (spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx)) \/ (nSH cx fp <= a < nSH cx fp + 8).

Lemma ne_wb_md : forall l mat (md : Model), m_fds (with_vm_backing l mat md) = m_fds md /\
  m_fs (with_vm_backing l mat md) = m_fs md.
Proof. intros l mat md. destruct md as [f [mp lz mt] io fs pr li ti sg sc]. split; reflexivity. Qed.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.

Section d.
Variable cx : ncx.
Variable fp k2 : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
#[local] Notation m3 := (ms_mem ms3).
#[local] Notation E0 := (nx_mkE cx fp (ms_regs ms3)).
Hypothesis HB : nx_base SK B KS cx.
Hypothesis HJ : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx)
  (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.
Hypothesis HFR : frames S3 = (NX_CID, fp) :: frames (n_Sc cx).
Variable q : Z.
Variable lh : option Z.
Hypothesis HM : nx_mid B MT KS cx fp NP_empty NSH_ph (nx_E cx) q (nx_ol cx lh)
  (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3.

(* ---- the geometry (PcapSourceNextHdrB.v's hb_J .. hb_geo_frame) ---- *)

Lemma ne_J : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
  (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx).
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. assumption. Qed.

Lemma ne_frame_addr_eq : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p.
Proof.
  intros c p. pose proof HJ as (_ & Hly3 & _). pose proof ne_J as (_ & Hlyc & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _). destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _).
  unfold frame_addr. rewrite EF3, EFc. reflexivity.
Qed.

Lemma ne_in_frames : forall c p, In (c, p) (n_own cx) -> In (c, p) (frames (n_Sc cx)).
Proof.
  intros c p H. pose proof ne_J as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact H.
Qed.

Local Ltac ne_base := let H := fresh in pose proof HB as H; unfold nx_base in H; decompose [and] H.

Lemma ne_psfr : In (n_cid cx, n_pos cx) (n_own cx) /\ frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) <= n_ps cx /\
  n_ps cx + PS_LEN <= frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx) /\
  n_ps cx mod 8 = 0 /\ 4096 <= n_ps cx /\ n_ps cx + PS_LEN <= 2 ^ 47.
Proof. ne_base. repeat split; assumption. Qed.

Lemma ne_buf : n_h cx <> 0 ->
  In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B (n_lyc cx) (n_Sc cx)) /\
  (n_buf cx + nx_bufn (n_cap cx) <= n_ps cx \/ n_ps cx + PS_LEN <= n_buf cx) /\ 0 <= n_cap cx <= NX_CAP_MAX.
Proof.
  intros Hh. ne_base.
  match goal with H : n_h cx <> 0 -> In (n_buf cx, _) _ /\ _ |- _ => destruct (H Hh) as (B1 & _ & _ & _ & _ & B6 & _ & B8) end.
  repeat split; try assumption; lia.
Qed.

Lemma ne_stream : n_h cx <> 0 ->
  In (n_h cx, SRC_FILE_BLOCK) (ablocks B (n_lyc cx) (n_Sc cx)) /\
  In (n_b cx, Z.of_nat (length (n_C cx))) (ablocks B (n_lyc cx) (n_Sc cx)) /\
  (n_ps cx + PS_LEN <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= n_ps cx) /\
  (n_ps cx + PS_LEN <= n_b cx \/ n_b cx + Z.of_nat (length (n_C cx)) <= n_ps cx) /\
  Z.of_nat (length (n_C cx)) < 2 ^ 26 /\ 0 <= n_p cx.
Proof.
  intros Hh. ne_base.
  match goal with H : n_h cx <> 0 -> In (n_h cx, SRC_FILE_BLOCK) _ /\ _ |- _ =>
    destruct (H Hh) as (S1 & S2 & _ & S4 & S5 & _ & _ & S8 & S9 & _) end.
  repeat split; try assumption; lia.
Qed.

Lemma ne_tsfr : n_h cx <> 0 -> n_ts cx <> 0 ->
  (exists tcid tpos, In (tcid, tpos) (n_own cx) /\ frame_addr (n_lyc cx) tcid tpos <= n_ts cx /\
     n_ts cx + 8 <= frame_addr (n_lyc cx) tcid tpos + fs_frame_bytes tcid) /\
  (n_ts cx + 8 <= n_ps cx \/ n_ps cx + PS_LEN <= n_ts cx) /\ 4096 <= n_ts cx.
Proof.
  intros Hh Ht. ne_base.
  match goal with H : n_h cx <> 0 -> n_ts cx <> 0 -> _ |- _ =>
    destruct (H Hh Ht) as (_ & _ & T3 & _ & _ & T6 & _ & _ & T9 & _) end.
  split; [exact T6|]. split; [exact T9 | exact T3].
Qed.

(* The own frame and a caller frame are apart. *)
Lemma ne_frames_apart : forall c p, In (c, p) (frames (n_Sc cx)) ->
  nF cx fp + 64 <= frame_addr (n_lyc cx) c p \/ frame_addr (n_lyc cx) c p + fs_frame_bytes c <= nF cx fp.
Proof.
  intros c p Hin. pose proof HJ as (HAR3 & _).
  apply in_split in Hin as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 m3 md3 (NX_CID, fp) (c, p) [] l2 l3 HAR3
    ltac:(rewrite HFR, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !ne_frame_addr_eq in Hd.
  assert (Hfb : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity). rewrite Hfb in Hd.
  unfold nF. lia.
Qed.

Lemma ne_geo :
  alloc_ceiling + NX_STK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= 2 ^ 47 /\
  spZ (n_regs cx) - 240 <= n_sp1 cx <= spZ (n_regs cx) - 224 /\
  4096 <= nF cx fp /\ nF cx fp + 64 <= alloc_ceiling /\ in_app (nF cx fp) 64 /\ nF cx fp mod 64 = 0 /\
  nSH cx fp = SHADOW_OFF + nF cx fp / 8 /\
  SHADOW_OFF + 512 <= nSH cx fp /\ nSH cx fp + 8 <= kHighMemBeg.
Proof.
  pose proof HB as HB'. unfold nx_base in HB'.
  destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hlo & Hhi & _).
  pose proof ne_J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (Hac & _ & HHB & _ & _).
  pose proof HJ as (HAR3 & _).
  assert (Hin : In (NX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ NX_CID fp HAR3 Hin) as (HF0 & HFc & HFia).
  pose proof (frame_al64 SEGS B ly3 S3 W3 m3 md3 NX_CID fp HAR3 Hin) as (H64 & _).
  assert (Hfb : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
  unfold nSH, nF, shadow_of_addr. rewrite <- ne_frame_addr_eq. rewrite Hfb in HFc, HFia.
  unfold n_sp1, nx_sp1, NX_MFRAME.
  assert (Hx : 0 <= spZ (n_regs cx) - 224) by (unfold NX_STK, AFREAD_STK in *; lia).
  pose proof (Z.div_mod (spZ (n_regs cx) - 224) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(lia)) as Hmp.
  pose proof (Z.div_mod (spZ (n_regs cx)) 16 ltac:(lia)) as Hd16.
  assert (Hm : (spZ (n_regs cx) - 224) mod 32 = 0 \/ (spZ (n_regs cx) - 224) mod 32 = 16) by (rewrite Hal in Hd16; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  assert (D0 : 512 <= frame_addr ly3 NX_CID fp / 8) by (apply Z.div_le_lower_bound; lia).
  assert (D1 : frame_addr ly3 NX_CID fp / 8 + 8 <= (frame_addr ly3 NX_CID fp + 64) / 8)
    by (replace (frame_addr ly3 NX_CID fp + 64) with (frame_addr ly3 NX_CID fp + 8 * 8) by lia;
        rewrite Z.div_add by lia; lia).
  assert (D2 : (frame_addr ly3 NX_CID fp + 64) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  change (2 ^ 47 / 8) with 17592186044416 in D2.
  unfold NX_STK, AFREAD_STK in *. unfold SHADOW_OFF. repeat split; lia.
Qed.

(* The caller's frame a byte of its struct (or of its timestamp cell) lies in, and the geometry
   of that frame. *)
Lemma ne_geo_frame : forall c p x n, In (c, p) (n_own cx) ->
  frame_addr (n_lyc cx) c p <= x -> x + n <= frame_addr (n_lyc cx) c p + fs_frame_bytes c -> 0 <= n ->
  4096 <= frame_addr (n_lyc cx) c p /\ frame_addr (n_lyc cx) c p + fs_frame_bytes c <= alloc_ceiling /\
  in_app (frame_addr (n_lyc cx) c p) (fs_frame_bytes c) /\
  off_img (frame_addr (n_lyc cx) c p) (fs_frame_bytes c) /\
  frame_addr (n_lyc cx) c p mod 64 = 0 /\ fs_frame_bytes c mod 64 = 0 /\
  (nF cx fp + 64 <= frame_addr (n_lyc cx) c p \/ frame_addr (n_lyc cx) c p + fs_frame_bytes c <= nF cx fp).
Proof.
  intros c p x n Hown Hlo Hhi Hn.
  pose proof (ne_in_frames c p Hown) as Hin. pose proof HJ as (HAR3 & _).
  assert (Hin3 : In (c, p) (frames S3)) by (rewrite HFR; right; exact Hin).
  pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR3 Hin3) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 m3 md3 c p HAR3 Hin3) as HFo.
  pose proof (frame_al64 SEGS B ly3 S3 W3 m3 md3 c p HAR3 Hin3) as (H64 & H64b & _).
  rewrite ne_frame_addr_eq in HF0, HFc, HFia, HFo, H64.
  pose proof (ne_frames_apart c p Hin) as Hap.
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|].
  split; [exact H64|]. split; [exact H64b | exact Hap].
Qed.

Lemma ne_shadow_not_app : forall a, nSH cx fp <= a < nSH cx fp + 8 ->
  kLowShadowBeg + 4096 <= a /\ a < kHighMemBeg.
Proof.
  intros a Ha. pose proof ne_geo as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2).
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* A byte of a caller's heap block is not written by the run. *)
Lemma ne_block_out : forall p n x, In (p, n) (ablocks B (n_lyc cx) (n_Sc cx)) ->
  p <= x < p + req_size n -> 0 <= x < 2 ^ 64 /\ ~ ne_wr cx fp x.
Proof.
  intros p n x Hin Hx. pose proof ne_J as (HARc & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & Hp4 & Hpc & Hpia & _).
  pose proof ne_geo as (Hsp & _). pose proof asan_consts as (Hac & _).
  split; [lia|]. intros [Hw | Hw]; [lia |].
  pose proof (ne_shadow_not_app x Hw). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* A byte of a caller frame is not written by the run, and neither is its shadow. *)
Lemma ne_frame_out : forall c p x, In (c, p) (n_own cx) ->
  frame_addr (n_lyc cx) c p <= x < frame_addr (n_lyc cx) c p + fs_frame_bytes c ->
  (0 <= x < 2 ^ 64 /\ ~ ne_wr cx fp x) /\
  (0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ ne_wr cx fp (shadow_of_addr SHADOW_OFF x)).
Proof.
  intros c p x Hown Hx.
  destruct (ne_geo_frame c p x 0 Hown ltac:(lia) ltac:(lia) ltac:(lia)) as (Hg4 & Hgc & Hgia & _ & Hg64 & Hgb64 & Hap).
  pose proof ne_geo as (Hsp & _ & _ & HF0 & HFc & HFia & HF64 & HSHe & HSH0 & HSH1).
  pose proof asan_consts as (Hac & _).
  assert (HG8 : frame_addr (n_lyc cx) c p mod 8 = 0) by (clear - Hg64; Z.div_mod_to_equations; lia).
  assert (Hn8 : fs_frame_bytes c mod 8 = 0) by (clear - Hgb64; Z.div_mod_to_equations; lia).
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  assert (Hsx : SHADOW_OFF + frame_addr (n_lyc cx) c p / 8 <= shadow_of_addr SHADOW_OFF x <
                SHADOW_OFF + frame_addr (n_lyc cx) c p / 8 + fs_frame_bytes c / 8).
  { unfold shadow_of_addr. clear - Hx HG8 Hn8 Hnn Hg4. Z.div_mod_to_equations. lia. }
  assert (Hsx2 : shadow_of_addr SHADOW_OFF x < kHighMemBeg).
  { unfold shadow_of_addr, kHighMemBeg, SHADOW_OFF in *.
    assert (x / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). change (0x7fffff800000 / 8) with 17592184995840 in *. lia. }
  split.
  - split; [lia|]. intros [Hw | Hw]; [lia |].
    pose proof (ne_shadow_not_app x Hw). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - split; [unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *; split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | lia]|].
    intros [Hw | Hw].
    + unfold kHighMemBeg in *. lia.
    + rewrite HSHe in Hw. exact (ne_shadow_apart (nF cx fp) (frame_addr (n_lyc cx) c p) (fs_frame_bytes c)
        (shadow_of_addr SHADOW_OFF x) HF64 HG8 Hn8 ltac:(lia) ltac:(lia) Hnn Hap Hw Hsx).
Qed.

(* ---- the seat at NP_empty ---- *)

Lemma ne_seat : st_ok_pi SEGS VAL E0 ne_ss (restrict (w_H W3) ms3).
Proof.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof HM as (Hbd & _).
  pose proof Hbd as ((_ & _ & _ & _ & _ & _ & Hnr & _ & _ & _ & _ & _ & H18 & H19 & _) & _).
  apply (nx_seat B KS LAWS TL cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 NP_empty nx_sr NSH_ph 4 6 0 [] [] nx_facts0
    HE HEI Hbd (nx_regs_ok B KS cx fp ms3 HB Hnr H18 H19) ltac:(unfold NX_FRAME; lia) (Forall_nil _) ltac:(lia) ltac:(lia)
    ltac:(vm_compute; reflexivity) (Forall_nil _) I).
  - unfold nx_regions0. repeat constructor.
  - exact (nx_facts0_ok B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 HE).
Qed.

(* The run's writes are the caller's to allow: the spill slots (in the stack window) and the own
   frame's shadow (PcapSourceNextHdrB.v's hb_awr without the struct's region). *)
Lemma ne_awr : awr_ok E0 (ss_mem ne_ss) (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx))
  (ablocks B ly3 S3) ly3 ((NX_CID, fp) :: n_own cx).
Proof.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof (nx_bases B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 HE HEI) as (U2 & U60 & U516 & U529 & U242 & U256).
  pose proof ne_geo as (Hsp & Hsp47 & Hsp1 & HF0 & HFc & HFia & HF64 & HSHe & HSH0 & HSH1).
  assert (Hst : n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK /\ spZ (n_regs cx) <= n_sp0 cx) by (ne_base; lia).
  unfold ne_ss, nx_ss, nx_regions, nx_regions0. cbn [ss_mem app].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_at _ _ _ _ _ _ _ _ _ _ NA_SP1 (n_sp1 cx)); [reflexivity | exact U60 | cbn; unfold NX_STK, AFREAD_STK in *; lia | cbn; unfold NX_SPILL; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ NA_FSH (nSH cx fp)); [reflexivity | exact U529 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi nx_shadow_region] in Ha. apply awr_byte_own_head_shadow.
    rewrite ne_frame_addr_eq. fold (nF cx fp). unfold shadow_addr. rewrite HSHe in Ha.
    assert (Hfb : fs_frame_bytes NX_CID / 8 = 8) by (vm_compute; reflexivity). rewrite Hfb. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
Qed.

(* A register the run does not write keeps its value (the seat's atom NA_CUR + i). *)
Lemma ne_reg : forall (ms' : machine_state) ss' i (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  st_ok_pi SEGS VAL E0 ss' (restrict (w_H W3) ms') -> sr_get (ss_regs ss') r = SOff (530 + i) 0 ->
  getr (ms_regs ms') r = getr (ms_regs ms3) r.
Proof.
  intros ms' ss' i r Hi Hr HS' Hsr.
  rewrite (st_ok_pi_restrict_reg _ E0 ss' ms' r HS'), Hsr, nx_sv_SOff0.
  etransitivity; [exact (nx_mkE_cur cx fp (ms_regs ms3) i Hi)|].
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hr. unfold bv_wrap. change (bv_modulus 5) with 32.
  apply Z.mod_small. lia.
Qed.

(* ---- what the run keeps of the middle state ---- *)
Section e.
Variable m' : word -> option byte.
Hypothesis HFm : frame_of E0 (ss_mem ne_ss) (rdW W3 m3) (rdW W3 m').
Hypothesis HGm : mem_grows (rdW W3 m3) (rdW W3 m').

Lemma ne_HV : forall a, 0 <= a < 2 ^ 64 -> ~ ne_wr cx fp a ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m3 a.
Proof.
  intros a Ha Hn.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof ne_geo as (Hsp & Hsp47 & Hsp1 & _).
  apply (nx_keep_out B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 true NSH_ph 4 6 0 [] [] m3 m' HE HEI HFm a Ha).
  - intros Hw. apply Hn. left. unfold NX_SPILL, NX_STK, AFREAD_STK in *. lia.
  - lia.
  - intros Hw. apply Hn. right. lia.
  - intros (r & Hin & _). destruct Hin.
Qed.

Lemma ne_mbyte : forall x, 0 <= x < 2 ^ 64 -> ~ ne_wr cx fp x ->
  mbyte SEGS (rdW W3 m') x = mbyte SEGS (rdW W3 m3) x.
Proof. intros x Hx Hn. apply (mbyte_of_aview SEGS). apply ne_HV; assumption. Qed.

Lemma ne_ra_step : forall x n, 0 <= n ->
  (forall y, x <= y < x + n -> exists c p, In (c, p) (n_own cx) /\
     frame_addr (n_lyc cx) c p <= y < frame_addr (n_lyc cx) c p + fs_frame_bytes c) ->
  range_addressable (aview SEGS (w_H W3) m3) SHADOW_OFF x n ->
  range_addressable (aview SEGS (w_H W3) m') SHADOW_OFF x n.
Proof.
  intros x n Hn Hfr HR. apply (PcapSourceCloseSpec.ra_frame _ _ x n HR).
  intros y Hy. destruct (Hfr y Hy) as (c & p & Hown & Hyr).
  destruct (ne_frame_out c p y Hown Hyr) as (_ & Hs1 & Hs2). apply ne_HV; assumption.
Qed.

(* The caller's kept relation across the run: PcapSourceNextSeat.v's nx_kept_step with no extra
   region (Ew' = False), then the write set back to the caller's. *)
Lemma ne_kept : forall Ew,
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m3 (spZ (n_regs cx)) Ew ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m' (spZ (n_regs cx)) Ew.
Proof.
  intros Ew Hbl HK.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof HK as (_ & _ & _ & _ & _ & K6).
  assert (HX : forall a, in_wrange E0 [] a -> False /\ ~ in_img SEGS a) by (intros a (r & Hin & _); destruct Hin).
  assert (HPr : forall a, spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx) -> apresent (w_H W3) m' a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HGm (K6 a Ha))).
  pose proof (nx_kept_step B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR E0 true NSH_ph 4 6 0 [] []
    m3 m' Ew (fun _ => False) HE HEI Hbl ltac:(unfold NX_FRAME; lia) ltac:(lia) ltac:(lia) HFm HGm HX HPr HK) as HK'.
  eapply nx_kept_mono; [| exact HK']. intros a [Ha | []]. exact Ha.
Qed.

(* The middle state at NP_loop from the one at NP_empty: the body and r24 the landing gives, the
   rest carried over the run (PcapSourceNextHdrB.v's hb_mid_step, with no byte of the struct written). *)
Lemma ne_mid_step : forall (ms' : machine_state) md',
  ms_mem ms' = m' ->
  nx_body cx fp NP_loop W3 ms' NSH_entry ->
  getr (ms_regs ms') 24 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nx_mid B MT KS cx fp NP_loop NSH_entry (nx_E cx) q (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx)
    k2 ly3 S3 W3 ms' md'.
Proof.
  intros ms' md' Hm' Hbd Hs8 Hfds Hfs.
  pose proof HM as (_ & _ & (Hk & Hbl & Hmo & Hfds3 & Hfs3) & HK & HEs & Hh & Hps & Hra & Hsrc & Hq & Hbuf & Hts).
  unfold nx_mid. rewrite Hm'.
  pose proof ne_psfr as (Hown & Hpl & Hph & Hps8 & Hps4 & Hps47).
  split; [exact Hbd|]. split; [exact Hs8|].
  split; [split; [exact Hk|]; split; [exact Hbl|]; split; [exact Hmo|]; split; [rewrite Hfds; exact Hfds3 | rewrite Hfs; exact Hfs3]|].
  split; [exact (ne_kept (nx_E cx) Hbl HK)|].
  split; [exact HEs|]. split; [exact Hh|].
  split.
  { destruct Hps as (Hf & Hsw & Hol & Hvt & Hvid & Hpad & Hpadl).
    assert (Hall : forall y, n_ps cx <= y < n_ps cx + PS_LEN ->
      mbyte SEGS (rdW W3 m') y = mbyte SEGS (rdW W3 m3) y).
    { intros y Hy. apply ne_mbyte; apply (proj1 (ne_frame_out (n_cid cx) (n_pos cx) y Hown ltac:(unfold PS_LEN in *; lia))). }
    unfold nx_ps_at.
    split; [eapply PcapSourceClose.vm_frame; [| exact Hf]; intros y Hy; apply Hall; unfold PS_F_OFF, PS_LEN in *; cbn in Hy; lia|].
    split; [eapply PcapSourceClose.vm_frame; [| exact Hsw]; intros y Hy; apply Hall; unfold PS_SW_OFF, PS_LEN in *; cbn in Hy; lia|].
    split; [eapply PcapSourceClose.vm_frame; [| exact Hol]; intros y Hy; apply Hall; unfold PS_OL_OFF, PS_LEN in *; cbn in Hy; lia|].
    split; [eapply PcapSourceClose.vm_frame; [| exact Hvt]; intros y Hy; apply Hall; unfold PS_VT_OFF, PS_LEN in *; cbn in Hy; lia|].
    split; [eapply PcapSourceClose.vm_frame; [| exact Hvid]; intros y Hy; apply Hall; unfold PS_VID_OFF, PS_LEN in *; cbn in Hy; lia|].
    split; [|exact Hpadl].
    apply (garr8_frame SEGS _ _ _ _ Hpad). intros y Hy. rewrite Hpadl in Hy. apply Hall. cbn in Hy. unfold PS_LEN. lia. }
  split.
  { apply ne_ra_step; [unfold PS_LEN; lia | | exact Hra].
    intros y Hy. exists (n_cid cx), (n_pos cx). split; [exact Hown | unfold PS_LEN in *; lia]. }
  destruct (ne_stream Hh) as (Hinh & Hinb & Hsh & Hsb & Hlen & Hp0).
  split.
  { apply (PcapSourceClose.asource_at_frame KS (rdW W3 m3) (rdW W3 m')); [|exact Hsrc].
    intros a [Ha | [Ha | Ha]].
    - pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as (_ & Hrq).
      destruct (ne_block_out (n_h cx) SRC_FILE_BLOCK a Hinh ltac:(lia)) as (H1 & H2).
      apply ne_mbyte; assumption.
    - pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as (_ & Hrq).
      destruct (ne_block_out (n_b cx) (Z.of_nat (length (n_C cx))) a Hinb ltac:(lia)) as (H1 & H2).
      apply ne_mbyte; assumption.
    - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _ & _).
      pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2.
      pose proof ne_geo as (Hsp & _).
      apply ne_mbyte; [unfold kLowMemEnd in Hr2; lia|].
      intros [Hw | Hw]; [pose proof asan_consts as (Hac & _); unfold pcap_img_end, YImgTop.IMG_TOP in *; lia|].
      pose proof (ne_shadow_not_app a Hw). unfold kLowShadowBeg, kLowMemEnd in *. lia. }
  split; [exact Hq|].
  split.
  { destruct Hbuf as (bj' & Hg & Hl). exists bj'. split; [|exact Hl].
    destruct (ne_buf Hh) as (Hinbuf & Hsep & Hcap).
    pose proof HB as HB'. unfold nx_base in HB'.
    assert (Hlb : Z.of_nat (length (n_bj cx)) = nx_bufn (n_cap cx))
      by (decompose [and] HB'; match goal with H : n_h cx <> 0 -> In (n_buf cx, _) _ /\ _ |- _ =>
            destruct (H Hh) as (_ & _ & _ & _ & L & _); exact L end).
    apply (garr8_frame SEGS _ _ _ _ Hg). intros y Hy. rewrite Hl, Hlb in Hy.
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & Hrq).
    destruct (ne_block_out (n_buf cx) (nx_bufn (n_cap cx)) y Hinbuf ltac:(lia)) as (H1 & H2).
    apply ne_mbyte; assumption. }
  intros Hts0. destruct (Hts Hts0) as (Hv & Hrat).
  destruct (ne_tsfr Hh Hts0) as ((tc & tp & Htown & Htl & Hth) & Htsep & Hts4).
  split.
  - eapply PcapSourceClose.vm_frame; [| exact Hv]. intros y Hy. cbn in Hy.
    apply ne_mbyte; apply (proj1 (ne_frame_out tc tp y Htown ltac:(lia))).
  - apply ne_ra_step; [lia | | exact Hrat].
    intros y Hy. exists tc, tp. split; [exact Htown | lia].
Qed.

End e.

(* ---- the landing at NP_loop ---- *)
Lemma ne_leaf : forall R (ms' : machine_state) md' ss',
  R cx q ->
  st_ok_pi SEGS VAL E0 ss' (restrict (w_H W3) ms') ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  frame_of E0 (ss_mem ne_ss) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  ss_resv ss' = None -> nx_sr_ok cx fp E0 (ss_regs ss') ->
  nx_land_chk true NE_VS (ss_mem ss') = true -> ss_pc ss' = NP_loop ->
  sr_get (ss_regs ss') 20 = SOff (530 + 20) 0 -> sr_get (ss_regs ss') 21 = SOff (530 + 21) 0 ->
  sr_get (ss_regs ss') 23 = SOff (530 + 23) 0 -> sr_get (ss_regs ss') 24 = SOff (530 + 24) 0 ->
  sr_get (ss_regs ss') 26 = SOff (530 + 26) 0 ->
  getr (ms_regs ms3) 20 = w64 (n_buf cx) -> getr (ms_regs ms3) 21 = w64 (n_ps cx) ->
  getr (ms_regs ms3) 23 = w64 (n_cap cx) -> getr (ms_regs ms3) 26 = w64 (nF cx fp + NO_PH) ->
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  nx_loop_at B MT KS R cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros R ms' md' ss' HR HS' HJ' HF HG Hfds Hfs Hrv Hsr Hchk Hpc G20 G21 G23 G24 G26 Hs4 Hs5 Hs7 Hs10 Hch.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof HM as (_ & H24 & _ & _ & _ & Hh & _).
  pose proof (nx_land_by B KS LAWS cx fp k2 ly3 S3 W3 ms' md' HB HJ' HFR E0 ss' NE_VS NSH_entry
    HE HEI HS' Hrv Hsr Hchk eq_refl eq_refl Hh) as Hbd.
  rewrite Hpc in Hbd.
  assert (Hs8 : getr (ms_regs ms') 24 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx))).
  { rewrite <- H24. exact (ne_reg ms' ss' 24 24%bv ltac:(lia) ltac:(vm_compute; reflexivity) HS' G24). }
  exists q, lh. split; [exact HR|].
  unfold nx_loop_inv. split.
  { exact (ne_mid_step (ms_mem ms') HF HG ms' md' eq_refl Hbd Hs8 Hfds Hfs). }
  split; [rewrite <- Hs4; exact (ne_reg ms' ss' 20 20%bv ltac:(lia) ltac:(vm_compute; reflexivity) HS' G20)|].
  split; [rewrite <- Hs5; exact (ne_reg ms' ss' 21 21%bv ltac:(lia) ltac:(vm_compute; reflexivity) HS' G21)|].
  split; [rewrite <- Hs7; exact (ne_reg ms' ss' 23 23%bv ltac:(lia) ltac:(vm_compute; reflexivity) HS' G23)|].
  split; [rewrite <- Hs10; exact (ne_reg ms' ss' 26 26%bv ltac:(lia) ltac:(vm_compute; reflexivity) HS' G26)|].
  exact Hch.
Qed.

(* ---- the walk 0x81b00 .. 0x81b0c ---- *)
Lemma ne_walk : forall POST R,
  nx_from SK B KS POST (nx_loop_at B MT KS R) -> R cx q ->
  getr (ms_regs ms3) 20 = w64 (n_buf cx) -> getr (ms_regs ms3) 21 = w64 (n_ps cx) ->
  getr (ms_regs ms3) 23 = w64 (n_cap cx) -> getr (ms_regs ms3) 26 = w64 (nF cx fp + NO_PH) ->
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST R HLOOP HR Hs4 Hs5 Hs7 Hs10 Hch.
  pose proof ne_seat as HS.
  pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE.
  pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
  pose proof HJ as HJ0.
  (* 0x81b00 addi a0,zero,-8; 0x81b04 sb a0,4(s3); 0x81b08 sb a0,5(s3); 0x81b0c j NP_loop (0x81998) *)
  paj_run_to_sh RUNTOP HS HJ0 NP_loop; [exact ne_awr|].
  lazymatch goal with |- SRr _ _ (mkCfg ?m ?md) _ =>
    apply (HLOOP cx fp k2 ly3 S3 W3 m md HB HJ0 HFR);
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
      apply (ne_leaf R m md _ HR HS HJ0 HFr HG) end end.
  - exact (proj1 (ne_wb_md _ _ _)).
  - exact (proj2 (ne_wb_md _ _ _)).
  - reflexivity.
  - apply (nx_sr_ok_std B KS cx fp HB _ _ HE); vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exact Hs4.
  - exact Hs5.
  - exact Hs7.
  - exact Hs10.
  - exact Hch.
Qed.

End d.

(* ---------------------------------------------------------------------------------------------- *)
(* The step                                                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

(* From NP_empty (0x81b00) to the record loop's head NP_loop (0x81998): `ph` out of scope again
   (shadow NSH_ph -> NSH_entry), the turn's position and header kept. Both producers (PcapSourceNextHdrB.v's KEmpty
   arm, PcapSourceNextSkip.v's KBig end) consume this one lemma. *)
Theorem nx_empty_step : forall (POST : ncx -> world SEGS -> config -> Prop) (R : ncx -> Z -> Prop),
  nx_from SK B KS POST (nx_loop_at B MT KS R) ->
  nx_from SK B KS POST (nx_empty_inv R).
Proof.
  intros POST R HLOOP cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR (q & lh & HR & HM & Hs4 & Hs5 & Hs7 & Hs10 & Hch).
  exact (ne_walk cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR q lh HM POST R HLOOP HR Hs4 Hs5 Hs7 Hs10 Hch).
Qed.

End c.
End b.
End a.

(* nx_empty_inv names no sink head, so SK is not among its binders: its arguments are {fx} {rc} {PI}
   B MT KS, the loop measure R and the eight of a phase predicate (as nx_hdra_inv's). *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (PI : PAImg pcap_listing) (B : asyms) (MT : ameter_ops)
  (KS : asource_syms) (R : ncx -> Z -> Prop) => @nx_empty_inv fx rc PI B MT KS R).
(* GUARD: the step's arguments, in the order a caller passes them (as pb_nx_hdrB's: SK by name, then
   B MT KS, the Section hypotheses LAWS TL ASIL, POST and R). *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing)
  (B : asyms) (MT : ameter_ops) (KS : asource_syms) (LAWS : AR_laws pa_segs B) (TL : PALib B)
  (ASIL : asource_img_laws SK pa_segs B KS) (POST : ncx -> world pa_segs -> config -> Prop)
  (R : ncx -> Z -> Prop) =>
  (nx_empty_step (SK := SK) B MT KS LAWS TL ASIL POST R
    : nx_from SK B KS POST (nx_loop_at B MT KS R) -> nx_from SK B KS POST (nx_empty_inv B MT KS R))).
