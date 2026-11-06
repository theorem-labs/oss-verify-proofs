(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 463 of its 516 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceNextFitB.v, with its module names changed; 206 of its 252 lines of code are new or changed and 470 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: the three landings of
   the header phase (lib/B/Prog/PcapSourceNextHdrB.v, a Theorem Labs lane) that go on inside the call.
     hb_loop_at  NP_loop (0x8174c) after an empty record (incl = 0, 0x817cc `beqz a0` taken, NP_empty
                 0x81858..0x81864 wrote the frame's shadow bytes 4 and 5 := 0xf8): nx_loop_at at q + 16, lh kept.
     hb_sk1_at   NP_sk1 (0x81814, `bgeu s7,s2` 0x81810 not taken: cap < incl): nx_sk1_inv at q.
     hb_fit_at   NP_fit (0x81988, `bgeu s7,s2` 0x81810 taken: 0 < incl <= cap): nx_fit_inv at q.
   Each takes the phase's entry facts at NP_hd_ra (nx_mid, the chain clause, nx_next_ok) and the facts the run
   leaves at the landing (the three write windows, the registers, the two shadow bytes of `ph`, ps->orig) as
   premises, so this file reads no image and walks nothing. The memory side is hb_body_keepX / hb_kept_stepX /
   hb_mid_keepX (lib/B/Prog/PcapSourceNextHdrBKeep.v; the X forms also leave out [sp1 - 16, sp1), the frame of
   the four rd_u32 calls that run between NP_hd_ra and the landing); the model side is
   lib/B/Prog/PcapSourceNextHdrWords.v
   (chain_empty_at, kind_fit, kind_cutfit) and lib/A/Prog/PcapSourceNextSpec.v (nx_chain_stop).

   Each landing states the four registers nx_mid names that PRE does not (s5 = ps, s7 = cap, s10 = the shadow
   address of ps, s11 = ps + 8): nx_mid at the landing asks for them, and nothing else fixes them.

   TAKEN FROM: the proof of hb_exit_at (lib/B/Prog/PcapSourceNextHdrB.v, a working branch e1a3de4997e,
   a Theorem Labs lane), whose post side these copy; the statements are a Theorem Labs lane's (HdrBLand-brief.md (sha256 7e999fd3bc13; internal record)).

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; capstone 5 disassembly of its unstripped twin). *)
(* Modified by Theorem Labs, 2026-10: the Require of PcapSourceNextFitB.v, made only for its vm_frame / asource_at_frame
   copies (deleted; lib/A/Prog/PcapSourceCloseSpec.v holds them), is dropped: this file names none of them. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI01 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import RdU32.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs PcapSourceNextHdrBDefs.
(* hb_body_keepX, hb_kept_stepX, hb_mid_keepX: what one segment of the run keeps; chain_empty_at and the kind
   lemmas. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import
PcapSourceNextHdrBKeep PcapSourceNextHdrWords PcapSourceNextSkipDefs PcapSourceNextFitADefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.

(* ---------------------------------------------------------------------------------------------- *)
(* nx_mid at a landing                                                                              *)
(* ---------------------------------------------------------------------------------------------- *)

(* The middle state at a landing pc with the frame's shadow sh (NSH_ph, or NSH_entry after NP_empty), the stream
   at q' = q + 16 and ps->orig = ol': the run from NP_hd_ra wrote only the three windows (the slot NS_SEC,
   ps->orig, the shadow bytes 4 and 5 of `ph`) and its rd_u32 callees only their frame [sp1 - 16, sp1), so every
   fact of the entry's nx_mid but those carries over (hb_exit_at's post side). *)
Lemma hb_land_mid : forall cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 md' q lh pc sh ol' q',
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms') md' k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W ms md3 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_pc_val ms' = w64 (BASE + pc) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  nregs cx ms' -> getr (ms_regs ms') 25 = w64 (nSH cx fp) ->
  getr (ms_regs ms') 21 = w64 (n_ps cx) -> getr (ms_regs ms') 23 = w64 (n_cap cx) ->
  getr (ms_regs ms') 26 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) ->
  getr (ms_regs ms') 27 = w64 (n_ps cx + PS_SW_OFF) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 4) = Some (nth 4 sh 0) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 5) = Some (nth 5 sh 0) ->
  (forall i, (i < 8)%nat -> i <> 4%nat -> i <> 5%nat -> nth i sh 0 = nth i NSH_ph 0) ->
  length sh = NX_NSH ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 ol' ->
  q + nx_hk (n_C cx) q = q' ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nx_mid B MT KS cx fp pc sh (nx_E cx) q' ol' (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W ms' md'.
Proof.
intros cx fp k2 ly3 S3 W ms ms' md3 md' q lh pc sh ol' q' HB HJ HJ' Hfr3 HMID UNCH
  Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 R21 R23 R26 R27 Hsh4 Hsh5 Hshrest Hshlen Vol' Hq' Hfds Hfs.
subst q'.
pose proof HMID as (HBODY & _ & _ & _ & _ & HJBK & HKEPT & _ & Hh0 & HPSAT & HRADDR & HSRC & Hqrange & HBJ &
  HTSV).
assert (UNCH24 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + PS_LEN) ->
  ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
  aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha N1 N2 N3 N4. apply UNCH;
  [exact Ha | exact N1 | clear - N2; unfold PS_LEN, PS_OL_OFF in *; lia | exact N3 | exact N4]. }
destruct (hb_mid_keepX B KS LAWS ASIL cx fp k2 ly3 S3 W ms ms' md3 (nx_ol cx lh) ol'
  (q + nx_hk (n_C cx) q) HB HJ Hfr3 UNCH Hh0 HPSAT Vol' HRADDR HSRC HBJ HTSV)
  as (Qps & Qra & Qsrc & Qbj & Qts).
split.
{ exact (hb_body_keepX B KS LAWS cx fp k2 ly3 S3 W ms ms' md3 NP_hd_ra pc sh HB HJ Hfr3 HBODY UNCH24
    Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 Hsh4 Hsh5 Hshrest Hshlen). }
split; [exact R21|]. split; [exact R23|]. split; [exact R26|]. split; [exact R27|].
split.
{ pose proof HJBK as (K1 & K2 & K3 & K4 & K5). split; [exact K1|]. split; [exact K2|].
  split; [exact K3|]. split; [rewrite Hfds; exact K4 | rewrite Hfs; exact K5]. }
split.
{ (* nx_kept *)
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres' & _).
  apply (hb_kept_stepX B KS LAWS cx fp k2 ly3 S3 W (ms_mem ms) md3 (ms_mem ms') HB HJ Hfr3);
  [ exact UNCH24
  | intros a Ha; apply Hpres';
    pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _);
    clear - Ha Hwlo Hwhi; lia
  | exact HKEPT ]. }
split; [intros a Ha; exact Ha|].
split; [exact Hh0|]. split; [exact Qps|]. split; [exact Qra|]. split; [exact Qsrc|].
split; [exact Hqrange|]. split; [exact Qbj|]. exact Qts.
Qed.

(* A full header leaves the stream at q + 16. *)
Lemma hb_hk16 : forall C q, q + 16 <= Z.of_nat (length C) -> q + nx_hk C q = q + 16.
Proof. intros C q H. unfold nx_hk, NX_PH_LEN. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (2) NP_sk1: cap < incl                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma hb_sk1_at : forall (R : ncx -> Z -> Prop) cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 md' q lh,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms') md' k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W ms md3 ->
  nx_next_ok R cx q -> nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  n_p cx <= q -> q + 16 <= Z.of_nat (length (n_C cx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  nregs cx ms' -> getr (ms_regs ms') 25 = w64 (nSH cx fp) ->
  getr (ms_regs ms') 21 = w64 (n_ps cx) -> getr (ms_regs ms') 23 = w64 (n_cap cx) ->
  getr (ms_regs ms') 26 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) -> getr (ms_regs ms') 27 = w64 (n_ps cx + PS_SW_OFF) ->
  getr (ms_regs ms') 19 = w64 (nF cx fp + NO_PH) -> getr (ms_regs ms') 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nx_incl cx q <> 0 -> n_cap cx < nx_incl cx q ->
  ms_pc_val ms' = w64 (BASE + NP_sk1) ->
  bv_unsigned (getr (ms_regs ms') 22) mod 2 ^ 32 = nx_incl cx q ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 4) = Some 0 ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 5) = Some 0 ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 (nx_ol cx (Some q)) ->
  nx_sk1_inv B MT KS R cx fp k2 ly3 S3 W ms' md'.
Proof.
intros R cx fp k2 ly3 S3 W ms ms' md3 md' q lh HB HJ HJ' Hfr3 HMID Hnext Hchain Hpq Hq16 UNCH
  Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 R21 R23 R26 R27 R19 R20 Hfds Hfs Hi0 Hcap Hpc R22 Hsh4 Hsh5 Vol'.
unfold nx_sk1_inv. exists q, lh.
split; [exact Hnext|]. split; [exact Hchain|]. split; [exact Hq16|].
split; [exact Hi0|]. split; [exact Hcap|].
split.
{ apply (hb_land_mid cx fp k2 ly3 S3 W ms ms' md3 md' q lh NP_sk1 NSH_ph (nx_ol cx (Some q)) (q + 16)
    HB HJ HJ' Hfr3 HMID UNCH Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 R21 R23 R26 R27);
  [ replace (nth 4 NSH_ph 0) with 0 by (vm_compute; reflexivity); exact Hsh4
  | replace (nth 5 NSH_ph 0) with 0 by (vm_compute; reflexivity); exact Hsh5
  | intros; reflexivity
  | vm_compute; reflexivity
  | exact Vol'
  | exact (hb_hk16 (n_C cx) q Hq16)
  | exact Hfds
  | exact Hfs ]. }
split; [exact R19|]. split; [exact R20|]. exact R22.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (3) NP_fit: 0 < incl <= cap                                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma hb_fit_at : forall (R : ncx -> Z -> Prop) cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 md' q lh,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms') md' k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W ms md3 ->
  nx_next_ok R cx q -> nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  n_p cx <= q -> q + 16 <= Z.of_nat (length (n_C cx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  nregs cx ms' -> getr (ms_regs ms') 25 = w64 (nSH cx fp) ->
  getr (ms_regs ms') 21 = w64 (n_ps cx) -> getr (ms_regs ms') 23 = w64 (n_cap cx) ->
  getr (ms_regs ms') 26 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) -> getr (ms_regs ms') 27 = w64 (n_ps cx + PS_SW_OFF) ->
  getr (ms_regs ms') 19 = w64 (nF cx fp + NO_PH) -> getr (ms_regs ms') 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  0 < PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <= n_cap cx ->
  ms_pc_val ms' = w64 (BASE + NP_fit) ->
  getr (ms_regs ms') 18 = w64 (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  getr (ms_regs ms') 22 = w64 (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  bv_unsigned (getr (ms_regs ms') 24) mod 2 ^ 32 = PSN.hw (n_sw cx =? 1) (nxF (n_C cx)) q 4 ->
  (exists v, nslot cx W ms' NS_SEC v /\ v mod 2 ^ 32 = PSN.hw (n_sw cx =? 1) (nxF (n_C cx)) q 0) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 4) = Some 0 ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 5) = Some 0 ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) ->
  nx_fit_inv B MT KS cx fp k2 ly3 S3 W ms' md'.
Proof.
intros R cx fp k2 ly3 S3 W ms ms' md3 md' q lh HB HJ HJ' Hfr3 HMID Hnext Hchain Hpq Hq16 UNCH
  Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 R21 R23 R26 R27 R19 R20 Hfds Hfs Hinc Hpc R18 R22 R24 HSEC
  Hsh4 Hsh5 Vol'.
(* the model: the record at q fits the buffer (KFit, or KCutFit when the file ends inside it), so the walk
   stops at q and q is the last non-empty header *)
assert (Hk : PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KFit \/
             PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KCutFit).
{ destruct (Z.le_gt_cases (q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) (Z.of_nat (length (n_C cx))))
    as [Hle|Hgt].
  - left. apply kind_fit; clear - Hq16 Hinc Hle; lia.
  - right. apply kind_cutfit; clear - Hq16 Hinc Hgt; lia. }
destruct (nx_chain_stop (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh Hchain
  ltac:(rewrite nxF_length; clear - Hq16; lia)
  ltac:(destruct Hk as [Hk|Hk]; rewrite Hk; discriminate)
  ltac:(destruct Hk as [Hk|Hk]; rewrite Hk; discriminate)) as (Hq' & Hlh').
unfold nx_fit_inv. cbv beta zeta.
exists q.
split.
{ apply (hb_land_mid cx fp k2 ly3 S3 W ms ms' md3 md' q lh NP_fit NSH_ph
    (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) (q + 16)
    HB HJ HJ' Hfr3 HMID UNCH Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 R21 R23 R26 R27);
  [ replace (nth 4 NSH_ph 0) with 0 by (vm_compute; reflexivity); exact Hsh4
  | replace (nth 5 NSH_ph 0) with 0 by (vm_compute; reflexivity); exact Hsh5
  | intros; reflexivity
  | vm_compute; reflexivity
  | exact Vol'
  | exact (hb_hk16 (n_C cx) q Hq16)
  | exact Hfds
  | exact Hfs ]. }
split; [unfold nx_q; exact Hq'|].
split; [unfold nx_lh; rewrite Hlh'; destruct Hk as [Hk|Hk]; rewrite Hk; reflexivity|].
split; [exact Hpq|]. split; [exact Hinc|].
split; [exact R18|]. split; [exact R22|]. split; [exact R24|]. exact HSEC.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (1) NP_loop: incl = 0                                                                            *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma hb_loop_at : forall (R : ncx -> Z -> Prop) cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 md' q lh,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms') md' k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh) (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W ms md3 ->
  nx_next_ok R cx q -> nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh ->
  n_p cx <= q -> q + 16 <= Z.of_nat (length (n_C cx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  nregs cx ms' -> getr (ms_regs ms') 25 = w64 (nSH cx fp) ->
  getr (ms_regs ms') 21 = w64 (n_ps cx) -> getr (ms_regs ms') 23 = w64 (n_cap cx) ->
  getr (ms_regs ms') 26 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) -> getr (ms_regs ms') 27 = w64 (n_ps cx + PS_SW_OFF) ->
  getr (ms_regs ms') 19 = w64 (nF cx fp + NO_PH) -> getr (ms_regs ms') 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q = 0 ->
  ms_pc_val ms' = w64 (BASE + NP_loop) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 4) = Some (nth 4 NSH_entry 0) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 5) = Some (nth 5 NSH_entry 0) ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 (nx_ol cx lh) ->
  nx_loop_at B MT KS R cx fp k2 ly3 S3 W ms' md'.
Proof.
intros R cx fp k2 ly3 S3 W ms ms' md3 md' q lh HB HJ HJ' Hfr3 HMID Hnext Hchain Hpq Hq16 UNCH
  Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 R21 R23 R26 R27 R19 R20 Hfds Hfs Hincl Hpc Hsh4 Hsh5 Vol'.
(* the next turn starts at q + 16 with the same lh (an empty record is no header the model keeps) *)
unfold nx_loop_at, nx_loop_inv. exists (q + 16), lh.
split; [exact (Hnext (q + 16) ltac:(clear - Hq16; lia))|].
split.
{ apply (hb_land_mid cx fp k2 ly3 S3 W ms ms' md3 md' q lh NP_loop NSH_entry (nx_ol cx lh) (q + 16)
    HB HJ HJ' Hfr3 HMID UNCH Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 R21 R23 R26 R27 Hsh4 Hsh5);
  [ intros i Hi H4 H5; destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; first [reflexivity | exfalso; lia]
  | reflexivity
  | exact Vol'
  | exact (hb_hk16 (n_C cx) q Hq16)
  | exact Hfds
  | exact Hfs ]. }
split; [exact R19|]. split; [exact R20|].
apply chain_empty_at; [exact Hchain | clear - Hq16; lia | exact Hincl | clear - Hq16; lia].
Qed.

End c.
End b.
End a.
