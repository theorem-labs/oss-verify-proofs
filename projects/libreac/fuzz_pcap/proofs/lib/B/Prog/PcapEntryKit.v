(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written for libreac/fuzz_pcap -- a Theorem Labs lane of the walk of fuzz_pcap's entry function
   LLVMFuzzerTestOneInput on fuzz_pcap.asan-ubsan (libreac v1.9.0, 0x80818, listing offset AF_LLVMFuzzerTestOneInput
   = 0x90 of lib/B/Prog/PcapList.v): phase L3, the record loop's head and the harness's skip loop, as cut lemmas in the
   pe_from form of lib/B/Prog/PcapEntryDefs.v at the waypoint invariants GI_* of lib/B/Prog/PcapEntryPhases.v.

   The stretches (pcs of the pin; capstone disassembly llvmf-au.dis (sha256 be945029c797; internal record)):
     KD  -> K4 / K5  0x80b04 `blez a0` (n = first <= 0 to 0x80e04: s10 := 24, n spilled at 0x70(s1), PP_K5 0x80e0c);
                     else the loop's constants (0x80b08 .. 0x80b3c: a3 := 0, calls := 0 at 0x68(s1), buf + 12 at
                     0x38(s1), s7 := ~b, s10 := 24, s5 := -8, 0xf00 at 0x30(s1), 10^6 2^32 at 0x40(s1), n at
                     0x70(s1)) to PP_K4 0x80b40.
     K4  -> KR       0x80b40 .. 0x80b8c: the calls bound 0x80b50 (abort), first := (calls = 0 ? n : a3) at 0x50(s1)
                     (0x80b5c .. 0x80b64), n <= cap 0x80b70 (abort), at + 16 <= g_file_len 0x80b7c (abort), the UBSan
                     guard 0x80b80 `beqz s2` (file = NULL), calls := calls + 1 (0x80b84 .. 0x80b8c), to PP_KR 0x80b90.
     KR  -> KRI      the UBSan guards 0x80b90 `bltu s7,s10` (wrap(file + e)) and 0x80b98 `bgeu s3,s5` (wrap(file + e +
                     8)), s3 := file + e, a1 := ps.swapped (0x80b9c `lw a1,8(s4)`), a0 := s3 + 8, and the call of rd32
                     (0x80ba4) to its return PP_KRI 0x80ba8.
     KRI -> KR / KO  s11 := incl (sign-extended), s9 := incl (zero-extended); 0x80bb4 `beqz s11` (an empty record) and
                     0x80bbc `bgeu a0(=cap),s9` (a fit one) decide the arm. Skip: s9 := e + incl, s6 := e + incl + 32,
                     s10 := e + incl + 16, 0x80bd0 `bgeu len,s6` back to PP_KR, else 0x80bd4 `j` to PP_abort. Fit: the
                     UBSan guard 0x80bdc `bltu a0(=-17),s3` (wrap(file + e + 16)), at + 16 + incl <= len 0x80be8
                     (abort), a1 := ps.swapped, s6 := ps.last_orig_len (0x80bf0 `lw s6,0xc(s4)`), a0 := s3 + 12, and
                     the call of rd32 (0x80bf8) to its return PP_KO 0x80bfc.
   The skip loop (KR -> KRI -> KR) is closed here by induction on |F| - e (pe_from_skip_m); the record loop's measure
   is the same register (s10 = at <= e <= Q), so pe_meas states every cut lemma at a bound m on |F| - s10 for the lane
   that closes the record loop (K4 <= KL2 <= ... <= KO <= KRI <= KR <= K4).

   Rule 24 (task text of a Theorem Labs lane): a search of the proof index for LLVMFuzzerTestOneInput (index v5 built
   2026-10-28T21:58:24Z, rebuilt 23:22:17Z, recipes 566eb6ffa5d) rc=0; the 30 named files are all in other units, and no
   row names libreac/fuzz_pcap; the working-branch search found no Qed walk of it on any asan-ubsan image. CONFIRM
   (23:47Z): the released fuzz_pcap harness walks (lib/U/Prog/Slot/USegE.v etc.) are for the v1.8 UBSAN image (343
   instructions, 176-byte frame) against this pin's 530 instructions with a 256-byte frame and ASan instrumentation, so
   this is a new proof. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapEntrySkip.v, with its module paths and module names changed; 609 of its 737 lines of code are new or changed and 2304 lines of the source are left out. *)
(* lib/B kit for the walk of fuzz_pcap's entry function LLVMFuzzerTestOneInput (0x80818, asan-ubsan build of libreac
   v1.9.0): helpers every phase file of the walk (lib/B/Prog/PcapEntry<Phase>.v) shares, moved out of
   lib/B/Prog/PcapEntryRec.v with the same names and statements (a Theorem Labs lane's request, 02:0xZ):
   - the lib/B instances of W_journal's run chain over ajournal_gx (bpaj_run_x / bpaj_run_to_x; lib/A's paj_run_x is
     fixed at lib/A's listing);
   - rec_ctx: what pe_base and the cut's journal give at a cut (stack, frame and input-block bounds);
   - the keep lemmas: the cut's memory facts across a stretch whose writes stay in one interval [lo, hi) (mk);
   - facts of the reader's model (kind_fit, res_*, rec_bytes_len, ...);
   - rd32_call: lib/B/Prog/Rd32.v pb_rd32X lifted to the harness's ajournal_gx, with the byte helpers it needs
     (asource_at_bytes, garr8_four, p_C_fb, trd32_hw);
   - EBx / Espan / branch_lt0, the shadow convention and the signed-branch helper of the stretches' runs. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapList PcapAddr PcapPa.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI09 YI08 YI0s YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YE00 YG0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Rd32.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct pcap_source_struct_next.
From LinuxProcessSemantics.Riscv Require Sem Instr.
Import ListNotations.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Module ACL := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceCloseSpec.
Module BCL := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSourceClose.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.

(* The lib/B instances of W_journal's run chain over ajournal_gx (lib/A's paj_run_x is fixed at lib/A's listing). *)
Definition bpaj_run_x (G : list (Z * Z)) (HG : gx_ok SEGS B G) (XO : Z) (OUT : list (Z * Z)) :=
  SRr_run_pi_tok_AJX psym SEGS B LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL pa_sigma pcap_listing
    pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
Definition bpaj_run_to_x (G : list (Z * Z)) (HG : gx_ok SEGS B G) (XO : Z) (OUT : list (Z * Z)) :=
  SRr_run_to_pi_tok_AJX psym SEGS B LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL pa_sigma pcap_listing
    pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.

(* ---- arithmetic ---- *)
Lemma w64_mod64 : forall z, w64 (z mod 2 ^ 64) = w64 z.
Proof.
intros z. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

Lemma mod64_mod8 : forall x, x mod 64 = 0 -> (x + 32) mod 8 = 0.
Proof.
intros x H. destruct (proj1 (Zmod_divides x 64 ltac:(lia)) H) as [q Hq].
rewrite Hq. replace (64 * q + 32) with ((8 * q + 4) * 8) by lia. apply Z_mod_mult.
Qed.

(* ---- what the start and the journal give at a cut ---- *)
Lemma rec_ctx : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  gx_ok SEGS B pe_G /\ AR SEGS B ly3 S3 W3 (ms_mem ms3) md3 /\
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  c_sp1 cx = pe_sp1 (spZ (c_regs cx)) /\
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W3) (ms_mem ms3) a) /\
  4096 <= pF cx fp /\ pF cx fp + PE_FRAME <= alloc_ceiling /\ pF cx fp mod 64 = 0 /\
  ly_F ly3 = ly_F (c_ly cx) /\
  (c_n cx = 0 \/ (0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)) /\
  spZ (c_regs cx) - 288 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0.
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr.
pose proof HB as (Hpre & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & _ & _ & HG & _).
pose proof Hpre as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hin) as (Hf4096 & Hfceil & _).
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hin) as (Hf64 & _).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (EFa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
rewrite EFa in Hf4096, Hfceil, Hf64.
assert (HFB : fs_frame_bytes PE_CID = PE_FRAME) by (vm_compute; reflexivity). rewrite HFB in Hfceil.
split; [exact HG|]. split; [exact HAR|]. split; [exact Hal|]. split; [unfold LLVMF_STK in *; lia|].
split; [lia|]. split; [exact Hsp1|]. split; [exact Hpres|].
split; [exact Hf4096|]. split; [exact Hfceil|]. split; [exact Hf64|]. split; [exact EF|].
pose proof HB as (_ & _ & _ & _ & Hinp & _).
split.
{ destruct Hinp as [[Hn0 _] | (Hn & Hinb)]; [left; exact Hn0 | right].
  pose proof Hpre as (HARc & _).
  destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HARc Hinb)
    as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
rewrite Hsp1. unfold pe_sp1, PE_MFRAME.
split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* ---- what a stretch keeps: memory unchanged outside one interval [lo, hi) ---- *)
Definition mk (W3 : world SEGS) (m m' : word -> option byte) (lo hi : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma mk_refl : forall W3 m lo hi, mk W3 m m lo hi.
Proof. intros W3 m lo hi a _ _. reflexivity. Qed.
Lemma mk_trans : forall W3 m1 m2 m3 lo hi, mk W3 m1 m2 lo hi -> mk W3 m2 m3 lo hi -> mk W3 m1 m3 lo hi.
Proof. intros W3 m1 m2 m3 lo hi H1 H2 a Ha Hn. rewrite (H2 a Ha Hn). exact (H1 a Ha Hn). Qed.
Lemma mk_mono : forall W3 m m' lo hi lo' hi', lo' <= lo -> hi <= hi' -> mk W3 m m' lo hi -> mk W3 m m' lo' hi'.
Proof. intros W3 m m' lo hi lo' hi' H1 H2 H a Ha Hn. apply H; [exact Ha | lia]. Qed.

Lemma mk_mbyte : forall W3 m m' lo hi a, mk W3 m m' lo hi -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  mbyte SEGS (mrestrict (w_H W3) m') a = mbyte SEGS (mrestrict (w_H W3) m) a.
Proof. intros W3 m m' lo hi a H Ha Hn. apply (mbyte_of_aview SEGS). exact (H a Ha Hn). Qed.

Lemma rdword_keep : forall W3 m m' lo hi a v,
  rdword (aview SEGS (w_H W3) m) a = Some v -> mk W3 m m' lo hi ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lo \/ hi <= a) ->
  rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
intros W3 m m' lo hi a v Hw H Ha0 Ha8 Hd. unfold rdword in *.
rewrite (H a), (H (a + 1)), (H (a + 2)), (H (a + 3)), (H (a + 4)), (H (a + 5)), (H (a + 6)), (H (a + 7)) by lia.
exact Hw.
Qed.

Lemma pslot_keep : forall cx W3 (ms ms' : machine_state) lo hi off v,
  pslot cx W3 ms off v -> mk W3 (ms_mem ms) (ms_mem ms') lo hi ->
  0 <= c_sp1 cx + off -> c_sp1 cx + off + 8 <= 2 ^ 64 -> (c_sp1 cx + off + 8 <= lo \/ hi <= c_sp1 cx + off) ->
  pslot cx W3 ms' off v.
Proof. intros cx W3 ms ms' lo hi off v H Hk H0 H8 Hd. unfold pslot in *. exact (rdword_keep W3 _ _ lo hi _ v H Hk H0 H8 Hd). Qed.

Lemma val_mem_keep : forall W3 m m' lo hi a n v,
  val_mem SEGS (mrestrict (w_H W3) m) a n v -> mk W3 m m' lo hi ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
  val_mem SEGS (mrestrict (w_H W3) m') a n v.
Proof.
intros W3 m m' lo hi a n v Hv H H0 Hn Hd. eapply BCL.vm_frame; [|exact Hv].
intros x Hx. apply (mk_mbyte W3 m m' lo hi x H); lia.
Qed.

Lemma garr8_keep : forall W3 m m' lo hi a l,
  garr8 SEGS (mrestrict (w_H W3) m) a l -> mk W3 m m' lo hi ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (a + Z.of_nat (length l) <= lo \/ hi <= a) ->
  garr8 SEGS (mrestrict (w_H W3) m') a l.
Proof.
intros W3 m m' lo hi a l Hg H H0 Hn Hd. apply (garr8_frame SEGS _ _ _ _ Hg).
intros x Hx. apply (mk_mbyte W3 m m' lo hi x H); lia.
Qed.

Lemma env_low : forall a, asrc_env_addr KS a -> 0x10000 <= a < pcap_img_end.
Proof. intros a Ha. exact (pa_img_range a (proj1 (asil_env _ _ _ _ ASIL a Ha))). Qed.

Lemma asource_at_keep : forall W3 m m' lo hi f b C p,
  asource_at SEGS KS (mrestrict (w_H W3) m) f b C p -> mk W3 m m' lo hi -> alloc_ceiling <= lo ->
  0 <= f -> f + SRC_FILE_BLOCK <= alloc_ceiling -> 0 <= b -> b + Z.of_nat (length C) <= alloc_ceiling ->
  asource_at SEGS KS (mrestrict (w_H W3) m') f b C p.
Proof.
intros W3 m m' lo hi f b C p Hs H Hlo Hf0 Hf1 Hb0 Hb1.
pose proof asan_consts as (C1 & _).
apply (BCL.asource_at_frame KS (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') f b C p); [|exact Hs].
intros a [Ha | [Ha | Ha]].
- apply (mk_mbyte W3 m m' lo hi a H); lia.
- apply (mk_mbyte W3 m m' lo hi a H); lia.
- pose proof (env_low a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
  apply (mk_mbyte W3 m m' lo hi a H); lia.
Qed.

Lemma asource_none_keep : forall W3 m m' lo hi,
  asource_none SEGS KS (mrestrict (w_H W3) m) -> mk W3 m m' lo hi -> alloc_ceiling <= lo ->
  asource_none SEGS KS (mrestrict (w_H W3) m').
Proof.
intros W3 m m' lo hi Hs H Hlo. pose proof asan_consts as (C1 & _).
apply (BCL.asource_none_frame KS (mrestrict (w_H W3) m) (mrestrict (w_H W3) m')); [|exact Hs].
intros a Ha. pose proof (env_low a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
apply (mk_mbyte W3 m m' lo hi a H); lia.
Qed.

(* The memory part of pe_body. *)
Lemma pe_body_keep : forall cx fp pc pc' W3 (ms ms' : machine_state) sh lo hi,
  pe_body cx fp pc W3 ms sh ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = getr (ms_regs ms) 2 -> getr (ms_regs ms') 8 = getr (ms_regs ms) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms) 9 -> getr (ms_regs ms') 3 = getr (ms_regs ms) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms) 4 ->
  mk W3 (ms_mem ms) (ms_mem ms') lo hi -> alloc_ceiling <= lo -> hi <= spZ (c_regs cx) - 104 ->
  alloc_ceiling + LLVMF_STK <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  4096 <= pF cx fp -> pF cx fp + PE_FRAME <= alloc_ceiling ->
  (c_n cx = 0 \/ (0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)) ->
  pe_body cx fp pc' W3 ms' sh.
Proof.
intros cx fp pc pc' W3 ms ms' sh lo hi
  (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (R2 & R8 & R9 & R3 & R4) & Hsav & Hhd & Hsh & Hlen & Hin)
  Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' E2 E8 E9 E3 E4 H Hlo Hhi Hsp H47 Hf0 Hf1 Hinp.
unfold LLVMF_STK in Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp0 : 0 <= spZ (c_regs cx)) by (unfold spZ; apply bv_unsigned_in_range).
unfold PE_FRAME in Hf1.
split; [exact Hpc'|]. split; [exact Hrv'|]. split; [exact Hsv'|]. split; [exact Hrom'|].
split; [exact Hfr'|]. split; [exact Hfc'|].
split; [unfold pregs; rewrite E2, E8, E9, E3, E4; exact (conj R2 (conj R8 (conj R9 (conj R3 R4))))|].
split.
{ destruct Hsav as [S1 S2]. split.
  - apply (rdword_keep W3 (ms_mem ms) (ms_mem ms') lo hi _ _ S1 H); lia.
  - intros j Hj. apply (rdword_keep W3 (ms_mem ms) (ms_mem ms') lo hi _ _ (S2 j Hj) H); lia. }
split.
{ destruct Hhd as (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - apply (rdword_keep W3 (ms_mem ms) (ms_mem ms') lo hi _ _ H1 H); lia.
  - apply (rdword_keep W3 (ms_mem ms) (ms_mem ms') lo hi _ _ H2 H); lia.
  - apply (rdword_keep W3 (ms_mem ms) (ms_mem ms') lo hi _ _ H3 H); lia.
  - apply (rdword_keep W3 (ms_mem ms) (ms_mem ms') lo hi _ _ H4 H); unfold PE_FLAGPTR; lia. }
split.
{ intros i Hi. rewrite (H (pSH cx fp + Z.of_nat i)); [exact (Hsh i Hi)| |];
  unfold pSH, shadow_of_addr, SHADOW_OFF; rewrite Hlen in Hi; unfold PE_NSH in Hi;
  pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia));
  pose proof (Z.div_le_mono (pF cx fp) alloc_ceiling 8 ltac:(lia) ltac:(lia)); lia. }
split; [exact Hlen|].
destruct Hinp as [Hn0 | (Hp0 & Hp1)].
- unfold c_n in Hn0. destruct (c_pl cx) as [|x l]; [apply garr8_nil | cbn in Hn0; lia].
- apply (garr8_keep W3 (ms_mem ms) (ms_mem ms') lo hi _ _ Hin H); rewrite ?length_map; unfold c_n in Hp1; lia.
Qed.

(* The record bytes the reader leaves in the buffer are at most incl long (its prefix, PSN.rec_bytes). *)
Lemma rec_bytes_len : forall sw F Q, 0 <= PSN.incl sw F Q -> (PSN.tagged sw F Q = true -> 16 <= PSN.incl sw F Q) ->
  Z.of_nat (length (PSN.rec_bytes sw F Q)) <= PSN.incl sw F Q.
Proof.
intros sw F Q H0 Ht. unfold PSN.rec_bytes, PSN.rec_raw.
assert (Hr : (length (firstn (Z.to_nat (PSN.incl sw F Q)) (skipn (Z.to_nat (Q + 16)) F)) <= Z.to_nat (PSN.incl sw F Q))%nat)
  by (rewrite length_firstn; lia).
destruct (PSN.tagged sw F Q) eqn:Et.
- specialize (Ht eq_refl).
  set (R := firstn (Z.to_nat (PSN.incl sw F Q)) (skipn (Z.to_nat (Q + 16)) F)) in *.
  rewrite !length_app, !length_firstn, length_skipn, length_skipn.
  lia.
- lia.
Qed.

Lemma hw_range : forall sw F q j, 0 <= PSN.hw sw F q j < 2 ^ 32.
Proof.
intros sw F q j. unfold PSN.hw, PSN.w32le, PSN.fb.
assert (R : forall i, 0 <= bv_unsigned (nth (Z.to_nat i) F (Z_to_bv 8 0)) < 256).
{ intros i. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) F (Z_to_bv 8 0))) as H. unfold bv_modulus in H. exact H. }
destruct sw; pose proof (R (q + j)); pose proof (R (q + j + 1)); pose proof (R (q + j + 2)); pose proof (R (q + j + 3)); lia.
Qed.

Lemma tagged_incl : forall sw F Q, PSN.tagged sw F Q = true -> 18 <= PSN.incl sw F Q.
Proof.
intros sw F Q H. unfold PSN.tagged in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
apply Z.leb_le in H. exact H.
Qed.

Lemma kind_fit : forall sw F cap Q, PSN.kind sw F cap Q = PSN.KFit ->
  0 < PSN.incl sw F Q /\ PSN.incl sw F Q <= cap /\ Q + 16 + PSN.incl sw F Q <= Z.of_nat (length F) /\
  16 <= Z.of_nat (length F) - Q.
Proof.
intros sw F cap Q. unfold PSN.kind, PSN.flen. pose proof (hw_range sw F Q 8) as R. unfold PSN.incl in *.
destruct (Z.of_nat (length F) - Q =? 0) eqn:A; [intros Hk; discriminate Hk|].
destruct (Z.of_nat (length F) - Q <? 16) eqn:Bq; [intros Hk; discriminate Hk|].
destruct (PSN.hw sw F Q 8 =? 0) eqn:C; [intros Hk; discriminate Hk|].
destruct (PSN.hw sw F Q 8 <=? cap) eqn:D.
- destruct (Q + 16 + PSN.hw sw F Q 8 <=? Z.of_nat (length F)) eqn:G; [|intros Hk; discriminate Hk].
  intros _. apply Z.ltb_ge in Bq. apply Z.eqb_neq in C. apply Z.leb_le in D. apply Z.leb_le in G. lia.
- destruct (cap =? 0); [intros Hk; discriminate Hk|].
  destruct (Q + 16 + PSN.hw sw F Q 8 <=? Z.of_nat (length F)); intros Hk; discriminate Hk.
Qed.

Lemma res_fit_pos : forall sw F cap Q, PSN.kind sw F cap Q = PSN.KFit -> 0 < PSN.res_of sw F cap Q.
Proof.
intros sw F cap Q Hk. destruct (kind_fit sw F cap Q Hk) as (H1 & _).
unfold PSN.res_of. rewrite Hk. unfold PSN.rec_len.
destruct (PSN.tagged sw F Q) eqn:Et; [pose proof (tagged_incl sw F Q Et); lia | lia].
Qed.

Lemma res_range : forall sw F cap Q, -1 <= PSN.res_of sw F cap Q < 2 ^ 32.
Proof.
intros sw F cap Q. pose proof (hw_range sw F Q 8) as R. unfold PSN.res_of, PSN.rec_len.
destruct (PSN.kind sw F cap Q); try lia. destruct (PSN.tagged sw F Q) eqn:Et; [pose proof (tagged_incl sw F Q Et)|];
unfold PSN.incl in *; lia.
Qed.

Lemma res_pos_fit : forall sw F cap Q, 0 < PSN.res_of sw F cap Q -> PSN.kind sw F cap Q = PSN.KFit.
Proof. intros sw F cap Q. unfold PSN.res_of. destruct (PSN.kind sw F cap Q); first [reflexivity | lia]. Qed.

Lemma p_lens : forall cx, Z.of_nat (length (p_C cx)) = p_nF cx.
Proof. intros cx. unfold p_C, p_nF. rewrite length_map. reflexivity. Qed.

Lemma p_reader_keep : forall cx fp W3 (ms ms' : machine_state) lo hi b h buf p,
  p_reader KS cx fp W3 ms b h buf p -> mk W3 (ms_mem ms) (ms_mem ms') lo hi -> alloc_ceiling <= lo ->
  4096 <= pF cx fp -> pF cx fp + PE_FRAME <= alloc_ceiling ->
  0 <= h -> h + SRC_FILE_BLOCK <= alloc_ceiling -> 0 <= b -> b + p_nF cx <= alloc_ceiling ->
  0 <= buf -> buf + p_bn cx <= alloc_ceiling ->
  p_reader KS cx fp W3 ms' b h buf p.
Proof.
intros cx fp W3 ms ms' lo hi b h buf p (Hsrc & (Hpf & Hpsw) & Hfit) H Hlo Hf0 Hf1 Hh0 Hh1 Hb0 Hb1 Hu0 Hu1.
pose proof asan_consts as (C1 & _). unfold PE_FRAME, pPS, pTS, PO_PS, PO_TS, pval in *.
split; [apply (asource_at_keep W3 (ms_mem ms) (ms_mem ms') lo hi _ _ _ _ Hsrc H Hlo); rewrite ?p_lens; lia|].
split; [split; [apply (val_mem_keep W3 _ _ lo hi _ _ _ Hpf H); cbn; lia | apply (val_mem_keep W3 _ _ lo hi _ _ _ Hpsw H); cbn; lia]|].
intros Hk. destruct (Hfit Hk) as (V1 & V2 & V3 & V4 & V5).
destruct (kind_fit _ _ _ _ Hk) as (I1 & I2 & _).
pose proof (p_sizes cx) as (_ & Hcap & _).
assert (HL : Z.of_nat (length (PSN.rec_bytes (p_sw cx) (p_F cx) (p_q cx p))) <= p_bn cx).
{ pose proof (rec_bytes_len (p_sw cx) (p_F cx) (p_q cx p) ltac:(lia)
    ltac:(intros Ht; pose proof (tagged_incl _ _ _ Ht); lia)) as R. unfold p_bn, p_cap in *. lia. }
split; [apply (val_mem_keep W3 _ _ lo hi _ _ _ V1 H); cbn; lia|].
split; [apply (val_mem_keep W3 _ _ lo hi _ _ _ V2 H); cbn; lia|].
split; [apply (val_mem_keep W3 _ _ lo hi _ _ _ V3 H); cbn; lia|].
split; [apply (val_mem_keep W3 _ _ lo hi _ _ _ V4 H); cbn; lia|].
apply (garr8_keep W3 _ _ lo hi _ _ V5 H); rewrite ?length_map; lia.
Qed.

Lemma p_glob_keep : forall cx W3 (ms ms' : machine_state) lo hi src,
  p_glob cx W3 ms src -> mk W3 (ms_mem ms) (ms_mem ms') lo hi -> alloc_ceiling <= lo ->
  p_glob cx W3 ms' src.
Proof.
intros cx W3 ms ms' lo hi src (G1 & G2) H Hlo. pose proof asan_consts as (C1 & _).
pose proof (pa_obj_img 2 ltac:(lia)) as R2. pose proof (pa_obj_img 4 ltac:(lia)) as R4.
unfold pcap_img_end, YImgTop.IMG_TOP in R2, R4. unfold pval in *.
split; [apply (val_mem_keep W3 _ _ lo hi _ _ _ G1 H) | apply (val_mem_keep W3 _ _ lo hi _ _ _ G2 H)];
  change (Z.of_nat 8) with 8; lia.
Qed.

(* The slots stay when the interval misses [s1 + 0x10, s1 + 0x98), or is the slot PS_N alone. *)
Definition slots_apart (cx : ecx) (lo hi : Z) : Prop :=
  hi <= c_sp1 cx + 16 \/ c_sp1 cx + 0x98 <= lo \/ (c_sp1 cx + PS_N <= lo /\ hi <= c_sp1 cx + PS_N + 8).

Lemma pslot_keep_apart : forall cx W3 (ms ms' : machine_state) lo hi off v,
  pslot cx W3 ms off v -> mk W3 (ms_mem ms) (ms_mem ms') lo hi -> slots_apart cx lo hi ->
  0 <= c_sp1 cx -> c_sp1 cx + 0x98 <= 2 ^ 64 ->
  (off = PS_FK \/ off = PS_D \/ off = PS_F \/ off = PS_SH \/ off = PS_VMASK \/ off = PS_BUF12 \/ off = PS_USEC \/
   off = PS_SHB \/ off = PS_FIRST \/ off = PS_TSP \/ off = PS_BUF \/ off = PS_CALLS \/ off = PS_CAP \/ off = PS_F0) ->
  pslot cx W3 ms' off v.
Proof.
intros cx W3 ms ms' lo hi off v Hs H Hap H0 H1 Hoff.
apply (pslot_keep cx W3 ms ms' lo hi off v Hs H);
  unfold slots_apart, PS_FK, PS_D, PS_F, PS_SH, PS_VMASK, PS_BUF12, PS_USEC, PS_SHB, PS_FIRST, PS_TSP, PS_BUF,
    PS_CALLS, PS_CAP, PS_F0, PS_N in *; lia.
Qed.

Lemma pslots_keep : forall cx fp W3 (ms ms' : machine_state) lo hi,
  pslots cx fp W3 ms -> mk W3 (ms_mem ms) (ms_mem ms') lo hi -> slots_apart cx lo hi ->
  0 <= c_sp1 cx -> c_sp1 cx + 0x98 <= 2 ^ 64 -> pslots cx fp W3 ms'.
Proof.
intros cx fp W3 ms ms' lo hi (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) H Hap H0 H1.
repeat split; eapply pslot_keep_apart; eauto 15.
Qed.

Lemma p_lslots_keep : forall cx fp W3 (ms ms' : machine_state) lo hi buf,
  p_lslots cx fp W3 ms buf -> mk W3 (ms_mem ms) (ms_mem ms') lo hi -> slots_apart cx lo hi ->
  0 <= c_sp1 cx -> c_sp1 cx + 0x98 <= 2 ^ 64 -> p_lslots cx fp W3 ms' buf.
Proof.
intros cx fp W3 ms ms' lo hi buf (S0 & S1 & S2 & S3 & S4) H Hap H0 H1.
split; [exact (pslots_keep cx fp W3 ms ms' lo hi S0 H Hap H0 H1)|].
repeat split; eapply pslot_keep_apart; eauto 15.
Qed.

(* ---- the file's bytes, as the reader's stream predicate holds them ---- *)
Lemma asource_at_bytes : forall m f bb C q, asource_at SEGS KS m f bb C q -> garr8 SEGS m bb C.
Proof.
intros m f bb C q (Wn & cpos & fl & md & H). cbv zeta in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & Hgb & _). exact Hgb.
Qed.

Lemma garr8_four : forall m base l i, garr8 SEGS m base l -> 0 <= i -> i + 4 <= Z.of_nat (length l) ->
  garr8 SEGS m (base + i)
    [nth (Z.to_nat i) l 0; nth (Z.to_nat (i + 1)) l 0; nth (Z.to_nat (i + 2)) l 0; nth (Z.to_nat (i + 3)) l 0].
Proof.
intros m base l i Hg Hi Hn j Hj.
assert (R : forall d, 0 <= d -> i + d < Z.of_nat (length l) ->
          val_mem SEGS m (base + i + d) 1 (nth (Z.to_nat (i + d)) l 0) /\ 0 <= nth (Z.to_nat (i + d)) l 0 < 256).
{ intros d Hd Hlt. pose proof (garr8_nthZ SEGS m base l (i + d) Hg ltac:(lia) ltac:(lia)) as [Hv Hr].
  split; [replace (base + i + d) with (base + (i + d)) by lia; exact Hv | exact Hr]. }
cbn [length] in Hj.
destruct j as [|[|[|[|j]]]]; cbn [nth Z.of_nat]; try (exfalso; cbn in Hj; lia).
- rewrite Z.add_0_r. destruct (R 0 ltac:(lia) ltac:(lia)) as [Hv Hr].
  rewrite ?Z.add_0_r in Hv. rewrite ?Z.add_0_r in Hr. split; [exact Hv | exact Hr].
- destruct (R 1 ltac:(lia) ltac:(lia)) as [Hv Hr]. split; [exact Hv | exact Hr].
- destruct (R 2 ltac:(lia) ltac:(lia)) as [Hv Hr]. split; [exact Hv | exact Hr].
- destruct (R 3 ltac:(lia) ltac:(lia)) as [Hv Hr]. split; [exact Hv | exact Hr].
Qed.

Lemma p_C_fb : forall cx i, nth (Z.to_nat i) (p_C cx) 0 = PSN.fb (p_F cx) i.
Proof.
intros cx i. unfold p_C, PSN.fb.
replace 0 with (bv_unsigned (Z_to_bv 8 0)) by reflexivity. apply map_nth.
Qed.

Lemma p_swz_01 : forall cx, p_swz cx = 0 \/ p_swz cx = 1.
Proof.
intros cx. unfold p_swz, PST.pcap_sw. destruct (PST.pcap_magic (p_F cx) =? 0xD4C3B2A1); [right | left]; reflexivity.
Qed.

Lemma trd32_hw : forall cx Q j (sw : word), bv_unsigned sw = p_swz cx ->
  Rd32.trd32_val sw (nth (Z.to_nat (Q + j)) (p_C cx) 0) (nth (Z.to_nat (Q + j + 1)) (p_C cx) 0)
    (nth (Z.to_nat (Q + j + 2)) (p_C cx) 0) (nth (Z.to_nat (Q + j + 3)) (p_C cx) 0) = p_hw cx Q j.
Proof.
intros cx Q j sw Hsw. rewrite !p_C_fb. unfold Rd32.trd32_val, p_hw, PSN.hw, PSN.w32le, p_sw.
assert (Hz : bv_eqb sw (Z_to_bv 64 0) = (p_swz cx =? 0)).
{ destruct (p_swz_01 cx) as [H0 | H1].
  - rewrite H0. cbn [Z.eqb]. apply bv_eqb_eq. apply bv_eq. rewrite Hsw, H0, Z_to_bv_unsigned. reflexivity.
  - rewrite H1. cbn [Z.eqb]. apply Bool.not_true_is_false. intros Hc.
    apply bv_eqb_eq in Hc. rewrite Hc, Z_to_bv_unsigned in Hsw. rewrite H1 in Hsw. discriminate Hsw. }
rewrite Hz. destruct (p_swz_01 cx) as [H0 | H1]; rewrite H0 || rewrite H1; cbn [Z.eqb];
  replace (Q + j + 1) with (Q + (j + 1)) by lia; replace (Q + j + 2) with (Q + (j + 2)) by lia;
  replace (Q + j + 3) with (Q + (j + 3)) by lia; reflexivity.
Qed.

(* ---- the rd32 call, lifted to the harness's journal ---- *)
(* TAKEN FROM: lib/B/Prog/Rd32.v pb_rd32X (trd32_specX at this image), proved on this branch. *)
Lemma rd32_call : forall STK sp0 FP ly S W0 mem md own lyc Sc (W3 : world SEGS) memc mdc k
    (regs : bvmap 5 word) p bb nn c0 c1 c2 c3,
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - Rd32.RD32_FRAME -> spZ regs <= sp0 ->
  In (bb, nn) (ablocks B lyc Sc) -> bb <= p -> p + 4 <= bb + nn ->
  garr8 SEGS (mrestrict (w_H W3) memc) p [c0; c1; c2; c3] ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_rd32)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2' => W2 = W3 /\ exists regs2 mem2 md2,
       c2' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W3 mem2 md2 k /\
       aregs_preserved regs regs2 /\
       getr regs2 10 = w64 (bv_swrap 32 (Rd32.trd32_val (getr regs 11) c0 c1 c2 c3)) /\
       same_but_materialized mdc md2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - Rd32.RD32_FRAME <= a < spZ regs) ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memc a)).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k regs p bb nn c0 c1 c2 c3
  HJ Hraw H10 Hal16 Hwlo Hwhi Hin Hbp Hpn Hgb.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof (ajournal_sub_init SEGS B STK sp0 FP ly S W0 memS md own lyc Sc W3 memc mdc k
  Rd32.RD32_FRAME (spZ regs) [] (spZ regs - sp0) HJi ltac:(lia)
  ltac:(pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & _) & _);
        rewrite Zminus_mod, Hal16, Hal; reflexivity)
  ltac:(lia) ltac:(unfold Rd32.RD32_FRAME; lia) ltac:(lia)) as HJ0.
eapply SRr_mono.
{ exact (Rd32.pb_rd32X SK B LAWS TL Rd32.RD32_FRAME (spZ regs) [] lyc Sc W3 memc mdc []
    lyc Sc W3 memc mdc 0 regs p bb nn c0 c1 c2 c3 HJ0 Hraw H10 Hal16 ltac:(lia) ltac:(lia) Hin Hbp Hpn Hgb). }
cbv beta. intros W2 c2' _ (regs2 & mem2 & md2 & -> & -> & HJ1 & HP & Hres & Hsame & Hfr & _).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split.
{ pose proof (ajournal_gx_callee SK SEGS B LAWS Hsegs pe_G STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k
    Rd32.RD32_FRAME (spZ regs) [] [] lyc Sc W3 mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; destruct Ha as (x & [] & _))) as HJ2.
  rewrite Z.add_0_r in HJ2. cbn [app] in HJ2. exact HJ2. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hsame | exact Hfr].
Qed.

(* ---- the symbolic start of each stretch ---- *)
Definition EBx : sv := SLit 2147450880.                     (* SHADOW_OFF = 0x7fff8000 *)
Definition Espan : Z * Z := (2147450880, 2147450880 + 2 ^ 44 - 1).

Lemma bsigned_w64 : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z H. rewrite signed_is_swrap_unsigned, Z_to_bv_unsigned, swrap_wrap'.
apply swrap64_id. unfold half64. lia.
Qed.

Lemma branch_lt0 : forall (E : env) v z, sv_denot E v = w64 z -> - 2 ^ 63 <= z < 2 ^ 63 ->
  Sem.branch_taken Instr.BC_LT (sv_denot E (SLit 0)) (sv_denot E v) = (0 <? z).
Proof.
intros E v z Hv Hz. cbn [Sem.branch_taken]. unfold bv_lts.
rewrite (denot_lit_U E (SLit 0)), (U_lit E 0 ltac:(lia)), Hv. unfold w64.
rewrite !bsigned_w64 by lia. reflexivity.
Qed.


(* ---- what a stretch keeps, pointwise and across two worlds: memory unchanged outside a set R ----
   mkw W3 W4 m m' R: every byte outside R reads in W4 / m' as it read in W3 / m. A callee's kept clause gives it
   (tclose_kept / nx_kept / acall_kept); mk is the case W4 = W3, R = [lo, hi) (mk_mkw). The _keepw lemmas are the keep
   lemmas above with mk replaced by mkw and each interval side condition by the pointwise one. *)
Definition mkw (W3 W4 : world SEGS) (m m' : word -> option byte) (R : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ R a -> aview SEGS (w_H W4) m' a = aview SEGS (w_H W3) m a.

Lemma mk_mkw : forall W3 m m' lo hi, mk W3 m m' lo hi <-> mkw W3 W3 m m' (fun a => lo <= a < hi).
Proof. intros W3 m m' lo hi. unfold mk, mkw. split; intros H; exact H. Qed.

Lemma mkw_mbyte : forall W3 W4 m m' R a, mkw W3 W4 m m' R -> 0 <= a < 2 ^ 64 -> ~ R a ->
  mbyte SEGS (mrestrict (w_H W4) m') a = mbyte SEGS (mrestrict (w_H W3) m) a.
Proof. intros W3 W4 m m' R a H Ha Hn. apply (mbyte_of_aview SEGS). exact (H a Ha Hn). Qed.

(* An address of an n-byte run outside R, from the run's pointwise condition. *)
Lemma nR_at : forall (R : Z -> Prop) base n x, (forall j, 0 <= j < n -> ~ R (base + j)) -> base <= x < base + n ->
  ~ R x.
Proof. intros R base n x N Hx. replace x with (base + (x - base)) by lia. apply N. lia. Qed.

Lemma rdword_keepw : forall W3 W4 m m' R a v,
  rdword (aview SEGS (w_H W3) m) a = Some v -> mkw W3 W4 m m' R ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (forall j, 0 <= j < 8 -> ~ R (a + j)) ->
  rdword (aview SEGS (w_H W4) m') a = Some v.
Proof.
intros W3 W4 m m' R a v Hw H Ha0 Ha8 Hd. unfold rdword in *.
assert (E : forall j, 0 <= j < 8 -> aview SEGS (w_H W4) m' (a + j) = aview SEGS (w_H W3) m (a + j))
  by (intros j Hj; apply H; [lia | exact (Hd j Hj)]).
pose proof (E 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
rewrite E0, (E 1), (E 2), (E 3), (E 4), (E 5), (E 6), (E 7) by lia.
exact Hw.
Qed.

Lemma pslot_keepw : forall cx W3 W4 (ms ms' : machine_state) R off v,
  pslot cx W3 ms off v -> mkw W3 W4 (ms_mem ms) (ms_mem ms') R ->
  0 <= c_sp1 cx + off -> c_sp1 cx + off + 8 <= 2 ^ 64 -> (forall j, 0 <= j < 8 -> ~ R (c_sp1 cx + off + j)) ->
  pslot cx W4 ms' off v.
Proof.
intros cx W3 W4 ms ms' R off v H Hk H0 H8 Hd. unfold pslot in *.
exact (rdword_keepw W3 W4 _ _ R _ v H Hk H0 H8 Hd).
Qed.

Lemma val_mem_keepw : forall W3 W4 m m' R a n v,
  val_mem SEGS (mrestrict (w_H W3) m) a n v -> mkw W3 W4 m m' R ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall j, 0 <= j < Z.of_nat n -> ~ R (a + j)) ->
  val_mem SEGS (mrestrict (w_H W4) m') a n v.
Proof.
intros W3 W4 m m' R a n v Hv H H0 Hn Hd. eapply BCL.vm_frame; [|exact Hv].
intros x Hx. apply (mkw_mbyte W3 W4 m m' R x H); [lia | apply (nR_at R a (Z.of_nat n)); [exact Hd | lia]].
Qed.

Lemma garr8_keepw : forall W3 W4 m m' R a l,
  garr8 SEGS (mrestrict (w_H W3) m) a l -> mkw W3 W4 m m' R ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (forall j, 0 <= j < Z.of_nat (length l) -> ~ R (a + j)) ->
  garr8 SEGS (mrestrict (w_H W4) m') a l.
Proof.
intros W3 W4 m m' R a l Hg H H0 Hn Hd. apply (garr8_frame SEGS _ _ _ _ Hg).
intros x Hx. apply (mkw_mbyte W3 W4 m m' R x H); [lia | apply (nR_at R a (Z.of_nat (length l))); [exact Hd | lia]].
Qed.

Lemma asource_at_keepw : forall W3 W4 m m' R f b C p,
  asource_at SEGS KS (mrestrict (w_H W3) m) f b C p -> mkw W3 W4 m m' R ->
  (forall j, 0 <= j < SRC_FILE_BLOCK -> ~ R (f + j)) -> (forall j, 0 <= j < Z.of_nat (length C) -> ~ R (b + j)) ->
  (forall a, asrc_env_addr KS a -> ~ R a) ->
  0 <= f -> f + SRC_FILE_BLOCK <= alloc_ceiling -> 0 <= b -> b + Z.of_nat (length C) <= alloc_ceiling ->
  asource_at SEGS KS (mrestrict (w_H W4) m') f b C p.
Proof.
intros W3 W4 m m' R f b C p Hs H Nf Nb Nenv Hf0 Hf1 Hb0 Hb1.
pose proof asan_consts as (C1 & _).
apply (BCL.asource_at_frame KS (mrestrict (w_H W3) m) (mrestrict (w_H W4) m') f b C p); [|exact Hs].
intros a [Ha | [Ha | Ha]].
- apply (mkw_mbyte W3 W4 m m' R a H); [lia | apply (nR_at R f SRC_FILE_BLOCK); [exact Nf | lia]].
- apply (mkw_mbyte W3 W4 m m' R a H); [lia | apply (nR_at R b (Z.of_nat (length C))); [exact Nb | lia]].
- pose proof (env_low a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
  apply (mkw_mbyte W3 W4 m m' R a H); [lia | exact (Nenv a Ha)].
Qed.

Lemma asource_none_keepw : forall W3 W4 m m' R,
  asource_none SEGS KS (mrestrict (w_H W3) m) -> mkw W3 W4 m m' R -> (forall a, asrc_env_addr KS a -> ~ R a) ->
  asource_none SEGS KS (mrestrict (w_H W4) m').
Proof.
intros W3 W4 m m' R Hs H Nenv. pose proof asan_consts as (C1 & _).
apply (BCL.asource_none_frame KS (mrestrict (w_H W3) m) (mrestrict (w_H W4) m')); [|exact Hs].
intros a Ha. pose proof (env_low a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
apply (mkw_mbyte W3 W4 m m' R a H); [lia | exact (Nenv a Ha)].
Qed.

Lemma p_glob_keepw : forall cx W3 W4 (ms ms' : machine_state) R src,
  p_glob cx W3 ms src -> mkw W3 W4 (ms_mem ms) (ms_mem ms') R ->
  (forall j, 0 <= j < 8 -> ~ R (pa_val (A_OBJ 2) + j)) -> (forall j, 0 <= j < 8 -> ~ R (pa_val (A_OBJ 4) + j)) ->
  p_glob cx W4 ms' src.
Proof.
intros cx W3 W4 ms ms' R src (G1 & G2) H N2 N4. pose proof asan_consts as (C1 & _).
pose proof (pa_obj_img 2 ltac:(lia)) as R2. pose proof (pa_obj_img 4 ltac:(lia)) as R4.
unfold pcap_img_end, YImgTop.IMG_TOP in R2, R4. unfold pval in *.
split; [apply (val_mem_keepw W3 W4 _ _ R _ _ _ G1 H) | apply (val_mem_keepw W3 W4 _ _ R _ _ _ G2 H)];
  change (Z.of_nat 8) with 8; first [lia | exact N2 | exact N4].
Qed.

(* The slots stay when no byte of [s1 + 0x10, s1 + 0x98) outside the slot PS_N is in R. *)
Definition slots_apartw (cx : ecx) (R : Z -> Prop) : Prop :=
  forall a, c_sp1 cx + 16 <= a < c_sp1 cx + 0x98 -> ~ (c_sp1 cx + PS_N <= a < c_sp1 cx + PS_N + 8) -> ~ R a.

Lemma pslot_keepw_apart : forall cx W3 W4 (ms ms' : machine_state) R off v,
  pslot cx W3 ms off v -> mkw W3 W4 (ms_mem ms) (ms_mem ms') R -> slots_apartw cx R ->
  0 <= c_sp1 cx -> c_sp1 cx + 0x98 <= 2 ^ 64 ->
  (off = PS_FK \/ off = PS_D \/ off = PS_F \/ off = PS_SH \/ off = PS_VMASK \/ off = PS_BUF12 \/ off = PS_USEC \/
   off = PS_SHB \/ off = PS_FIRST \/ off = PS_TSP \/ off = PS_BUF \/ off = PS_CALLS \/ off = PS_CAP \/ off = PS_F0) ->
  pslot cx W4 ms' off v.
Proof.
intros cx W3 W4 ms ms' R off v Hs H Hap H0 H1 Hoff.
apply (pslot_keepw cx W3 W4 ms ms' R off v Hs H); [| | intros j Hj; apply Hap];
  unfold PS_FK, PS_D, PS_F, PS_SH, PS_VMASK, PS_BUF12, PS_USEC, PS_SHB, PS_FIRST, PS_TSP, PS_BUF,
    PS_CALLS, PS_CAP, PS_F0, PS_N in *; lia.
Qed.

Lemma pslots_keepw : forall cx fp W3 W4 (ms ms' : machine_state) R,
  pslots cx fp W3 ms -> mkw W3 W4 (ms_mem ms) (ms_mem ms') R -> slots_apartw cx R ->
  0 <= c_sp1 cx -> c_sp1 cx + 0x98 <= 2 ^ 64 -> pslots cx fp W4 ms'.
Proof.
intros cx fp W3 W4 ms ms' R (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) H Hap H0 H1.
repeat split; eapply pslot_keepw_apart; eauto 15.
Qed.

Lemma p_lslots_keepw : forall cx fp W3 W4 (ms ms' : machine_state) R buf,
  p_lslots cx fp W3 ms buf -> mkw W3 W4 (ms_mem ms) (ms_mem ms') R -> slots_apartw cx R ->
  0 <= c_sp1 cx -> c_sp1 cx + 0x98 <= 2 ^ 64 -> p_lslots cx fp W4 ms' buf.
Proof.
intros cx fp W3 W4 ms ms' R buf (S0 & S1 & S2 & S3 & S4) H Hap H0 H1.
split; [exact (pslots_keepw cx fp W3 W4 ms ms' R S0 H Hap H0 H1)|].
repeat split; eapply pslot_keepw_apart; eauto 15.
Qed.

(* The reader's footprint: the FILE block h, the copy b, the environment, ps (24 bytes), ts (8 bytes) and the record
   buffer buf. *)
Lemma p_reader_keepw : forall cx fp W3 W4 (ms ms' : machine_state) R b h buf p,
  p_reader KS cx fp W3 ms b h buf p -> mkw W3 W4 (ms_mem ms) (ms_mem ms') R ->
  (forall j, 0 <= j < SRC_FILE_BLOCK -> ~ R (h + j)) -> (forall j, 0 <= j < p_nF cx -> ~ R (b + j)) ->
  (forall a, asrc_env_addr KS a -> ~ R a) ->
  (forall j, 0 <= j < 24 -> ~ R (pPS cx fp + j)) -> (forall j, 0 <= j < 8 -> ~ R (pTS cx fp + j)) ->
  (forall j, 0 <= j < p_bn cx -> ~ R (buf + j)) ->
  4096 <= pF cx fp -> pF cx fp + PE_FRAME <= alloc_ceiling ->
  0 <= h -> h + SRC_FILE_BLOCK <= alloc_ceiling -> 0 <= b -> b + p_nF cx <= alloc_ceiling ->
  0 <= buf -> buf + p_bn cx <= alloc_ceiling ->
  p_reader KS cx fp W4 ms' b h buf p.
Proof.
intros cx fp W3 W4 ms ms' R b h buf p (Hsrc & (Hpf & Hpsw) & Hfit) H Nh Nb Nenv Nps Nts Nbuf
  Hf0 Hf1 Hh0 Hh1 Hb0 Hb1 Hu0 Hu1.
pose proof asan_consts as (C1 & _). unfold PE_FRAME, pPS, pTS, PO_PS, PO_TS, pval in *.
split; [apply (asource_at_keepw W3 W4 (ms_mem ms) (ms_mem ms') R _ _ _ _ Hsrc H); rewrite ?p_lens;
  first [exact Nh | exact Nb | exact Nenv | lia]|].
split; [split; [apply (val_mem_keepw W3 W4 _ _ R _ _ _ Hpf H) | apply (val_mem_keepw W3 W4 _ _ R _ _ _ Hpsw H)];
  cbn; first [lia | intros j Hj; apply (nR_at R (pF cx fp + 32) 24); [exact Nps | lia]]|].
intros Hk. destruct (Hfit Hk) as (V1 & V2 & V3 & V4 & V5).
destruct (kind_fit _ _ _ _ Hk) as (I1 & I2 & _).
pose proof (p_sizes cx) as (_ & Hcap & _).
assert (HL : Z.of_nat (length (PSN.rec_bytes (p_sw cx) (p_F cx) (p_q cx p))) <= p_bn cx).
{ pose proof (rec_bytes_len (p_sw cx) (p_F cx) (p_q cx p) ltac:(lia)
    ltac:(intros Ht; pose proof (tagged_incl _ _ _ Ht); lia)) as RL. unfold p_bn, p_cap in *. lia. }
split; [apply (val_mem_keepw W3 W4 _ _ R _ _ _ V1 H); cbn;
  first [lia | intros j Hj; apply (nR_at R (pF cx fp + 32) 24); [exact Nps | lia]]|].
split; [apply (val_mem_keepw W3 W4 _ _ R _ _ _ V2 H); cbn;
  first [lia | intros j Hj; apply (nR_at R (pF cx fp + 32) 24); [exact Nps | lia]]|].
split; [apply (val_mem_keepw W3 W4 _ _ R _ _ _ V3 H); cbn;
  first [lia | intros j Hj; apply (nR_at R (pF cx fp + 32) 24); [exact Nps | lia]]|].
split; [apply (val_mem_keepw W3 W4 _ _ R _ _ _ V4 H); cbn;
  first [lia | intros j Hj; apply (nR_at R (pF cx fp + 96) 8); [exact Nts | lia]]|].
apply (garr8_keepw W3 W4 _ _ R _ _ V5 H); rewrite ?length_map;
  first [lia | intros j Hj; rewrite ?length_map in Hj; apply (nR_at R buf (p_bn cx)); [exact Nbuf | lia]].
Qed.

(* The memory part of pe_body, pointwise: R misses the saved registers [sp0 - 104, sp0), the frame's header words
   (pF, pF + 8, pF + 16, pF + PE_FLAGPTR), its 16 shadow bytes and the input block. *)
Lemma pe_body_keepw : forall cx fp pc pc' W3 W4 (ms ms' : machine_state) sh R,
  pe_body cx fp pc W3 ms sh ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = getr (ms_regs ms) 2 -> getr (ms_regs ms') 8 = getr (ms_regs ms) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms) 9 -> getr (ms_regs ms') 3 = getr (ms_regs ms) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms) 4 ->
  mkw W3 W4 (ms_mem ms) (ms_mem ms') R ->
  (forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> ~ R a) ->
  (forall a, pF cx fp <= a < pF cx fp + 24 -> ~ R a) ->
  (forall a, pF cx fp + PE_FLAGPTR <= a < pF cx fp + PE_FLAGPTR + 8 -> ~ R a) ->
  (forall a, pSH cx fp <= a < pSH cx fp + 16 -> ~ R a) ->
  (forall a, c_p cx <= a < c_p cx + c_n cx -> ~ R a) ->
  alloc_ceiling + LLVMF_STK <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  4096 <= pF cx fp -> pF cx fp + PE_FRAME <= alloc_ceiling ->
  (c_n cx = 0 \/ (0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)) ->
  pe_body cx fp pc' W4 ms' sh.
Proof.
intros cx fp pc pc' W3 W4 ms ms' sh R
  (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (R2 & R8 & R9 & R3 & R4) & Hsav & Hhd & Hsh & Hlen & Hin)
  Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' E2 E8 E9 E3 E4 H Nsav Nhd Nfl Nsh Ninp Hsp H47 Hf0 Hf1 Hinp.
unfold LLVMF_STK in Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp0 : 0 <= spZ (c_regs cx)) by (unfold spZ; apply bv_unsigned_in_range).
unfold PE_FRAME in Hf1.
split; [exact Hpc'|]. split; [exact Hrv'|]. split; [exact Hsv'|]. split; [exact Hrom'|].
split; [exact Hfr'|]. split; [exact Hfc'|].
split; [unfold pregs; rewrite E2, E8, E9, E3, E4; exact (conj R2 (conj R8 (conj R9 (conj R3 R4))))|].
split.
{ destruct Hsav as [S1 S2]. split.
  - apply (rdword_keepw W3 W4 (ms_mem ms) (ms_mem ms') R _ _ S1 H); [lia | lia | intros j Hj; apply Nsav; lia].
  - intros j Hj. apply (rdword_keepw W3 W4 (ms_mem ms) (ms_mem ms') R _ _ (S2 j Hj) H);
      [lia | lia | intros i Hi; apply Nsav; lia]. }
split.
{ destruct Hhd as (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - apply (rdword_keepw W3 W4 (ms_mem ms) (ms_mem ms') R _ _ H1 H); [lia | lia | intros j Hj; apply Nhd; lia].
  - apply (rdword_keepw W3 W4 (ms_mem ms) (ms_mem ms') R _ _ H2 H); [lia | lia | intros j Hj; apply Nhd; lia].
  - apply (rdword_keepw W3 W4 (ms_mem ms) (ms_mem ms') R _ _ H3 H); [lia | lia | intros j Hj; apply Nhd; lia].
  - apply (rdword_keepw W3 W4 (ms_mem ms) (ms_mem ms') R _ _ H4 H); unfold PE_FLAGPTR in *;
      [lia | lia | intros j Hj; apply Nfl; lia]. }
split.
{ intros i Hi. rewrite (H (pSH cx fp + Z.of_nat i)); [exact (Hsh i Hi)| |].
  - unfold pSH, shadow_of_addr, SHADOW_OFF; rewrite Hlen in Hi; unfold PE_NSH in Hi;
    pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia));
    pose proof (Z.div_le_mono (pF cx fp) alloc_ceiling 8 ltac:(lia) ltac:(lia)); lia.
  - apply Nsh. rewrite Hlen in Hi. unfold PE_NSH in Hi. lia. }
split; [exact Hlen|].
destruct Hinp as [Hn0 | (Hp0 & Hp1)].
- unfold c_n in Hn0. destruct (c_pl cx) as [|x l]; [apply garr8_nil | cbn in Hn0; lia].
- apply (garr8_keepw W3 W4 (ms_mem ms) (ms_mem ms') R _ _ Hin H); unfold c_n in *; rewrite ?length_map;
    [lia | lia | intros j Hj; rewrite ?length_map in Hj; apply Ninp; lia].
Qed.

(* ---- a block just allocated is not among the blocks before it ---- *)
Lemma block_fresh : forall ly S (W : world SEGS) mem md L bb nn,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (L ++ [(bb, nn)]) -> ~ In (bb, nn) L.
Proof.
intros ly S W mem md L bb nn HAR HP Hin.
assert (Hin0 : In (bb, nn) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md bb nn HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
assert (Hpos : forall b, In b (ablocks B ly S) -> 1 <= req_size (snd b)).
{ intros [p n] Hb. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn).
  exact (proj1 (req_size_pos n ltac:(lia))). }
assert (Gen : forall l, (forall b, In b l -> 1 <= req_size (snd b)) ->
          pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l).
{ induction l as [|x t IH]; intros Hp Hw; [constructor|].
  cbn [map pairwise] in Hw. destruct Hw as [Hx Ht]. constructor.
  - intros Hxt. rewrite Forall_forall in Hx.
    specialize (Hx _ (in_map (fun b => (fst b, req_size (snd b))) t x Hxt)).
    pose proof (Hp x (or_introl eq_refl)) as Hx1. unfold zdisjoint in Hx. cbn [fst snd] in Hx. lia.
  - apply IH; [intros b Hb; apply Hp; right; exact Hb | exact Ht]. }
pose proof (Permutation_NoDup HP (Gen _ Hpos Hpw)) as HND.
pose proof (NoDup_remove_2 L [] (bb, nn) HND) as Hn. rewrite app_nil_r in Hn. exact (Hn Hin).
Qed.

(* ---- a symbolic run whose regions all have an empty write window changes no byte ---- *)
Lemma no_write_run_mem : forall (E : env) (rs : smem) (m m' : word -> option byte),
  frame_of E rs m m' -> (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> m' = m.
Proof.
intros E rs m m' HF Hw. apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality. intros x.
apply HF. intros (r & Hin & Hr). pose proof (Hw r Hin) as Hr2. lia.
Qed.

(* ---- the allocator calls, lifted to the harness's journal ---- *)
(* lib/A/Prog/PaJournalFs.v amalloc04_sub_fs under ajournal_gx pe_G 0 []: the gx journal opened to its inner ajournal
   (start memory memS), the rule applied to it, and the result repacked with the same memS (ajournal_gx_pack). *)
Lemma amalloc_call : forall (HM : amalloc04_rule SEGS B MT)
    W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n (o : Z) raw ch,
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B) ->
  mo_ok MT Sc (mo_malloc MT n) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
     4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
     acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
     mo_le MT Sc S2 (mo_malloc MT n) /\
     m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
Proof.
intros HM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k n o raw ch HJ Ha0 Hn Hlive Hsp Ho16 Ho Hstk
  Hgp Htp Hra Hraw Hnev Hch HU MOK.
destruct HJ as (H0 & H1 & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
eapply SRr_mono.
{ exact (amalloc04_sub_fs SK SEGS B LAWS pa_segs_low MT HM W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc k
           n o raw ch HJi Ha0 Hn Hlive Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Ec & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & MLE &
  Efd & Efs).
exists ly2, S2, regs2, mem2, md2, res. split; [exact Ec|].
split.
{ eapply ajournal_gx_pack; [exact H0 | exact H1 | | exact Hag | intros a Ha _; lia].
  rewrite !Z.add_0_r. exact HJ2. }
repeat (split; [assumption|]). assumption.
Qed.

(* lib/A/Prog/PaJournalFs.v afree04_sub_fs under ajournal_gx pe_G 0 [], as amalloc_call. *)
Lemma afree_call : forall (HF : afree04_rule SEGS B MT)
    W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (pa, n) (ablocks B lyc Sc) ->
  getr regsT 10 = w64 pa ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
  In (call_trace0 (pc_free_ra0 (as_code B)) regsT ch) (as_universe B) ->
  (In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
  mo_ok MT Sc (mo_free MT) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
     aregs_preserved regsT regs2 /\
     (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
     frames S2 = frames Sc /\
     acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
     mo_le MT Sc S2 (mo_free MT) /\
     m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
Proof.
intros HF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch HJ Hin Ha0 Hsp Ho16 Ho Hstk Hgp Htp
  Hra Hraw Hnev Hch HU Hcov MOK.
destruct HJ as (H0 & H1 & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
eapply SRr_mono.
{ exact (afree04_sub_fs SK SEGS B LAWS pa_segs_low MT HF W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc k
           pa n o raw ch HJi Hin Ha0 Hsp Ho16 Ho Hstk Hgp Htp Hra Hraw Hnev Hch HU Hcov MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HP & Hbl & Hfr & HK & MLE & Efd & Efs).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|].
split.
{ eapply ajournal_gx_pack; [exact H0 | exact H1 | | exact Hag | intros a Ha _; lia].
  rewrite !Z.add_0_r. exact HJ2. }
repeat (split; [assumption|]). assumption.
Qed.

End c.
End b.
End a.
