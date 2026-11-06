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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapEntrySkip.v, with its module paths and module names changed; 2897 of its 3032 lines of code are new or changed and 2297 lines of the source are left out. *)
(* lib/B walk of fuzz_pcap's entry function LLVMFuzzerTestOneInput (0x80818, asan-ubsan build of libreac v1.9.0), phase
   L4, the record checks: the cuts PP_KO -> PP_KT1 -> PP_KT2 -> PP_KL2 -> PP_K4 / PP_K5 of lib/B/Prog/PcapEntryDefs.v,
   at the waypoint invariants GI_* of lib/B/Prog/PcapEntryPhases.v. Every number is read from the pin
   fuzz_pcap.asan-ubsan (sha256 9e66f771f22af67a...; capstone disassembly of the unstripped twin,
   llvmf-au.dis (sha256 be945029c797; internal record)).

   The stretches (each a pe_from cut lemma, `pe_from GI_next -> pe_from GI_self`):
   - KO  0x80bfc -> 0x80d5c: the orig_len test (`bne s6,a0` 0x80bfc), the VLAN tag (incl >= 18, 0x80c08; the bytes at
         rec + 28, rec + 29 behind their shadow checks 0x80c1c / 0x80c48), the tag test against ps.last_vlan_tagged
         (0x80c6c), then on the tagged arm the length test (0x80c84), bcmp(buf, data, 12) (0x80c94), bcmp(buf + 12,
         data + 16, incl - 16) (0x80cc4) and the VLAN id (rec + 30, rec + 31 behind their shadow checks 0x80ce4, 0x80d04;
         the test 0x80d24), on the untagged arm the length test (0x80d30) and bcmp(buf, data, n) (0x80d40); then ts is
         loaded (0x80d4c) and rd32(rec, swapped) (0x80d58) returns at PP_KT1;
   - KT1 0x80d5c -> 0x80d80: the guard 0x80d60 (wrap(rec + 4)), sec * 10^6 (mulhu 0x80d74), rd32(rec + 4, swapped)
         (0x80d7c) returns at PP_KT2;
   - KT2 0x80d80 -> 0x80dbc: the timestamp test (0x80d8c), ts := ~0 (0x80d98), at := at + 16 + incl (0x80da8), and
         pcap_source_next(&ps, buf, cap, &ts) (0x80db8) returns at PP_KL2;
   - KL2 0x80dbc -> 0x80b40 / 0x80e0c: n is stored (0x80dc8) and `bgtz` (0x80dcc) goes back to the loop head PP_K4,
         else `j` (0x80dd0) to the join PP_K5.
   Each open cut is stated as a Definition `<name>_stmt` and proved in turn as the Lemma `<name>`. The cuts of the
   record loop also have measured forms `<name>_m` (PcapEntrySkip.pe_meas, a bound on |F| - s10), and pe_recloop
   (at the end) closes the loop PP_K4 -> ... -> PP_KL2 -> PP_K4 by induction on that bound. *)
From OSSVerify.libreac.fuzz_pcap Require Symbols.
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

From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntryKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceNextSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapEntryCalls.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapEntrySkip.
Module ANX := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceNextSpec.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* ---- the cut statements ---- *)

(* PP_KO -> PP_KT1: the record's checks and the rd32 of the seconds. *)
Definition pe_from_KO_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_KT1 B MT KS) -> pe_from SK B MT KS POST (GI_KO B MT KS).

(* PP_KT1 -> PP_KT2: the guard on rec + 4 and the rd32 of the microseconds. *)
Definition pe_from_KT1_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_KT2 B MT KS) -> pe_from SK B MT KS POST (GI_KT1 B MT KS).

(* PP_KT2 -> PP_KL2: the timestamp test, ts := ~0, the new position and the loop's pcap_source_next. *)
Definition pe_from_KT2_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_KL2 B MT KS) -> pe_from SK B MT KS POST (GI_KT2 B MT KS).

(* PP_KL2 -> PP_K4 (n > 0, the back edge 0x80dcc) / PP_K5 (n <= 0, j 0x80dd0). *)
Definition pe_from_KL2_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K4 B MT KS) -> pe_from SK B MT KS POST (GI_K5 B MT KS) ->
  pe_from SK B MT KS POST (GI_KL2 B MT KS).


(* ---- the walk's Section hypotheses ---- *)
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.

(* PP_KL2 0x80dbc: the slots region [s1 + 0x10, s1 + 0x98) with PS_FIRST's word, written at PS_N. *)
Definition kl2_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 16 152 112 120 [YP09.mkChunk PS_FIRST (CVal 8 (SOff 32 0))].
Definition kl2_regions : smem := [kl2_region].
Definition kl2_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition ss_kl2 : sstate := mkSS PP_KL2 sr_atoms kl2_regions None kl2_facts.
Definition kl2_extra (first : Z) : list word := [w64 first].

Lemma kl2_entry : forall cx (W3 : world SEGS) (ms3 : machine_state) first,
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) ->
  ms_pc_val ms3 = w64 (BASE + PP_KL2) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  2 ^ 46 <= c_sp1 cx <= 2 ^ 47 -> c_sp1 cx mod 32 = 0 ->
  (forall a, c_sp1 cx + 112 <= a < c_sp1 cx + 120 -> apresent (w_H W3) (ms_mem ms3) a) ->
  0 <= first < 2 ^ 64 ->
  pslot cx W3 ms3 PS_FIRST first ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) (kl2_extra first))) ss_kl2 (restrict (w_H W3) ms3) /\
  sh_ok SEGS EBx [] (Eimg (Ereg (ms_regs ms3) (kl2_extra first))) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx W3 ms3 first H9 Hpc Hrv Hsv Hrom Hfr Hfc Hsp Hal Hpres Hfirst Hsl.
set (E := Eimg (Ereg (ms_regs ms3) (kl2_extra first))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (kl2_extra first)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = w64 first) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
split.
- assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KL2)) (ms_mem ms3) (seg_rom SEGS)).
  { destruct ms3; cbn in *; unfold mkst; subst; f_equal; assumption. }
  rewrite Hms, restrict_mkst_fx. unfold ss_kl2. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold kl2_regions, kl2_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. fold E. rewrite U9.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_FIRST 8 (SOff 32 0) first);
      [cbn [sv_denot]; rewrite E32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hsl).
  + cbn [pairwise_disjoint all_disjoint kl2_regions]. tauto.
  + split; [|split; [exact I | exact I]].
    cbn [kl2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite U9, E32, unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply Forall_nil.
Qed.

(* ---- the record loop's measure: the reader's answer never moves backwards ---- *)
Lemma chain_ge : forall sw F cap fuel q lh, q <= fst (fst (PSN.chain sw F cap fuel q lh)).
Proof.
intros sw F cap fuel. induction fuel as [|f IH]; intros q lh; [cbn; lia|].
cbn [PSN.chain]. pose proof (PcapEntryKit.hw_range sw F q 8) as Hr. unfold PSN.incl in *.
destruct (PSN.kind sw F cap q) eqn:Ek; try (cbn; lia).
- pose proof (IH (q + 16) lh) as H. lia.
- pose proof (IH (q + 16 + PSN.hw sw F q 8) (Some q)) as H.
  destruct (PSN.chain sw F cap f (q + 16 + PSN.hw sw F q 8) (Some q)) as [[Q o] l].
  cbn [fst] in H |- *. lia.
Qed.

Lemma p_le_q : forall cx p, p <= p_q cx p.
Proof.
intros cx p. unfold p_q, PSN.psn_q, PSN.psn_chain. apply chain_ge.
Qed.

(* The measured form, for the lane that closes the record loop: s10 = p is the same at PP_KL2 and at PP_K4, so the
   bound m on |F| - s10 passes through unchanged (the turn's decrease happens in the KT2 stretch, at 0x80da8). *)
Lemma pe_from_KL2_m : forall m POST,
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_K4 B MT KS) m) ->
  pe_from SK B MT KS POST (GI_K5 B MT KS) ->
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_KL2 B MT KS) m).
Proof.
intros m POST HK4 HK5.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo (HI & HM).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct (PcapEntryKit.rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HI as (b & h & buf & j & p & Hcut & Hn26 & Hgood & Hj1 & Hjp & HpF & R10 & R18 & R20 & R21 & R23 & R24 & R26
  & Hls & Hcalls & Hfirst & Hglob & Hrd).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
(* the blocks of the cut: the copy, the FILE and the buffer are live, so each lies under the ceiling *)
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hu3 : In (buf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096 & Hbceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR Hh3) as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 buf (p_bn cx) HAR Hu3) as (_ & Hu4096 & Huceil & _).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as [_ Hrq2].
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hrq3].
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
unfold LLVMF_STK in Hspc, Hpres.
assert (Hs1 : 2 ^ 46 <= c_sp1 cx <= 2 ^ 47) by lia.
(* the start state *)
destruct (kl2_entry cx W3 ms3 (p_first cx mod 2 ^ 64) Rs1 Hpc Hrv Hsv Hrom Hfreg Hfcsr Hs1 Hal32
  ltac:(intros a Ha; apply Hpres; lia)
  ltac:(pose proof (Z.mod_pos_bound (p_first cx) (2 ^ 64) ltac:(lia)); lia)
  Hfirst) as [HS SHOK].

remember (Eimg (Ereg (ms_regs ms3) (kl2_extra (p_first cx mod 2 ^ 64)))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat ->
  ew E i = ew (Ereg (ms_regs ms3) (kl2_extra (p_first cx mod 2 ^ 64))) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = w64 (p_first cx mod 2 ^ 64))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (kl2_extra (p_first cx mod 2 ^ 64))) E)
  by (split; [intros i Hi; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HEdef.
pose proof (PcapEntryKit.bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (PcapEntryKit.bpaj_run_to_x B LAWS pe_G HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_tok RUN HS HJ SHOK Espan;
  [ apply awr_ok_x_of0; unfold ss_kl2, kl2_regions, kl2_region; cbn [ss_mem];
    eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil] |].

pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_sp1 cx + 112 <= a < c_sp1 cx + 120) HFr
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia|]);
        destruct Hin)) as UN1'.
assert (UN1 : mk W3 (ms_mem ms3) (ms_mem ms) (c_sp1 cx + 112) (c_sp1 cx + 120))
  by (intros a Ha Hn; apply UN1'; [exact Ha | exact Hn]).
clear UN1' HF HFr HG.
assert (D10 : sv_denot E (SOff 10 0) = w64 (p_res cx (p_q cx p)))
  by (cbn [sv_denot]; rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10;
      unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
pose proof (res_range (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p)) as Hres0.
unfold p_res, p_kind in *.
psrr_branch_tok RUN BR HS SHOK Espan.
- (* n > 0: the back edge to PP_K4 *)
  rewrite (branch_lt0 E (SOff 10 0) _ D10 ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Espan PP_K4;
    [ apply awr_ok_x_of0; cbn [ss_mem];
      eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia
      | cbn [YP09.r_whi]; lia | apply awr_ok_nil] |].

  repeat rewrite wvb_collapse in HJ.
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_sp1 cx + 112 <= a < c_sp1 cx + 120) HFr
    ltac:(intros bb wlo whi aa Hin HRr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in HRr; rewrite ?U9 in HRr; lia|]);
          destruct Hin)) as UN2'.
  assert (UN : mk W3 (ms_mem ms3) (ms_mem ms0) (c_sp1 cx + 112) (c_sp1 cx + 120))
    by (apply (mk_trans W3 _ (ms_mem ms) _ _ _ UN1); intros a Ha Hn; apply UN2'; [exact Ha | exact Hn]).
  clear UN1 UN2' HF HFr HG.
  assert (Hap : slots_apart cx (c_sp1 cx + 112) (c_sp1 cx + 120))
    by (unfold slots_apart, PS_N; lia).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (13%bv : bv 5) Q13.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
  rewrite E32 in Q13.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q20.
  rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in Q21.
  rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23 in Q23.
  rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in Q24.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in Q26.
  (* the value the store left in PS_N *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict mkst] in HR0 end.
  pose proof (field_of_region E _ 9%nat (c_sp1 cx) _ _ _ _ _ 112 8%N (SOff 10 0)
    (PSN.res_of (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p)) HR0 U9 ltac:(cbn; tauto) D10
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VN.
  change (N.to_nat 8) with 8%nat in VN.
  (* the target cut *)
  apply (HK4 cx fp k acc ly3 S3 W3 _ _ HB HJ Hfr Hmo).
  pmkst HS.
  split; [| cbn [ms_regs mkst]; rewrite Q26; rewrite R26 in HM; exact HM ].
  exists b, h, buf, j, p.
  assert (Hfit : PSN.kind (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) = PSN.KFit)
    by (apply res_pos_fit; lia).
  split.
  { split.
    { eapply (pe_body_keep cx fp PP_KL2 PP_K4 W3 ms3 _ PSH_ts (c_sp1 cx + 112) (c_sp1 cx + 120) Hbody);
      try reflexivity; try (cbn [ms_regs mkst]; first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9]);
      [ cbn [ms_mem mkst]; exact UN | lia | lia | unfold LLVMF_STK; lia | lia | exact Hf0 | exact Hf1 | exact Hinp ]. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)); exact Hfds
           | repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hgood|].
  split; [lia|]. split; [lia|]. split; [exact Hfit|].
  split; [right; split; [lia | cbn [ms_regs mkst]; rewrite Q13; apply w64_mod64]|].
  split; [cbn [ms_regs mkst]; exact Q18|]. split; [cbn [ms_regs mkst]; exact Q20|].
  split; [cbn [ms_regs mkst]; exact Q21|]. split; [cbn [ms_regs mkst]; exact Q23|].
  split; [cbn [ms_regs mkst]; exact Q24|]. split; [cbn [ms_regs mkst]; exact Q26|].
  split; [cbn [ms_mem mkst]; exact (p_lslots_keep cx fp W3 ms3 _ _ _ buf Hls UN Hap ltac:(lia) ltac:(lia))|].
  split; [cbn [ms_mem mkst]; exact (pslot_keep_apart cx W3 ms3 _ _ _ _ _ Hcalls UN Hap ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst]; unfold pslot, PS_N;
          exact (rdword_of_val_mem SEGS (w_H W3) _ _ _ VN ltac:(lia))|].
  split; [cbn [ms_mem mkst]; exact (p_glob_keep cx W3 ms3 _ _ _ b Hglob UN ltac:(lia))|].
  cbn [ms_mem mkst].
  exact (PcapEntryKit.p_reader_keep B KS ASIL cx fp W3 ms3 _ _ _ b h buf p Hrd UN ltac:(lia) Hf0 Hf1
           ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
- (* n <= 0: the join PP_K5 *)
  rewrite (branch_lt0 E (SOff 10 0) _ D10 ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Espan PP_K5;
    [ apply awr_ok_x_of0; cbn [ss_mem];
      eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia
      | cbn [YP09.r_whi]; lia | apply awr_ok_nil] |].
  repeat rewrite wvb_collapse in HJ.
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_sp1 cx + 112 <= a < c_sp1 cx + 120) HFr
    ltac:(intros bb wlo whi aa Hin HRr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in HRr; rewrite ?U9 in HRr; lia|]);
          destruct Hin)) as UN2'.
  assert (UN : mk W3 (ms_mem ms3) (ms_mem ms0) (c_sp1 cx + 112) (c_sp1 cx + 120))
    by (apply (mk_trans W3 _ (ms_mem ms) _ _ _ UN1); intros a Ha Hn; apply UN2'; [exact Ha | exact Hn]).
  clear UN1 UN2' HF HFr HG.
  assert (Hap : slots_apart cx (c_sp1 cx + 112) (c_sp1 cx + 120)) by (unfold slots_apart, PS_N; lia).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
  prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
  rewrite E32 in Q10.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q20.
  rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in Q24.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in Q26.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict mkst] in HR0 end.
  pose proof (Z.mod_pos_bound (PSN.res_of (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p)) (2 ^ 64) ltac:(lia)) as Hmod.
  pose proof (field_of_region E _ 9%nat (c_sp1 cx) _ _ _ _ _ 112 8%N (SOff 10 0)
    (PSN.res_of (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) mod 2 ^ 64) HR0 U9 ltac:(cbn; tauto)
    ltac:(rewrite D10; symmetry; apply w64_mod64)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VN.
  change (N.to_nat 8) with 8%nat in VN.
  apply (HK5 cx fp k acc ly3 S3 W3 _ _ HB HJ Hfr Hmo).
  pmkst HS.
  exists b, h, buf, p.
  assert (Hnfit : PSN.kind (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) <> PSN.KFit)
    by (intros Hk0; pose proof (res_fit_pos _ _ _ _ Hk0); lia).
  split.
  { split.
    { eapply (pe_body_keep cx fp PP_KL2 PP_K5 W3 ms3 _ PSH_ts (c_sp1 cx + 112) (c_sp1 cx + 120) Hbody);
      try reflexivity; try (cbn [ms_regs mkst]; first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9]);
      [ cbn [ms_mem mkst]; exact UN | lia | lia | unfold LLVMF_STK; lia | lia | exact Hf0 | exact Hf1 | exact Hinp ]. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)); exact Hfds
           | repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hgood|].
  split; [lia|]. split; [exact Hnfit|].
  split; [cbn [ms_regs mkst]; rewrite Q10; apply w64_mod64|].
  split; [cbn [ms_regs mkst]; exact Q18|]. split; [cbn [ms_regs mkst]; exact Q20|].
  split; [cbn [ms_regs mkst]; exact Q24|]. split; [cbn [ms_regs mkst]; exact Q26|].
  split; [cbn [ms_mem mkst]; exact (pslots_keep cx fp W3 ms3 _ _ _ (proj1 Hls) UN Hap ltac:(lia) ltac:(lia))|].
  split; [cbn [ms_mem mkst];
          exact (pslot_keep_apart cx W3 ms3 _ _ _ _ _ (proj1 (proj2 Hls)) UN Hap ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst]; unfold pslot, PS_N;
          exact (rdword_of_val_mem SEGS (w_H W3) _ _ _ VN ltac:(lia))|].
  split; [cbn [ms_mem mkst]; exact (p_glob_keep cx W3 ms3 _ _ _ b Hglob UN ltac:(lia))|].
  cbn [ms_mem mkst].
  exact (PcapEntryKit.p_reader_keep B KS ASIL cx fp W3 ms3 _ _ _ b h buf p Hrd UN ltac:(lia) Hf0 Hf1
           ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma pe_from_KL2 : pe_from_KL2_stmt.
Proof.
unfold pe_from_KL2_stmt. intros POST HK4 HK5.
apply (PcapEntrySkip.pe_from_meas_all B MT KS POST). intros m.
apply (pe_from_KL2_m m POST); [apply (PcapEntrySkip.pe_meas_of B MT KS POST); exact HK4 | exact HK5].
Qed.



(* PP_KT1 0x80d5c: the slots (PS_USEC is read at 0x80d70) and `ps` (ps.swapped at 0x80d64); nothing is written. *)
Definition kt1_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 16 152 0 0 [YP09.mkChunk PS_USEC (CVal 8 (SLit (1000000 * 2 ^ 32)))];
   YP09.mkRegion (Some 20%nat) 0 24 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))]].
Definition kt1_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF 0 (2 ^ 47) 0);
           (20%nat, mkAF 4096 (2 ^ 47) 3); (10%nat, mkAF 0 (2 ^ 64 - 1) 0);
           (32%nat, mkAF 0 1 0)] [] [].
Definition ss_kt1 : sstate := mkSS PP_KT1 sr_atoms kt1_regions None kt1_facts.
Definition kt1_extra (swz : Z) : list word := [w64 swz].

Lemma kt1_entry : forall cx (W3 : world SEGS) (ms3 : machine_state) s3v psv swz,
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) -> getr (ms_regs ms3) 19 = w64 s3v ->
  getr (ms_regs ms3) 20 = w64 psv ->
  ms_pc_val ms3 = w64 (BASE + PP_KT1) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  2 ^ 46 <= c_sp1 cx <= 2 ^ 47 -> c_sp1 cx mod 32 = 0 ->
  0 <= s3v <= 2 ^ 47 -> 4096 <= psv <= 2 ^ 47 -> psv mod 8 = 0 -> psv + 24 <= c_sp1 cx + 16 ->
  pslot cx W3 ms3 PS_USEC (1000000 * 2 ^ 32) ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (psv + 8) 4 swz -> 0 <= swz <= 1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) (kt1_extra swz))) ss_kt1 (restrict (w_H W3) ms3) /\
  sh_ok SEGS EBx [] (Eimg (Ereg (ms_regs ms3) (kt1_extra swz))) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx W3 ms3 s3v psv swz H9 H19 H20 Hpc Hrv Hsv Hrom Hfr Hfc Hsp Hal Hs3 Hps Hps8 Hdis Hslot Hsw Hswr.
set (E := Eimg (Ereg (ms_regs ms3) (kt1_extra swz))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (kt1_extra swz)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), H9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = s3v)
  by (rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), H19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = psv)
  by (rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), H20; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 swz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (U32 : bv_unsigned (ew E 32) = swz) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U10r : 0 <= bv_unsigned (ew E 10) <= 2 ^ 64 - 1).
{ pose proof (bv_unsigned_in_range 64 (ew E 10)) as Hq. unfold bv_modulus in Hq.
  change (Z.of_N 64) with 64 in Hq. lia. }
split; [|apply Forall_nil].
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KT1)) (ms_mem ms3) (seg_rom SEGS))
  by (destruct ms3; cbn in *; unfold mkst; subst; f_equal; assumption).
rewrite Hms, restrict_mkst_fx. unfold ss_kt1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold kt1_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; cbn [base_val]; fold E.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_USEC 8 (SLit (1000000 * 2 ^ 32)) (1000000 * 2 ^ 32));
      [reflexivity | zside | zside |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hslot).
  + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ psv 8 4 (SOff 32 0) swz);
      [cbn [sv_denot]; rewrite E32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside | exact Hsw].
- apply pairwise_disjoint_of_extents.
  unfold kt1_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  cbn [base_val]. fold E. rewrite U9, U20.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [kt1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite U9, U19, U20, U32.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* The microsecond scale: mulhu(a0 << 32, 10^6 * 2^32) = sec * 10^6 (0x80d6c, 0x80d70, 0x80d74). *)
Lemma mulhu_usec : forall (E : env) hw, ew E 10 = w64 (bv_swrap 32 hw) -> 0 <= hw < 2 ^ 32 ->
  U E (SMd Instr.M_MULHU (SAlu Instr.ALU_SLL (SOff 10 0) (SLit 32)) (SLit 4294967296000000))
  = hw * 1000000.
Proof.
intros E hw Hew Hhw.
assert (Hu : bv_unsigned (ew E 10) mod 2 ^ 32 = hw).
{ rewrite Hew. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 32) with 4294967296. change (2 ^ 32) with 4294967296 in Hhw. lia. }
pose proof (bv_unsigned_in_range 64 (ew E 10)) as Hur. unfold bv_modulus in Hur.
change (Z.of_N 64) with 64 in Hur.
rewrite U_SMd, U_SAlu, !U_SLit, U_SOff. cbn [zalu_raw zmd_raw].
rewrite (zcanon_id 32) by (unfold M64; lia). rewrite (zcanon_id 4294967296000000) by (unfold M64; lia).
change (Z.land 32 63) with 32. rewrite Z.add_0_r.
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
assert (Hc : zcanon (bv_unsigned (ew E 10)) = bv_unsigned (ew E 10)) by (apply zcanon_id; unfold M64; lia).
rewrite Hc.
assert (Hm : zcanon (bv_unsigned (ew E 10) * 2 ^ 32) = hw * 2 ^ 32).
{ unfold zcanon, M64. replace (bv_unsigned (ew E 10) * 2 ^ 32) with (2 ^ 32 * bv_unsigned (ew E 10)) by lia.
  replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity.
  rewrite Z.mul_mod_distr_l by lia. rewrite Hu. lia. }
rewrite Hm.
replace (hw * 2 ^ 32 * 4294967296000000) with (hw * 1000000 * 2 ^ 64) by lia.
rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* The measured form: s10 = Q at PP_KT1 and at PP_KT2, so the bound m on |F| - s10 passes through unchanged. *)
Lemma pe_from_KT1_m : forall m POST,
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_KT2 B MT KS) m) ->
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_KT1 B MT KS) m).
Proof.
intros m POST HKT2.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo (HI & HM).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct (PcapEntryKit.rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
cbv zeta in HI.
destruct HI as (b & h & buf & i & p & Hcut & Hn26 & Hgood & Hi0 & Hip & HpQ & Hfit & R10 & R18 & R19 & R20 & R21
  & R22 & R23 & R24 & R26 & R27 & Hls & Hcalls & Hfirst & Hglob & Hrd).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hu3 : In (buf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096 & Hbceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR Hh3) as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 buf (p_bn cx) HAR Hu3) as (_ & Hu4096 & Huceil & _).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hrq3].
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
unfold LLVMF_STK in Hspc, Hpres.
assert (Hs1 : 2 ^ 46 <= c_sp1 cx <= 2 ^ 47) by lia.
destruct (kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) Hfit) as (Hi1 & Hi2 & Hi3 & Hi4).
assert (HQ0 : 0 <= p_q cx p) by lia.
assert (HQF : p_q cx p + 16 <= p_nF cx) by (unfold p_nF; lia).
destruct Hrd as (Hsrc & (Hpsf & Hpsw) & Hfitc).
pose proof (PcapEntryKit.asource_at_bytes KS _ _ _ _ _ Hsrc) as Hbytes.
assert (Hfr1 : pF cx fp + 128 <= alloc_ceiling) by (unfold PE_FRAME in Hf1; lia).
assert (Hps8 : pPS cx fp mod 8 = 0).
{ unfold pPS, PO_PS. apply mod64_mod8. exact Hf64. }
destruct (kt1_entry cx W3 ms3 (b + p_q cx p) (pPS cx fp) (p_swz cx) Rs1 R19 R20 Hpc Hrv Hsv Hrom Hfreg Hfcsr
  Hs1 Hal32 ltac:(lia) ltac:(unfold pPS, PO_PS; lia) Hps8 ltac:(unfold pPS, PO_PS; lia)
  (proj2 (proj2 (proj2 (proj2 Hls)))) Hpsw
  ltac:(pose proof (PcapEntryKit.p_swz_01 cx); lia)) as [HS SHOK].
remember (Eimg (Ereg (ms_regs ms3) (kt1_extra (p_swz cx)))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i0, (i0 < A_TEXT)%nat -> ew E i0 = ew (Ereg (ms_regs ms3) (kt1_extra (p_swz cx))) i0)
  by (intros i0 Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i0 (r : bv 5), (i0 < A_TEXT)%nat -> Z.of_nat i0 = bv_unsigned r -> ew E i0 = getr (ms_regs ms3) r)
  by (intros i0 r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i0 r Hr)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
clear HEdef.
pose proof (PcapEntryKit.bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (PcapEntryKit.bpaj_run_to_x B LAWS pe_G HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_tok RUN HS HJ SHOK Espan;
  [ apply awr_ok_x_of0; unfold ss_kt1, kt1_regions; cbn [ss_mem];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]; apply awr_ok_nil |].
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_sp1 cx - 16 <= a < c_sp1 cx) HFr
    ltac:(intros bb0 wlo whi aa Hin HRr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in HRr; lia|]);
          destruct Hin)) as UN1'.
  assert (UN1 : mk W3 (ms_mem ms3) (ms_mem ms) (c_sp1 cx - 16) (c_sp1 cx))
    by (intros a Ha Hn; apply UN1'; [exact Ha | exact Hn]).
  clear UN1' HF HFr HG.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  assert (EWm : forall i0 (r : bv 5), (i0 < A_TEXT)%nat -> Z.of_nat i0 = bv_unsigned r ->
            ew E i0 = getr (ms_regs ms3) r) by exact EW.
  rewrite (EWm 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in Q2.
  rewrite (EWm 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EWm 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EWm 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EWm 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1 in Q9.
  rewrite (EWm 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
  rewrite (EWm 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q20.
  rewrite (EWm 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in Q21.
  rewrite (EWm 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl), R22 in Q22.
  rewrite (EWm 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23 in Q23.
  rewrite (EWm 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in Q24.
  rewrite (EWm 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in Q26.
  rewrite (EWm 27%nat 27%bv ltac:(unfold A_TEXT; lia) eq_refl), R27 in Q27.
  assert (E10v : ew E 10 = w64 (bv_swrap 32 (p_hw cx (p_q cx p) 0)))
    by (rewrite (EWm 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R10).
  assert (HD : sv_denot E (SMd Instr.M_MULHU (SAlu Instr.ALU_SLL (SOff 10 0) (SLit 32))
                 (SLit 4294967296000000)) = w64 (p_hw cx (p_q cx p) 0 * 1000000))
    by (rewrite (denot_lit_U E _), (mulhu_usec E (p_hw cx (p_q cx p) 0) E10v (hw_range _ _ _ _)); reflexivity).
  cbn [sv_denot] in HD. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in HD. rewrite HD in Q25.
  assert (E19v : bv_unsigned (ew E 19) = b + p_q cx p)
    by (rewrite (EWm 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19; apply unsigned_lit_small; lia).
  rewrite E19v in Q10.
  assert (E32x : ew E 32 = w64 (p_swz cx))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
  assert (E32v : bv_unsigned (getr (ms_regs ms) 11) = p_swz cx)
    by (rewrite Q11, E32x; apply unsigned_lit_small; pose proof (PcapEntryKit.p_swz_01 cx); lia).
  assert (Hb4 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) b (p_C cx))
    by (apply (PcapEntryKit.garr8_keep W3 _ _ _ _ _ _ Hbytes UN1); rewrite ?p_lens; lia).
  pose proof (PcapEntryKit.garr8_four _ _ _ (p_q cx p + 4) Hb4 ltac:(lia)
    ltac:(rewrite PcapEntryKit.p_lens; lia)) as H4.
  assert (Hspm : spZ (ms_regs ms) = c_sp1 cx)
    by (unfold spZ at 1; rewrite Q2; apply unsigned_lit_small; lia).
  assert (Hsp16m : c_sp1 cx mod 16 = 0).
  { destruct (proj1 (Zmod_divides (c_sp1 cx) 32 ltac:(lia)) Hal32) as [q Hq]. rewrite Hq.
    replace (32 * q) with ((2 * q) * 16) by lia. apply Z_mod_mult. }
  pmkst HS.
  rewrite (pa_xcalls PS_rd32 AF_rd32 ltac:(cbv [pcap_xcalls In]; tauto)).
  eapply SRr_bind.
  { eapply (PcapEntryKit.rd32_call B LAWS TL LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx)
      (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms)
      (b + (p_q cx p + 4)) b (p_nF cx) _ _ _ _ HJ).
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q10. unfold w64. f_equal. lia.
    - rewrite Hspm. exact Hsp16m.
    - rewrite Hspm. unfold Rd32.RD32_FRAME, LLVMF_STK. lia.
    - rewrite Hspm. lia.
    - exact Hb3.
    - lia.
    - unfold p_nF in *. lia.
    - cbn [ms_mem mkst]. exact H4. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hres & Hsame & Hfrm).
  assert (UN : mk W3 (ms_mem ms3) mem2 (c_sp1 cx - 16) (c_sp1 cx)).
  { apply (PcapEntryKit.mk_trans W3 _ (ms_mem ms) _ _ _ UN1). intros a Ha Hn. apply Hfrm; [exact Ha|].
    rewrite Hspm. unfold Rd32.RD32_FRAME. lia. }
  assert (Hap : PcapEntryKit.slots_apart cx (c_sp1 cx - 16) (c_sp1 cx))
    by (unfold PcapEntryKit.slots_apart; lia).
  assert (HPk : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
  { intros r Hr. pose proof (HP (bv_unsigned r) Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. }
  assert (HB2 : pe_body cx fp PP_KT2 W3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) PSH_ts).
  { eapply (PcapEntryKit.pe_body_keep cx fp PP_KT1 PP_KT2 W3 ms3 _ PSH_ts (c_sp1 cx - 16) (c_sp1 cx) Hbody);
      [ cbn [ms_pc_val mkst]; rewrite Q1; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity
      | cbn [ms_regs mkst]; rewrite (HPk (2%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)), Q2;
        symmetry; exact Rsp
      | cbn [ms_regs mkst]; rewrite (HPk (8%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)), Q8;
        reflexivity
      | cbn [ms_regs mkst]; rewrite (HPk (9%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)), Q9;
        symmetry; exact Rs1
      | cbn [ms_regs mkst]; rewrite (HPk (3%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)), Q3;
        reflexivity
      | cbn [ms_regs mkst]; rewrite (HPk (4%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)), Q4;
        reflexivity
      | cbn [ms_mem mkst]; exact UN | lia | lia | unfold LLVMF_STK; lia | lia | exact Hf0 | exact Hf1
      | exact Hinp ]. }
  apply (HKT2 cx fp k acc ly3 S3 W3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2 HB HJ2 Hfr Hmo).
  split; [| cbn [ms_regs mkst];
            rewrite (HPk (26%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)), Q26;
            rewrite R26 in HM; exact HM ].
  exists b, h, buf, i, p.
  split.
  { split.
    { exact HB2. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [rewrite (proj1 (same_but_materialized_fs _ _ Hsame));
            repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)); exact Hfds
           | rewrite (proj2 (same_but_materialized_fs _ _ Hsame));
             repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hgood|].
  split; [exact Hi0|]. split; [exact Hip|]. split; [exact HpQ|]. split; [exact Hfit|].
  split.
  { cbn [ms_regs mkst]. rewrite Hres.
    rewrite (PcapEntryKit.trd32_hw cx (p_q cx p) 4 (getr (ms_regs ms) 11) E32v). reflexivity. }
  split; [cbn [ms_regs mkst]; rewrite (HPk (18%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q18|].
  split; [cbn [ms_regs mkst]; rewrite (HPk (20%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q20|].
  split; [cbn [ms_regs mkst]; rewrite (HPk (21%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q21|].
  split; [cbn [ms_regs mkst]; rewrite (HPk (22%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q22|].
  split; [cbn [ms_regs mkst]; rewrite (HPk (23%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q23|].
  split; [cbn [ms_regs mkst]; rewrite (HPk (24%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q24|].
  split; [cbn [ms_regs mkst]; rewrite (HPk (25%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q25|].
  split; [cbn [ms_regs mkst]; rewrite (HPk (26%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q26|].
  split; [cbn [ms_regs mkst]; rewrite (HPk (27%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; lia)); exact Q27|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.p_lslots_keep cx fp W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) _ _ buf Hls UN Hap ltac:(lia) ltac:(lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) _ _ _ _ Hcalls UN Hap ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) _ _ _ _ Hfirst UN Hap ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst]; exact (PcapEntryKit.p_glob_keep cx W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) _ _ b Hglob UN ltac:(lia))|].
  cbn [ms_mem mkst].
  exact (PcapEntryKit.p_reader_keep B KS ASIL cx fp W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) _ _ b h buf p
           (conj Hsrc (conj (conj Hpsf Hpsw) Hfitc)) UN ltac:(lia) Hf0 Hf1
           ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.





Lemma pe_from_KT1 : pe_from_KT1_stmt.
Proof.
unfold pe_from_KT1_stmt. intros POST HKT2.
apply (PcapEntrySkip.pe_from_meas_all B MT KS POST). intros m.
apply (pe_from_KT1_m m POST). apply (PcapEntrySkip.pe_meas_of B MT KS POST). exact HKT2.
Qed.

(* ---- PP_KO -> PP_KT1 ----
   The proof (pe_from_KO, at the end): the start state ss_ko PP_KO; 0x80bfc `bne s6,a0` refuted (orig = hw 12); the
   tag test 0x80c08 split on incl < 18. Three paths reach the untagged arm 0x80d2c (incl < 18; F[Q+28] <> 0x81;
   F[Q+28] = 0x81 and F[Q+29] <> 0); each ends in the NEW cut GI_U at PP_U, which pe_from_U carries to PP_KT1
   (0x80d30 refuted from n = incl, bcmp(buf, rec, n), the join, rd32). The tagged path (incl >= 18, F[Q+28] = 0x81,
   F[Q+29] = 0) runs on to PP_KT1 itself: 0x80c84 refuted from n = incl - 4, bcmp(buf, rec, 12), bcmp(buf + 12,
   rec + 16, incl - 16), the VLAN id 0x80d24 refuted from ps.last_vlan_id = rec_vid, the join, rd32.
   UBSan guards (0x80c10, 0x80c3c, 0x80ca4, 0x80cac, 0x80cd0, 0x80cd8): decided by the runs from the atom ranges of
   ss_ko (s3 = b + Q in [4096, 0x7fffff800000], buf in [4096, 0x7fffff800000]); no trap arm is ever stepped.
   ASan shadow checks of rec + 12 .. rec + 15 = b + Q + 28 .. b + Q + 31 (0x80c28, 0x80c54, 0x80cf4, 0x80d0c): FORM B.
   The copy is malloc(|F|), so the granule of these bytes may be the last, partial one and the shadow byte may be
   nonzero; the token run (PaShadow.v (sha256 0c4d47929598; internal record), Reusable/YCbn.v tok_load / tok_branch) gives the `lb` a fresh atom
   (covered x 8 fails: ko_SH covers [28, 32) only), lets the entry `bnez` go either way, and in its slow-block arm
   refutes the `blt` fall-through into `j` / `jal __asan_report_load1` from need x (0 + 1): [x, x + 1) is
   addressable, which ko_SH covers. ko_SH is sh_ok from YCbq.v range_addressable_of_block on the copy block
   (b, |F|), which holds because the tagged arm is entered only when incl >= 18: |F| >= Q + 16 + incl >= Q + 34. *)

(* The bcmp calls (0x80c94, 0x80cc4, 0x80d40) take the kit's runtime rule for the bcmp interceptor. *)
Hypothesis ABCMP : abcmp_realizes SEGS B (pa_sigma PS___interceptor_trampoline_bcmp).

(* TAKEN FROM: Reusable/YG0d.v:353 abcmp_realizes (the Section hypothesis ABCMP) through Reusable/YCbq.v:2060
   aj_bcmp_at, on a fresh donor journal at the call state (YCbq.v:1825 ajournal_sub_init) repacked by
   lib/A/Prog/PaJournalFs.v ajournal_gx_callee; the descriptors and the file system by PaJournalFs.ajournal_closed_fs
   (the donor journal's footprint is empty). *)
Lemma U_sext32_small : forall E a v, U E a = v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 a) = v.
Proof.
intros E a v Ha Hv. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Z.mod_small by lia. rewrite Rd32.rd_swrap32_small by lia. apply zcanon_id. unfold M64. lia.
Qed.


(* The 32-bit zero extension of s11 - c (addi a0,s11,-c; slli a0,a0,32; srli a0,a0,32), as the runs leave it. *)
Lemma U_zext_sub32 : forall E v n c k, U E v = n -> 0 < c <= n -> n < 2 ^ 31 -> k = - (c * 2 ^ 32) ->
  U E (SAlu Instr.ALU_SRL (SAlu Instr.ALU_ADD (SAlu Instr.ALU_SLL v (SLit 32)) (SLit k)) (SLit 32)) = n - c.
Proof.
intros E v n c k Hv Hc Hn ->.
rewrite !U_SAlu, Hv, !U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 32) by (unfold M64; lia). change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (n * 2 ^ 32)) by (unfold M64; lia).
assert (Hk : zcanon (- (c * 2 ^ 32)) = 2 ^ 64 - c * 2 ^ 32).
{ unfold zcanon, M64. symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
rewrite Hk.
assert (Hs : zcanon (n * 2 ^ 32 + (2 ^ 64 - c * 2 ^ 32)) = (n - c) * 2 ^ 32).
{ unfold zcanon, M64. symmetry. apply (Z.mod_unique _ _ 1); lia. }
rewrite Hs, Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma bcmp_call : forall STK sp0 FP ly S W0 mem md own lyc Sc (W3 : world SEGS) memc mdc k
    (regs : bvmap 5 word) x y n,
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 2 * ESTACK -> spZ regs <= sp0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> YK0s.ret_ok (getr regs 1) ->
  src_ok SEGS W3 regs memc x n -> src_ok SEGS W3 regs memc y n ->
  (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview SEGS (w_H W3) memc) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W3) memc) x n) ->
  range_addressable (aview SEGS (w_H W3) memc) SHADOW_OFF y n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W3) memc) y n) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (pa_sigma PS___interceptor_trampoline_bcmp)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2' => W2 = W3 /\ exists regs2 mem2 md2,
       c2' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W3 mem2 md2 k /\
       aregs_preserved regs regs2 /\
       (getr regs2 10 = w64 0 <->
          forall i, 0 <= i < n -> aview SEGS (w_H W3) memc (x + i) = aview SEGS (w_H W3) memc (y + i)) /\
       m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memc a)).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k regs x y n
  HJ H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hal16 Hwlo Hwhi Hgp Htp Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (ajournal_sub_init SEGS B STK sp0 FP ly S W0 memS md own lyc Sc W3 memc mdc k
  (2 * ESTACK) (spZ regs) [] (spZ regs - sp0) HJi ltac:(lia)
  ltac:(pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & _) & _);
        rewrite Zminus_mod, Hal16, Hal; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia)) as HJ0.
eapply SRr_mono.
{ exact (aj_bcmp_at SEGS B LAWS Hsegs _ ABCMP W3 regs memc (2 * ESTACK) (spZ regs) [] lyc Sc W3 memc mdc []
    lyc Sc mdc 0 x y n 0 (getr regs 1) HJ0 H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn ltac:(lia) ltac:(reflexivity)
    ltac:(lia) ltac:(lia) Hgp Htp eq_refl Hraw Hsx Hsy
    ltac:(rewrite Z.add_0_r; exact Hbx) ltac:(rewrite Z.add_0_r; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2' _ (-> & regs2 & mem2 & md2 & v & -> & HJ1 & HP & Hres & Hcmp & Hfrm & _).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split.
{ pose proof (ajournal_gx_callee SK SEGS B LAWS Hsegs pe_G STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k
    (2 * ESTACK) (spZ regs) [] [] lyc Sc W3 mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; destruct Ha as (z & [] & _))) as HJ2.
  rewrite Z.add_0_r in HJ2. cbn [app] in HJ2. exact HJ2. }
split; [exact HP|]. split; [rewrite Hres; exact Hcmp|].
destruct (ajournal_closed_fs SK SEGS B (2 * ESTACK) (spZ regs) [] lyc Sc W3 memc mdc [] lyc Sc W3 mem2 md2 0
  sink_closed_nil HJ1) as [F1 F2].
split; [exact F1|]. split; [exact F2|].
intros a Ha Hna. apply Hfrm; [exact Ha | rewrite Z.add_0_r; exact Hna].
Qed.


(* ---- the record's bytes: the buffer's (PSN.rec_bytes) against the copy's ---- *)
Lemma nth_map_u : forall (l : list byte) j,
  nth j (map (fun x : byte => bv_unsigned x) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. intros l j. rewrite <- (map_nth (fun x : byte => bv_unsigned x) l (Z_to_bv 8 0) j). reflexivity. Qed.

Lemma rec_raw_len : forall sw F Q, 0 <= Q -> 0 <= PSN.incl sw F Q -> Q + 16 + PSN.incl sw F Q <= Z.of_nat (length F) ->
  length (PSN.rec_raw sw F Q) = Z.to_nat (PSN.incl sw F Q).
Proof. intros sw F Q H0 H1 H2. unfold PSN.rec_raw. rewrite length_firstn, length_skipn. lia. Qed.

Lemma rec_raw_nth : forall sw F Q j, 0 <= Q -> 0 <= j < PSN.incl sw F Q ->
  Q + 16 + PSN.incl sw F Q <= Z.of_nat (length F) ->
  nth (Z.to_nat j) (PSN.rec_raw sw F Q) (Z_to_bv 8 0) = nth (Z.to_nat (Q + 16 + j)) F (Z_to_bv 8 0).
Proof.
intros sw F Q j H0 Hj H2. unfold PSN.rec_raw. rewrite nth_firstn.
replace (Z.to_nat j <? Z.to_nat (PSN.incl sw F Q))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn. f_equal. lia.
Qed.

(* The untagged record: the buffer holds the incl bytes after the header. *)
Lemma rec_bytes_untagged : forall sw F Q j, PSN.tagged sw F Q = false -> 0 <= Q -> 0 <= j < PSN.incl sw F Q ->
  Q + 16 + PSN.incl sw F Q <= Z.of_nat (length F) ->
  length (PSN.rec_bytes sw F Q) = Z.to_nat (PSN.incl sw F Q) /\
  nth (Z.to_nat j) (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes sw F Q)) 0 =
  nth (Z.to_nat (Q + 16 + j)) (map (fun x : byte => bv_unsigned x) F) 0.
Proof.
intros sw F Q j Ht H0 Hj H2. unfold PSN.rec_bytes. rewrite Ht.
split; [apply rec_raw_len; lia|].
rewrite !nth_map_u. f_equal. apply rec_raw_nth; lia.
Qed.

(* The tagged record: the buffer holds the 12 address bytes, then the bytes after the tag, then the trailer. *)
Lemma rec_bytes_tagged : forall sw F Q, PSN.tagged sw F Q = true -> 0 <= Q ->
  Q + 16 + PSN.incl sw F Q <= Z.of_nat (length F) ->
  length (PSN.rec_bytes sw F Q) = Z.to_nat (PSN.incl sw F Q) /\
  (forall j, 0 <= j < 12 ->
     nth (Z.to_nat j) (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes sw F Q)) 0 =
     nth (Z.to_nat (Q + 16 + j)) (map (fun x : byte => bv_unsigned x) F) 0) /\
  (forall j, 0 <= j < PSN.incl sw F Q - 16 ->
     nth (Z.to_nat (12 + j)) (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes sw F Q)) 0 =
     nth (Z.to_nat (Q + 32 + j)) (map (fun x : byte => bv_unsigned x) F) 0).
Proof.
intros sw F Q Ht H0 H2. pose proof (PcapEntryKit.tagged_incl sw F Q Ht) as H18.
assert (HL : length (PSN.rec_raw sw F Q) = Z.to_nat (PSN.incl sw F Q)) by (apply rec_raw_len; lia).
unfold PSN.rec_bytes. rewrite Ht.
split.
{ rewrite !length_app, !length_firstn, length_skipn, length_skipn, HL. lia. }
split.
- intros j Hj. rewrite !nth_map_u. f_equal.
  rewrite app_nth1 by (rewrite length_firstn, HL; lia).
  rewrite nth_firstn. replace (Z.to_nat j <? 12)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  apply rec_raw_nth; lia.
- intros j Hj. rewrite !nth_map_u. f_equal.
  rewrite app_nth2 by (rewrite length_firstn, HL; lia).
  rewrite length_firstn, HL. replace (Z.to_nat (12 + j) - Nat.min 12 (Z.to_nat (PSN.incl sw F Q)))%nat with (Z.to_nat j) by lia.
  rewrite app_nth1 by (rewrite length_firstn, length_skipn, HL; lia).
  rewrite nth_firstn. replace (Z.to_nat j <? Z.to_nat (PSN.incl sw F Q - 16))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. replace (16 + Z.to_nat j)%nat with (Z.to_nat (16 + j)) by lia.
  rewrite rec_raw_nth by lia. f_equal. lia.
Qed.


(* PP_KO 0x80bfc: the symbolic start. Atoms beyond the registers: 32 = the shadow base SHADOW_OFF (slot PS_SHB,
   reloaded 0x80c1c / 0x80c48 / 0x80ce4), 33 = buf (PS_BUF), 34 = buf + 12 (PS_BUF12), 35 = n (PS_N), 36 = &ts
   (PS_TSP), 37 = ps.last_vlan_tagged, 38 = ps.last_vlan_id, 39 = ts, 40 = ps.swapped, 41 .. 44 = the copy's bytes at
   Q + 28 .. Q + 31 (region ko_bytes, added on the arm incl >= 18 only). The regions are read-only: the stretch
   stores nothing. *)
Definition ko_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 16 152 0 0
    [YP09.mkChunk PS_VMASK (CVal 8 (SLit 3840)); YP09.mkChunk PS_BUF12 (CVal 8 (SOff 34 0));
     YP09.mkChunk PS_SHB (CVal 8 (SOff 32 0)); YP09.mkChunk PS_TSP (CVal 8 (SOff 36 0));
     YP09.mkChunk PS_BUF (CVal 8 (SOff 33 0)); YP09.mkChunk PS_N (CVal 8 (SOff 35 0))].
Definition ko_ps : YP09.region :=
  YP09.mkRegion (Some 20%nat) 8 22 0 0
    [YP09.mkChunk 8 (CVal 4 (SOff 40 0)); YP09.mkChunk 16 (CVal 4 (SOff 37 0)); YP09.mkChunk 20 (CVal 2 (SOff 38 0))].
Definition ko_ts : YP09.region := YP09.mkRegion (Some 36%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
Definition ko_bytes : YP09.region :=
  YP09.mkRegion (Some 19%nat) 28 32 0 0
    [YP09.mkChunk 28 (CVal 1 (SOff 41 0)); YP09.mkChunk 29 (CVal 1 (SOff 42 0));
     YP09.mkChunk 30 (CVal 1 (SOff 43 0)); YP09.mkChunk 31 (CVal 1 (SOff 44 0))].
Definition ko_regions : smem := [ko_slots; ko_ps; ko_ts].
Definition ko_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF 4096 140737479966720 0);
           (32%nat, mkAF 2147450880 2147450880 0); (33%nat, mkAF 4096 140737479966720 0)] [] [].
Definition ss_ko (pc : Z) : sstate := mkSS pc sr_atoms ko_regions None ko_facts.
Definition KBx : sv := SOff 32 0.
Definition ko_SH : list shent := [mkSHE 19 28 32].
Definition ko_extra (buf nv tsp tag vid ts sw c28 c29 c30 c31 : Z) : list word :=
  map (Z_to_bv 64) [SHADOW_OFF; buf; buf + 12; nv; tsp; tag; vid; ts; sw; c28; c29; c30; c31].


(* The bytes of two arrays agree, address by address: what the bcmp rule's post needs. *)
Lemma aview_eq_of_garr8 : forall (W : world SEGS) (m : word -> option byte) x y d n (L1 L2 : list Z),
  garr8 SEGS (mrestrict (w_H W) m) x L1 -> garr8 SEGS (mrestrict (w_H W) m) y L2 ->
  0 <= d -> d + n <= Z.of_nat (length L1) -> n <= Z.of_nat (length L2) ->
  (forall j, 0 <= j < n -> nth (Z.to_nat (d + j)) L1 0 = nth (Z.to_nat j) L2 0) ->
  forall j, 0 <= j < n -> aview SEGS (w_H W) m (x + d + j) = aview SEGS (w_H W) m (y + j).
Proof.
intros W m x y d n L1 L2 H1 H2 Hd Hn1 Hn2 HE j Hj.
destruct (garr8_nthZ SEGS (mrestrict (w_H W) m) x L1 (d + j) H1 ltac:(lia) ltac:(lia)) as [V1 R1].
destruct (garr8_nthZ SEGS (mrestrict (w_H W) m) y L2 j H2 ltac:(lia) ltac:(lia)) as [V2 R2].
rewrite Z.add_assoc in V1.
rewrite (aview_of_val_mem1 SEGS (w_H W) m (x + d + j) _ V1 R1).
rewrite (aview_of_val_mem1 SEGS (w_H W) m (y + j) _ V2 R2).
rewrite (HE j Hj). reflexivity.
Qed.


Lemma aview_eq_of_garr8_2 : forall (W : world SEGS) (m : word -> option byte) x y d1 d2 n (L1 L2 : list Z),
  garr8 SEGS (mrestrict (w_H W) m) x L1 -> garr8 SEGS (mrestrict (w_H W) m) y L2 ->
  0 <= d1 -> 0 <= d2 -> d1 + n <= Z.of_nat (length L1) -> d2 + n <= Z.of_nat (length L2) ->
  (forall j, 0 <= j < n -> nth (Z.to_nat (d1 + j)) L1 0 = nth (Z.to_nat (d2 + j)) L2 0) ->
  forall j, 0 <= j < n -> aview SEGS (w_H W) m (x + d1 + j) = aview SEGS (w_H W) m (y + d2 + j).
Proof.
intros W m x y d1 d2 n L1 L2 H1 H2 Hd1 Hd2 Hn1 Hn2 HE j Hj.
destruct (garr8_nthZ SEGS (mrestrict (w_H W) m) x L1 (d1 + j) H1 ltac:(lia) ltac:(lia)) as [V1 R1].
destruct (garr8_nthZ SEGS (mrestrict (w_H W) m) y L2 (d2 + j) H2 ltac:(lia) ltac:(lia)) as [V2 R2].
rewrite Z.add_assoc in V1, V2.
rewrite (aview_of_val_mem1 SEGS (w_H W) m (x + d1 + j) _ V1 R1).
rewrite (aview_of_val_mem1 SEGS (w_H W) m (y + d2 + j) _ V2 R2).
rewrite (HE j Hj). reflexivity.
Qed.


(* The VLAN id as 0x80d14 .. 0x80d20 compute it: ((rec[14] << 8) & 0xf00) | rec[15] = rec_vid. *)
Lemma vlan_id_bits : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  Z.lor (Z.land (x * 2 ^ 8) 3840) y = (256 * x + y) mod 4096.
Proof.
intros x y Hx Hy.
assert (HA : Z.land (x * 2 ^ 8) 3840 = (x mod 16) * 2 ^ 8).
{ change 3840 with (Z.shiftl (Z.ones 4) 8). rewrite <- Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
rewrite HA, Z.lor_comm, (Rd32.rd_lor_disj y ((x mod 16) * 2 ^ 8) 8 (x mod 16)) by (try lia; reflexivity).
pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as Hm.
apply (Z.mod_unique _ _ (x / 16)); [lia|].
pose proof (Z.div_mod x 16 ltac:(lia)). lia.
Qed.

(* One bcmp call of the stretch: the two ranges are inside live blocks, the bytes agree, so a0 = 0 at the return.
   TAKEN FROM: bcmp_call (above) over the Section hypothesis ABCMP. *)
Lemma bcmp_zero : forall STK sp0 FP ly S W0 mem md own lyc Sc (W3 : world SEGS) memc mdc kk
    (regs : bvmap 5 word) x y n bx nx by_ ny,
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc kk ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 2 * ESTACK -> spZ regs <= sp0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> YK0s.ret_ok (getr regs 1) ->
  AR SEGS B lyc Sc W3 memc mdc ->
  In (bx, nx) (ablocks B lyc Sc) -> bx <= x -> x + n <= bx + nx ->
  In (by_, ny) (ablocks B lyc Sc) -> by_ <= y -> y + n <= by_ + ny ->
  (forall j, 0 <= j < n -> aview SEGS (w_H W3) memc (x + j) = aview SEGS (w_H W3) memc (y + j)) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (pa_sigma PS___interceptor_trampoline_bcmp)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2' => W2 = W3 /\ exists regs2 mem2 md2,
       c2' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W3 mem2 md2 kk /\
       aregs_preserved regs regs2 /\ getr regs2 10 = w64 0 /\
       m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memc a)).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc kk regs x y n bx nx by_ ny
  HJ H10 H11 H12 Hn Hal16 Hwlo Hwhi Hgp Htp Hraw HAR Hinx Hbx Hxn Hiny Hby Hyn HE.
pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
destruct (al_blocks _ _ LAWS lyc Sc W3 memc mdc bx nx HAR Hinx) as (_ & Hx4096 & Hxceil & _ & _ & _ & Hnx).
destruct (al_blocks _ _ LAWS lyc Sc W3 memc mdc by_ ny HAR Hiny) as (_ & Hy4096 & Hyceil & _ & _ & _ & Hny).
pose proof (req_size_pos0 nx ltac:(lia)) as [_ Hrx]. pose proof (req_size_pos0 ny ltac:(lia)) as [_ Hry].
assert (Hsrc : forall u m0, In (u, m0) (ablocks B lyc Sc) -> forall a, u <= a < u + m0 ->
          aview SEGS (w_H W3) memc a <> None).
{ intros u m0 Hin a Ha.
  destruct (al_blocks _ _ LAWS lyc Sc W3 memc mdc u m0 HAR Hin) as (_ & _ & _ & _ & Hpr & _ & Hm0).
  pose proof (req_size_pos0 m0 ltac:(lia)) as [_ Hrq].
  apply (aview_some_of_apresent SEGS). apply (proj1 (Hpr a ltac:(lia))). }
eapply SRr_mono.
{ exact (bcmp_call STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc kk regs x y n HJ H10 H11 H12
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hal16 Hwlo Hwhi Hgp Htp Hraw
    ltac:(intros a Ha; split; [apply (Hsrc bx nx Hinx); lia | lia])
    ltac:(intros a Ha; split; [apply (Hsrc by_ ny Hiny); lia | lia])
    ltac:(intros a Ha; lia) ltac:(intros a Ha; lia)
    (amem_range_of_block SEGS B LAWS lyc Sc W3 memc mdc bx nx x n HAR Hinx ltac:(lia) ltac:(lia))
    (amem_range_of_block SEGS B LAWS lyc Sc W3 memc mdc by_ ny y n HAR Hiny ltac:(lia) ltac:(lia))
    (range_addressable_of_block SEGS B LAWS lyc Sc W3 memc mdc bx nx x n HAR Hinx ltac:(lia) ltac:(lia))
    ltac:(intros Hpos; exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W3 memc mdc bx nx x n HAR Hinx ltac:(lia) ltac:(lia) Hpos))
    (range_addressable_of_block SEGS B LAWS lyc Sc W3 memc mdc by_ ny y n HAR Hiny ltac:(lia) ltac:(lia))
    ltac:(intros Hpos; exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W3 memc mdc by_ ny y n HAR Hiny ltac:(lia) ltac:(lia) Hpos))). }
cbv beta. intros W2 c2' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hcmp & F1 & F2 & Hfrm).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
split; [exact HP|]. split; [apply (proj2 Hcmp); exact HE|]. split; [exact F1|]. split; [exact F2 | exact Hfrm].
Qed.


Lemma ko_entry : forall cx fp pc (W3 : world SEGS) (ms3 : machine_state) bq buf nv tag vid ts c28 c29 c30 c31,
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) -> getr (ms_regs ms3) 19 = w64 bq ->
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) ->
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  2 ^ 46 <= c_sp1 cx <= 2 ^ 47 -> c_sp1 cx mod 32 = 0 -> alloc_ceiling <= c_sp1 cx ->
  4096 <= pF cx fp -> pF cx fp + PE_FRAME <= alloc_ceiling ->
  4096 <= bq <= 140737479966720 -> 4096 <= buf <= 140737479966720 ->
  0 <= nv < 2 ^ 64 -> 0 <= tag < 2 ^ 32 -> 0 <= vid < 2 ^ 16 -> 0 <= ts < 2 ^ 64 ->
  pslot cx W3 ms3 PS_VMASK 0xf00 -> pslot cx W3 ms3 PS_BUF12 (buf + 12) -> pslot cx W3 ms3 PS_SHB SHADOW_OFF ->
  pslot cx W3 ms3 PS_TSP (pF cx fp + PO_TS) -> pslot cx W3 ms3 PS_BUF buf -> pslot cx W3 ms3 PS_N nv ->
  pval W3 ms3 (pPS cx fp + 8) 4 (p_swz cx) -> pval W3 ms3 (pPS cx fp + 16) 4 tag ->
  pval W3 ms3 (pPS cx fp + 20) 2 vid -> pval W3 ms3 (pTS cx fp) 8 ts ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) (ko_extra buf nv (pTS cx fp) tag vid ts (p_swz cx) c28 c29 c30 c31)))
    (ss_ko pc) (restrict (w_H W3) ms3).
Proof.
intros cx fp pc W3 ms3 bq buf nv tag vid ts c28 c29 c30 c31 H9 H19 H20 Hpc Hrv Hsv Hrom Hfr Hfc Hsp Hal Hceil Hf0 Hf1 Hbq Hbuf
  Hnv Htag Hvid Hts SVM SB12 SSHB STSP SBUF SN Vsw Vtag Vvid Vts.
pose proof asan_consts as (C1 & _).
unfold PE_FRAME in Hf1.
assert (Hsw : 0 <= p_swz cx < 2 ^ 32) by (unfold p_swz, PST.pcap_sw; destruct (_ =? _); lia).
set (E := Eimg (Ereg (ms_regs ms3) (ko_extra buf nv (pTS cx fp) tag vid ts (p_swz cx) c28 c29 c30 c31))).
assert (EL : forall i, (i < A_TEXT)%nat ->
  ew E i = ew (Ereg (ms_regs ms3) (ko_extra buf nv (pTS cx fp) tag vid ts (p_swz cx) c28 c29 c30 c31)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = w64 bq)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 19 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = w64 (pPS cx fp))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (buf + 12)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (pTS cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 tag) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 vid) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 ts) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (p_swz cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 8)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = bq) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = pPS cx fp) by (rewrite E20; apply unsigned_lit_small; unfold pPS, PO_PS; lia).
assert (U36 : bv_unsigned (ew E 36) = pTS cx fp) by (rewrite E36; apply unsigned_lit_small; unfold pTS, PO_TS; lia).
assert (Hval : forall v (e : nat), ew E e = Z_to_bv 64 v -> sv_denot E (SOff e 0) = Z_to_bv 64 v)
  by (intros v e He; cbn [sv_denot]; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS)).
{ destruct ms3; cbn in *; unfold mkst; subst; f_equal; assumption. }
rewrite Hms, restrict_mkst_fx. unfold ss_ko. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ko_regions, ko_slots, ko_ps, ko_ts.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold pslot in *. unfold PS_VMASK, PS_BUF12, PS_SHB, PS_TSP, PS_BUF, PS_N in *.
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 48 8 (SLit 3840) 3840); [reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SVM).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 56 8 (SOff 34 0) (buf + 12)); [exact (Hval _ _ E34) | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SB12).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 72 8 (SOff 32 0) SHADOW_OFF);
        [exact (Hval _ _ E32) | unfold SHADOW_OFF; zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SSHB).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 88 8 (SOff 36 0) (pTS cx fp));
        [exact (Hval _ _ E36) | unfold pTS, PO_TS; zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ STSP).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 96 8 (SOff 33 0) buf); [exact (Hval _ _ E33) | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SBUF).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 35 0) nv); [exact (Hval _ _ E35) | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SN).
  + rewrite U20. unfold pPS, PO_PS in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold pval in *.
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (pF cx fp + 32) 8 4 (SOff 40 0) (p_swz cx)); [exact (Hval _ _ E40) | zside | zside |].
      exact Vsw.
    * apply (chunk_ok_val SEGS E _ (pF cx fp + 32) 16 4 (SOff 37 0) tag); [exact (Hval _ _ E37) | zside | zside |].
      exact Vtag.
    * apply (chunk_ok_val SEGS E _ (pF cx fp + 32) 20 2 (SOff 38 0) vid); [exact (Hval _ _ E38) | zside | zside |].
      exact Vvid.
  + rewrite U36. unfold pTS, PO_TS in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold pval in *.
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (pF cx fp + 96) 0 8 (SOff 39 0) ts); [exact (Hval _ _ E39) | zside | zside |].
    rewrite Z.add_0_r. exact Vts.
- apply pairwise_disjoint_of_extents.
  unfold ko_regions, ko_slots, ko_ps, ko_ts, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U20, U36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, pPS, pTS, PO_PS, PO_TS. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [ko_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite U9, U19, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.


(* The runs of the stretch store nothing: every region is read-only, so the write obligation is empty and the run
   keeps every byte. *)
Ltac ko_awr :=
  apply awr_ok_x_of0;
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].
Ltac ko_kept HFr UN :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; lia|]);
          destruct HinW)) as UN.



(* NEW CUT. PP_U 0x80d2c: the record is not VLAN-tagged (the three paths of the tag test join here), the harness
   is about to check n against incl and to bcmp(buf, rec, n). s6 = rec = b + Q + 16 (0x80c00). GI_KO's facts at
   this pc, with tagged = false, s6 = rec and a0 dead. pe_from_U proves it against GI_KT1. *)
Definition PP_U : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x514) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.          (* 0x80d2c, `ld a0,0x70(s1)` *)

Definition GI_U (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p : Z,
  let Q := p_q cx p in
  p_cut B cx fp PP_U PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p <= Q /\ p_kind cx Q = PSN.KFit /\
  PSN.tagged (p_sw cx) (p_F cx) Q = false /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 19 = w64 (b + Q) /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 21 = w64 (-8) /\
  getr (ms_regs ms3) 22 = w64 (b + Q + 16) /\
  getr (ms_regs ms3) 23 = w64 (- b - 1) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 25 = w64 (p_hw cx Q 8) /\ getr (ms_regs ms3) 26 = w64 Q /\
  getr (ms_regs ms3) 27 = w64 (bv_swrap 32 (p_hw cx Q 8)) /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_CALLS (i + 1) /\ pslot cx W3 ms3 PS_N (p_res cx Q) /\
  pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader KS cx fp W3 ms3 b h buf p.

Definition pe_from_U_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_KT1 B MT KS) -> pe_from SK B MT KS POST GI_U.

(* The measured form: s10 = Q at PP_U and at PP_KT1, so the bound m on |F| - s10 passes through unchanged. *)
Lemma pe_from_U_m : forall m POST,
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_KT1 B MT KS) m) ->
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas GI_U m).
Proof.
intros m POST HKT1.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo (HI & HM).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct (PcapEntryKit.rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgpv & Htpv & _).
destruct HI as (b & h & buf & i & p & HI). cbv zeta in HI.
destruct HI as (Hcut & Hn26 & Hgood & Hi0 & Hip & HpQ & Hfit & Etag & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25
  & R26 & R27 & Hls & Hcalls & HsN & Hfirst & Hglob & Hrd).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
(* the blocks of the cut: the copy, the FILE and the buffer are live, so each lies under the ceiling *)
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hu3 : In (buf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096 & Hbceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR Hh3) as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 buf (p_bn cx) HAR Hu3) as (_ & Hu4096 & Huceil & _).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
assert (Hbncap : p_cap cx <= p_bn cx) by (unfold p_bn; lia).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrq1a Hrq1].
pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as [_ Hrq2].
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [Hrq3a Hrq3].
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
unfold LLVMF_STK in Hspc, Hpres.
assert (Hs1 : 2 ^ 46 <= c_sp1 cx <= 2 ^ 47) by lia.
(* the record: fit, so 0 < incl <= cap and Q + 16 + incl <= |F| *)
unfold p_kind in Hfit.
destruct (PcapEntryKit.kind_fit _ _ _ _ Hfit) as (I1 & I2 & I3 & I4).
fold (p_nF cx) in I3, I4.
assert (HFlen : Z.of_nat (length (p_F cx)) = p_nF cx) by reflexivity.
assert (HQ0 : 24 <= p_q cx p) by lia.
(* the reader's facts *)
destruct Hrd as (Hsrc & (Hpf & Hpsw) & Hfitr).
destruct (Hfitr Hfit) as (Vorig & Vtag & Vvid & Vts & Vbuf).
destruct Hls as (Hsl & Hslbuf & Hslvm & Hslb12 & Hslus).
pose proof Hsl as (S_F0 & S_D & S_SHB & S_SH & S_F & S_FK & S_TSP & S_CAP).
pose proof Hsrc as (Wc & cpos & flc & mdcx & A0 & A1 & A2 & A3 & A4 & A5 & A6 & Hbok & HgC & _).
rewrite PcapEntryKit.p_lens in A2, A3, A4.
set (Q := p_q cx p) in *.
clear A0 A1 A5 A6.
(* the start state *)
assert (Hnv : 0 < p_res cx Q <= 2040).
{ unfold p_res, PSN.res_of, PSN.rec_len. rewrite Hfit.
  destruct (PSN.tagged (p_sw cx) (p_F cx) Q) eqn:Et; [pose proof (PcapEntryKit.tagged_incl _ _ _ Et)|]; split; lia. }
assert (Hts : 0 <= PSN.rec_ts (p_sw cx) (p_F cx) Q < 2 ^ 64)
  by (unfold PSN.rec_ts; pose proof (hw_range (p_sw cx) (p_F cx) Q 0); pose proof (hw_range (p_sw cx) (p_F cx) Q 4); lia).
assert (Hvid : 0 <= (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0) < 2 ^ 16)
  by (destruct (PSN.tagged _ _ _); [unfold PSN.rec_vid; pose proof (Z.mod_pos_bound (256 * PSN.fb (p_F cx) (Q + 30) + PSN.fb (p_F cx) (Q + 31)) 4096 ltac:(lia)); lia | lia]).
assert (Htag : 0 <= (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0) < 2 ^ 32) by (destruct (PSN.tagged _ _ _); lia).
pose proof (ko_entry cx fp PP_U W3 ms3 (b + Q) buf (p_res cx Q) _ _ _
  (PSN.fb (p_F cx) (Q + 28)) (PSN.fb (p_F cx) (Q + 29)) (PSN.fb (p_F cx) (Q + 30)) (PSN.fb (p_F cx) (Q + 31))
  Rs1 R19 R20 Hpc Hrv Hsv Hrom Hfreg Hfcsr Hs1 Hal32 ltac:(lia) Hf0 Hf1 ltac:(lia) ltac:(lia) ltac:(lia) Htag Hvid Hts
  Hslvm Hslb12 S_SHB S_TSP Hslbuf HsN Hpsw Vtag Vvid Vts) as HS.
set (XT := ko_extra buf (p_res cx Q) (pTS cx fp)
  (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0)
  (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0)
  (PSN.rec_ts (p_sw cx) (p_F cx) Q) (p_swz cx)
  (PSN.fb (p_F cx) (Q + 28)) (PSN.fb (p_F cx) (Q + 29)) (PSN.fb (p_F cx) (Q + 30)) (PSN.fb (p_F cx) (Q + 31))) in HS.
remember (Eimg (Ereg (ms_regs ms3) XT)) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall ii, (ii < A_TEXT)%nat -> ew E ii = ew (Ereg (ms_regs ms3) XT) ii)
  by (intros ii Hii; subst E; apply Eimg_low; exact Hii).
assert (EW : forall ii (r : bv 5), (ii < A_TEXT)%nat -> Z.of_nat ii = bv_unsigned r -> ew E ii = getr (ms_regs ms3) r)
  by (intros ii r Hii Hr; rewrite EL by exact Hii; exact (ew_Ereg_nat (ms_regs ms3) _ ii r Hr)).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) XT) E)
  by (split; [intros i' Hi'; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j XT (Z_to_bv 64 0)).
{ intros j Hj. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
clear HEdef.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (buf + 12)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (p_res cx Q)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (pTS cx fp)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0)) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0))
  by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = Z_to_bv 64 (PSN.rec_ts (p_sw cx) (p_F cx) Q)) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E 40 = Z_to_bv 64 (p_swz cx)) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = Z_to_bv 64 (PSN.fb (p_F cx) (Q + 28))) by exact (EX 9%nat ltac:(lia)).
assert (E42 : ew E 42 = Z_to_bv 64 (PSN.fb (p_F cx) (Q + 29))) by exact (EX 10%nat ltac:(lia)).
assert (E43 : ew E 43 = Z_to_bv 64 (PSN.fb (p_F cx) (Q + 30))) by exact (EX 11%nat ltac:(lia)).
assert (E44 : ew E 44 = Z_to_bv 64 (PSN.fb (p_F cx) (Q + 31))) by exact (EX 12%nat ltac:(lia)).
assert (U35 : U E (SOff 35 0) = p_res cx Q) by (apply U_atom; [exact E35 | lia]).
assert (U37 : U E (SOff 37 0) = if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0) by (apply U_atom; [exact E37 | lia]).
assert (U25 : U E (SOff 25 0) = PSN.incl (p_sw cx) (p_F cx) Q).
{ rewrite U_SOff, (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25. unfold p_hw. fold (PSN.incl (p_sw cx) (p_F cx) Q).
  unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
pose proof (PcapEntryKit.bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (PcapEntryKit.bpaj_run_to_x B LAWS pe_G HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
assert (SHOK0 : sh_ok SEGS KBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
(* 0x80d2c `ld a0,0x70(s1)`: n, then the length test *)
paj_run_tok RUN HS HJ SHOK0 Espan; [ko_awr |].
ko_kept HFr UN1. clear HF HFr HG.
  assert (Hres : p_res cx Q = PSN.incl (p_sw cx) (p_F cx) Q)
    by (unfold p_res, PSN.res_of, PSN.rec_len; rewrite Hfit, Etag; reflexivity).
  psrr_branch_tok RUN BR HS SHOK0 Espan.
  { exfalso. rewrite branch_ne_U, U35, U25, Hres, Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK0 Espan; [ko_awr |].
  ko_kept HFr UN2. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  rewrite E33 in Q10. rewrite (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl), R22 in Q11.
  rewrite E35 in Q12. rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in Q4.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in Q2.
  assert (UNa : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem ms0) 0 0)
    by (intros a Ha Hn; rewrite (UN2 a Ha ltac:(tauto)); exact (UN1 a Ha ltac:(tauto))).
  assert (Qsp : spZ (ms_regs ms0) = c_sp1 cx)
    by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
  pose proof HJ as (_ & _ & (memS1 & HJi1 & _) & _). rewrite !Z.add_0_r in HJi1.
  pose proof HJi1 as (HAR2 & _).
  assert (HgC2 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms0)) b (p_C cx))
    by (apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem ms0) 0 0 _ _ HgC UNa); pose proof (PcapEntryKit.p_lens cx); lia).
  assert (Vbuf2 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms0)) buf
                    (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes (p_sw cx) (p_F cx) Q))).
  { apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem ms0) 0 0 _ _ Vbuf UNa); rewrite ?length_map;
    pose proof (PcapEntryKit.rec_bytes_len (p_sw cx) (p_F cx) Q ltac:(lia) ltac:(intros Ht; rewrite Etag in Ht; discriminate Ht)); lia. }
  destruct (rec_bytes_untagged (p_sw cx) (p_F cx) Q 0 Etag ltac:(lia) ltac:(lia) ltac:(lia)) as (HRL & _).
  eapply SRr_bind.
  { eapply (bcmp_zero LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms0) _ k (ms_regs ms0) buf (b + Q + 16) (p_res cx Q)
      buf (p_bn cx) b (p_nF cx) HJ Q10 ltac:(rewrite Q11; f_equal; lia) Q12 ltac:(lia)
      ltac:(rewrite Qsp; lia) ltac:(rewrite Qsp; unfold ESTACK, LLVMF_STK; lia) ltac:(rewrite Qsp; lia)
      ltac:(rewrite Q3; exact Hgpv) ltac:(rewrite Q4; exact Htpv)
      ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
      HAR2 Hu3 ltac:(lia) ltac:(lia) Hb3 ltac:(lia) ltac:(lia)).
    intros j Hj. symmetry. replace (b + Q + 16 + j) with (b + (Q + 16) + j) by lia.
    apply (aview_eq_of_garr8 W3 (ms_mem ms0) b buf (Q + 16) (p_res cx Q) (p_C cx)
             (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes (p_sw cx) (p_F cx) Q))
             HgC2 Vbuf2 ltac:(lia) ltac:(pose proof (PcapEntryKit.p_lens cx); lia) ltac:(rewrite length_map, HRL; lia)); [|lia].
    intros jj Hjj. unfold p_C. symmetry.
    exact (proj2 (rec_bytes_untagged (p_sw cx) (p_F cx) Q jj Etag ltac:(lia) ltac:(lia) ltac:(lia))). }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hres4 & Hfds4 & Hfs4 & Hkept4).
  rewrite Qsp in Hkept4.
  assert (UNb : PcapEntryKit.mk W3 (ms_mem ms3) mem4 (c_sp1 cx - 2 * ESTACK) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (Hkept4 a Ha Hn); exact (UNa a Ha ltac:(lia))).
  assert (U9b : bv_unsigned (ew E 9) = c_sp1 cx)
    by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
  assert (U20b : bv_unsigned (ew E 20) = pPS cx fp)
    by (rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20; apply unsigned_lit_small;
        unfold pPS, PO_PS, PE_FRAME in *; lia).
  assert (U36b : bv_unsigned (ew E 36) = pTS cx fp)
    by (rewrite E36; apply unsigned_lit_small; unfold pTS, PO_TS, PE_FRAME in *; lia).
  jafter_call_keep_pi HS 46%nat regs4 (mrestrict (w_H W3) mem4) HP4 [0; 1; 2]%nat HSa.
  match type of HSa with ?tq -> _ => assert (HRK : tq); [|specialize (HSa HRK); clear HRK] end.
  { cbn [ms_mem restrict mkst].
    repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?U9b, ?U20b, ?U36b; intros a Ha;
    first [ apply (mbyte_of_aview SEGS); apply Hkept4; unfold pPS, pTS, PO_PS, PO_TS, ESTACK, PE_FRAME in *; lia
          | exfalso; lia ]. }
  clear HS. rewrite <- restrict_mkst_fx in HSa. rename HSa into HS. rewrite Q1.
  remember (havoc E 46 (map (getr regs4) CLOB)) as E2 eqn:HE2 in HS.
  assert (HEIa : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD : forall kk, (kk < 46)%nat -> ew E2 kk = ew E kk)
    by (intros kk Hkk; rewrite HE2; apply YN3v.ew_havoc_old; exact Hkk).
  assert (HAEa : env_agree 32 (Ereg (ms_regs ms3) XT) E2)
    by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE]).
  clear HE2.
  assert (SHOKa : sh_ok SEGS KBx [] E2 (mrestrict (w_H W3) mem4)) by apply Forall_nil.
  apply (st_ok_pi_pin_reg' E2 _ _ (10%bv : bv 5) 0) in HS; [| cbn [ms_regs restrict mkst]; exact Hres4 | reflexivity].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end.
  paj_run_tok RUN HS HJ4 SHOKa Espan; [ko_awr |].
  ko_kept HFr UN5. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  rewrite (OLD 2%nat ltac:(cbv; lia)) in P2.
  rewrite (OLD 3%nat ltac:(cbv; lia)) in P3.
  rewrite (OLD 4%nat ltac:(cbv; lia)) in P4.
  rewrite (OLD 8%nat ltac:(cbv; lia)) in P8.
  rewrite (OLD 9%nat ltac:(cbv; lia)) in P9.
  rewrite (OLD 19%nat ltac:(cbv; lia)) in P10.
  rewrite (OLD 40%nat ltac:(cbv; lia)) in P11.
  rewrite (OLD 18%nat ltac:(cbv; lia)) in P18.
  rewrite (OLD 19%nat ltac:(cbv; lia)) in P19.
  rewrite (OLD 20%nat ltac:(cbv; lia)) in P20.
  rewrite (OLD 21%nat ltac:(cbv; lia)) in P21.
  rewrite (OLD 39%nat ltac:(cbv; lia)) in P22.
  rewrite (OLD 23%nat ltac:(cbv; lia)) in P23.
  rewrite (OLD 24%nat ltac:(cbv; lia)) in P24.
  rewrite (OLD 26%nat ltac:(cbv; lia)) in P26.
  rewrite (OLD 27%nat ltac:(cbv; lia)) in P27.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in P2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in P3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in P4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs0 in P8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1 in P9.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in P18.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in P19.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in P20.
  rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in P21.
  rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23 in P23.
  rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in P24.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in P26.
  rewrite (EW 27%nat 27%bv ltac:(unfold A_TEXT; lia) eq_refl), R27 in P27.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in P10.
  rewrite E39 in P22. rewrite E40 in P11.
  rewrite pa_sigma_rd32.
  assert (UNc : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem ms1) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (UN5 a Ha ltac:(tauto)); exact (UNb a Ha Hn)).
  assert (Qsp4 : spZ (ms_regs ms1) = c_sp1 cx)
    by (unfold spZ; rewrite P2; unfold w64; apply unsigned_lit_small; lia).
  assert (HgC4 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms1)) b (p_C cx))
    by (apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem ms1) _ _ _ _ HgC UNc);
        pose proof (PcapEntryKit.p_lens cx); unfold ESTACK in *; lia).
  pose proof (PcapEntryKit.garr8_four _ _ _ (Q + 0) HgC4 ltac:(lia)
    ltac:(pose proof (PcapEntryKit.p_lens cx); lia)) as H4.
  assert (Hbvu : bv_unsigned (getr (ms_regs ms1) 11) = p_swz cx).
  { rewrite P11. destruct (PcapEntryKit.p_swz_01 cx) as [H0 | H1];
    rewrite ?H0, ?H1; vm_compute; reflexivity. }
  eapply SRr_bind.
  { exact (PcapEntryKit.rd32_call B LAWS TL LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms1) _ k (ms_regs ms1) (b + (Q + 0)) b (p_nF cx) _ _ _ _ HJ4
      ltac:(rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity])
      ltac:(rewrite P10; unfold w64; f_equal; lia)
      ltac:(rewrite Qsp4; lia) ltac:(rewrite Qsp4; unfold Rd32.RD32_FRAME, LLVMF_STK; lia)
      ltac:(rewrite Qsp4; lia) Hb3 ltac:(lia) ltac:(lia)
      ltac:(cbn [ms_mem mkst]; exact H4)). }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hres5 & Hsame5 & Hkept5).
  rewrite Qsp4 in Hkept5.
  assert (UNd : PcapEntryKit.mk W3 (ms_mem ms3) mem5 (c_sp1 cx - 2 * ESTACK) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (Hkept5 a Ha ltac:(unfold Rd32.RD32_FRAME, ESTACK in *; lia)); exact (UNc a Ha Hn)).
  assert (Hap : PcapEntryKit.slots_apart cx (c_sp1 cx - 2 * ESTACK) (c_sp1 cx)) by (unfold PcapEntryKit.slots_apart; lia).
  assert (G26 : getr regs5 26 = getr (ms_regs ms1) 26) by (exact (HP5 26 ltac:(unfold acallee_saved; lia))).
  apply (HKT1 cx fp k acc ly3 S3 W3 (mkst regs5 (getr (ms_regs ms1) 1) mem5 (seg_rom SEGS)) md5 HB HJ5 Hfr Hmo).
  split; [| cbn [ms_regs mkst]; rewrite G26, P26; rewrite R26 in HM; exact HM ].
  exists b, h, buf, i, p. cbv zeta. fold Q.
  assert (G2 : getr regs5 2 = getr (ms_regs ms1) 2) by (exact (HP5 2 ltac:(unfold acallee_saved; lia))).
  assert (G3 : getr regs5 3 = getr (ms_regs ms1) 3) by (exact (HP5 3 ltac:(unfold acallee_saved; lia))).
  assert (G4 : getr regs5 4 = getr (ms_regs ms1) 4) by (exact (HP5 4 ltac:(unfold acallee_saved; lia))).
  assert (G8 : getr regs5 8 = getr (ms_regs ms1) 8) by (exact (HP5 8 ltac:(unfold acallee_saved; lia))).
  assert (G9 : getr regs5 9 = getr (ms_regs ms1) 9) by (exact (HP5 9 ltac:(unfold acallee_saved; lia))).
  assert (G18 : getr regs5 18 = getr (ms_regs ms1) 18) by (exact (HP5 18 ltac:(unfold acallee_saved; lia))).
  assert (G19 : getr regs5 19 = getr (ms_regs ms1) 19) by (exact (HP5 19 ltac:(unfold acallee_saved; lia))).
  assert (G20 : getr regs5 20 = getr (ms_regs ms1) 20) by (exact (HP5 20 ltac:(unfold acallee_saved; lia))).
  assert (G21 : getr regs5 21 = getr (ms_regs ms1) 21) by (exact (HP5 21 ltac:(unfold acallee_saved; lia))).
  assert (G22 : getr regs5 22 = getr (ms_regs ms1) 22) by (exact (HP5 22 ltac:(unfold acallee_saved; lia))).
  assert (G23 : getr regs5 23 = getr (ms_regs ms1) 23) by (exact (HP5 23 ltac:(unfold acallee_saved; lia))).
  assert (G24 : getr regs5 24 = getr (ms_regs ms1) 24) by (exact (HP5 24 ltac:(unfold acallee_saved; lia))).
  assert (G27 : getr regs5 27 = getr (ms_regs ms1) 27) by (exact (HP5 27 ltac:(unfold acallee_saved; lia))).
  split.
  { split.
    { eapply (PcapEntryKit.pe_body_keep cx fp PP_U PP_KT1 W3 ms3 (mkst regs5 (getr (ms_regs ms1) 1) mem5 (seg_rom SEGS))
                PSH_ts (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) Hbody).
      - cbn [ms_pc_val mkst]. rewrite P1. reflexivity.
      - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - cbn [ms_regs mkst]. rewrite G2, P2, Rsp. reflexivity.
      - cbn [ms_regs mkst]. rewrite G8, P8, Rs0. reflexivity.
      - cbn [ms_regs mkst]. rewrite G9, P9, Rs1. reflexivity.
      - cbn [ms_regs mkst]. rewrite G3, P3, Rgp. reflexivity.
      - cbn [ms_regs mkst]. rewrite G4, P4, Rtp. reflexivity.
      - cbn [ms_mem mkst]. exact UNd.
      - unfold ESTACK in *; lia.
      - lia.
      - unfold LLVMF_STK; lia.
      - lia.
      - exact Hf0. - exact Hf1. - exact Hinp. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split.
    - rewrite (proj1 (same_but_materialized_fs _ _ Hsame5)).
      repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)).
      rewrite Hfds4. repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)). exact Hfds.
    - rewrite (proj2 (same_but_materialized_fs _ _ Hsame5)).
      repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)).
      rewrite Hfs4. repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)). exact Hfs. }
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HpQ|].
  split; [unfold p_kind; exact Hfit|].
  split.
  { cbn [ms_regs mkst]. rewrite Hres5, (PcapEntryKit.trd32_hw cx Q 0 (getr (ms_regs ms1) 11) Hbvu). reflexivity. }
  split; [cbn [ms_regs mkst]; rewrite G18; exact P18|].
  split; [cbn [ms_regs mkst]; rewrite G19; exact P19|].
  split; [cbn [ms_regs mkst]; rewrite G20; exact P20|].
  split; [cbn [ms_regs mkst]; rewrite G21; exact P21|].
  split; [cbn [ms_regs mkst]; rewrite G22; exact P22|].
  split; [cbn [ms_regs mkst]; rewrite G23; exact P23|].
  split; [cbn [ms_regs mkst]; rewrite G24; exact P24|].
  split; [cbn [ms_regs mkst]; rewrite G26; exact P26|].
  split; [cbn [ms_regs mkst]; rewrite G27; exact P27|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.p_lslots_keep cx fp W3 ms3 (mkst regs5 (getr (ms_regs ms1) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) buf
                   (conj Hsl (conj Hslbuf (conj Hslvm (conj Hslb12 Hslus)))) UNd Hap ltac:(lia) ltac:(lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst regs5 (getr (ms_regs ms1) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) _ _ Hcalls UNd Hap ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst regs5 (getr (ms_regs ms1) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) _ _ Hfirst UNd Hap ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst]; exact (PcapEntryKit.p_glob_keep cx W3 ms3 (mkst regs5 (getr (ms_regs ms1) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) b Hglob UNd ltac:(unfold ESTACK in *; lia))|].
  cbn [ms_mem mkst].
  exact (PcapEntryKit.p_reader_keep B KS ASIL cx fp W3 ms3 (mkst regs5 (getr (ms_regs ms1) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) b h buf p (conj Hsrc (conj (conj Hpf Hpsw) Hfitr)) UNd
           ltac:(unfold ESTACK in *; lia) Hf0 Hf1 ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).

Qed.

Lemma pe_from_U : pe_from_U_stmt.
Proof.
unfold pe_from_U_stmt. intros POST HKT1.
apply (PcapEntrySkip.pe_from_meas_all B MT KS POST). intros m.
apply (pe_from_U_m m POST). apply (PcapEntrySkip.pe_meas_of B MT KS POST). exact HKT1.
Qed.

(* The measured form: s10 = Q from PP_KO through PP_U to PP_KT1, so the bound m on |F| - s10 passes through
   unchanged. *)
Lemma pe_from_KO_m : forall m POST,
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_KT1 B MT KS) m) ->
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_KO B MT KS) m).
Proof.
intros m POST HKT1.
pose proof (pe_from_U_m m POST HKT1) as HU.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo (HI & HM).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct (PcapEntryKit.rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgpv & Htpv & _).
destruct HI as (b & h & buf & i & p & HI). cbv zeta in HI.
destruct HI as (Hcut & Hn26 & Hgood & Hi0 & Hip & HpQ & Hfit & R10 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25
  & R26 & R27 & Hls & Hcalls & HsN & Hfirst & Hglob & Hrd).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
(* the blocks of the cut: the copy, the FILE and the buffer are live, so each lies under the ceiling *)
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hu3 : In (buf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096 & Hbceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR Hh3) as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 buf (p_bn cx) HAR Hu3) as (_ & Hu4096 & Huceil & _).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
assert (Hbncap : p_cap cx <= p_bn cx) by (unfold p_bn; lia).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrq1a Hrq1].
pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as [_ Hrq2].
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [Hrq3a Hrq3].
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
unfold LLVMF_STK in Hspc, Hpres.
assert (Hs1 : 2 ^ 46 <= c_sp1 cx <= 2 ^ 47) by lia.
(* the record: fit, so 0 < incl <= cap and Q + 16 + incl <= |F| *)
unfold p_kind in Hfit.
destruct (PcapEntryKit.kind_fit _ _ _ _ Hfit) as (I1 & I2 & I3 & I4).
fold (p_nF cx) in I3, I4.
assert (HFlen : Z.of_nat (length (p_F cx)) = p_nF cx) by reflexivity.
assert (HQ0 : 24 <= p_q cx p) by lia.
(* the reader's facts *)
destruct Hrd as (Hsrc & (Hpf & Hpsw) & Hfitr).
destruct (Hfitr Hfit) as (Vorig & Vtag & Vvid & Vts & Vbuf).
destruct Hls as (Hsl & Hslbuf & Hslvm & Hslb12 & Hslus).
pose proof Hsl as (S_F0 & S_D & S_SHB & S_SH & S_F & S_FK & S_TSP & S_CAP).
pose proof Hsrc as (Wc & cpos & flc & mdcx & A0 & A1 & A2 & A3 & A4 & A5 & A6 & Hbok & HgC & _).
rewrite PcapEntryKit.p_lens in A2, A3, A4.
set (Q := p_q cx p) in *.
clear A0 A1 A5 A6.
(* the start state *)
assert (Hnv : 0 < p_res cx Q <= 2040).
{ unfold p_res, PSN.res_of, PSN.rec_len. rewrite Hfit.
  destruct (PSN.tagged (p_sw cx) (p_F cx) Q) eqn:Et; [pose proof (PcapEntryKit.tagged_incl _ _ _ Et)|]; split; lia. }
assert (Hts : 0 <= PSN.rec_ts (p_sw cx) (p_F cx) Q < 2 ^ 64)
  by (unfold PSN.rec_ts; pose proof (hw_range (p_sw cx) (p_F cx) Q 0); pose proof (hw_range (p_sw cx) (p_F cx) Q 4); lia).
assert (Hvid : 0 <= (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0) < 2 ^ 16)
  by (destruct (PSN.tagged _ _ _); [unfold PSN.rec_vid; pose proof (Z.mod_pos_bound (256 * PSN.fb (p_F cx) (Q + 30) + PSN.fb (p_F cx) (Q + 31)) 4096 ltac:(lia)); lia | lia]).
assert (Htag : 0 <= (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0) < 2 ^ 32) by (destruct (PSN.tagged _ _ _); lia).
pose proof (ko_entry cx fp PP_KO W3 ms3 (b + Q) buf (p_res cx Q) _ _ _
  (PSN.fb (p_F cx) (Q + 28)) (PSN.fb (p_F cx) (Q + 29)) (PSN.fb (p_F cx) (Q + 30)) (PSN.fb (p_F cx) (Q + 31))
  Rs1 R19 R20 Hpc Hrv Hsv Hrom Hfreg Hfcsr Hs1 Hal32 ltac:(lia) Hf0 Hf1 ltac:(lia) ltac:(lia) ltac:(lia) Htag Hvid Hts
  Hslvm Hslb12 S_SHB S_TSP Hslbuf HsN Hpsw Vtag Vvid Vts) as HS.
set (XT := ko_extra buf (p_res cx Q) (pTS cx fp)
  (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0)
  (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0)
  (PSN.rec_ts (p_sw cx) (p_F cx) Q) (p_swz cx)
  (PSN.fb (p_F cx) (Q + 28)) (PSN.fb (p_F cx) (Q + 29)) (PSN.fb (p_F cx) (Q + 30)) (PSN.fb (p_F cx) (Q + 31))) in HS.
remember (Eimg (Ereg (ms_regs ms3) XT)) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall ii, (ii < A_TEXT)%nat -> ew E ii = ew (Ereg (ms_regs ms3) XT) ii)
  by (intros ii Hii; subst E; apply Eimg_low; exact Hii).
assert (EW : forall ii (r : bv 5), (ii < A_TEXT)%nat -> Z.of_nat ii = bv_unsigned r -> ew E ii = getr (ms_regs ms3) r)
  by (intros ii r Hii Hr; rewrite EL by exact Hii; exact (ew_Ereg_nat (ms_regs ms3) _ ii r Hr)).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) XT) E)
  by (split; [intros i' Hi'; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j XT (Z_to_bv 64 0)).
{ intros j Hj. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
clear HEdef.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (buf + 12)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (p_res cx Q)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (pTS cx fp)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0)) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0))
  by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = Z_to_bv 64 (PSN.rec_ts (p_sw cx) (p_F cx) Q)) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E 40 = Z_to_bv 64 (p_swz cx)) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = Z_to_bv 64 (PSN.fb (p_F cx) (Q + 28))) by exact (EX 9%nat ltac:(lia)).
assert (E42 : ew E 42 = Z_to_bv 64 (PSN.fb (p_F cx) (Q + 29))) by exact (EX 10%nat ltac:(lia)).
assert (E43 : ew E 43 = Z_to_bv 64 (PSN.fb (p_F cx) (Q + 30))) by exact (EX 11%nat ltac:(lia)).
assert (E44 : ew E 44 = Z_to_bv 64 (PSN.fb (p_F cx) (Q + 31))) by exact (EX 12%nat ltac:(lia)).
assert (U35 : U E (SOff 35 0) = p_res cx Q) by (apply U_atom; [exact E35 | lia]).
assert (U37 : U E (SOff 37 0) = if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0) by (apply U_atom; [exact E37 | lia]).
assert (U25 : U E (SOff 25 0) = PSN.incl (p_sw cx) (p_F cx) Q).
{ rewrite U_SOff, (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25. unfold p_hw. fold (PSN.incl (p_sw cx) (p_F cx) Q).
  unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
pose proof (PcapEntryKit.bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (PcapEntryKit.bpaj_run_to_x B LAWS pe_G HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
assert (SHOK0 : sh_ok SEGS KBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
(* 0x80bfc `bne s6,a0`: s6 = ps.last_orig_len (0x80bf0) and a0 = rd32 of orig_len (0x80bf8), the same word *)
psrr_branch_tok RUN BR HS SHOK0 Espan.
{ exfalso. rewrite branch_ne_U in Hc.
  assert (U22 : U E (SOff 22 0) = U E (SOff 10 0)).
  { rewrite !U_SOff, (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl), (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R22, R10.
    unfold p_hw, PSN.orig. reflexivity. }
  rewrite U22, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK0 Espan; [ko_awr |].
ko_kept HFr UN1. clear HF HFr HG.
assert (U27 : U E (SOff 27 0) = PSN.incl (p_sw cx) (p_F cx) Q).
{ rewrite U_SOff, (EW 27%nat 27%bv ltac:(unfold A_TEXT; lia) eq_refl), R27. unfold p_hw. fold (PSN.incl (p_sw cx) (p_F cx) Q).
  rewrite Rd32.rd_swrap32_small by lia. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
(* 0x80c08 `bltu s11,a0(=18)`: the VLAN-tag test, incl < 18 *)
psrr_branch_tok RUN BR HS SHOK0 Espan.
- rewrite branch_ltu_U, U27, U_lit in Hc by lia. apply Z.ltb_lt in Hc.
  assert (Etag : PSN.tagged (p_sw cx) (p_F cx) Q = false)
    by (destruct (PSN.tagged _ _ _) eqn:Et; [pose proof (PcapEntryKit.tagged_incl _ _ _ Et); lia | reflexivity]).
  paj_run_tok RUN HS HJ SHOK0 Espan; [ko_awr |].
  ko_kept HFr UN2. clear HF HFr HG.
  (* 0x80c6c `bne a1,a0`: a1 = ps.last_vlan_tagged (0x80c68) = 0, a0 = 0 (0x80c64) *)
  psrr_branch_tok RUN BR HS SHOK0 Espan.
  { exfalso. rewrite branch_ne_U, (U_sext32_small E _ 0) in Hc0; [| rewrite U37, Etag; reflexivity | lia].
    rewrite U_lit in Hc0 by lia. discriminate Hc0. }
  clear Hc0.
  (* 0x80c70 `beqz a0` -> the untagged arm at PP_U *)
  paj_run_to_tok RUNTO HS HJ SHOK0 Espan PP_U; [ko_awr |].
  ko_kept HFr UNk. clear HF HFr HG.
  assert (UNu : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem ms1) alloc_ceiling alloc_ceiling)
    by (intros a Ha Hn; rewrite (UNk a Ha ltac:(tauto)), (UN2 a Ha ltac:(tauto)); exact (UN1 a Ha ltac:(tauto))).
  assert (Hapu : PcapEntryKit.slots_apart cx alloc_ceiling alloc_ceiling) by (unfold PcapEntryKit.slots_apart; lia).
  pmkst HS.
  prreg HS (2%bv : bv 5) T2.
  prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18.
  prreg HS (19%bv : bv 5) T19.
  prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22.
  prreg HS (23%bv : bv 5) T23.
  prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25.
  prreg HS (26%bv : bv 5) T26.
  prreg HS (27%bv : bv 5) T27.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in T18.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in T19.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in T20.
  rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in T21.
  rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23 in T23.
  rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in T24.
  rewrite (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25 in T25.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in T26.
  rewrite (EW 27%nat 27%bv ltac:(unfold A_TEXT; lia) eq_refl), R27 in T27.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in T2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in T3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in T4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs0 in T8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1 in T9.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in T22.
  apply (HU cx fp k acc ly3 S3 W3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms1) (seg_rom SEGS)) _ HB HJ Hfr Hmo).
  split; [| cbn [ms_regs mkst]; rewrite T26; rewrite R26 in HM; exact HM ].
  exists b, h, buf, i, p. cbv zeta. fold Q.
  split.
  { split.
    { eapply (PcapEntryKit.pe_body_keep cx fp PP_KO PP_U W3 ms3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms1) (seg_rom SEGS)) PSH_ts alloc_ceiling alloc_ceiling Hbody).
      - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - cbn [ms_regs mkst]. rewrite T2, Rsp. reflexivity.
      - cbn [ms_regs mkst]. rewrite T8, Rs0. reflexivity.
      - cbn [ms_regs mkst]. rewrite T9, Rs1. reflexivity.
      - cbn [ms_regs mkst]. rewrite T3, Rgp. reflexivity.
      - cbn [ms_regs mkst]. rewrite T4, Rtp. reflexivity.
      - cbn [ms_mem mkst]. exact UNu.
      - lia. - lia. - unfold LLVMF_STK; lia. - lia. - exact Hf0. - exact Hf1. - exact Hinp. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)); exact Hfds
           | repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HpQ|].
  split; [unfold p_kind; exact Hfit|]. split; [exact Etag|].
  split; [cbn [ms_regs mkst]; exact T18|]. split; [cbn [ms_regs mkst]; exact T19|].
  split; [cbn [ms_regs mkst]; exact T20|]. split; [cbn [ms_regs mkst]; exact T21|].
  split; [cbn [ms_regs mkst]; rewrite T22; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [cbn [ms_regs mkst]; exact T23|]. split; [cbn [ms_regs mkst]; exact T24|].
  split; [cbn [ms_regs mkst]; exact T25|]. split; [cbn [ms_regs mkst]; exact T26|].
  split; [cbn [ms_regs mkst]; exact T27|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.p_lslots_keep cx fp W3 ms3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms1) (seg_rom SEGS)) alloc_ceiling alloc_ceiling buf
                   (conj Hsl (conj Hslbuf (conj Hslvm (conj Hslb12 Hslus)))) UNu Hapu ltac:(lia) ltac:(lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms1) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ Hcalls UNu Hapu
                   ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep cx W3 ms3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms1) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ HsN UNu
                   ltac:(unfold PS_N; lia) ltac:(unfold PS_N; lia) ltac:(unfold PS_N; lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms1) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ Hfirst UNu Hapu
                   ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst]; exact (PcapEntryKit.p_glob_keep cx W3 ms3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms1) (seg_rom SEGS)) alloc_ceiling alloc_ceiling b Hglob UNu ltac:(lia))|].
  cbn [ms_mem mkst].
  exact (PcapEntryKit.p_reader_keep B KS ASIL cx fp W3 ms3 (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms1) (seg_rom SEGS)) alloc_ceiling alloc_ceiling b h buf p
           (conj Hsrc (conj (conj Hpf Hpsw) Hfitr)) UNu ltac:(lia) Hf0 Hf1 ltac:(lia)
           ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
- (* incl >= 18: the VLAN-tag candidate. The two bytes at rec + 12, rec + 13 (= b + Q + 28, b + Q + 29) are inside
     the copy, so the region ko_bytes and the shadow entry ko_SH can be added here. *)
  rewrite branch_ltu_U, U27, U_lit in Hc by lia. apply Z.ltb_ge in Hc.
  assert (HQ32 : Q + 32 <= p_nF cx) by lia.
  assert (U19' : bv_unsigned (ew E 19) = b + Q)
    by (rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19; apply unsigned_lit_small; lia).
  assert (U32' : U E (SOff 32 0) = SHADOW_OFF)
    by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
  assert (U9' : bv_unsigned (ew E 9) = c_sp1 cx)
    by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
  assert (U20' : bv_unsigned (ew E 20) = pPS cx fp)
    by (rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20; apply unsigned_lit_small;
        unfold pPS, PO_PS, PE_FRAME in *; lia).
  assert (U36' : bv_unsigned (ew E 36) = pTS cx fp)
    by (rewrite E36; apply unsigned_lit_small; unfold pTS, PO_TS, PE_FRAME in *; lia).
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (UNx : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem msx) alloc_ceiling alloc_ceiling)
      by (intros a Ha Hn; exact (UN1 a Ha ltac:(tauto)));
    assert (HgCx : garr8 SEGS (mrestrict (w_H W3) (ms_mem msx)) b (p_C cx))
      by (apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem msx) _ _ _ _ HgC UNx); pose proof (PcapEntryKit.p_lens cx); lia);
    assert (HBY : forall j, 0 <= j < 4 ->
      val_mem SEGS (mrestrict (w_H W3) (ms_mem msx)) (b + Q + 28 + j) 1 (PSN.fb (p_F cx) (Q + 28 + j)));
    [ intros j Hj;
      destruct (garr8_nthZ SEGS (mrestrict (w_H W3) (ms_mem msx)) b (p_C cx) (Q + 28 + j) HgCx
        ltac:(lia) ltac:(pose proof (PcapEntryKit.p_lens cx); lia)) as [V R];
      unfold p_C in V; rewrite nth_map_u in V; rewrite !Z.add_assoc in V; exact V | ] end.
  (* the region of the four bytes rec + 12 .. rec + 15, and the shadow entry that covers them *)
  assert (RGB : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) ko_bytes).
  { unfold ko_bytes, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19'. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS E _ (b + Q) 28 1 (SOff 41 0) (PSN.fb (p_F cx) (Q + 28)));
      [ cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold PSN.fb; pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 28)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; cbn; lia | cbn; lia |].
      pose proof (HBY 0 ltac:(lia)) as V. rewrite !Z.add_0_r in V. exact V.
    - apply (chunk_ok_val SEGS E _ (b + Q) 29 1 (SOff 42 0) (PSN.fb (p_F cx) (Q + 29)));
      [ cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold PSN.fb; pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; cbn; lia | cbn; lia |].
      pose proof (HBY 1 ltac:(lia)) as V. replace (Q + 28 + 1) with (Q + 29) in V by lia.
      replace (b + Q + 29) with (b + Q + 28 + 1) by lia. exact V.
    - apply (chunk_ok_val SEGS E _ (b + Q) 30 1 (SOff 43 0) (PSN.fb (p_F cx) (Q + 30)));
      [ cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold PSN.fb; pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 30)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; cbn; lia | cbn; lia |].
      pose proof (HBY 2 ltac:(lia)) as V. replace (Q + 28 + 2) with (Q + 30) in V by lia.
      replace (b + Q + 30) with (b + Q + 28 + 2) by lia. exact V.
    - apply (chunk_ok_val SEGS E _ (b + Q) 31 1 (SOff 44 0) (PSN.fb (p_F cx) (Q + 31)));
      [ cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold PSN.fb; pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 31)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; cbn; lia | cbn; lia |].
      pose proof (HBY 3 ltac:(lia)) as V. replace (Q + 28 + 3) with (Q + 31) in V by lia.
      replace (b + Q + 31) with (b + Q + 28 + 3) by lia. exact V. }
  assert (DISJB : all_disjoint E ko_bytes ko_regions).
  { pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) PE_CID fp HAR Hb3
      ltac:(rewrite Hfr; left; reflexivity)) as Hsep.
    assert (EFa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
    rewrite EFa in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    change (fs_frame_bytes PE_CID) with 128 in Hsep.
    apply all_disjoint_of_extents.
    unfold ko_bytes, ko_regions, ko_slots, ko_ps, ko_ts, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19'. rewrite U9', U20', U36'.
    cbn [zall_disjoint]. unfold zdisj, pPS, pTS, PO_PS, PO_TS. cbn [fst snd].
    unfold PE_FRAME in *. repeat split; lia. }
  pose proof (st_ok_pi_add_region E _ _ ko_bytes HS ltac:(vm_compute; reflexivity) RGB DISJB) as HSb.
  clear HS. rename HSb into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & _ & _ & Hbapp & _).
  assert (U19u : U E (SOff 19 0) = b + Q)
    by (rewrite U_SOff, U19', Z.add_0_r; apply zcanon_id; unfold M64; lia).
  pose proof HJ as (_ & _ & (memSt & HJit & _) & _). rewrite !Z.add_0_r in HJit.
  pose proof HJit as (HARt & _).
  (* the shadow entry of rec + 12 .. rec + 15: the copy block's shadow marks [b, b + |F|) addressable and
     b + Q + 32 <= b + |F| (HQ32, from incl >= 18) *)
  assert (SHOK1 : sh_ok SEGS KBx ko_SH E (mrestrict (w_H W3) (ms_mem ms))).
  { unfold sh_ok, ko_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms) E KBx 19%nat (b + Q + 28) 4 (b + Q) 28 32).
    - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ b (p_nF cx) (b + Q + 28) 4
               HARt Hb3 ltac:(lia) ltac:(lia)).
    - unfold KBx. exact U32'.
    - exact U19u.
    - lia.
    - lia.
    - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
  (* 0x80c0c .. 0x80c34: the guard 0x80c10 (rec + 12 does not wrap: s3's range), the shadow check of rec + 12
     (0x80c14 .. 0x80c28, FORM B from SHOK1), the byte 0x80c2c, and the test `bne a0,0x81` 0x80c34 *)
  paj_run_tok RUN HS HJ SHOK1 Espan; [ko_awr |].
  ko_kept HFr UNt. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK1 Espan.
  { (* F[Q+28] <> 0x81: not tagged; join the untagged arm at PP_U *)
    lazymatch goal with Hcx : Sem.branch_taken _ (sv_denot ?EV _) _ = true |- _ =>
      assert (U41 : U EV (SExt false 8 (SOff 41 0)) = PSN.fb (p_F cx) (Q + 28));
      [ rewrite U_zext; change (2 ^ Z.of_N 8) with 256;
        rewrite (U_atom EV 41%nat (PSN.fb (p_F cx) (Q + 28)) ltac:(cbn [ew ewset Nat.eqb]; exact E41) ltac:(unfold PSN.fb;
          pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 28)) (p_F cx) (Z_to_bv 8 0))) as HR;
          change (bv_modulus 8) with 256 in HR; lia));
        apply Z.mod_small; unfold PSN.fb;
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 28)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; lia
      | rewrite branch_ne_U, U41, U_lit in Hcx by lia; apply negb_true_iff, Z.eqb_neq in Hcx;
        assert (Etag : PSN.tagged (p_sw cx) (p_F cx) Q = false)
          by (unfold PSN.tagged; apply andb_false_iff; left; apply andb_false_iff; right;
              apply Z.eqb_neq; exact Hcx) ] end.
    paj_run_tok RUN HS HJ SHOK1 Espan; [ko_awr |].
    ko_kept HFr UNt2. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK1 Espan;
    [ exfalso;
      lazymatch goal with Hcx : Sem.branch_taken _ (sv_denot ?EV _) _ = true |- _ =>
        assert (U37x : U EV (SOff 37 0) = 0);
        [ rewrite (U_atom EV 37%nat (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0)
            ltac:(cbn [ew ewset Nat.eqb]; exact E37) ltac:(destruct (PSN.tagged _ _ _); lia));
          rewrite Etag; reflexivity
        | rewrite branch_ne_U, (U_sext32_small EV _ 0 U37x ltac:(lia)), U_lit in Hcx by lia;
          discriminate Hcx ] end
    | ].
  paj_run_to_tok RUNTO HS HJ SHOK1 Espan PP_U; [ko_awr |].
  ko_kept HFr UNk. clear HF HFr HG.
  assert (UNu : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem ms2) alloc_ceiling alloc_ceiling)
    by (intros a Ha Hn; rewrite (UNk a Ha ltac:(tauto)), (UNt2 a Ha ltac:(tauto)), (UNt a Ha ltac:(tauto)); exact (UNx a Ha ltac:(lia))).
  assert (Hapu : PcapEntryKit.slots_apart cx alloc_ceiling alloc_ceiling) by (unfold PcapEntryKit.slots_apart; lia).
  pmkst HS.
  prreg HS (2%bv : bv 5) T2.
  prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18.
  prreg HS (19%bv : bv 5) T19.
  prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22.
  prreg HS (23%bv : bv 5) T23.
  prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25.
  prreg HS (26%bv : bv 5) T26.
  prreg HS (27%bv : bv 5) T27.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in T18.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in T19.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in T20.
  rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in T21.
  rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23 in T23.
  rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in T24.
  rewrite (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25 in T25.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in T26.
  rewrite (EW 27%nat 27%bv ltac:(unfold A_TEXT; lia) eq_refl), R27 in T27.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in T2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in T3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in T4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs0 in T8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1 in T9.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in T22.
  apply (HU cx fp k acc ly3 S3 W3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms2) (seg_rom SEGS)) _ HB HJ Hfr Hmo).
  split; [| cbn [ms_regs mkst]; rewrite T26; rewrite R26 in HM; exact HM ].
  exists b, h, buf, i, p. cbv zeta. fold Q.
  split.
  { split.
    { eapply (PcapEntryKit.pe_body_keep cx fp PP_KO PP_U W3 ms3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms2) (seg_rom SEGS)) PSH_ts alloc_ceiling alloc_ceiling Hbody).
      - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - cbn [ms_regs mkst]. rewrite T2, Rsp. reflexivity.
      - cbn [ms_regs mkst]. rewrite T8, Rs0. reflexivity.
      - cbn [ms_regs mkst]. rewrite T9, Rs1. reflexivity.
      - cbn [ms_regs mkst]. rewrite T3, Rgp. reflexivity.
      - cbn [ms_regs mkst]. rewrite T4, Rtp. reflexivity.
      - cbn [ms_mem mkst]. exact UNu.
      - lia. - lia. - unfold LLVMF_STK; lia. - lia. - exact Hf0. - exact Hf1. - exact Hinp. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)); exact Hfds
           | repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HpQ|].
  split; [unfold p_kind; exact Hfit|]. split; [exact Etag|].
  split; [cbn [ms_regs mkst]; exact T18|]. split; [cbn [ms_regs mkst]; exact T19|].
  split; [cbn [ms_regs mkst]; exact T20|]. split; [cbn [ms_regs mkst]; exact T21|].
  split; [cbn [ms_regs mkst]; rewrite T22; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [cbn [ms_regs mkst]; exact T23|]. split; [cbn [ms_regs mkst]; exact T24|].
  split; [cbn [ms_regs mkst]; exact T25|]. split; [cbn [ms_regs mkst]; exact T26|].
  split; [cbn [ms_regs mkst]; exact T27|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.p_lslots_keep cx fp W3 ms3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms2) (seg_rom SEGS)) alloc_ceiling alloc_ceiling buf
                   (conj Hsl (conj Hslbuf (conj Hslvm (conj Hslb12 Hslus)))) UNu Hapu ltac:(lia) ltac:(lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms2) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ Hcalls UNu Hapu
                   ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep cx W3 ms3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms2) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ HsN UNu
                   ltac:(unfold PS_N; lia) ltac:(unfold PS_N; lia) ltac:(unfold PS_N; lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms2) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ Hfirst UNu Hapu
                   ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst]; exact (PcapEntryKit.p_glob_keep cx W3 ms3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms2) (seg_rom SEGS)) alloc_ceiling alloc_ceiling b Hglob UNu ltac:(lia))|].
  cbn [ms_mem mkst].
  exact (PcapEntryKit.p_reader_keep B KS ASIL cx fp W3 ms3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms2) (seg_rom SEGS)) alloc_ceiling alloc_ceiling b h buf p
           (conj Hsrc (conj (conj Hpf Hpsw) Hfitr)) UNu ltac:(lia) Hf0 Hf1 ltac:(lia)
           ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* F[Q+28] = 0x81: the first tag byte matches; the second byte decides *)
  lazymatch goal with Hcx : Sem.branch_taken _ (sv_denot ?EV _) _ = false |- _ =>
    assert (U41 : U EV (SExt false 8 (SOff 41 0)) = PSN.fb (p_F cx) (Q + 28));
    [ rewrite U_zext; change (2 ^ Z.of_N 8) with 256;
      rewrite (U_atom EV 41%nat (PSN.fb (p_F cx) (Q + 28)) ltac:(cbn [ew ewset Nat.eqb]; exact E41) ltac:(unfold PSN.fb;
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 28)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; lia));
      apply Z.mod_small; unfold PSN.fb;
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 28)) (p_F cx) (Z_to_bv 8 0))) as HR;
      change (bv_modulus 8) with 256 in HR; lia
    | rewrite branch_ne_U, U41, U_lit in Hcx by lia; apply negb_false_iff, Z.eqb_eq in Hcx;
      assert (Hb28 : PSN.fb (p_F cx) (Q + 28) = 129) by exact Hcx ] end.
  assert (Etagv : PSN.tagged (p_sw cx) (p_F cx) Q = (PSN.fb (p_F cx) (Q + 29) =? 0)).
  { unfold PSN.tagged. rewrite Hb28.
    replace (18 <=? PSN.incl (p_sw cx) (p_F cx) Q) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity. }
  (* 0x80c38 .. 0x80c6c: the guard 0x80c3c, the shadow check of rec + 13 (0x80c40 .. 0x80c54, FORM B from SHOK1),
     the byte 0x80c58, seqz 0x80c5c, ps.last_vlan_tagged 0x80c68, and the test 0x80c6c *)
  paj_run_tok RUN HS HJ SHOK1 Espan; [ko_awr |].
  ko_kept HFr UNt3. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK1 Espan.
  { (* the tag flag ps.last_vlan_tagged agrees with the two bytes: the abort is refuted *)
    exfalso.
    lazymatch goal with Hcx : Sem.branch_taken _ (sv_denot ?EV _) _ = true |- _ =>
      assert (U42 : U EV (SExt false 8 (SOff 42 0)) = PSN.fb (p_F cx) (Q + 29));
      [ rewrite U_zext; change (2 ^ Z.of_N 8) with 256;
        rewrite (U_atom EV 42%nat (PSN.fb (p_F cx) (Q + 29)) ltac:(cbn [ew ewset Nat.eqb]; exact E42) ltac:(unfold PSN.fb;
          pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
          change (bv_modulus 8) with 256 in HR; lia));
        apply Z.mod_small; unfold PSN.fb;
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; lia
      | ];
      assert (U37x : U EV (SOff 37 0) = (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0))
        by (apply U_atom; [cbn [ew ewset Nat.eqb]; exact E37 | destruct (PSN.tagged _ _ _); lia]);
      assert (URHS : U EV (SAlu Instr.ALU_SLTU (SExt false 8 (SOff 42 0)) (SLit 1))
                     = (if PSN.fb (p_F cx) (Q + 29) =? 0 then 1 else 0));
      [ rewrite U_SAlu, U42, (U_lit EV 1 ltac:(lia)); cbn [zalu_raw];
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; unfold PSN.fb;
        destruct (Z.ltb_spec (bv_unsigned (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) 1);
        destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) 0);
        try lia; rewrite zcanon_id by (unfold M64; lia); reflexivity
      | ];
      rewrite branch_ne_U,
        (U_sext32_small EV (SOff 37 0) _ U37x ltac:(destruct (PSN.tagged _ _ _); lia)), URHS, <- Etagv,
        Z.eqb_refl in Hcx;
      discriminate Hcx end. }
  paj_run_tok RUN HS HJ SHOK1 Espan; [ko_awr |].
  ko_kept HFr UNt4. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK1 Espan.
  { (* F[Q+29] <> 0: not tagged after all; join the untagged arm at PP_U *)
    lazymatch goal with Hcx : Sem.branch_taken _ (sv_denot ?EV _) _ = true |- _ =>
      assert (U42 : U EV (SExt false 8 (SOff 42 0)) = PSN.fb (p_F cx) (Q + 29));
      [ rewrite U_zext; change (2 ^ Z.of_N 8) with 256;
        rewrite (U_atom EV 42%nat (PSN.fb (p_F cx) (Q + 29)) ltac:(cbn [ew ewset Nat.eqb]; exact E42) ltac:(unfold PSN.fb;
          pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
          change (bv_modulus 8) with 256 in HR; lia));
        apply Z.mod_small; unfold PSN.fb;
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; lia
      | ];
      assert (URHS : U EV (SAlu Instr.ALU_SLTU (SExt false 8 (SOff 42 0)) (SLit 1))
                     = (if PSN.fb (p_F cx) (Q + 29) =? 0 then 1 else 0));
      [ rewrite U_SAlu, U42, (U_lit EV 1 ltac:(lia)); cbn [zalu_raw];
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; unfold PSN.fb;
        destruct (Z.ltb_spec (bv_unsigned (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) 1);
        destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) 0);
        try lia; rewrite zcanon_id by (unfold M64; lia); reflexivity
      | ];
      rewrite branch_eq_U, URHS, (U_lit EV 0 ltac:(lia)) in Hcx;
      assert (Etag : PSN.tagged (p_sw cx) (p_F cx) Q = false);
      [ rewrite Etagv; destruct (PSN.fb (p_F cx) (Q + 29) =? 0); [discriminate Hcx | reflexivity] | ] end.
  paj_run_to_tok RUNTO HS HJ SHOK1 Espan PP_U; [ko_awr |].
  ko_kept HFr UNk. clear HF HFr HG.
  assert (UNu : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem ms4) alloc_ceiling alloc_ceiling)
    by (intros a Ha Hn; rewrite (UNk a Ha ltac:(tauto)), (UNt4 a Ha ltac:(tauto)), (UNt3 a Ha ltac:(tauto)), (UNt a Ha ltac:(tauto)); exact (UNx a Ha ltac:(lia))).
  assert (Hapu : PcapEntryKit.slots_apart cx alloc_ceiling alloc_ceiling) by (unfold PcapEntryKit.slots_apart; lia).
  pmkst HS.
  prreg HS (2%bv : bv 5) T2.
  prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18.
  prreg HS (19%bv : bv 5) T19.
  prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22.
  prreg HS (23%bv : bv 5) T23.
  prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25.
  prreg HS (26%bv : bv 5) T26.
  prreg HS (27%bv : bv 5) T27.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in T18.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in T19.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in T20.
  rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in T21.
  rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23 in T23.
  rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in T24.
  rewrite (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25 in T25.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in T26.
  rewrite (EW 27%nat 27%bv ltac:(unfold A_TEXT; lia) eq_refl), R27 in T27.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in T2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in T3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in T4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs0 in T8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1 in T9.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in T22.
  apply (HU cx fp k acc ly3 S3 W3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms4) (seg_rom SEGS)) _ HB HJ Hfr Hmo).
  split; [| cbn [ms_regs mkst]; rewrite T26; rewrite R26 in HM; exact HM ].
  exists b, h, buf, i, p. cbv zeta. fold Q.
  split.
  { split.
    { eapply (PcapEntryKit.pe_body_keep cx fp PP_KO PP_U W3 ms3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms4) (seg_rom SEGS)) PSH_ts alloc_ceiling alloc_ceiling Hbody).
      - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - cbn [ms_regs mkst]. rewrite T2, Rsp. reflexivity.
      - cbn [ms_regs mkst]. rewrite T8, Rs0. reflexivity.
      - cbn [ms_regs mkst]. rewrite T9, Rs1. reflexivity.
      - cbn [ms_regs mkst]. rewrite T3, Rgp. reflexivity.
      - cbn [ms_regs mkst]. rewrite T4, Rtp. reflexivity.
      - cbn [ms_mem mkst]. exact UNu.
      - lia. - lia. - unfold LLVMF_STK; lia. - lia. - exact Hf0. - exact Hf1. - exact Hinp. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)); exact Hfds
           | repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HpQ|].
  split; [unfold p_kind; exact Hfit|]. split; [exact Etag|].
  split; [cbn [ms_regs mkst]; exact T18|]. split; [cbn [ms_regs mkst]; exact T19|].
  split; [cbn [ms_regs mkst]; exact T20|]. split; [cbn [ms_regs mkst]; exact T21|].
  split; [cbn [ms_regs mkst]; rewrite T22; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [cbn [ms_regs mkst]; exact T23|]. split; [cbn [ms_regs mkst]; exact T24|].
  split; [cbn [ms_regs mkst]; exact T25|]. split; [cbn [ms_regs mkst]; exact T26|].
  split; [cbn [ms_regs mkst]; exact T27|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.p_lslots_keep cx fp W3 ms3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms4) (seg_rom SEGS)) alloc_ceiling alloc_ceiling buf
                   (conj Hsl (conj Hslbuf (conj Hslvm (conj Hslb12 Hslus)))) UNu Hapu ltac:(lia) ltac:(lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms4) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ Hcalls UNu Hapu
                   ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep cx W3 ms3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms4) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ HsN UNu
                   ltac:(unfold PS_N; lia) ltac:(unfold PS_N; lia) ltac:(unfold PS_N; lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms4) (seg_rom SEGS)) alloc_ceiling alloc_ceiling _ _ Hfirst UNu Hapu
                   ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst]; exact (PcapEntryKit.p_glob_keep cx W3 ms3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms4) (seg_rom SEGS)) alloc_ceiling alloc_ceiling b Hglob UNu ltac:(lia))|].
  cbn [ms_mem mkst].
  exact (PcapEntryKit.p_reader_keep B KS ASIL cx fp W3 ms3 (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms4) (seg_rom SEGS)) alloc_ceiling alloc_ceiling b h buf p
           (conj Hsrc (conj (conj Hpf Hpsw) Hfitr)) UNu ltac:(lia) Hf0 Hf1 ltac:(lia)
           ltac:(unfold SRC_FILE_BLOCK; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* F[Q+29] = 0 and F[Q+28] = 0x81 and incl >= 18: the record IS VLAN-tagged *)
  lazymatch goal with Hcx : Sem.branch_taken _ (sv_denot ?EV _) _ = false |- _ =>
      assert (U42 : U EV (SExt false 8 (SOff 42 0)) = PSN.fb (p_F cx) (Q + 29));
      [ rewrite U_zext; change (2 ^ Z.of_N 8) with 256;
        rewrite (U_atom EV 42%nat (PSN.fb (p_F cx) (Q + 29)) ltac:(cbn [ew ewset Nat.eqb]; exact E42) ltac:(unfold PSN.fb;
          pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
          change (bv_modulus 8) with 256 in HR; lia));
        apply Z.mod_small; unfold PSN.fb;
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; lia
      | ];
      assert (URHS : U EV (SAlu Instr.ALU_SLTU (SExt false 8 (SOff 42 0)) (SLit 1))
                     = (if PSN.fb (p_F cx) (Q + 29) =? 0 then 1 else 0));
      [ rewrite U_SAlu, U42, (U_lit EV 1 ltac:(lia)); cbn [zalu_raw];
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) as HR;
        change (bv_modulus 8) with 256 in HR; unfold PSN.fb;
        destruct (Z.ltb_spec (bv_unsigned (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) 1);
        destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (Q + 29)) (p_F cx) (Z_to_bv 8 0))) 0);
        try lia; rewrite zcanon_id by (unfold M64; lia); reflexivity
      | ];
    rewrite branch_eq_U, URHS, (U_lit EV 0 ltac:(lia)) in Hcx;
    assert (Hb29 : PSN.fb (p_F cx) (Q + 29) = 0);
    [ destruct (Z.eqb_spec (PSN.fb (p_F cx) (Q + 29)) 0); [assumption | cbn in Hcx; discriminate Hcx] | ] end.
  assert (Etag : PSN.tagged (p_sw cx) (p_F cx) Q = true) by (rewrite Etagv, Hb29; reflexivity).
  assert (Hrec4 : p_res cx Q = PSN.incl (p_sw cx) (p_F cx) Q - 4)
    by (unfold p_res, PSN.res_of, PSN.rec_len; rewrite Hfit, Etag; reflexivity).
  paj_run_tok RUN HS HJ SHOK1 Espan; [ko_awr |].
  ko_kept HFr UNv1. clear HF HFr HG.
  (* 0x80c84 `bne a1,a0`: n = rec_len = incl - 4 for a tagged record, a0 = (incl - 4) zero-extended (0x80c74..0x80c7c) *)
  psrr_branch_tok RUN BR HS SHOK1 Espan.
  { exfalso.
    lazymatch goal with Hcx : Sem.branch_taken _ (sv_denot ?EV _) _ = true |- _ =>
      assert (U35x : U EV (SOff 35 0) = p_res cx Q)
        by (apply U_atom; [cbn [ew ewset Nat.eqb]; exact E35 | lia]);
      assert (U27x : U EV (SOff 27 0) = PSN.incl (p_sw cx) (p_F cx) Q)
        by (rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite <- U_SOff; exact U27);
      rewrite branch_ne_U, U35x, (U_zext_sub32 EV (SOff 27 0) (PSN.incl (p_sw cx) (p_F cx) Q) 4 (-17179869184)
        U27x ltac:(lia) ltac:(lia) ltac:(lia)), Hrec4, Z.eqb_refl in Hcx;
      discriminate Hcx end. }
  paj_run_tok RUN HS HJ SHOK1 Espan; [ko_awr |].
  ko_kept HFr UNv2. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10.
  prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  rewrite E33 in Q10. rewrite U19' in Q11.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in Q4.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in Q2.
  assert (Qsp : spZ (ms_regs ms5) = c_sp1 cx)
    by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
  assert (UNb0 : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem ms5) alloc_ceiling alloc_ceiling)
    by (intros a Ha Hn; rewrite (UNv2 a Ha ltac:(tauto)), (UNv1 a Ha ltac:(tauto)), (UNt4 a Ha ltac:(tauto)),
          (UNt3 a Ha ltac:(tauto)), (UNt a Ha ltac:(tauto)); exact (UNx a Ha ltac:(lia))).
  pose proof HJ as (_ & _ & (memS5 & HJi5 & _) & _). rewrite !Z.add_0_r in HJi5.
  pose proof HJi5 as (HAR5 & _).
  assert (HgC5 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms5)) b (p_C cx))
    by (apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem ms5) _ _ _ _ HgC UNb0);
        pose proof (PcapEntryKit.p_lens cx); lia).
  destruct (rec_bytes_tagged (p_sw cx) (p_F cx) Q Etag ltac:(lia) ltac:(lia)) as (HRL & HR12 & HRrest).
  assert (Vbuf5 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms5)) buf
                    (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes (p_sw cx) (p_F cx) Q)))
    by (apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem ms5) _ _ _ _ Vbuf UNb0); rewrite ?length_map, ?HRL; lia).
  (* bcmp(buf, rec, 12) 0x80c94: the buffer's first 12 bytes are the record's (PSN.rec_bytes, tagged) *)
  eapply SRr_bind.
  { eapply (bcmp_zero LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms5) _ k (ms_regs ms5) buf (b + Q + 16) 12
      buf (p_bn cx) b (p_nF cx) HJ Q10 ltac:(rewrite Q11; f_equal; lia) Q12 ltac:(lia)
      ltac:(rewrite Qsp; lia) ltac:(rewrite Qsp; unfold ESTACK, LLVMF_STK; lia) ltac:(rewrite Qsp; lia)
      ltac:(rewrite Q3; exact Hgpv) ltac:(rewrite Q4; exact Htpv)
      ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
      HAR5 Hu3 ltac:(lia) ltac:(lia) Hb3 ltac:(lia) ltac:(lia)).
    intros j Hj. symmetry. replace (b + Q + 16 + j) with (b + (Q + 16) + j) by lia.
    apply (aview_eq_of_garr8 W3 (ms_mem ms5) b buf (Q + 16) 12 (p_C cx)
             (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes (p_sw cx) (p_F cx) Q))
             HgC5 Vbuf5 ltac:(lia) ltac:(pose proof (PcapEntryKit.p_lens cx); lia) ltac:(rewrite length_map, HRL; lia));
      [|lia].
    intros jj Hjj. unfold p_C. symmetry. exact (HR12 jj Hjj). }
  cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hres6 & Hfds6 & Hfs6 & Hkept6).
  rewrite Qsp in Hkept6.
  assert (UNb1 : PcapEntryKit.mk W3 (ms_mem ms3) mem6 (c_sp1 cx - 2 * ESTACK) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (Hkept6 a Ha Hn); exact (UNb0 a Ha ltac:(lia))).
  jafter_call_keep_pi HS 46%nat regs6 (mrestrict (w_H W3) mem6) HP6 [0; 1; 2; 3]%nat HSa.
  match type of HSa with ?tq -> _ => assert (HRK : tq); [|specialize (HSa HRK); clear HRK] end.
  { cbn [ms_mem restrict mkst].
    repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb];
    rewrite ?U9', ?U19', ?U20', ?U36'; intros a Ha;
    first [ apply (mbyte_of_aview SEGS); apply Hkept6; unfold pPS, pTS, PO_PS, PO_TS, ESTACK, PE_FRAME in *; lia
          | exfalso; lia ]. }
  clear HS. rewrite <- restrict_mkst_fx in HSa. rename HSa into HS. rewrite Q1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    remember Ex as E2 eqn:HE2 in HS end.
  assert (HEIa : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]).
  assert (OLD : forall kk, (kk < 46)%nat -> ew E2 kk = ew E kk)
    by (intros kk Hkk; rewrite HE2, (YN3v.ew_havoc_old _ _ _ _ Hkk); cbn [ew ewset];
        repeat match goal with |- context [Nat.eqb ?x ?m] => destruct (Nat.eqb_spec x m); [lia|] end; reflexivity).
  clear HE2.
  assert (SHOKa : sh_ok SEGS KBx [] E2 (mrestrict (w_H W3) mem6)) by apply Forall_nil.
  apply (st_ok_pi_pin_reg' E2 _ _ (10%bv : bv 5) 0) in HS; [| cbn [ms_regs restrict mkst]; exact Hres6 | reflexivity].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end.
  (* 0x80c98 `bnez a0` (bcmp returned 0), the guards 0x80ca4 / 0x80cac, and the call of bcmp at 0x80cc4 *)
  paj_run_tok RUN HS HJ6 SHOKa Espan; [ko_awr |].
  ko_kept HFr UNv3. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) Z1. prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4.
  prreg HS (10%bv : bv 5) Z10. prreg HS (11%bv : bv 5) Z11. prreg HS (12%bv : bv 5) Z12.
  lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msy) =>
    pose proof (st_ok_restrict_reg sg Hh Ex ssx msy (12%bv : bv 5) HS) as Z12';
    let e := eval vm_compute in (sr_get (ss_regs ssx) (12%bv : bv 5)) in
    change (sr_get (ss_regs ssx) (12%bv : bv 5)) with e in Z12'; cbn [ms_regs restrict mkst] in Z12' end.
  clear Z12.
  assert (U27y : U E2 (SOff 27 0) = PSN.incl (p_sw cx) (p_F cx) Q)
    by (rewrite U_SOff, OLD by lia; rewrite <- U_SOff; exact U27).
  rewrite (denot_lit_U E2 _), (U_zext_sub32 E2 (SOff 27 0) (PSN.incl (p_sw cx) (p_F cx) Q) 16 (-68719476736)
    U27y ltac:(lia) ltac:(lia) ltac:(lia)) in Z12'.
  rewrite (OLD 34%nat ltac:(lia)), E34 in Z10.
  rewrite (OLD 19%nat ltac:(lia)), U19' in Z11.
  rewrite (OLD 2%nat ltac:(lia)), (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in Z2.
  rewrite (OLD 3%nat ltac:(lia)), (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in Z3.
  rewrite (OLD 4%nat ltac:(lia)), (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in Z4.
  assert (Qsp6 : spZ (ms_regs ms6) = c_sp1 cx)
    by (unfold spZ; rewrite Z2; unfold w64; apply unsigned_lit_small; lia).
  assert (UNb2 : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem ms6) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (UNv3 a Ha ltac:(tauto)); exact (UNb1 a Ha Hn)).
  pose proof HJ6 as (_ & _ & (memS6 & HJi6 & _) & _). rewrite !Z.add_0_r in HJi6.
  pose proof HJi6 as (HAR6 & _).
  assert (HgC6 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms6)) b (p_C cx))
    by (apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem ms6) _ _ _ _ HgC UNb2);
        pose proof (PcapEntryKit.p_lens cx); unfold ESTACK in *; lia).
  assert (Vbuf6 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms6)) buf
                    (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes (p_sw cx) (p_F cx) Q)))
    by (apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem ms6) _ _ _ _ Vbuf UNb2);
        rewrite ?length_map, ?HRL; unfold ESTACK in *; lia).
  (* bcmp(buf + 12, rec + 16, incl - 16) 0x80cc4: the bytes after the tag *)
  eapply SRr_bind.
  { eapply (bcmp_zero LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms6) _ k (ms_regs ms6) (buf + 12) (b + Q + 32)
      (PSN.incl (p_sw cx) (p_F cx) Q - 16)
      buf (p_bn cx) b (p_nF cx) HJ6 Z10 ltac:(rewrite Z11; f_equal; lia)
      ltac:(rewrite Z12'; reflexivity) ltac:(lia)
      ltac:(rewrite Qsp6; lia) ltac:(rewrite Qsp6; unfold ESTACK, LLVMF_STK; lia) ltac:(rewrite Qsp6; lia)
      ltac:(rewrite Z3; exact Hgpv) ltac:(rewrite Z4; exact Htpv)
      ltac:(rewrite Z1; apply ret_ok_codeptr_v; [lia | reflexivity])
      HAR6 Hu3 ltac:(lia) ltac:(lia) Hb3 ltac:(lia) ltac:(lia)).
    intros j Hj. replace (b + Q + 32 + j) with (b + (Q + 32) + j) by lia.
    apply (aview_eq_of_garr8_2 W3 (ms_mem ms6) buf b 12 (Q + 32) (PSN.incl (p_sw cx) (p_F cx) Q - 16)
             (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes (p_sw cx) (p_F cx) Q)) (p_C cx)
             Vbuf6 HgC6 ltac:(lia) ltac:(lia) ltac:(rewrite length_map, HRL; lia)
             ltac:(pose proof (PcapEntryKit.p_lens cx); lia)); [|lia].
    intros jj Hjj. unfold p_C. exact (HRrest jj Hjj). }
  cbv beta. intros W7 c7 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Hres7 & Hfds7 & Hfs7 & Hkept7).
  rewrite Qsp6 in Hkept7.
  assert (UNb3 : PcapEntryKit.mk W3 (ms_mem ms3) mem7 (c_sp1 cx - 2 * ESTACK) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (Hkept7 a Ha Hn); exact (UNb2 a Ha Hn)).
  assert (U9'' : bv_unsigned (ew E2 9) = c_sp1 cx) by (rewrite OLD by lia; exact U9').
  assert (U19'' : bv_unsigned (ew E2 19) = b + Q) by (rewrite OLD by lia; exact U19').
  assert (U20'' : bv_unsigned (ew E2 20) = pPS cx fp) by (rewrite OLD by lia; exact U20').
  assert (U36'' : bv_unsigned (ew E2 36) = pTS cx fp) by (rewrite OLD by lia; exact U36').
  jafter_call_keep_pi HS 62%nat regs7 (mrestrict (w_H W3) mem7) HP7 [0; 1; 2; 3]%nat HSa.
  match type of HSa with ?tq -> _ => assert (HRK : tq); [|specialize (HSa HRK); clear HRK] end.
  { cbn [ms_mem restrict mkst].
    repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?U9'', ?U19'', ?U20'', ?U36''; intros a Ha;
    first [ apply (mbyte_of_aview SEGS); apply Hkept7; unfold pPS, pTS, PO_PS, PO_TS, ESTACK, PE_FRAME in *; lia
          | exfalso; lia ]. }
  clear HS. rewrite <- restrict_mkst_fx in HSa. rename HSa into HS. rewrite Z1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    remember Ex as E3 eqn:HE3 in HS end.
  assert (HEIb : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [assumption | cbv; lia]).
  assert (OLD3 : forall kk, (kk < 46)%nat -> ew E3 kk = ew E kk)
    by (intros kk Hkk; rewrite HE3; rewrite (YN3v.ew_havoc_old _ 62 _ kk) by lia; apply OLD; exact Hkk).
  clear HE3.
  pose proof HJ7 as (_ & _ & (memS7 & HJi7 & _) & _). rewrite !Z.add_0_r in HJi7.
  pose proof HJi7 as (HAR7 & _).
  (* the same shadow entry at the memory after the two bcmp calls (AR of their journal) *)
  assert (SHOKb : sh_ok SEGS KBx ko_SH E3 (mrestrict (w_H W3) mem7)).
  { unfold sh_ok, ko_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) mem7 E3 KBx 19%nat (b + Q + 28) 4 (b + Q) 28 32).
    - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem7 _ b (p_nF cx) (b + Q + 28) 4
               HAR7 Hb3 ltac:(lia) ltac:(lia)).
    - unfold KBx. rewrite U_SOff, OLD3 by lia. rewrite <- U_SOff. exact U32'.
    - rewrite U_SOff, OLD3 by lia. rewrite <- U_SOff. exact U19u.
    - lia.
    - lia.
    - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
  apply (st_ok_pi_pin_reg' E3 _ _ (10%bv : bv 5) 0) in HS; [| cbn [ms_regs restrict mkst]; exact Hres7 | reflexivity].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end.
  (* 0x80cc8 `bnez a0`, the guards 0x80cd0 / 0x80cd8, the shadow checks of rec + 14, rec + 15 (0x80cf4, 0x80d0c)
     and their loads, ps.last_vlan_id (0x80cf0), the VLAN id (0x80d14 .. 0x80d20), up to the test 0x80d24 *)
  paj_run_tok RUN HS HJ7 SHOKb Espan; [ko_awr |].
  ko_kept HFr UNv4. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOKb Espan.
  { (* 0x80d24 `bne a0,a2`: the id the bytes give is ps.last_vlan_id = rec_vid (0x80cf0, mask PS_VMASK = 0xf00) *)
    exfalso.
    lazymatch goal with Hcx : Sem.branch_taken _ (sv_denot ?EV _) _ = true |- _ =>
      assert (Hfb : forall j, 0 <= PSN.fb (p_F cx) j < 256)
        by (intros j; unfold PSN.fb; pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat j) (p_F cx) (Z_to_bv 8 0))) as HR;
            change (bv_modulus 8) with 256 in HR; lia);
      assert (U43 : U EV (SExt false 8 (SOff 43 0)) = PSN.fb (p_F cx) (Q + 30));
      [ rewrite U_zext; change (2 ^ Z.of_N 8) with 256;
        rewrite (U_atom EV 43%nat (PSN.fb (p_F cx) (Q + 30))
          ltac:(cbn [ew ewset Nat.eqb]; rewrite OLD3 by lia; exact E43) ltac:(pose proof (Hfb (Q + 30)); lia));
        apply Z.mod_small; apply Hfb
      | ];
      assert (U44 : U EV (SExt false 8 (SOff 44 0)) = PSN.fb (p_F cx) (Q + 31));
      [ rewrite U_zext; change (2 ^ Z.of_N 8) with 256;
        rewrite (U_atom EV 44%nat (PSN.fb (p_F cx) (Q + 31))
          ltac:(cbn [ew ewset Nat.eqb]; rewrite OLD3 by lia; exact E44) ltac:(pose proof (Hfb (Q + 31)); lia));
        apply Z.mod_small; apply Hfb
      | ];
      assert (U38 : U EV (SExt false 16 (SOff 38 0)) = PSN.rec_vid (p_F cx) Q);
      [ rewrite U_zext; change (2 ^ Z.of_N 16) with 65536;
        rewrite (U_atom EV 38%nat (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0)
          ltac:(cbn [ew ewset Nat.eqb]; rewrite OLD3 by lia; exact E38) ltac:(lia));
        rewrite Etag; apply Z.mod_small; unfold PSN.rec_vid;
        pose proof (Z.mod_pos_bound (256 * PSN.fb (p_F cx) (Q + 30) + PSN.fb (p_F cx) (Q + 31)) 4096 ltac:(lia)); lia
      | ];
      assert (ULHS : U EV (SAlu Instr.ALU_OR (SAlu Instr.ALU_AND (SAlu Instr.ALU_SLL (SExt false 8 (SOff 43 0)) (SLit 8))
                       (SLit 3840)) (SExt false 8 (SOff 44 0))) = PSN.rec_vid (p_F cx) Q);
      [ pose proof (Hfb (Q + 30)) as H30; pose proof (Hfb (Q + 31)) as H31;
        rewrite !U_SAlu, U43, U44, !U_SLit; cbn [zalu_raw];
        rewrite (zcanon_id 8), (zcanon_id 3840) by (unfold M64; lia); change (Z.land 8 63) with 8;
        rewrite Z.shiftl_mul_pow2 by lia;
        rewrite (zcanon_id (PSN.fb (p_F cx) (Q + 30) * 2 ^ 8)) by (unfold M64; lia);
        rewrite (zcanon_id (Z.land (PSN.fb (p_F cx) (Q + 30) * 2 ^ 8) 3840))
          by (pose proof (Z.land_nonneg (PSN.fb (p_F cx) (Q + 30) * 2 ^ 8) 3840) as HN;
              pose proof (Z_land_upper (PSN.fb (p_F cx) (Q + 30) * 2 ^ 8) 3840 ltac:(lia)); unfold M64; lia);
        rewrite vlan_id_bits by lia; unfold PSN.rec_vid;
        apply zcanon_id; unfold M64;
        pose proof (Z.mod_pos_bound (256 * PSN.fb (p_F cx) (Q + 30) + PSN.fb (p_F cx) (Q + 31)) 4096 ltac:(lia)); lia
      | ];
      rewrite branch_ne_U, ULHS, U38, Z.eqb_refl in Hcx; discriminate Hcx end. }
  (* 0x80d28 `j` to the join 0x80d48: &ts, ts, ps.swapped, and the call of rd32 (0x80d58) *)
  paj_run_tok RUN HS HJ7 SHOKb Espan; [ko_awr |].
  ko_kept HFr UNv5. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  rewrite (OLD3 2%nat ltac:(cbv; lia)) in P2.
  rewrite (OLD3 3%nat ltac:(cbv; lia)) in P3.
  rewrite (OLD3 4%nat ltac:(cbv; lia)) in P4.
  rewrite (OLD3 8%nat ltac:(cbv; lia)) in P8.
  rewrite (OLD3 9%nat ltac:(cbv; lia)) in P9.
  rewrite (OLD3 19%nat ltac:(cbv; lia)) in P10.
  rewrite (OLD3 40%nat ltac:(cbv; lia)) in P11.
  rewrite (OLD3 18%nat ltac:(cbv; lia)) in P18.
  rewrite (OLD3 19%nat ltac:(cbv; lia)) in P19.
  rewrite (OLD3 20%nat ltac:(cbv; lia)) in P20.
  rewrite (OLD3 21%nat ltac:(cbv; lia)) in P21.
  rewrite (OLD3 39%nat ltac:(cbv; lia)) in P22.
  rewrite (OLD3 23%nat ltac:(cbv; lia)) in P23.
  rewrite (OLD3 24%nat ltac:(cbv; lia)) in P24.
  rewrite (OLD3 26%nat ltac:(cbv; lia)) in P26.
  rewrite (OLD3 27%nat ltac:(cbv; lia)) in P27.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in P2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in P3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in P4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs0 in P8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1 in P9.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in P18.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in P19.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in P20.
  rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in P21.
  rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23 in P23.
  rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in P24.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in P26.
  rewrite (EW 27%nat 27%bv ltac:(unfold A_TEXT; lia) eq_refl), R27 in P27.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in P10.
  rewrite E39 in P22. rewrite E40 in P11.
  rewrite pa_sigma_rd32.
  assert (UNc : PcapEntryKit.mk W3 (ms_mem ms3) (ms_mem ms8) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (UNv5 a Ha ltac:(tauto)), (UNv4 a Ha ltac:(tauto)); exact (UNb3 a Ha Hn)).
  assert (Qsp4 : spZ (ms_regs ms8) = c_sp1 cx)
    by (unfold spZ; rewrite P2; unfold w64; apply unsigned_lit_small; lia).
  assert (HgC4 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms8)) b (p_C cx))
    by (apply (PcapEntryKit.garr8_keep W3 (ms_mem ms3) (ms_mem ms8) _ _ _ _ HgC UNc);
        pose proof (PcapEntryKit.p_lens cx); unfold ESTACK in *; lia).
  pose proof (PcapEntryKit.garr8_four _ _ _ (Q + 0) HgC4 ltac:(lia)
    ltac:(pose proof (PcapEntryKit.p_lens cx); lia)) as H4.
  assert (Hbvu : bv_unsigned (getr (ms_regs ms8) 11) = p_swz cx).
  { rewrite P11. destruct (PcapEntryKit.p_swz_01 cx) as [H0 | H1];
    rewrite ?H0, ?H1; vm_compute; reflexivity. }
  eapply SRr_bind.
  { exact (PcapEntryKit.rd32_call B LAWS TL LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms8) _ k (ms_regs ms8) (b + (Q + 0)) b (p_nF cx) _ _ _ _ HJ7
      ltac:(rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity])
      ltac:(rewrite P10; unfold w64; f_equal; lia)
      ltac:(rewrite Qsp4; lia) ltac:(rewrite Qsp4; unfold Rd32.RD32_FRAME, LLVMF_STK; lia)
      ltac:(rewrite Qsp4; lia) Hb3 ltac:(lia) ltac:(lia)
      ltac:(cbn [ms_mem mkst]; exact H4)). }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hres5 & Hsame5 & Hkept5).
  rewrite Qsp4 in Hkept5.
  assert (UNd : PcapEntryKit.mk W3 (ms_mem ms3) mem5 (c_sp1 cx - 2 * ESTACK) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (Hkept5 a Ha ltac:(unfold Rd32.RD32_FRAME, ESTACK in *; lia)); exact (UNc a Ha Hn)).
  assert (Hap : PcapEntryKit.slots_apart cx (c_sp1 cx - 2 * ESTACK) (c_sp1 cx)) by (unfold PcapEntryKit.slots_apart; lia).
  assert (G26 : getr regs5 26 = getr (ms_regs ms8) 26) by (exact (HP5 26 ltac:(unfold acallee_saved; lia))).
  apply (HKT1 cx fp k acc ly3 S3 W3 (mkst regs5 (getr (ms_regs ms8) 1) mem5 (seg_rom SEGS)) md5 HB HJ5 Hfr Hmo).
  split; [| cbn [ms_regs mkst]; rewrite G26, P26; rewrite R26 in HM; exact HM ].
  exists b, h, buf, i, p. cbv zeta. fold Q.
  assert (G2 : getr regs5 2 = getr (ms_regs ms8) 2) by (exact (HP5 2 ltac:(unfold acallee_saved; lia))).
  assert (G3 : getr regs5 3 = getr (ms_regs ms8) 3) by (exact (HP5 3 ltac:(unfold acallee_saved; lia))).
  assert (G4 : getr regs5 4 = getr (ms_regs ms8) 4) by (exact (HP5 4 ltac:(unfold acallee_saved; lia))).
  assert (G8 : getr regs5 8 = getr (ms_regs ms8) 8) by (exact (HP5 8 ltac:(unfold acallee_saved; lia))).
  assert (G9 : getr regs5 9 = getr (ms_regs ms8) 9) by (exact (HP5 9 ltac:(unfold acallee_saved; lia))).
  assert (G18 : getr regs5 18 = getr (ms_regs ms8) 18) by (exact (HP5 18 ltac:(unfold acallee_saved; lia))).
  assert (G19 : getr regs5 19 = getr (ms_regs ms8) 19) by (exact (HP5 19 ltac:(unfold acallee_saved; lia))).
  assert (G20 : getr regs5 20 = getr (ms_regs ms8) 20) by (exact (HP5 20 ltac:(unfold acallee_saved; lia))).
  assert (G21 : getr regs5 21 = getr (ms_regs ms8) 21) by (exact (HP5 21 ltac:(unfold acallee_saved; lia))).
  assert (G22 : getr regs5 22 = getr (ms_regs ms8) 22) by (exact (HP5 22 ltac:(unfold acallee_saved; lia))).
  assert (G23 : getr regs5 23 = getr (ms_regs ms8) 23) by (exact (HP5 23 ltac:(unfold acallee_saved; lia))).
  assert (G24 : getr regs5 24 = getr (ms_regs ms8) 24) by (exact (HP5 24 ltac:(unfold acallee_saved; lia))).
  assert (G27 : getr regs5 27 = getr (ms_regs ms8) 27) by (exact (HP5 27 ltac:(unfold acallee_saved; lia))).
  split.
  { split.
    { eapply (PcapEntryKit.pe_body_keep cx fp PP_KO PP_KT1 W3 ms3 (mkst regs5 (getr (ms_regs ms8) 1) mem5 (seg_rom SEGS))
                PSH_ts (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) Hbody).
      - cbn [ms_pc_val mkst]. rewrite P1. reflexivity.
      - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - cbn [ms_regs mkst]. rewrite G2, P2, Rsp. reflexivity.
      - cbn [ms_regs mkst]. rewrite G8, P8, Rs0. reflexivity.
      - cbn [ms_regs mkst]. rewrite G9, P9, Rs1. reflexivity.
      - cbn [ms_regs mkst]. rewrite G3, P3, Rgp. reflexivity.
      - cbn [ms_regs mkst]. rewrite G4, P4, Rtp. reflexivity.
      - cbn [ms_mem mkst]. exact UNd.
      - unfold ESTACK in *; lia.
      - lia.
      - unfold LLVMF_STK; lia.
      - lia.
      - exact Hf0. - exact Hf1. - exact Hinp. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split.
    - rewrite (proj1 (same_but_materialized_fs _ _ Hsame5)).
      repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)).
      rewrite Hfds7. repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)).
      rewrite Hfds6. repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)). exact Hfds.
    - rewrite (proj2 (same_but_materialized_fs _ _ Hsame5)).
      repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)).
      rewrite Hfs7. repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)).
      rewrite Hfs6. repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)). exact Hfs. }
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HpQ|].
  split; [unfold p_kind; exact Hfit|].
  split.
  { cbn [ms_regs mkst]. rewrite Hres5, (PcapEntryKit.trd32_hw cx Q 0 (getr (ms_regs ms8) 11) Hbvu). reflexivity. }
  split; [cbn [ms_regs mkst]; rewrite G18; exact P18|].
  split; [cbn [ms_regs mkst]; rewrite G19; exact P19|].
  split; [cbn [ms_regs mkst]; rewrite G20; exact P20|].
  split; [cbn [ms_regs mkst]; rewrite G21; exact P21|].
  split; [cbn [ms_regs mkst]; rewrite G22; exact P22|].
  split; [cbn [ms_regs mkst]; rewrite G23; exact P23|].
  split; [cbn [ms_regs mkst]; rewrite G24; exact P24|].
  split; [cbn [ms_regs mkst]; rewrite G26; exact P26|].
  split; [cbn [ms_regs mkst]; rewrite G27; exact P27|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.p_lslots_keep cx fp W3 ms3 (mkst regs5 (getr (ms_regs ms8) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) buf
                   (conj Hsl (conj Hslbuf (conj Hslvm (conj Hslb12 Hslus)))) UNd Hap ltac:(lia) ltac:(lia))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst regs5 (getr (ms_regs ms8) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) _ _ Hcalls UNd Hap ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst];
          exact (PcapEntryKit.pslot_keep_apart cx W3 ms3 (mkst regs5 (getr (ms_regs ms8) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) _ _ Hfirst UNd Hap ltac:(lia) ltac:(lia) ltac:(tauto))|].
  split; [cbn [ms_mem mkst]; exact (PcapEntryKit.p_glob_keep cx W3 ms3 (mkst regs5 (getr (ms_regs ms8) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) b Hglob UNd ltac:(unfold ESTACK in *; lia))|].
  cbn [ms_mem mkst].
  exact (PcapEntryKit.p_reader_keep B KS ASIL cx fp W3 ms3 (mkst regs5 (getr (ms_regs ms8) 1) mem5 (seg_rom SEGS)) (c_sp1 cx - 2 * ESTACK) (c_sp1 cx) b h buf p (conj Hsrc (conj (conj Hpf Hpsw) Hfitr)) UNd
           ltac:(unfold ESTACK in *; lia) Hf0 Hf1 ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; lia)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma pe_from_KO : pe_from_KO_stmt.
Proof.
unfold pe_from_KO_stmt. intros POST HKT1.
apply (PcapEntrySkip.pe_from_meas_all B MT KS POST). intros m.
apply (pe_from_KO_m m POST). apply (PcapEntrySkip.pe_meas_of B MT KS POST). exact HKT1.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* KT2: the timestamp test (0x80d8c), ts := ~0 (0x80d98), at := at + 16 + incl (0x80da8) and the loop's           *)
(* pcap_source_next (0x80db8), which returns at PP_KL2.                                                          *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* ---- the stretch's own Section hypotheses ---- *)
(* The read-only window lies below musl's open-file-list head (PcapBase's class, as every pcap walk takes it), for
   PcapBase.arodata_ok_journalP at the call. *)
Context {HRO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* This image's pcap_source_next window. PcapEntryDefs.v, "Stack room at a call of the body", bounds every callee of
   the body by 32368 bytes below s1 (the asan-ubsan pcap_source_next asks 272 + 64 + AFREAD_STK); the stretch is
   stated for any window inside that bound, so it does not depend on the figure's owner. *)
Variable NSTK : Z.
Hypothesis NSTK_OK : 0 <= NSTK <= 32368.
(* The meter laws, for the meter across the call (mle_station). *)
Hypothesis MTL : ameter_laws MT.
(* TAKEN FROM: lib/A/Prog/PcapSourceNextSpec.v tpcap_source_next_specX (a Theorem Labs lane, image-free), applied at this
   call site through a Theorem Labs lane's lib/B/Prog/PcapEntryCalls.v next_call. *)
Hypothesis NEXT : ANX.tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NSTK B MT KS
  (BASE + AF_pcap_source_next).

(* ---- arithmetic and model helpers of the stretch ---- *)

(* `slli a0,a0,0x20; srli a0,a0,0x20` (0x80d80, 0x80d84): the zero-extension of rd32's sign-extended answer
   (PcapEntrySkip.v's w3_zext32, by text). *)
Lemma kt2_zext32 : forall E n v, ew E n = w64 (bv_swrap 32 v) -> 0 <= v < 2 ^ 32 ->
  U E (SAlu Instr.ALU_SRL (SAlu Instr.ALU_SLL (SOff n 0) (SLit 32)) (SLit 32)) = v.
Proof.
intros E n v Hn Hv.
assert (Hu : U E (SOff n 0) = v + (if v <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32)).
{ assert (Hid : forall z, zcanon (zcanon z) = zcanon z) by (intros z; unfold zcanon, M64; apply Zmod_mod).
  unfold U. rewrite denot_SOff, Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit, Hid.
  apply Rd32.rd_sx32. exact Hv. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hu, !(U_lit E 32 ltac:(lia)).
change (Z.land 32 63) with 32. rewrite Z.shiftl_mul_pow2 by lia.
assert (Hm : zcanon ((v + (if v <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32)) * 2 ^ 32) = v * 2 ^ 32).
{ unfold zcanon, M64. destruct (Z.ltb_spec v (2 ^ 31)).
  - rewrite Z.add_0_r. apply Z.mod_small. nia.
  - replace ((v + (2 ^ 64 - 2 ^ 32)) * 2 ^ 32) with (v * 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. nia. }
rewrite Hm. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
apply zcanon_id. unfold M64. lia.
Qed.

(* The timestamp test `bne s6,a0` (0x80d8c) is NOT taken: s6 = rec_ts = sec * 10^6 + usec, s9 = sec * 10^6 and
   a0 = usec (PSN.rec_ts, lib/Prog/pcap_source_struct_next.v). *)
Lemma kt2_ts_same : forall E hw0 hw4,
  ew E 22 = w64 (hw0 * 1000000 + hw4) -> ew E 25 = w64 (hw0 * 1000000) -> ew E 10 = w64 (bv_swrap 32 hw4) ->
  0 <= hw0 < 2 ^ 32 -> 0 <= hw4 < 2 ^ 32 ->
  Sem.branch_taken Instr.BC_NE (sv_denot E (SOff 22 0))
    (sv_denot E (SAlu Instr.ALU_ADD (SOff 25 0)
       (SAlu Instr.ALU_SRL (SAlu Instr.ALU_SLL (SOff 10 0) (SLit 32)) (SLit 32)))) = false.
Proof.
intros E hw0 hw4 H22 H25 H10 R0 R4. rewrite branch_ne_U.
rewrite (U_atom E 22 (hw0 * 1000000 + hw4) H22) by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 25 (hw0 * 1000000) H25) by lia.
rewrite (kt2_zext32 E 10 hw4 H10 R4). rewrite zcanon_id by (unfold M64; lia). rewrite Z.eqb_refl. reflexivity.
Qed.

(* `addi s11,s11,0x10; slli s11,s11,0x20; srli a0,s11,0x20; add s10,s10,a0` (0x80d9c..0x80da8): the harness's new
   position at := at + 16 + incl, with incl the zero-extension of rd32's sign-extended answer. *)
Lemma kt2_s10 : forall (x y : word) q n,
  bv_unsigned x = q -> bv_unsigned y = zcanon (bv_swrap 32 n) -> 0 <= n <= 2040 -> 0 <= q -> q + 16 + n < 2 ^ 64 ->
  Sem.alu64 Instr.ALU_ADD x
    (Sem.alu64 Instr.ALU_SRL
       (Sem.alu64 Instr.ALU_ADD (Sem.alu64 Instr.ALU_SLL y (Z_to_bv 64 32)) (Z_to_bv 64 68719476736))
       (Z_to_bv 64 32)) = w64 (q + 16 + n).
Proof.
intros x y q n Hx Hy Hn Hq Hsum.
assert (Hyv : bv_unsigned y = n) by (rewrite Hy, Rd32.rd_sx32 by lia; destruct (Z.ltb_spec n (2 ^ 31)); lia).
assert (H32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit_small; lia).
assert (H36 : bv_unsigned (Z_to_bv 64 68719476736) = 68719476736) by (apply unsigned_lit_small; lia).
assert (S1 : bv_unsigned (Sem.alu64 Instr.ALU_SLL y (Z_to_bv 64 32)) = n * 2 ^ 32).
{ rewrite alu64_unsigned, Hyv, H32. cbn [zalu_raw]. change (Z.land 32 63) with 32.
  rewrite Z.shiftl_mul_pow2 by lia. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). nia. }
assert (S2 : bv_unsigned (Sem.alu64 Instr.ALU_ADD (Sem.alu64 Instr.ALU_SLL y (Z_to_bv 64 32))
               (Z_to_bv 64 68719476736)) = (n + 16) * 2 ^ 32).
{ rewrite alu64_unsigned, S1, H36. cbn [zalu_raw].
  replace (n * 2 ^ 32 + 68719476736) with ((n + 16) * 2 ^ 32) by (change 68719476736 with (16 * 2 ^ 32); nia).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). nia. }
assert (S3 : bv_unsigned (Sem.alu64 Instr.ALU_SRL
               (Sem.alu64 Instr.ALU_ADD (Sem.alu64 Instr.ALU_SLL y (Z_to_bv 64 32)) (Z_to_bv 64 68719476736))
               (Z_to_bv 64 32)) = n + 16).
{ rewrite alu64_unsigned, S2, H32. cbn [zalu_raw]. change (Z.land 32 63) with 32.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64). lia. }
apply bv_eq. rewrite alu64_unsigned, S3, Hx. cbn [zalu_raw].
unfold w64. rewrite Z_to_bv_unsigned. f_equal. lia.
Qed.

(* pos_of at a fit record: the position the harness computes is the reader's own next position. *)
Lemma kt2_pos_fit : forall cx Q, p_kind cx Q = PSN.KFit -> p_pos cx Q = Q + 16 + PSN.incl (p_sw cx) (p_F cx) Q.
Proof. intros cx Q H. unfold p_pos, p_kind in *. unfold PSN.pos_of. rewrite H. reflexivity. Qed.

(* A prefix of an array is an array (the record bytes the call leaves at the head of the buffer). *)
Lemma kt2_garr8_firstn : forall m base l n, garr8 SEGS m base l -> garr8 SEGS m base (firstn n l).
Proof.
intros m base l n Hg. rewrite <- (firstn_skipn n l) in Hg. exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) Hg)).
Qed.

(* ---- the facts the callee's statement asks of the harness's state (the lib/B twins of
   lib/A/Prog/PcapHarnessTail.v's aview_memS / gagree_high / aro_now / meta_now / pch_achain) ---- *)

Lemma kt2_aview_memS : forall cx memS a, gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> 0 <= a < 2 ^ 64 ->
  ~ inG pe_G a -> aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
intros cx memS a Hag Ha HnG. apply (aview_gagree SEGS pe_G _ _ _ a Hag).
apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

Lemma kt2_gagree_high : forall cx memS a, gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  alloc_ceiling <= a < 2 ^ 64 -> aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
intros cx memS a Hag Ha. pose proof asan_consts as (C1 & _).
apply (kt2_aview_memS cx memS a Hag ltac:(lia)).
pose proof (pa_obj_img 4 ltac:(lia)) as O4. pose proof (pa_obj_img 2 ltac:(lia)) as O2.
unfold pcap_img_end, YImgTop.IMG_TOP in O4, O2.
unfold pe_G. intros HG.
apply inG_cons in HG as [HG|HG]; [|apply inG_cons in HG as [HG|HG]; [|exact (inG_nil a HG)]];
  unfold in_zr in HG; cbn [fst snd] in HG; lia.
Qed.

Lemma kt2_aro : forall cx memS own ly4 S4 (W4 : world SEGS) mem4 md4 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS
    (c_md cx) own ly4 S4 W4 mem4 md4 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W4) mem4).
Proof.
intros cx memS own ly4 S4 W4 mem4 md4 k HB HJ Hag.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrod & _ & _ & _ & _ & _ & _ & _ & _ & HGX & HGD & _).
eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ|].
intros a Hro Ho He.
assert (Hi : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
pose proof (pa_img_range a Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
rewrite (kt2_aview_memS cx memS a Hag ltac:(lia)); [exact (Hrod a Hro Ho He)|].
intros HaG. exact (proj1 (HGD a HaG) Hro).
Qed.

Lemma kt2_meta : forall cx memS own ly4 S4 (W4 : world SEGS) mem4 md4 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS
    (c_md cx) own ly4 S4 W4 mem4 md4 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  asrc_meta_inv SEGS KS ly4 (mrestrict (w_H W4) mem4) (c_M cx).
Proof.
intros cx memS own ly4 S4 W4 mem4 md4 k HB HJ Hag.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ) & _ & _ &
  _ & _ & _ & HGX & HGD & _).
pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
split; [rewrite Eextra; exact HX|]. split; [exact Himg|].
split; [exact (asrc_meta_ptr_of_AR SK SEGS B KS ASIL _ _ _ _ _ HAR')|]. split.
- eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
  destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
  pose proof (pa_img_range x Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
  rewrite <- (kt2_aview_memS cx memS x Hag ltac:(lia)).
  + apply (F3 x Hi Hns He). apply fp_spares_below. exact Hlt.
  + intros HxG. destruct (HGD x HxG) as (_ & Hnm & _). apply Hnm. lia.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
  intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_of_aview SEGS).
  rewrite <- (kt2_aview_memS cx memS a Hag ltac:(lia)).
  + apply F5.
    * apply Exists_exists. exists (c_M cx, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
    * intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi. pose proof (Himg a Hi). lia.
  + intros HaG. pose proof (proj1 (HGX a HaG)) as Hi. pose proof (Himg a Hi). lia.
Qed.

Lemma kt2_achain : forall cx memS own ly4 S4 (W4 : world SEGS) mem4 md4 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS
    (c_md cx) own ly4 S4 W4 mem4 md4 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  rdword (aview SEGS (w_H W4) mem4) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W4) mem4) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  achain ly4 (aview SEGS (w_H W4) mem4) (c_sp1 cx) (spZ (c_regs cx)) (pch cx).
Proof.
intros cx memS own ly4 S4 W4 mem4 md4 k HB HJ Hag R8 R16.
pose proof HB as ((_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof Hstk as (Hal & _ & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hlo.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (Hs1b : spZ (c_regs cx) - 288 <= c_sp1 cx <= spZ (c_regs cx) - 256).
{ rewrite Hsp1. unfold pe_sp1, PE_MFRAME.
  pose proof (Z.div_mod (spZ (c_regs cx) - 256) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 256) 32 ltac:(lia)) as M. lia. }
apply (achain_ly_top (c_ly cx)); [exact Etop|].
assert (H8 : spZ (c_regs cx) mod 8 = 0).
{ pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D.
  apply Z.mod_divide; [lia|]. exists (2 * (spZ (c_regs cx) / 16)). lia. }
pose proof asan_consts as (C1 & _).
assert (Hc0 : alloc_ceiling <= spZ (c_regs cx)) by lia.
assert (Ht64 : ly_top (c_ly cx) <= 2 ^ 64) by (change (2 ^ 47) with 140737488355328 in H47;
  change (2 ^ 64) with 18446744073709551616; lia).
unfold pch. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
- assert (HK : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
    aview SEGS (w_H W4) mem4 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a)
    by (intros a Ha; rewrite <- (kt2_gagree_high cx memS a Hag ltac:(lia)); apply F1; lia).
  refine (achain_push _ _ _ _ _ _ _ _ Hch Ht64 HK R8 R16 Hra4 Hc0 H8 _ _); lia.
- left. split; [right; left; lia | reflexivity].
Qed.

(* The bytes of the harness's body that the call keeps: the saved registers, the spill slots, the frame's header
   words, the frame's shadow, the input and the two globals. Everything else the cut states (ps, the timestamp
   cell, the record buffer and the FILE block) the call's own post gives back. *)
Definition kt2_foot (cx : ecx) (fp a : Z) : Prop :=
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/
  (c_sp1 cx + 16 <= a < c_sp1 cx + 152) \/
  (pF cx fp <= a < pF cx fp + 24) \/
  (pF cx fp + PE_FLAGPTR <= a < pF cx fp + PE_FLAGPTR + 8) \/
  (pSH cx fp <= a < pSH cx fp + 16) \/
  (c_p cx <= a < c_p cx + c_n cx) \/
  (VAL (A_OBJ 2) <= a < VAL (A_OBJ 2) + 8) \/
  (VAL (A_OBJ 4) <= a < VAL (A_OBJ 4) + 8).

Lemma kt2_foot_dec : forall cx fp a, kt2_foot cx fp a \/ ~ kt2_foot cx fp a.
Proof. intros cx fp a. unfold kt2_foot, PE_FLAGPTR. lia. Qed.

(* A region of the symbolic state the engine stopped at (a call), by index. *)
Lemma kt2_region_call : forall E ss (ms : machine_state) (W4 : world SEGS) idx r tgt,
  st_ok SEGS E (setpc ss tgt) (restrict (w_H W4) ms) -> nth_error (ss_mem ss) idx = Some r ->
  region_ok SEGS E (mrestrict (w_H W4) (ms_mem ms)) r.
Proof.
intros E ss ms W4 idx r tgt HS Hn.
pose proof (st_ok_region_nth E (setpc ss tgt) (restrict (w_H W4) ms) idx r HS Hn) as HR.
cbn [restrict ms_mem] in HR. exact HR.
Qed.

(* lia without the hypotheses that speak of `mod` or `/`: with the euclidean-division flag every such hypothesis
   adds variables to every lia problem, and the stretch's context holds many of them. *)
Ltac kt2_lia := once (repeat match goal with
  | H : context [Z.modulo _ _] |- _ => clear H
  | H : context [Z.div _ _] |- _ => clear H
  end); lia.

(* PP_KT2 0x80d80: the slots region [s1 + 0x58, s1 + 0x80) (read only) with the three words the stretch loads
   (PS_TSP 0x80d94, PS_BUF 0x80db0, PS_CAP 0x80db4), and the timestamp cell [TS, TS + 8) that 0x80d98 writes.
   The extra atoms: 32 = TS = pTS cx fp, 33 = buf, 34 = cap. The stretch makes no shadow check and the timestamp
   cell is a frame byte whose range the facts cannot place on one side of the shadow, so its runs take the EMPTY
   shadow span (PcapEntryEnd.v's W5Bx / W5span convention). *)
Definition kt2_Bx : sv := SLit 0.
Definition kt2_span : Z * Z := (0, 0).
Definition kt2_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 88 128 88 88
     [YP09.mkChunk PS_TSP (CVal 8 (SOff 32 0)); YP09.mkChunk PS_BUF (CVal 8 (SOff 33 0));
      YP09.mkChunk PS_CAP (CVal 8 (SOff 34 0))];
   YP09.mkRegion (Some 32%nat) 0 8 0 8 []].
Definition kt2_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_kt2 : sstate := mkSS PP_KT2 sr_atoms kt2_regions None kt2_facts.
Definition kt2_extra (ts buf cap : Z) : list word := [w64 ts; w64 buf; w64 cap].

Lemma kt2_entry : forall cx (W3 : world SEGS) (ms3 : machine_state) ts buf cap,
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) ->
  ms_pc_val ms3 = w64 (BASE + PP_KT2) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  2 ^ 46 <= c_sp1 cx <= 2 ^ 47 -> c_sp1 cx mod 32 = 0 ->
  4096 <= ts -> ts + 8 <= c_sp1 cx -> ts mod 32 = 0 ->
  (forall a, ts <= a < ts + 8 -> apresent (w_H W3) (ms_mem ms3) a) ->
  0 <= buf < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  pslot cx W3 ms3 PS_TSP ts -> pslot cx W3 ms3 PS_BUF buf -> pslot cx W3 ms3 PS_CAP cap ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) (kt2_extra ts buf cap))) ss_kt2 (restrict (w_H W3) ms3) /\
  sh_ok SEGS kt2_Bx [] (Eimg (Ereg (ms_regs ms3) (kt2_extra ts buf cap))) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx W3 ms3 ts buf cap H9 Hpc Hrv Hsv Hrom Hfr Hfc Hsp Hal Hts0 Hts1 Hts2 Hpres Hbuf Hcap Q88 Q96 Q120.
set (E := Eimg (Ereg (ms_regs ms3) (kt2_extra ts buf cap))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (kt2_extra ts buf cap)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = w64 ts) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (E33 : ew E 33 = w64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
assert (E34 : ew E 34 = w64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 2)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = ts) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KT2)) (ms_mem ms3) (seg_rom SEGS))
    by (destruct ms3; cbn in *; unfold mkst; subst; f_equal; assumption).
  rewrite Hms, restrict_mkst_fx. unfold ss_kt2. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold kt2_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; cbn [base_val]; fold E.
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      -- apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_TSP 8 (SOff 32 0) ts);
           [cbn [sv_denot]; rewrite E32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
         exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q88).
      -- apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_BUF 8 (SOff 33 0) buf);
           [cbn [sv_denot]; rewrite E33; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
         exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q96).
      -- apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_CAP 8 (SOff 34 0) cap);
           [cbn [sv_denot]; rewrite E34; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
         exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q120).
    * rewrite U32. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | apply Forall_nil].
  + apply pairwise_disjoint_of_extents.
    unfold kt2_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. fold E. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [kt2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite U9, U32. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply Forall_nil.
Qed.

(* The measured form: s10 goes from Q at PP_KT2 to Q + 16 + incl at PP_KL2 (0x80da8), and incl > 0 at the fit
   record, so the bound on |F| - s10 drops by at least 16. *)
Lemma pe_from_KT2_m : forall m POST,
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_KL2 B MT KS) (m - 16)) ->
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_KT2 B MT KS) m).
Proof.
intros m POST HKL2.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo (HI & HM).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct (PcapEntryKit.rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
cbv zeta in HI.
destruct HI as (b & h & buf & i & p & Hcut & Hn26 & Hgood & Hi0 & Hip & HpQ & Hfit & R10 & R18 & R20 & R21 & R22
  & R23 & R24 & R25 & R26 & R27 & Hls & Hcalls & Hfirst & Hglob & Hrd).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
pose proof Hls as ((QF0 & QD & QSHB & QSH & QF & QFK & QTSP & QCAP) & QBUF & QVM & QB12 & QUS).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR Hfin) as (HFal & HFapp & HFpres & HFSpres).
rewrite Efa in HFal, HFapp, HFpres, HFSpres. change (fs_frame_bytes PE_CID) with 128 in *.
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hu3 : In (buf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096 & Hbceil & Hbapp & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR Hh3)
  as (_ & Hh4096 & Hhceil & Hhapp & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 buf (p_bn cx) HAR Hu3) as (_ & Hu4096 & Huceil & Huapp & _).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as [_ Hrq2].
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hrq3].
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil, Hhapp.
assert (ERS : req_size (p_bn cx) = p_bn cx)
  by (unfold req_size; destruct (Z.eqb_spec (p_bn cx) 0) as [E0|_]; [lia | reflexivity]).
rewrite ERS in Huceil, Huapp.
unfold LLVMF_STK in Hspc, Hpres. unfold PE_FRAME in Hf1.
assert (Hs1 : 2 ^ 46 <= c_sp1 cx <= 2 ^ 47) by lia.
assert (HTS : pTS cx fp = pF cx fp + 96) by reflexivity.
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (HTS32 : pTS cx fp mod 32 = 0)
  by (rewrite HTS; apply Z.mod_divide in Hf64; [|lia]; destruct Hf64 as [q Hq]; rewrite Hq;
      replace (q * 64 + 96) with ((2 * q + 3) * 32) by lia; apply Z_mod_mult).
assert (Hps8 : pPS cx fp mod 8 = 0) by (rewrite Hps; apply mod64_mod8; exact Hf64).
assert (Hts8 : pTS cx fp mod 8 = 0) by (rewrite HTS; apply mod64_mod8 in Hf64; lia).
(* the record's incl and the harness's new position *)
destruct (kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) Hfit) as (Hi1 & Hi2 & Hi3 & Hi4).
pose proof (p_lens cx) as HCL. fold (p_nF cx) in Hi3, Hi4.
assert (Hpos : p_pos cx (p_q cx p) = p_q cx p + 16 + PSN.incl (p_sw cx) (p_F cx) (p_q cx p))
  by exact (kt2_pos_fit cx (p_q cx p) Hfit).
assert (HQ0 : 24 <= p_q cx p) by lia.
(* the start state *)
destruct (kt2_entry cx W3 ms3 (pTS cx fp) buf (p_cap cx) Rs1 Hpc Hrv Hsv Hrom Hfreg Hfcsr Hs1 Hal32
  ltac:(lia) ltac:(lia) HTS32 ltac:(intros a Ha; apply (proj1 (HFpres a ltac:(rewrite HTS in Ha; lia))))
  ltac:(lia) ltac:(lia) QTSP QBUF QCAP) as [HS SHOK].
remember (Eimg (Ereg (ms_regs ms3) (kt2_extra (pTS cx fp) buf (p_cap cx)))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i0, (i0 < A_TEXT)%nat ->
          ew E i0 = ew (Ereg (ms_regs ms3) (kt2_extra (pTS cx fp) buf (p_cap cx))) i0)
  by (intros i0 Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i0 (r : bv 5), (i0 < A_TEXT)%nat -> Z.of_nat i0 = bv_unsigned r ->
          ew E i0 = getr (ms_regs ms3) r)
  by (intros i0 r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i0 r Hr)).
assert (E32 : ew E 32 = w64 (pTS cx fp))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (E33 : ew E 33 = w64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
assert (E34 : ew E 34 = w64 (p_cap cx))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 2)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pTS cx fp) by (rewrite E32; apply unsigned_lit_small; lia).
clear HEdef.
pose proof (PcapEntryKit.bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_tok RUN HS HJ SHOK kt2_span;
  [ apply awr_ok_x_of0; unfold ss_kt2, kt2_regions; cbn [ss_mem];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
    eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil];
    cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists PE_CID, fp;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite Efa;
    change (fs_frame_bytes PE_CID) with 128; rewrite HTS in Ha; lia |].
(* 0x80d8c bne s6,a0 to PP_abort: s6 = rec_ts = sec * 10^6 + usec = s9 + a0 *)
psrr_branch_tok RUN BR HS SHOK kt2_span.
{ exfalso.
  rewrite (kt2_ts_same E (p_hw cx (p_q cx p) 0) (p_hw cx (p_q cx p) 4)
    ltac:(rewrite (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl), R22; reflexivity)
    ltac:(rewrite (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25; reflexivity)
    ltac:(rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10; reflexivity)
    (hw_range _ _ _ _) (hw_range _ _ _ _)) in Hc.
  discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK kt2_span;
  [ apply awr_ok_x_of0; cbn [ss_mem];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
    eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil];
    cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists PE_CID, fp;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite Efa;
    change (fs_frame_bytes PE_CID) with 128; rewrite HTS in Ha; lia |].

(* the stretch wrote only the timestamp cell *)
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => pTS cx fp <= a < pTS cx fp + 8) HFr
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U32 in Hrr; lia|]);
        destruct Hin)) as UNa.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => pTS cx fp <= a < pTS cx fp + 8) HFr0
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U32 in Hrr; lia|]);
        destruct Hin)) as UNb.
assert (UN : mk W3 (ms_mem ms3) (ms_mem ms0) (pTS cx fp) (pTS cx fp + 8))
  by (apply (mk_trans W3 _ (ms_mem ms) _ _ _ ltac:(intros a Ha Hn; apply UNa; [exact Ha | exact Hn]));
      intros a Ha Hn; apply UNb; [exact Ha | exact Hn]).
clear UNa UNb HF HFr HG HF0 HFr0 HG0.
(* the shadow of the frame is apart from every app range *)
assert (HSHv : pSH cx fp = SHADOW_OFF + pF cx fp / 8) by reflexivity.
assert (Hdiv1 : 0 <= pF cx fp / 8) by (apply Z.div_pos; lia).
assert (Hdiv2 : pF cx fp / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (Hdiv3 : alloc_ceiling / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (Dsh : forall q n, in_app q n -> forall a, pSH cx fp <= a < pSH cx fp + 16 -> ~ (q <= a < q + n)).
{ intros q n (Hq1 & Hq2) a Ha. rewrite HSHv in Ha. unfold SHADOW_OFF in Ha.
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hq2. lia. }
assert (Dts_sh : forall a, pSH cx fp <= a < pSH cx fp + 16 -> ~ (pTS cx fp <= a < pTS cx fp + 8))
  by (intros a Ha Hx; apply (Dsh (pF cx fp) 128 HFapp a Ha); rewrite HTS in Hx; lia).
assert (HSHr : SHADOW_OFF <= pSH cx fp /\ pSH cx fp + 16 <= 17594333495296)
  by (rewrite HSHv; unfold SHADOW_OFF; lia).
(* the shadow bytes and the addressability of ps and of the timestamp cell at the call *)
assert (Hsh0 : pshadow cx fp W3 ms0 PSH_ts).
{ intros ii Hi. rewrite Hshlen in Hi. unfold PE_NSH in Hi.
  rewrite (UN (pSH cx fp + Z.of_nat ii) ltac:(unfold SHADOW_OFF in HSHr; lia)
    ltac:(apply Dts_sh; lia)).
  apply Hsh. rewrite Hshlen. unfold PE_NSH. lia. }
assert (HRA : range_addressable (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (pPS cx fp) ANX.PS_LEN).
{ apply zero_shadow_range; [exact Hps8 | reflexivity |].
  intros ii Hi. unfold ANX.PS_LEN in Hi. change (24 / 8) with 3 in Hi.
  rewrite Hps, shadow_of_addr_aligned_off by (apply mod64_mod8 in Hf64; lia).
  change (32 / 8) with 4.
  assert (Hii3 : ii = 0 \/ ii = 1 \/ ii = 2) by lia.
  destruct Hii3 as [Hz|[Hz|Hz]]; rewrite Hz.
  - replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH, shadow_of_addr; lia).
    exact (Hsh0 4%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
  - replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH, shadow_of_addr; lia).
    exact (Hsh0 5%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
  - replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH, shadow_of_addr; lia).
    exact (Hsh0 6%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)). }
assert (HRAts : range_addressable (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (pTS cx fp) 8).
{ apply zero_shadow_range; [exact Hts8 | reflexivity |].
  intros jj Hj. change (8 / 8) with 1 in Hj. assert (Hj0 : jj = 0) by lia. rewrite Hj0.
  rewrite HTS, shadow_of_addr_aligned_off by (apply mod64_mod8 in Hf64; lia).
  change (96 / 8) with 12.
  replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 12 + 0) with (pSH cx fp + Z.of_nat 12) by (unfold pSH, shadow_of_addr; lia).
  exact (Hsh0 12%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)). }

(* the journal opened at the call, and what the allocator invariant gives there *)
destruct (PcapEntryCalls.gx_open SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag & _).
pose proof HJi as (HAR0 & _).
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms0) _ buf (p_bn cx) HAR0 Hu3) as (_ & _ & _ & _ & Hupres & _).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms0) _ PE_CID fp HAR0 Hfin) as (_ & _ & HFpres0 & _).
rewrite Efa in HFpres0. change (fs_frame_bytes PE_CID) with 128 in HFpres0.
rewrite ERS in Hupres.
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as HFoff.
rewrite Efa in HFoff. change (fs_frame_bytes PE_CID) with 128 in HFoff.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFoff.
(* the two blocks the harness took are fresh *)
assert (HufL : ~ In (buf, p_bn cx) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK)])).
{ refine (block_fresh B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ buf (p_bn cx) HAR _). rewrite <- app_assoc. exact Hperm. }
assert (HhL : ~ In (h, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (buf, p_bn cx)])).
{ refine (block_fresh B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ h SRC_FILE_BLOCK HAR _).
  eapply Permutation_trans; [exact Hperm|]. rewrite <- app_assoc. apply Permutation_app_head.
  cbn [app]. apply perm_skip. apply perm_swap. }
assert (Hbufout : ~ In (buf, p_bn cx) (ablocks B (c_ly cx) (c_S cx)))
  by (intros Hin; apply HufL; apply in_or_app; left; exact Hin).
assert (Hhout : ~ In (h, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx)))
  by (intros Hin; apply HhL; apply in_or_app; left; exact Hin).
assert (Hne_uh : (buf, p_bn cx) <> (h, SRC_FILE_BLOCK))
  by (intros Heq; apply HufL; apply in_or_app; right; right; left; exact (eq_sym Heq)).
assert (Hne_ub : (buf, p_bn cx) <> (b, p_nF cx))
  by (intros Heq; apply HufL; apply in_or_app; right; left; exact (eq_sym Heq)).
(* how the blocks and the frame lie *)
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf (p_bn cx) PE_CID fp HAR Hu3 Hfin) as Dbf.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ h SRC_FILE_BLOCK PE_CID fp HAR Hh3 Hfin) as Dhf.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b (p_nF cx) PE_CID fp HAR Hb3 Hfin) as Dbb.
unfold zdisjoint in Dbf, Dhf, Dbb. cbn [fst snd] in Dbf, Dhf, Dbb.
rewrite Efa in Dbf, Dhf, Dbb. change (fs_frame_bytes PE_CID) with 128 in Dbf, Dhf, Dbb.
change (req_size SRC_FILE_BLOCK) with 1304 in Dhf. rewrite ERS in Dbf.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hu3 Hh3 Hne_uh) as Duh.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hu3 Hb3 Hne_ub) as Dub.
unfold zdisjoint in Duh, Dub. cbn [fst snd] in Duh, Dub.
change (req_size SRC_FILE_BLOCK) with 1304 in Duh. rewrite ERS in Duh, Dub.
(* the words of ps the call reads, and the record's bytes, at the call *)
destruct Hrd as (Hsrc & (Hpsf & Hpsw) & Hfitc).
destruct (Hfitc Hfit) as (Vorig & Vtag & Vvid & Vts & Vbuf).
unfold pval, pPS, pTS, PO_PS, PO_TS in Hpsf, Hpsw, Vorig, Vtag, Vvid, Vts.
assert (VM : forall a n v, val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) a n v ->
          pF cx fp + 32 <= a -> a + Z.of_nat n <= pF cx fp + 56 ->
          val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) a n v)
  by (intros a n v Hv Ha1 Ha2; apply (PcapEntryKit.val_mem_keep W3 _ _ _ _ _ _ _ Hv UN); rewrite ?HTS; kt2_lia).
assert (Hpsf0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (pF cx fp + 32) 8 h)
  by (apply VM; [exact Hpsf | kt2_lia | cbn; kt2_lia]).
assert (Hpsw0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (pF cx fp + 32 + 8) 4 (p_swz cx))
  by (apply VM; [exact Hpsw | kt2_lia | cbn; kt2_lia]).
assert (Hlol0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (pF cx fp + 32 + 12) 4
                  (PSN.orig (p_sw cx) (p_F cx) (p_q cx p)))
  by (apply VM; [exact Vorig | kt2_lia | cbn; kt2_lia]).
assert (Hlvt0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (pF cx fp + 32 + 16) 4
                  (if PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) then 1 else 0))
  by (apply VM; [exact Vtag | kt2_lia | cbn; kt2_lia]).
assert (Hlvid0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms0)) (pF cx fp + 32 + 20) 2
                  (if PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) then PSN.rec_vid (p_F cx) (p_q cx p) else 0))
  by (apply VM; [exact Vvid | kt2_lia | cbn; kt2_lia]).
assert (MKW0 : PcapEntryKit.mkw W3 W3 (ms_mem ms3) (ms_mem ms0) (fun a => pTS cx fp <= a < pTS cx fp + 8))
  by (apply (proj1 (PcapEntryKit.mk_mkw W3 _ _ _ _)); exact UN).
assert (Nh : forall j, 0 <= j < SRC_FILE_BLOCK -> ~ (pTS cx fp <= h + j < pTS cx fp + 8)).
{ unfold SRC_FILE_BLOCK. intros j Hj Hx. rewrite HTS in Hx. kt2_lia. }
assert (Nb : forall j, 0 <= j < Z.of_nat (length (p_C cx)) -> ~ (pTS cx fp <= b + j < pTS cx fp + 8)).
{ intros j Hj Hx. rewrite HCL in Hj. rewrite HTS in Hx. kt2_lia. }
assert (Nenv : forall a, asrc_env_addr KS a -> ~ (pTS cx fp <= a < pTS cx fp + 8)).
{ intros a Ha Hx. pose proof (PcapEntryKit.env_low B KS ASIL a Ha) as Henv.
  unfold pcap_img_end, YImgTop.IMG_TOP in Henv. rewrite HTS in Hx. kt2_lia. }
assert (Hsrc0 : asource_at SEGS KS (mrestrict (w_H W3) (ms_mem ms0)) h b (p_C cx) (p_pos cx (p_q cx p))).
{ exact (PcapEntryKit.asource_at_keepw B KS ASIL W3 W3 (ms_mem ms3) (ms_mem ms0)
    (fun a => pTS cx fp <= a < pTS cx fp + 8) h b (p_C cx) _ Hsrc MKW0 Nh Nb Nenv
    ltac:(kt2_lia) ltac:(unfold SRC_FILE_BLOCK; kt2_lia) ltac:(kt2_lia) ltac:(rewrite HCL; kt2_lia)). }
(* the bytes of the record buffer and the two pad bytes of ps *)
destruct (garr8_of_present SEGS (mrestrict (w_H W3) (ms_mem ms0)) buf (Z.to_nat (p_bn cx))) as (bj & Hbjl & Hbj).
{ intros a Ha. rewrite Z2Nat.id in Ha by kt2_lia. apply PcapEntryCalls.present_rdW.
  exact (proj1 (Hupres a ltac:(kt2_lia))). }
destruct (garr8_of_present SEGS (mrestrict (w_H W3) (ms_mem ms0)) (pF cx fp + 32 + 22) 2%nat) as (pad & Hpadl & Hpad).
{ intros a Ha. cbn in Ha. apply PcapEntryCalls.present_rdW. exact (proj1 (HFpres0 a ltac:(kt2_lia))). }

(* the registers at the call *)
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12. prreg HS (13%bv : bv 5) T13. prreg HS (18%bv : bv 5) T18.
prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23.
prreg HS (24%bv : bv 5) T24. prreg HS (26%bv : bv 5) T26.
pose proof (@pa_B_ok _ _ PI) as (HBR & HBR1 & _).
assert (Hsp : spZ (ms_regs ms0) = c_sp1 cx)
  by (unfold spZ; rewrite T2, (EW 2%nat 2%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl), Rsp;
      unfold w64; apply unsigned_lit_small; kt2_lia).
assert (Hs0Z : s0Z (ms_regs ms0) = spZ (c_regs cx))
  by (unfold s0Z; rewrite T8, (EW 8%nat 8%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl), Rs0;
      unfold w64; apply unsigned_lit_small; kt2_lia).
assert (Hsp16b : c_sp1 cx mod 16 = 0).
{ destruct (proj1 (Zmod_divides (c_sp1 cx) 32 ltac:(kt2_lia)) Hal32) as [q Hq]. rewrite Hq.
  replace (32 * q) with ((2 * q) * 16) by kt2_lia. apply Z_mod_mult. }
(* the saved registers at the call, for the call chain *)
assert (Hsav8 : rdword (aview SEGS (w_H W3) (ms_mem ms0)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
  by (apply (PcapEntryKit.rdword_keep W3 _ _ _ _ _ _ (proj1 Hsav) UN); rewrite ?HTS; kt2_lia).
assert (Hsav16 : rdword (aview SEGS (w_H W3) (ms_mem ms0)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ pose proof (proj2 Hsav 0 ltac:(kt2_lia)) as H0.
  replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by kt2_lia.
  apply (PcapEntryKit.rdword_keep W3 _ _ _ _ _ _ H0 UN); rewrite ?HTS; kt2_lia. }
(* the word the store 0x80d98 left in the timestamp cell *)
pose proof (kt2_region_call E _ ms0 W3 1%nat
  (YP09.mkRegion (Some 32%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit (2 ^ 64 - 1)))]) _ HS
  ltac:(vm_compute; reflexivity)) as HRts.
pose proof (field_of_region E _ 32%nat (pTS cx fp) _ _ _ _ _ 0 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) HRts U32
  ltac:(cbn; tauto) ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); kt2_lia)
  ltac:(cbn; kt2_lia)) as Vts0.
change (N.to_nat 8) with 8%nat in Vts0. rewrite Z.add_0_r in Vts0.
(* the right to write the three objects the call may change *)
assert (EBN : ANX.nx_bufn (p_cap cx) = p_bn cx) by reflexivity.
assert (WRF : forall q n, pF cx fp <= q -> q + n <= pF cx fp + 128 ->
  ANX.nx_wr_ok NSTK B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) ly3 S3 [(PE_CID, fp)]
    (spZ (ms_regs ms0)) q n).
{ intros q n Hq1 Hq2 a Ha. split.
  - right; right; right. exists PE_CID, fp. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID) with 128. kt2_lia.
  - rewrite Hsp. kt2_lia. }
assert (WRB : ANX.nx_wr_ok NSTK B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) ly3 S3
                [(PE_CID, fp)] (spZ (ms_regs ms0)) buf (ANX.nx_bufn (p_cap cx))).
{ rewrite EBN. intros a Ha. split.
  - right; right; left. exists buf, (p_bn cx). split; [exact Hu3|]. split; [exact Hbufout | kt2_lia].
  - rewrite Hsp. kt2_lia. }
pose proof (hw_range (p_sw cx) (p_F cx) (p_q cx p) 12) as Horig.
assert (X1588 : 0 <= 1588 < 2 ^ 40) by lia.
(* the call *)
pmkst HS.
rewrite (pa_xcalls PS_pcap_source_next AF_pcap_source_next ltac:(cbv [pcap_xcalls In]; tauto)).
eapply SRr_bind.
{ eapply (PcapEntryCalls.next_call SK B MT KS NSTK NEXT LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx)
    (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms0) _ k (ms_regs ms0)
    (pF cx fp + 32) buf (p_cap cx) (pF cx fp + 96) h b
    (p_q cx p + 16 + PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) (p_swz cx)
    (PSN.orig (p_sw cx) (p_F cx) (p_q cx p))
    (if PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) then 1 else 0)
    (if PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) then PSN.rec_vid (p_F cx) (p_q cx p) else 0)
    (2 ^ 64 - 1) (c_M cx) PE_CID fp (p_C cx) bj pad (pch cx) HJ).
  - exact (kt2_aro cx memS _ ly3 S3 W3 (ms_mem ms0) _ k HB HJi Hag).
  - rewrite T1. exact (ret_ok_codeptr_v 1588 X1588 eq_refl).
  - unfold raZ. rewrite T1, unsigned_lit_small by kt2_lia. kt2_lia.
  - rewrite T3, (EW 3%nat 3%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl), Rgp. exact Hgp.
  - rewrite T4, (EW 4%nat 4%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl), Rtp. exact Htp.
  - rewrite T10, (EW 20%nat 20%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl), R20. reflexivity.
  - rewrite T11, E33. reflexivity.
  - rewrite T12, E34. reflexivity.
  - rewrite T13, E32. reflexivity.
  - rewrite Hsp. exact Hsp16b.
  - rewrite Hsp. unfold LLVMF_STK. kt2_lia.
  - rewrite Hsp. kt2_lia.
  - rewrite Hsp, Hs0Z. exact (kt2_achain cx memS _ ly3 S3 W3 (ms_mem ms0) _ k HB HJi Hag Hsav8 Hsav16).
  - rewrite Hfr. vm_compute. reflexivity.
  - unfold ANX.PS_F_OFF. rewrite Z.add_0_r. exact Hpsf0.
  - kt2_lia.
  - exact Hps8.
  - kt2_lia.
  - unfold ANX.PS_LEN. kt2_lia.
  - unfold amem_range, ANX.PS_LEN. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. kt2_lia.
  - left. reflexivity.
  - rewrite Efa. kt2_lia.
  - rewrite Efa. change (fs_frame_bytes PE_CID) with 128. unfold ANX.PS_LEN. kt2_lia.
  - exact HRA.
  - intros _. unfold ANX.nx_ps_at, ANX.PS_F_OFF, ANX.PS_SW_OFF, ANX.PS_OL_OFF, ANX.PS_VT_OFF, ANX.PS_VID_OFF.
    rewrite Z.add_0_r. split; [exact Hpsf0|]. split; [exact Hpsw0|]. split; [exact Hlol0|].
    split; [exact Hlvt0|]. split; [exact Hlvid0|]. split; [exact Hpad | exact Hpadl].
  - intros _. exact (p_swz_01 cx).
  - intros _. split; [exact Horig|]. split; [destruct (PSN.tagged (p_sw cx) (p_F cx) (p_q cx p)); kt2_lia|].
    destruct (PSN.tagged (p_sw cx) (p_F cx) (p_q cx p)); [|kt2_lia]. unfold PSN.rec_vid.
    pose proof (Z.mod_pos_bound (256 * PSN.fb (p_F cx) (p_q cx p + 30) + PSN.fb (p_F cx) (p_q cx p + 31)) 4096
      ltac:(kt2_lia)). lia.
  - intros _. exact (WRF (pF cx fp + 32) ANX.PS_LEN ltac:(kt2_lia) ltac:(unfold ANX.PS_LEN; kt2_lia)).
  - intros _. rewrite EBN. split; [exact Hu3|]. split; [kt2_lia|]. split; [kt2_lia|].
    split; [exact Hbj|]. split; [rewrite Hbjl, Z2Nat.id by kt2_lia; reflexivity|].
    split; [unfold ANX.NX_CAP_MAX; kt2_lia|].
    split; [rewrite <- EBN; exact WRB | unfold ANX.PS_LEN; kt2_lia].
  - intros _ _. split; [exact Vts0|]. split; [exact Hts8|]. split; [kt2_lia|]. split; [kt2_lia|].
    split; [unfold amem_range; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
            unfold kLowMemEnd, kHighMemBeg, kHighMemEnd; kt2_lia|].
    split; [exists PE_CID, fp; split; [left; reflexivity|];
            rewrite Efa; change (fs_frame_bytes PE_CID) with 128; kt2_lia|].
    split; [exact (WRF (pF cx fp + 96) 8 ltac:(kt2_lia) ltac:(kt2_lia))|].
    split; [exact HRAts|]. split; [unfold ANX.PS_LEN; kt2_lia | rewrite EBN; kt2_lia].
  - intros _. split; [exact Hh3|]. split; [rewrite HCL; exact Hb3|].
    split; [rewrite <- Hpos; exact Hsrc0|].
    split; [rewrite HCL; kt2_lia|]. split; [rewrite HCL; kt2_lia|].
    rewrite EBN. change SRC_FILE_BLOCK with 1304. rewrite HCL.
    split; [kt2_lia|]. split; [kt2_lia|]. split; [unfold ANX.PS_LEN; kt2_lia|]. split; [unfold ANX.PS_LEN; kt2_lia|].
    split; [intros _; split; kt2_lia|].
    intros x Hx. unfold asource_fp in Hx. apply inFP_cons in Hx as [Hx|Hx]; [|left; exact Hx].
    right. exists h, SRC_FILE_BLOCK. split; [exact Hh3|]. split; [exact Hhout|].
    change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx. kt2_lia.
  - intros _. exact (kt2_meta cx memS _ ly3 S3 W3 (ms_mem ms0) _ k HB HJi Hag). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HP2 & Hbl2 & Hfrs2 & Hmle & Hfd2 & Hfs2
  & Hfin2).

destruct Hfin2 as [(Hh0 & _) | (_ & Ha0 & HK & Hsrc2 & Hps2 & (bj' & Hbj'1 & Hbj'2 & Hbj'3) & Hts2)];
  [exfalso; kt2_lia|].
destruct HK as (K1 & K2 & K3 & K4 & _ & _).
subst c2.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGD & _).
(* what the call kept of the harness's body *)
assert (Hinb3 : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ intros Hn. pose proof HB as (_ & _ & _ & _ & Hin0 & _).
  destruct Hin0 as [[H0 _] | (_ & Hin0)]; [kt2_lia|].
  apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin0. }
assert (Hinbc : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hn. pose proof HB as (_ & _ & _ & _ & Hin0 & _).
  destruct Hin0 as [[H0 _] | (_ & Hin0)]; [kt2_lia | exact Hin0]. }
assert (NE : forall a, ~ (pF cx fp + 32 <= a < pF cx fp + 56) -> ~ (buf <= a < buf + p_bn cx) ->
  ~ (pF cx fp + 96 <= a < pF cx fp + 104) -> ~ (h <= a < h + 1304) ->
  ~ ANX.nx_wrset (pF cx fp + 32) buf (p_cap cx) (pF cx fp + 96) h a).
{ intros a N1 N2 N3 N4 Hw. unfold ANX.nx_wrset, ANX.PS_LEN in Hw. rewrite EBN in Hw. unfold SRC_FILE_BLOCK in Hw.
  destruct Hw as [Hw|[Hw|[[_ Hw]|[_ Hw]]]]; [apply N1 | apply N2 | apply N3 | apply N4]; kt2_lia. }
assert (KEEP : forall a, kt2_foot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. unfold kt2_foot, PE_FLAGPTR in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]].
  - rewrite <- (UN a ltac:(kt2_lia) ltac:(rewrite HTS; kt2_lia)).
    apply K1; [kt2_lia | rewrite Hsp; kt2_lia | apply NE; kt2_lia].
  - rewrite <- (UN a ltac:(kt2_lia) ltac:(rewrite HTS; kt2_lia)).
    apply K1; [kt2_lia | rewrite Hsp; kt2_lia | apply NE; kt2_lia].
  - rewrite <- (UN a ltac:(kt2_lia) ltac:(rewrite HTS; kt2_lia)).
    apply (K4 PE_CID fp a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa;
      change (fs_frame_bytes PE_CID) with 128; kt2_lia | apply NE; kt2_lia].
  - rewrite <- (UN a ltac:(kt2_lia) ltac:(rewrite HTS; kt2_lia)).
    apply (K4 PE_CID fp a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa;
      change (fs_frame_bytes PE_CID) with 128; kt2_lia | apply NE; kt2_lia].
  - rewrite <- (UN a ltac:(unfold SHADOW_OFF in HSHr; kt2_lia) (Dts_sh a Ha)).
    apply (K4 PE_CID fp a Hfin).
    + right. unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID / 8) with 16.
      change (shadow_addr (pF cx fp)) with (pSH cx fp). kt2_lia.
    + apply NE.
      * intros Hx. apply (Dsh _ _ HFapp a Ha). kt2_lia.
      * intros Hx. exact (Dsh _ _ Huapp a Ha Hx).
      * intros Hx. apply (Dsh _ _ HFapp a Ha). kt2_lia.
      * intros Hx. exact (Dsh _ _ Hhapp a Ha Hx).
  - destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn]; [|exfalso; kt2_lia].
    pose proof (Hinb3 Hn) as Hin3.
    pose proof (req_size_pos (c_n cx) ltac:(kt2_lia)) as [_ Hrqn].
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR Hin3 Hfin) as Dif.
    unfold zdisjoint in Dif. cbn [fst snd] in Dif. rewrite Efa in Dif.
    change (fs_frame_bytes PE_CID) with 128 in Dif.
    assert (Hne1 : (c_p cx, c_n cx) <> (buf, p_bn cx))
      by (intros Heq; apply Hbufout; rewrite <- Heq; exact (Hinbc Hn)).
    assert (Hne2 : (c_p cx, c_n cx) <> (h, SRC_FILE_BLOCK))
      by (intros Heq; apply Hhout; rewrite <- Heq; exact (Hinbc Hn)).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin3 Hu3 Hne1) as Diu.
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin3 Hh3 Hne2) as Dih.
    unfold zdisjoint in Diu, Dih. cbn [fst snd] in Diu, Dih. rewrite ERS in Diu.
    change (req_size SRC_FILE_BLOCK) with 1304 in Dih.
    rewrite <- (UN a ltac:(kt2_lia) ltac:(rewrite HTS; kt2_lia)).
    replace a with (c_p cx + (a - c_p cx)) by kt2_lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hin3); [kt2_lia|].
    replace (c_p cx + (a - c_p cx)) with a by kt2_lia.
    apply NE; kt2_lia.
  - pose proof (pa_obj_img 2 ltac:(kt2_lia)) as O2. unfold pcap_img_end, YImgTop.IMG_TOP in O2.
    rewrite <- (UN a ltac:(kt2_lia) ltac:(rewrite HTS; kt2_lia)).
    assert (HaG : inG pe_G a)
      by (unfold pe_G; apply (proj2 (inG_cons _ _ _)); right; apply (proj2 (inG_cons _ _ _)); left;
          unfold in_zr; cbn [fst snd]; kt2_lia).
    destruct (HGX a HaG) as [Hi Hno]. destruct (HGD a HaG) as (_ & _ & Herr & _).
    exact (K3 a Hi Hno Herr).
  - pose proof (pa_obj_img 4 ltac:(kt2_lia)) as O4. unfold pcap_img_end, YImgTop.IMG_TOP in O4.
    rewrite <- (UN a ltac:(kt2_lia) ltac:(rewrite HTS; kt2_lia)).
    assert (HaG : inG pe_G a)
      by (unfold pe_G; apply (proj2 (inG_cons _ _ _)); left; unfold in_zr; cbn [fst snd]; kt2_lia).
    destruct (HGX a HaG) as [Hi Hno]. destruct (HGD a HaG) as (_ & _ & Herr & _).
    exact (K3 a Hi Hno Herr). }
assert (MKW : mkw W3 W2 (ms_mem ms3) mem2 (fun a => ~ kt2_foot cx fp a)).
{ intros a Ha Hnn. destruct (kt2_foot_dec cx fp a) as [Hf|Hf]; [exact (KEEP a Hf) | exfalso; exact (Hnn Hf)]. }

assert (HPk : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms0) r).
{ intros r Hr. pose proof (HP2 (bv_unsigned r) Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. }
assert (NR : forall a, kt2_foot cx fp a -> ~ (fun a0 => ~ kt2_foot cx fp a0) a) by (intros a Ha Hn; exact (Hn Ha)).
assert (HB2 : pe_body cx fp PP_KL2 W2 (mkst regs2 (getr (ms_regs ms0) 1) mem2 (seg_rom SEGS)) PSH_ts).
{ eapply (pe_body_keepw cx fp PP_KT2 PP_KL2 W3 W2 ms3 (mkst regs2 (getr (ms_regs ms0) 1) mem2 (seg_rom SEGS))
    PSH_ts (fun a => ~ kt2_foot cx fp a) Hbody);
  [ cbn [ms_pc_val mkst]; rewrite T1; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
  | reflexivity
  | cbn [ms_regs mkst]; rewrite (HPk (2%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)), T2;
    exact (EW 2%nat 2%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl)
  | cbn [ms_regs mkst]; rewrite (HPk (8%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)), T8;
    exact (EW 8%nat 8%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl)
  | cbn [ms_regs mkst]; rewrite (HPk (9%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)), T9;
    exact (EW 9%nat 9%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl)
  | cbn [ms_regs mkst]; rewrite (HPk (3%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)), T3;
    exact (EW 3%nat 3%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl)
  | cbn [ms_regs mkst]; rewrite (HPk (4%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)), T4;
    exact (EW 4%nat 4%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl)
  | cbn [ms_mem mkst]; exact MKW
  | intros a Ha; apply NR; unfold kt2_foot; kt2_lia
  | intros a Ha; apply NR; unfold kt2_foot; kt2_lia
  | intros a Ha; apply NR; unfold kt2_foot; kt2_lia
  | intros a Ha; apply NR; unfold kt2_foot; kt2_lia
  | intros a Ha; apply NR; unfold kt2_foot; kt2_lia
  | unfold LLVMF_STK; kt2_lia | kt2_lia | exact Hf0 | unfold PE_FRAME; kt2_lia | exact Hinp ]. }
assert (SAP : slots_apartw cx (fun a => ~ kt2_foot cx fp a))
  by (intros a Ha1 Ha2; apply NR; unfold kt2_foot; kt2_lia).
(* the reader's model at the new position *)
set (pn := p_q cx p + 16 + PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) in *.
assert (Ef : forall (Hk2 : p_kind cx (p_q cx pn) = PSN.KFit),
  ANX.nx_fit (p_swz cx =? 1) (p_C cx) (p_cap cx) pn = true).
{ intros Hk2. unfold ANX.nx_fit, ANX.nx_kind, ANX.nx_q. rewrite PcapEntryCalls.nxF_pC.
  change (PSN.kind (p_swz cx =? 1) (p_F cx) (p_cap cx) (PSN.psn_q (p_swz cx =? 1) (p_F cx) (p_cap cx) pn))
    with (p_kind cx (p_q cx pn)). rewrite Hk2. reflexivity. }
assert (S26 : getr regs2 26 = w64 pn).
{ rewrite (HPk (26%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)), T26.
  subst pn. apply kt2_s10.
  - rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl), R26. apply unsigned_lit_small. kt2_lia.
  - rewrite (EW 27%nat 27%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl), R27. unfold w64. rewrite unsigned_lit. reflexivity.
  - kt2_lia.
  - kt2_lia.
  - kt2_lia. }
apply (HKL2 cx fp (k + ANX.EV_NEXT) acc ly2 S2 W2 (mkst regs2 (getr (ms_regs ms0) 1) mem2 (seg_rom SEGS)) md2 HB HJ2
  ltac:(rewrite Hfrs2; exact Hfr)
  ltac:(rewrite <- (Z.add_0_r acc); exact (mle_station MT _ _ _ _ _ MTL Hmo Hmle))).
split; [| cbn [ms_regs mkst]; rewrite S26; rewrite R26 in HM; subst pn; unfold w64 in HM |- *;
          rewrite unsigned_lit_small in HM by kt2_lia; rewrite unsigned_lit_small by kt2_lia; kt2_lia ].
exists b, h, buf, (i + 1), pn.
split.
{ split; [exact HB2|]. split; [unfold ANX.EV_NEXT; kt2_lia|]. split; [exact Hacc|].
  split; [rewrite Hbl2; exact Hperm|].
  split; [rewrite Hfd2; repeat rewrite (proj1 (ACL.wvb_fds_fs _ _ _)); exact Hfds
         | rewrite Hfs2; repeat rewrite (proj2 (ACL.wvb_fds_fs _ _ _)); exact Hfs]. }
split; [exact Hn26|]. split; [exact Hgood|].
split; [kt2_lia|]. split; [subst pn; kt2_lia|]. split; [subst pn; kt2_lia|].
split.
{ cbn [ms_regs mkst]. rewrite Ha0. unfold ANX.nx_res, ANX.nx_q. rewrite PcapEntryCalls.nxF_pC. reflexivity. }
split; [cbn [ms_regs mkst]; rewrite (HPk (18%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)),
          T18, (EW 18%nat 18%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl); exact R18|].
split; [cbn [ms_regs mkst]; rewrite (HPk (20%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)),
          T20, (EW 20%nat 20%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl); exact R20|].
split; [cbn [ms_regs mkst]; rewrite (HPk (21%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)),
          T21, (EW 21%nat 21%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl); exact R21|].
split; [cbn [ms_regs mkst]; rewrite (HPk (23%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)),
          T23, (EW 23%nat 23%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl); exact R23|].
split; [cbn [ms_regs mkst]; rewrite (HPk (24%bv : bv 5) ltac:(unfold acallee_saved; vm_compute bv_unsigned; kt2_lia)),
          T24, (EW 24%nat 24%bv ltac:(unfold A_TEXT; kt2_lia) eq_refl); exact R24|].
split; [cbn [ms_regs mkst]; exact S26|].
split; [exact (p_lslots_keepw cx fp W3 W2 ms3 (mkst regs2 (getr (ms_regs ms0) 1) mem2 (seg_rom SEGS)) _ buf
                 Hls MKW SAP ltac:(kt2_lia) ltac:(kt2_lia))|].
split; [exact (pslot_keepw_apart cx W3 W2 ms3 (mkst regs2 (getr (ms_regs ms0) 1) mem2 (seg_rom SEGS)) _ _ _
                 Hcalls MKW SAP ltac:(kt2_lia) ltac:(kt2_lia) ltac:(tauto))|].
split; [exact (pslot_keepw_apart cx W3 W2 ms3 (mkst regs2 (getr (ms_regs ms0) 1) mem2 (seg_rom SEGS)) _ _ _
                 Hfirst MKW SAP ltac:(kt2_lia) ltac:(kt2_lia) ltac:(tauto))|].
split; [exact (p_glob_keepw cx W3 W2 ms3 (mkst regs2 (getr (ms_regs ms0) 1) mem2 (seg_rom SEGS)) _ b Hglob MKW
                 ltac:(intros j Hj; apply NR; unfold kt2_foot; kt2_lia)
                 ltac:(intros j Hj; apply NR; unfold kt2_foot; kt2_lia))|].
(* p_reader at the new position: the call's post *)
destruct Hps2 as (Hf2 & Hsw2 & Hol2 & Hvt2 & Hvid2 & _).
unfold ANX.PS_F_OFF, ANX.PS_SW_OFF, ANX.PS_OL_OFF, ANX.PS_VT_OFF, ANX.PS_VID_OFF in Hf2, Hsw2, Hol2, Hvt2, Hvid2.
rewrite Z.add_0_r in Hf2.
unfold p_reader. cbn zeta.
split.
{ cbn [ms_mem mkst]. unfold ANX.nx_pos, ANX.nx_q in Hsrc2. rewrite PcapEntryCalls.nxF_pC in Hsrc2. exact Hsrc2. }
split; [split; [exact Hf2 | exact Hsw2]|].
intros Hk2.
pose proof (Ef Hk2) as Ef2.
assert (Hlh : PSN.psn_lh (p_sw cx) (p_F cx) (p_cap cx) pn = Some (p_q cx pn)).
{ apply PcapEntryCalls.k3_lh_fit; [kt2_lia | split; [subst pn; kt2_lia | fold (p_nF cx); subst pn; kt2_lia] | exact Hk2]. }
assert (Eo : ANX.nx_orig (p_swz cx =? 1) (p_C cx) (p_cap cx) pn (PSN.orig (p_sw cx) (p_F cx) (p_q cx p))
             = PSN.orig (p_sw cx) (p_F cx) (p_q cx pn)).
{ unfold ANX.nx_orig, ANX.nx_lh. rewrite PcapEntryCalls.nxF_pC.
  change (PSN.psn_lh (p_swz cx =? 1) (p_F cx) (p_cap cx) pn) with (PSN.psn_lh (p_sw cx) (p_F cx) (p_cap cx) pn).
  rewrite Hlh. reflexivity. }
rewrite Eo in Hol2.
unfold ANX.nx_vtag, ANX.nx_vid in Hvt2, Hvid2. rewrite Ef2 in Hvt2, Hvid2.
unfold ANX.nx_q in Hvt2, Hvid2. rewrite PcapEntryCalls.nxF_pC in Hvt2, Hvid2.
pose proof (Hts2 ltac:(kt2_lia)) as Hts3.
unfold ANX.nx_tsv in Hts3. rewrite Ef2 in Hts3. unfold ANX.nx_q in Hts3. rewrite PcapEntryCalls.nxF_pC in Hts3.
pose proof (Hbj'3 Ef2) as Hpre.
unfold ANX.nx_rec, ANX.nx_q in Hpre. rewrite PcapEntryCalls.nxF_pC in Hpre.
pose proof (kt2_garr8_firstn _ _ _
  (length (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes (p_swz cx =? 1) (p_F cx)
     (PSN.psn_q (p_swz cx =? 1) (p_F cx) (p_cap cx) pn)))) Hbj'1) as Hrec.
rewrite Hpre in Hrec.
cbn [ms_mem mkst]. unfold pval, pPS, pTS, PO_PS, PO_TS.
split; [exact Hol2|]. split; [exact Hvt2|]. split; [exact Hvid2|]. split; [exact Hts3 | exact Hrec].
Qed.

Lemma pe_from_KT2 : pe_from_KT2_stmt.
Proof.
unfold pe_from_KT2_stmt. intros POST HKL2.
apply (PcapEntrySkip.pe_from_meas_all B MT KS POST). intros m.
apply (pe_from_KT2_m m POST). apply (PcapEntrySkip.pe_meas_of B MT KS POST). exact HKL2.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The record loop PP_K4 -> PP_KR -> ... -> PP_KO -> PP_KT1 -> PP_KT2 -> PP_KL2 -> PP_K4, closed by induction on   *)
(* the bound m on |F| - s10: the turn adds 16 + incl > 16 to s10 (pe_from_KT2_m), every other cut keeps it.        *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* At the loop head the reader's fit record lies at or after s10 = p and ends inside F, so |F| - p >= 16. *)
Lemma pe_meas_K4_low : forall m cx fp k acc ly3 S3 W3 ms3 md3,
  PcapEntrySkip.pe_meas (GI_K4 B MT KS) m cx fp k acc ly3 S3 W3 ms3 md3 -> 16 <= m.
Proof.
intros m cx fp k acc ly3 S3 W3 ms3 md3 (HI & HM).
destruct HI as (b & h & buf & i & p & _ & Hn26 & _ & Hi0 & Hip & Hfit & _ & _ & _ & _ & _ & _ & R26 & _).
pose proof (p_sizes cx) as (HnF & _).
pose proof (p_le_q cx p) as HpQ.
destruct (kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) Hfit) as (Hi1 & _ & Hi3 & _).
fold (p_nF cx) in Hi3.
rewrite R26 in HM. unfold w64 in HM. rewrite unsigned_lit_small in HM by lia. lia.
Qed.

Lemma pe_recloop_fuel : forall (n : nat) m POST, m <= 16 * Z.of_nat n ->
  pe_from SK B MT KS POST (GI_K5 B MT KS) ->
  pe_from SK B MT KS POST (PcapEntrySkip.pe_meas (GI_K4 B MT KS) m).
Proof.
induction n as [|n IH]; intros m POST Hm HK5.
- intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HGI.
  exfalso. pose proof (pe_meas_K4_low m cx fp k acc ly3 S3 W3 ms3 md3 HGI). cbn [Z.of_nat] in Hm. lia.
- apply (PcapEntrySkip.pe_from_K4_m B MT KS LAWS ASIL POST).
  apply (PcapEntrySkip.pe_from_skip_m B MT KS LAWS TL ASIL POST).
  apply (pe_from_KO_m m POST). apply (pe_from_KT1_m m POST). apply (pe_from_KT2_m m POST).
  apply (pe_from_KL2_m (m - 16) POST); [| exact HK5].
  apply (IH (m - 16) POST); [rewrite Nat2Z.inj_succ in Hm; lia | exact HK5].
Qed.

Lemma pe_recloop : forall POST,
  pe_from SK B MT KS POST (GI_K5 B MT KS) -> pe_from SK B MT KS POST (GI_K4 B MT KS).
Proof.
intros POST HK5.
apply (PcapEntrySkip.pe_from_meas_all B MT KS POST). intros m.
apply (pe_recloop_fuel (Z.to_nat (Z.max m 0)) m POST); [|exact HK5].
pose proof (Z2Nat.id (Z.max m 0) ltac:(lia)) as Hid. lia.
Qed.

End c.
End b.
End a.
Arguments pe_from_KO_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_KT1_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_KT2_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_KL2_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_U_stmt {fx rc} SK {PI} B MT KS.
