(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 101 of its 135 lines of code are new or changed and 546 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8, listing offset AF_pcap_source_next = 0xe30) on the ASan+UBSan
   build of libreac v1.9.0: lib/A's image-generic contract tpcap_source_next_specX (lib/A/Prog/PcapSourceNextDefs.v)
   at this image (segs := SEGS, rlo := pa_relro_lo, rhi := pa_relro_hi of lib/B's PAImg, nstk := NX_STK_B), from
   the phases of the walk. The composition is lib/A/Prog/PcapSourceNext.v's, over lib/B's phase layer
   (lib/B/Prog/PcapSourceNextDefs.v).

   THE PHASES (each a lemma of the shape `nx_from POST GI_next -> nx_from POST GI_self`, one file per phase):
     entry   0x815b8 -> NP_loop 0x8174c (the open reader) / NP_x0 0x818cc (the closed reader)  PcapSourceNextEntry.v
     hdA     NP_loop -> NP_hd_ra 0x81770 (the header fread 0x8176c)                           PcapSourceNextHdrA.v
     hdB     NP_hd_ra -> (rd_u32 x4: 0x81788, 0x817a8, 0x817c8, 0x817f0) -> NP_loop (KEmpty) /
             NP_sk1 0x81814 / NP_fit 0x81988 / NP_exit 0x818b4                                PcapSourceNextHdrB.v
     skip    NP_sk1 -> NP_loop (KBig) / NP_exit (KBig0, KCutBig)                              PcapSourceNextSkip.v
     fitA    NP_fit -> NP_ts 0x81b1c / NP_exit (KCutFit)                                      PcapSourceNextFitA.v
     fitB    NP_ts -> NP_exit                                                                 PcapSourceNextFitB.v
     exit    NP_exit -> NP_x0, and NP_x0 -> the return 0x8196c                                PcapSourceNextExit.v
   Every phase is a proved lemma (nx_entryX, nxb_hdA_ph, nx_hdrb_ph, nxb_skip_ph, pb_nx_fitA, pb_nx_tsX, nx_exit_from /
   nx_x0_ph), over the entry predicates its lane defines (nx_hdra_inv, PcapSourceNextHdrBDefs.v; nx_sk1_inv,
   PcapSourceNextSkipDefs.v; nx_fit_inv, PcapSourceNextFitADefs.v; nx_ts_inv, PcapSourceNextFitBDefs.v).

   THE CALLEES the phases call, as Section hypotheses of their exact statement types (one per callee; the phase
   lemmas take them as theirs): the fread wrapper (afread_spec, lib/A/Stdio/PFreadISpec.v) at its three sites,
   __asan_memmove (amemmove_realizes, lib/A/Rt/MemmoveDef.v), __asan_stack_malloc_0 (astack_malloc_realizes 0,
   Reusable/YG0d.v), and the laws of the allocator, the model, the meter, the frames, the kit and the stream. rd_u32
   (trd_u32_specX, lib/B/Prog/RdU32.v) at its four sites is not a hypothesis: a Theorem Labs lane's walk proves it (pb_rd_u32X).
   No phase is a hypothesis.

   THE RECORD LOOP goes by induction on the bytes of the file left after the turn's start, as lib/A's.

   THE REQUIRE CLOSURE of this file (porter 01:25Z) holds lib/B files, the core and only image-free lib/A modules:
   the shared statement comes from lib/A/Prog/PcapSourceNextSpec.v (through lib/B PcapSourceNextDefs), the kit from
   lib/A PcapSourceNextKitG (through lib/B PcapSourceNextKit), the seat from lib/A PcapSourceNextSeatG (through lib/B
   PcapSourceNextSeat); no file here Requires lib/A PcapSourceNextDefs / Kit / Seat or any PcapSourceClose. The
   commit that wires a phase states `Print Libraries` for it. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import RdU32.
(* The phases, one file each (PcapSourceNextEntry, PcapSourceNextHdrA, PcapSourceNextHdrB, PcapSourceNextSkip, PcapSourceNextFitA, PcapSourceNextFitB, PcapSourceNextExit). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextExit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextFitBDefs PcapSourceNextFitB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextHdrBDefs PcapSourceNextHdrA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextSkipDefs PcapSourceNextFitADefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextFitA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextHdrB PcapSourceNextSkip.
(* LAST: lib/B's phase layer (it exports lib/A's image-free Spec for the shared statement). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* ---- the callees and the laws (the phase lemmas' Section hypotheses) ---- *)

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.
Hypothesis H_sm0 : astack_malloc_realizes SEGS B 0.                          (* class NX_CID = 0; 0x81634 *)
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis H_fread :
  afread_spec SK SEGS B KS (@pa_sigma _ pcap_listing PI PS___interceptor_trampoline_fread). (* 0x8176c, 0x81848, 0x819a4 *)
Hypothesis H_memmove : amemmove_realizes SEGS B (@pa_sigma _ pcap_listing PI PS___asan_memmove). (* 0x81af4 *)
(* rd_u32 (0x81788, 0x817a8, 0x817c8, 0x817f0) is proved: a Theorem Labs lane's pb_rd_u32X (lib/B/Prog/RdU32.v). *)
Lemma nxb_rdu32 : trd_u32_specX SK SEGS B (BASE + AF_rd_u32).
Proof. apply (@pb_rd_u32X _ _ SK _ B); assumption. Qed.

#[local] Abbreviation POST := (nx_post SK B MT KS).
#[local] Abbreviation FROM := (nx_from SK B KS POST).

(* ---- the composition ---- *)

(* The exit phases (PcapSourceNextExit.v). *)
Lemma nxb_x0_ok : FROM (nx_x0_inv B MT KS).
Proof. apply (nx_x0_ph SK); assumption. Qed.

Lemma nxb_exit_ok : FROM (nx_exit_inv B MT KS).
Proof. apply (nx_exit_from SK); first [exact nxb_x0_ok | assumption]. Qed.

(* NP_ts -> NP_exit (PcapSourceNextFitB.v). *)
Lemma nxb_ts_ok : FROM (nx_ts_inv B MT KS).
Proof. apply (@pb_nx_tsX _ _ SK _); first [exact nxb_exit_ok | assumption]. Qed.

(* NP_fit -> NP_ts / NP_exit (PcapSourceNextFitA.v). *)
Lemma nxb_fit_ok : FROM (nx_fit_inv B MT KS).
Proof. apply (@pb_nx_fitA _ _ SK _ B MT KS); first [exact nxb_ts_ok | exact nxb_exit_ok | assumption]. Qed.

(* NP_loop -> NP_hd_ra (a Theorem Labs lane, PcapSourceNextHdrA.v). *)
Lemma nxb_hdA_ok : forall R : ncx -> Z -> Prop,
  FROM (nx_hdra_inv B MT KS R) ->
  FROM (fun cx fp k2 ly3 S3 W3 ms3 md3 =>
          exists q lh, nx_next_ok R cx q /\ nx_loop_inv B MT KS cx fp q lh k2 ly3 S3 W3 ms3 md3).
Proof. intros R HN. apply (@nxb_hdA_ph _ _ SK _ B MT KS); first [exact HN | assumption]. Qed.

(* NP_hd_ra -> NP_loop / NP_sk1 / NP_fit / NP_exit, through the four rd_u32 calls (a Theorem Labs lane,
   PcapSourceNextHdrB.v). *)
Lemma nxb_hdB_ok : forall R : ncx -> Z -> Prop,
  FROM (nx_loop_at B MT KS R) -> FROM (nx_sk1_inv B MT KS R) -> FROM (nx_fit_inv B MT KS) ->
  FROM (nx_exit_inv B MT KS) -> FROM (nx_hdra_inv B MT KS R).
Proof.
intros R H1 H2 H3 H4. apply (@nx_hdrb_ph _ _ SK _ B MT KS);
  first [exact H1 | exact H2 | exact H3 | exact H4 | exact nxb_rdu32 | assumption].
Qed.

(* NP_sk1 -> NP_loop (KBig) / NP_exit (KBig0, KCutBig) (a Theorem Labs lane, PcapSourceNextSkip.v). *)
Lemma nxb_skip_ok : forall R : ncx -> Z -> Prop,
  FROM (nx_loop_at B MT KS R) -> FROM (nx_exit_inv B MT KS) -> FROM (nx_sk1_inv B MT KS R).
Proof. intros R H1 H2. apply (@nxb_skip_ph _ _ SK _ B MT KS); first [exact H1 | exact H2 | assumption]. Qed.

Lemma nxb_loop_inv_q : forall cx fp q lh k2 ly3 S3 W3 ms3 md3,
  nx_loop_inv B MT KS cx fp q lh k2 ly3 S3 W3 ms3 md3 -> n_p cx <= q <= Z.of_nat (length (n_C cx)).
Proof.
intros cx fp q lh k2 ly3 S3 W3 ms3 md3 ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hq & _) & _).
exact Hq.
Qed.

(* The loop heads whose file has fewer than n bytes left. *)
Definition nxb_lt (n : nat) : ncx -> Z -> Prop :=
  fun cx q => 0 <= Z.of_nat (length (n_C cx)) - q < Z.of_nat n.

Lemma nxb_loop_ok_n : forall n, FROM (nx_loop_at B MT KS (nxb_lt n)).
Proof.
induction n as [|n IH].
- intros cx fp k2 ly3 S3 W3 ms3 md3 _ _ _ (q & lh & Hlt & _). unfold nxb_lt in Hlt. cbn [Z.of_nat] in Hlt. lia.
- pose proof (nxb_skip_ok (nxb_lt n) IH nxb_exit_ok) as HSK1.
  pose proof (nxb_hdB_ok (nxb_lt n) IH HSK1 nxb_fit_ok nxb_exit_ok) as HHD.
  pose proof (nxb_hdA_ok (nxb_lt n) HHD) as TURN.
  intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF (q & lh & Hlt & HL).
  apply (TURN cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF).
  exists q, lh. split; [|exact HL].
  intros q' Hq'. unfold nxb_lt in *. rewrite Nat2Z.inj_succ in Hlt. lia.
Qed.

Lemma nxb_loop_ok : FROM (nx_loop_at B MT KS (fun _ _ => True)).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF (q & lh & _ & HL).
pose proof (nxb_loop_inv_q _ _ _ _ _ _ _ _ _ _ HL) as Hq.
apply (nxb_loop_ok_n (S (Z.to_nat (Z.of_nat (length (n_C cx)) - q))) cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF).
exists q, lh. split; [|exact HL].
unfold nxb_lt. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.

(* ---- the contract ---- *)

Theorem pb_pcap_source_nextX :
  tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NX_STK_B B MT KS (BASE + AF_pcap_source_next).
Proof.
unfold tpcap_source_next_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps buf cap ts h b p sw lol lvt lvid tsv M
  cid pos C bj pad ch.
intros.
set (cx := mkNCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps buf cap ts h b p sw
  lol lvt lvid tsv M cid pos C bj pad ch (Ereg regs [])).
assert (HB : nx_base SK B KS cx).
{ unfold nx_base.
  (* every premise by name; `split` closes the atom equation for sp by eq_refl *)
  repeat (first [assumption | split]).
  all: first [ intros n0 r0 Hn0; exact (ew_Ereg_nat regs [] n0 r0 Hn0)
             | exact (f_equal (fun w => bv_unsigned w) (ew_Ereg_nat regs [] 2 2%bv eq_refl)) ]. }
(* The entry phase (PcapSourceNextEntry.v). *)
assert (HS : nx_start SK B KS POST)
  by (apply (@nx_entryX _ _ SK _ B MT KS); first [exact nxb_loop_ok | exact nxb_x0_ok | assumption]).
exact (HS cx HB).
Qed.

End c.
End b.
End a.

Arguments pb_pcap_source_nextX {fx rc} SK {PI}.
