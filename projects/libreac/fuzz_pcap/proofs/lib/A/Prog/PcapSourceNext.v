(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 76 of its 113 lines of code are new or changed and 543 lines of the source are left out. *)
(* pcap_source_next (0x8181c, listing offset AF_pcap_source_next = 0x10e4) on the ASan build of
   libreac v1.9.0: the contract tpcap_source_next_specX (lib/A/Prog/PcapSourceNextSpec.v) at this
   image (segs := SEGS, rlo := pa_relro_lo, rhi := pa_relro_hi, nstk := NX_STK), from the phases of
   the walk. The Section's hypotheses are the callee contracts (the fread wrapper, __asan_memmove,
   __asan_stack_malloc_0) and the laws of the allocator, the model, the meter and the stream.

   THE PHASES (each a lemma of the shape `nx_from POST GI_next -> nx_from POST GI_self`, one file
   per phase, each proved by its lane):
     entry   0x8181c -> NP_loop (the open reader) / NP_x0 (the closed reader)   PcapSourceNextEntry.v
     hdA     NP_loop -> NP_hd_ra (the header fread)                              PcapSourceNextHdrA.v
     hdB     NP_hd_ra -> NP_loop (KEmpty) / NP_sk1 / NP_fit / NP_exit            PcapSourceNextHdrB.v
     skip    NP_sk1 -> NP_loop (KBig) / NP_exit (KBig0, KCutBig)                 PcapSourceNextSkip.v
     fitA    NP_fit -> NP_ts / NP_exit (KCutFit)                                 PcapSourceNextFitA.v
     fitB    NP_ts -> NP_exit                                                    PcapSourceNextFitB.v
     exit    NP_exit -> NP_x0, and NP_x0 -> the return                          PcapSourceNextExit.v
   The invariants between them are nx_loop_inv / nx_exit_inv / nx_x0_inv (PcapSourceNextDefs.v),
   nx_hdra_inv (HdrBDefs), nx_sk1_inv (SkipDefs), nx_fit_inv (FitADefs), nx_ts_inv (FitBDefs).

   THE RECORD LOOP goes by induction on the bytes of the file left after the turn's start,
   |C| - q: a turn that goes back to the loop head does so at some q' with q < q' <= |C| (KEmpty:
   q + 16; KBig: q + 16 + incl, PcapSourceNextSpec.nx_chain_empty / nx_chain_big), so the turn
   lemmas take the loop head as `nx_from POST (nx_loop_at R)` and the start of the turn carries
   `nx_next_ok R cx q`. The skip loop's own measure is inside the skip phase. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YE01 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC45 YC85 YC88 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceNextExit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextFitBDefs PcapSourceNextFitB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import
PcapSourceNextSkipDefs PcapSourceNextFitADefs PcapSourceNextHdrBDefs PcapSourceNextHdrB PcapSourceNextHdrA
PcapSourceNextSkip PcapSourceNextFitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

#[local] Notation POST := (nx_post SK B MT KS).
#[local] Notation FROM := (nx_from SK B KS POST).
#[local] Notation GIT :=
  (ncx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) (only parsing).

(* ---- the callee contracts and laws the proved phases take ---- *)

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
(* __asan_stack_malloc_0, by cgif's name (YG0d.v:285; StackMalloc0.stack_malloc0_contract's type at
   class 0), and the model's progress law for a class-0 frame. *)
Hypothesis ASM0 : astack_malloc_realizes SEGS B NX_CID.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.
(* The fread wrapper's contract, at the trampoline's entry (the three fread sites of the body). *)
Hypothesis AFREAD : afread_spec SK SEGS B KS (pa_sigma PS___interceptor_trampoline_fread).
(* __asan_memmove's contract, at its entry (the record's VLAN-tag memmove). *)
Hypothesis AMM : amemmove_realizes SEGS B (pa_sigma PS___asan_memmove).

(* ---- the composition ---- *)

(* a Theorem Labs lane (PcapSourceNextExit.v): NP_x0 -> ret, and NP_exit -> ret. *)
Lemma nx_x0_ok : FROM (nx_x0_inv B MT KS).
Proof. exact (nx_x0_ph (SK:=SK) B MT KS LAWS ML MTF ASF FFL ASIL). Qed.

Lemma nx_exit_ok : FROM (nx_exit_inv B MT KS).
Proof. exact (nx_exit_from (SK:=SK) B MT KS LAWS ML MTF ASF FFL ASIL nx_x0_ok). Qed.

(* a Theorem Labs lane (PcapSourceNextFitB.v): NP_ts -> NP_exit. *)
Lemma nx_ts_ok : FROM (nx_ts_inv B MT KS).
Proof. exact (pb_nx_tsX (SK:=SK) B MT KS LAWS ASIL nx_exit_ok). Qed.

(* a Theorem Labs lane (PcapSourceNextFitA.v, with a Theorem Labs lane's memmove call PcapSourceNextFitACall.v): NP_fit ->
   NP_ts / NP_exit. *)
Lemma nx_fit_ok : FROM (nx_fit_inv B MT KS).
Proof. exact (fa_fit_phase (SK:=SK) B MT KS LAWS AFREAD ASIL AMM nx_ts_ok nx_exit_ok). Qed.

Lemma nx_loop_inv_q : forall cx fp q lh k2 ly3 S3 W3 ms3 md3,
  nx_loop_inv B MT KS cx fp q lh k2 ly3 S3 W3 ms3 md3 -> n_p cx <= q <= Z.of_nat (length (n_C cx)).
Proof.
intros cx fp q lh k2 ly3 S3 W3 ms3 md3 ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hq & _) & _). exact Hq.
Qed.

(* The loop heads whose file has fewer than n bytes left. *)
Definition nx_lt (n : nat) : ncx -> Z -> Prop :=
  fun cx q => 0 <= Z.of_nat (length (n_C cx)) - q < Z.of_nat n.

Lemma nx_loop_ok_n : forall n, FROM (nx_loop_at B MT KS (nx_lt n)).
Proof.
induction n as [|n IH].
- intros cx fp k2 ly3 S3 W3 ms3 md3 _ _ _ (q & lh & Hlt & _). unfold nx_lt in Hlt. cbn [Z.of_nat] in Hlt. lia.
- (* a Theorem Labs lane (PcapSourceNextSkip.v): NP_sk1 -> NP_loop (KBig, through a Theorem Labs lane's nx_empty_step) / NP_exit. *)
  pose proof (pb_skip (SK:=SK) B MT KS LAWS TL AFREAD ASIL (nx_lt n) IH nx_exit_ok) as HSK1.
  (* a Theorem Labs lane (PcapSourceNextHdrB.v): NP_hd_ra -> NP_loop / NP_sk1 / NP_fit / NP_exit. *)
  pose proof (pb_nx_hdrB (SK:=SK) B MT KS LAWS TL ASIL POST (nx_lt n) IH HSK1 nx_fit_ok nx_exit_ok) as HHD.
  (* The hdA phase (PcapSourceNextHdrA.v): NP_loop -> NP_hd_ra (the header fread). *)
  pose proof (pb_hdA SK B MT KS LAWS ASIL AFREAD (nx_lt n) HHD) as TURN.
  intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF (q & lh & Hlt & HL).
  apply (TURN cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF).
  exists q, lh. split; [|exact HL].
  intros q' Hq'. unfold nx_lt in *. rewrite Nat2Z.inj_succ in Hlt. lia.
Qed.

Lemma nx_loop_ok : FROM (nx_loop_at B MT KS (fun _ _ => True)).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF (q & lh & _ & HL).
pose proof (nx_loop_inv_q _ _ _ _ _ _ _ _ _ _ HL) as Hq.
apply (nx_loop_ok_n (S (Z.to_nat (Z.of_nat (length (n_C cx)) - q))) cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF).
exists q, lh. split; [|exact HL].
unfold nx_lt. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.

(* ---- the contract ---- *)

Theorem pb_pcap_source_nextX :
  tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NX_STK B MT KS (BASE + AF_pcap_source_next).
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
(* The entry phase (PcapSourceNextEntry.v): 0x8181c -> NP_loop / NP_x0. *)
exact (nx_entryX (SK:=SK) B MT KS LAWS TL TLF ML MTL MTF ASM0 SMP FFL ASIL POST nx_loop_ok nx_x0_ok cx HB).
Qed.

End c.
End b.
End a.

Arguments pb_pcap_source_nextX {fx rc} SK {PI}.
