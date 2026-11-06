(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/RepPrfS.v (commit 4d286b2e618d, file sha256 7be1f8d166f2) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 14 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 17 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepPrfS.v (commit f01d79f3fb5, cf refill round 3; file sha256 0d5e74ef2b40) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 14 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 14 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (the internal file accept.tsv, re-measured each run): _ZN11__sanitizer9VSNPrintfEPciPKcPv+0x1c0 (data-differs: ACCEPTED by hand: jump table (33 entries, each the same VSNPrintf+off on both images))), and 18 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker's class-full report walk, slice F2): the symbolic states of
   __sanitizer::Printf's silent path at cgif_file_fuzzer's asan-ubsan image (pin 1c29845fe605), and the four runs
   that join them.  The walk, with P = Printf's entry sp:
     Printf 0x67f24 (frame 0x50, the va_list at P - 56) -> SharedPrintfCode 0x68628 (frame 0x1b0, the 400-byte
     buffer at P - 512) -> internal_memset 0x64ba4 of that buffer to 0xaa (run 1, then the kit YB15.tfib_imemset)
     -> SharedPrintfCodeNoBuffer 0x6852c (frame 0x80, append_pid = 0) -> VSNPrintf 0x6795c (run 2; its contract is
     a hypothesis) -> RawWrite 0x61a58 = internal_strlen 0x64cf8 + ReportFile::Write 0x67628, which returns at once
     because the RELRO word 0xa3418 is 1, RemoveANSIEscapeSequencesFromString 0x60f2c (no ESC byte in a line),
     __sanitizer_on_print 0x685d8 (a ret), the callback *0x137f90 = AppendToErrorMessageBuffer 0x55df8 (run 3; its
     contract is a hypothesis) -> LogMessageOnPrintf 0x6e064 (log_to_syslog, the byte at 0x137de8, is 0),
     UnmapOrDie(0, 0) 0x66bf4, and the three epilogues to Printf's ret 0x67f6c (run 4).
   rule 24: proves function __sanitizer::Printf (with RepPrfcf.v; reuse search: ossv proof index v5, built
   2026-10-30T01:54:20Z, `proof-index VSNPrintf Printf SharedPrintfCode AppendNumber
   AppendToErrorMessageBuffer MmapOrDie` 2026-10-30T02:25:54Z exit 0: the unit's ten lines are all `address` rows
   of its symbol and decode tables, nothing reusable). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0m YF0x YFl0 YFl2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RepIFcf RepPrfD.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

Definition runR (pc : Z) (ss : sstate) : sstate * run_status := sym_run_toN_sh tfibsegs reptbl FUEL pc ss.
Definition pin (ss : sstate) (r : bv 5) (e : sv) : sstate :=
  mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition addreg (r : YP09.region) (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The seed at Printf's entry.  Atom 2 is the entry sp P; the window [P - PR_STK, P) is three regions, the low
   one holding the callees' frames (VSNPrintf's and AppendToErrorMessageBuffer's), then
   SharedPrintfCodeNoBuffer's frame, then SharedPrintfCode's saved registers and Printf's frame.  The 400-byte
   buffer [P - 512, P - 112) is NOT a region of the seed: internal_memset and VSNPrintf write it, and nothing
   before the two buffer regions of section 2 reads it. *)
Definition R_LOW : YP09.region := YP09.mkRegion (Some 2%nat) (- PR_STK) (-640) (- PR_STK) (-640) [].
Definition R_NB : YP09.region := YP09.mkRegion (Some 2%nat) (-640) (-512) (-640) (-512) [].
Definition R_TOP : YP09.region := YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 [].
Definition PCONST : smem := [lit8 C_PFCB A_APPEND; lit8 C_SILENT 1].
Definition PMEM0 : smem := [R_LOW; R_NB; R_TOP] ++ PCONST.
Definition PFF : facts := mkFacts [(2%nat, mkAF (kHighMemBeg + PR_STK) kHighMemEnd 4)] [] [].
Definition SS_P0 : sstate := mkSS A_PRINTF sr_atoms PMEM0 None PFF.

(* run 1: the two prologues, to internal_memset's entry. *)
Definition P1r : sstate * run_status := Eval vm_compute in runR 0x64ba4 SS_P0.
(* the memset kit's effect: it clobbers a1, a2, a3 and returns to 0x67fa0; the buffer it writes is in no region. *)
Definition P1s : sstate := Eval vm_compute in ss_after_stretch (fst P1r) (ss_mem (fst P1r)) 32 [11; 12; 13]%bv 0x67fa0.
(* run 2: SharedPrintfCodeNoBuffer's prologue and its append_pid = 0 branch, to VSNPrintf's entry. *)
Definition P2r : sstate * run_status := Eval vm_compute in runR A_VSNPRINTF P1s.
(* VSNPrintf returns at 0x6860c.  R_LOW is dropped over the call (its window holds VSNPrintf's frame). *)
Definition P2c : sstate := Eval vm_compute in ss_after_call (fst P2r) (skipn 1 (ss_mem (fst P2r))) 35 0x6860c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The rendered line in the buffer: its bytes read-only, its NUL writable (RemoveANSIEscapeSequencesFromString
   rewrites the NUL and nothing else, since no byte of a line is ESC). *)
Definition bufchunks (out : list Z) : list YP09.chunk :=
  map (fun p => YP09.mkChunk (-512 + Z.of_nat (fst p)) (CVal 1 (SLit (snd p)))) (combine (seq 0 (length out)) out).
Definition R_BUF (out : list Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-512) (-512 + Z.of_nat (length out)) 0 0 (bufchunks out).
Definition R_NUL (out : list Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-512 + Z.of_nat (length out)) (-511 + Z.of_nat (length out))
    (-512 + Z.of_nat (length out)) (-511 + Z.of_nat (length out))
    [YP09.mkChunk (-512 + Z.of_nat (length out)) (CVal 1 (SLit 0))].
Definition P3s (out : list Z) : sstate :=
  pin (addreg (R_BUF out) (addreg (R_NUL out) (addreg R_LOW P2c))) 10%bv (SLit (Z.of_nat (length out))).
(* run 3: RawWrite, RemoveANSIEscapeSequencesFromString, __sanitizer_on_print and the callback load, to
   AppendToErrorMessageBuffer's entry with a0 = the buffer and ra = 0x68640. *)
Definition P3r (out : list Z) : sstate * run_status := runR A_APPEND (P3s out).
Definition P3e (out : list Z) : sstate := fst (P3r out).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The lines of the arm: the first format's, and the second's at each of the 31 classes. *)
Definition OUTS : list (list Z) := render1 :: map (fun c => render2 c (class_size c)) (map Z.of_nat (seq 1 31)).
Lemma OUTS_render2 : forall c, 1 <= c <= 31 -> In (render2 c (class_size c)) OUTS.
Proof.
intros c Hc. unfold OUTS. right. apply in_map_iff. exists c. split; [reflexivity|].
apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma OUTS_len : forallb (fun out => Z.of_nat (length out) <? 400) OUTS = true.
Proof. vm_compute. reflexivity. Qed.
(* The state run 3 reaches, as a function of the line: the line's length is in a2, a3 and s5 (the callback's
   arguments and RemoveANSIEscapeSequencesFromString's cursor), nothing else of it is left in the registers, and
   the memory below the buffer is the same for every line. *)
Definition P3regs (len : Z) : list sv :=
[SLit 0; SLit 0x68640; SOff 2 (-640); SOff 3 0; SOff 4 0; SOff 36 0; SOff 37 0; SOff 38 0;
 SOff 10 0; SLit 0; SOff 2 (-512); SLit A_APPEND; SLit len; SOff 2 (-513 + len); SOff 43 0; SOff 44 0;
 SOff 45 0; SOff 46 0; SOff 2 (-512); SLit 400; SOff 20 0; SLit len; SOff 22 0; SOff 23 0;
 SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0]%nat.
Definition R_LOW3 : YP09.region := YP09.mkRegion (Some 2%nat) (- PR_STK) (-640) (- PR_STK) (-640)
 [YP09.mkChunk (-672) (CVal 8 (SOff 2 (-512))); YP09.mkChunk (-664) (CVal 8 (SLit 0));
  YP09.mkChunk (-656) (CVal 8 (SOff 10 0)); YP09.mkChunk (-648) (CVal 8 (SLit 0x68624))]%nat.
Definition R_NB3 : YP09.region := YP09.mkRegion (Some 2%nat) (-640) (-512) (-640) (-512)
 [YP09.mkChunk (-624) (CVal 8 (SLit 0)); YP09.mkChunk (-632) (CVal 8 (SLit 0));
  YP09.mkChunk (-640) (CVal 8 (SLit 0)); YP09.mkChunk (-616) (CVal 8 (SOff 2 (-56)));
  YP09.mkChunk (-608) (CVal 8 (SOff 2 (-56))); YP09.mkChunk (-600) (CVal 8 (SOff 25 0));
  YP09.mkChunk (-592) (CVal 8 (SOff 24 0)); YP09.mkChunk (-584) (CVal 8 (SOff 23 0));
  YP09.mkChunk (-576) (CVal 8 (SOff 22 0)); YP09.mkChunk (-568) (CVal 8 (SOff 21 0));
  YP09.mkChunk (-560) (CVal 8 (SOff 20 0)); YP09.mkChunk (-552) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-544) (CVal 8 (SLit 0)); YP09.mkChunk (-536) (CVal 8 (SOff 10 0));
  YP09.mkChunk (-528) (CVal 8 (SOff 2 (-56))); YP09.mkChunk (-520) (CVal 8 (SLit 0x67fb4))]%nat.
Definition R_TOP3 : YP09.region := YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0
 [YP09.mkChunk (-112) (CVal 8 (SOff 18 0)); YP09.mkChunk (-104) (CVal 8 (SOff 9 0));
  YP09.mkChunk (-96) (CVal 8 (SOff 8 0)); YP09.mkChunk (-88) (CVal 8 (SLit 0x67f64));
  YP09.mkChunk (-80) (CVal 8 (SOff 2 (-56))); YP09.mkChunk (-32) (CVal 8 (SOff 14 0));
  YP09.mkChunk (-40) (CVal 8 (SOff 13 0)); YP09.mkChunk (-48) (CVal 8 (SOff 12 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 11 0)); YP09.mkChunk (-8) (CVal 8 (SOff 17 0));
  YP09.mkChunk (-16) (CVal 8 (SOff 16 0)); YP09.mkChunk (-24) (CVal 8 (SOff 15 0));
  YP09.mkChunk (-72) (CVal 8 (SOff 1 0))]%nat.
Definition P3tail : smem := [R_LOW3; R_NB3; R_TOP3] ++ PCONST.
Definition P3end (out : list Z) : sstate :=
  mkSS A_APPEND (P3regs (Z.of_nat (length out))) (R_BUF out :: R_NUL out :: P3tail) None PFF.
Lemma P3_ends : Forall (fun out => P3r out = (P3end out, RS_running)) OUTS.
Proof. repeat (apply Forall_cons; [vm_compute; reflexivity|]). apply Forall_nil. Qed.

(* AppendToErrorMessageBuffer returns at 0x68640.  Only SharedPrintfCodeNoBuffer's frame and the top of the
   window survive the call as regions: the two buffer regions and R_LOW3 go (the callee's frame is in R_LOW3's
   window) and the two image cells of PCONST go (the callback's cell is in the allocator's owned set).  R_LOW
   comes back chunkless, with the two cells LogMessageOnPrintf reads (the GOT word of common_flags and its
   log_to_syslog byte, both in TfibSyms' as_const, YF0m.v).  s5 is forgotten with the caller-saved registers,
   so what the tail runs over does not depend on the line. *)
Definition R_CFG : YP09.region := lit8 0xa2840 0x13d228.
Definition R_SYSLOG : YP09.region := lit8 0x13d268 0.
Definition CLOBP : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 28; 29; 30; 31]%bv.
Definition P4keep : smem := [R_NB3; R_TOP3].
Definition P4s (out : list Z) : sstate :=
  addreg R_SYSLOG (addreg R_CFG (addreg R_LOW (ss_after_stretch (P3end out) P4keep 51 CLOBP 0x68640))).
Definition P4S : sstate := Eval vm_compute in P4s [].
Lemma P4s_const : forall out, P4s out = P4S.
Proof. intros out. unfold P4s, P4S, P3end, ss_after_stretch. vm_compute. reflexivity. Qed.
(* run 4: LogMessageOnPrintf, UnmapOrDie(0, 0) and the three epilogues, to Printf's ret. *)
Definition P4R : sstate * run_status := Eval vm_compute in runR 0x67f6c P4S.
Definition P4E : sstate := Eval vm_compute in fst P4R.
Lemma P4_run : runR 0x67f6c P4S = (P4E, RS_running).
Proof. vm_compute. reflexivity. Qed.


(* The runs reach the entries they must: run 1 internal_memset, run 2 VSNPrintf, run 3 the callback, run 4 the ret. *)
Lemma P12_pcs : snd P1r = RS_running /\ ss_pc (fst P1r) = 0x64ba4 /\ snd P2r = RS_running /\ ss_pc (fst P2r) = A_VSNPRINTF.
Proof. vm_compute. repeat split; reflexivity. Qed.
