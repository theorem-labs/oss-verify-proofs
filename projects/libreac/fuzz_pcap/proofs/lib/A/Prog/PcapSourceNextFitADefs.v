(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the entry predicate of the phase
   at NP_fit (listing offset 0x1408, address 0x81b40), where the header of a record that the buffer
   can hold (0 < incl <= cap) has been read. The phase itself (0x81b40 .. 0x81ce4) is walked in
   lib/A/Prog/PcapSourceNextFitA.v.

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin, capstone 5 disassembly
   next.dis (sha256 06286410ee55; internal record)).

   WHAT THE HEADER PHASE LEAVES AT 0x81b40 (the path 0x819bc .. 0x81abc `bgeu s7,s11` taken):
     a0          the swap word ps->sw          `ld a0,0x58(s1); lw a0,0(a0)` 0x819e4, 0x819e8
     a2 t1 a7 t0 header bytes 0, 1, 2, 3      `lbu a2,0(s10)` .. `lbu t0,3(s10)` 0x81a98 .. 0x81aa4
     a1 a6 a4 a5 header bytes 4, 5, 6, 7      `lbu a1,4(s10)` .. `lbu a5,7(s10)` 0x81a80 .. 0x81a8c
     s9          incl (sign-extended 32 bits; incl <= cap <= 2040, so it is incl)   0x81a00 / 0x81a28
     s11         incl (zero-extended)          `slli t2,s9,0x20; srli s11,t2,0x20` 0x81aac, 0x81ab0
     s6          -1                            `addi s6,zero,-1` 0x819bc
     s4 s5 s7 s8 buf, ps, cap, the shadow byte address of ps (0x8186c, 0x81888, 0x81868, 0x81924)
     s2 s3       F and the shadow address of F
   and ps->orig written (`sw a3,0(t2)` 0x81ab8): the struct's orig field holds the record's orig_len.
   The stream stands after the 16-byte header (q + 16). *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* THE ENTRY PREDICATE AT NP_fit (0x81b40). q is the position of the record in the file: the model's
   final position (nx_q), with the record's header the last non-empty one (nx_lh = Some q). Its
   header has been read, so the stream stands at q + 16; its incl is not 0 and the buffer can hold it
   (incl <= cap). ps->orig holds the record's orig_len; ps->vtag, ps->vid and ts are the caller's.
   The middle state is the shared nx_mid (PcapSourceNextDefs.v) at NP_fit with `ph` in scope. *)
Definition nx_fit_inv (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  let sw := (n_sw cx =? 1) in
  let F := nxF (n_C cx) in
  let R := ms_regs ms3 in
  exists q : Z,
  nx_mid B MT KS cx fp NP_fit NSH_ph (nx_E cx) (q + 16) (PSN.orig sw F q) (n_lvt cx) (n_lvid cx)
    (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
  (* the model: the record q *)
  nx_q sw (n_C cx) (n_cap cx) (n_p cx) = q /\
  nx_lh sw (n_C cx) (n_cap cx) (n_p cx) = Some q /\
  n_p cx <= q /\
  0 < PSN.incl sw F q <= n_cap cx /\
  (* the registers (s2, s3, s8 are nx_mid's) *)
  getr R 10 = w64 (n_sw cx) /\                                                   (* a0: ps->sw *)
  getr R 12 = w64 (PSN.fb F q) /\ getr R 6 = w64 (PSN.fb F (q + 1)) /\          (* a2, t1 *)
  getr R 17 = w64 (PSN.fb F (q + 2)) /\ getr R 5 = w64 (PSN.fb F (q + 3)) /\    (* a7, t0 *)
  getr R 11 = w64 (PSN.fb F (q + 4)) /\ getr R 16 = w64 (PSN.fb F (q + 5)) /\    (* a1, a6 *)
  getr R 14 = w64 (PSN.fb F (q + 6)) /\ getr R 15 = w64 (PSN.fb F (q + 7)) /\    (* a4, a5 *)
  getr R 20 = w64 (n_buf cx) /\ getr R 21 = w64 (n_ps cx) /\                     (* s4, s5 *)
  getr R 22 = w64 (-1) /\ getr R 23 = w64 (n_cap cx) /\                          (* s6, s7 *)
  getr R 25 = w64 (PSN.incl sw F q) /\ getr R 27 = w64 (PSN.incl sw F q).        (* s9, s11 *)

End c.
End b.
End a.

(* nx_fit_inv names no sink head (asource_at takes none), so SK is not among its binders: its
   arguments are {fx rc} {PI} B MT KS and the eight of a phase predicate (fx: nx_body0 states the
   floating-point state). *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (PI : PAImg pcap_listing) (B : asyms) (MT : ameter_ops)
  (KS : asource_syms) => @nx_fit_inv fx rc PI B MT KS).
