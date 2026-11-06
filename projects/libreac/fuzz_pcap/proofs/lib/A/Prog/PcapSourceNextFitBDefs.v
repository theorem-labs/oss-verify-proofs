(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the entry predicate of the phase
   at NP_ts (listing offset 0x15ac, address 0x81ce4), where a record that fits has been read into the
   caller's buffer and its VLAN tag (if any) stripped. The phase itself (0x81ce4 .. 0x81d24) is walked
   in lib/A/Prog/PcapSourceNextFitB.v.

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin, capstone 5 disassembly).

   THE CODE OF THE PHASE (0x81ce4 .. 0x81d20):
     0x81ce4 beqz s5,0x81d1c          the caller asked for no timestamp (s5 = &ts, reloaded 0x81c08)
     0x81ce8 srli a0,s5,3
     0x81cec ld   a1,0x28(s1)         the shadow base, from the spill slot NS_SB
     0x81cf0 add  a0,a0,a1
     0x81cf4 lbu  a0,0(a0)            the shadow byte of ts
     0x81cf8 bnez a0,0x81e88          the error path (__asan_report_store8), not taken
     0x81cfc lui  a0,0x3d09
     0x81d00 slli s10,s10,0x20        the seconds, in the high word
     0x81d04 slli s7,s7,0x20          the microseconds, in the high word
     0x81d08 slli a0,a0,0x1a          a0 = 0x3d09 << 38 = 10^6 * 2^32
     0x81d0c mulhu a0,s10,a0          a0 = sec * 10^6
     0x81d10 srli a1,s7,0x20          a1 = usec
     0x81d14 add  a0,a0,a1
     0x81d18 sd   a0,0(s5)            ts := sec * 10^6 + usec
     0x81d1c slli s9,s9,0x20
     0x81d20 srli s6,s9,0x20          the return value: (uint32) incl
   so the phase reads the low 32 bits of s10 (sec), s7 (usec) and s9 (the record's length), and s5. *)
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
(* PSN (Pau's model, lib/Prog/pcap_source_struct_next.v) is PcapSourceNextDefs.PSN. *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The two halves of the record's timestamp, as the record header holds them (bytes 0..3 and
   4..7 of the header at the record's position, byte-swapped when the file is). *)
Definition nx_tsec (sw : bool) (C : list Z) (cap p : Z) : Z := PSN.hw sw (nxF C) (nx_q sw C cap p) 0.
Definition nx_tusec (sw : bool) (C : list Z) (cap p : Z) : Z := PSN.hw sw (nxF C) (nx_q sw C cap p) 4.

(* The timestamp the call stores, for a record that fits: sec * 10^6 + usec (PSN.rec_ts). *)
Lemma nx_tsv_fit : forall sw C cap p tsv, nx_fit sw C cap p = true ->
  nx_tsv sw C cap p tsv = nx_tsec sw C cap p * 1000000 + nx_tusec sw C cap p.
Proof. intros sw C cap p tsv H. unfold nx_tsv. rewrite H. reflexivity. Qed.

(* The word the call returns for a record that fits: the record's length in the buffer. *)
Lemma nx_res_fit : forall sw C cap p, nx_fit sw C cap p = true ->
  nx_res sw C cap p = nx_reclen sw C cap p.
Proof.
  intros sw C cap p H. unfold nx_fit, nx_kind in H. unfold nx_res, nx_reclen, PSN.res_of.
  destruct (PSN.kind sw (nxF C) cap (nx_q sw C cap p)); first [discriminate | reflexivity].
Qed.

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

(* THE ENTRY PREDICATE AT NP_ts (0x81ce4). The shared middle state nx_mid at NP_ts with `ph` in
   scope, every caller byte of the post's set allowed (nx_E), the stream after the record (the
   model's nx_pos), the struct's orig / vtag / vid as the model leaves them and the timestamp cell
   still the caller's (n_tsv); the record at the model's final position fits (KFit) and the head of
   the buffer holds its bytes; s5 holds &ts (reloaded at 0x81c08), and the low words of s9, s10
   and s7 hold the record's length in the buffer, the timestamp's seconds and its microseconds. *)
Definition nx_ts_inv (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  let sw := (n_sw cx =? 1) in
  nx_mid B MT KS cx fp NP_ts NSH_ph (nx_E cx) (nx_pos sw (n_C cx) (n_cap cx) (n_p cx))
    (nx_orig sw (n_C cx) (n_cap cx) (n_p cx) (n_lol cx))
    (nx_vtag sw (n_C cx) (n_cap cx) (n_p cx) (n_lvt cx))
    (nx_vid sw (n_C cx) (n_cap cx) (n_p cx) (n_lvid cx)) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
  nx_fit sw (n_C cx) (n_cap cx) (n_p cx) = true /\
  (exists bj', garr8 SEGS (rdW W3 (ms_mem ms3)) (n_buf cx) bj' /\ length bj' = length (n_bj cx) /\
     firstn (length (nx_rec sw (n_C cx) (n_cap cx) (n_p cx))) bj' = nx_rec sw (n_C cx) (n_cap cx) (n_p cx)) /\
  getr (ms_regs ms3) 21 = w64 (n_ts cx) /\                                                      (* s5 *)
  bv_unsigned (getr (ms_regs ms3) 25) mod 2 ^ 32 = nx_reclen sw (n_C cx) (n_cap cx) (n_p cx) /\ (* s9 *)
  bv_unsigned (getr (ms_regs ms3) 26) mod 2 ^ 32 = nx_tsec sw (n_C cx) (n_cap cx) (n_p cx) /\   (* s10 *)
  bv_unsigned (getr (ms_regs ms3) 23) mod 2 ^ 32 = nx_tusec sw (n_C cx) (n_cap cx) (n_p cx).    (* s7 *)

End c.
End b.
End a.

(* nx_ts_inv names no sink head (asource_at takes none), so SK is not among its binders: its
   arguments are {fx} {rc} {PI} B MT KS (nx_body states the floating-point state) and the eight of
   a phase predicate, as nx_exit_inv's. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (PI : PAImg pcap_listing) (B : asyms) (MT : ameter_ops)
  (KS : asource_syms) => @nx_ts_inv fx rc PI B MT KS : ncx -> Z -> Z -> alayout -> astate -> world pa_segs ->
  machine_state -> Model -> Prop).
