(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: the entry
   predicate of the phase at NP_ts (listing offset 0x1394, address 0x81b1c), where a record that fits has been
   read into the caller's buffer and its VLAN tag (if any) stripped. The phase itself (0x81b1c .. 0x81b60, then
   `j` NP_exit 0x818b4) is walked in lib/B/Prog/PcapSourceNextFitB.v. This is the lib/B twin of
   lib/A/Prog/PcapSourceNextFitBDefs.v (a Theorem Labs lane), over lib/B's phase layer (lib/B/Prog/PcapSourceNextDefs.v).

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; symbols from its unstripped twin fuzz_pcap.asan-ubsan (sha256 c969d83cdd59),
   capstone 5 disassembly).

   THE CODE OF THE PHASE (0x81b1c .. 0x81b60):
     0x81b1c beqz a7,0x81b58          the caller asked for no timestamp (a7 = &ts, reloaded from NS_TS)
     0x81b20 andi a0,a7,7
     0x81b24 bnez a0,0x81b64          the UBSan alignment guard: `unimp` (NP_trap) when ts is misaligned
     0x81b28 srli a0,a7,3
     0x81b2c add  a0,a0,t0            t0 = the shadow base, reloaded from NS_SB on every path into NP_ts
     0x81b30 lbu  a0,0(a0)            the shadow byte of ts
     0x81b34 bnez a0,0x81c30          the error path (__asan_report_store8 0x81c34), not taken
     0x81b38 lui  a0,0x3d09
     0x81b3c slli a1,s2,0x20          the seconds (s2, reloaded from NS_SEC at 0x819e8), in the high word
     0x81b40 slli s8,s8,0x20          the microseconds (s8, rd_u32 (ph + 4) 0x817ac), in the high word
     0x81b44 slli a0,a0,0x1a          a0 = 0x3d09 << 38 = 10^6 * 2^32
     0x81b48 mulhu a0,a1,a0           a0 = sec * 10^6
     0x81b4c srli a1,s8,0x20          a1 = usec
     0x81b50 add  a0,a0,a1
     0x81b54 sd   a0,0(a7)            ts := sec * 10^6 + usec
     0x81b58 slli s6,s6,0x20
     0x81b5c srli a1,s6,0x20          the result: (uint32) the record's length in the buffer (s6)
     0x81b60 j    0x818b4             NP_exit
   so the phase reads a7, t0 and the low 32 bits of s2 (sec), s8 (usec) and s6 (the record's length); a6 = F
   (from NS_FK) and s3 = F (from NS_F0) are reloaded before NP_ts on every path (0x819a8 / 0x8198c, 0x81a50 /
   0x81a54, 0x81afc / 0x81b00, 0x81b10 / 0x81b14) and pass through to NP_exit, whose invariant names them. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadISpec.
(* lib/B's phase layer, after every lib/A import (it shadows lib/A's phase names). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The two halves of the record's timestamp, as the record header holds them (bytes 0..3 and 4..7 of the
   header at the record's position, byte-swapped when the file is): the words rd_u32 (ph + 0) and
   rd_u32 (ph + 4) return. The same text as lib/A's PcapSourceNextFitBDefs (image-free). *)
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
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* THE ENTRY PREDICATE AT NP_ts (0x81b1c). lib/B's shared middle state nx_mid at NP_ts with `ph` in scope
   (NSH_ph), every caller byte of the post's set allowed (nx_E), the stream after the record (the model's
   nx_pos), the struct's orig / vtag / vid as the model leaves them and the timestamp cell still the
   caller's (n_tsv); the record at the model's final position fits (KFit) and the head of the buffer holds
   its bytes. The phase's own registers: a6 = F and s3 = F (the reloads NP_exit needs), a7 = &ts (from
   NS_TS), t0 = the shadow base (from NS_SB), and the low words of s6, s2 and s8 hold the record's length
   in the buffer, the timestamp's seconds and its microseconds. *)
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
  getr (ms_regs ms3) 16 = w64 (nF cx fp) /\                                                     (* a6 *)
  getr (ms_regs ms3) 19 = w64 (nF cx fp) /\                                                     (* s3 *)
  getr (ms_regs ms3) 17 = w64 (n_ts cx) /\                                                      (* a7 *)
  getr (ms_regs ms3) 5 = w64 SHADOW_OFF /\                                                      (* t0 *)
  bv_unsigned (getr (ms_regs ms3) 22) mod 2 ^ 32 = nx_reclen sw (n_C cx) (n_cap cx) (n_p cx) /\ (* s6 *)
  bv_unsigned (getr (ms_regs ms3) 18) mod 2 ^ 32 = nx_tsec sw (n_C cx) (n_cap cx) (n_p cx) /\   (* s2 *)
  bv_unsigned (getr (ms_regs ms3) 24) mod 2 ^ 32 = nx_tusec sw (n_C cx) (n_cap cx) (n_p cx).    (* s8 *)

End c.
End b.
End a.

(* nx_ts_inv names no sink head (asource_at takes none), so SK is not among its binders: its arguments are
   {fx} {rc} {PI} B MT KS and the eight of a phase predicate, as lib/B's nx_exit_inv. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (PI : PAImg pcap_listing) (B : asyms) (MT : ameter_ops)
  (KS : asource_syms) => @nx_ts_inv fx rc PI B MT KS : ncx -> Z -> Z -> alayout -> astate -> world pa_segs ->
  machine_state -> Model -> Prop).
