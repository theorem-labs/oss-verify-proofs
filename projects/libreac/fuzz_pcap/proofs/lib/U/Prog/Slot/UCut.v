From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel libreac_fuzz_fopen_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Require OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.
Import ListNotations.
Open Scope Z_scope.

(* The cuts of the fuzz_pcap ubsan slot (entry_fn 0x12c4c). Each cut
   is a return address of a call or a loop head; its predicate is CUTST with the slot's heap blocks hb and the
   registers and memory the next segment reads. File and record names are those of the plain chain model. *)
Module PS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Module PN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Module PW := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.

(* The input model INP(pl) of the slot contract. *)
Definition uF (g : ghost) : list byte := tl (g_in g).
Definition un (g : ghost) : Z := zlen (uF g).
Definition ud (g : ghost) : Z := match g_in g with [] => 0 | d :: _ => bv_unsigned d end.
Definition ucap (g : ghost) : Z := 8 * ud g.
Definition ubn (g : ghost) : Z := Z.max (ucap g) 1.
Definition uswz (g : ghost) : Z := PS.pcap_sw (uF g).
Definition usw (g : ghost) : bool := uswz g =? 1.
Definition ugood (g : ghost) : bool := PS.pcap_good (uF g).
Definition usrc (g : ghost) : Z := if g_n g =? 0 then g_p g else g_p g + 1.

(* The reader's walk over uF. *)
Definition uQ (g : ghost) (p : Z) : Z := PN.psn_q (usw g) (uF g) (ucap g) p.
Definition ukind (g : ghost) (q : Z) : PN.pkind := PN.kind (usw g) (uF g) (ucap g) q.
Definition ures (g : ghost) (q : Z) : Z := PN.res_of (usw g) (uF g) (ucap g) q.
Definition upos (g : ghost) (q : Z) : Z := PN.pos_of (usw g) (uF g) (ucap g) q.
Definition ufirst (g : ghost) : Z := ures g (uQ g 24).
Definition uout1 (g : ghost) (p : Z) : list byte := snd (fst (PN.psn_chain (usw g) (uF g) (ucap g) p)).
Definition uwalk (g : ghost) (p : Z) : list byte := PW.walk_out (S (length (uF g))) (usw g) (uF g) (ucap g) p.
(* The output after the walk: the call after the reopen (from 24). *)
Definition uC0 (g : ghost) : list byte := uout1 g 24.
(* The output of the rest of the walk after the call from p answered with the record Q = uQ g p. *)
Definition uafter (g : ghost) (p : Z) : list byte :=
  (if PN.is_fit (ukind g (uQ g p)) then uwalk g (upos g (uQ g p)) else []) ++ uC0 g.

Definition A5 : word := Z_to_bv 64 0xa5a5a5a5a5a5a5a5.
Definition TSK : Z := 1000000 * 2 ^ 32.

Section Cuts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Let CUT := CUTST B APIf ra empty.

(* The stdio and frame-cell facts every cut after E carries. *)
Definition ENV (g : ghost) (m : word -> option byte) : Prop :=
  stdio_ok m /\ guard_ok m /\ (exists fl md, errf m fl md) /\
  q64 m (spk g 0) (ud g) /\ q64 m G_FILE_LEN (un g).

Definition PSC (g : ghost) (m : word -> option byte) (h : Z) (lol lvt lvid : word) : Prop :=
  exists pad, rw_cells rsegs m (spk g 48) (PS.ps_cells (wz h) (wz (uswz g)) lol lvt lvid pad).

Definition BUFC (m : word -> option byte) (buf n : Z) : Prop :=
  exists bj, Arr.u8arr rsegs m buf bj /\ Z.of_nat (length bj) = n.

(* 0x12cf0: malloc returned b, the block for the file copy. *)
Definition Inv_K12d28 (g : ghost) (c : config) : Prop :=
  exists b, CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z) 1 [(b, un g)] (fun regs m =>
    getr regs 10 = wz b /\ getr regs 9 = wz (usrc g) /\ getr regs 18 = wz (un g) /\ getr regs 26 = wz G_FILE_LEN /\
    stdio_ok m /\ guard_ok m /\ (exists fl md, errf m fl md) /\ ofl_empty m /\
    q64 m (spk g 0) (ud g) /\ q64 m G_FILE_LEN (un g) /\ q64 m (G_FILE_LEN + 8) (usrc g)) c.

(* 0x12d38: pcap_source_open answered (0: the stream h is open at 24; -1: refused, h freed or never made). *)
Definition Inv_K12d70 (g : ghost) (c : config) : Prop :=
  exists b, (ugood g = true /\ exists h, CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 2 [(b, un g); (h, 1304)] (fun regs m =>
      getr regs 10 = wz 0 /\ getr regs 8 = wz b /\ getr regs 26 = wz G_FILE_LEN /\ ENV g m /\
      q64 m (G_FILE_LEN + 8) b /\ bytes_at rsegs m b (uF g) /\
      PSC g m h (wz 0) (wz 0) (wz 0) /\ mstl m h b (uF g) 24 (wz 0) (wz 0) /\ ofl_one m h) c) \/
    (ugood g = false /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 1 [(b, un g)] (fun regs m =>
      getr regs 10 = wz (-1) /\ getr regs 8 = wz b /\ getr regs 26 = wz G_FILE_LEN /\ ENV g m /\
      q64 m (G_FILE_LEN + 8) b /\ bytes_at rsegs m b (uF g) /\ q64 m (spk g 48) 0 /\ ofl_empty m) c).

(* 0x12ddc: malloc returned buf, the record buffer of max(cap, 1) bytes. *)
Definition Inv_K12e14 (g : ghost) (c : config) : Prop :=
  exists b h buf, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z) 3 [(b, un g); (h, 1304); (buf, ubn g)] (fun regs m =>
    getr regs 10 = wz buf /\ getr regs 8 = wz b /\ getr regs 9 = wz (ucap g) /\ getr regs 26 = wz G_FILE_LEN /\
    ENV g m /\ q64 m (G_FILE_LEN + 8) b /\ bytes_at rsegs m b (uF g) /\
    PSC g m h (wz 0) (wz 0) (wz 0) /\ mstl m h b (uF g) 24 (wz 0) (wz 0) /\ ofl_one m h /\ BUFC m buf (ubn g)) c.

(* The reader's state right after its call from file position p (record Q = uQ g p): the stream at upos Q, the
   source fields of the chain, the timestamp cell (ts = spk g 40) and the buffer (it starts with the record when Q
   is fit). *)
Definition RECST (g : ghost) (b h buf p : Z) (m : word -> option byte) : Prop :=
  mstl m h b (uF g) (upos g (uQ g p)) (wz 0) (wz 0) /\ ofl_one m h /\
  (exists lol lvt lvid, PSC g m h (PN.lol_of (usw g) (uF g) (PN.psn_lh (usw g) (uF g) (ucap g) p) lol)
     (PN.vt_of (usw g) (uF g) (ucap g) (uQ g p) lvt) (PN.vid_of (usw g) (uF g) (ucap g) (uQ g p) lvid)) /\
  rw_cells rsegs m (spk g 40) [C8 (PN.ts_of (usw g) (uF g) (ucap g) (uQ g p) (wz (-1)))] /\
  (exists bj, Arr.u8arr rsegs m buf bj /\ Z.of_nat (length bj) = ubn g /\
     (PN.is_fit (ukind g (uQ g p)) = true ->
        firstn (Z.to_nat (PN.incl (usw g) (uF g) (uQ g p))) bj = PN.rec_bytes (usw g) (uF g) (uQ g p))).

(* The registers and memory the slot keeps from the record buffer's malloc to the end of the walk. *)
Definition WKEEP (g : ghost) (b buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 8 = wz b /\ getr regs 9 = wz (ucap g) /\ getr regs 26 = wz G_FILE_LEN /\
  ENV g m /\ q64 m (G_FILE_LEN + 8) b /\ bytes_at rsegs m b (uF g) /\ q64 m (spk g 24) buf.

Definition HB3 (g : ghost) (b h buf : Z) : list (Z * Z) := [(b, un g); (h, 1304); (buf, ubn g)].

(* 0x12e04: the first call of the walk (from 24, with ts) answered. *)
Definition Inv_K12e3c (g : ghost) (c : config) : Prop :=
  exists b h buf, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z) 3 (HB3 g b h buf) (fun regs m =>
    getr regs 10 = wz (ufirst g) /\ getr regs 18 = wz buf /\ WKEEP g b buf regs m /\ RECST g b h buf 24 m) c.

(* K4, 0x12e38, the head of the walk's loop, index i: the call from p answered with the fit record uQ g p,
   whose length is in s5; the harness position s9 = p; s11 = the first answer. *)
Definition Inv_K4 (g : ghost) (i p : Z) (c : config) : Prop :=
  exists b h buf a3, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z) 3 (HB3 g b h buf) (fun regs m =>
    WKEEP g b buf regs m /\ RECST g b h buf p m /\
    0 <= i /\ 24 + 17 * i <= p /\ ukind g (uQ g p) = PN.KFit /\
    getr regs 18 = wz (-8) /\ getr regs 20 = bv_not (wz b) /\ getr regs 21 = wz (ures g (uQ g p)) /\
    getr regs 25 = wz p /\ getr regs 27 = wz (ufirst g) /\ getr regs 13 = a3 /\
    ((i = 0 /\ p = 24) \/ (0 < i /\ a3 = wz (ufirst g))) /\
    q64 m (spk g 8) (buf + 12) /\ q64 m (spk g 16) TSK /\ rw_cells rsegs m (spk g 32) [C8 (wz i)]) c.

(* 0x13034: the walk's call from p (the position after the record of K4 at index i - 1) answered. *)
Definition Inv_K1306c (g : ghost) (i p : Z) (c : config) : Prop :=
  exists b h buf, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z) 3 (HB3 g b h buf) (fun regs m =>
    WKEEP g b buf regs m /\ RECST g b h buf p m /\
    1 <= i /\ 24 + 17 * i <= p /\ p <= un g /\
    getr regs 10 = wz (ures g (uQ g p)) /\ getr regs 18 = wz (-8) /\ getr regs 20 = bv_not (wz b) /\
    getr regs 25 = wz p /\ getr regs 27 = wz (ufirst g) /\
    q64 m (spk g 8) (buf + 12) /\ q64 m (spk g 16) TSK /\ rw_cells rsegs m (spk g 32) [C8 (wz i)]) c.

(* K5, 0x1304c, the end of the walk: the call from p answered with the record uQ g p, which is not fit. *)
Definition Inv_K5 (g : ghost) (p : Z) (c : config) : Prop :=
  exists b h buf, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z) 3 (HB3 g b h buf) (fun regs m =>
    WKEEP g b buf regs m /\ RECST g b h buf p m /\
    24 <= p /\ p <= un g /\ ukind g (uQ g p) <> PN.KFit /\
    getr regs 21 = wz (ures g (uQ g p)) /\ getr regs 25 = wz p /\ getr regs 27 = wz (ufirst g)) c.

(* The tail: close, reopen, the call from 24 without ts, close, the call on the closed reader, two frees. *)
Definition TKEEP (g : ghost) (b buf : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  WKEEP g b buf regs m /\ getr regs 27 = wz (ufirst g) /\ BUFC m buf (ubn g).

Definition Inv_K130a4 (g : ghost) (c : config) : Prop :=
  exists b buf, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z) 3 [(b, un g); (buf, ubn g)] (fun regs m =>
    TKEEP g b buf regs m /\ ofl_empty m /\ (exists lol lvt lvid, PSC g m 0 lol lvt lvid)) c.

Definition Inv_K130bc (g : ghost) (c : config) : Prop :=
  exists b buf h, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z) 4 [(b, un g); (buf, ubn g); (h, 1304)] (fun regs m =>
    getr regs 10 = wz 0 /\ TKEEP g b buf regs m /\ PSC g m h (wz 0) (wz 0) (wz 0) /\
    mstl m h b (uF g) 24 (wz 0) (wz 0) /\ ofl_one m h) c.

Definition Inv_K130d4 (g : ghost) (c : config) : Prop :=
  exists b buf h, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z) 4 [(b, un g); (buf, ubn g); (h, 1304)] (fun regs m =>
    getr regs 10 = wz (ufirst g) /\ TKEEP g b buf regs m /\
    mstl m h b (uF g) (upos g (uQ g 24)) (wz 0) (wz 0) /\ ofl_one m h /\
    (exists lol lvt lvid, PSC g m h lol lvt lvid)) c.

Definition Inv_K130e0 (g : ghost) (c : config) : Prop :=
  exists b buf, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z) 4 [(b, un g); (buf, ubn g)] (fun regs m =>
    TKEEP g b buf regs m /\ ofl_empty m /\ (exists lol lvt lvid, PSC g m 0 lol lvt lvid)) c.

Definition Inv_K130f4 (g : ghost) (c : config) : Prop :=
  exists b buf, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z) 4 [(b, un g); (buf, ubn g)] (fun regs m =>
    getr regs 10 = wz (-1) /\ TKEEP g b buf regs m /\ ofl_empty m) c.

Definition Inv_K13104 (g : ghost) (c : config) : Prop :=
  exists b, ugood g = true /\ CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z) 4 [(b, un g)] (fun regs m =>
    getr regs 8 = wz b /\ stdio_ok m /\ guard_ok m /\ (exists fl md, errf m fl md) /\ ofl_empty m) c.

(* 0x130d4: both paths (the refused open and the end) after free(b). *)
Definition Inv_K1310c (g : ghost) (c : config) : Prop :=
  exists km, CUT g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) km [] (fun _ m => stdio_ok m /\ guard_ok m /\ (exists fl md, errf m fl md) /\
    ofl_empty m) c.

End Cuts.
