(* crtA_iface: the addresses and the frame shape of check_round_trip in image A (fuzz_decode.asan), for the
   cgif-form walk of lib/A/Prog/check_round_trip_cg.v.

   FORM (decision of the porter, a Theorem Labs lane, 2026-10-29 01:54Z): check_round_trip's own body is walked as decode's
   footprint runs (lib/Lib/ExecF.v evtF), bridged into cgif's SRr by LeafCgKit.v:101 bridge_evtF_stmt, with the
   journal re-established across each run by lib/Reusable/YCbq.v:636 ajournal_exec.  The Pa engine of
   lib/Reusable/YP0l.v cannot walk this function: its convert loop is float code (fmv.w.x at +0xc4 and
   fcvt.s.w / fmul.s / fsw at +0x18c .. +0x194 of the entry), and YP0l.v:265 answers SR_unsupported on every float
   instruction; the malloc'd float buffers the loop writes are not modelled by the symbolic memory either.

   Control flow (offsets from the entry; the listing lib/A/Prog/DecodeList.v, slots AF_check_round_trip ..
   AF_check_braid), from the record of the same function on a working branch at dc455613c81
   (lib/A/Prog/crt_iface.v, crt_segs_F.v, crt_loopF.v), re-based here on the listing's own names:
     +0x000 entry, frame 96 bytes            +0x060 call malloc(4 nch ns), returns +0x064
     +0x06c call malloc(8 nch), ret +0x070   +0x084 call calloc(3 nch ns, 1), ret +0x088
     +0x088 .. +0x098 the three NULL checks and `nch <= 0`, then the convert loop +0x0d4 .. +0x1ec
     +0x1f0 .. +0x204 call reac_braid_encode, ret +0x208
     +0x214 call bcmp, ret +0x218; +0x218 branch on the result
     +0x220 call free(again) ret +0x224, +0x228 call free(planar) ret +0x22c, +0x264 tail jump to free(planes).
   The blocks at +0x268 (__asan_handle_no_return, abort), +0x270 / +0x278 / +0x280 (__asan_report_load1),
   +0x288 (__asan_report_store4) and +0x28c (__asan_report_store8) are the unreachable exits. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr DecodeList.
Import ListNotations.
Open Scope Z_scope.

(* Every address below comes from the listing: the entry and the runtime entries are decode_sigma of the listing's
   names, and every interior point is an offset from the entry. *)
Definition CRT_ENTRY : Z := decode_sigma DS_check_round_trip.
Definition CRT_AT (off : Z) : Z := CRT_ENTRY + off.
Definition CRT_MALLOC : Z := decode_sigma DS___interceptor_trampoline_malloc.
Definition CRT_CALLOC : Z := decode_sigma DS___interceptor_trampoline_calloc.
Definition CRT_FREE : Z := decode_sigma DS___interceptor_trampoline_free.
Definition CRT_ENCODE : Z := decode_sigma DS_reac_braid_encode.
Definition CRT_BCMP : Z := decode_sigma DS___interceptor_trampoline_bcmp.

(* The entry the listing gives the function is the listing's own slot. *)
Lemma CRT_ENTRY_listing : CRT_ENTRY = decode_text + AF_check_round_trip.
Proof. reflexivity. Qed.

(* The cut points of the walk, as offsets from the entry. *)
Definition CRT_RET_MALLOC1 : Z := CRT_AT 0x64.
Definition CRT_RET_MALLOC2 : Z := CRT_AT 0x70.
Definition CRT_RET_CALLOC : Z := CRT_AT 0x88.
Definition CRT_LOOP_IN : Z := CRT_AT 0xd4.
(* The inner loop's head: the samples of one channel.  Its back edge is the `bne a7, t3` at +0x19c, its exit
   the `j` at +0x1a0 to the outer loop's tail.  Image B names the same point CRT_ILOOP (offset +0x168 there). *)
Definition CRT_ILOOP : Z := CRT_AT 0x10c.
(* The outer loop's tail: the channel pointers are bumped here and the back edge `bne a3, s3` at +0x1ec goes
   back to CRT_LOOP_IN. *)
Definition CRT_LOOP_TAIL : Z := CRT_AT 0x1d8.
Definition CRT_LOOP_OUT : Z := CRT_AT 0x1f0.
Definition CRT_RET_ENCODE : Z := CRT_AT 0x208.
Definition CRT_RET_BCMP : Z := CRT_AT 0x218.
Definition CRT_RET_FREE1 : Z := CRT_AT 0x224.
Definition CRT_RET_FREE2 : Z := CRT_AT 0x22c.
Definition CRT_EPILOGUE : Z := CRT_AT 0x22c.

(* check_round_trip's own frame: 96 bytes. *)
Definition CRT_FRAME : Z := 96.

(* lui a5, 0xff000 at +0xac writes the sign-extended value 2^64 - 2^24. *)
Definition CRT_A5 : Z := 2 ^ 64 - 2 ^ 24.

(* The 96-byte frame: the caller's s10, s9, ..., s1, s0, ra at 0(sp) .. 88(sp). *)
Definition crt_fr (c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
  [C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].
