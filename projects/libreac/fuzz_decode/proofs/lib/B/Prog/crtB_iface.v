(* crtB_iface: the addresses and the frame shape of check_round_trip in image B (fuzz_decode.asan-ubsan, original
   pin), for the cgif-form walk of lib/B/Prog/check_round_trip_cg.v.  Twin of lib/A/Prog/crtA_iface.v
   (a working branch ae1529ccb00): the same names, image B's offsets.

   FORM (decision of the porter, a Theorem Labs lane, 2026-10-29 01:54Z): check_round_trip's own body is walked as decode's
   footprint runs (lib/Lib/ExecF.v evtF), bridged into cgif's SRr, with the journal re-established across each run
   by lib/Reusable/YCbq.v:636 ajournal_exec.  The Pa engine of lib/Reusable/YP0l.v cannot walk this function: its
   convert loop is float code (fmv.w.x at +0x100, fcvt.s.w / fmul.s / fsw at +0x200 .. +0x208).

   Control flow (offsets from the entry; the listing lib/B/Prog/DecodeBList.v, slot AF_check_round_trip; neutral
   disassembly of the original image, CUTPOINTS.md), the same as the
   donor record lib/B/Prog/crt_segs.v / crt_iface.v on a working branch at dc455613c81 (entry 0x80d54,
   frame 160: the record's addresses are the original image's):
     +0x000 entry, frame 160 bytes              +0x064 call malloc(4 nch ns), returns +0x068
     +0x074 call malloc(8 nch), ret +0x078      +0x090 call calloc(3 nch ns, 1), ret +0x094
     +0x094 .. +0x0b0 the three NULL checks and `nch <= 0`, +0x0b4 .. +0x108 the loop constants,
     +0x10c outer loop head, +0x168 inner loop head, +0x24c outer tail, +0x26c loop exit
     +0x26c .. +0x284 call reac_braid_encode, ret +0x288
     +0x294 call bcmp, ret +0x298; +0x298 branch on the result
     +0x2a0 call free(again) ret +0x2a4, +0x2a8 call free(planar) ret +0x2ac, +0x2e8 tail jump to free(planes).
   The unreachable exits: +0x2ec / +0x2f8 (UBSan `unimp`), +0x2f0 (before_abort, abort), +0x2fc (store4 report),
   +0x300 / +0x308 / +0x310 (load1 reports), +0x318 (store8 report).  The four slow paths +0x218 / +0x224 / +0x230
   / +0x23c of the inner loop are reachable (partially poisoned granule) and return to the main path. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr DecodeBList.
Import ListNotations.
Open Scope Z_scope.

(* Every address below comes from the listing: the entry and the runtime entries are decodeb_sigma of the listing's
   names, and every interior point is an offset from the entry. *)
Definition CRT_ENTRY : Z := decodeb_sigma DB_check_round_trip.
Definition CRT_AT (off : Z) : Z := CRT_ENTRY + off.
Definition CRT_MALLOC : Z := decodeb_sigma DB___interceptor_trampoline_malloc.
Definition CRT_CALLOC : Z := decodeb_sigma DB___interceptor_trampoline_calloc.
Definition CRT_FREE : Z := decodeb_sigma DB___interceptor_trampoline_free.
Definition CRT_ENCODE : Z := decodeb_sigma DB_reac_braid_encode.
Definition CRT_BCMP : Z := decodeb_sigma DB___interceptor_trampoline_bcmp.

(* The entry the listing gives the function is the listing's own slot. *)
Lemma CRT_ENTRY_listing : CRT_ENTRY = decodeb_text + AF_check_round_trip.
Proof. reflexivity. Qed.

(* The cut points of the walk, as offsets from the entry (CUTPOINTS.md). *)
Definition CRT_RET_MALLOC1 : Z := CRT_AT 0x68.
Definition CRT_RET_MALLOC2 : Z := CRT_AT 0x78.
Definition CRT_RET_CALLOC : Z := CRT_AT 0x94.
(* The outer loop's head (`mul a0,a4,s2`), over the channels; back edge `bne a4,a0` at +0x268. *)
Definition CRT_LOOP_IN : Z := CRT_AT 0x10c.
(* The inner loop's head (`add a1,a3,s1`), over the samples of one channel; back edge `bne t6,s1` at +0x210, exit
   the `j` at +0x214 to the outer loop's tail.  Image A names the same point CRT_ILOOP (offset +0x10c there). *)
Definition CRT_ILOOP : Z := CRT_AT 0x168.
(* The outer loop's tail (`addi a4,a4,1`): the channel pointers are bumped here, the back edge goes to
   CRT_LOOP_IN. *)
Definition CRT_LOOP_TAIL : Z := CRT_AT 0x24c.
Definition CRT_LOOP_OUT : Z := CRT_AT 0x26c.
Definition CRT_RET_ENCODE : Z := CRT_AT 0x288.
Definition CRT_RET_BCMP : Z := CRT_AT 0x298.
Definition CRT_RET_FREE1 : Z := CRT_AT 0x2a4.
Definition CRT_RET_FREE2 : Z := CRT_AT 0x2ac.
Definition CRT_EPILOGUE : Z := CRT_AT 0x2ac.

(* check_round_trip's own frame: 160 bytes. *)
Definition CRT_FRAME : Z := 160.

(* lui t3, 0xff000 at +0xe4 writes the sign-extended value 2^64 - 2^24; slli t5, t2, 61 at +0xf8 writes 2^61. *)
Definition CRT_T3 : Z := 2 ^ 64 - 2 ^ 24.
Definition CRT_T5 : Z := 2 ^ 61.

(* The 160-byte frame as 20 8-byte slots (donor crt_segs.v:21-24): 0(sp) .. 48(sp) the function's own slots
   (8: again, 16: 3 nch ns, 24: audio, 32: ~planes, 40: nch, 48: planes), then the caller's s11, s10, ..., s1, s0,
   ra at 56(sp) .. 152(sp). *)
Definition crt_fr (v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
  [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5;
   C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].
