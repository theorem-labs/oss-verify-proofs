(* lib/B/ACtlK.v -- the WALK-INTERNAL constants of fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput, in
   the released cgif_file_fuzzer form.  Written by a Theorem Labs lane as the image-B twin of a Theorem Labs lane's lib/A/ACtlK.v
   (b535733d786, the frame-law / typecheck fix of a working branch e76ced8e847); single writer.

   ONE CONSTANT, ONE SOURCE (porter a Theorem Labs lane, 21:36Z and 21:37Z).  The program constants of the lib contract
   are NOT defined here.  The relocated core carries the donor's root YCfn.v (the image-B twin of A/ACfn.v) with
   ctrl's values, filled from this unit's measurement through port_core's --override table, and the LIBX
   statement (YCfn.v:57-67, tfib_lib_contract_x) stays the donor's text over those names; this walk PROVES it.
   The values a Theorem Labs lane measured on the pinned v1.9.0 asan-ubsan image and handed to the porter
   (constants-B.md (a working note, not in this delivery); image A's are a Theorem Labs lane's constants-A.md (a working note, not in this delivery)):
     A_LLVMF   0x81018      (A 0x80edc)
     RA_LLVMF  0x80f14      (A 0x80dd8)
     A_EMPTY   0x5dbd20     oft_aligned_copy.empty (A 0x5daee0)
     LLVMF_STK 32768        the donor's value, TRUE for B: the measured need is 19999 (20464 by cut facts alone)
     LIVE_LIB  2^33         the donor's value (one block at a time, as in A)
     EV_LIB    2000         the CORE's bound; ctrl's need is EV_LLVMF below
     RLO / RHI 0x9f1a0 / 0xa15e8   .data.rel.ro's start to the GNU_RELRO filesz end (a Theorem Labs lane 00:35Z: the span's first
                                   0x38 bytes, .init_array / .fini_array / .preinit_array at 0x9f168, are not read-only
                                   data of record; image A's RLO is 0x9e380, the same + 0x38)
     gp 0x10800, errno 0x5dc5ac    fields of the CtrlB bundle (the donor's TfibLib, root YCeh.v:25-36; tp 0x5dc650 - 164)
   Object numbering is a Theorem Labs lane's (lib/A/Prog/CtrlAddr.v:68-103, `ctrl_obj`; image B uses the same object
   numbering in its twin lib/B/Prog/CtrlAddr.v:76-111 `ctrl_obj`): the cells are 30 = CELL_K and 31 = UAR, not grant's 32 / 33; cite the image's own file,
   never a second table.

   CLOSURE (porter rulings 21:29Z-21:33Z).  Requires, never Imports: lib/B/AsanRT.v (ctrl's v1.9 image-B runtime-cell
   file; closure Stdlib, LPS BvBase / RiscvSemantics / MemImageType / State / Run, lib/Lib/Mem, lib/B/Img0),
   lib/Lib/Mem.v, lib/B/Img0.v.  Not required, by rule: lib/B/AsanRTInv.v (the frame-route invariant),
   lib/B/MemNorm.v (it pulls the ASan-side lib/B/Reusable).  No statement about the ASan run uses ctrl's plain
   Exec / PropExec / Step.  SHADOWED NAMES (a Theorem Labs lane via the porter, 21:37Z): getr, mkst and seg_rom exist in BOTH
   lib/Lib and the core's YK11 and DIFFER (lib/Lib's mkst empties the FP registers), so every use of cfg_at / mkst /
   getr / seg_rom in a walk file is YK11-qualified and lib/Lib is never Imported after YK11.  ONE SOURCE PER BYTE:
   where the core's AR / YF0m rows state a runtime cell, the walk uses the core's fact; AsanRT.v serves only what
   the core does not mention (the split is fixed when the core lands).  The journal's sink head is the core's
   Reusable.YE2k.tfib_sink_head (ofl_head 0x5fcd48), named where the top instantiates it (lib/B/ACtl.v), not here. *)

From Coq Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require AsanRT Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem PropExec.
Local Open Scope Z_scope.

(* The allocator events one call of THIS function needs.  MEASURED on image B's code: 526 = the 7-pass round trip
   (bound `li a0,7` at 0x81ac4; malloc 0x81760, free 0x81a9c) x 2 events + the 256-pass frame loop (bound `li a0,256`
   at 0x82d20; malloc 0x81f4c, free 0x82d18) x 2 events - the same 526 as image A.  The walk states its cut bounds
   with this name and meets the core's EV_LIB through the fact EV_LLVMF <= EV_LIB, proved where the core's name is
   in scope. *)
Definition EV_LLVMF : Z := 526.

(* The three runtime facts the cut layer carries (ACtlCut.ctl_rt); ctrl's inline shadow checks read those cells at
   nearly every cut.  Sources: AsanRT.v for the cells and the shadow; ro_agree is RESTATED (one line, ctrl's
   lib/B/MemNorm.v:41-42) because MemNorm.v is outside the allowed closure.  word / byte are LPS's (AsanRT.v does
   not define them), and lib/Lib/Mem.v's predicates take the segment list first (ProgWorld's scratch typecheck on
   the planning core, 23:00Z).  mem_inv is NOT carried (a Theorem Labs lane 00:35Z, both images): a Theorem Labs lane measured that it has
   no source in the core's world at the entry or after a world step (progworld-stmts.md section 0 (a working note, not in this delivery)). *)
Definition asan_cells_at (m : word -> option byte) : Prop := AsanRT.asan_cells m.
Definition shadow_rw_at (m : word -> option byte) : Prop := AsanRT.shadow_rw m.
Definition ro_agree_at (m : word -> option byte) : Prop :=
  forall a, Mem.ro_addr Img0.rsegs a = true -> Mem.mrd Img0.rsegs m a = PropExec.seg_rom Img0.rsegs a.

(* Names ctrl's transcribed cut bodies (lib/B/ACtlCutP.v) read, restated or re-exported because their home
   modules are outside the port closure.  One line each, with its source; none is a program constant of the
   lib contract (those are Reusable.YCfn's). *)
(* the ASan shadow offset, from the allowed AsanRT.v (one source) *)
Definition ASAN_K : Z := AsanRT.ASAN_K.
(* ctrl's bound on its own input length, restated from lib/B/Contract.v:50 (the frame route, outside the
   closure).  It is not the core's MALLOC_MAX. *)
Definition ANMAX : Z := 2 ^ 30.
(* ctrl's served size of a request (n = 0 is served as 1 byte), restated from lib/B/Contract.v:129.  Used ONLY in
   body conjuncts about addressable bytes (ctrl's HB); the live-block LIST is the core's, whose entries carry the
   REQUEST size (amalloc04_rule's post appends (res, n), donor YC5d.v:67-74), never a_size n. *)
Definition a_size (n : Z) : Z := Z.max n 1.
