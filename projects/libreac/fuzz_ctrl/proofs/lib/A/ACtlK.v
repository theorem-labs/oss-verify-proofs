(* lib/A/ACtlK.v -- the WALK-INTERNAL constants of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput, in the
   released cgif_file_fuzzer form.  Written by a Theorem Labs lane; single writer.

   ONE CONSTANT, ONE SOURCE (porter a Theorem Labs lane, 21:36Z and 21:37Z).  The program constants of the lib contract
   are NOT defined here.  The relocated core carries the donor's A/ACfn.v (its AD1q / AD2o Require it) with
   ctrl's values, filled from this unit's measurement through port_core's --override table, and the LIBX
   statement (ACfn.v:59-72, tfib_lib_contract_x) stays the donor's text over those names; this walk PROVES it.
   The values a Theorem Labs lane measured on the pinned v1.9.0 image and handed to the porter
   (constants-A.md (a working note, not in this delivery), both image sha256s and the
   25-byte PT_LOAD difference re-checked):
     A_LLVMF   0x80edc      (donor 0x80490)
     RA_LLVMF  0x80dd8      (donor 0x8038c)
     A_EMPTY   0x5daee0     oft_aligned_copy.empty (donor 0x5d8660)
     LLVMF_STK 32768        the donor's value, TRUE for ctrl: the measured deepest static path needs 9311
     LIVE_LIB  2^33         the donor's value, TRUE for ctrl: the measured need is 65535 (one block at a time)
     EV_LIB    2000         the CORE's bound, used in its composition (AD1r.v:582); ctrl's need is EV_LLVMF below
     RLO / RHI 0x9e380 / 0xa07c8   the values of record.  0x9e348 is PT_GNU_RELRO's p_vaddr; RLO = 0x9e380 because the
                                   first 56 bytes are the init / fini / preinit arrays.  Never the page-rounded
                                   0x9e000 / 0xa1000
     gp 0x10800, errno 0x5db76c    fields of the CtrlB bundle (the donor's TfibLib, ACeh.v:25-36)
   Object numbering is a Theorem Labs lane's (lib/A/Prog/CtrlAddr.v:68-103, `ctrl_obj`): the cells are 30 = CELL_K and
   31 = UAR, not grant's 32 / 33; cite that file, never a second table.

   CLOSURE (porter rulings 21:29Z-21:33Z).  Requires, never Imports: lib/A/AsanRT.v (ctrl's v1.9 runtime-cell
   file, auditor blob b67d26f8ec7; closure Stdlib, LPS BvBase / RiscvSemantics / MemImageType / State / Run,
   lib/Lib/Mem, lib/A/Img0), lib/Lib/Mem.v, lib/A/Img0.v.  Not required, by rule: lib/A/AsanRTInv.v (the
   frame-route invariant), lib/A/MemNorm.v (it pulls the ASan-side lib/A/Reusable).  No statement about the ASan
   run uses ctrl's plain Exec / PropExec / Step.  SHADOWED NAMES (a Theorem Labs lane via the porter, 21:37Z): getr, mkst and
   seg_rom exist in BOTH lib/Lib and the core's YK11 and DIFFER (lib/Lib's mkst empties the FP registers), so
   every use of cfg_at / mkst / getr / seg_rom in a walk file is YK11-qualified and lib/Lib is never Imported
   after YK11.  ONE SOURCE PER BYTE: where the core's AR / AF0m rows state a runtime cell, the walk uses the
   core's fact; AsanRT.v serves only what the core does not mention (the split is fixed when the core lands). *)

From Coq Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AsanRT Img0.
(* Absolute form: lib/A/Bz/Lib, lib/B/Bz/Lib and lib/AZ/Lib hold twins of Mem and PropExec (batch 3, item 8). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Local Open Scope Z_scope.

(* The allocator events one call of THIS function needs.  MEASURED: 526 = the 7-pass round trip
   (0x81954 li a1,7) x 2 events + the 256-pass frame loop (0x82940 li a0,254 and its bound) x 2 events.  (at most 2128
   is the per-RUN total: up to 4 calls x 526 + 3 to 24 driver events in main / target_run, outside this function.)  The walk states its
   cut bounds with this name and meets the core's EV_LIB through the fact EV_LLVMF <= EV_LIB, proved where the
   core's name is in scope. *)
Definition EV_LLVMF : Z := 526.

(* The three runtime facts the cut layer carries (ACtlCut.ctl_rt), carried because ctrl's inline shadow checks read
   those cells at nearly every cut.  Sources: AsanRT.v for the cells and the shadow; ro_agree is RESTATED (one
   line, ctrl's lib/A/MemNorm.v:41-42) because MemNorm.v is outside the allowed closure, over lib/Lib/Mem.v's
   ro_addr / mrd.  word / byte are LPS's (AsanRT.v does not define them), and lib/Lib/Mem.v's predicates take
   the segment list first (ProgWorld's scratch typecheck on the planning core, 23:00Z).
   mem_inv is NOT carried (a Theorem Labs lane 00:34Z, accepted by a Theorem Labs lane): it has no source in the core's world at the
   entry or after a world step (a Theorem Labs lane, progworld-stmts.md section 0 (a working note, not in this delivery)), so no lemma could produce it. *)
Definition asan_cells_at (m : word -> option byte) : Prop := AsanRT.asan_cells m.
Definition shadow_rw_at (m : word -> option byte) : Prop := AsanRT.shadow_rw m.
Definition ro_agree_at (m : word -> option byte) : Prop :=
  forall a, Mem.ro_addr Img0.rsegs a = true -> Mem.mrd Img0.rsegs m a = PropExec.seg_rom Img0.rsegs a.

(* Names ctrl's transcribed cut bodies (lib/A/ACtlCutP.v) read, restated or re-exported because their home
   modules are outside the port closure.  One line each, with its source; none is a program constant of the
   lib contract (those are A.ACfn's). *)
(* the ASan shadow offset, from the allowed AsanRT.v (one source) *)
Definition ASAN_K : Z := AsanRT.ASAN_K.
(* ctrl's bound on its own input length, restated from lib/A/Contract.v:50 (the frame route, outside the
   closure).  It is not the core's MALLOC_MAX. *)
Definition ANMAX : Z := 2 ^ 30.
(* ctrl's served size of a request (n = 0 is served as 1 byte), restated from lib/A/Contract.v:129.  Used ONLY in
   body conjuncts about addressable bytes (ctrl's HB); the live-block LIST is the core's, whose entries carry the
   REQUEST size (amalloc04_rule's post appends (res, n), donor YC5d.v:67-74), never a_size n. *)
Definition a_size (n : Z) : Z := Z.max n 1.
