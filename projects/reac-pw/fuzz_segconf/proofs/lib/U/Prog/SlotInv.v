(* Cut invariants of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, [0x13888, 0x14268)): the live harness
   blocks of each cut and one Inv_<cut> per cut between ENTRY and RET, each a CUTST of Prog/SlotFR.v (FR over the
   live harness blocks hb, at some FP state with rounding mode 0), whose semantic part is a PARAMETER: the record
   cut_preds carries one predicate per cut, which the contracts state over the spine's models (their
   Prog/seg_cuts.v: P_K13984, P_K139e4, P_K13aac, P_K13c34, P_K13c3c, P_K13e90, P_K141ec). Statement text: no
   function is proved here.
   The form is reac-pw/fuzz_role's Prog/SlotInv.v (commit 52bb2f1ed35d; reac-pw/fuzz_pin's and
   libreac/fuzz_ctrl's released Prog/SlotInv.v, commit 25e3d17bdb50), with segconf's cuts and blocks
   (ELF afc060e3cc9c):
   - c = malloc(16616) (0x1396c, struct reac_segconf), m = calloc(1, 9236) (0x13980, struct mconf); per file turn
     f < nfiles <= 4: text = malloc(n + 1) (0x13aa8), free(text) (0x13c34); tab = calloc(cap + 1, 18) (0x13e7c),
     mt = calloc(cap + 1, 20) (0x13e8c); then free(mt), free(tab), free(m), free(c) (0x141f0 .. 0x14208). The new
     block is at the head of hb; every free is of the head block.
   - Cuts (pc, hb): K13984 after calloc(m) [m; c]; K139e4 the file-loop head of turn f [m; c] (with f < 4: the loop
     bound the slot's induction needs, libreac/fuzz_ctrl's Prog/Seg/Slot.v loop_frames); K13aac after malloc(text)
     [text; m; c]; K13c34 at `jal free` of text [text; m; c]; K13c3c after the loop [m; c]; K13e90 after calloc(mt)
     [mt; tab; m; c]; K141ec before the frees [mt; tab; m; c]. The size >= 2^26 return (0x138c4 `bnez a2` to
     0x1420c) passes no cut: the slot runs it from ENTRY as one evt (GV bounds g_n below 2^26 at the cuts).
   - The sizes of text, tab and mt are existential in the cut and the cut predicate states them
     (nt = seg_txt_n inp f + 1, ntab = 18 * (seg_cap inp + 1), nmt = 20 * (seg_cap inp + 1));
     the sizes of c and m are fixed here.
   - Each cut predicate takes the input bytes inp = g_in g, the input pointer p = g_p g and the entry sp S = g_S g
     (fsp g = S - 240), the turn f where there is one, the block addresses (and sizes), then the registers (read with
     Reusable.YK11.getr) and the memory. FR carries no byte of the hb blocks: each predicate holds c's and m's (and
     text's, tab's, mt's) contents as bytes_at. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR.
Import ListNotations.
Open Scope Z_scope.

(* struct reac_segconf (the reader's state, 0x40e8 = 16616 bytes: malloc's a0 at 0x13964) and struct mconf (the
   harness model, 0x2414 = 9236 bytes: calloc's a1 = s11 + 0x414 with s11 = 0x2000, 0x13978-0x1397c). *)
Definition C_SIZE : Z := 16616.
Definition M_SIZE : Z := 9236.

(* The live harness blocks (new block at the head). *)
Definition hb_c (bc : Z) : list (Z * Z) := [(bc, C_SIZE)].
Definition hb_cm (bc bm : Z) : list (Z * Z) := [(bm, M_SIZE); (bc, C_SIZE)].
Definition hb_tcm (bc bm t nt : Z) : list (Z * Z) := (t, nt) :: hb_cm bc bm.
Definition hb_tab (bc bm tab ntab : Z) : list (Z * Z) := (tab, ntab) :: hb_cm bc bm.
Definition hb_end (bc bm tab ntab mt nmt : Z) : list (Z * Z) := (mt, nmt) :: hb_tab bc bm tab ntab.

(* The semantic part of each cut: arguments inp p S, the turn f where there is one, the blocks, then regs and mem. *)
Record cut_preds := CutPreds {
  cp_K13984 : list byte -> Z -> Z -> Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop;
  cp_K139e4 : list byte -> Z -> Z -> nat -> Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop;
  cp_K13aac : list byte -> Z -> Z -> nat -> Z -> Z -> Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop;
  cp_K13c34 : list byte -> Z -> Z -> nat -> Z -> Z -> Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop;
  cp_K13c3c : list byte -> Z -> Z -> Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop;
  cp_K13e90 : list byte -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop;
  cp_K141ec : list byte -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> bvmap 5 word -> (word -> option byte) -> Prop
}.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.
Let segs := ms_segs B.

(* H(X) for a cut indexed by the turn (libreac/fuzz_ctrl's Prog/SlotInv.v Hat). *)
Definition Hat {I : Type} (X : ghost -> I -> config -> Prop) (i : I) : Prop :=
  forall g c, X g i c -> SR segs c (Post B APIf ra g).

(* K13984, calloc(m)'s return (0x13980 `jal calloc` with a0 = 1, a1 = 9236; malloc(c) at 0x1396c before it). *)
Definition Inv_K13984 (g : ghost) (c : config) : Prop :=
  exists bc bm, CUTST B APIf ra empty g 0x13984 (hb_cm bc bm) (cp_K13984 CP (g_in g) (g_p g) (g_S g) bc bm) c.

(* K139e4, the file-loop head of turn f (back edge 0x13c38 `bne` -> 0x139e4). *)
Definition Inv_K139e4 (g : ghost) (f : nat) (c : config) : Prop :=
  (f < 4)%nat /\
  exists bc bm, CUTST B APIf ra empty g 0x139e4 (hb_cm bc bm) (cp_K139e4 CP (g_in g) (g_p g) (g_S g) f bc bm) c.

(* K13aac, malloc(text)'s return in turn f (0x13aa8 `jal malloc`, a0 = n + 1). *)
Definition Inv_K13aac (g : ghost) (f : nat) (c : config) : Prop :=
  exists bc bm t nt,
    CUTST B APIf ra empty g 0x13aac (hb_tcm bc bm t nt) (cp_K13aac CP (g_in g) (g_p g) (g_S g) f bc bm t nt) c.

(* K13c34, free(text) in turn f (0x13c34 `jal free`, a0 = s7 = text). *)
Definition Inv_K13c34 (g : ghost) (f : nat) (c : config) : Prop :=
  exists bc bm t nt,
    CUTST B APIf ra empty g 0x13c34 (hb_tcm bc bm t nt) (cp_K13c34 CP (g_in g) (g_p g) (g_S g) f bc bm t nt) c.

(* K13c3c, after the loop (0x13c38 `bne` not taken). *)
Definition Inv_K13c3c (g : ghost) (c : config) : Prop :=
  exists bc bm, CUTST B APIf ra empty g 0x13c3c (hb_cm bc bm) (cp_K13c3c CP (g_in g) (g_p g) (g_S g) bc bm) c.

(* K13e90, calloc(mt)'s return (0x13e8c `jal calloc` with a0 = cap + 1, a1 = 20; calloc(tab) at 0x13e7c). *)
Definition Inv_K13e90 (g : ghost) (c : config) : Prop :=
  exists bc bm tab ntab mt nmt,
    CUTST B APIf ra empty g 0x13e90 (hb_end bc bm tab ntab mt nmt)
      (cp_K13e90 CP (g_in g) (g_p g) (g_S g) bc bm tab ntab mt nmt) c.

(* K141ec, after check_declared, before the frees (0x141ec `mv a0,s4`; 0x141f0 `jal free`). *)
Definition Inv_K141ec (g : ghost) (c : config) : Prop :=
  exists bc bm tab ntab mt nmt,
    CUTST B APIf ra empty g 0x141ec (hb_end bc bm tab ntab mt nmt)
      (cp_K141ec CP (g_in g) (g_p g) (g_S g) bc bm tab ntab mt nmt) c.

End Slot.
