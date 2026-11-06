(* ctrl_lay_block (0x86104), fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the descriptor D4 of pb_ctrl_lay_block's
   glue, the boundary between region R23 (lay_R23, ctrl_lay_block_gR23.v) and region R4 (lay_R4, ctrl_lay_block_gR4.v).
   rule 24: no function proved.

   PLAN OF RECORD: ctrl_lay_block-B-glue-plan.md section 2 (a working note, not in this delivery) (D4).
   D4 holds at the class-1 flag store `sb zero,0(a0)` at pc 0x86440 = 549952, before the store, on the REAL memory
   mem3 (after R23's journal step): the journal with the class-1 frame (1, pos) still owned, the store state's
   registers, the premises of ctrl_lay_block_cutsF.ly_store_tail read at the real memory (R4 moves them to
   MemNorm.normalize rsegs mem3), the output block, and what the call kept so far (acall_kept from the entry memory).

   The store state (ctrl_lay_block_cutsF.ly_store_tail, cut file ad0627f1a39) is
     mkR xra spc gp tp x5 x6 x7 sp SP2 (fs_flag FS 1 j) x11 .. x17 sfr x19 .. x23 (shadow_addr frb) frb ASAN_K s11
         x28 .. x31
   with Section CUTS's ra sp gp tp s0 .. s11 := the entry registers of the call (regs 1, 2, 3, 4, 8, 9, 18 .. 27),
   FS := ly_F lyc, j := pos, frb := fs_frame FS 1 pos; xra, spc, sfr and the caller-saved registers are free.

   CLOSURE: the _F files are Required QUALIFIED; lib.Lib is named lib.Lib.X. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_ctrl_lay_block.
(* the _F closure and the bridges, QUALIFIED only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Img0 AsanRT MemNorm ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c ctrl_lay_blockF_on.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section D4.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
Variable B : asyms.

(* The arguments: the call's (tctrl_lay_block_spec's binders, minus f), then the class-1 position pos and the store
   point's journal state ly3 S3 W3 mem3 md3 with its register file regs3. *)
Definition lay_D4 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
  (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (p md g : Z) (fr tb mb nb gb : list byte)
  (pos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  (* the journal at the store: the class-1 frame (1, pos) still owned, nothing else changed in the frame list *)
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly3 S3 W3 mem3 md3 k /\
  frames S3 = (1, pos) :: frames Sc /\ ablocks B ly3 S3 = ablocks B lyc Sc /\ ly_F ly3 = ly_F lyc /\
  0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 /\
  (* the side stack above the image (fs_place of the cuts' FP0), the output block's home (tctrl_lay_block_spec);
     together they put the flag byte above the image and outside the output block *)
  B.Prog.asan_stack_malloc_c.ASAN_GT <= ly_F lyc /\ tctrl_lay_block_home B lyc Sc (p + 18) 32 /\
  (* the call's entry facts R4 reads (tctrl_lay_block_spec's premises) *)
  sp0 - STK <= spZ regs - CTRL_LAY_BLOCK_STK /\ spZ regs <= sp0 /\ lib.Reusable.YK0s.ret_ok (getr regs 1) /\
  (* the store state's fixed registers *)
  getr regs3 3 = getr regs 3 /\ getr regs3 4 = getr regs 4 /\ getr regs3 8 = getr regs 2 /\
  getr regs3 9 = w64 ((spZ regs - 128) / 32 * 32) /\
  getr regs3 10 = w64 (B.Prog.asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos) /\
  getr regs3 24 = w64 (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) /\
  getr regs3 25 = w64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) /\
  getr regs3 26 = w64 B.AsanRT.ASAN_K /\ getr regs3 27 = getr regs 27 /\
  (* ly_store_tail's memory premises at the real memory (R4: rw_cells_normalize, mem_inv_normalize, store_ok from
     the cell's writability) and the flag byte apart from the 12 saves *)
  B.MemNorm.ro_agree B.Img0.rsegs mem3 /\
  (exists fb : byte, lib.Lib.Step.rw_cells B.Img0.rsegs mem3
     (B.Prog.asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos) [lib.Lib.Cells.C1 fb]) /\
  lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (spZ regs - 96)
    (B.Prog.ctrl_lay_blockF_on.SAVES (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
       (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)) /\
  (B.Prog.asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos + 1 <= spZ regs - 96 \/
   spZ regs <= B.Prog.asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos) /\
  (* the output block as the run leaves it, visible in the store world *)
  lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (p + 18)
    [lib.Lib.Cells.CB 32 (B.Prog.ctrl_lay_blockF_on.LAY md g fr tb mb nb gb)] /\
  B.ProgBridge.range_visible (w_H W3) (p + 18) 32 /\
  (* the side stack visible in the store world (ly_store_tail's footprint premise RFS) *)
  B.ProgBridge.range_visible (w_H W3) (ly_F lyc) B.Prog.asan_stack_malloc_c.FS_SIZE /\
  (* what the call kept so far, from its entry memory *)
  acall_kept SEGS B lyc Sc W memc W3 mem3 (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) (tctrl_lay_block_out p).

End D4.
