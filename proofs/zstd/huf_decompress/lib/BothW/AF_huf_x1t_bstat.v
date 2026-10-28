From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma x1_statB : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (RNG : footprint) (SPA r : Z) (Q : machine_state -> Prop),
  16 <= SPA < 2^63 -> 0 <= r < 2^64 ->
  (2^64 - 120 < r ->
     evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 (2^64 - 120)) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 (Z_to_bv 64 r) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x80618) fc None m (seg_rom bsegs))) ->
  (r <= 2^64 - 120 ->
     evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 (2^64 - 120)) a2 a3 a4 a5 a6 a7
                             s2 s3 (Z_to_bv 64 r) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x80464) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR ra (Z_to_bv 64 (SPA - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x80454) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros SPR RR KERR KOK.
  zstep. zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 (2^64 - 120)) by (apply Z_to_bv_eqm; reflexivity).
  zstep. bcase KI.
  - zstep. zstep.
    replace (SPA - 16 + 16) with SPA by lia.
    apply KERR. rewrite ?unsigned_lit in KI by lia. lia.
  - zstep.
    replace (SPA - 16 + 16) with SPA by lia.
    apply KOK. rewrite ?unsigned_lit in KI by lia. lia.
Qed.

End CANSEC1.
