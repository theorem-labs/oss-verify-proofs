(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env Gq_obj Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section D2Kit.
Variable RT : rt_sig.

Definition d2_join (Σ : rts RT) (PMc : Model -> Prop) (gp s0 : word)
    (sa fb lo fr shf w h wpls wpld datas datad rd bufs1 bufs2 n1 ta t38 t14 : Z) (dead3 : nat) (svd : list cell) (mh : mem)
    : config -> Prop :=
  fun c => ASTA RT Σ PMc (fun ms => exists (m' : mem) (ic : word) (j0 j56 j160 : list byte)
      (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s3' s7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms = MS (mkR ra' (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' (Z_to_bv 64 bufs1)
                   (Z_to_bv 64 fr) s3' (Z_to_bv 64 SHB) (Z_to_bv 64 (w - 1)) (Z_to_bv 64 w) s7' (Z_to_bv 64 ta) (Z_to_bv 64 t38) (Z_to_bv 64 bufs2) (Z_to_bv 64 shf)
                   t3' t4' t5' t6')
              F' (Z_to_bv 64 0x9eae4) (frm_clear fc') None m' (seg_rom asegs)
      /\ ART RT Σ m' /\ mem_inv asegs m' /\ stk asegs m' lo sa /\ LIBH m' /\ io_ssp m'
      /\ rw_cells asegs m' sa [CB 24 j0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 fr); C8 (Z_to_bv 64 (fr + 80)); C8 (Z_to_bv 64 (fr + 112))]
      /\ rw_cells asegs m' (sa + 56) [CB 32 j56; C8 (Z_to_bv 64 (h - 1)); C8 (Z_to_bv 64 (4 * wpls)); C8 (Z_to_bv 64 wpls); C8 (Z_to_bv 64 datas);
                                    C8 (Z_to_bv 64 wpld); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 bufs1); C8 ic; C8 (Z_to_bv 64 t14)]
      /\ rw_cells asegs m' (sa + 160) (CB dead3 j160 :: svd)
      /\ agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) sa a /\ outside [(datad, datad + rd); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1); (sa, sa + fb)] a) mh m') c.

End D2Kit.
