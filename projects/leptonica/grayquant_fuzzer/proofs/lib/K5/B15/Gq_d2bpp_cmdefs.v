(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env Gq_obj Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section D2CMDEFS.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition d2cm_keep (L : list (Z * Z)) (frames : list (Z * nat)) (sa pixd : Z) (a : Z) : Prop :=
  aclient L frames sa a /\ outside [(pixd + 48, pixd + 56)] a.

(* [comment removed for export] *)
Definition d2cm_post (Σ : rts RT) PMc (gp : word) (sa usp lo fr pixd : Z) (vd : pixv) (L0 : list (Z * Z)) (m0 : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (m' : mem) (cmap carr : Z)
                  (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
    ASTA RT Σ' PMc (eq (MS (mkR ra' (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' a7'
                                 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 112)) s4' s5' s6' s7' s8' (Z_to_bv 64 (fr / 8 + 2147450880)) s10' s11' t3' t4' t5' t6')
                            F' (Z_to_bv 64 0xa0394) (frm_clear fc') None m' (seg_rom asegs))) c
    /\ ART RT Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo sa /\ LIBH m' /\ io_ssp m'
    /\ rt_live RT Σ' = (carr, 16) :: (cmap, 24) :: L0 /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ - 6 <= rt_credit RT Σ'
    /\ cmap_obj (rt_live RT Σ') m' cmap (mkCmapv carr 2 4 4) /\ 0 < cmap /\ 0 < carr /\ cmap <> carr
    /\ (forall e, In e (rt_live RT Σ) -> fst e <> cmap /\ fst e <> carr)
    /\ (forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) sa a -> (a < cmap \/ cmap + 24 <= a) /\ (a < carr \/ carr + 16 <= a))
    /\ rw_cells asegs m' pixd (pix_cells (mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vd) (p_yres vd) (p_inf vd) (p_spec vd) cmap (p_data vd)))
    /\ agree_on (d2cm_keep L0 (rt_frames RT Σ) sa pixd) m0 m'.

(* [comment removed for export] *)
Definition d2_cmfree_cps : Prop :=
  forall (Σ : rts RT) PMc (m : mem)
         (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (sa usp lo fr pixd bufs1 bufs2 n1 tv t38 t14 fp1 s6v s7v : Z) (vd : pixv) (L0 : list (Z * Z)) (frs0 : list (Z * nat)),
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σ = (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, n1) :: (bufs1, n1) :: L0 -> 0 < n1 ->
  rt_frames RT Σ = (fr, 2%nat) :: frs0 ->
  (forall p n, In (p, n) L0 -> 0 < n) ->
  (forall e, In e L0 -> fst e <> bufs1 /\ fst e <> bufs2 /\ fst e <> tv /\ fst e <> t38 /\ fst e <> t14) ->
  NoDup [bufs1; bufs2; tv; t38; t14] ->
  Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> Z.of_nat (length (rt_frames RT Σ)) + 3 <= Z.of_nat FRAMES_MAX -> 6 <= rt_credit RT Σ ->
  pix_obj (rt_live RT Σ) m pixd vd (mkCmapv 0 0 0 0) -> In (pixd, 64) L0 -> In (p_data vd, rsize vd) L0 -> p_cmap vd = 0 -> p_data vd <> 0 ->
  0 <= fp1 < 2^64 -> chain_ok m usp fp1 [RA_TOP] ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> 0 <= lo -> lo + LSTK 10 <= sa -> sa mod 32 = 0 -> sa + 256 <= usp -> usp <= sa + 272 -> usp mod 16 = 0 ->
  usp + 16 <= USTACK_TOP -> usp <= rt_sp0 RT Σ -> 0 < fr -> fr mod 64 = 0 -> fr + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo sa -> LIBH m -> io_ssp m ->
  rw_cells asegs m (usp + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 RA_FUZZ_OP1)] ->
  rw_cells asegs m (sa + 32) [C8 (Z_to_bv 64 1)] -> rw_cells asegs m (sa + 48) [C8 (Z_to_bv 64 (fr + 112))] ->
  rw_cells asegs m (sa + 112) [C8 (Z_to_bv 64 tv); C8 (Z_to_bv 64 t38)] -> rw_cells asegs m (fr + 112) [C8 (Z_to_bv 64 pixd)] ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 fr) s3 (Z_to_bv 64 t14) (Z_to_bv 64 bufs1) (Z_to_bv 64 s6v) (Z_to_bv 64 s7v) (Z_to_bv 64 bufs2)
                                        (Z_to_bv 64 (fr / 8 + 2147450880)) s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0xa0340) (frm_clear fc) None m (seg_rom asegs))))
    (d2cm_post Σ PMc gp sa usp lo fr pixd vd L0 m).

End D2CMDEFS.
