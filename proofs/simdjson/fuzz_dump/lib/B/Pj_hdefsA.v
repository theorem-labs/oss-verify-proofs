(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_pid1A Atp_pidiA Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition PJ_LFTOI_SM : Z := 0xae6b8.
Definition PJ_LFTOI_PID : Z := 0xb1888.
Definition PJ_OKARM_A : Z := 0xb1898.
Definition PJ_JOIN_A : Z := 0xb1ad0.

Definition PJ_OKARM_STACK_A : Z := PJ_SER_STACK_A.

Definition pj_pid_costA (len : Z) : Z := pid_cost6 (Z.max len 32) + mcost (len + 64) + S2A_COST len.

Definition SJ_W : list (Z * Z) := [(0x6a9840, 0x6a9848); (0x6a9860, 0x6a9862); (0x6a98e0, 0x6a990c); (0x6a9940, 0x6a9942)].
Definition pid_XA (P RES : Z) : list (Z * Z) := (P, P + 80) :: (RES, RES + 24) :: SJ_W.

Section HStmts.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PDONE : rts RT -> mem -> Z -> list (Z * Z) -> Prop.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition pdone_fpA : Prop :=
  forall (Σ Σ' : rts RT) (m m' : mem) (P : Z) (L : list (Z * Z)),
    PDONE Σ m P L -> ART RT Σ m -> rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ ->
    (forall a : word, (P <= bv_unsigned a < P + 80 \/ shad P <= bv_unsigned a < shad P + 10 \/ in_live (rt_live RT Σ) (bv_unsigned a)) -> m' a = m a) ->
    PDONE Σ' m' P L.

Definition pj_pid_cpsA : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (P RES d : Z) (bs p1 p17 p57 jr : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = wz RES -> a1 = wz P -> a2 = wz (P + 24) -> a3 = wz d -> a4 = wz (Z.of_nat (length bs)) -> a5 = wz 1 -> tp = wz TPV_A ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  fobj RT Σ m P 80 -> rw_cells bsegs m P (parser_init p1 p17 p57) ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP -> RES mod 8 = 0 -> rw_cells bsegs m RES [CB 24 jr] ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + 8 <= LIVE_MAX -> (length (rt_frames RT Σ) + PID_FRAMES <= FRAMES_MAX)%nat ->
  pj_pid_costA (Z.of_nat (length bs)) <= rt_credit RT Σ ->
  LIB m -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_pid m)))
    (fun c => exists (Σ' : rts RT) (cp : list (Z * Z)) (impl idx oc ia tape sbuf : Z),
       let len := Z.of_nat (length bs) in let cap := Z.max len 32 in
       ASTA RT Σ' PMc (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (pid_XA P RES) m m'
         /\ (exists (r : word) j20, rw_cells bsegs m' RES (res_cellsA (P + 24) r j20) /\ bv_unsigned r < 64
               /\ s2a_okres tape sbuf (roundup64 (cap + 3)) (al_sbuf cap) r m'
               /\ (r = wz 0 -> len <= SJ_PADMAX))
         /\ LIB m' /\ PDONE Σ' m' P (rt_live RT Σ) /\ fobj RT Σ' m' P 80
         /\ rw_cells bsegs m' (P + 24) [C8 (wz tape); C8 (wz sbuf)]) c
       /\ rt_live RT Σ' = cp ++ (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: rt_live RT Σ
       /\ ((exists COPY, cp = [(COPY, len + 64)] /\ 0 < COPY /\ len <= SJ_PADMAX) \/ cp = [])
       /\ (0 < impl /\ 0 < idx /\ 0 < oc /\ 0 < ia /\ 0 < tape /\ 0 < sbuf /\ tape mod 16 = 0 /\ sbuf mod 16 = 0)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - pj_pid_costA len <= rt_credit RT Σ').

Section WithPM.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition pj_okarm_W (E : pjenvA) (S1 : Z) : list (Z * Z) :=
  [(S1 + 24, S1 + 32); (pa_SB E, pa_SB E + 88); (pa_F E + 272, pa_F E + 560);
   (shad (pa_F E) + 4, shad (pa_F E) + 15); (shad (pa_F E) + 34, shad (pa_F E) + 70); (PJ_LOC_LO_A, PJ_LOC_HI_A)].

Definition pj_shadow_cut : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 11 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 10 ++ repeat (Z_to_bv 8 (-14)) 4
  ++ repeat (Z_to_bv 8 (-8)) 36 ++ repeat (Z_to_bv 8 (-13)) 10.

Definition pj_okarm_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (E : pjenvA) (S1 usp : Z)
         (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (j24 jsb jos : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  pjenvA_ok E -> pa_kF E = 4%nat -> pa_SB E = pa_F E + 32 -> pa_DOC E = pa_F E + 184 ->
  pa_live RT Σ E (sbA0 (pa_SB E)) -> DOCREPA E m -> pj_locA m -> libc_nl m -> lockwA m -> io_ssp m ->
  rw_cells bsegs m (S1 + 24) [CB 8 j24] -> rw_cells bsegs m (S1 + 64) [C8 (wz (pa_F E + 184)); C8 (wz 1); C4 (wz 0)] ->
  rw_cells bsegs m (pa_SB E) [CB 88 jsb] -> rw_cells bsegs m (pa_F E + 272) [CB 288 jos] ->
  rw_cells bsegs m (shad (pa_F E)) (map C1 pj_shadow_cut) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (pa_lo E) S1 -> pa_lo E + PJ_OKARM_STACK_A <= S1 -> S1 + 192 + 16 <= USTACK_TOP -> S1 mod 32 = 0 ->
  S1 + 192 <= usp <= S1 + 208 -> frm0 fc ->
  rt_frames RT Σ = [(pa_F E, 4%nat)] -> Z.of_nat (length (pa_L E)) + 3 <= LIVE_MAX -> 2 * pa_n E + 2 + 2^30 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' t3' t4' t5' t6' F' fc' m',
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) S1 ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - (2 * pa_n E + 2 + 2^30) <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) S1 (pj_okarm_W E S1) m m' -> LOCBA m' ->
     (exists j24' jsb' jos', rw_cells bsegs m' (S1 + 24) [CB 8 j24'] /\ rw_cells bsegs m' (pa_SB E) [CB 88 jsb'] /\ rw_cells bsegs m' (pa_F E + 272) [CB 288 jos']) ->
     rw_cells bsegs m' (shad (pa_F E)) (map C1 pj_shadow_cut) ->
     aevt Σ' K (MS (mkR ra' (wz S1) gp (wz TPV_A) t0' t1' t2' (wz usp) (wz S1) a0' a1' a2' a3' a4' a5' a6' a7'
                       (wz (pa_F E)) (wz (pa_F E + 160)) (wz (shad (pa_F E))) s5' s6' s7' s8' s9' (wz (pa_F E)) (wz SHB) t3' t4' t5' t6')
                  F' (wz PJ_JOIN_A) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz 0) a1 a2 a3 a4 a5 a6 a7
                  (wz (pa_F E)) (wz (pa_F E + 160)) (wz (shad (pa_F E))) s5 s6 s7 s8 s9 (wz (pa_F E)) (wz SHB) t3 t4 t5 t6)
             F (wz PJ_OKARM_A) fc None m (seg_rom bsegs)).

End WithPM.
End HStmts.
