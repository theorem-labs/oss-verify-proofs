(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDOut BzDK BzDOKp DecCutFA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require L2Stmt.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section StmtD.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition hbCreateDecodeTables_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z),
  let usp := bv_unsigned sp in
  let LIM := DS + 45436 + 1032 * t in let BASE := DS + 51628 + 1032 * t in let PERM := DS + 57820 + 1032 * t in let LEN := DS + 43888 + 258 * t in
  let W := [(LIM, LIM + 1032); (BASE, BASE + 1032); (PERM, PERM + 1032)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 LIM -> a1 = Z_to_bv 64 BASE -> a2 = Z_to_bv 64 PERM -> a3 = Z_to_bv 64 LEN ->
  a4 = Z_to_bv 64 minLen -> a5 = Z_to_bv 64 maxLen -> a6 = Z_to_bv 64 alpha ->
  tp = Z_to_bv 64 0x5fc0d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  u32arr a0segs m LIM lws -> length lws = 258%nat -> u32arr a0segs m BASE bws -> length bws = 258%nat ->
  u32arr a0segs m PERM pws -> length pws = 258%nat -> u8arr a0segs m LEN lbs -> length lbs = 258%nat ->
  In (DS, 64144) (rt_live RT Σ) -> DS mod 16 = 0 -> 0 <= t < 6 ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 64 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  1 <= alpha <= 258 -> (1 <= minLen /\ minLen <= maxLen <= 20) -> (forall j, 0 <= j < alpha -> minLen <= uv8 lbs j <= maxLen) ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9dfd4) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (lws' bws' pws' : list word),
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom a0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo usp
          /\ u32arr a0segs m' LIM lws' /\ length lws' = 258%nat /\ u32arr a0segs m' BASE bws' /\ length bws' = 258%nat
          /\ u32arr a0segs m' PERM pws' /\ length pws' = 258%nat
          /\ (let '(limit, base, perm) := hb_create (sv32 lws) (sv32 bws) (sv32 pws) (uv8 lbs) minLen maxLen alpha in
              ag32s lws' limit 258 /\ ag32s bws' base 258 /\ ag32s pws' perm 258)
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dmemL (cx : bctx) (payload : list byte) (m : mem) (v : dv) : Prop :=
  rw_cells a0segs m (b_s cx) (HEAD_CELLS (dv_h v)) /\
  rw_cells a0segs m (b_s cx + 1092) [C4 (Z_to_bv 64 (dv_nbu v))] /\
  u32arr a0segs m (b_s cx + 1096) (dv_cf v) /\
  rw_cells a0segs m (b_s cx + 3152) (MID_CELLS (dv_d v)) /\
  rw_cells a0segs m (b_s cx + 64036) (SAVE_CELLS (dv_j1 v) (dv_snb v) (dv_j2 v)) /\
  drest_at a0segs m (b_s cx) (dv_r v) /\
  rw_cells a0segs m (b_strm cx) (STRM_CELLS (dv_b v)) /\
  blk_at a0segs m cx (dv_k v) /\
  bytes_at a0segs m (b_src cx) payload.

(* [comment removed for export] *)
Definition dsepA (cx : bctx) : Prop :=
  let s := b_s cx in let strm := b_strm cx in let src := b_src cx in let len := b_len cx in let dst := b_dst cx in let dlen := b_dlen cx in let n := b_n cx in
  disj s 64144 strm 80 /\ disj s 64144 src len /\ disj s 64144 dst dlen /\ disj strm 80 src len /\ disj strm 80 dst dlen /\ disj src len dst dlen /\
  (b_tt cx <> 0 -> disj s 64144 (b_tt cx) (400000 * n) /\ disj strm 80 (b_tt cx) (400000 * n) /\ disj src len (b_tt cx) (400000 * n) /\ disj dst dlen (b_tt cx) (400000 * n)) /\
  (b_ll16 cx <> 0 -> disj s 64144 (b_ll16 cx) (200000 * n) /\ disj strm 80 (b_ll16 cx) (200000 * n) /\ disj src len (b_ll16 cx) (200000 * n) /\ disj dst dlen (b_ll16 cx) (200000 * n)) /\
  (b_ll4 cx <> 0 -> disj s 64144 (b_ll4 cx) (50000 * n) /\ disj strm 80 (b_ll4 cx) (50000 * n) /\ disj src len (b_ll4 cx) (50000 * n) /\ disj dst dlen (b_ll4 cx) (50000 * n)) /\
  (b_ll16 cx <> 0 -> b_ll4 cx <> 0 -> disj (b_ll16 cx) (200000 * n) (b_ll4 cx) (50000 * n)).

(* [comment removed for export] *)
Definition dpureA (cx : bctx) : Prop :=
  0 <= b_len cx < 134217728 /\ 0 <= b_dlen cx < 134217728 /\ (b_small cx = 0 \/ b_small cx = 1) /\ 0 <= b_n cx <= 9 /\
  b_s cx mod 16 = 0 /\ b_tt cx mod 16 = 0 /\ b_ll16 cx mod 16 = 0 /\ b_ll4 cx mod 16 = 0 /\
  dsepA cx.

(* [comment removed for export] *)
Definition dliveA (Σ : rts RT) (m : mem) (cx : bctx) (zp zn op on : Z) : Prop :=
  In (b_s cx, 64144) (rt_live RT Σ) /\
  In (zp, zn) (rt_live RT Σ) /\ zp <= b_src cx /\ b_src cx + b_len cx <= zp + zn /\
  In (op, on) (rt_live RT Σ) /\ op <= b_dst cx /\ b_dst cx + b_dlen cx <= op + on /\
  (b_tt cx <> 0 -> In (b_tt cx, 400000 * b_n cx) (rt_live RT Σ)) /\
  (b_ll16 cx <> 0 -> In (b_ll16 cx, 200000 * b_n cx) (rt_live RT Σ)) /\
  (b_ll4 cx <> 0 -> In (b_ll4 cx, 50000 * b_n cx) (rt_live RT Σ)) /\
  L2Stmt.strm_okA RT Σ m (b_strm cx).

(* [comment removed for export] *)
Definition DEC_STACK : Z := 848 + 256.

(* [comment removed for export] *)
Definition decompress14_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (cx : bctx) (payload : list byte) (J : jk) (d : dst) (s : dstrm) (zp zn op on lo : Z),
  let usp := bv_unsigned sp in
  let W := [(b_s cx, b_s cx + 64144); (b_strm cx, b_strm cx + 20)] ++ blk_ivls cx in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 (b_s cx) -> tp = Z_to_bv 64 0x5fc0d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  dmemL cx payload m (dvF cx J d s) -> L_libA.LIB_A m ->
  dliveA Σ m cx zp zn op on -> dpureA cx ->
  Z.of_nat (length payload) = b_len cx -> 1 <= b_n cx ->
  (b_small cx = 0 -> b_tt cx <> 0) -> (b_small cx = 1 -> b_ll16 cx <> 0 /\ b_ll4 cx <> 0) ->
  dpureF cx (bs_of cx J s) payload J d s -> d_state d = 14 -> 0 <= s_avail_out s <= b_dlen cx ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + DEC_STACK <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9e368) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (J' : jk),
          let '(rv, d', s') := decompress d s in
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom a0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo usp
          /\ dmemL cx payload m' (dvF cx J' d' s') /\ L_libA.LIB_A m'
          /\ dpureF cx (bs_of cx J s) payload J' d' s' /\ dpost14W (rv, d', s')
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRMD (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w48 w56 w64 w72 : word) : list cell :=
  [C8 w0; C4 w8; C4 w12; C4 w16; CB 4 q1; C8 w24; C4 w32; C4 w36; C4 w40; CB 4 q2; C8 w48; C8 w56; C8 w64; C8 w72].
Lemma strm_cells_eq : forall b : bzs, STRM_CELLS b =
  STRMD (Z_to_bv 64 (bs_src b + (bs_len b - bs_ai b))) (Z_to_bv 64 (bs_ai b)) (bs_til b) (bs_tih b) (bs_q1 b)
        (Z_to_bv 64 (bs_dst b + (bs_dlen b - bs_av b))) (Z_to_bv 64 (bs_av b)) (bs_tol b) (bs_toh b) (bs_q2 b) (Z_to_bv 64 (bs_S b)) (bs_bzalloc b) (bs_bzfree b) (bs_opaque b).
Proof. reflexivity. Qed.
Definition DBZA : Z := 0x82450.   (* [comment removed for export] *)
Definition DBZF : Z := 0x82458.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hwf10A (h : dsh) (strm small : Z) : Prop :=
  sh_strm h = strm /\ sh_state h = 10 /\ sh_bsBuff h = 0 /\ sh_bsLive h = 0 /\ bv_unsigned (sh_small h) = small /\
  sh_cbn h = 0 /\ sh_verb h = 0 /\
  length (sh_p1 h) = 3%nat /\ length (sh_p2 h) = 3%nat /\ length (sh_p3 h) = 3%nat /\
  0 <= sh_solen h < 2 ^ 32 /\ 0 <= sh_rNToGo h < 2 ^ 32 /\ 0 <= sh_rTPos h < 2 ^ 32 /\ 0 <= sh_n h < 2 ^ 32 /\
  0 <= sh_origPtr h < 2 ^ 32.
(* [comment removed for export] *)
Definition dstate10A (m : mem) (S strm small : Z) (h0 : dsh) (nbu0 : Z) (cf0 : list word) (d0 : dsm) (r0 : drest) (js : list byte) : Prop :=
  rw_cells a0segs m S (HEAD_CELLS h0) /\ hwf10A h0 strm small /\
  rw_cells a0segs m (S + 1092) [C4 (Z_to_bv 64 nbu0)] /\ 0 <= nbu0 < 2 ^ 32 /\
  u32arr a0segs m (S + 1096) cf0 /\ length cf0 = 257%nat /\
  rw_cells a0segs m (S + 3152) (MID_CELLS d0) /\ sm_tt d0 = 0 /\ sm_ll16 d0 = 0 /\ sm_ll4 d0 = 0 /\ 0 <= sm_nInUse d0 < 2 ^ 32 /\ sm_cccrc d0 = Z_to_bv 64 0 /\
  drest_at a0segs m S r0 /\
  rw_cells a0segs m (S + 64036) [CB 108 js].
(* [comment removed for export] *)
Definition strm10A (b0 : bzs) (cx : bctx) : Prop :=
  bzs_wf b0 /\ bs_S b0 = b_s cx /\ bs_src b0 = b_src cx /\ bs_len b0 = b_len cx /\ bs_dst b0 = b_dst cx /\ bs_dlen b0 = b_dlen cx /\
  bs_bzalloc b0 = Z_to_bv 64 DBZA /\ bs_bzfree b0 = Z_to_bv 64 DBZF /\ bs_opaque b0 = Z_to_bv 64 0 /\ bs_ai b0 = bs_len b0 /\ bs_av b0 = bs_dlen b0 /\
  bs_til b0 = Z_to_bv 64 0.

(* [comment removed for export] *)
Definition cx_blocks (cx : bctx) (n tt l16 l4 : Z) : bctx :=
  BCX (b_s cx) (b_strm cx) (b_src cx) (b_len cx) (b_dst cx) (b_dlen cx) (b_pdl cx) (b_sp cx) (b_small cx) n tt l16 l4.
Definition dblocks (n tt l16 l4 : Z) : list (Z * Z) :=
  (if l4 =? 0 then [] else [(l4, 50000 * n)]) ++ (if l16 =? 0 then [] else [(l16, 200000 * n)]) ++ (if tt =? 0 then [] else [(tt, 400000 * n)]).
(* [comment removed for export] *)
Definition dblocks_ok (small n tt l16 l4 : Z) : Prop :=
  (n = 0 /\ tt = 0 /\ l16 = 0 /\ l4 = 0) \/ (1 <= n <= 9 /\ ((small = 0 /\ tt <> 0 /\ l16 = 0 /\ l4 = 0) \/ (small = 1 /\ tt = 0 /\ l16 <> 0 /\ l4 <> 0))).

(* [comment removed for export] *)
Definition DEC10_COST : Z := 1 + mcost 3600000.
Definition BZD_COST (len : Z) : Z := DEC10_COST + len + 2.
Definition BZD_STACK : Z := 400 + DEC_STACK.

(* [comment removed for export] *)
Definition decompress10_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (cx : bctx) (payload : list byte)
         (h0 : dsh) (nbu0 : Z) (cf0 : list word) (d0 : dsm) (r0 : drest) (js : list byte) (b0 : bzs) (zp zn op on lo : Z),
  let usp := bv_unsigned sp in
  let W := [(b_s cx, b_s cx + 64144); (b_strm cx, b_strm cx + 20)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 (b_s cx) -> tp = Z_to_bv 64 0x5fc0d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  ra = Z_to_bv 64 0x87038 -> (bv_unsigned s0 <= usp \/ bv_unsigned s0 mod 8 <> 0 \/ 2 ^ 63 <= bv_unsigned s0) ->
  dstate10A m (b_s cx) (b_strm cx) (b_small cx) h0 nbu0 cf0 d0 r0 js ->
  rw_cells a0segs m (b_strm cx) (STRM_CELLS b0) -> strm10A b0 cx ->
  bytes_at a0segs m (b_src cx) payload -> Z.of_nat (length payload) = b_len cx -> L_libA.LIB_A m ->
  dliveA Σ m cx zp zn op on -> dpureA cx -> b_n cx = 0 -> b_tt cx = 0 -> b_ll16 cx = 0 -> b_ll4 cx = 0 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> DEC10_COST <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + DEC_STACK <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9e368) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT) (n tt l16 l4 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (junkD : dst),
          let cx' := cx_blocks cx n tt l16 l4 in
          let '(rv, dF, sF) := decompress (dst_init junkD 0 (b_small cx)) (dstrm_init (map bv_unsigned payload) (b_dlen cx)) in
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom a0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo usp /\ L_libA.LIB_A m'
          /\ dliveA Σ' m' cx' zp zn op on /\ dpureA cx' /\ dblocks_ok (b_small cx) n tt l16 l4
          /\ ((exists J' : jk, dmemL cx' payload m' (dvF cx' J' dF sF) /\ dpureF cx' b0 payload J' dF sF /\ dpost14W (rv, dF, sF) /\ 1 <= n)
              \/ ((rv = BZ_OK \/ rv = BZ_DATA_ERROR_MAGIC) /\ 10 <= d_state dF <= 13 /\ s_out sF = [] /\ s_avail_out sF = b_dlen cx /\ n = 0
                  /\ exists (h : dsh) (dm : dsm) (ai : Z) (til tih : word),
                       rw_cells a0segs m' (b_s cx) (HEAD_CELLS h) /\ sh_strm h = b_strm cx /\ 0 <= sh_state h < 2 ^ 31 /\ sh_state h <> BZ_X_OUTPUT
                       /\ rw_cells a0segs m' (b_s cx + 3152) (MID_CELLS dm) /\ sm_tt dm = 0 /\ sm_ll16 dm = 0 /\ sm_ll4 dm = 0
                       /\ rw_cells a0segs m' (b_strm cx) (STRM_CELLS (bupd b0 ai til tih)) /\ 0 <= ai <= bs_ai b0))
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = dblocks n tt l16 l4 ++ rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - DEC10_COST <= rt_credit RT Σ' <= rt_credit RT Σ - 1).

(* [comment removed for export] *)
Definition bzDecompress_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (cx : bctx) (payload db0 : list byte)
         (h0 : dsh) (nbu0 : Z) (cf0 : list word) (d0 : dsm) (r0 : drest) (js : list byte) (b0 : bzs) (zp zn op on lo : Z),
  let usp := bv_unsigned sp in
  let W := [(b_s cx, b_s cx + 64144); (b_strm cx, b_strm cx + 80); (b_dst cx, b_dst cx + b_dlen cx)] in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 (b_strm cx) -> tp = Z_to_bv 64 0x5fc0d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  dstate10A m (b_s cx) (b_strm cx) (b_small cx) h0 nbu0 cf0 d0 r0 js ->
  rw_cells a0segs m (b_strm cx) (STRM_CELLS b0) -> strm10A b0 cx ->
  bytes_at a0segs m (b_src cx) payload -> Z.of_nat (length payload) = b_len cx ->
  u8arr a0segs m (b_dst cx) db0 -> Z.of_nat (length db0) = b_dlen cx -> L_libA.LIB_A m ->
  dliveA Σ m cx zp zn op on -> dpureA cx -> b_n cx = 0 -> b_tt cx = 0 -> b_ll16 cx = 0 -> b_ll4 cx = 0 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> BZD_COST (b_len cx) <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + BZD_STACK <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x84294) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT) (n tt l16 l4 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (junkD : dst)
                                        (h : dsh) (dm : dsm) (b' : bzs) (db rest : list byte),
          let cx' := cx_blocks cx n tt l16 l4 in
          let '(rv, dF, sF) := bzDecompress (dst_init junkD 0 (b_small cx)) (dstrm_init (map bv_unsigned payload) (b_dlen cx)) in
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom a0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo usp /\ L_libA.LIB_A m'
          /\ dliveA Σ' m' cx' zp zn op on /\ dpureA cx' /\ dblocks_ok (b_small cx) n tt l16 l4
          /\ rw_cells a0segs m' (b_s cx) (HEAD_CELLS h) /\ sh_strm h = b_strm cx
          /\ rw_cells a0segs m' (b_s cx + 3152) (MID_CELLS dm) /\ sm_tt dm = tt /\ sm_ll16 dm = l16 /\ sm_ll4 dm = l4
          /\ rw_cells a0segs m' (b_strm cx) (STRM_CELLS b') /\ bzs_wf b' /\ bs_S b' = b_s cx /\ bs_dst b' = b_dst cx /\ bs_dlen b' = b_dlen cx
          /\ bs_bzfree b' = Z_to_bv 64 DBZF /\ bs_opaque b' = Z_to_bv 64 0 /\ bs_av b' = s_avail_out sF
          /\ u8arr a0segs m' (b_dst cx) db /\ Z.of_nat (length db) = b_dlen cx
          /\ db = map (Z_to_bv 8) (s_output sF) ++ rest /\ Z.of_nat (length (s_output sF)) = b_dlen cx - s_avail_out sF
          /\ -5 <= rv <= 4
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = dblocks n tt l16 l4 ++ rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - BZD_COST (b_len cx) <= rt_credit RT Σ' <= rt_credit RT Σ).

(* [comment removed for export] *)
Definition bzDecompressInit_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (STRM small : Z) (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w48 : word) (lo : Z),
  let usp := bv_unsigned sp in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 STRM -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 small -> (small = 0 \/ small = 1) ->
  tp = Z_to_bv 64 0x5fc0d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  rw_cells a0segs m STRM (STRMD w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) -> length q1 = 4%nat -> length q2 = 4%nat ->
  L2Stmt.strm_okA RT Σ m STRM ->
  Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 128 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x83eb4) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT) (S : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc'
                                        (h0 : dsh) (nbu0 : Z) (cf0 : list word) (d0 : dsm) (r0 : drest) (js : list byte),
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom a0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo usp
          /\ dstate10A m' S STRM small h0 nbu0 cf0 d0 r0 js
          /\ rw_cells a0segs m' STRM (STRMD w0 w8 (Z_to_bv 64 0) (Z_to_bv 64 0) q1 w24 w32 (Z_to_bv 64 0) (Z_to_bv 64 0) q2 (Z_to_bv 64 S)
                                          (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0))
          /\ S mod 16 = 0 /\ (forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (S <= a < S + 64144))
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(STRM, STRM + 80)] m m') c
       /\ rt_live RT Σ' = (S, 64144) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition rm0 (p : Z) (l : list (Z * Z)) : list (Z * Z) := if p =? 0 then l else live_remove p l.
Definition bzDecompressEnd_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (STRM S n tt l16 l4 : Z) (h : dsh) (dm : dsm) (b : bzs) (lo : Z),
  let usp := bv_unsigned sp in
  let W := [(S, S + 64144); (STRM + 48, STRM + 56)] ++ map (fun e => (fst e, fst e + snd e)) (dblocks n tt l16 l4) in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 STRM -> tp = Z_to_bv 64 0x5fc0d8 -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  rw_cells a0segs m S (HEAD_CELLS h) -> sh_strm h = STRM ->
  rw_cells a0segs m (S + 3152) (MID_CELLS dm) -> sm_tt dm = tt -> sm_ll16 dm = l16 -> sm_ll4 dm = l4 ->
  rw_cells a0segs m STRM (STRM_CELLS b) -> bs_S b = S -> bs_bzfree b = Z_to_bv 64 DBZF -> bs_opaque b = Z_to_bv 64 0 -> length (bs_q1 b) = 4%nat -> length (bs_q2 b) = 4%nat ->
  L2Stmt.strm_okA RT Σ m STRM ->
  In (S, 64144) (rt_live RT Σ) -> (forall e, In e (dblocks n tt l16 l4) -> In e (rt_live RT Σ)) -> 0 <= n <= 9 ->
  (tt <> 0 \/ l16 <> 0 \/ l4 <> 0 -> 1 <= n) ->      (* [comment removed for export] *)
  S mod 16 = 0 -> 0 <= tt -> 0 <= l16 -> 0 <= l4 ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 128 <= usp ->
  usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x87b68) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
          ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom a0segs)
          /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo usp
          /\ rw_cells a0segs m' STRM (STRM_CELLS (BZS (bs_src b) (bs_len b) (bs_ai b) (bs_til b) (bs_tih b) (bs_q1 b) (bs_dst b) (bs_dlen b) (bs_av b)
                                                     (bs_tol b) (bs_toh b) (bs_q2 b) 0 (bs_bzalloc b) (bs_bzfree b) (bs_opaque b)))
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m') c
       /\ rt_live RT Σ' = live_remove S (rm0 l4 (rm0 l16 (rm0 tt (rt_live RT Σ))))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

End StmtD.
