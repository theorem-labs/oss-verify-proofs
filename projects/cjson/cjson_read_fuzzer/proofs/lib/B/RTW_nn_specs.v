(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Frame Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_aspec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Definition large_alloc_nn_specW : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g ->
  0 <= n -> bprim n = false -> needed n <= 2^40 ->
  a0 = wz A_SECONDARY -> a1 = wz A_GSTATS -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  SEC_ALLOC_COST n + SEC_SLOT_TAX + rt_prov st <= g_res g ->
  mmap_placeable mo (smapsize n) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ALARGE_ALLOC_STACK ->
  mem_inv bsegs m ->
  LSCPS bsegs (sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ALARGE_ALLOC) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ms_a0 (ms : machine_state) : word := reg_get (ms_regs ms) 10.
Lemma ms_a0_MS : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F pc fc rv m ro,
  ms_a0 (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv m ro) = a0.
Proof. intros. reflexivity. Qed.
Definition nz_post (P : machine_state -> Model -> lghost -> Prop) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => P ms' mo' g' /\ ms_a0 ms' <> wz 0.
Lemma wz_nz : forall r, 0 < r < 2^64 -> wz r <> wz 0.
Proof.
  intros r Hr E. apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !unsigned_lit in E by lia. lia.
Qed.

(* [comment removed for export] *)
Definition refill_room (st : rtstate) (cls : Z) : Prop :=
  navail st cls < nrefill cls -> r_mapped (rg st cls) + 262144 <= KFREEARRAY_OFF.
Definition refill_nn_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (cls lo : Z),
  RTS st m mo g ->
  1 <= cls <= 30 -> cch st cls = [] ->
  a0 = wz (acache st) -> a1 = wz (pcaddr st cls) -> a2 = wz A_ALLOC -> a3 = wz cls ->
  tp = wz ATP ->
  rt_prov st <= g_res g ->
  refill_room st cls ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  mem_inv bsegs m ->
  LSCPS bsegs (refill2_post 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AREFILL) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)
Definition cnn_ok (st : rtstate) (mo : Model) (n : Z) : Prop :=
  if bprim n then refill_room st (pclass n) else mmap_placeable mo (smapsize n).

(* [comment removed for export] *)
Definition combined_alloc_nn_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 ->
  a0 = wz A_ALLOC -> a1 = wz (acache st) -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  calloc_deposit n + rt_prov st <= g_res g ->
  cnn_ok st mo n ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK -> bv_unsigned sp <= st_sp0 st ->
  mem_inv bsegs m ->
  LSCPS bsegs (nz_post (calloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ACALLOC) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)
Definition alloc_post_nn (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n : Z) (tr : list Z) (lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' =>
    nz_post (alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g) ms' mo' g'
    /\ (bprim n = false -> alloc_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g ms' mo' g').
Definition allocate_nn_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n S : Z) (tr : list Z) (lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 ->
  a0 = wz A_ALLOC -> a1 = wz n -> a2 = wz 8 -> a3 = wz S -> a4 = wz 1 -> a5 = wz 1 ->
  tp = wz ATP ->
  rw_cells bsegs m S [C8 (wz (S + 16)); C4 (wz (zlen tr)); C4 (wz 0)] -> cells_at bsegs m (S + 16) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  bv_unsigned sp <= S -> S + BST_SIZE <= st_sp0 st + 4096 ->
  trs_room tr (st_trs st) ->
  alloc_deposit n + rt_prov st <= g_res g ->
  cnn_ok st mo n ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AALLOCATE_STACK <= bv_unsigned sp -> bv_unsigned sp <= st_sp0 st ->
  mem_inv bsegs m ->
  LSCPS bsegs (alloc_post_nn ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AALLOCATE) fc None m (seg_rom bsegs)) mo g.


End CeilWrap.
