(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_secondary_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition ALARGE_ALLOC : Z := 0x3686c.     (* [comment removed for export] *)
Definition AGET_BLOCK_BEGIN : Z := 0x343d0. (* [comment removed for export] *)
Definition ALARGE_DEALLOC : Z := 0x34718.   (* [comment removed for export] *)
Definition ALARGE_ALLOC_STACK : Z := 2048.  (* [comment removed for export] *)
Definition AGBB_STACK : Z := 64.
Definition ALARGE_DEALLOC_STACK : Z := 2048. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SEC_ALLOC_COST (n : Z) : Z := smapsize n + smapsize n / 8 + 8192.

(* [comment removed for export] *)
Lemma prov_slots_le : forall st, RTWF st -> SEC_SLOT_TAX * nsec st <= rt_prov st.
Proof.
  intros st WF. pose proof (rt_prov_nonneg st WF) as NN. unfold rt_prov in *.
  pose proof (prov_classes_nonneg st).
  assert (0 <= prov_nb st) by (unfold prov_nb; destruct (st_qthread st); unfold NB; lia).
  pose proof (prov_q_nonneg st (qc_bytes_nonneg _)).
  assert (0 <= prov_ptr st) by (unfold prov_ptr; lia).
  assert (0 <= prov_live st).
  { apply prov_live_nonneg. apply Forall_forall. intros b Hb.
    destruct (wk_block st (wf_blocks_ok st WF) b ltac:(unfold all_blocks; apply in_or_app; left; exact Hb)) as [Hn _]. lia. }
  pose proof (prov_quar_nonneg st).
  assert (0 <= prov_depot st).
  { unfold prov_depot. pose proof (wd_nnb_max st (wf_depot_ok st WF)) as HN. pose proof (wd_nsb_max st (wf_depot_ok st WF)) as HS.
    unfold NODEBLOCK_SIZE, STOREBLOCK_SIZE. nia. }
  pose proof (prov_l24_nonneg st). pose proof (prov_emb_nonneg st).   (* [comment removed for export] *)
  unfold prov_slots. lia.
Qed.

Definition same_but_secondary (st st' : rtstate) : Prop :=
  st_sp0 st' = st_sp0 st /\ st_pbase st' = st_pbase st /\ st_spacebeg st' = st_spacebeg st
  /\ st_regions st' = st_regions st /\ st_cache_inited st' = st_cache_inited st /\ st_cache st' = st_cache st
  /\ st_pa st' = st_pa st
  /\ st_qthread st' = st_qthread st /\ st_qglobal st' = st_qglobal st /\ st_depot st' = st_depot st
  /\ st_trs st' = st_trs st /\ st_trs0 st' = st_trs0 st /\ st_fs st' = st_fs st /\ st_hints st' = st_hints st
  /\ st_lf st' = st_lf st /\ st_t st' = st_t st /\ st_ctx st' = st_ctx st /\ st_tls st' = st_tls st
  /\ st_loose0 st' = st_loose0 st /\ st_ia_inited st' = st_ia_inited st /\ st_lb st' = st_lb st
  /\ st_apend st' = st_apend st /\ st_qpend st' = st_qpend st /\ st_qtmp st' = st_qtmp st.

(* [comment removed for export] *)
Definition secondary_fp (st : rtstate) (mb n : Z) : list (Z * Z) :=
  [(A_SECONDARY, A_SECONDARY + 624); (A_GSTATS, A_GSTATS + 40); (st_pa st, st_pa st + PTRARR_RES_SIZE);
   (mb, mb + smapsize n); (SH mb - 4096, SH (mb + smapsize n) + 4096)]      (* [comment removed for export] *)
  ++ fp_tpage st ++ map (fun e : Z * Z => (fst e, fst e + 32)) (st_sec st).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_alloc_rel (st st' : rtstate) (n : Z) (r : Z) : Prop :=
  same_but_secondary st st' /\ st_qcur st' = st_qcur st
  /\ ( (r = 0 /\ st_sec st' = st_sec st /\ st_spend st' = st_spend st /\ st_nreserved st' = st_nreserved st)
     \/ (exists mb, r = sec_alloc_beg mb /\ ablk mb (mb + smapsize n) /\ mb mod 4096 = 0 /\ mb + smapsize n <= alloc_ceiling
            /\ st_sec st' = st_sec st ++ [(mb, n)] /\ st_spend st' = (mb, n) :: st_spend st
            /\ (st_nreserved st' = st_nreserved st \/ st_nreserved st' = st_nreserved st + 2^14)) ).

Definition sec_alloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists r,
        a0' = wz r /\ sec_alloc_rel st st' n r
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m'
        /\ (r = 0 -> rt_frame (secondary_fp st 0 0) lo (bv_unsigned sp) m m' /\ budget_ok st g st' g' 0)
        /\ (forall mb, r = sec_alloc_beg mb -> ablk mb (mb + smapsize n) ->
              rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m'
              /\ budget_ok st g st' g' (SEC_ALLOC_COST n + SEC_SLOT_TAX)
              (* [comment removed for export] *)
              /\ rw_cells asegs m' (SH mb) (zcells (zrep SV_HEAP_LEFT_RZ 512))
              /\ rw_cells asegs m' (SH (sec_alloc_beg mb + rounded8 n + 4096)) (zcells (zrep SV_HEAP_LEFT_RZ ((mb + smapsize n - (sec_alloc_beg mb + rounded8 n + 4096)) / 8)))
              /\ sec_win g' mb n)                                            (* [comment removed for export] *)
        /\ gmono g g').

Definition large_alloc_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g ->
  0 <= n -> bprim n = false -> needed n <= 2^40 ->
  a0 = wz A_SECONDARY -> a1 = wz A_GSTATS -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  SEC_ALLOC_COST n + SEC_SLOT_TAX + rt_prov st <= g_res g ->          (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ALARGE_ALLOC_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (sec_alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ALARGE_ALLOC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Definition sec_alloc2_post_null (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' =>
        a0' = wz 0 /\ st' = st
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m'
        /\ rt_frame (secondary_fp st 0 0) lo (bv_unsigned sp) m m' /\ budget_ok st g st' g' 0
        /\ gmono g g').
Definition sec_alloc2_post_blk (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists mb,
        a0' = wz (sec_alloc_beg mb) /\ sec_alloc_rel st st' n (sec_alloc_beg mb) /\ ablk mb (mb + smapsize n)
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m'
        /\ rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m'
        /\ budget_ok st g st' g' (SEC_ALLOC_COST n + SEC_SLOT_TAX)
        /\ rw_cells asegs m' (SH mb) (zcells (zrep SV_HEAP_LEFT_RZ 512))
        /\ rw_cells asegs m' (SH (sec_alloc_beg mb + rounded8 n + 4096)) (zcells (zrep SV_HEAP_LEFT_RZ ((mb + smapsize n - (sec_alloc_beg mb + rounded8 n + 4096)) / 8)))
        /\ sec_win g' mb n
        /\ gmono g g').

Definition large_alloc_spec2 : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g ->
  0 <= n -> bprim n = false -> needed n <= 2^40 ->
  a0 = wz A_SECONDARY -> a1 = wz A_GSTATS -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  SEC_ALLOC_COST n + SEC_SLOT_TAX + rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ALARGE_ALLOC_STACK ->
  mem_inv asegs m ->
  LSCPS2 asegs (sec_alloc2_post_null ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
               (sec_alloc2_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ALARGE_ALLOC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gbb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (sec_alloc_beg mb)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (A_SECONDARY + 616, A_SECONDARY + 620)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (exists j3, rw_cells asegs m' (A_SECONDARY + 616) [W1 0; CB 3 j3])     (* [comment removed for export] *)
    /\ stk asegs m' lo (bv_unsigned sp).

Definition get_block_begin_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (mb n p lo : Z),
  RTS st m mo g ->
  In (mb, n) (st_sec st) -> sec_alloc_beg mb <= p < mb + smapsize n ->
  a0 = wz A_SECONDARY -> a1 = wz p ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AGBB_STACK ->
  mem_inv asegs m ->
  evt asegs (gbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz AGET_BLOCK_BEGIN) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_dealloc_rel (st st' : rtstate) (b : qbatch) (d : Z) (mb n : Z) : Prop :=
  same_but_secondary st st' /\ st_spend st' = st_spend st /\ st_nreserved st' = st_nreserved st
  /\ st_qcur st' = [(b, d + 1)]
  /\ Permutation (st_sec st) ((mb, n) :: st_sec st').

Definition sec_dealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (b : qbatch) (d mb n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        sec_dealloc_rel st st' b d mb n
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m'
        /\ gmono g g' /\ budget_ok st g st' g' 0).

Definition large_dealloc_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (b : qbatch) (d mb n lo : Z),
  RTS st m mo g ->
  st_qcur st = [(b, d)] -> 0 <= d < qb_count b -> nthz (qb_elems b) d (0, 0) = (sec_user mb, n) -> bprim n = false ->
  a0 = wz A_SECONDARY -> a1 = wz A_GSTATS -> a2 = wz (sec_alloc_beg mb) ->
  tp = wz ATP ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ALARGE_DEALLOC_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (sec_dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st b d mb n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ALARGE_DEALLOC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)


End CeilWrap.
End RTW_secondary_iface.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Module RTW_q_needs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface RTW_secondary_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Definition same_but_secondary_p (st st' : rtstate) : Prop :=
  st_sp0 st' = st_sp0 st /\ st_pbase st' = st_pbase st /\ st_spacebeg st' = st_spacebeg st
  /\ st_regions st' = st_regions st /\ st_cache_inited st' = st_cache_inited st /\ st_cache st' = st_cache st
  /\ st_pa st' = st_pa st /\ st_nreserved st' = st_nreserved st
  /\ st_qthread st' = st_qthread st /\ st_qglobal st' = st_qglobal st /\ st_depot st' = st_depot st
  /\ st_trs st' = st_trs st /\ st_trs0 st' = st_trs0 st /\ st_fs st' = st_fs st /\ st_hints st' = st_hints st
  /\ st_lf st' = st_lf st /\ st_t st' = st_t st /\ st_ctx st' = st_ctx st /\ st_tls st' = st_tls st
  /\ st_loose0 st' = st_loose0 st /\ st_ia_inited st' = st_ia_inited st /\ st_lb st' = st_lb st
  /\ st_apend st' = st_apend st /\ st_spend st' = st_spend st /\ st_qtmp st' = st_qtmp st /\ st_qcur st' = st_qcur st.

Definition sec_dealloc_pend_rel (st st' : rtstate) (A n mb : Z) : Prop :=
  same_but_secondary_p st st'
  /\ st_qpend st' = remove_first ck_eqb (A, n) (st_qpend st)
  /\ Permutation (st_sec st) ((mb, n) :: st_sec st').

Definition sec_dealloc_pend_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (A n mb lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        sec_dealloc_pend_rel st st' A n mb
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m'
        /\ gmono g g' /\ budget_ok st g st' g' 0).

(* [comment removed for export] *)
Definition large_dealloc_pend_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n mb lo : Z),
  RTS st m mo g ->
  In (A, n) (st_qpend st) -> bprim n = false -> A = sec_user mb ->
  a0 = wz A_SECONDARY -> a1 = wz A_GSTATS -> a2 = wz (sec_alloc_beg mb) ->
  tp = wz ATP ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ALARGE_DEALLOC_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (sec_dealloc_pend_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st A n mb lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ALARGE_DEALLOC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_class_fine (st : rtstate) (c : Z) : list (Z * Z) :=
  [(rbeg st c + r_mapped (rg st c), rbeg st c + KREGIONSIZE);
   (SH (rbeg st c + r_mapped (rg st c)), SH (rbeg st c) + KREGIONSIZE / 8);
   (rinfo st c, rinfo st c + 128)].
Definition primary_fp_fine (st : rtstate) (c : Z) : list (Z * Z) := fp_class_fine st c ++ fp_tpage st.

(* [comment removed for export] *)
Definition refill_ret0 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (cls lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ refill_rel st st' cls 0 /\ RTREP st' m' /\ RTWF st'
    /\ stk asegs m' lo (bv_unsigned sp) /\ rt_frame (primary_fp_fine st cls ++ fp_emb st') lo (bv_unsigned sp) m m'.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition refill_post1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (cls lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' =>
        a0' = wz 1 /\ refill_rel st st' cls 1
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ rt_frame (primary_fp_fine st cls ++ fp_emb st') lo (bv_unsigned sp) m m'   (* [comment removed for export] *)
        /\ gmono g g' /\ budget_ok st g st' g' 0).

Definition refill_spec_spin : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (cls lo : Z),
  RTS st m mo g ->
  1 <= cls <= 30 -> cch st cls = [] ->
  (* [comment removed for export] *)
  (navail st cls < nrefill cls -> r_mapped (rg st cls) + 262144 <= KFREEARRAY_OFF) ->
  a0 = wz (acache st) -> a1 = wz (pcaddr st cls) -> a2 = wz A_ALLOC -> a3 = wz cls ->
  tp = wz ATP ->
  rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  (forall ms', refill_ret0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m ms' -> evt asegs (jself asegs) ms') ->
  LSCPS asegs (refill_post1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AREFILL) fc None m (seg_rom asegs)) mo g.


End CeilWrap.
End RTW_q_needs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
Import RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pwdj_insert : forall (r : Z * Z) L1 L2,
  pwdj (L1 ++ L2) -> Forall (fun r' => snd r <= fst r' \/ snd r' <= fst r) (L1 ++ L2) -> pwdj (L1 ++ r :: L2).
Proof.
  intros r L1 L2. revert L2. induction L1 as [|x L1 IH]; intros L2 HP HF.
  - cbn. split; [exact HF| exact HP].
  - cbn in HP |- *. destruct HP as [HX HP]. apply Forall_cons_iff in HF as [H1 HF]. split.
    + apply Forall_app in HX as [HX1 HX2]. apply Forall_app. split; [exact HX1|]. constructor; [lia| exact HX2].
    + apply IH; [exact HP| exact HF].
Qed.

Lemma index_of_app_new : forall l mb n, ~ In mb (map fst l) -> index_of (l ++ [(mb, n)]) mb = zlen l.
Proof.
  induction l as [|[b k] l IH]; intros mb n Hn; cbn.
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec b mb) as [E|NE]; [exfalso; apply Hn; left; exact E|].
    rewrite IH by (intros C; apply Hn; right; exact C). rewrite zlen_cons. reflexivity.
Qed.
Lemma index_of_app_old : forall l e x, In x (map fst l) -> index_of (l ++ [e]) x = index_of l x.
Proof.
  induction l as [|[b k] l IH]; intros e x Hx; [destruct Hx|]. cbn. destruct (Z.eqb_spec b x) as [E|NE]; [reflexivity|].
  rewrite IH; [reflexivity|]. destruct Hx as [Hx|Hx]; [cbn in Hx; congruence| exact Hx].
Qed.

Lemma NoDup_app_single : forall (l : list Z) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  intros l x ND NI. eapply Permutation_NoDup; [apply Permutation_cons_append|]. constructor; assumption.
Qed.

Lemma region_free_elim : forall maps (a n b sz : word), region_free maps a n = true -> In (b, sz) maps ->
  0 < bv_unsigned n -> 0 < bv_unsigned sz ->
  bv_unsigned a + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned sz <= bv_unsigned a.
Proof.
  intros maps a n b sz Hf Hin Hn Hs. pose proof (region_free_In maps a n b sz Hf Hin) as Ho.
  unfold iv_overlap in Ho. apply andb_false_iff in Ho as [Ho|Ho]; apply Z.ltb_ge in Ho; lia.
Qed.

Lemma asegs_reserved_sec : segments_reserved asegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x71000); (Z_to_bv 64 0xa1000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xa3000, Z_to_bv 64 0x55c000)].
Proof. vm_compute. reflexivity. Qed.
Lemma reserved_below : forall mo (b s : word), LOK asegs mo -> In (b, s) (vm_reserved (m_vmmaps mo)) ->
  bv_unsigned b + bv_unsigned s <= AIMG_HI.
Proof.
  intros mo b s HO Hin. rewrite (lok_resv _ _ HO), asegs_reserved_sec in Hin. unfold AIMG_HI.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; rewrite !unsigned_lit by lia; lia.
Qed.

Lemma n_lt_needed : forall n, 0 <= n -> n + 16 <= needed n.
Proof.
  intros n Hn. unfold needed, needed0. pose proof (usz_le_rounded8 n) as (U1 & _). pose proof (rz_size_range n) as [RZ _].
  unfold usz in U1. destruct (is_primary n); lia.
Qed.
Lemma smapsize_pos : forall n, 0 <= n -> 8192 <= smapsize n /\ smapsize n mod 4096 = 0.
Proof.
  intros n Hn. unfold smapsize, roundup. pose proof (n_lt_needed n Hn). split; [Z.div_mod_to_equations; lia|].
  rewrite Z.add_mod, Z_mod_mult, Z.mod_same by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TR.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (LB : list (Z * Z))
          (AP SP QP : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.
Hypothesis WF : RTWF st.

Section SECREG.
Variables (mb n : Z).
Hypothesis HP : bprim n = false.
Hypothesis Hn : 0 <= n.
Hypothesis Hneed : needed n <= 2^40.
Hypothesis Hal : mb mod 4096 = 0.
Hypothesis Hlo : ablk mb (mb + smapsize n).   (* [comment removed for export] *)
Hypothesis Hhi : mb + smapsize n <= CEIL.
Hypothesis FRESH : forall r, In r (rt_ranges st) -> mb + smapsize n <= fst r \/ snd r <= mb.
Hypothesis ROOM : nsec st < 2^20.

Definition grow : bool := nsec st =? a8.
Definition nres' : Z := a8 + (if grow then 2^14 else 0).
Let stR := mkRT a1 a2 a3 a4 a5 a6 a7 nres' (a9 ++ [(mb, n)]) a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP ((mb, n) :: SP) QP b4 b5.

Lemma smap_facts : 8192 <= smapsize n /\ smapsize n mod 4096 = 0 /\ n < 2^40.
Proof. pose proof (smapsize_pos n Hn) as [S1 S2]. pose proof (n_lt_needed n Hn). repeat split; try assumption. lia. Qed.

(* [comment removed for export] *)
Lemma secreg_all_blocks : all_blocks stR = all_blocks st. Proof. reflexivity. Qed.
Lemma secreg_qelems : qelems stR = qelems st. Proof. reflexivity. Qed.
Lemma secreg_qall : qall stR = qall st. Proof. reflexivity. Qed.
Lemma secreg_used : forall c, used_cptrs stR c = used_cptrs st c. Proof. reflexivity. Qed.
Lemma secreg_rg : forall c, rg stR c = rg st c. Proof. reflexivity. Qed.
Lemma secreg_cch : forall c, cch stR c = cch st c. Proof. reflexivity. Qed.
Lemma secreg_nsec : nsec stR = nsec st + 1.
Proof. unfold nsec. cbn [st_sec stR st]. rewrite zlen_app. cbn. unfold zlen. cbn. lia. Qed.
Lemma secreg_same : same_but_secondary st stR.
Proof. unfold same_but_secondary. repeat split; reflexivity. Qed.
Lemma secreg_rel : sec_alloc_rel st stR n (sec_alloc_beg mb).
Proof.
  split; [exact secreg_same|]. split; [reflexivity|]. right. exists mb.
  split; [reflexivity|]. split; [exact Hlo|]. split; [exact Hal|]. split; [rewrite CEIL_eq; exact Hhi|].
  split; [reflexivity|]. split; [reflexivity|]. cbn [st_nreserved st stR]. unfold nres'. destruct grow; lia.
Qed.

(* [comment removed for export] *)
Lemma mb_new : ~ In mb (map fst a9).
Proof.
  intros Hin. apply in_map_iff in Hin as ([b k] & E & Hin). cbn in E. subst b.
  destruct (FRESH (mb, mb + smapsize k)) as [D|D].
  - unfold rt_ranges. cbn [st_pbase st_pa st_loose0 st_sec st_depot st]. do 2 right. rewrite !in_app_iff. right; left.
    apply in_map_iff. exists (mb, k). auto.
  - cbn [fst] in D. pose proof smap_facts. lia.
  - cbn [snd] in D. destruct (ws_entry st (wf_sec_ok st WF) _ Hin) as (_ & K & _). cbn [snd] in K.
    pose proof (smapsize_pos k ltac:(lia)). lia.
Qed.
Lemma mbn_new_sec : ~ In (mb, n) a9.
Proof. intros C. apply mb_new. apply in_map_iff. exists (mb, n). auto. Qed.
Lemma mbn_new_spend : ~ In (mb, n) SP.
Proof. intros C. apply mbn_new_sec. exact (proj1 (ws_spend st (wf_sec_ok st WF) _ C)). Qed.
Lemma user_new : ~ In (sec_user mb, n) (all_blocks st).
Proof.
  intros C. pose proof (wk_block st (wf_blocks_ok st WF) _ C) as (_ & _ & _ & HS). cbn [fst snd] in HS.
  specialize (HS HP). apply mbn_new_sec. replace mb with (b_map_beg (sec_user mb)) at 1; [exact HS|].
  unfold b_map_beg, sec_user. lia.
Qed.

(* [comment removed for export] *)
Lemma secreg_rt_ranges : rt_ranges stR =
  ((a2, a2 + PRIM_RES_SIZE) :: (a7, a7 + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) a21 ++ map (fun e => (fst e, fst e + smapsize (snd e))) a9)
  ++ (mb, mb + smapsize n) :: (map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks a12) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks a12)).
Proof.
  unfold rt_ranges. cbn [st_pbase st_pa st_loose0 st_sec st_depot stR]. rewrite ?map_app. cbn [map app fst snd].
  rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed.
Lemma rt_ranges_split : rt_ranges st =
  ((a2, a2 + PRIM_RES_SIZE) :: (a7, a7 + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) a21 ++ map (fun e => (fst e, fst e + smapsize (snd e))) a9)
  ++ (map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks a12) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks a12)).
Proof. unfold rt_ranges. cbn [st_pbase st_pa st_loose0 st_sec st_depot st]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. reflexivity. Qed.
Lemma secreg_In_ranges : forall r, In r (rt_ranges stR) <-> r = (mb, mb + smapsize n) \/ In r (rt_ranges st).
Proof.
  intros r. rewrite secreg_rt_ranges, rt_ranges_split. split; intros H.
  - apply in_app_iff in H as [H|[H|H]]; [right; apply in_or_app; left; exact H| left; symmetry; exact H| right; apply in_or_app; right; exact H].
  - destruct H as [->|H]; [apply in_or_app; right; left; reflexivity|].
    apply in_app_iff in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H].
Qed.

Lemma RTWF_secreg : RTWF stR.
Proof.
  pose proof smap_facts as (SM1 & SM2 & SM3). pose proof mb_new as NEW.
  pose proof (wf_base_ok st WF) as WB. pose proof (wf_sec_ok st WF) as WS.
  constructor.
  - (* [comment removed for export] *) destruct WB; constructor; try assumption.
    + intros r Hr. apply secreg_In_ranges in Hr as [->|Hr]; [cbn [fst snd]; unfold CEIL in *; blia| exact (wb_ranges r Hr)].
    + rewrite secreg_rt_ranges. apply pwdj_insert; [rewrite <- rt_ranges_split; exact wb_pwdj|].
      rewrite <- rt_ranges_split. apply Forall_forall. intros r Hr. cbn [fst snd]. destruct (FRESH r Hr); lia.
    + cbn [st_nreserved stR]. unfold nres', grow. cbn [st_nreserved st] in wb_nres. unfold PTRARR_RES_SIZE in *.
      destruct (Z.eqb_spec (nsec st) a8) as [E|NE]; [| rewrite Z.add_0_r; exact wb_nres].
      split; [lia|]. split; [rewrite Z.add_mod, (proj1 (proj2 wb_nres)) by lia; reflexivity|].
      assert (a8 <= 2^20 - 2^14) by (Z.div_mod_to_equations; (cut_on [ROOM wb_sp0 wb_nres E H H4] nia)). lia.
  - (* [comment removed for export] *) intros c Hc. destruct (wf_class_ok st WF c Hc); constructor; assumption.
  - (* [comment removed for export] *) pose proof (wf_blocks_ok st WF) as WK. constructor; [| exact (wk_nodup st WK)].
    intros b Hb. pose proof (wk_block st WK b Hb) as (K1 & K2 & K3 & K4). unfold wf_block. split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
    intros HF. cbn [st_sec stR]. apply in_or_app. left. exact (K4 HF).
  - (* [comment removed for export] *) destruct WS; constructor.
    + cbn [st_sec stR]. rewrite map_app. cbn [map fst]. apply NoDup_app_single; [exact ws_nodup| exact NEW].
    + rewrite secreg_nsec. cbn [st_nreserved stR]. unfold nres', grow. cbn [st_nreserved st] in ws_nres.
      destruct (Z.eqb_spec (nsec st) a8); lia.
    + intros e He. cbn [st_sec st_spend stR] in He |- *. apply in_app_iff in He as [He|[<-|[]]].
      * destruct (ws_entry e He) as (E1 & E2 & E3 & E4). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
        destruct E4 as [E4|E4]; [left; exact E4| right; right; exact E4].
      * cbn [fst snd]. split; [exact HP|]. split; [lia|]. split; [exact Hal|]. right. left. reflexivity.
    + intros e He. cbn [st_sec st_spend stR] in He |- *. destruct He as [<-|He].
      * split; [apply in_or_app; right; left; reflexivity| exact user_new].
      * destruct (ws_spend e He) as [T1 T2]. split; [apply in_or_app; left; exact T1| exact T2].
    + cbn [st_spend stR]. constructor; [exact mbn_new_spend| exact ws_spend_nodup].
  - destruct (wf_quar_ok st WF); constructor; assumption.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

(* [comment removed for export] *)
Lemma rt_prov_secreg : rt_prov stR + (if grow then PTRC else 0) <= rt_prov st + SEC_SLOT_TAX + 16.
Proof.
  assert (E1 : prov_classes stR = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stR = prov_nb st) by reflexivity.
  assert (E3 : prov_q stR = prov_q st) by reflexivity.
  assert (E5 : prov_live stR = prov_live st) by reflexivity.
  assert (E6 : prov_quar stR = prov_quar st) by reflexivity.
  assert (E7 : prov_depot stR = prov_depot st) by reflexivity.
  assert (E8 : prov_slots stR = prov_slots st + SEC_SLOT_TAX) by (unfold prov_slots; rewrite secreg_nsec; lia).
  assert (E9 : prov_l24 stR = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb stR = prov_emb st) by reflexivity.
  assert (E4 : prov_ptr stR + (if grow then PTRC else 0) <= prov_ptr st + 16).
  { unfold prov_ptr. cbn [st_nreserved stR st]. rewrite secreg_nsec. unfold nres', grow.
    pose proof (ws_nres st (wf_sec_ok st WF)) as NR. cbn [st_nreserved st] in NR.
    destruct (Z.eqb_spec (nsec st) a8) as [E|NE]; unfold PTRC; lia. }
  unfold rt_prov. rewrite E1, E2, E3, E5, E6, E7, E8, E9. lia.
Qed.

(* [comment removed for export] *)
Lemma sec_index_new : sec_index stR mb = nsec st.
Proof. unfold sec_index, nsec. cbn [st_sec stR st]. apply index_of_app_new. exact mb_new. Qed.
Lemma sec_index_old : forall x, In x (map fst a9) -> sec_index stR x = sec_index st x.
Proof. intros x Hx. unfold sec_index. cbn [st_sec stR st]. apply index_of_app_old. exact Hx. Qed.
Lemma sec_nth_old : forall i, 0 <= i < nsec st -> nthz (st_sec stR) i (0,0) = nthz (st_sec st) i (0,0).
Proof. intros i Hi. cbn [st_sec stR st]. unfold nthz. destruct (i <? 0) eqn:E; [reflexivity|]. apply app_nth1. unfold nsec, zlen in Hi. cbn [st_sec st] in Hi. lia. Qed.
Lemma sec_nth_new : nthz (st_sec stR) (nsec st) (0,0) = (mb, n).
Proof.
  cbn [st_sec stR st]. unfold nthz, nsec, zlen. cbn [st_sec st]. destruct (Z.of_nat (length a9) <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite Nat2Z.id. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma secreg_rt_loose : forall e, In e (rt_loose stR) <-> e = (mb, smapsize n) \/ In e (rt_loose st).
Proof.
  intros e. unfold rt_loose. cbn [st_loose0 st_sec st_depot stR st]. rewrite map_app. cbn [map fst snd]. split; intros H.
  - rewrite !in_app_iff in H. cbn [In] in H. rewrite !in_app_iff.
    destruct H as [H|[[H|[H|[]]]|[H|H]]]; [right; tauto| right; tauto| left; symmetry; exact H| right; tauto| right; tauto].
  - rewrite !in_app_iff. cbn [In]. rewrite !in_app_iff in H. destruct H as [->|[H|[H|[H|H]]]]; tauto.
Qed.

Lemma RTMODEL_secreg : forall mo, RTMODEL st mo -> mb + smapsize n <= 2^64 ->
  sec_plain mo mb (smapsize n) ->                      (* [comment removed for export] *)
  RTMODEL stR (mm_add_map (wz mb) (wz (smapsize n)) mo).
Proof.
  intros mo (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9) HB PL. pose proof smap_facts as (SM1 & _).
  assert (U1 : bv_unsigned (wz mb) = mb) by (unfold wz; apply unsigned_lit; unfold KHIGHMEM_BEG in *; blia).
  assert (U2 : bv_unsigned (wz (smapsize n)) = smapsize n) by (unfold wz; apply unsigned_lit; unfold KHIGHMEM_BEG in *; blia).
  unfold RTMODEL. rewrite mm_add_map_vmmaps. cbn [vm_maps vm_limit st_pbase st_pa stR st].
  split; [right; exact M1|]. split; [right; exact M2|]. split; [right; exact M3|]. split; [right; exact M4|].
  split; [| split; [| split; [| split]]].
  - intros e He. apply secreg_rt_loose in He as [->|He]; [left; reflexivity| right; exact (M5 e He)].
  - right; exact M6.   (* [comment removed for export] *)
  - intros x Hx. rewrite mm_add_map_lzf. exact (M7 x Hx).
  - exact M8.
  - (* [comment removed for export] *)
    intros e He x Hx. cbn [st_sec stR] in He. unfold sec_plain in *.
    change (m_vm_lazy (mm_add_map (wz mb) (wz (smapsize n)) mo)) with (m_vm_lazy mo).
    change (vm_noaccess (m_vmmaps (mm_add_map (wz mb) (wz (smapsize n)) mo))) with (vm_noaccess (m_vmmaps mo)).
    apply in_app_iff in He as [He|[<-|[]]]; [exact (M9 e He x Hx)| cbn [fst snd] in Hx; exact (PL x Hx)].
Qed.

Lemma GWIN_secreg_map : forall m mo g, GWIN st m mo g -> GWIN stR m (mm_add_map (wz mb) (wz (smapsize n)) mo) g.
Proof. intros m mo g H x Hw Hz Hr. rewrite mm_add_map_lzf in Hz. exact (H x Hw Hz Hr). Qed.
Lemma GWIN_secreg : forall m mo g, GWIN st m mo g -> GWIN stR m mo g.
Proof. intros m mo g H. exact H. Qed.

(* [comment removed for export] *)
Section GROW.
Variable mo : Model.
Hypothesis HO : LOK asegs mo.
Let A := a7 + 8 * a8.
(* [comment removed for export] *)
Lemma grow_site_range : grow = true -> a7 <= A /\ A + PTRARR_BLOCK <= a7 + PTRARR_RES_SIZE /\ A mod 4096 = 0 /\ ablk a7 (a7 + PTRARR_RES_SIZE) /\ a7 + PTRARR_RES_SIZE <= CEIL.
Proof.
  intros HG. unfold grow in HG. apply Z.eqb_eq in HG.
  pose proof (wb_nres st (wf_base_ok st WF)) as (N1 & N2 & N3). cbn [st_nreserved st] in N1, N2, N3.
  pose proof (pa_range st WF) as (P1 & P2 & _). pose proof (wb_pa_align st (wf_base_ok st WF)) as PAL. cbn [st_pa st] in P1, P2, PAL.
  unfold A, PTRARR_BLOCK, PTRARR_RES_SIZE, CEIL in *.
  assert (a8 <= 2^20 - 2^14) by (Z.div_mod_to_equations; nia).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact P1| lia].
Qed.

Lemma secreg_fixed_site : RTMODEL st mo -> grow = true -> mmap_fixed_site mo A PTRARR_BLOCK.
Proof.
  intros HM HG. pose proof (grow_site_range HG) as (G1 & G2 & G3 & G4 & G5). pose proof HM as (_ & M2 & _).
  pose proof (ablk_img _ _ G4) as G4i. unfold AIMG_HI in G4i.
  unfold mmap_fixed_site. unfold PTRARR_BLOCK, PTRARR_RES_SIZE, KHIGHMEM_BEG, CEIL in *.
  split; [exact G3|]. split; [blia|]. split; [rewrite CEIL_eq; unfold CEIL; lia|]. split.
  - apply region_free_intro. intros b s Hin. pose proof (reserved_below mo b s HO Hin) as R. unfold AIMG_HI in R.
    unfold iv_overlap. rewrite !unsigned_lit by blia. apply andb_false_iff.
    first [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; lia].
  - unfold map_contains. apply existsb_exists. exists (wz a7, wz PTRARR_RES_SIZE). split; [exact M2|]. cbn [fst snd].
    unfold wz, PTRARR_RES_SIZE. rewrite !unsigned_lit by lia. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma lzf_commit_out : forall x : word, grow = true ->
  in_range A PTRARR_BLOCK x = false -> lzf (mm_commit (wz A) (wz PTRARR_BLOCK) mo) x = lzf mo x.
Proof.
  intros x HG Hx. pose proof (grow_site_range HG) as (G1 & G2 & G3 & G4 & G5). unfold PTRARR_BLOCK, PTRARR_RES_SIZE, KHIGHMEM_BEG, CEIL in *.
  assert (HuA : bv_unsigned (wz A) = A) by (unfold wz; apply unsigned_lit; blia).
  assert (Hun : bv_unsigned (wz 131072) = 131072) by (unfold wz; apply unsigned_lit; lia).
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  unfold lzf. rewrite mm_commit_lazy, mm_commit_na, !inzr_maps_subtract by (try assumption; rewrite ?HuA, ?Hun; lia).
  rewrite HuA, Hun. unfold in_range in Hx. rewrite Hx. cbn [negb]. rewrite !andb_true_r. reflexivity.
Qed.
Lemma lzf_commit_imp : forall x : word, grow = true -> lzf (mm_commit (wz A) (wz PTRARR_BLOCK) mo) x = true -> lzf mo x = true.
Proof.
  intros x HG H. destruct (in_range A PTRARR_BLOCK x) eqn:E; [| rewrite (lzf_commit_out x HG E) in H; exact H].
  exfalso. pose proof (grow_site_range HG) as (G1 & G2 & G3 & G4 & G5). unfold PTRARR_BLOCK, PTRARR_RES_SIZE, KHIGHMEM_BEG, CEIL in *.
  assert (HuA : bv_unsigned (wz A) = A) by (unfold wz; apply unsigned_lit; blia).
  assert (Hun : bv_unsigned (wz 131072) = 131072) by (unfold wz; apply unsigned_lit; lia).
  pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  unfold lzf in H. rewrite mm_commit_lazy, inzr_maps_subtract in H by (try assumption; rewrite ?HuA, ?Hun; lia).
  rewrite HuA, Hun in H. unfold in_range in E. rewrite E in H. cbn [negb] in H. rewrite andb_false_r in H. discriminate.
Qed.

(* [comment removed for export] *)
Lemma RTMODEL_commit_pa : forall st0, RTMODEL st0 mo -> grow = true -> RTMODEL st0 (mm_commit (wz A) (wz PTRARR_BLOCK) mo).
Proof.
  intros st0 (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9) HG. pose proof (grow_site_range HG) as (G1 & G2 & G3 & G4 & G5).
  unfold RTMODEL. rewrite mm_commit_maps. change (vm_limit (m_vmmaps (mm_commit (wz A) (wz PTRARR_BLOCK) mo))) with (vm_limit (m_vmmaps mo)).
  repeat (split; [assumption|]). split; [| split; [exact M8|]].
  - intros x Hx. rewrite lzf_commit_out; [exact (M7 x Hx)| exact HG|].
    unfold in_range. destruct (ablk_disj_band _ _ G4) as [D|D];
    unfold KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG, PTRARR_BLOCK, PTRARR_RES_SIZE, CEIL in *;
    apply andb_false_iff; [right; apply Z.ltb_ge; lia| left; apply Z.leb_gt; lia].
  - (* [comment removed for export] *)
    intros e He x Hx. destruct (M9 e He x Hx) as [P1 P2].
    unfold PTRARR_BLOCK, PTRARR_RES_SIZE, KHIGHMEM_BEG, CEIL in *.
    assert (HuA : bv_unsigned (wz A) = A) by (unfold wz; apply unsigned_lit; blia).
    assert (Hun : bv_unsigned (wz 131072) = 131072) by (unfold wz; apply unsigned_lit; lia).
    pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
    rewrite mm_commit_lazy, mm_commit_na, !inzr_maps_subtract by (try assumption; rewrite ?HuA, ?Hun; lia).
    rewrite P1, P2. split; reflexivity.
Qed.
Lemma GWIN_commit_pa : forall st0 m g, GWIN st0 m mo g -> grow = true -> GWIN st0 m (mm_commit (wz A) (wz PTRARR_BLOCK) mo) g.
Proof. intros st0 m g H HG x Hw Hz Hr. apply (H x Hw); [| exact Hr]. apply lzf_commit_imp; [exact HG| exact Hz]. Qed.
End GROW.
End SECREG.
End TR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rt_range_entry : forall st mo r, RTMODEL st mo -> In r (rt_ranges st) ->
  exists lo sz, r = (lo, lo + sz) /\ In (wz lo, wz sz) (vm_maps (m_vmmaps mo)).
Proof.
  intros st mo r (M1 & M2 & M3 & M4 & M5 & _) Hr. rewrite rt_ranges_tail in Hr.
  destruct Hr as [<-|[<-|Hr]]; [exists (st_pbase st), PRIM_RES_SIZE; auto| exists (st_pa st), PTRARR_RES_SIZE; auto|].
  cbn [app] in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|[Hr|Hr]]]; apply in_map_iff in Hr.
  - destruct Hr as ([b k] & <- & Hin). exists b, k. split; [reflexivity|]. apply (M5 (b, k)). unfold rt_loose. apply in_or_app. left. exact Hin.
  - destruct Hr as ([b k] & <- & Hin). exists b, (smapsize k). split; [reflexivity|]. apply (M5 (b, smapsize k)). unfold rt_loose.
    apply in_or_app; right; apply in_or_app; left. apply in_map_iff. exists (b, k). auto.
  - destruct Hr as (b & <- & Hin). exists b, NODEBLOCK_SIZE. split; [reflexivity|]. apply (M5 (b, NODEBLOCK_SIZE)). unfold rt_loose.
    rewrite !in_app_iff. right; right; left. apply in_map_iff. exists b. auto.
  - destruct Hr as (b & <- & Hin). exists b, STOREBLOCK_SIZE. split; [reflexivity|]. apply (M5 (b, STOREBLOCK_SIZE)). unfold rt_loose.
    rewrite !in_app_iff. right; right; right. apply in_map_iff. exists b. auto.
Qed.

(* [comment removed for export] *)
Theorem grant_plain : forall mo (a : word) k, LOK asegs mo -> 0 < k < 2^64 -> mmap_grant mo a k -> sec_plain mo (bv_unsigned a) k.
Proof.
  intros mo a k HO Hk (_ & _ & _ & RF) x Hx.
  rewrite region_free_app in RF. apply andb_true_iff in RF as [_ RF].
  assert (U3 : bv_unsigned (Z_to_bv 64 k : word) = k) by (apply unsigned_lit; lia).
  assert (NM : in_rangesb (vm_maps (m_vmmaps mo)) x = false).
  { destruct (in_rangesb (vm_maps (m_vmmaps mo)) x) eqn:E; [| reflexivity]. exfalso.
    apply in_rangesb_true in E as (b & sz & Hin & Hbx).
    eapply (region_free_false_of _ a (Z_to_bv 64 k) b sz x RF Hin); [rewrite U3; lia| exact Hbx]. }
  split.
  - destruct (in_rangesb (vm_noaccess (m_vmmaps mo)) x) eqn:E; [| reflexivity]. rewrite (lok_na_maps _ _ HO x E) in NM. discriminate.
  - destruct (in_rangesb (m_vm_lazy mo) x) eqn:E; [| reflexivity]. rewrite (lok_lazy_maps _ _ HO x E) in NM. discriminate.
Qed.

(* [comment removed for export] *)
Lemma sec_plain_vm : forall mo mo' mb sz, sec_plain mo mb sz ->
  vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) -> m_vm_lazy mo' = m_vm_lazy mo -> sec_plain mo' mb sz.
Proof. intros mo mo' mb sz H E1 E2 x Hx. rewrite E1, E2. exact (H x Hx). Qed.
Lemma sec_plain_add_map : forall mo a n mb sz, sec_plain mo mb sz -> sec_plain (mm_add_map a n mo) mb sz.
Proof. intros mo a n mb sz H. eapply sec_plain_vm; [exact H| reflexivity| reflexivity]. Qed.
(* [comment removed for export] *)
Lemma sec_plain_add_lazy : forall mo (a : word) k mb sz, sec_plain mo mb sz -> 0 < k < 2^64 ->
  (bv_unsigned a + k <= mb \/ mb + sz <= bv_unsigned a) -> sec_plain (mm_add_lazy a (Z_to_bv 64 k) mo) mb sz.
Proof.
  intros mo a k mb sz H Hk D x Hx. destruct (H x Hx) as [P1 P2].
  assert (U3 : bv_unsigned (Z_to_bv 64 k : word) = k) by (apply unsigned_lit; lia).
  rewrite mm_add_lazy_lazy, mm_add_lazy_vmmaps, mm_add_map_vmmaps. cbn [vm_noaccess in_rangesb existsb fst snd].
  fold (in_rangesb (m_vm_lazy mo) x). fold (in_rangesb (vm_noaccess (m_vmmaps mo)) x). rewrite P1, P2, U3.
  split; [reflexivity|]. rewrite orb_false_r. apply andb_false_iff.
  destruct D as [D|D]; [right; apply Z.ltb_ge; lia| left; apply Z.leb_gt; lia].
Qed.
(* [comment removed for export] *)
Lemma sec_plain_commit : forall mo (addr n : word) mb sz, LOK asegs mo -> sec_plain mo mb sz ->
  bv_unsigned addr + bv_unsigned n <= 2^64 -> sec_plain (mm_commit addr n mo) mb sz.
Proof.
  intros mo addr n mb sz HO H Hb x Hx. destruct (H x Hx) as [P1 P2]. pose proof (bv_unsigned_in_range 64 n).
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  rewrite mm_commit_lazy, mm_commit_na, !inzr_maps_subtract by (try assumption; lia). rewrite P1, P2. split; reflexivity.
Qed.
Lemma sec_plain_unmap : forall mo (addr n : word) mb sz, LOK asegs mo -> sec_plain mo mb sz ->
  sec_plain (mm_unmap addr n mo) mb sz.
Proof.
  intros mo addr n mb sz HO H x Hx. destruct (H x Hx) as [P1 P2]. pose proof (bv_unsigned_in_range 64 n). pose proof (bv_unsigned_in_range 64 addr).
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  rewrite mm_unmap_lazy, mm_unmap_na, !inzr_maps_subtract by (try assumption; lia). rewrite P1, P2. split; reflexivity.
Qed.
(* [comment removed for export] *)

Theorem grant_fresh : forall st mo (a : word) k, LOK asegs mo -> RTMODEL st mo -> RTWF st -> 0 < k < 2^64 ->
  mmap_grant mo a k -> forall r, In r (rt_ranges st) -> bv_unsigned a + k <= fst r \/ snd r <= bv_unsigned a.
Proof.
  intros st mo a k HO HM WF Hk (_ & _ & _ & RF) r Hr.
  pose proof (wb_ranges st (wf_base_ok st WF) r Hr) as (R1 & R2 & R3 & R4).
  destruct (rt_range_entry st mo r HM Hr) as (lo & sz & -> & Hin). cbn [fst snd] in *.
  rewrite region_free_app in RF. apply andb_true_iff in RF as [_ RF].
  assert (U1 : bv_unsigned (wz lo) = lo) by (unfold wz; apply unsigned_lit; unfold KHIGHMEM_BEG in *; blia).
  assert (U2 : bv_unsigned (wz sz) = sz) by (unfold wz; apply unsigned_lit; unfold KHIGHMEM_BEG in *; blia).
  assert (U3 : bv_unsigned (Z_to_bv 64 k : word) = k) by (apply unsigned_lit; lia).
  pose proof (region_free_elim _ a (Z_to_bv 64 k) (wz lo) (wz sz) RF Hin ltac:(rewrite U3; lia) ltac:(rewrite U2; lia)) as D.
  rewrite U1, U2, U3 in D. lia.
Qed.


End CeilWrap.
