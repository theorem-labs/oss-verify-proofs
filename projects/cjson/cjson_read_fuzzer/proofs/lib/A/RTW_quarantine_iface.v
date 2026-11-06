(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition AQPUT : Z := 0x36200.          (* [comment removed for export] *)
Definition AQPUT_STACK : Z := 2816.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_but_quarantine (st st' : rtstate) : Prop :=
  st_sp0 st' = st_sp0 st /\ st_pbase st' = st_pbase st /\ st_spacebeg st' = st_spacebeg st /\ st_pa st' = st_pa st
  /\ st_depot st' = st_depot st /\ st_trs st' = st_trs st /\ st_trs0 st' = st_trs0 st
  /\ st_fs st' = st_fs st /\ st_hints st' = st_hints st /\ st_lf st' = st_lf st
  /\ st_t st' = st_t st /\ st_ctx st' = st_ctx st /\ dtls_same st st' /\ loose0_ext st st'   (* [comment removed for export] *)
  /\ st_ia_inited st' = st_ia_inited st /\ st_lb st' = st_lb st
  /\ st_apend st' = st_apend st /\ st_spend st' = st_spend st.

(* [comment removed for export] *)
Definition qput_rel (st st' : rtstate) (A n : Z) : Prop :=
  same_but_quarantine st st'
  /\ st_qpend st' = remove_first ck_eqb (A, n) (st_qpend st)
  /\ st_qtmp st' = [] /\ st_qcur st' = []
  (* [comment removed for export] *)
  /\ (forall c, 0 <= c < KNUMCLASSES -> c <> 24 -> fresh_cls st c -> fresh_cls st' c).

(* [comment removed for export] *)
Definition qput_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (A n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        qput_rel st st' A n
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'          (* [comment removed for export] *)
        /\ gmono g g' /\ budget_ok st g st' g' (fp n + cost_free)).

Definition quarantine_put_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n S lo : Z),
  RTS st m mo g ->
  In (A, n) (st_qpend st) -> st_qtmp st = [] -> st_qcur st = [] -> st_apend st = [] ->      (* [comment removed for export] *)
  a0 = wz A_QUAR -> a1 = wz (qcache_t st) -> a2 = wz (acache st) -> a3 = wz S -> a4 = wz (b_chunk_beg A) -> a5 = wz (usz n) ->
  tp = wz ATP ->
  bv_unsigned sp <= st_sp0 st ->        (* [comment removed for export] *)
  rt_prov st + (fp n + cost_free) <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AQPUT_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (qput_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st A n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AQPUT) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)


End CeilWrap.
