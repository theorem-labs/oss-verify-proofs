(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Abbreviation vis m lo hi := (stk bsegs m lo hi).
(* [comment removed for export] *)
Definition zcells (vs : list Z) : list cell := map (fun v => C1 (zb v)) vs.
Lemma zcells_shcells : forall vs, zcells vs = shcells vs. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Abbreviation W8 z := (C8 (wz z)).
Abbreviation W4 z := (C4 (wz z)).
Abbreviation W2 z := (C2 (wz z)).
Abbreviation W1 z := (C1 (zb z)).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section REP.
Variable st : rtstate.
Variable m : word -> option byte.

Let P := st_pbase st.
Let S := st_spacebeg st.
Let PA := st_pa st.
Let t := st_t st.
Let fs := st_fs st.
Let d := st_depot st.

(* [comment removed for export] *)
Definition R_link : Prop :=
  (forall a v, In (a, v) ALINK_WORDS -> cells_at bsegs m a [W8 v])
  /\ (forall a, A_GLOBREC_LO <= a < A_GLOBREC_HI -> m (wa a) = None).

(* [comment removed for export] *)
Definition R_emb : Prop :=
  (exists j0 j1, rw_cells bsegs m A_EMB
      [W8 (if emb_d st =? 0 then 0 else A_EMB + 32); CB 8 j0; W8 0; CB 8 j1; W8 (emb_d st); W8 (if emb_d st =? 0 then 0 else EMB_CAP); W8 (emb_sz st)])
  /\ (emb_d st <> 0 -> vis m (emb_d st) (emb_d st + EMB_CAP)).

(* [comment removed for export] *)
Definition R_consts : Prop :=
  cells_at bsegs m A_SHADOW_OFF_CELL [W8 SHADOW_OFFSET]
  /\ cells_at bsegs m A_UAR_OPTION [W4 1]
  /\ cells_at bsegs m A_AFLAGS [CB 120 (map zb aflags_bytes)]
  /\ cells_at bsegs m A_CFLAGS [CB 288 (map zb cflags_bytes)]
  /\ cells_at bsegs m A_PAGESIZE_CACHED [W8 4096]
  /\ cells_at bsegs m A_KHIGHMEMEND [W8 KHIGHMEM_END]
  /\ cells_at bsegs m A_KMIDMEMBEG [W8 0]
  /\ cells_at bsegs m A_KMIDMEMEND [W8 0]
  /\ cells_at bsegs m A_ASAN_INITED [W1 1; W1 1; W1 0]          (* [comment removed for export] *)
  /\ cells_at bsegs m A_MCS [W4 30]
  /\ cells_at bsegs m A_CAN_POISON [W1 1]
  /\ cells_at bsegs m A_TSD_KEY_INITED [W1 1]
  /\ cells_at bsegs m A_TSD_KEY [W4 0]
  /\ cells_at bsegs m A_MAY_RETURN_NULL [W1 1; W1 0]             (* [comment removed for export] *)
  /\ (exists oom : byte, rw_cells bsegs m A_ALLOC_OOM [C1 oom]) (* [comment removed for export] *)
  /\ cells_at bsegs m A_DYING [W4 0]
  /\ cells_at bsegs m A_VERBOSITY [W4 0]
  /\ cells_at bsegs m A_MFHOOKS (repeat (W8 0) 10)
  /\ cells_at bsegs m A_LSAN_DISABLE [W4 0]
  /\ rw_cells bsegs m A_IA_INITED [W1 (if st_ia_inited st then 1 else 0); W1 0; W1 0; W1 0]   (* [comment removed for export] *)
  /\ cells_at bsegs m AHOOKS [W8 AMALLOC; W8 AFREE; W8 AREALLOC]        (* [comment removed for export] *)
  /\ cells_at bsegs m A_LIBC_PAGESIZE [W8 4096]                          (* [comment removed for export] *)
  /\ rw_cells bsegs m A_MU_GLOBALS [W8 0]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m A_GLOBALS_REGD [W8 1]                                (* [comment removed for export] *)
  /\ cells_at bsegs m A_TPCG_INITED [W1 0]                                 (* [comment removed for export] *)
  /\ cells_at bsegs m A_TOOLNAME [W8 A_ASAN_STR]                            (* [comment removed for export] *)
  /\ cells_at bsegs m A_PRINTF_CB [W8 A_EMB_CB]
  /\ R_emb.                                                                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition R_alloc : Prop :=
  (exists j1 j2 j3, rw_cells bsegs m A_ALLOC
      [W8 P; W8 PRIM_RES_SIZE; CB 16 j1; W8 S; W4 (2^32 - 1); CB 4 j2; W8 (S + KSPACESIZE); W1 0; CB 7 j3])
  /\ (exists j1 j2 j3, rw_cells bsegs m A_SECONDARY
      [W8 4096; W8 PA; W8 PA; W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st);
       CB 552 j2; W1 0; CB 7 j3])
  /\ (exists j, rw_cells bsegs m A_GSTATS [CB 40 j])
  /\ (exists j1 j2 j3 j4, rw_cells bsegs m A_QUAR
      [CB 64 j1; W8 QUAR_MAX_SIZE; W8 QUAR_MIN_SIZE; W8 QUAR_MAX_CACHE; CB 64 j2; W1 0; W1 0; CB 6 j3;
       W8 (zlen (st_qglobal st)); W8 (qc_first (st_qglobal st)); W8 (qc_last (st_qglobal st)); W8 (qc_bytes (st_qglobal st));
       CB 64 j4])
  /\ cells_at bsegs m A_MAXUSERSZ [W8 (2^40); W2 16; W2 2048; W1 1].

(* [comment removed for export] *)
Definition rinfo_cells (c : Z) (jr : list byte) (je : list byte) (js : list byte) : list cell :=
  let r := rg st c in
  [W8 0; W8 0; W8 (num_freed st c); W8 (r_mapped_fa r); W8 (r_allocated r); W8 0; W8 (r_mapped r); W8 0;
   CB 4 jr; W1 (if r_exhausted r then 1 else 0); CB 3 je; CB 56 js].
Definition R_rinfo : Prop :=
  vis m (ris st) (ris st + 4096)
  /\ forall c, 0 <= c < KNUMCLASSES -> exists jr je js, rw_cells bsegs m (rinfo st c) (rinfo_cells c jr je js).

(* [comment removed for export] *)
Definition R_regions : Prop :=
  forall c, 0 <= c < KNUMCLASSES ->
    let r := rg st c in
    vis m (rbeg st c) (rbeg st c + r_mapped r)
    /\ vis m (SH (rbeg st c)) (SH (rbeg st c) + r_mapped r / 8)
    /\ vis m (fabeg st c) (fabeg st c + r_mapped_fa r)
    /\ vis m (SH (fabeg st c)) (SH (fabeg st c) + r_mapped_fa r / 8)
    /\ (forall i, 0 <= i < num_freed st c -> rw_cells bsegs m (fabeg st c + 4 * i) [W4 (nthz (r_fa r) i 0)])
    /\ rw_cells bsegs m (SH (rbeg st c + r_allocated r)) (zcells (zrep SV_HEAP_LEFT_RZ ((r_mapped r - r_allocated r) / 8))).

(* [comment removed for export] *)
Definition R_avail : Prop :=
  forall c k, 0 <= c < KNUMCLASSES -> In k (avail_cptrs st c ++ apend_cptrs st c) ->
    rw_cells bsegs m (SH (cptr_addr st c k)) (zcells (sh_avail c)).

(* [comment removed for export] *)
Definition R_cache : Prop :=
  forall c, 0 <= c < KNUMCLASSES ->
    rw_cells bsegs m (pcaddr st c) [W4 (zlen (cch st c)); W4 (pc_max_count st c); W8 (pc_class_size st c)]
    /\ (forall i, 0 <= i < zlen (cch st c) -> rw_cells bsegs m (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)]).

(* [comment removed for export] *)
Definition R_thread : Prop :=
  vis m t (t + 4096)
  /\ (exists j1 j2 j3 j4 j5,
        rw_cells bsegs m t [W8 (st_ctx st); W8 (ASTACK_TOP (st_sp0 st)); W8 (ASTACK_BOTTOM (st_sp0 st)); CB 16 j1;
                            W1 0; CB 7 j2; C8 j3; C8 j4; C8 j5; W8 fs])
  /\ rw_cells bsegs m (qcache_t st) [W8 (zlen (st_qthread st)); W8 (qc_first (st_qthread st)); W8 (qc_last (st_qthread st));
                                     W8 (qc_bytes (st_qthread st))]
  /\ rw_cells bsegs m (t + T_UNWINDING) [W1 0]
  /\ rw_cells bsegs m (st_ctx st + CTX_TID) [W4 0]
  /\ rw_cells bsegs m (st_ctx st + CTX_THREAD) [W8 t]
  /\ cells_at bsegs m A_TSD_PTR [W8 A_TSD_MAIN]
  /\ cells_at bsegs m A_TSD_MAIN [W8 (st_ctx st)]
  /\ cells_at bsegs m A_DTV_PTR [W8 A_DTV]
  /\ cells_at bsegs m (A_DTV + 8 * A_TLSMOD) [W8 A_TLSBASE]
  /\ cells_at bsegs m A_FSTLS_CELL [W8 fs]
  /\ cells_at bsegs m (ATP + A_DTLS_OFF) [W8 (tl_dtls_block (st_tls st))]
  /\ cells_at bsegs m (tl_dtls_block (st_tls st) + 16 * A_TLSMOD + 8) [W8 (tl_dtls_w (st_tls st))].

(* [comment removed for export] *)
Definition hdr_cells (state : Z) (n : Z) (b1 : byte) (cid : word) : list cell :=
  [W1 state; C1 b1; W2 (size_hi n); W4 (size_lo n); C8 cid].
Definition R_bighdr (A n : Z) : Prop :=
  16 < rz_size n -> rw_cells bsegs m (b_alloc_beg A n) [W8 KALLOCBEG_MAGIC; W8 (b_chunk_beg A)].
Definition R_secmap (mb n : Z) : Prop :=
  vis m mb (mb + smapsize n)
  /\ vis m (SH mb) (SH mb + smapsize n / 8)
  /\ rw_cells bsegs m mb [W8 mb; W8 (smapsize n); W8 (needed n); W8 (sec_index st mb)].
Definition R_sechdr (A n : Z) : Prop := bprim n = false -> R_secmap (b_map_beg A) n.
(* [comment removed for export] *)
Inductive bmode := BLive | BQuar | BPend.   (* [comment removed for export] *)
Definition bm_state (md : bmode) : Z := match md with BLive => hdr_state_live | _ => hdr_state_quar end.
Definition R_bshadow (md : bmode) (A n : Z) : Prop :=
  match md, bprim n with
  | BLive, true => rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_live n))
  | BQuar, true => rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_quar n))
  | BPend, true => vis m (SH (b_lo A n)) (SH (b_lo A n) + sh_tot n)       (* [comment removed for export] *)
  | BLive, false => rw_cells bsegs m (SH A) (zcells (shadow_enc (usz n)))
  | _, false => True
  end.
Definition R_block (md : bmode) (A n : Z) : Prop :=
  (exists b1 cid, rw_cells bsegs m (b_chunk_beg A) (hdr_cells (bm_state md) n b1 cid) /\ hdr_b1_ok (bv_unsigned b1))
  /\ R_bighdr A n /\ R_sechdr A n
  /\ vis m (b_lo A n) (b_hi A n)
  /\ R_bshadow md A n.
Definition R_live : Prop := forall A n, In (A, n) (st_lb st) -> R_block BLive A n.

(* [comment removed for export] *)
Definition R_quar : Prop :=
  (forall A n, In (A, n) (qelems st) -> R_block BQuar A n)
  /\ (forall A n, In (A, n) (st_qpend st) -> R_block BPend A n).

(* [comment removed for export] *)
Definition R_qslots (b : qbatch) : Prop :=
  vis m (qb_addr b) (qb_addr b + QBATCH_SIZE)
  /\ (forall i, 0 <= i < qb_count b -> rw_cells bsegs m (qb_addr b + 24 + 8 * i) [W8 (b_chunk_beg (fst (nthz (qb_elems b) i (0,0))))])
  /\ rw_cells bsegs m (SH (qb_addr b)) (zcells (sh_avail 24)).
Fixpoint R_qlist (q : list qbatch) : Prop :=
  match q with
  | [] => True
  | b :: q' => rw_cells bsegs m (qb_addr b) [W8 (qc_first q'); W8 (qb_size b); W8 (qb_count b)] /\ R_qslots b /\ R_qlist q'
  end.
Definition R_batches : Prop :=
  R_qlist (st_qthread st) /\ R_qlist (st_qglobal st) /\ R_qlist (st_qtmp st)
  /\ (forall bd, In bd (st_qcur st) ->      (* [comment removed for export] *)
        (exists nx, rw_cells bsegs m (qb_addr (fst bd)) [W8 nx; W8 (qb_size (fst bd)); W8 (qb_count (fst bd))]) /\ R_qslots (fst bd)).

(* [comment removed for export] *)
Definition R_ptrarr : Prop :=
  vis m PA (PA + 8 * st_nreserved st)
  /\ (forall i, 0 <= i < nsec st -> rw_cells bsegs m (PA + 8 * i) [W8 (fst (nthz (st_sec st) i (0,0)))])
  /\ (forall e, In e (st_spend st) -> R_secmap (fst e) (snd e)).

(* [comment removed for export] *)
Definition R_depot : Prop :=
  (forall i, 0 <= i < 2^DEPOT_TAB_LOG -> rw_cells bsegs m (A_DEPOT + 4 * i) [W4 (d_tab d i)])
  /\ (exists j, rw_cells bsegs m A_DEPOT_NIDS [W4 (d_U d); CB 4 j; W1 0; W1 0; W1 0; W1 0])   (* [comment removed for export] *)
  /\ (forall k, 0 <= k < 2^15 -> rw_cells bsegs m (A_DEPOT_MAP1 + 8 * k) [W8 (nthz (d_nblocks d) k 0)])
  /\ (forall b, In b (d_nblocks d) -> vis m b (b + NODEBLOCK_SIZE))
  /\ (forall id, 1 <= id <= d_U d ->
        rw_cells bsegs m (dnode_addr d id) [W8 (dn_hash (dnode d id)); W4 (dn_link (dnode d id)); W4 (dn_store (dnode d id))])
  /\ rw_cells bsegs m A_STACKSTORE [W8 (d_T d); W8 (STOREBLOCK_SIZE * d_nsb d)]
  /\ (forall b, 0 <= b < SSTORE_NBLOCKS -> exists j1,
        rw_cells bsegs m (A_STACKSTORE + 16 + 16 * b) [W8 (nthz (d_sblocks d) b 0); CB 4 j1; W1 0; W1 0; W1 0; W1 0])
     (* [comment removed for export] *)
  /\ (forall b, In b (d_sblocks d) -> vis m b (b + STOREBLOCK_SIZE)).

(* [comment removed for export] *)
Definition R_fs : Prop :=
  vis m fs (fs + FS_TOTAL)
  /\ vis m (SH (fs + FS_FRAMES_OFF)) (SH (fs + FS_TOTAL))
  /\ (forall k, 0 <= k < 11 -> rw_cells bsegs m (fs + 8 * k) [W8 (fhint st k)])
  /\ rw_cells bsegs m (fs + 88) [W8 FS_LOG]
  /\ rw_cells bsegs m (fs + 96) [W1 0]
  /\ (forall k pos, 0 <= k < 11 -> 0 <= pos < fcap k -> rw_cells bsegs m (fflag_addr fs k pos) [W1 (flag_val st k pos)])
  /\ (forall F k, In (F, k) (st_lf st) -> cells_at bsegs m (F + fsz k - 8) [W8 (fflag_addr fs k (fpos st F k))]).

(* [comment removed for export] *)
Definition R_ia : Prop :=
  forall i, 0 <= i < 2^15 -> rw_cells bsegs m (A_IA_MAP1 + 8 * i) [W8 0].

(* [comment removed for export] *)
Definition R_lowshadow : Prop :=
  forall g, SH AIMG_LO <= g < SH AIMG_HI -> rw_cells bsegs m g [W1 (alowsh g)].

End REP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record RTREP (st : rtstate) (m : word -> option byte) : Prop := mkRTREP {
  rr_link : R_link m;
  rr_consts : R_consts st m;
  rr_alloc : R_alloc st m;
  rr_rinfo : R_rinfo st m;
  rr_regions : R_regions st m;
  rr_avail : R_avail st m;
  rr_cache : R_cache st m;
  rr_thread : R_thread st m;
  rr_live : R_live st m;
  rr_quar : R_quar st m;
  rr_batches : R_batches st m;
  rr_ptrarr : R_ptrarr st m;
  rr_depot : R_depot st m;
  rr_fs : R_fs st m;
  rr_ia : R_ia m;
  rr_lowshadow : R_lowshadow m }.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zin (lo sz : Z) (L : list (word * word)) : Prop := In (wz lo, wz sz) L.
(* [comment removed for export] *)
Definition rt_loose (st : rtstate) : list (Z * Z) :=
  st_loose0 st
  ++ map (fun e => (fst e, smapsize (snd e))) (st_sec st)
  ++ map (fun b => (b, NODEBLOCK_SIZE)) (d_nblocks (st_depot st))
  ++ map (fun b => (b, STOREBLOCK_SIZE)) (d_sblocks (st_depot st)).

(* [comment removed for export] *)
Definition sec_plain (mo : Model) (mb sz : Z) : Prop :=
  forall x : word, mb <= bv_unsigned x < mb + sz ->
    in_rangesb (vm_noaccess (m_vmmaps mo)) x = false /\ in_rangesb (m_vm_lazy mo) x = false.

Definition RTMODEL (st : rtstate) (mo : Model) : Prop :=
  let h := m_vmmaps mo in
  (* [comment removed for export] *)
  zin (st_pbase st) PRIM_RES_SIZE (vm_maps h)
  /\ zin (st_pa st) PTRARR_RES_SIZE (vm_maps h)
  /\ zin KHIGHSHADOW_BEG HIGHSHADOW_SIZE (vm_maps h)
  /\ zin KLOWSHADOW_BEG LOWSHADOW_SIZE (vm_maps h)
  (* [comment removed for export] *)
  /\ (forall e, In e (rt_loose st) -> zin (fst e) (snd e) (vm_maps h))
  (* [comment removed for export] *)
  /\ zin KLOWSHADOW_END (KHIGHSHADOW_BEG - KLOWSHADOW_END) (vm_maps h)
  (* [comment removed for export] *)
  /\ (forall x : word,
        (KLOWSHADOW_BEG <= bv_unsigned x < KLOWSHADOW_END \/ KHIGHSHADOW_BEG <= bv_unsigned x < KHIGHMEM_BEG) ->
        lzf mo x = true)
  (* [comment removed for export] *)
  /\ vm_limit h = target_alloc_limit
  (* [comment removed for export] *)
  /\ (forall e, In e (st_sec st) -> sec_plain mo (fst e) (smapsize (snd e))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RTMODEL_vm_frame : forall st mo mo',
  RTMODEL st mo -> m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> RTMODEL st mo'.
Proof.
  intros st mo mo' H Hv Hl. unfold RTMODEL, sec_plain in *. unfold lzf in *. rewrite Hv, Hl. exact H.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Abbreviation vis m lo hi := (stk bsegs m lo hi).
Abbreviation W8 z := (C8 (wz z)).
Abbreviation W4 z := (C4 (wz z)).
Abbreviation W2 z := (C2 (wz z)).
Abbreviation W1 z := (C1 (zb z)).
