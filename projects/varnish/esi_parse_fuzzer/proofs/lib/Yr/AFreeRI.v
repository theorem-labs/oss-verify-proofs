(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSnjd AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeB1 ATransp AFreeB3 AFreeH AFreeRS AFreeRX.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section RI.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Definition rheld : list Z := [].

  (* [comment removed for export] *)
  Definition lentry_cells (sb : Z) (v : mem) (e : qentry) : Prop :=
    hdr_repr_ LPA sb v (qe_chunk e) (qe_n e) CHUNK_QUARANTINE /\
    junk_at rsegs v (user_of sb (qe_chunk e) (qe_n e)) 8 /\
    mapped v (chunk_lo sb (qe_chunk e)) (chunk_hi sb (qe_chunk e) - chunk_lo sb (qe_chunk e)) /\
    match qe_chunk e with
    | ChP (CP c k) => bytes_at rsegs v (sh (chunk_addr sb c k)) (pshadow_quar c (qe_n e))
    | ChS (CS mb n0) => bytes_at rsegs v (sh mb) (sshadow_quar (qe_n e))
    end.

  (* [comment removed for export] *)
  Definition lbatch_cells (sb : Z) (v : mem) (a : Z) (es : list qentry) (j : nat) (sz : Z) : Prop :=
    (forall i e, (j <= i)%nat -> nth_error es i = Some e -> u64_at rsegs v (a + off_qb_batch (Z.of_nat i)) (hdr_of sb (qe_chunk e) (qe_n e))) /\
    u64_at rsegs v (a + off_qb_size) sz /\
    mapped v a kQuarantineBatchBytes.

  (* [comment removed for export] *)
  Fixpoint tmp_chain (sb : Z) (v : mem) (more : list batch) : Prop :=
    match more with
    | [] => True
    | b :: r =>
        let a := batch_addr sb b in
        rw_cells rsegs v a [C8 (wz (match r with [] => 0 | b' :: _ => batch_addr sb b' end)); C8 (wz (batch_bytes b)); C8 (wz (Z.of_nat (length (ba_entries b))))] /\
        tmp_chain sb v r
    end.
  Definition tmp_hdr (sb : Z) (v : mem) (T : Z) (more : list batch) : Prop :=
    rw_cells rsegs v T [C8 (wz (Z.of_nat (length more)));
                        C8 (wz (match more with [] => 0 | b :: _ => batch_addr sb b end));
                        C8 (wz (match more with [] => 0 | _ => batch_addr sb (last more (BA 0 [])) end));
                        C8 (wz (q_bytes more))].

  (* [comment removed for export] *)
  Record rcells (A : AState) (v : mem) (T : Z) (cur : option (batch * nat)) (more : list batch) : Prop := {
    rc_arepr : @arepr _ DepotRepL LPA AL_pasan rheld A v;
    rc_tmp : tmp_hdr (a_sb A) v T more;
    rc_chain : tmp_chain (a_sb A) v more;
    rc_more_entries : forall b e, In b more -> In e (ba_entries b) -> lentry_cells (a_sb A) v e;
    rc_more_objs : forall b, In b more -> lbatch_cells (a_sb A) v (batch_addr (a_sb A) b) (ba_entries b) 0 (batch_bytes b) /\
                                          bytes_at rsegs v (sh (batch_addr (a_sb A) b)) (pshadow_free kQuarantineBatchClass);
    rc_cur : match cur with
             | None => True
             | Some (b0, i) => (forall j e, (i <= j)%nat -> nth_error (ba_entries b0) j = Some e -> lentry_cells (a_sb A) v e) /\
                               lbatch_cells (a_sb A) v (batch_addr (a_sb A) b0) (ba_entries b0) i (batch_bytes b0) /\
                               bytes_at rsegs v (sh (batch_addr (a_sb A) b0)) (pshadow_free kQuarantineBatchClass)
             end }.

  (* [comment removed for export] *)
  Definition limbo_of (cur : option (batch * nat)) (more : list batch) : list batch :=
    match cur with None => more | Some (b0, i) => BA (ba_idx b0) (skipn i (ba_entries b0)) :: more end.

  (* [comment removed for export] *)
  Record RINV (A : AState) (m : mem) (md : Model) (T : Z) (cur : option (batch * nat)) (more : list batch) : Prop := {
    ri_wf : WFR A;
    ri_limbo : a_qlimbo A = limbo_of cur more;
    ri_cells : rcells A (aview_of (pa_hull A) m) T cur more;
    ri_hidden : hidden_repr (a_pl A) (a_reg A) (a_sec A) m;
    ri_extra : wf_extra LPA pa_site_pcs (a_pl A);
    ri_ledger : aledger_ AL_pasan (a_pl A) (a_reg A) (a_sec A) md;
    ri_minv : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md;
    ri_halted : m_halted md = None;
    ri_cover : acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md);
    ri_ceil : alloc_top (m_vmmaps md) = alloc_ceiling }.

End RI.
