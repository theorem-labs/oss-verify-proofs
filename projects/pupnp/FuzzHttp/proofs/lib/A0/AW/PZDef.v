(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit H_scanner_get_token H_map_str_to_int H_parse_uric H_match_A H_match_X H_presp_seg H_phdr_seg H_phdr H_pent_seg H_pent_kit H_germ_GL H_pparse_stmt.
Import ListNotations.
Open Scope Z_scope.

Notation PZ_GMAX := 64000%Z.

Section PZ.
Context {HCEIL : HasCeiling}.

Definition pz_mem (ws mws : list word) (cslack : list byte) (GL : list (Z * Z)) (m : mem) : Prop :=
  H_phdr.phdr_statics ws m cslack /\ H_pent_kit.gstA GL m
  /\ shw m FMT_CHUNK_A 7 /\ shw m FMT_CRLF_A 3 /\ H_pent_seg.pstatE PZ_GMAX m
  /\ shw m FMT_RESP_A 16 /\ shw m FMT_SSCANF_A 11
  /\ shw m FMT_REQ09_A 10 /\ shw m FMT_REQ_A 22 /\ shw m A0_FMT_SSCANF_VER 8
  /\ u64arr asegs m METHOD_TAB_A mws /\ shw m METHOD_TAB_A 176 /\ table_strings_A m mws 11
  /\ shw m 0x21ca0 6 /\ shw m 0xaea40 4 /\ shw m MARKTAB_A 10 /\ shw m RESVTAB_A 13
  /\ rw_cells asegs m 0xaad48 [C8 (wz 0xaea40)] /\ (exists gv, rw_cells asegs m 0xaea40 [C4 gv])
  /\ shw m A0_ERRNO 4.

Definition PZ_of (GL : list (Z * Z)) (m : mem) : Prop :=
  exists (ws mws : list word) (cslack : list byte),
    length ws = 66%nat
    /\ (forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64)
    /\ meth_tab_okA mws
    /\ Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL
    /\ pz_mem ws mws cslack GL m.

#[using="Type"] Lemma pp_stat_of_PZ : forall GL m (canary : word) (ev : word), PZ_of GL m ->
  rw_cells asegs m A0_ERRNO [C4 ev] -> rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  exists ws mws cslack,
    length ws = 66%nat
    /\ (forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64)
    /\ meth_tab_okA mws
    /\ Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL
    /\ pp_statA m PZ_GMAX canary ws mws cslack GL.
Proof.
  intros GL m canary ev (ws & mws & cslack & H1 & H2 & H3 & H4 & HM) EC GC SC.
  exists ws, mws, cslack. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  destruct HM as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20).
  unfold pp_statA. repeat (split; [assumption|]). split; [exists ev; exact EC|]. split; [exact A20|]. split; [exact GC| exact SC].
Qed.

Definition PZ (m : mem) : Prop := PZ_of GL_germ m.
End PZ.
