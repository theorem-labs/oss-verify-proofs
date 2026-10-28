(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr MState Ceiling RunWord.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls F_strncasecmp H_memptr_cmp H_obj H_prep H_fuzz_stmt H_statics
     H_entity_read_method H_pent_A H_parse_uri_A H_UpnpPrintf H_phdr_B H_httpmsg_destroy H_pparse_stmt H_pparse_B H_fuzz_entry
     H_reql_B RMallocRep RMalloc_iface RDriver_ctx AllocInst.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.

Section P0.
Context {HGW : HasGuard} {HCEIL : HasCeiling}.

#[using="Type"] Lemma P0_layout_ok : layout_ok AI_P0.
Proof.
  constructor; cbn [ai_L AI_P0 P0L al_client_static al_img al_errno fst snd].
  - intros lo hi CS. unfold p0_client_static in CS. exists (0x2a000, 0x5d000). split; [right; left; reflexivity| cbn; lia].
  - exists (0x2a000, 0x5d000). split; [right; left; reflexivity|]. unfold RERRNO. cbn. lia.
  - pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. intros w [<-|[<-|[]]]; cbn; lia.
  - unfold RERRNO. lia.
Qed.

#[using="Type"] Lemma P0_canary_ok : canary_ok AI_P0.
Proof.
  intros s LB m HR. destruct (RHEAP_ssp s LB m HR) as [S1 S2]. unfold got_ssp, ssp_guard in S1, S2.
  split; [exact S1| eexists; exact S2].
Qed.

#[using="Type"] Lemma P0_ssp0 : forall s LB m, AllocIF.RHEAP rsegs AI_P0 s LB m ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 guard_word].
Proof. intros s LB m HR. exact (RHEAP_ssp s LB m HR). Qed.

#[using="Type"] Lemma P0_errnc : forall lo hi, al_client_static (ai_L rsegs AI_P0) lo hi -> hi <= al_errno (ai_L rsegs AI_P0) \/ al_errno (ai_L rsegs AI_P0) + 4 <= lo.
Proof. cbn [ai_L AI_P0 P0L al_client_static al_errno]. intros lo hi CS. unfold p0_client_static in CS. lia. Qed.

#[using="Type"] Lemma P0_blkwin : forall s LB m (b : block (ai_K rsegs AI_P0)), AllocIF.RHEAP rsegs AI_P0 s LB m -> In b LB -> blk_addr b + blk_size b <= 0x2a000 \/ 0x5d000 <= blk_addr b.
Proof. intros s LB m b HR HIN. exact (P0_block_img s LB m b HR HIN). Qed.

#[using="Type"] Lemma P0_static : forall X n, 0x2a000 <= X -> X + n <= 0x5d000 -> 0 < n ->
  (X + n <= RLIBC \/ RCTX + 928 <= X) -> (X + n <= RERRNO \/ RERRNO + 4 <= X) -> (X + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= X) ->
  (X + n <= RGOT_SSP \/ RGOT_SSP + 8 <= X) -> (X + n <= RVMLOCK \/ RVMLOCK + 8 <= X) ->
  exists lo hi, al_client_static (ai_L rsegs AI_P0) lo hi /\ lo <= X /\ X + n <= hi.
Proof.
  intros X n H1 H2 H3 H4 H5 H6 H7 H8. exists X, (X + n). cbn [ai_L AI_P0 P0L al_client_static]. unfold p0_client_static. repeat split; lia.
Qed.

Ltac p0_static := apply P0_static; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn; lia.

#[using="Type"] Lemma P0_strncasecmp : strncasecmp_stmt.
Proof.
  unfold strncasecmp_stmt. intros. eapply evt_mono; [eapply F_strncasecmp.strncasecmp_spec; eassumption|].
  cbv beta. intros ms' Q. exact Q.
Qed.

  Variable AC : alloc_contracts AI_P0.

  #[using="AC"] Theorem reql_P0 : reql_stmt AI_P0.
  Proof.
    eapply (H_reql_B.reql_proof AI_P0 AC P0_layout_ok); try reflexivity.
    - exact P0_canary_ok.
    - exact P0_errnc.
    - exact (P0_block_ge_4096).
    - exact (P0_block_img).
    - exact P0_strncasecmp.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
  Qed.
  Let REQL : reql_stmt AI_P0 := reql_P0.

  #[using="AC REQL"] Theorem parser_parse_P0 : parser_parse_stmt AI_P0.
  Proof.
    eapply (parser_parse_proof AI_P0 AC P0_layout_ok); try reflexivity.
    - exact P0_canary_ok.
    - exact P0_errnc.
    - exact (P0_block_ge_4096).
    - exact (P0_block_img).
    - exact P0_blkwin.
    - apply germ_spec.
    - exact P0_strncasecmp.
    - cbn. left. reflexivity.
    - cbn. right. left. reflexivity.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - p0_static.
    - exact REQL.
  Qed.

  #[using="AC REQL"] Theorem fuzz_one_P0 : fuzz_one_stmt AI_P0.
  Proof.
    eapply (fuzz_one_proof AI_P0 AC P0_layout_ok); try reflexivity.
    - intros a Ha. unfold gd_addr in Ha.
      assert (E : exists X n, (X <= a < X + n) /\ 0x2a000 <= X /\ X + n <= 0x5d000 /\ 0 < n
                /\ (X + n <= RLIBC \/ RCTX + 928 <= X) /\ (X + n <= RERRNO \/ RERRNO + 4 <= X) /\ (X + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= X)
                /\ (X + n <= RGOT_SSP \/ RGOT_SSP + 8 <= X) /\ (X + n <= RVMLOCK \/ RVMLOCK + 8 <= X)).
      { unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK.
        destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]];
          [exists 0x2b1a8, 528| exists 0x2b3b8, 176| exists 0x2b468, 16| exists 0x3b700, 12| exists 0x2a118, 16]; cbn; lia. }
      destruct E as (X & n & R & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
      destruct (P0_static X n H1 H2 H3 H4 H5 H6 H7 H8) as (lo & hi & CS & A & B2). exists lo, hi. split; [exact CS| lia].
    - exact P0_ssp0.
    - exact parser_parse_P0.
    - cbn. lia.
  Qed.
End P0.

From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require AllocRealloc2.

Theorem reql_P0_closed {HGW : HasGuard} {HCEIL : HasCeiling} : reql_stmt AI_P0.
Proof. exact (reql_P0 AllocRealloc2.AC_P0). Qed.

Theorem parser_parse_P0_closed {HGW : HasGuard} {HCEIL : HasCeiling} : parser_parse_stmt AI_P0.
Proof. exact (parser_parse_P0 AllocRealloc2.AC_P0). Qed.

Theorem fuzz_one_P0_closed {HGW : HasGuard} {HCEIL : HasCeiling} : fuzz_one_stmt AI_P0.
Proof. exact (fuzz_one_P0 AllocRealloc2.AC_P0). Qed.
