(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut DecTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Ltac dr_destruct H :=
  let a1 := fresh "DRunz" in let l1 := fresh "Lunz" in
  let a2 := fresh "DRcfc" in let l2 := fresh "Lcfc" in
  let a3 := fresh "DRinUse" in let l3 := fresh "LinUse" in
  let a4 := fresh "DRin16" in let l4 := fresh "Lin16" in
  let a5 := fresh "DRs2u" in let l5 := fresh "Ls2u" in
  let a6 := fresh "DRmtfa" in let l6 := fresh "Lmtfa" in
  let a7 := fresh "DRmtfb" in let l7 := fresh "Lmtfb" in
  let a8 := fresh "DRsel" in let l8 := fresh "Lsel" in
  let a9 := fresh "DRselm" in let l9 := fresh "Lselm" in
  let a10 := fresh "DRlen" in let l10 := fresh "Llen" in
  let a11 := fresh "DRlim" in let l11 := fresh "Llim" in
  let a12 := fresh "DRbase" in let l12 := fresh "Lbase" in
  let a13 := fresh "DRperm" in let l13 := fresh "Lperm" in
  let a14 := fresh "DRminl" in let l14 := fresh "Lminl" in
  cps_destruct H as ((a1 & l1) & (a2 & l2) & (a3 & l3) & (a4 & l4) & (a5 & l5) & (a6 & l6) & (a7 & l7) &
                 (a8 & l8) & (a9 & l9) & (a10 & l10) & (a11 & l11) & (a12 & l12) & (a13 & l13) & (a14 & l14));
  cbn [r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl]
    in a1, l1, a2, l2, a3, l3, a4, l4, a5, l5, a6, l6, a7, l7, a8, l8, a9, l9, a10, l10, a11, l11, a12, l12, a13, l13, a14, l14.

Ltac dr_open :=
  match goal with
  | H : hidden (drest_at _ _ _ _) |- _ => unfold hidden in H; dr_destruct H
  | H : drest_at _ _ _ _ |- _ => dr_destruct H
  end.

(* [comment removed for export] *)
Ltac dr_piece :=
  lazymatch goal with
  | |- u8arr ?sg ?m ?A _ => match goal with H : u8arr sg m A _ |- _ => exact H end
  | |- u32arr ?sg ?m ?A _ => match goal with H : u32arr sg m A _ |- _ => exact H end
  | |- Z.of_nat (length _) = _ => rewrite ?upd_length, ?repeat_length; first [ assumption | reflexivity | lia ]
  end.

Ltac dr_close :=
  lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?m _) =>
  match goal with U : u32arr sg m (?S + 68)%Z _ |- _ =>
    let DR := fresh "DR" in
    eassert (DR : drest_at sg m S (DREST _ _ _ _ _ _ _ _ _ _ _ _ _ _));
    [ unfold drest_at; cbn [r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl];
      repeat match goal with |- _ /\ _ => split end; dr_piece
    | ]
  end end.

(* [comment removed for export] *)
Ltac lit_store_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
      change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (le1_lit z); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_app_iff : forall segs m A pre post,
  rw_cells segs m A (pre ++ post) <-> rw_cells segs m A pre /\ rw_cells segs m (A + Z.of_nat (cells_size pre))%Z post.
Proof.
  intros segs m A pre post. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    rewrite (cells_bytes_length pre W1) in B2.
    rewrite Nat2Z.inj_add in WR. apply wr_at_app in WR; [|lia|lia]. destruct WR as [R1 R2].
    split; [ split; [ split; [exact W1 | exact B1] | exact R1 ] | split; [ split; [exact W2 | exact B2] | exact R2 ] ].
  - intros [[[W1 B1] R1] [[W2 B2] R2]].
    rewrite (cells_bytes_length pre W1). rewrite Nat2Z.inj_add.
    split; [ split; [ split; [exact W1 | exact W2] | split; [exact B1 | exact B2] ] |].
    apply wr_at_app; [lia|lia|]. split; [exact R1 | exact R2].
Qed.

Lemma rw_cells_CB_length : forall segs m A pre n bs post,
  rw_cells segs m A (pre ++ CB n bs :: post) -> length bs = n.
Proof.
  intros segs m A pre n bs post [[W _] _]. apply cells_wf_app in W. destruct W as [_ W]. cbn in W. destruct W as [W _]. exact W.
Qed.
End ACeilS1.


(* [comment removed for export] *)
Ltac rw_split3 H k Hmid Hpost :=
  lazymatch type of H with rw_cells ?sg ?m ?A ?cs =>
    rewrite <- (firstn_skipn k cs) in H; cbn [firstn skipn] in H;
    apply (proj1 (rw_cells_app_iff sg m A _ _)) in H;
    let H2 := fresh in
    destruct H as [H H2];
    lazymatch type of H2 with rw_cells _ _ _ (?c :: ?rest) =>
      change (c :: rest) with ([c] ++ rest) in H2;
      apply (proj1 (rw_cells_app_iff sg m _ _ _)) in H2; destruct H2 as [Hmid Hpost]
    end;
    cbn [firstn skipn cells_size csize Nat.add app] in H, Hmid, Hpost;
    repeat match goal with
    | G : context [(?a + Z.of_nat ?n)%Z] |- _ =>
        let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in G
    end
  end.

(* [comment removed for export] *)
Ltac rw_join3 H Hmid Hpost :=
  lazymatch type of Hmid with rw_cells ?sg ?m ?B [?c] =>
  lazymatch type of Hpost with rw_cells _ _ _ ?post =>
    let H2 := fresh in
    assert (H2 : rw_cells sg m B ([c] ++ post))
      by (apply (proj2 (rw_cells_app_iff sg m B [c] post)); split; [exact Hmid| cbn [cells_size csize Nat.add];
          match type of Hpost with rw_cells _ _ ?C _ => replace (B + _)%Z with C by lia end; exact Hpost]);
    clear Hmid Hpost;
    lazymatch type of H with rw_cells _ _ ?A ?pre =>
      let H3 := fresh in
      assert (H3 : rw_cells sg m A (pre ++ ([c] ++ post)))
        by (apply (proj2 (rw_cells_app_iff sg m A pre ([c] ++ post))); split; [exact H| cbn [cells_size csize Nat.add];
            replace (A + _)%Z with B by lia; exact H2]);
      clear H H2; cbn [app] in H3; rename H3 into H
    end
  end end.

(* [comment removed for export] *)
Ltac u8_store_doneA ARR i :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga (le1 ?x)) _) =>
      lazymatch type of ARR with u8arr _ _ ?A ?bs =>
        let H := fresh "ARR" in
        pose proof (u8arr_write_le1 segs mm A bs i x ARR ltac:(lia)) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga [?b]) _) =>
      lazymatch type of ARR with u8arr _ _ ?A ?bs =>
        let H := fresh "ARR" in
        pose proof (u8arr_write segs mm A bs i b ARR ltac:(lia)) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  end.
