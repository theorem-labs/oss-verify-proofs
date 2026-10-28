(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface RZ_block_iface RZ_dframe_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem zd_checkcont_proof : zd_checkcont_stmt.
Proof.
  intros until expd. intros H1C RD0 RD8 RD1 RDST RSZ MI -> -> ->. unfold PZD_CHECKCONT.
  unfold dctx_h1, wz0 in *.
  assert (MU : munch [(DCTX + 29888, DCTX + 29920)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  zs. fck. zs. zs. fck.
  zs. if_cases KS; zify_cond KS.
  - zs. apply evt_done. unfold zd_checkcont_post. do 3 eexists. exists m.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    replace (dsize =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite orb_true_r. exact H1C.
  - zs. zs. zs. zs. zs. if_cases KD; zify_cond KD.
    + zs. apply evt_done. unfold zd_checkcont_post. do 3 eexists. exists m.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      replace (DST =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [orb]. exact H1C.
    + zs. zs. zs. zs. zs. zs. zs. zs.
      apply evt_done. unfold zd_checkcont_post. do 3 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      replace (DST =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (dsize =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb].
      exact H1C.
Qed.

Section DBEGIN.
  Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP DCTX : Z)
            (llt mlt oft huf pde pfx vst dend expd pcs dsz bt stg le fe : word) (ws : list word) (jhb : list byte)
            (ovd dcb dce trace gend : word) (lo : Z).
  Hypothesis PTRC : dctx_ptrs usegs m DCTX llt mlt oft huf.
  Hypothesis H1C : dctx_h1 usegs m DCTX pde pfx vst dend expd.
  Hypothesis H3C : dctx_h3 usegs m DCTX pcs dsz bt stg le fe.
  Hypothesis H5C : dctx_h5 usegs m DCTX ws.
  Hypothesis H5OK : h5_frame_ok ws.
  Hypothesis TXC : dctx_tx usegs m DCTX jhb ovd dcb dce trace.
  Hypothesis OWN : dctx_owned usegs m DCTX.
  Hypothesis GOT : rw_cells usegs m 0x36e40 [C8 gend; C8 wz0].
  Hypothesis RD0 : 4096 <= DCTX.  Hypothesis RD1 : DCTX + 95992 < 2^47.  Hypothesis RD8 : DCTX mod 8 = 0.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 64.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis DS : DCTX + 95992 <= lo \/ SP <= DCTX.
  Hypothesis GS : 0x36e40 + 16 <= lo \/ SP <= 0x36e40.
  Hypothesis GD : 0x36e40 + 16 <= DCTX \/ DCTX + 95992 <= 0x36e40.
  Hypothesis MI : mem_inv usegs m.

  Notation W := [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                 (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SP - 64, SP)].

  Lemma dbegin_body :
    evt usegs (zd_dbegin_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP DCTX ws jhb ovd dcb dce lo m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) wz0 wz0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DBEGIN) fc None m (seg_rom usegs)).
  Proof.
    unfold PZD_DBEGIN.
    destruct H5C as [H5C' H5L]. destruct OWN as [OWE OWX].
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
    destruct H5OK as (K_FMT & K_REST).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof ST as (LO0 & _ & _).
    lazymatch goal with |- evt _ ?Q _ => set (Q0 := Q) end.
    h5_open ws H5L.
    unfold wz0 in *. subst b0.
    (* [comment removed for export] *)
    destruct (stk_open usegs m (DCTX + 32) (DCTX + 29888) (DCTX + 10296) 4 OWE ltac:(lia) ltac:(lia)) as (jh & HUF0 & OWE1 & OWE2).
    destruct (stk_open usegs m (DCTX + 10296 + Z.of_nat 4) (DCTX + 29888) (DCTX + 26684) 12 OWE2 ltac:(lia) ltac:(lia)) as (jr & REP & OWE3 & OWE4).
    clear OWE OWE2.
    (* [comment removed for export] *)
    apply (rw_cells_merge usegs m (DCTX + 29976) [C8 pcs; C8 dsz] [C4 bt; C4 stg] [C4 le; C4 fe]) in H3C. cbn [app cells_size csize Nat.add cells_bytes cbytes] in H3C.
    apply (rw_cells_merge usegs m (DCTX + 29976) [C8 pcs; C8 dsz; CB 8 _] [C4 le; C4 fe] []) in H3C. cbn [app cells_size csize Nat.add cells_bytes cbytes] in H3C.
    carve_frame 48%nat ST.
    do 7 zs. do 5 zs.
    zs. if_true.
    zs. zs. fck. zs. zs. fck.
    do 7 zs. zs. rewrite sx32w_small by lia.
    do 4 zs. zs. if_true.
    do 6 zs. do 10 zs. do 10 zs. do 10 zs.
    zs. if_true.
    do 8 zs.
    release_frame FR ST SP.
    zs.
    apply (rw_cells_recell usegs _ (DCTX + 29976) _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in H3C; [| cbn; tauto | vm_compute; reflexivity].
    assert (BH : bytes_at usegs m1 (DCTX + 10296) (le4 (Z_to_bv 64 201326604))).
    { pose proof (proj2 (proj1 HUF0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    assert (BR : bytes_at usegs m1 (DCTX + 26684) (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8))).
    { pose proof (proj2 (proj1 REP)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    assert (OWE' : stk usegs m1 (DCTX + 32) (DCTX + 29888)).
    { eapply (stk_close usegs m1 (DCTX + 32) (DCTX + 29888) (DCTX + 10296) _ OWE1 HUF0); [| lia | cbn [cells_size csize Nat.add]; lia].
      cbn [cells_size csize Nat.add].
      eapply (stk_close usegs m1 _ (DCTX + 29888) (DCTX + 26684) _ OWE3 REP); [| lia | cbn [cells_size csize Nat.add]; lia].
      cbn [cells_size csize Nat.add]. exact OWE4. }
    apply evt_done. unfold Q0, zd_dbegin_post. do 14 eexists. exists m1.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_h5, dctx_tx, dctx_owned, wz0.
    split; [exact PTRC|]. split; [exact H1C|]. split; [exact H3C|]. split; [split; [exact H5C'| reflexivity]|].
    split; [exact TXC|]. split; [split; [exact OWE'| exact OWX]|]. split; [exact BH| exact BR].
  Qed.
End DBEGIN.

Theorem zd_dbegin_proof : zd_dbegin_stmt.
Proof.
  intros until lo. intros PTRC H1C H3C H5C H5OK TXC OWN GOT RD0 RD1 RD8 ST LO RSP DS GS GD MI -> -> ->.
  eapply dbegin_body; eassumption.
Qed.
Print Assumptions zd_dbegin_proof.
