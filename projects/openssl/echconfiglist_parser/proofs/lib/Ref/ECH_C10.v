(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C1_dup ECH_C10_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition PM_RA1 : Z := 0x26d2c4.    Definition PM_RA2 : Z := 0x26d2f4.
  Definition PS_RA1 : Z := 0x26d374.    Definition PS_RA2 : Z := 0x26d38c.
  Definition PK_FILE : Z := 0x33a73.     (* [comment removed for export] *)

  Definition pm_frame (j : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
    [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pm1_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s5 : word)
      (F : bvmap 5 word) (fc : bv 32) (pkt dptr lptr lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j,
      ms' = MS (mkR (Z_to_bv 64 PM_RA1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 lptr)
                   (Z_to_bv 64 0) (Z_to_bv 64 PK_FILE) (Z_to_bv 64 518) (Z_to_bv 64 0) a4 a5 a6 a7
                   (Z_to_bv 64 dptr) s3 s4 (Z_to_bv 64 pkt) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
      /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -64) (pm_frame j s5 s4 s3 s2 s1 s0 ra).

  Lemma pm_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt dptr lptr lo : Z),
      rw_cells rsegs m dptr [C8 (wz 0)] -> (dptr + 8 <= lo \/ bv_unsigned sp <= dptr) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
      evt rsegs (pm1_post sp gp tp t0 t1 t2 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s5 F fc pkt dptr lptr lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pkt) (Z_to_bv 64 dptr) (Z_to_bv 64 lptr) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_PACKET_memdup) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros DP OD ST CEIL LO MI. hcb. unfold P_PACKET_memdup, P_CRYPTO_free. unfold wz in DP.
    pose proof (word_range sp) as SPR. pose proof (rw_cells_bound _ _ _ _ DP) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 64%nat ST.
    do 19 step. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Definition pm2_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 : word)
      (F : bvmap 5 word) (fc : bv 32) (pkt cur ms len dptr lptr : Z) (j : list byte) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ( (len = 0 /\
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m1 (seg_rom rsegs))
        \/ (len <> 0 /\
         ms' = MS (mkR (Z_to_bv 64 PM_RA2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 lptr)
                      (Z_to_bv 64 cur) (Z_to_bv 64 len) (Z_to_bv 64 PK_FILE) (Z_to_bv 64 527) a4 a5 a6 a7
                      (Z_to_bv 64 dptr) (Z_to_bv 64 1) (Z_to_bv 64 len) (Z_to_bv 64 pkt) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 P_CRYPTO_memdup) fc None m1 (seg_rom rsegs)
         /\ rw_cells rsegs m1 (bv_unsigned sp + -64) (pm_frame j s5 s4 s3 s2 s1 s0 ra)) )
      /\ munch [(dptr, dptr + 8); (lptr, lptr + 8)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
      /\ rw_cells rsegs m1 pkt (pk_cells cur ms len)
      /\ rw_cells rsegs m1 dptr [C8 (wz 0)] /\ rw_cells rsegs m1 lptr [C8 (wz 0)].

  Lemma pm_seg2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s5 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt cur ms len dptr lptr oldlen : Z) (j : list byte),
      rw_cells rsegs m pkt (pk_cells cur ms len) -> bv_unsigned sp <= pkt -> 0 <= len < 2^64 ->
      rw_cells rsegs m dptr [C8 (wz 0)] -> rw_cells rsegs m lptr [C8 (wz oldlen)] -> cells_apart dptr lptr ->
      apart pkt 24 dptr 8 -> apart pkt 24 lptr 8 ->
      (dptr + 8 <= bv_unsigned sp + -64 \/ bv_unsigned sp <= dptr) -> (lptr + 8 <= bv_unsigned sp + -64 \/ bv_unsigned sp <= lptr) ->
      rw_cells rsegs m (bv_unsigned sp + -64) (pm_frame j s5 s4 s3 s2 s1 s0 ra) -> mem_inv rsegs m ->
      evt rsegs (pm2_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 F fc pkt cur ms len dptr lptr j m)
        (MS (mkR (Z_to_bv 64 PM_RA1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 lptr)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 dptr) s3 s4 (Z_to_bv 64 pkt) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PM_RA1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until j. intros PK SPK HL DP LP AP APD APL OD OL FR MI. unfold PM_RA1.
    replace (ret_pc (Z_to_bv 64 0x26d2c4)) with (Z_to_bv 64 0x26d2c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold cells_apart, apart, pk_cells, pm_frame, wz in *.
    pose proof (word_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ DP) as DB. pose proof (rw_cells_bound _ _ _ _ LP) as LBB. pose proof (rw_cells_bound _ _ _ _ PK) as PB.
    cbn [cells_size csize Nat.add] in DB, LBB, PB.
    pose proof (munch_refl [(dptr, dptr + 8); (lptr, lptr + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    st1. step. st1. step.
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      do 10 step. apply evt_done. eexists. split; [left; split; [| reflexivity]|].
      { revert K0. rewrite ?unsigned_lit by lia. lia. }
      repeat (split; [assumption|]). assumption.
    - do 7 step. apply evt_done. eexists. split; [right; split; [| split; [reflexivity| eassumption]]|].
      { revert K0. rewrite ?unsigned_lit by lia. lia. }
      repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_seg3 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt len dptr lptr D : Z) (j : list byte),
      0 < D < 2^64 -> 0 <= len < 2^64 ->
      rw_cells rsegs m dptr [C8 (wz 0)] -> rw_cells rsegs m lptr [C8 (wz 0)] -> cells_apart dptr lptr ->
      (dptr + 8 <= bv_unsigned sp + -64 \/ bv_unsigned sp <= dptr) -> (lptr + 8 <= bv_unsigned sp + -64 \/ bv_unsigned sp <= lptr) ->
      rw_cells rsegs m (bv_unsigned sp + -64) (pm_frame j s5 s4 s3 s2 s1 s0 ra) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m1 (seg_rom rsegs)
                   /\ munch [(dptr, dptr + 8); (lptr, lptr + 8)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
                   /\ rw_cells rsegs m1 dptr [C8 (wz D)] /\ rw_cells rsegs m1 lptr [C8 (wz len)])
        (MS (mkR (Z_to_bv 64 PM_RA2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 lptr)
                 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 dptr) (Z_to_bv 64 1) (Z_to_bv 64 len) (Z_to_bv 64 pkt) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PM_RA2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until j. intros HD HL DP LP AP OD OL FR MI. unfold PM_RA2.
    replace (ret_pc (Z_to_bv 64 0x26d2f4)) with (Z_to_bv 64 0x26d2f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold cells_apart, apart, pm_frame, wz in *.
    pose proof (word_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ DP) as DB. pose proof (rw_cells_bound _ _ _ _ LP) as LBB. cbn [cells_size csize Nat.add] in DB, LBB.
    pose proof (munch_refl [(dptr, dptr + 8); (lptr, lptr + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    st1. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    st1. do 11 step. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ps1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
      (F : bvmap 5 word) (fc : bv 32) (pkt dptr lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j,
      ms' = MS (mkR (Z_to_bv 64 PS_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 dptr)
                   (Z_to_bv 64 0) (Z_to_bv 64 PK_FILE) (Z_to_bv 64 547) a3 a4 a5 a6 a7
                   (Z_to_bv 64 pkt) (Z_to_bv 64 PK_FILE) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra).

  Lemma ps_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt dptr lo : Z),
      rw_cells rsegs m dptr [C8 (wz 0)] -> (dptr + 8 <= lo \/ bv_unsigned sp <= dptr) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (ps1_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc pkt dptr lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pkt) (Z_to_bv 64 dptr) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_PACKET_strndup) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros DP OD ST CEIL LO MI. hcb. unfold P_PACKET_strndup, P_CRYPTO_free. unfold wz in DP.
    pose proof (word_range sp) as SPR. pose proof (rw_cells_bound _ _ _ _ DP) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 48%nat ST.
    do 17 step. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma ps_seg2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt cur ms len dptr : Z),
      rw_cells rsegs m pkt (pk_cells cur ms len) -> bv_unsigned sp <= pkt -> mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 PS_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 dptr)
                                         (Z_to_bv 64 cur) (Z_to_bv 64 len) (Z_to_bv 64 PK_FILE) (Z_to_bv 64 550) a4 a5 a6 a7
                                         (Z_to_bv 64 pkt) (Z_to_bv 64 PK_FILE) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_CRYPTO_strndup) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 PS_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 dptr)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pkt) (Z_to_bv 64 PK_FILE) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PS_RA1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until dptr. intros PK SPK MI. unfold PS_RA1, PS_RA2, PK_FILE, P_CRYPTO_strndup.
    replace (ret_pc (Z_to_bv 64 0x26d374)) with (Z_to_bv 64 0x26d374) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold pk_cells, wz in PK. pose proof (word_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. cbn [cells_size csize Nat.add] in PB.
    do 6 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ps_seg3 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pkt dptr D : Z) (j : list byte),
      0 < D < 2^64 ->
      rw_cells rsegs m dptr [C8 (wz 0)] -> (dptr + 8 <= bv_unsigned sp + -48 \/ bv_unsigned sp <= dptr) ->
      rw_cells rsegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m1 (seg_rom rsegs)
                   /\ munch [(dptr, dptr + 8)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
                   /\ rw_cells rsegs m1 dptr [C8 (wz D)])
        (MS (mkR (Z_to_bv 64 PS_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 dptr)
                 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pkt) (Z_to_bv 64 PK_FILE) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PS_RA2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until j. intros HD DP OD FR MI. unfold PS_RA2.
    replace (ret_pc (Z_to_bv 64 0x26d38c)) with (Z_to_bv 64 0x26d38c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold cm_frame, wz in *. pose proof (word_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ DP) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (munch_refl [(dptr, dptr + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. replace (Z.b2z (0 <? D)) with 1 by (destruct (Z.ltb_spec 0 D); cbn; lia).
    st1. do 8 step. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport rsegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  Lemma pkmemdup_spec : pkmemdup_stmt H.
  Proof.
    unfold pkmemdup_stmt. intros until errv.
    intros A0 A1 A2 PK SPK DP LP AP (DCR & DOI & DB8) (LCR & LOI & LB8) APD APL ACD ACL BS [CR CX] HL
           HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM.
    unfold PKMEMDUP_STACK, FR_PACKET_memdup, CMEMDUP_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    hcb. subst a0 a1 a2. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    unfold off_image, IMG_LO, IMG_HI in DOI, LOI. unfold cells_apart, apart in AP, APD, APL, ACD, ACL.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. unfold pk_cells in PB. cbn [cells_size csize Nat.add] in PB.
    pose proof (rclient_range_off_frame _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ lo HP DCR CEIL ltac:(lia)) as OFFD.
    pose proof (rclient_range_off_frame _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ lo HP LCR CEIL ltac:(lia)) as OFFL.
    pose proof (rclient_range_off_frame _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ lo HP CR CEIL ltac:(lia)) as OFFC.
    pose proof (rclient_range_off_errno _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ HP DCR ltac:(lia) ltac:(lia)) as ERD.
    pose proof (rclient_range_off_errno _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ HP LCR ltac:(lia) ltac:(lia)) as ERL.
    pose proof (rclient_range_off_auxv _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ HP DCR ltac:(lia) ltac:(lia)) as AXD.
    pose proof (rclient_range_off_auxv _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ HP LCR ltac:(lia) ltac:(lia)) as AXL.
    unfold RERRNO in ERD, ERL. unfold RAUXV_CELL in AXD, AXL.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply pm_seg1 with (lo := lo); [exact DP| lia| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    pose proof (cfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo); rewrite ?unsigned_lit by lia;
        [eapply (krel_halted H HH); exact KREL| eapply (krel_lazy H HH); exact KREL| exact ST1| exact CEIL| lia| exact MI1| |].
      - eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM].
      - eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]. }
    intros [ms2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & -> & MU2 & WM2 & MI2 & ST2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in MU2, ST2 by lia.
    assert (MU12 : munch [(lo, bv_unsigned sp)] m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; intros x Hx; cbn in Hx |- *; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM1 WM2) as WM12.
    apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1) in MU2 as FR2; [| exact WM2| cbn; lia].
    apply (rw_cells_transport rsegs _ m m2 _ _ PK) in MU12 as PK2; [| exact WM12| cbn; lia].
    apply (rw_cells_transport rsegs _ m m2 _ _ DP) in MU12 as DP2; [| exact WM12| cbn; lia].
    apply (rw_cells_transport rsegs _ m m2 _ _ LP) in MU12 as LP2; [| exact WM12| cbn; lia].
    apply (bytes_at_transport rsegs _ m m2 _ _ BS) in MU12 as BS2; [| cbn; lia].
    subst tp. rewrite errno_RATP in ERR. rewrite ?errno_RATP.
    apply (rw_cells_transport rsegs _ m m2 _ _ ERR) in MU12 as ERR2; [| exact WM12| unfold RERRNO; cbn; lia].
    assert (MF2 : MEMFLAG m2 v) by (eapply MEMFLAG_across; [exact MU12| exact WM12| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (HP2 : hs_RHEAP H s LB m2).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU12| exact WM12|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX2 : hs_rauxv_ok H m2 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU12| exact WM12|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (XP2 : xpres LB (bv_unsigned sp) ([(dptr, dptr + 8); (lptr, lptr + 8)] ++ memflag_foot) m m2).
    { eapply xpres_of_munch; [exact MU12| exact WM12| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    clear MU1 WM1 MI1 ST1 FR1 MU2 WM2 CF.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply pm_seg2 with (oldlen := oldlen);
      [exact PK2| lia| lia| exact DP2| exact LP2| unfold cells_apart, apart; lia| unfold apart; lia| unfold apart; lia| lia| lia| exact FR2| exact MI2]|].
    intros ms3 (m3 & CASES & MU3 & WM3 & MI3 & PK3 & DP3 & LP3).
    apply (stk_transport_disjoint rsegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| clear - OFFD OFFL LO SPR; cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ ERR2) in MU3 as ERR3; [| exact WM3| clear - ERD ERL; unfold RERRNO; cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2) in MU3 as FR3; [| exact WM3| clear - OFFD OFFL LO SPR; cbn; lia].
    assert (HP3 : hs_RHEAP H s LB m3).
    { eapply (HH_RHEAP_frame H HH); [exact HP2| exact MU3| exact WM3|].
      constructor; [eapply rclient_range_write_ok; [exact DCR| lia]|]. constructor; [eapply rclient_range_write_ok; [exact LCR| lia]| constructor]. }
    assert (AUX3 : hs_rauxv_ok H m3 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    assert (XP3 : xpres LB (bv_unsigned sp) ([(dptr, dptr + 8); (lptr, lptr + 8)] ++ memflag_foot) m m3).
    { eapply xpres_trans; [exact XP2|]. eapply xpres_of_munch; [exact MU3| exact WM3| | exact HB].
      constructor; [right; intros a Ha; cbn in Ha |- *; lia|]. constructor; [right; intros a Ha; cbn in Ha |- *; lia| constructor]. }
    assert (MF3 : MEMFLAG m3 v) by (eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]).
    assert (IM3 : IMPL_mem m3) by (eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]).
    assert (GM3 : GOT_mem m3) by (eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]).
    destruct CASES as [(L0 & ->)|(L1 & -> & FR3')].
    - (* [comment removed for export] *)
      apply (sr_done H HH). unfold pkmemdup_post. cbn [cfg_ms cfg_model]. unfold zlength.
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv, s, LB, 0.
      split; [reflexivity|]. split; [exact KREL|]. split; [apply (mpres_refl H HH)|]. split; [exact MI3|].
      split. { unfold pm_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
      split; [exact ERR3|]. split; [exact AUX3|]. split; [exact HP3|].
      split; [rewrite L0 in PK3; rewrite L0; exact PK3|]. split; [exact DP3|]. split; [rewrite L0; cbn; exact LP3|].
      split; [left; split; [exact L0| split; reflexivity]|].
      split; [exact XP3|]. split; [exists v; split; [exact MF3| clear; lia]|]. split; [exact IM3| exact GM3].
    - (* [comment removed for export] *)
      clear FR3'. apply (bytes_at_transport rsegs _ m2 m3 _ _ BS2) in MU3 as BS3; [| cbn; lia].
      pose proof (cmemdup_spec H HH) as CM. unfold cmemdup_stmt in CM.
      eapply (sr_seq H HH).
      { eapply CM with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (bs := bs); unfold zlength; rewrite ?unsigned_lit by lia; try reflexivity.
        all: try first [exact BS3| exact HP3| exact KREL| exact AUX3| exact ST3| exact CEIL| exact ERR3| exact MI3| exact MF3| exact IM3| exact GM3].
        all: try (unfold CMEMDUP_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
        split; [eapply rclient_range_SP_mono; [exact CR| lia]| exact CX]. }
      intros [ms4 mo4] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO. unfold zlength in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 & errv4 & A & p & s' &
                      -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & BR & HEAP4 & BLK4 & MF4 & IM4 & GM4).
      rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST4, XP4 by lia.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in FR3; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in PK3; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in DP3; [| eapply rclient_range_SP_mono; [exact DCR| lia]| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in LP3; [| eapply rclient_range_SP_mono; [exact LCR| lia]| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ _ _ _ HEAP4 DCR ltac:(lia) ltac:(lia)) as SEPD.
      pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ _ _ _ HEAP4 LCR ltac:(lia) ltac:(lia)) as SEPL.
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL4| eapply pm_seg3;
        [clear - BR1 BR4 HCEILB; lia| clear - HL L1; lia| exact DP3| exact LP3| exact AP| clear - OFFD LO; lia| clear - OFFL LO; lia| exact FR3| exact MI4]|].
      intros ms5 (m5 & -> & MU5 & WM5 & MI5 & DP5 & LP5).
      apply (sr_done H HH). unfold pkmemdup_post. cbn [cfg_ms cfg_model]. unfold zlength.
      exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m5, errv4, s', ((p, A, Z.of_nat (length bs)) :: LB), A.
      split; [reflexivity|]. split; [exact KREL4|]. split; [exact MP4|]. split; [exact MI5|].
      split. { apply (rw_cells_transport rsegs _ m4 m5 _ _ FR3) in MU5 as FR5; [| exact WM5| clear - OFFD OFFL LO SPR; cbn; lia].
               apply (stk_transport_disjoint rsegs _ m4 m5 _ _ ST4) in MU5 as ST5; [| exact WM5| clear - OFFD OFFL LO SPR; cbn; lia].
               unfold pm_frame in FR5. release_frame FR5 ST5 (bv_unsigned sp). exact ST5. }
      split. { eapply rw_cells_transport; [exact ERR4| exact MU5| exact WM5| rewrite errno_RATP; unfold RERRNO; cbn; lia]. }
      split. { eapply (HH_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5|]. unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
      split. { eapply (HH_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5|].
               constructor; [apply rclient_write_ok_cons; eapply rclient_range_write_ok; [exact DCR| lia]|].
               constructor; [apply rclient_write_ok_cons; eapply rclient_range_write_ok; [exact LCR| lia]| constructor]. }
      split. { eapply rw_cells_transport; [exact PK3| exact MU5| exact WM5| cbn; lia]. }
      split; [exact DP5|]. split; [destruct (Z.eqb_spec (Z.of_nat (length bs)) 0); [lia| exact LP5]|].
      split. { right. split; [lia|]. exists p. split; [exact BR|]. split; [reflexivity|].
               eapply rw_cells_transport; [exact BLK4| exact MU5| exact WM5| cbn; lia]. }
      split. { eapply xpres_trans; [exact XP3|]. eapply xpres_trans.
               - eapply xpres_weaken; [exact XP4| lia| auto|]. intros a Ha. apply rin_ivs_app. right. exact Ha.
               - eapply xpres_of_munch_gen; [exact MU5| exact WM5|]. intros a Ha [HC HX]. clear - Ha HX. cbn. cbn in HX. lia. }
      split; [exists 1; split; [eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]| destruct MF as (fb0 & _ & _ & V01); clear - V01; lia]|].
      split; [eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]|].
      eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4].
  Qed.

  Lemma pkstrndup_spec : pkstrndup_stmt H.
  Proof.
    unfold pkstrndup_stmt. intros until errv.
    intros A0 A1 PK SPK HC DP (DCR & DOI & DB8) APD ACD BS [CR CX] HL
           HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM.
    unfold PKSTRNDUP_STACK, FR_PACKET_strndup, CSTRNDUP_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    hcb. subst a0 a1. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    unfold off_image, IMG_LO, IMG_HI in DOI. unfold apart in APD, ACD.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. unfold pk_cells in PB. cbn [cells_size csize Nat.add] in PB.
    pose proof (rclient_range_off_frame _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ lo HP DCR CEIL ltac:(lia)) as OFFD.
    pose proof (rclient_range_off_frame _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ lo HP CR CEIL ltac:(lia)) as OFFC.
    pose proof (rclient_range_off_errno _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ HP DCR ltac:(lia) ltac:(lia)) as ERD.
    pose proof (rclient_range_off_auxv _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ HP DCR ltac:(lia) ltac:(lia)) as AXD.
    unfold RERRNO in ERD. unfold RAUXV_CELL in AXD.
    pose proof (strnlen_le bs) as KL.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply ps_seg1 with (lo := lo); [exact DP| lia| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    pose proof (cfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo); rewrite ?unsigned_lit by lia;
        [eapply (krel_halted H HH); exact KREL| eapply (krel_lazy H HH); exact KREL| exact ST1| exact CEIL| lia| exact MI1| |].
      - eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM].
      - eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]. }
    intros [ms2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & -> & MU2 & WM2 & MI2 & ST2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU2, ST2 by lia.
    assert (MU12 : munch [(lo, bv_unsigned sp)] m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; intros x Hx; cbn in Hx |- *; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM1 WM2) as WM12.
    apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1) in MU2 as FR2; [| exact WM2| cbn; lia].
    apply (rw_cells_transport rsegs _ m m2 _ _ PK) in MU12 as PK2; [| exact WM12| cbn; lia].
    apply (rw_cells_transport rsegs _ m m2 _ _ DP) in MU12 as DP2; [| exact WM12| cbn; lia].
    apply (bytes_at_transport rsegs _ m m2 _ _ BS) in MU12 as BS2; [| cbn; lia].
    subst tp. rewrite errno_RATP in ERR. rewrite ?errno_RATP.
    apply (rw_cells_transport rsegs _ m m2 _ _ ERR) in MU12 as ERR2; [| exact WM12| unfold RERRNO; cbn; lia].
    assert (MF2 : MEMFLAG m2 v) by (eapply MEMFLAG_across; [exact MU12| exact WM12| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (HP2 : hs_RHEAP H s LB m2).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU12| exact WM12|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX2 : hs_rauxv_ok H m2 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU12| exact WM12|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (XP2 : xpres LB (bv_unsigned sp) ((dptr, dptr + 8) :: memflag_foot) m m2).
    { eapply xpres_of_munch; [exact MU12| exact WM12| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    clear MU1 WM1 MI1 ST1 FR1 MU2 WM2 CF.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply ps_seg2; [exact PK2| lia| exact MI2]|].
    intros ms3 ->.
    (* [comment removed for export] *)
    pose proof (cstrndup_spec H HH) as CS. unfold cstrndup_stmt in CS.
    eapply (sr_seq H HH).
    { eapply CS with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (bs := bs); unfold zlength; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact BS2| exact HP2| exact KREL| exact AUX2| exact ST2| exact CEIL| exact ERR2| exact MI2| exact MF2| exact IM2| exact GM2].
      all: try (unfold CSTRNDUP_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      split; [eapply rclient_range_SP_mono; [exact CR| lia]| exact CX]. }
    intros [ms4 mo4] PO. unfold cstrndup_post in PO. cbn [cfg_ms cfg_model] in PO. cbv zeta in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 & errv4 & A & p & s' &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & BR & HEAP4 & BLK4 & MF4 & IM4 & GM4).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST4, XP4 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in FR2; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in PK2; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in DP2; [| eapply rclient_range_SP_mono; [exact DCR| lia]| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ _ _ _ HEAP4 DCR ltac:(lia) ltac:(lia)) as SEPD.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply ps_seg3; [lia| exact DP2| lia| exact FR2| exact MI4]|].
    intros ms5 (m5 & -> & MU5 & WM5 & MI5 & DP5).
    apply (sr_done H HH). unfold pkstrndup_post. cbn [cfg_ms cfg_model]. cbv zeta. unfold zlength.
    exists v0, v1, v2, (Z_to_bv 64 1), d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m5, errv4, s', A, p.
    split; [reflexivity|]. split; [exact KREL4|]. split; [exact MP4|]. split; [exact MI5|].
    split. { apply (rw_cells_transport rsegs _ m4 m5 _ _ FR2) in MU5 as FR5; [| exact WM5| cbn; lia].
             apply (stk_transport_disjoint rsegs _ m4 m5 _ _ ST4) in MU5 as ST5; [| exact WM5| cbn; lia].
             unfold cm_frame in FR5. release_frame FR5 ST5 (bv_unsigned sp). exact ST5. }
    split. { eapply rw_cells_transport; [exact ERR4| exact MU5| exact WM5| rewrite errno_RATP; unfold RERRNO; cbn; lia]. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5|].
             constructor; [apply rclient_write_ok_cons; eapply rclient_range_write_ok; [exact DCR| lia]| constructor]. }
    split. { eapply rw_cells_transport; [exact BLK4| exact MU5| exact WM5| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact PK2| exact MU5| exact WM5| cbn; lia]. }
    split; [exact DP5|].
    split. { eapply xpres_trans; [exact XP2|]. eapply xpres_trans.
             - eapply xpres_weaken; [exact XP4| lia| auto|]. intros a Ha. right. exact Ha.
             - eapply xpres_of_munch_gen; [exact MU5| exact WM5|]. intros a Ha [HC' HX]. clear - Ha HX. cbn. cbn in HX. lia. }
    split; [eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; cbn; lia| exact MF4]|].
    split; [eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM4]|].
    eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM4].
  Qed.

  Theorem C10_spec : C10_stmts H.
  Proof. split; [exact pkmemdup_spec| exact pkstrndup_spec]. Qed.
End W.
