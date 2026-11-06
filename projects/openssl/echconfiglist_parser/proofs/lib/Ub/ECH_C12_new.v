(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_malloc ECH_C12_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition VPM_FILE : Z := 0x370f2.        (* [comment removed for export] *)
  Definition VN_RA : Z := 0x2165bc.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition vpm_zero_cells : list cell :=
    [CB 36 (zeros 36); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
     C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Lemma vpm_zero_recut : forall m A, rw_cells usegs m A [CB (Z.to_nat 136) (zeros (Z.to_nat 136))] -> rw_cells usegs m A vpm_zero_cells.
  Proof. intros m A HB. eapply rw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.
  Lemma vpm_empty_cells : forall p, vpm_cells (vpm_empty p) =
    [CB 36 (zeros 36); C4 (wz 0); C8 (wz 18446744073709551615); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
     C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vn_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 VN_RA) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1
                       (Z_to_bv 64 136) (Z_to_bv 64 VPM_FILE) (Z_to_bv 64 358) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -16)
          /\ rw_cells usegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_X509_VERIFY_PARAM_new) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. hcb. unfold P_X509_VERIFY_PARAM_new, P_CRYPTO_zalloc, VN_RA, VPM_FILE.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 10 step. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vn_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (p : bptr),
      0 < A -> A mod 16 = 0 -> A + 136 <= bv_unsigned sp + -16 ->
      rw_cells usegs m A vpm_zero_cells ->
      rw_cells usegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(A, A + 136)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 A (vpm_cells (vpm_empty p)))
        (MS (mkR (Z_to_bv 64 VN_RA) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 VN_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until p. intros HA HAL HS BLK FR MI. unfold VN_RA.
    replace (ret_pc (Z_to_bv 64 0x2165bc)) with (Z_to_bv 64 0x2165bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold vpm_zero_cells, wz in BLK. rewrite vpm_empty_cells. unfold wz.
    pose proof (munch_refl [(A, A + 136)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. ubal_by HAL. step. if_lit.   (* [comment removed for export] *)
    step. st1. st1. do 4 step. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  Lemma vpmnew_spec : vpmnew_stmt H.
  Proof.
    unfold vpmnew_stmt. intros until errv.
    intros HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM RAE.
    unfold VPMNEW_STACK, FR_X509_VERIFY_PARAM_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    unfold VPM_SIZE in BUD.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    eapply (sr_evt_krel H HH); [exact KREL| eapply vn_seg1; [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 136) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: try first [exact KREL| exact ST1| exact CEIL| exact MI1| exact TP].
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]
           | |- lb_bytes _ + _ <= _ => lia
           | |- lb_big _ + _ <= _ => rewrite big1_small by (unfold BIGB; lia); lia
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; constructor; [cbn; lia| constructor]
           | |- rw_cells _ _ _ _ => subst tp; rewrite errno_RATP in *; errno_across ERR MU1 WM1
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           end. }
    intros [ms2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -16)) in ST2, XP2 by lia. change (136 * 1) with 136 in BR, HEAP2, BLK.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    apply vpm_zero_recut in BLK.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply vn_seg2 with (p := p); [lia| exact BR2| lia| exact BLK| exact FR1| exact MI2]|].
    intros ms3 (m3 & -> & MU3 & WM3 & MI3 & HDR3).
    apply (sr_done H HH).
    unfold vpmnew_post. cbn [cfg_ms cfg_model].
    apply (rw_cells_transport usegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
    exists u0, u1, u2, (Z_to_bv 64 (-1)), b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, A, p, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|].
    split. { apply (stk_transport_disjoint usegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
             eapply stk_release in FR3; [| exact ST3| lia]. cbn [cells_size csize Nat.add] in FR3.
             replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) in FR3 by lia. exact FR3. }
    split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; lia]. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    split. { eapply xpres_trans; [exact XP1|]. eapply xpres_trans; [eapply (xpres_weaken LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto]|].
             eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right. exists (p, A, 136). split; [left; reflexivity| cbn; lia]. }
    split.
    { unfold VPMobj, VPM_SIZE. split; [exact HDR3|]. split; [left; reflexivity|]. cbn. reflexivity. }
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2].
  Qed.
End W.
