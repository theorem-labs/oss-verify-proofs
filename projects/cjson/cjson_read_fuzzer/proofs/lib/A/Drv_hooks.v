(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface CJ_conv Drv_base Drv_iface2 Drv_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CeilWrap.
Context {ACEIL : Ceil}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma uwt_small_s0 : forall m lo top pc0 prev f k, f <= prev -> uwt m lo top pc0 prev f k [].
Proof. intros. apply uwt_stop. left. exact H. Qed.

(* [comment removed for export] *)
Lemma lrz_lscps_vm : forall (P : machine_state -> Model -> lghost -> Prop) ms mo g T,
  LSCPS asegs P ms mo g -> (forall ms' mo' g', P ms' mo' g' -> vm_only mo mo' -> LRZ asegs ms' mo' g' T) -> LRZ asegs ms mo g T.
Proof.
  intros P ms mo g T H K mr mat HI. apply (H mr mat HI T). intros ms' mo' g' mr' mat' HP HI' HV. apply (K _ _ _ HP HV _ _ HI').
Qed.

Lemma DMOD_vm_only : forall fs F mo mo', DMOD fs F mo -> vm_only mo mo' -> DMOD fs F mo'.
Proof.
  intros fs F mo mo' [HF HS HH] (Vfd & _ & Vfs & Vpr & _). unfold m_fds, m_fs, m_halted in *.
  split; unfold m_fds, m_fs, m_halted; rewrite ?Vfd, ?Vfs, ?Vpr; assumption.
Qed.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).
  Let ART := CJ_iface.ART AI.
  Hypothesis TROK : drv_traces_ok TI.

  Lemma drv_stat_hook : forall pc0 sp0 sp ra,
    In [pc0; ra] S_DRIVER -> In [pc0] S_DRIVER -> STAT TI (hook_tr pc0 sp0 sp ra []).
  Proof. intros pc0 sp0 sp ra H2 H1. unfold hook_tr. destruct (hop1_ok sp0 sp); apply TROK; assumption. Qed.

  (* [comment removed for export] *)
  Lemma drv_free :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B np A n lo : Z) (errv : word) (T : TSet),
      ART sp0 SPB LB [] TRS B m mo g -> In (A, n) LB -> TINV TI np TRS ->
      In [PC0_FREE; bv_unsigned ra] S_DRIVER ->
      bv_unsigned s0 <= bv_unsigned sp -> bv_unsigned sp <= SPB ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
      a0 = wz A -> cost_free <= B ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (mo' : Model) (g' : lghost)
              (TRS' : list (list Z)),
          mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' AERRNO [C4 errv] ->
          cj_pres sp0 (cb_remove A LB) [] (bv_unsigned sp) m m' -> gmono g g' -> TINV TI np TRS' -> vm_only mo mo' ->
          ART sp0 SPB (cb_remove A LB) [] TRS' (B - cost_free) m' mo' g' ->
          LRZ asegs (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs)) mo' g' T) ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz AFREE) fc None m (seg_rom asegs)) mo g T.
  Proof.
    intros until T. intros HART HINB HT HIN HS0 HSPB ST CEIL LO ER MI TP Ha0 HB K.
    assert (HST : STAT TI (hook_tr PC0_FREE sp0 (bv_unsigned sp) (bv_unsigned ra) [])).
    { apply drv_stat_hook; [exact HIN|]. unfold S_DRIVER. cbn. tauto. }
    eapply lrz_lscps_vm.
    { eapply (art_free AI) with (lo := lo) (tl := []);
        first [exact HART| exact HINB| exact HSPB| exact ST| exact CEIL| exact LO| exact ER| exact MI| exact TP| exact Ha0| exact HB
              | pose proof (drv_ra_ok _ _ HIN); tauto
              | apply uwt_small_s0; exact HS0
              | eapply (tinv_room TI); [exact HT| exact HST] ]. }
    cbv beta. intros ms' mo' g' (x5 & x6 & x7 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & TRS' & -> & MI' & ST' & ER' & PR & GM & TP' & HA) HV.
    eapply K; [exact MI'| exact ST'| exact ER'| exact PR| exact GM| eapply (tinv_put TI); [exact HT| exact HST| exact TP']| exact HV| exact HA].
  Qed.

  (* [comment removed for export] *)
  Lemma drv_free_null :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B lo : Z) (errv : word) (T : TSet),
      ART sp0 SPB LB [] TRS B m mo g ->
      In [PC0_FREE; bv_unsigned ra] S_DRIVER ->
      bv_unsigned s0 <= bv_unsigned sp -> bv_unsigned sp <= SPB ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
      a0 = wz 0 ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (mo' : Model) (g' : lghost),
          mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' AERRNO [C4 errv] ->
          cj_pres sp0 LB [] (bv_unsigned sp) m m' -> gmono g g' -> vm_only mo mo' ->
          ART sp0 SPB LB [] TRS B m' mo' g' ->
          LRZ asegs (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs)) mo' g' T) ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz AFREE) fc None m (seg_rom asegs)) mo g T.
  Proof.
    intros until T. intros HART HIN HS0 HSPB ST CEIL LO ER MI TP Ha0 K.
    eapply lrz_lscps_vm.
    { eapply (art_free_null AI) with (lo := lo) (tl := []);
        first [exact HART| exact HSPB| exact ST| exact CEIL| exact LO| exact ER| exact MI| exact TP| exact Ha0
              | pose proof (drv_ra_ok _ _ HIN); tauto
              | apply uwt_small_s0; exact HS0 ]. }
    cbv beta. intros ms' mo' g' PO. unfold afree_null_post in PO.
    intros HV. destruct PO as (x5 & x6 & x7 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & -> & REST).
    decompose [and] REST. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable DI : drv_iface2 AI.
  Let ADRV := Drv_iface2.ADRV AI DI.

  (* [comment removed for export] *)
  Lemma drv_malloc_nn :
    forall (k : nat)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B np n lo : Z) (errv : word) (T : TSet),
      ART sp0 SPB LB [] TRS B m mo g -> ADRV (S k) m mo g -> TINV TI np TRS ->
      In [PC0_MALLOC; bv_unsigned ra] S_DRIVER ->
      bv_unsigned s0 <= bv_unsigned sp -> bv_unsigned sp <= SPB ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
      a0 = wz n -> 0 < n <= DRV_REQ_MAX -> cost_malloc n <= B -> DRV_BFLOOR <= B -> (is_primary n = true -> k = 0%nat) ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (mo' : Model) (g' : lghost)
              (errv' : word) (TRS' : list (list Z)) (A : Z) (junk : list byte),
          mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' AERRNO [C4 errv'] ->
          cj_pres sp0 LB [] (bv_unsigned sp) m m' -> gmono g g' -> TINV TI np TRS' -> vm_only mo mo' ->
          A <> 0 -> ablock_range A n -> ~ In A (map fst LB) ->
          ART sp0 SPB ((A, n) :: LB) [] TRS' (B - cost_malloc n) m' mo' g' -> ADRV k m' mo' g' ->
          rw_cells asegs m' A [CB (Z.to_nat n) junk] ->
          LRZ asegs (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz A) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs)) mo' g' T) ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz AMALLOC) fc None m (seg_rom asegs)) mo g T.
  Proof.
    intros until T. intros HART HDRV HT HIN HS0 HSPB ST CEIL LO ER MI TP Ha0 Hn HB HBF HPK K.
    assert (HST : STAT TI (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) [])).
    { apply drv_stat_hook; [exact HIN|]. unfold S_DRIVER. cbn. tauto. }
    eapply lrz_lscps_vm.
    { eapply (art2_malloc AI DI) with (lo := lo) (tl := []) (errv := errv);
        first [exact HART| exact HDRV| exact HSPB| exact ST| exact CEIL| exact LO| exact ER| exact MI| exact TP| exact Ha0| exact Hn| exact HB| exact HBF| exact HPK
              | pose proof (drv_ra_ok _ _ HIN); tauto
              | apply uwt_small_s0; exact HS0
              | eapply (tinv_room TI); [exact HT| exact HST] ]. }
    cbv beta. intros ms' mo' g' (x5 & x6 & x7 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & errv' & TRS' & A & junk
                                 & -> & MI' & ST' & ER' & PR & GM & TP' & NZ & BR & NI & _ & HA & HD & BLK) HV.
    eapply K; [exact MI'| exact ST'| exact ER'| exact PR| exact GM| eapply (tinv_put TI); [exact HT| exact HST| exact TP']| exact HV
              | exact NZ| exact BR| exact NI| exact HA| exact HD| exact BLK].
  Qed.

  (* [comment removed for export] *)
  Lemma drv_free2 :
    forall (k : nat)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B np A n lo : Z) (errv : word) (T : TSet),
      ART sp0 SPB LB [] TRS B m mo g -> ADRV k m mo g -> In (A, n) LB -> TINV TI np TRS ->
      In [PC0_FREE; bv_unsigned ra] S_DRIVER ->
      bv_unsigned s0 <= bv_unsigned sp -> bv_unsigned sp <= SPB ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
      a0 = wz A -> cost_free <= B ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (mo' : Model) (g' : lghost)
              (TRS' : list (list Z)),
          mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' AERRNO [C4 errv] ->
          cj_pres sp0 (cb_remove A LB) [] (bv_unsigned sp) m m' -> gmono g g' -> TINV TI np TRS' -> vm_only mo mo' ->
          ART sp0 SPB (cb_remove A LB) [] TRS' (B - cost_free) m' mo' g' -> ADRV k m' mo' g' ->
          LRZ asegs (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs)) mo' g' T) ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz AFREE) fc None m (seg_rom asegs)) mo g T.
  Proof.
    intros until T. intros HART HDRV HINB HT HIN HS0 HSPB ST CEIL LO ER MI TP Ha0 HB K.
    assert (HST : STAT TI (hook_tr PC0_FREE sp0 (bv_unsigned sp) (bv_unsigned ra) [])).
    { apply drv_stat_hook; [exact HIN|]. unfold S_DRIVER. cbn. tauto. }
    eapply lrz_lscps_vm.
    { eapply (art2_free AI DI k) with (lo := lo) (tl := []);
        first [split; [exact HART| exact HDRV] | exact HINB| exact HSPB| exact ST| exact CEIL| exact LO| exact ER| exact MI| exact TP| exact Ha0| exact HB
              | pose proof (drv_ra_ok _ _ HIN); tauto
              | apply uwt_small_s0; exact HS0
              | eapply (tinv_room TI); [exact HT| exact HST] ]. }
    cbv beta. intros ms' mo' g' (x5 & x6 & x7 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & TRS' & -> & MI' & ST' & ER' & PR & GM & TP' & [HA HD]) HV.
    eapply K; [exact MI'| exact ST'| exact ER'| exact PR| exact GM| eapply (tinv_put TI); [exact HT| exact HST| exact TP']| exact HV| exact HA| exact HD].
  Qed.
End S.
End CeilWrap.
