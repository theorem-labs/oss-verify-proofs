(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BZBridge BSysStep BExec BellsX BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk BsCXXHeap.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Stubs.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis Lsr : SR_laws H.
  Hypothesis Lmpres : MPRES_laws H.

  Let SRdone : forall (Q : config -> Prop) c, Q c -> as_SR H Q c. Proof. exact (proj1 Lsr). Qed.
  Let SRmono : forall (Q Q' : config -> Prop) c, as_SR H Q c -> (forall c', Q c' -> Q' c') -> as_SR H Q' c. Proof. exact (proj1 (proj2 Lsr)). Qed.
  Let SRseq : forall (Q1 Q2 : config -> Prop) c, as_SR H Q1 c -> (forall c', Q1 c' -> as_SR H Q2 c') -> as_SR H Q2 c. Proof. exact (proj1 (proj2 (proj2 Lsr))). Qed.
  Let SRlift : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
      as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = ms -> evt asegs P ms ->
      (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> P (as_VIS H s msF') -> as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msF mo).
  Proof. exact (proj2 (proj2 (proj2 Lsr))). Qed.
  Let MPtrans : forall mo1 mo2 mo3, as_MPRES H mo1 mo2 -> as_MPRES H mo2 mo3 -> as_MPRES H mo1 mo3. Proof. exact (proj2 Lmpres). Qed.

  Lemma j_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                       (F : bvmap 5 word) (fc : bv 32) (m : mem) (pc target : Z),
    (pc = AOPDEL /\ target = AFREE_STUB) \/ (pc = AOPDEL2 /\ target = AOPDEL) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 target) fc None m (seg_rom asegs))
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
  Proof.
    intros until target. intros PT MI.
    destruct PT as [[-> ->]|[-> ->]]; unfold AOPDEL, AOPDEL2, AFREE_STUB.
    - step. apply evt_done. reflexivity.
    - step. apply evt_done. reflexivity.
  Qed.

  Lemma free_stmt_via_j : forall pc target pc0,
    (pc = AOPDEL /\ target = AFREE_STUB) \/ (pc = AOPDEL2 /\ target = AOPDEL) ->
    free_stmt_at H target pc0 -> free_stmt_at H pc pc0.
  Proof.
    intros pc target pc0 PT FS. unfold free_stmt_at. intros until sbs. intros VIS HP K IN CF CB SH SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0.
    eapply SRlift; [exact K | exact VIS | apply j_evt; [exact PT| exact MI] |].
    intros msF' mo' K' MP E. cbv beta in E.
    eapply SRmono.
    { exact (FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF' m s LB p A n lo B errv mo' CH bs sbs
                E HP K' IN CF CB SH SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0). }
    intros c' PO. unfold free_post in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & s' & V' & K2 & MP2 & REST).
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', s'.
    split; [exact V'|]. split; [exact K2|]. split; [exact (MPtrans _ _ _ MP MP2)| exact REST].
  Qed.

  Lemma free_null_stmt_via_j : forall pc target,
    (pc = AOPDEL /\ target = AFREE_STUB) \/ (pc = AOPDEL2 /\ target = AOPDEL) ->
    free_null_stmt_at H target -> free_null_stmt_at H pc.
  Proof.
    intros pc target PT FS. unfold free_null_stmt_at. intros until CH. intros VIS HP K CF AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH.
    eapply SRlift; [exact K | exact VIS | apply j_evt; [exact PT| exact MI] |].
    intros msF' mo' K' MP E. cbv beta in E.
    eapply SRmono.
    { exact (FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF' m s LB lo B errv mo' CH
                E HP K' CF AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH). }
    intros c' PO. unfold free_null_post in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & s' & V' & K2 & MP2 & REST).
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', s'.
    split; [exact V'|]. split; [exact K2|]. split; [exact (MPtrans _ _ _ MP MP2)| exact REST].
  Qed.

  Lemma opdel_of_free : free_stmt H -> opdel_stmt H.
  Proof. intros FS. exact (free_stmt_via_j AOPDEL AFREE_STUB APC0_FREE (or_introl (conj eq_refl eq_refl)) FS). Qed.
  Lemma opdel2_of_free : free_stmt H -> opdel2_stmt H.
  Proof. intros FS. exact (free_stmt_via_j AOPDEL2 AOPDEL APC0_FREE (or_intror (conj eq_refl eq_refl)) (opdel_of_free FS)). Qed.
  Lemma opdel_null_of_free_null : free_null_stmt_at H AFREE_STUB -> free_null_stmt_at H AOPDEL.
  Proof. intros FS. exact (free_null_stmt_via_j AOPDEL AFREE_STUB (or_introl (conj eq_refl eq_refl)) FS). Qed.
  Lemma opdel2_null_of_free_null : free_null_stmt_at H AFREE_STUB -> free_null_stmt_at H AOPDEL2.
  Proof. intros FS. exact (free_null_stmt_via_j AOPDEL2 AOPDEL (or_intror (conj eq_refl eq_refl)) (opdel_null_of_free_null FS)). Qed.

  Definition opnew_W (SP : Z) : list (Z * Z) := [(SP - 16, SP)].
  Lemma opnew_pro :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (n lo : Z),
    a0 = Z_to_bv 64 n -> 1 <= n <= 2^28 ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo + 16 <= bv_unsigned sp ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists m1,
                 ms' = MS (mkR (Z_to_bv 64 ARA_OPNEW) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 n) s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AMALLOC_STUB) fc None m1 (seg_rom asegs)
                 /\ munch (opnew_W (bv_unsigned sp)) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
                 /\ stk asegs m1 lo (bv_unsigned sp + -16)
                 /\ rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AOPNEW) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros -> N ST CEIL LO MI. unfold AOPNEW, AMALLOC_STUB, ARA_OPNEW. acb.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl (opnew_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold opnew_W in MU.
    carve_frame 16%nat ST.
    step. step. step. zstep. zstep. step. step.
    replace (n + Z.b2z (n <? 1)) with n by (destruct (Z.ltb_spec n 1); cbn; lia).
    apply evt_done. exists m1. split; [reflexivity|]. unfold opnew_W. repeat (split; [assumption|]). assumption.
  Qed.

  Lemma opnew_epi :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (ra0 s00 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A lo : Z),
    0 < A < 2^47 ->
    sp = Z_to_bv 64 (bv_unsigned sp - 16 + 16) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo <= bv_unsigned sp ->
    rw_cells asegs m (bv_unsigned sp) [C8 s00; C8 ra0] -> bv_unsigned sp + 16 < 2^64 ->
    mem_inv asegs m ->
    evt asegs (fun ms' =>
                 ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 s00 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m (seg_rom asegs)
                 /\ stk asegs m lo (bv_unsigned sp + 16))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ARA_OPNEW)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HA _ ST CEIL FR SPH MI. unfold ARA_OPNEW. acb.
    replace (ret_pc (Z_to_bv 64 0x17d554)) with (Z_to_bv 64 0x17d554) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
    step. step. step. step. apply evt_done. split; [reflexivity|].
    release_frame FR ST (bv_unsigned sp + 16). exact ST.
  Qed.

  Hypothesis Lbr : RHEAP_block_range H.
  Hypothesis Lfsb : RHEAP_fsb H.
  Lemma apres_of_munch0 : forall s LB SP W m0 m m',
    as_RHEAP H s LB m0 ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => aceil <= fst iv /\ snd iv <= SP) W ->
    apres H LB SP m m'.
  Proof.
    intros s LB SP W m0 m m' RH MU WM FW a Ha Hc. acb.
    pose proof (Lfsb _ _ _ RH) as (F1 & F2 & F3).
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as [H1 H2]. cbn in H1, H2.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      intros K. unfold aclient_addr in Hc.
      destruct Hc as [Hc|Hc]; [lia|].
      assert (LOW : a < aceil); [| lia].
      destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
      - acb; unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      - pose proof (Lbr _ _ _ _ RH Hb) as (_ & _ & _ & _ & R & _). lia.
      - pose proof (Lbr _ _ _ _ RH Hb) as (_ & _ & R0 & R1 & R & _).
        pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
        unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
      - lia.
      - pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) ltac:(acb; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
        acb; unfold AFS_SIZE in *. lia.
      - acb; unfold AHI_LO in *. lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma apres_trans0 : forall LB SP m1 m2 m3, apres H LB SP m1 m2 -> apres H LB SP m2 m3 -> apres H LB SP m1 m3.
  Proof.
    intros LB SP m1 m2 m3 P1 P2 a Ha Hc. destruct (P1 a Ha Hc) as [E1 W1]. destruct (P2 a Ha Hc) as [E2 W2].
    split; [congruence| auto].
  Qed.
  Lemma apres_weaken_sp : forall LB SP SP' m m', apres H LB SP m m' -> SP <= SP' -> apres H LB SP' m m'.
  Proof.
    intros LB SP SP' m m' P LE a Ha Hc. apply P; [exact Ha|].
    unfold aclient_addr in *. destruct Hc as [Hc|Hc]; [left; lia| right; exact Hc].
  Qed.

  Hypothesis Lrf : RHEAP_frame H.
  Hypothesis Laux : rauxv_frame H.
  Hypothesis Lch : chain_laws H.
  Hypothesis Ltr : TR_laws H.
  Hypothesis Lmalloc : malloc_stmt H.

  Theorem opnew_of_malloc : opnew_stmt H.
  Proof.
    unfold opnew_stmt. intros until mo. intros VIS HP K AOK COST AUX SPB ST CEIL LO ERR MI TP SP16 AC A0 N.
    unfold AOPNEW_STACK, AMALLOC_STACK in LO. acb.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (EA : bv_unsigned tp + (-164) = AERRNO) by (subst tp; unfold AERRNO, ATP; rewrite unsigned_lit; lia).
    rewrite EA in ERR.

    eapply SRlift; [exact K | exact VIS | eapply (opnew_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n lo A0 N ST CEIL ltac:(lia) MI) |].
    intros msF1 mo1 K1 MP1 PO. cbv beta in PO. destruct PO as (m1 & V1 & MU & WM & MI1 & ST1 & FR).
    assert (FW : Forall (fun iv : Z * Z => aceil <= fst iv /\ snd iv <= bv_unsigned sp) (opnew_W (bv_unsigned sp))).
    { unfold opnew_W. constructor; [cbn; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1).
    { eapply Lrf; [exact HP| exact MU| exact WM|]. unfold opnew_W. constructor; [left; cbn; lia| constructor]. }
    assert (AUX1 : as_rauxv_ok H m1 B).
    { eapply (Laux LB); [exact AUX| exact MU| exact WM|]. unfold opnew_W. constructor; [left; cbn; lia| constructor]. }
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame; [exact AC| exact MU| exact WM|]. unfold opnew_W. constructor; [| constructor].
      apply aconst_ok_high; [| right; left]; acb; unfold sh, AIMG_TOP, ASHADOW_BASE in *; lia. }
    assert (ERR1 : rw_cells asegs m1 AERRNO [C4 errv]).
    { eapply (rw_cells_transport asegs _ m m1); [exact ERR| exact MU| exact WM|]. unfold opnew_W, AERRNO, ATP. cbn. lia. }
    pose proof (apres_of_munch0 s LB (bv_unsigned sp) _ m m m1 HP MU WM FW) as PRES1.

    eapply SRseq.
    { unfold malloc_stmt, malloc_stmt_at in Lmalloc.
      eapply (Lmalloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF1 m1 s LB n lo B errv mo1 []);
        [ exact V1| exact HP1| exact K1| exact AOK| exact COST| exact AUX1| rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; exact ST1| exact CEIL| rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
        | rewrite EA; exact ERR1| exact MI1| exact TP
        | rewrite unsigned_lit by lia; rewrite <- Z.add_mod_idemp_l, SP16 by lia; reflexivity| exact AC1
        | apply (proj1 Lch); rewrite unsigned_lit by lia; left; lia
        | cbn [map]; rewrite unsigned_lit by (unfold ARA_OPNEW; lia); exact Ltr
        | reflexivity| exact N]. }

    intros [msF2 mo2] PO. unfold malloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & bj & p & s' &
                    V2 & K2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & BR & HP2 & BLK & ADN & AC2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -16)) in ST2, HPRES by lia.
    pose proof BR as (BA & _ & _ & _ & BHI & _).
    apply (apres_rw_cells H _ _ _ _ _ _ HPRES) in FR; [| left; cbn; lia].
    eapply SRlift; [exact K2 | exact V2 | |].
    { eapply (opnew_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ra s0 F fc m2 A lo);
        rewrite ?unsigned_lit by lia; [lia| | exact ST2| lia| exact FR| lia| exact MI2].
      rewrite Z.sub_add. reflexivity. }
    intros msF3 mo3 K3 MP3 PO. cbv beta in PO. destruct PO as [V3 ST3].
    rewrite (unsigned_lit (bv_unsigned sp + -16)) in V3, ST3 by lia.
    replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) in V3, ST3 by lia. rewrite Z_to_bv_bv_unsigned in V3.
    apply SRdone. unfold malloc_post.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, bj, p, s'.
    split; [exact V3|]. split; [exact K3|]. split; [exact (MPtrans _ _ _ MP1 (MPtrans _ _ _ MP2 MP3))|].
    split; [exact MI2|]. split; [exact ST3|]. split; [exact ERR2|]. split; [exact AUX2|].
    split; [| split; [exact BR| split; [exact HP2| split; [exact BLK| split; [exact ADN| split; [exact AC2| exact AL2]]]]]].
    eapply apres_trans0; [exact PRES1|]. eapply apres_weaken_sp; [exact HPRES| lia].
  Qed.

End Stubs.
