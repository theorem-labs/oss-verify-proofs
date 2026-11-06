(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_20088_210bc BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkReduce BigModel BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreSpecs L5KnP L5ParseArith L5ParseKit L5ParseSpecs L5Bytes L5E1A L5E1B L5E1C L5StrctorKit L5StrctorTail L5StrctorMid2 L5StrctorMid L5StrctorHead.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module L5STR.
Import L5CS L5PS L5E1 L5E1B L5E1C L5STRK L5STRT L5STRH.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_2.
Context {SCFG_P : ScfgP}.

Ltac uscr := unfold STRCTOR_SCR, TOBIG_SCR, DETAIL_SCR, ADDD_SCR, MUL10_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis LYX : layoutx L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis Htb3 : tobig3_spec L HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L.
Let IMGLO := IMGLO L LY. Let IMGHI := IMGHI L LY. Let ERR := ERR L LY. Let ERRNO_LO := ERRNO_LO L LY.
Let credit_ok_mono := credit_ok_mono L. Let debit_mono := debit_mono L.
Let hpres_of_core := hpres_of_core L. Let hi_heap_clientx := hi_heap_clientx L HI LY LYX HIok.
Let stat_keep_hpres := stat_keep_hpres L LY. Let defined_across := defined_across L LY. Let hpres_W_mono := hpres_W_mono L.
Let e1_head := e1_head L HI LY LYX HIok.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem strctor_ok : strctor_spec L HI.
Proof.
  intros fx R M model K LB cr o so sp fbo s gd fl av uid rnd canary hw HH MOK HK0 H10 H11 Hlen SR CRED CR160 CR41 H1 H2 H3 H4 STK Ufb Hfbo Ao Olo Ohi WO
         Aso SOlo SOhi APso STR ES AVTOP KN KE.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). uscr.
  change (32 + (16 + (96 + (96 + (64 + (64 + (64 + (16 + 8224)))))))) with 8672 in *.
  pose proof (L5PK.lb_wf_of_heap L HI LB cr M _ HIok HH) as LBWF.
  rewrite L5CoreKit.L5K.rl10 in H10. rewrite L5CoreKit.L5K.rl11 in H11. rewrite L5CoreKit.L5K.rl1 in H1. rewrite L5CoreKit.L5K.rl2 in H2.
  rewrite L5CoreKit.L5K.rl3 in H3. rewrite L5CoreKit.L5K.rl4 in H4.
  assert (WR32: L5.writable RSEGS M (sp - 32) 32).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  set (ds := snd (split_sign s)) in *. set (neg := fst (split_sign s)) in *.
  assert (LDS: (length ds <= length s)%nat). { subst ds. unfold split_sign. destruct s as [|c t]. cbn; lia. destruct (c =? 45); cbn; lia. }
  (* [comment removed for export] *)
  assert (STEP1: exists (fx1 : FPState) R1 M1 (pch : Z),
     msteps RSEGS (st fx R STRCTOR M) (st fx1 R1 TOBIG3 M1)
     /\ (forall i, In i KS_S1S -> getr R1 (reg i) = getr R (reg i))
     /\ getr R1 (reg 1) = Z_to_bv 64 TB3RET /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 32)
     /\ getr R1 (reg 10) = Z_to_bv 64 pch /\ getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat (length s)) /\ getr R1 (reg 12) = Z_to_bv 64 o
     /\ L5.u64_at RSEGS M1 (o + 24) 0 /\ L5.u64_at RSEGS M1 (o + 16) 0 /\ L5.u64_at RSEGS M1 (o + 8) 0 /\ L5.u8_at RSEGS M1 o (Z.land fbo 252)
     /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
     /\ L5.u64_at RSEGS M1 (sp - 8) STRCTOR_RET
     /\ (forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> ~ (o <= bv_unsigned x < o + 32) -> M1 x = M x) /\ mem_grows M M1
     /\ L5.bytes_at RSEGS M1 pch s /\ 4096 <= pch /\ pch + Z.of_nat (length s) <= 2 ^ 47
     /\ digits_at L LB (sp - 32) pch (length s) /\ (pch + Z.of_nat (length s) <= o \/ o + 32 <= pch)).
  { destruct STR as [SS|(w0 & pd & SL & INB & W0 & Hw0)].
    - (* [comment removed for export] *)
      destruct SS as (L22 & B0 & BY & _).
      destruct (ps1s_conc fx R M sp o so fbo (2 * Z.of_nat (length s)) H2 H10 H11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 WR32 WO Ufb
                  ltac:(lia) B0 ltac:(lia) (land1_even (Z.of_nat (length s)) ltac:(lia)) ltac:(lia) Ao ltac:(lia) Aso ltac:(lia) ltac:(lia) ltac:(lia))
        as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & C24 & C16 & C8 & Cfb & F24 & F16 & F8 & FR1 & GR1).
      exists fx1, R1, M1, (so + 1). split. unfold STRCTOR, TOBIG3. exact MS1. split. exact K1. split. exact R1_1. split. exact R1_2. split. exact R1_10.
      split. { rewrite R1_11. f_equal. rewrite Z.mul_comm. apply Z.div_mul. lia. } split. exact R1_12.
      split. exact C24. split. exact C16. split. exact C8. split. rewrite Z.add_0_r in Cfb. exact Cfb. split. exact F24. split. exact F16.
      split. { rewrite H1, BG.unsigned_lit in F8. exact F8. unfold STRCTOR_RET. lia. }
      split. { intros x Hx Hy. apply FR1; lia. } split. exact GR1.
      split. { eapply (L5C.bytes_at_agree RSEGS M M1). 2: lia. 2: lia. 2: exact BY. intros i Hi. apply FR1; rewrite BG.unsigned_lit by lia; lia. }
      split. lia. split. lia. split. { right. right. left. split. lia. lia. } lia.
    - (* [comment removed for export] *)
      destruct SL as (TB & U0 & U8 & U16 & BY & _). pose proof (LBWF (pd, w0 - 1) INB) as (Wq0 & W1 & W2). cbn in Wq0, W1, W2. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in W1.
      pose proof (L5B.u8_of_u64 RSEGS M so w0 0 ltac:(lia) ltac:(lia) Hw0 ltac:(lia) U0) as B0. rewrite Z.add_0_r in B0.
      destruct (ps1l_conc fx R M sp o so fbo (L5B.byte_k w0 0) (Z.of_nat (length s)) pd H2 H10 H11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold L5B.byte_k; pose proof (Z.mod_pos_bound (Z.shiftr w0 (8 * Z.of_nat 0)) 256 ltac:(lia)); lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 WR32 WO Ufb
                  ltac:(lia) B0 ltac:(unfold L5B.byte_k; pose proof (Z.mod_pos_bound (Z.shiftr w0 (8 * Z.of_nat 0)) 256 ltac:(lia)); lia) (land1_odd_byte w0 ltac:(lia) TB) U8 U16
                  ltac:(lia) Ao ltac:(lia) Aso ltac:(lia) ltac:(lia) ltac:(lia))
        as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & C24 & C16 & C8 & Cfb & F24 & F16 & F8 & FR1 & GR1).
      exists fx1, R1, M1, pd. split. unfold STRCTOR, TOBIG3. exact MS1. split. exact K1. split. exact R1_1. split. exact R1_2. split. exact R1_10.
      split. exact R1_11. split. exact R1_12.
      split. exact C24. split. exact C16. split. exact C8. split. rewrite Z.add_0_r in Cfb. exact Cfb. split. exact F24. split. exact F16.
      split. { rewrite H1, BG.unsigned_lit in F8. exact F8. unfold STRCTOR_RET. lia. }
      split. { intros x Hx Hy. apply FR1; lia. } split. exact GR1.
      split. { eapply (L5C.bytes_at_agree RSEGS M M1). 2: lia. 2: lia. 2: exact BY. intros i Hi. apply FR1; rewrite BG.unsigned_lit by lia; lia. }
      split. lia. split. lia. split. { right. left. exists pd, (w0 - 1). split. exact INB. lia. } lia. }
  destruct STEP1 as (fx1 & R1 & M1 & pch & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & C24 & C16 & C8 & Cfb & F24 & F16 & F8 & FR1 & GR1 & BY1 & PLO & PHI & DAT & APO).
  clear STR.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  assert (AG1: forall a k, (a + k <= sp - 32 \/ sp <= a) -> (a + k <= o \/ o + 32 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M1 a k).
  { intros a k H1a H2a Ha Hk i Hi. apply FR1; rewrite BG.unsigned_lit by lia; lia. }
  assert (R1i: forall i, In i KS_S1S -> getr R1 (reg i) = getr R (reg i)) by exact K1.
  assert (ES1: e1_statics M1 gd fl av uid rnd canary hw).
  { eapply e1_statics_keep. exact ES. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha.
    destruct ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _). apply FR1; rewrite BG.unsigned_lit by lia; lia. }
  assert (HH1: hi_heap HI LB cr M1 (m_vmmaps model)).
  { eapply hi_heap_clientx. exact HH. lia. 2: exact GR1. intros a Ha.
    destruct (Z_lt_le_dec a (sp - 32)) as [L1|G1]; [destruct (Z_lt_le_dec a o) as [L2|G2]; [left| destruct (Z_lt_le_dec a (o + 32)) as [L3|G3]; [right; left; lia| left]] | destruct (Z_lt_le_dec a sp) as [L4|G4]; [right; left; lia | destruct (Z_lt_le_dec a o) as [L2|G2]; [left| destruct (Z_lt_le_dec a (o + 32)) as [L3|G3]; [right; left; lia| left]]]].
    all: apply FR1; rewrite BG.unsigned_lit by lia; lia. }
  (* [comment removed for export] *)
  assert (HP1: L5C.hpres L LB sp STRCTOR_SCR [(o, 32)] M M1).
  { apply L5C.hpres_intro.
    - intros a (Ha & CA & NE & OW). apply FR1; rewrite BG.unsigned_lit by lia. 2: { intros Hin. apply (OW (o, 32)). left; reflexivity. unfold L5.in_rng; cbn. lia. }
      destruct CA as [IB|[[S1 S2]|IM]]. destruct IB as (bb & Hb & Hin). pose proof (LBWF bb Hb) as (Q0 & Q1 & Q2). lia. uscr. lia. rewrite (ly_img_hi L LY) in IM. lia.
    - uscr. intros i Hi. apply GR1. apply DEF. lia.
    - intros a _ _ _ Hd. apply GR1. exact Hd. }
  (* [comment removed for export] *)
  eapply (Htb3 fx1 R1 M1 model K LB cr pch o (sp - 32) TB3RET (Z.land fbo 252) s).
  - exact HH1.
  - exact MOK.
  - exact HK0.
  - rewrite L5CoreKit.L5K.rl10. exact R1_10.
  - rewrite L5CoreKit.L5K.rl11. exact R1_11.
  - rewrite L5CoreKit.L5K.rl12. exact R1_12.
  - exact Hlen.
  - exact CRED.
  - rewrite L5CoreKit.L5K.rl1. exact R1_1.
  - apply ra_ok_lit. unfold TB3RET; lia. reflexivity.
  - rewrite L5CoreKit.L5K.rl2. exact R1_2.
  - rewrite L5CoreKit.L5K.rl3, (R1i 3%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H3.
  - rewrite L5CoreKit.L5K.rl4, (R1i 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
  - split. { replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    uscr. split. lia. split. lia. split. lia. eapply L5.defined_grows. exact GR1. eapply L5.defined_sub. exact DEF. lia. lia.
  - (* [comment removed for export] *)
    unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st Z.of_nat]. split. exact Cfb. split. apply L5PA.land252_range. lia. split. exact C8.
    split. { pose proof (land252_3 fbo Hfbo) as X. apply (f_equal (fun x => Z.testbit x 0)) in X. rewrite Z.land_spec in X. change (Z.testbit 3 0) with true in X.
             rewrite Bool.andb_true_r in X. rewrite X. reflexivity. }
    split. exact C16. split. exact C24. repeat split; lia.
  - apply land252_3. lia.
  - exact Ao.
  - lia.
  - exact Ohi.
  - eapply L5.writable_grows. exact GR1. exact WO.
  - exact BY1.
  - exact SR.
  - exact PLO.
  - exact PHI.
  - exact DAT.
  - exact APO.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 LB2 cr2 TP MBV2 HH2.
    unfold tobig_post in TP. cbv zeta in TP. change (snd (split_sign s)) with ds in TP. change (fst (split_sign s)) with neg in TP.
    destruct TP as (RP2 & TPc).
    assert (MOK2: model_ok model2).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV2); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV2); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV2); exact Y3]]. }
    pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    pose proof (RP2 2%bv ltac:(inl)) as P2. rewrite L5CoreKit.L5K.rl2 in P2.
    assert (R2_2: getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite P2; exact R1_2).
    assert (R2i: forall i, In i [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg i) = getr R (reg i)).
    { intros i Hi. rewrite (L5CoreKit.L5K.regs_preserved_index R1 R2 i RP2) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H').
      apply R1i. pose proof Hi as H'; L5CoreKit.L5K.inlist H'. }
    destruct TPc as [(PAR & R2_11 & PP)|(NP & R2_11 & NPP)].
    + (* [comment removed for export] *)
      pose proof PP as (st' & OB2 & OL2 & ST2 & CR2 & HPt).
      assert (AG2: forall a k, sp - 32 <= a -> a + k <= sp -> L5C.agree_on M1 M2 a k).
      { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HPt. uscr; lia. uscr; lia. lia. lia.
        intros i Hi r' [<-|[]]. unfold L5.in_rng; cbn. lia. }
      assert (E8: L5.u64_at RSEGS M2 (sp - 8) STRCTOR_RET). { eapply (L5C.u64_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact F8. }
      assert (E16: L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (reg 8)))). { eapply (L5C.u64_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact F16. }
      assert (E24: L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (reg 9)))). { eapply (L5C.u64_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact F24. }
      rewrite L5CoreKit.L5K.rl11 in R2_11.
      destruct (ps2_conc fx2 R2 M2 sp STRCTOR_RET (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) R2_2 R2_11 ltac:(lia) ltac:(unfold STRCTOR_RET; lia)
                  (wrange _) (wrange _) ltac:(lia) A16 E8 E16 E24)
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & FR3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2.
      { eapply msteps_trans. exact MS3. apply ret_sret. exact R3_1. unfold STRCTOR_RET; lia. reflexivity. }
      assert (AG3: forall a k, L5C.agree_on M2 M3 a k) by (intros a k i Hi; apply FR3).
      apply (KN fx3 R3 M3 model2 LB2 cr2).
      * split.
        { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
          destruct Hi as [<-|Hi]. { rewrite R3_2, H2. reflexivity. }
          destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply L5KP.In_of_existsb; reflexivity). apply R2i. inl. }
          destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply L5KP.In_of_existsb; reflexivity). apply R2i. inl. }
          destruct Hi as [<-|Hi]. { rewrite R3_8. apply lit_of_word. }
          destruct Hi as [<-|Hi]. { rewrite R3_9. apply lit_of_word. }
          assert (G: forall j, In j [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
          { intros j Hj. assert (A3: In j KS_S2) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
            rewrite (K3 j A3). apply R2i. pose proof Hj as H'. L5CoreKit.L5K.inlist H'. }
          apply G. L5CoreKit.L5K.inlist Hi. }
        split. exact PAR.
        unfold parse_post. cbv zeta. change (snd (split_sign s)) with ds. change (fst (split_sign s)) with neg. exists st'. split. { eapply (L5C.big_at_agree RSEGS M2 M3). apply AG3. lia. lia. exact OB2. }
        split. { eapply (obj_limbs_agree M2 M3). exact OL2. cbn [L5.bo_st]. intros cap q E. subst st'.
                 destruct OB2 as (_ & _ & _ & (_ & _ & _ & X4 & X5 & X6 & X7 & X8)). cbn [L5.bo_len] in X4. rewrite wlist_length. split. apply AG3. lia. }
        split. { destruct st' as [v0 v1|cap q]. exact ST2. destruct ST2 as (S1 & S2 & S3 & (S4 & S5 & S6)). split. exact S1. split. exact S2. split. exact S3.
                 split. exact S4. split. exact S5. eapply (L5C.defined_agree M2 M3). apply AG3. exact S6. }
        split. exact CR2.
        assert (HP12: L5C.hpres L LB sp STRCTOR_SCR [(o, 32)] M M2).
        { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp STRCTOR_SCR [(o,32)] (sp - 32) TOBIG_SCR [(o,32)] M M1 M2). exact LBWF. uscr; lia. lia. exact HP1. exact HPt. apply L5PK.lb_sub_refl. uscr; lia. lia. uscr; lia.
          constructor. eapply L5PK.wr_declared. left; reflexivity. lia. lia. constructor. }
        eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp STRCTOR_SCR [(o,32)] M M2 M3 []). exact LBWF. uscr; lia. exact HP12. intros x Hx. apply FR3. exact GR3. constructor.
      * eapply e1_statics_keep. 2: { intros a Ha. apply FR3. } eapply e1_statics_keep. exact ES1.
        destruct ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
        apply (stat_keep_hpres av LB (sp - 32) TOBIG_SCR [(o, 32)] M1 M2 HPt). uscr; lia. uscr; lia. lia. lia. lia.
        intros i Hi r' [<-|[]]. unfold L5.in_rng; cbn. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Hi. lia.
      * exact MBV2.
      * eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB2 cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia.
        intros x Hx. apply FR3. exact GR3. constructor.
    + (* [comment removed for export] *)
      destruct NPP as (ELB & OB2 & CR2 & HPt). subst LB2.
      destruct ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
      assert (AG2: forall a k, sp - 32 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M1 M2 a k).
      { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HPt. uscr; lia. uscr; lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
      assert (STAT2: forall a, stat_rd av a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { apply (stat_keep_hpres av LB (sp - 32) TOBIG_SCR [] M1 M2 HPt). uscr; lia. uscr; lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
      pose proof (e1_statics_keep M1 M2 gd fl av uid rnd canary hw ES1 STAT2) as ES2.
      assert (HP02: L5C.hpres L LB sp STRCTOR_SCR [(o, 32)] M M2).
      { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp STRCTOR_SCR [(o,32)] (sp - 32) TOBIG_SCR [] M M1 M2). exact LBWF. uscr; lia. lia. exact HP1. exact HPt. apply L5PK.lb_sub_refl. uscr; lia. lia. uscr; lia. constructor. }
      pose proof (L5C.hpres_defined L LB sp STRCTOR_SCR [(o,32)] M M2 HP02) as DEF2.
      set (Wf := [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)]).
      assert (HQ2: L5C.hpres L LB sp STRCTOR_SCR Wf M M2).
      { eapply hpres_W_mono. exact HP02. intros a Ha r' [<-|[]]. apply Ha. left; reflexivity. }
      assert (FRA0: forall Ma Mb, (L5.u64_at RSEGS Ma (sp - 8) STRCTOR_RET /\ L5.u64_at RSEGS Ma (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS Ma (sp - 24) (bv_unsigned (getr R (reg 9)))
                                    /\ L5.big_at RSEGS Ma o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))) ->
                 L5C.agree_on Ma Mb (sp - 32) 32 -> L5C.agree_on Ma Mb o 32 ->
                 (L5.u64_at RSEGS Mb (sp - 8) STRCTOR_RET /\ L5.u64_at RSEGS Mb (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS Mb (sp - 24) (bv_unsigned (getr R (reg 9)))
                  /\ L5.big_at RSEGS Mb o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0)))).
      { intros Ma Mb (Y1 & Y2 & Y3 & Y4) AGs AGo. split. eapply (L5C.u64_at_agree RSEGS Ma Mb). eapply L5C.agree_on_sub. exact AGs. lia. lia. lia. lia. exact Y1.
        split. eapply (L5C.u64_at_agree RSEGS Ma Mb). eapply L5C.agree_on_sub. exact AGs. lia. lia. lia. lia. exact Y2.
        split. eapply (L5C.u64_at_agree RSEGS Ma Mb). eapply L5C.agree_on_sub. exact AGs. lia. lia. lia. lia. exact Y3.
        eapply (L5C.big_at_agree RSEGS Ma Mb). exact AGo. lia. lia. exact Y4. }
      assert (PQ2: L5.u64_at RSEGS M2 (sp - 8) STRCTOR_RET /\ L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (reg 9)))
                  /\ L5.big_at RSEGS M2 o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))).
      { split. eapply (L5C.u64_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact F8. split. eapply (L5C.u64_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact F16.
        split. eapply (L5C.u64_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact F24. exact OB2. }
      rewrite L5CoreKit.L5K.rl11 in R2_11.
      destruct (ps3_conc fx2 R2 M2 sp R2_2 R2_11 ltac:(lia) ltac:(lia) A16) as (fx3 & R3 & M3 & MS3 & K3 & R3_2 & R3_9 & R3_10 & FR3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      assert (AG3: forall a k, L5C.agree_on M2 M3 a k) by (intros a k i Hi; apply FR3).
      assert (R3i: forall i, In i [3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg i) = getr R (reg i)).
      { intros i Hi. rewrite (K3 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply R2i. pose proof Hi as H'. L5CoreKit.L5K.inlist H'. }
      pose proof ES2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC1 & IC2 & IC3).
      assert (DEF3: L5.defined M3 (sp - STRCTOR_SCR) STRCTOR_SCR) by (eapply L5.defined_grows; [exact GR3 | exact DEF2]).
      assert (GPv: GP = 67584) by reflexivity. assert (TPv: TP = 459832) by reflexivity.
      assert (ES3: e1_statics M3 gd fl av uid rnd canary hw). { eapply e1_statics_keep. exact ES2. intros a Ha. apply FR3. }
      assert (HH3: hi_heap HI LB cr2 M3 (m_vmmaps model2)).
      { eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia. intros x Hx. apply FR3. exact GR3. constructor. }
      assert (HQ3: L5C.hpres L LB sp STRCTOR_SCR Wf M M3).
      { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp STRCTOR_SCR Wf M M2 M3 []). exact LBWF. uscr; lia. exact HQ2. intros x Hx. apply FR3. exact GR3. constructor. }
      pose proof (FRA0 M2 M3 PQ2 (AG3 _ _) (AG3 _ _)) as P3.
      change (32 + (16 + (96 + (96 + (64 + (64 + (64 + (16 + 8224)))))))) with 8672 in DEF3.
      eapply (e1_head fx3 R R3 M M3 model model2 K LB cr cr2 o sp fbo s gd fl av uid rnd canary hw HK0 NP H2 H3 H4 A16 ltac:(lia) SHI STOP Olo Ohi Hfbo AVTOP LBWF
                CR2 CR160 CR41 R3_2 R3_9 R3_10 R3i DEF3 ES3 HH3 MOK2 MBV2 P3 HQ3 KE).
Qed.

End WithHeap.
End SCFG_2.

End L5STR.
