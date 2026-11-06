(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_201fc_21084 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkDivBaseU BigModel BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5KnP L5ParseArith L5ParseKit L5ParseSpecsU L5Bytes L5E1AU L5E1BU L5E1CU L5StrctorKitU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module L5STRTU.
Import L5CSU L5PSU L5E1U L5E1BU L5E1CU L5STRKU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
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
(* [comment removed for export] *)
Lemma e1_tail (fx10 : FPState) R R10 M M10 model model9 K LB cr cr2 (o sp fbo : Z) s fl (av uid rnd canary hw A ref : Z) :
  let ds := snd (split_sign s) in
  K [] -> no_parse s ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  sp mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 8688 <= sp -> sp <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> sp <= o -> o + 32 <= hl_sptop L -> 0 <= fbo < 256 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  (* [comment removed for export] *)
  getr R10 (reg 1) = Z_to_bv 64 134328 -> getr R10 (reg 2) = Z_to_bv 64 (sp - 32) -> getr R10 (reg 10) = Z_to_bv 64 (A + 128) ->
  getr R10 (reg 11) = Z_to_bv 64 388648 -> getr R10 (reg 12) = Z_to_bv 64 269892 ->
  (forall i, In i [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R10 (reg i) = getr R (reg i)) ->
  (* [comment removed for export] *)
  L5.defined M10 (sp - 8688) 8688 -> L5.defined M10 A 160 -> L5.defined M10 ref 41 ->
  e1_statics M10 true fl av uid rnd canary hw ->
  L5.u64_at RSEGS M10 (sp - 8) STRCTOR_RET -> L5.u64_at RSEGS M10 (sp - 16) (bv_unsigned (getr R (reg 8))) -> L5.u64_at RSEGS M10 (sp - 24) (bv_unsigned (getr R (reg 9))) ->
  L5.big_at RSEGS M10 o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0)) ->
  L5.u64_at RSEGS M10 (A + 128 + 24) 393560 -> L5.u32_at RSEGS M10 (A + 128 + 16) 22 -> L5.u64_at RSEGS M10 (A + 128 + 0) 388624 -> L5.u64_at RSEGS M10 (A + 128 + 8) (ref + 24) ->
  L5.u64_at RSEGS M10 (ref + 24) 2334106421097295433 -> L5.u64_at RSEGS M10 (ref + 32) 8389754676633367137 -> L5.u8_at RSEGS M10 (ref + 40) 0 ->
  L5.u32_at RSEGS M10 (ref + 16) 0 -> L5.u64_at RSEGS M10 (ref + 8) 16 -> L5.u64_at RSEGS M10 (ref + 0) 16 ->
  (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M10 (A + i) 0) -> (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M10 (A + 48 + i) 0) ->
  (* [comment removed for export] *)
  hi_heap HI ((ref, 41) :: (A, 160) :: LB) (debit L (debit L cr2 160) 41) M10 (m_vmmaps model9) -> model_ok model9 -> model_but_vm model model9 ->
  4096 <= A -> (A + 160 <= 0x10000 \/ 0x92000 <= A) -> A mod 16 = 0 -> A + 160 <= hl_sptop L - 8388608 -> blocks_apart A 160 LB ->
  4096 <= ref -> (ref + 41 <= 0x10000 \/ 0x92000 <= ref) -> ref mod 16 = 0 -> ref + 41 <= hl_sptop L - 8388608 -> blocks_apart ref 41 ((A, 160) :: LB) ->
  credit_le (parse_debit L cr (length ds)) cr2 ->
  L5C.hpres L LB sp STRCTOR_SCR [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)] M M10 ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
      no_parse s -> e1_landing L LB cr M M' R R' o sp fbo (length ds) av uid rnd canary hw LB' cr' ->
      model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (cfg R' E1_LANDING M' model') K) ->
  srealizes RSEGS SCFG (cfg R10 THROW M10 model9) K.
Proof.
  intros ds HK0 NP H2 H3 H4 A16 SLO SHI STOP Olo Ohi Hfbo AVTOP LBWF R10_1 R10_2 R10_10 R10_11 R10_12 R10i DEF10 DEFA10 DEFr10 ES10 F8 F16 F24 OB10
         O24 O16 O0 O8 W24 W32 W40 W16 W8 W0 Z0 Z48 HH10 MOK9 MBV09 BR0 BR1 BR2 BR4 BA RR0 RR1 RR2 RR4 BAr CR2 HP010 KE.
  pose proof MOK9 as (Mh9 & Ml9 & Mm9). assert (GPv: GP = 67584) by reflexivity. assert (TPv: TP = 462648) by reflexivity.
  pose proof ES10 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20).
  pose proof (auxv_cells M10 av uid rnd hw S13) as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S1, S2, S3, S4, S5, S6, S7, S8, S9.
  assert (WUW: L5.writable RSEGS M10 462433 6). { apply (writable_img M10 UW_FLAGS 6 wseg_uwflags); unfold UW_FLAGS; lia. }
  assert (WUC: L5.writable RSEGS M10 459776 4). { apply (writable_img M10 EH_UNCAUGHT 4 wseg_uncaught); unfold EH_UNCAUGHT; lia. }
  (* [comment removed for export] *)
  assert (STEPT: exists (fx11 : FPState) R11 M11,
     msteps RSEGS (st fx10 R10 THROW M10) (st fx11 R11 E1_LANDING M11)
     /\ (forall i, In i KS_T0 -> getr R11 (reg i) = getr R10 (reg i))
     /\ getr R11 (reg 2) = Z_to_bv 64 (sp - 32 + 32) /\ getr R11 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) /\ getr R11 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9)))
     /\ getr R11 (reg 10) = Z_to_bv 64 (A + 128 - 32) /\ getr R11 (reg 11) = Z_to_bv 64 1
     /\ L5.u64_at RSEGS M11 (A + 128 - 8) (sp - 32 + 32) /\ L5.u64_at RSEGS M11 (A + 128 - 40) (A + 128) /\ L5.u64_at RSEGS M11 (A + 128 - 48) 133644
     /\ L5.u64_at RSEGS M11 (A + 128 - 56) 91856 /\ L5.u64_at RSEGS M11 (A + 128 - 64) 91995 /\ L5.u32_at RSEGS M11 (A + 128 - 68) 1
     /\ L5.u8_at RSEGS M11 (0 + 462436) 0 /\ L5.u8_at RSEGS M11 (0 + 462435) 1 /\ L5.u8_at RSEGS M11 (0 + 462438) 0 /\ L5.u8_at RSEGS M11 (0 + 462437) 1
     /\ L5.u64_at RSEGS M11 (A + 128 - 16) 0 /\ L5.u8_at RSEGS M11 (0 + 462434) 0 /\ L5.u8_at RSEGS M11 (0 + 462433) 1
     /\ L5.u64_at RSEGS M11 (A + 128 - 120) 1 /\ L5.u64_at RSEGS M11 (A + 128 - 24) 260436 /\ L5.u64_at RSEGS M11 (A + 128 - 32) 4849336966747728640
     /\ L5.u64_at RSEGS M11 (A + 128 - 88) 145512 /\ L5.u64_at RSEGS M11 (A + 128 - 104) 269892 /\ L5.u64_at RSEGS M11 (A + 128 - 112) 388648
     /\ L5.u64_at RSEGS M11 (A + 128 - 96) 145780 /\ L5.u32_at RSEGS M11 (0 + 459776) 1
     /\ (forall x : word, ~ (sp - 32 + -7984 <= bv_unsigned x < sp - 32 + -7984 + 7984) -> ~ (A + 128 + -120 <= bv_unsigned x < A + 128 + -120 + 40) ->
           ~ (A + 128 + -68 <= bv_unsigned x < A + 128 + -68 + 68) -> ~ (0 + 459776 <= bv_unsigned x < 0 + 459776 + 4) -> ~ (0 + 462433 <= bv_unsigned x < 0 + 462433 + 6) -> M11 x = M10 x)
     /\ mem_grows M10 M11).
  { destruct fl.
    - destruct S5 as (U0 & U1 & U2 & U3 & U4 & U5).
      destruct (e1tu_v1_conc fx10 R10 M10 (sp - 32) (A + 128) av canary uid rnd hw (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9)))
                  R10_1 R10_2 ltac:(rewrite (R10i 3%nat) by inl; rewrite H3, GPv; reflexivity) ltac:(rewrite (R10i 4%nat) by inl; rewrite H4, TPv; reflexivity)
                  R10_10 R10_11 R10_12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (wrange _) (wrange _) ltac:(lia)
                  ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                  ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF10| lia| lia] | lia | lia]) ltac:(eapply L5.defined_sub; [exact DEF10 | lia | lia])
                  ltac:(lia) ltac:(replace (A + 128) with (A + 8 * 16) by lia; rewrite Z_mod_plus_full; exact BR2)
                  ltac:(replace (A + 128 - 128) with A by lia; apply (L5C.writable_of_defined RSEGS); [exact DEFA10 | lia | lia]) ltac:(replace (A + 128 - 128) with A by lia; exact DEFA10)
                  ltac:(lia) S10 ltac:(right; lia) ltac:(left; lia) ltac:(left; lia) ltac:(lia) S18 S19 S20
                  ltac:(rewrite Z.add_0_l; exact S2) ltac:(rewrite Z.add_0_l; exact S8) ltac:(rewrite Z.add_0_l; exact S9)
                  X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 X18
                  ltac:(replace (sp - 32 + 24) with (sp - 8) by lia; exact F8) ltac:(replace (sp - 32 + 16) with (sp - 16) by lia; exact F16) ltac:(replace (sp - 32 + 8) with (sp - 24) by lia; exact F24)
                  ltac:(rewrite Z.add_0_l; exact U0) ltac:(rewrite Z.add_0_l; exact U1) ltac:(rewrite Z.add_0_l; exact U2) ltac:(rewrite Z.add_0_l; exact U3) ltac:(rewrite Z.add_0_l; exact U4) ltac:(rewrite Z.add_0_l; exact U5)
                  ltac:(rewrite Z.add_0_l; exact WUW) ltac:(rewrite Z.add_0_l; exact WUC))
        as (fx11 & R11 & M11 & MS11 & K11 & REST).
      exists fx11, R11, M11. split. unfold THROW, E1_LANDING. exact MS11. split. intros i Hi. apply K11. revert Hi. clear. intros Hi. exact Hi.
      decompose [and] REST. repeat split; assumption.
    - destruct S5 as (U0 & U2 & U4).
      destruct (e1tu_v0_conc fx10 R10 M10 (sp - 32) (A + 128) av canary uid rnd hw (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9)))
                  R10_1 R10_2 ltac:(rewrite (R10i 3%nat) by inl; rewrite H3, GPv; reflexivity) ltac:(rewrite (R10i 4%nat) by inl; rewrite H4, TPv; reflexivity)
                  R10_10 R10_11 R10_12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (wrange _) (wrange _) ltac:(lia)
                  ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                  ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF10| lia| lia] | lia | lia]) ltac:(eapply L5.defined_sub; [exact DEF10 | lia | lia])
                  ltac:(lia) ltac:(replace (A + 128) with (A + 8 * 16) by lia; rewrite Z_mod_plus_full; exact BR2)
                  ltac:(replace (A + 128 - 128) with A by lia; apply (L5C.writable_of_defined RSEGS); [exact DEFA10 | lia | lia]) ltac:(replace (A + 128 - 128) with A by lia; exact DEFA10)
                  ltac:(lia) S10 ltac:(right; lia) ltac:(left; lia) ltac:(left; lia) ltac:(lia) S18 S19 S20
                  ltac:(rewrite Z.add_0_l; exact S2) ltac:(rewrite Z.add_0_l; exact S8) ltac:(rewrite Z.add_0_l; exact S9)
                  X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 X18
                  ltac:(replace (sp - 32 + 24) with (sp - 8) by lia; exact F8) ltac:(replace (sp - 32 + 16) with (sp - 16) by lia; exact F16) ltac:(replace (sp - 32 + 8) with (sp - 24) by lia; exact F24)
                  ltac:(rewrite Z.add_0_l; exact U0) ltac:(rewrite Z.add_0_l; exact U2) ltac:(rewrite Z.add_0_l; exact U4)
                  ltac:(rewrite Z.add_0_l; exact WUW) ltac:(rewrite Z.add_0_l; exact WUC))
        as (fx11 & R11 & M11 & MS11 & K11 & REST).
      exists fx11, R11, M11. split. unfold THROW, E1_LANDING. exact MS11. split. exact K11.
      decompose [and] REST. repeat split; assumption. }
  clear S5.
  destruct STEPT as (fx11 & R11 & M11 & MS11 & K11 & R11_2 & R11_8 & R11_9 & R11_10 & R11_11 & T8' & T40 & T48 & T56 & T64 & T68 & V28 & V27 & V30 & V29 & T16 & V26 & V25
                     & T120 & T24 & T32 & T88 & T104 & T112 & T96 & VUC & FR11 & GR11).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh9. exact Ml9. exact MS11.
  assert (AG11: forall a k, (a + k <= sp - 8016 \/ sp - 32 <= a) -> (a + k <= A + 8 \/ A + 48 <= a) -> (a + k <= A + 60 \/ A + 128 <= a) ->
                (a + k <= 459776 \/ 459780 <= a) -> (a + k <= 462433 \/ 462439 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M10 M11 a k).
  { intros a k H1a H2a H3a H4a H5a Ha Hk i Hi. apply FR11; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (BAr (A, 160) ltac:(left; reflexivity)) as RA. cbn in RA.
  Ltac t64 AG H := eapply (L5C.u64_at_agree RSEGS); [apply AG; lia | lia | lia | exact H].
  apply (KE fx11 R11 M11 model9 ((ref, 41) :: (A, 160) :: LB) (debit L (debit L cr2 160) 41) NP).
  - unfold e1_landing. exists (A + 128), ref.
    split. { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
      destruct Hi as [<-|Hi]. { rewrite R11_2, H2. f_equal. lia. }
      destruct Hi as [<-|Hi]. { rewrite (K11 3%nat) by (apply L5KP.In_of_existsb; reflexivity). apply R10i. inl. }
      destruct Hi as [<-|Hi]. { rewrite (K11 4%nat) by (apply L5KP.In_of_existsb; reflexivity). apply R10i. inl. }
      destruct Hi as [<-|Hi]. { rewrite R11_8. apply lit_of_word. }
      destruct Hi as [<-|Hi]. { rewrite R11_9. apply lit_of_word. }
      assert (G: forall j, In j [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R11 (reg j) = getr R (reg j)).
      { intros j Hj. assert (A3: In j KS_T0) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H'). rewrite (K11 j A3). apply R10i. pose proof Hj as H'. L5CoreKit.L5K.inlist H'. }
      apply G. L5CoreKit.L5K.inlist Hi. }
    split. { rewrite L5CoreKit.L5K.rl10. exact R11_10. }
    split. { rewrite L5CoreKit.L5K.rl11. exact R11_11. }
    split. { replace (A + 128 - 128) with A by lia. reflexivity. }
    split. { apply debit_mono. apply debit_mono. exact CR2. }
    split. { replace (A + 128 - 128) with A by lia. split. { split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. exact BR2. split. lia. lia. }
             split. exact BA. eapply L5.defined_grows. exact GR11. exact DEFA10. }
    split. { replace (A + 128 - 128) with A by lia. split. { split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact RR1. split. exact RR2. split. lia. lia. }
             split. exact BAr. eapply L5.defined_grows. exact GR11. exact DEFr10. }
    split. { (* [comment removed for export] *)
      unfold e1_exception_at, TI_SYSTEM_ERROR, DTOR_SYSTEM_ERROR, VT_SYSTEM_ERROR, SYSCAT_OBJ, UNEXPECTED_H, TERMINATE_H, E1_ACTION, E1_LSDA, E1_LANDING, UE_CLEANUP, EXC_CLASS.
      split. { intros i Hi. eapply (L5C.u8_at_agree RSEGS M10 M11). apply AG11; lia. lia. lia. replace (A + 128 - 128 + i) with (A + i) by lia. apply Z0. lia. }
      split. replace (A + 128 - 120) with (A + 128 - 120) by lia; exact T120.
      split. exact T112. split. exact T104. split. exact T96. split. exact T88.
      split. { intros i Hi. eapply (L5C.u8_at_agree RSEGS M10 M11). apply AG11; lia. lia. lia. replace (A + 128 - 80 + i) with (A + 48 + i) by lia. apply Z48. lia. }
      split. exact T68. split. exact T64. split. exact T56. split. exact T48. split. exact T40. split. exact T32. split. exact T24. split. exact T16.
      split. { replace (sp - 32 + 32) with sp in T8' by lia. exact T8'. }
      split. { replace (A + 128) with (A + 128 + 0) at 1 by lia. t64 AG11 O0. } split. t64 AG11 O8.
      split. { eapply u32_at_agree. apply AG11; lia. lia. lia. exact O16. } split. t64 AG11 O24.
      split. { replace ref with (ref + 0) at 1 by lia. t64 AG11 W0. } split. t64 AG11 W8.
      split. { eapply u32_at_agree. apply AG11; lia. lia. lia. exact W16. }
      assert (J17: rdn RSEGS M11 (Z_to_bv 64 (ref + 24)) 17 = Some (word_to_le_bytes 8 (Z_to_bv 64 2334106421097295433) ++ word_to_le_bytes 8 (Z_to_bv 64 8389754676633367137) ++ [Z_to_bv 8 0])).
      { change 17%nat with (8 + (8 + 1))%nat. apply (L5B.rdn_join RSEGS M11 8). lia. lia. { pose proof (L5C.u64_at_agree RSEGS M10 M11 (ref + 24) _ ltac:(apply AG11; lia) ltac:(lia) ltac:(lia) W24) as X. exact X. }
        replace (ref + 24 + Z.of_nat 8) with (ref + 32) by lia. apply (L5B.rdn_join RSEGS M11 8). lia. lia.
        { pose proof (L5C.u64_at_agree RSEGS M10 M11 (ref + 32) _ ltac:(apply AG11; lia) ltac:(lia) ltac:(lia) W32) as X. exact X. }
        replace (ref + 32 + Z.of_nat 8) with (ref + 40) by lia.
        pose proof (L5C.u8_at_agree RSEGS M10 M11 (ref + 40) 0 ltac:(apply AG11; lia) ltac:(lia) ltac:(lia) W40) as X. exact X. }
      pose proof (L5C.rdn_bytes_at RSEGS M11 (word_to_le_bytes 8 (Z_to_bv 64 2334106421097295433) ++ word_to_le_bytes 8 (Z_to_bv 64 8389754676633367137) ++ [Z_to_bv 8 0]) (ref + 24)
                    ltac:(lia) ltac:(cbn; lia) J17) as BY.
      replace (map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 2334106421097295433) ++ word_to_le_bytes 8 (Z_to_bv 64 8389754676633367137) ++ [Z_to_bv 8 0]))
         with [73;110;118;97;108;105;100;32;97;114;103;117;109;101;110;116;0] in BY by (vm_compute; reflexivity).
      exact BY. }
    split. { (* [comment removed for export] *)
      unfold e1_statics_landed, EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP.
      split. t64 AG11 S1. split. rewrite Z.add_0_l in VUC; exact VUC.
      split. { eapply (L5C.u8_at_agree RSEGS M10 M11). apply AG11; lia. lia. lia. exact S3. }
      split. { eapply (L5C.u8_at_agree RSEGS M10 M11). apply AG11; lia. lia. lia. exact S4. }
      rewrite !Z.add_0_l in V25, V26, V27, V28, V29, V30.
      split. exact V25. split. exact V26. split. exact V27. split. exact V28. split. exact V29. split. exact V30.
      split. t64 AG11 S6. split. t64 AG11 S7. split. t64 AG11 S8. split. t64 AG11 S9.
      split. { intros j Hj. eapply (L5C.u64_at_agree RSEGS M10 M11). apply AG11; lia. lia. lia. apply S13. exact Hj. }
      assert (AGI: L5C.agree_on M10 M11 65536 (393568 - 65536)) by (apply AG11; lia).
      split. { intros i Hi. rewrite (AGI i) by lia. apply S18. exact Hi. }
      split. { intros i Hi. rewrite (AGI i) by lia. apply S19. exact Hi. }
      intros i Hi. rewrite (AGI i) by lia. apply S20. exact Hi. }
    split. { eapply (L5C.big_at_agree RSEGS M10 M11). apply AG11; lia. lia. lia. exact OB10. }
    (* [comment removed for export] *)
    eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp STRCTOR_SCR _ M M10 M11 [(sp - 32 + -7984, 7984); (A + 128 + -120, 40); (A + 128 + -68, 68); (0 + 459776, 4); (0 + 462433, 6)]).
    exact LBWF. uscr; lia. exact HP010.
    { intros x Hx. apply FR11; intros Hin.
      - apply (Hx (sp - 32 + -7984, 7984)). left; reflexivity. unfold L5.in_rng; cbn. lia.
      - apply (Hx (A + 128 + -120, 40)). right; left; reflexivity. unfold L5.in_rng; cbn. lia.
      - apply (Hx (A + 128 + -68, 68)). right; right; left; reflexivity. unfold L5.in_rng; cbn. lia.
      - apply (Hx (0 + 459776, 4)). right; right; right; left; reflexivity. unfold L5.in_rng; cbn. lia.
      - apply (Hx (0 + 462433, 6)). right; right; right; right; left; reflexivity. unfold L5.in_rng; cbn. lia. }
    exact GR11.
    assert (FRA: L5PK.fresh_rng L LB A 160). { split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. lia. exact BA. }
    constructor. apply L5PK.wr_scratch; uscr; lia.
    constructor. eapply L5PK.wr_fresh. exact FRA. lia. lia.
    constructor. eapply L5PK.wr_fresh. exact FRA. lia. lia.
    constructor. eapply L5PK.wr_declared. right; left; reflexivity. unfold EH_UNCAUGHT; lia. unfold EH_UNCAUGHT; lia.
    constructor. eapply L5PK.wr_declared. right; right; right; left; reflexivity. unfold UW_FLAGS; lia. unfold UW_FLAGS; lia.
    constructor.
  - exact MBV09.
  - eapply hi_heap_clientx. exact HH10. lia. 2: exact GR11. intros a Ha.
    destruct (Z_lt_le_dec a 459776) as [L0|G0]. 2: destruct (Z_lt_le_dec a 459780) as [L0'|G0']. 2: { right; right; right. unfold statx, EH_CAUGHT. lia. }
    all: destruct (Z_lt_le_dec a 462433) as [L1|G1]; [| destruct (Z_lt_le_dec a 462439) as [L1'|G1']; [right; right; right; unfold statx, UW_FLAGS; lia |]].
    all: destruct (Z_lt_le_dec a (A + 8)) as [L2|G2]; [| destruct (Z_lt_le_dec a (A + 128)) as [L2'|G2']; [right; right; left; exists (A, 160); split; [right; left; reflexivity| cbn; lia] |]].
    all: destruct (Z_lt_le_dec a (sp - 8016)) as [L3|G3]; [left; apply FR11; rewrite BG.unsigned_lit by lia; lia|].
    all: destruct (Z_lt_le_dec a (sp - 32)) as [L4|G4]; [right; left; lia| left; apply FR11; rewrite BG.unsigned_lit by lia; lia].
Qed.
End WithHeap.
End SCFG_2.

End L5STRTU.
