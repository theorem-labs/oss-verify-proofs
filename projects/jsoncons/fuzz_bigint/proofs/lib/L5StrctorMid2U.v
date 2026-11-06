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
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5KnP L5ParseArith L5ParseKit L5ParseSpecsU L5Bytes L5E1AU L5E1BU L5E1CU L5StrctorKitU L5StrctorTailU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module L5STRM2U.
Import L5CSU L5PSU L5E1U L5E1BU L5E1CU L5STRKU L5STRTU.
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
Let e1_tail := e1_tail L HI LY LYX HIok.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma e1_mid2 (fx8 : FPState) R R9 M M9 model model9 K LB cr cr2 (o sp fbo : Z) s (fl : bool) (av uid rnd canary hw A ref : Z) :
  let ds := snd (split_sign s) in
  K [] -> no_parse s ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  sp mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 8688 <= sp -> sp <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> sp <= o -> o + 32 <= hl_sptop L -> 0 <= fbo < 256 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  credit_le (parse_debit L cr (length ds)) cr2 ->
  (* [comment removed for export] *)
  getr R9 (reg 2) = Z_to_bv 64 (sp - 32 - 128) -> getr R9 (reg 9) = Z_to_bv 64 (sp - 32 - 55) -> getr R9 (reg 10) = Z_to_bv 64 ref -> getr R9 (reg 18) = Z_to_bv 64 16 ->
  (forall i, In i [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg i) = getr R (reg i)) ->
  (* [comment removed for export] *)
  L5.defined M9 (sp - 8688) 8688 -> L5.defined M9 A 160 -> L5.defined M9 ref 41 -> e1_statics M9 true fl av uid rnd canary hw ->
  (L5.u64_at RSEGS M9 (sp - 8) STRCTOR_RET /\ L5.u64_at RSEGS M9 (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M9 (sp - 24) (bv_unsigned (getr R (reg 9)))
   /\ L5.big_at RSEGS M9 o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))) ->
  (forall i, 0 <= i < 160 -> (i < 8 \/ 48 <= i < 60) -> L5.u8_at RSEGS M9 (A + i) 0) ->
  (* [comment removed for export] *)
  L5.u64_at RSEGS M9 (sp - 32 - 120) 266272 -> L5.u64_at RSEGS M9 (sp - 32 - 128) (A + 128) ->
  L5.u64_at RSEGS M9 (sp - 32 - 56) 7235433442201979168 -> L5.u64_at RSEGS M9 (sp - 32 - 48) 7954884667833999648 -> L5KP.uw_at RSEGS 2 M9 (sp - 32 - 40) 116 ->
  L5.u64_at RSEGS M9 (sp - 32 - 72) 269780 -> L5.u64_at RSEGS M9 (sp - 32 - 80) 393560 -> L5.u64_at RSEGS M9 (sp - 32 - 88) (A + 128) -> L5.u64_at RSEGS M9 (sp - 32 - 96) 22 ->
  L5.u64_at RSEGS M9 (sp - 32 - 104) (bv_unsigned (getr R (reg 19))) ->
  L5.u64_at RSEGS M9 (sp - 32 - 8) 134328 -> L5.u64_at RSEGS M9 (sp - 32 - 16) (A + 128) -> L5.u64_at RSEGS M9 (sp - 32 - 24) 22 -> L5.u64_at RSEGS M9 (sp - 32 - 32) (bv_unsigned (getr R (reg 18))) ->
  (* [comment removed for export] *)
  hi_heap HI ((ref, 41) :: (A, 160) :: LB) (debit L (debit L cr2 160) 41) M9 (m_vmmaps model9) -> model_ok model9 -> model_but_vm model model9 ->
  4096 <= A -> (A + 160 <= 0x10000 \/ 0x92000 <= A) -> A mod 16 = 0 -> A + 160 <= hl_sptop L - 8388608 -> blocks_apart A 160 LB ->
  4096 <= ref -> (ref + 41 <= 0x10000 \/ 0x92000 <= ref) -> ref mod 16 = 0 -> ref + 41 <= hl_sptop L - 8388608 -> blocks_apart ref 41 ((A, 160) :: LB) ->
  L5C.hpres L LB sp STRCTOR_SCR [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)] M M9 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
      no_parse s -> e1_landing L LB cr M M' R R' o sp fbo (length ds) av uid rnd canary hw LB' cr' ->
      model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (cfg R' E1_LANDING M' model') K) ->
  srealizes RSEGS SCFG (cfg R9 MALLOC_RET M9 model9) K.
Proof.
  intros ds HK0 NP H2 H3 H4 A16 SLO SHI STOP Olo Ohi Hfbo AVTOP LBWF CR2 R9_2 R9_9 R9_10 R9_18 R9i DEF9 DEFA9 DEFr ES9 P9 Z9
         Q120 Q128 V56 V48 V40 Q72 Q80 Q88 Q96 Q104 Q8 Q16 Q24 Q32 HH9 MOK9 MBV BR0 BR1 BR2 BR4 BA RR0 RR1 RR2 RR4 BAr HQ9 KE.
  pose proof MOK9 as (Mh9 & Ml9 & Mm9). assert (GPv: GP = 67584) by reflexivity. assert (TPv: TP = 462648) by reflexivity.
  set (Wf := [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)]) in *.
  pose proof ES9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  pose proof ES9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC1t & IC2t & IC3t).
  pose proof (BAr (A, 160) ltac:(left; reflexivity)) as RA. cbn in RA.
  unfold cfg.
      assert (FRA0: forall Ma Mb, (L5.u64_at RSEGS Ma (sp - 8) STRCTOR_RET /\ L5.u64_at RSEGS Ma (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS Ma (sp - 24) (bv_unsigned (getr R (reg 9)))
                                    /\ L5.big_at RSEGS Ma o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))) ->
                 L5C.agree_on Ma Mb (sp - 32) 32 -> L5C.agree_on Ma Mb o 32 ->
                 (L5.u64_at RSEGS Mb (sp - 8) STRCTOR_RET /\ L5.u64_at RSEGS Mb (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS Mb (sp - 24) (bv_unsigned (getr R (reg 9)))
                  /\ L5.big_at RSEGS Mb o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0)))).
      { intros Ma Mb (Y1 & Y2 & Y3 & Y4) AGs AGo. split. eapply (L5C.u64_at_agree RSEGS Ma Mb). eapply L5C.agree_on_sub. exact AGs. lia. lia. lia. lia. exact Y1.
        split. eapply (L5C.u64_at_agree RSEGS Ma Mb). eapply L5C.agree_on_sub. exact AGs. lia. lia. lia. lia. exact Y2.
        split. eapply (L5C.u64_at_agree RSEGS Ma Mb). eapply L5C.agree_on_sub. exact AGs. lia. lia. lia. lia. exact Y3.
        eapply (L5C.big_at_agree RSEGS Ma Mb). exact AGo. lia. lia. exact Y4. }
      assert (FRA: L5PK.fresh_rng L LB A 160). { split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. lia. exact BA. }
           (* [comment removed for export] *)
           destruct (e1c2u_conc fx8 R9 M9 (sp - 32) (A + 128) ref (bv_unsigned (getr R (reg 18)))
                       R9_2
                       ltac:(rewrite (R9i 3%nat) by inl; rewrite H3, GPv; reflexivity)
                       ltac:(rewrite (R9i 4%nat) by inl; rewrite H4, TPv; reflexivity)
                       R9_9
                       R9_10
                       R9_18
                       ltac:(lia) ltac:(lia) ltac:(lia) (wrange _) ltac:(lia)
                       ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                       ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF9| lia| lia] | lia | lia]) ltac:(eapply L5.defined_sub; [exact DEF9 | lia | lia])
                       ltac:(lia) ltac:(replace (A + 128) with (A + 8 * 16) by lia; rewrite Z_mod_plus_full; exact BR2)
                       ltac:(replace (A + 128 - 128) with A by lia; apply (L5C.writable_of_defined RSEGS); [exact DEFA9 | lia | lia]) ltac:(replace (A + 128 - 128) with A by lia; exact DEFA9)
                       ltac:(lia) RR2 ltac:(apply (L5C.writable_of_defined RSEGS); [exact DEFr | lia | lia]) DEFr
                       ltac:(right; lia) ltac:(lia) ltac:(right; lia) ltac:(lia) ltac:(lia) IC1t IC2t IC3t
                       Q120 Q128 V56 V48 V40
                       Q72 Q80 Q88
                       Q96
                       ltac:(rewrite (R9i 19%nat) by inl; exact Q104)
                       Q8 Q16 Q24
                       Q32)
             as (fx10 & R10 & M10 & MS10 & K10 & R10_1 & R10_2 & R10_8 & R10_9 & R10_10 & R10_11 & R10_12 & R10_18 & R10_19 & O24 & O16 & O0 & O8 & W24 & W32 & W40 & W16 & W8 & W0 & FR10 & GR10).
           unfold MALLOC_RET. eapply (L5.cps_of_msteps RSEGS). exact Mh9. exact Ml9. exact MS10.
           (* [comment removed for export] *)
           assert (AG10: forall a k, (a + k <= sp - 224 \/ sp - 160 <= a) -> (a + k <= A + 128 \/ A + 160 <= a) -> (a + k <= ref \/ ref + 41 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M9 M10 a k).
           { intros a k H1a H2a H3a Ha Hk i Hi. apply FR10; rewrite BG.unsigned_lit by lia; lia. }
           assert (STAT10: forall a, stat_rd av a -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
           { intros a Ha. apply FR10; rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; lia. }
           pose proof (e1_statics_keep M9 M10 true fl av uid rnd canary hw ES9 STAT10) as ES10.
           assert (FRR: L5PK.fresh_rng L LB ref 41). { split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact RR1. split. lia. intros b Hb. apply BAr. right. exact Hb. }
           assert (HQ10: L5C.hpres L LB sp STRCTOR_SCR Wf M M10).
           { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp STRCTOR_SCR Wf M M9 M10 [(sp - 32 + -192, 64); (A + 128 + 0, 32); (ref + 0, 41)]). exact LBWF. uscr; lia. exact HQ9.
             intros x Hx. apply FR10; intros Hin. apply (Hx (sp - 32 + -192, 64)). left; reflexivity. unfold L5.in_rng; cbn. lia.
             apply (Hx (A + 128 + 0, 32)). right; left; reflexivity. unfold L5.in_rng; cbn. lia.
             apply (Hx (ref + 0, 41)). right; right; left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR10.
             constructor. apply L5PK.wr_scratch; uscr; lia. constructor. eapply L5PK.wr_fresh. exact FRA. lia. lia.
             constructor. eapply L5PK.wr_fresh. exact FRR. lia. lia. constructor. }
           pose proof (FRA0 M9 M10 P9 ltac:(apply AG10; lia) ltac:(apply AG10; lia)) as (F8' & F16' & F24' & OB10).
           assert (HH10: hi_heap HI ((ref, 41) :: (A, 160) :: LB) (debit L (debit L cr2 160) 41) M10 (m_vmmaps model9)).
           { eapply hi_heap_clientx. exact HH9. lia. 2: exact GR10. intros a Ha.
             destruct (Z_lt_le_dec a ref) as [L0|G0']. 2: destruct (Z_lt_le_dec a (ref + 41)) as [L0'|G0'']. 2: { right; right; left. exists (ref, 41). split. left; reflexivity. cbn. lia. }
             all: destruct (Z_lt_le_dec a (A + 128)) as [La|Ga]; [| destruct (Z_lt_le_dec a (A + 160)) as [La'|Ga']; [right; right; left; exists (A, 160); split; [right; left; reflexivity| cbn; lia] |]].
             all: destruct (Z_lt_le_dec a (sp - 224)) as [L1|G1']; [left; apply FR10; rewrite BG.unsigned_lit by lia; lia|].
             all: destruct (Z_lt_le_dec a (sp - 160)) as [L2|G2]; [right; left; lia| left; apply FR10; rewrite BG.unsigned_lit by lia; lia]. }
           assert (Z6': forall i, 0 <= i < 160 -> (i < 8 \/ 48 <= i < 60) -> L5.u8_at RSEGS M10 (A + i) 0).
           { intros i Hi Hr. eapply (L5C.u8_at_agree RSEGS M9 M10). apply AG10; lia. lia. lia.
             apply Z9. lia. lia. }
           eapply (e1_tail fx10 R R10 M M10 model model9 K LB cr cr2 o sp fbo s fl av uid rnd canary hw A ref HK0 NP H2 H3 H4 A16 ltac:(lia) SHI STOP Olo Ohi Hfbo AVTOP LBWF
                    R10_1 R10_2 R10_10 R10_11 R10_12).
           ++ intros i Hi. cbn in Hi. destruct Hi as [<-|[<-|[<-|Hi]]].
              1-2: rewrite (K10 _) by (apply L5KP.In_of_existsb; reflexivity); apply R9i; inl.
              rewrite R10_18. apply lit_of_word.
              rewrite (K10 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply R9i. pose proof Hi as H'. L5CoreKit.L5K.inlist H'.
           ++ eapply L5.defined_grows. exact GR10. exact DEF9.
           ++ eapply L5.defined_grows. exact GR10. exact DEFA9.
           ++ eapply L5.defined_grows. exact GR10. exact DEFr.
           ++ exact ES10.
           ++ exact F8'. ++ exact F16'. ++ exact F24'. ++ exact OB10.
           ++ exact O24. ++ exact O16. ++ exact O0. ++ exact O8. ++ exact W24. ++ exact W32. ++ exact W40. ++ exact W16. ++ exact W8. ++ exact W0.
           ++ intros i Hi. apply Z6'; lia.
           ++ intros i Hi. replace (A + 48 + i) with (A + (48 + i)) by lia. apply Z6'; lia.
           ++ exact HH10.
           ++ exact MOK9.
           ++ exact MBV.
           ++ lia. ++ exact BR1. ++ exact BR2. ++ lia. ++ exact BA. ++ lia. ++ exact RR1. ++ exact RR2. ++ lia. ++ exact BAr.
           ++ exact CR2.
           ++ exact HQ10.
           ++ exact KE.
Qed.

End WithHeap.
End SCFG_2.

End L5STRM2U.
