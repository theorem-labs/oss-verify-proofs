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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5KnP L5ParseArith L5ParseKit L5ParseSpecs L5Bytes L5E1A L5E1B L5E1C L5StrctorKit L5StrctorTail L5StrctorMid2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module L5STRM.
Import L5CS L5PS L5E1 L5E1B L5E1C L5STRK L5STRT L5STRM2.
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
Let e1_mid2 := e1_mid2 L HI LY LYX HIok.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma e1_mid (fx7 : FPState) R R7 M M7 model model5 K LB cr cr2 (o sp fbo : Z) s (fl : bool) (av uid rnd canary hw A : Z) :
  let ds := snd (split_sign s) in
  K [] -> no_parse s ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  sp mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 8672 <= sp -> sp <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> sp <= o -> o + 32 <= hl_sptop L -> 0 <= fbo < 256 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  credit_le (parse_debit L cr (length ds)) cr2 -> credit_ok L (debit L (parse_debit L cr (length ds)) 160) 41 ->
  (* [comment removed for export] *)
  getr R7 (reg 2) = Z_to_bv 64 (sp - 32) -> getr R7 (reg 8) = Z_to_bv 64 (A + 128) -> getr R7 (reg 9) = Z_to_bv 64 22 ->
  getr R7 (reg 10) = Z_to_bv 64 (A + 128) -> getr R7 (reg 11) = Z_to_bv 64 22 -> getr R7 (reg 12) = Z_to_bv 64 390752 ->
  (forall i, In i [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg i) = getr R (reg i)) ->
  (* [comment removed for export] *)
  L5.defined M7 (sp - 8672) 8672 -> L5.defined M7 A 160 -> e1_statics M7 true fl av uid rnd canary hw ->
  (L5.u64_at RSEGS M7 (sp - 8) STRCTOR_RET /\ L5.u64_at RSEGS M7 (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M7 (sp - 24) (bv_unsigned (getr R (reg 9)))
   /\ L5.big_at RSEGS M7 o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))) ->
  (forall i, 0 <= i < 160 -> (i < 8 \/ 48 <= i < 60) -> L5.u8_at RSEGS M7 (A + i) 0) ->
  hi_heap HI ((A, 160) :: LB) (debit L cr2 160) M7 (m_vmmaps model5) -> model_ok model5 -> model_but_vm model model5 ->
  4096 <= A -> (A + 160 <= 0x10000 \/ 0x91000 <= A) -> A mod 16 = 0 -> A + 160 <= hl_sptop L - 8388608 -> blocks_apart A 160 LB ->
  L5C.hpres L LB sp STRCTOR_SCR [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)] M M7 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
      no_parse s -> e1_landing L LB cr M M' R R' o sp fbo (length ds) av uid rnd canary hw LB' cr' ->
      model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (cfg R' E1_LANDING M' model') K) ->
  srealizes RSEGS SCFG (cfg R7 SYSERR M7 model5) K.
Proof.
  intros ds HK0 NP H2 H3 H4 A16 SLO SHI STOP Olo Ohi Hfbo AVTOP LBWF CR2 CR41 R7_2 R7_8 R7_9 R7_10 R7_11 R7_12 R7i DEF7 DEFA7 ES7 P7 Z7 HH7 MOK5 MBV
         BR0 BR1 BR2 BR4 BA HQ7 KE.
  pose proof MOK5 as (Mh5 & Ml5 & Mm5). assert (GPv: GP = 67584) by reflexivity. assert (TPv: TP = 459832) by reflexivity.
  set (Wf := [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)]) in *.
  pose proof ES7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
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
        pose proof ES7 as (_ & _ & _ & _ & _ & TDL & LMC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC1s & IC2s & IC3s).
        (* [comment removed for export] *)
        destruct (L5B.u32_of_rom RSEGS M7 ERRNO rom_errno ltac:(unfold ERRNO; lia) ltac:(unfold ERRNO; lia)) as (errn & Hen & Uerr). unfold ERRNO in Uerr.
        destruct (L5B.u64_of_defined RSEGS M7 (sp - 32 - 1152) ltac:(lia) ltac:(lia) ltac:(eapply L5.defined_sub; [exact DEF7 | lia | lia])) as (d40 & Hd40 & U40).
        destruct (L5B.u64_of_defined RSEGS M7 (sp - 32 - 40) ltac:(lia) ltac:(lia) ltac:(eapply L5.defined_sub; [exact DEF7 | lia | lia])) as (d41 & Hd41 & U41).
        destruct (e1c1_conc fx7 R7 M7 (sp - 32) (A + 128) errn d40 d41 R7_2
                    ltac:(rewrite (R7i 3%nat) by inl; rewrite H3, GPv; reflexivity) ltac:(rewrite (R7i 4%nat) by inl; rewrite H4, TPv; reflexivity)
                    R7_10 R7_11 R7_12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                    ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF7| lia| lia] | lia | lia]) ltac:(eapply L5.defined_sub; [exact DEF7 | lia | lia])
                    ltac:(lia) ltac:(replace (A + 128) with (A + 8 * 16) by lia; rewrite Z_mod_plus_full; exact BR2)
                    ltac:(replace (A + 128 - 128) with A by lia; apply (L5C.writable_of_defined RSEGS); [exact DEFA7 | lia | lia]) ltac:(replace (A + 128 - 128) with A by lia; exact DEFA7)
                    ltac:(right; lia) ltac:(lia) IC1s IC2s IC3s ltac:(rewrite Z.add_0_l; exact Uerr)
                    ltac:(rewrite Z.add_0_l; apply (writable_img M7 ERRNO 4 wseg_errno); unfold ERRNO; lia) ltac:(rewrite Z.add_0_l; exact TDL) ltac:(rewrite Z.add_0_l; exact LMC) U40 U41)
          as (fx8 & R8 & M8 & MS8 & K8 & R8_1 & R8_2 & R8_8 & R8_9 & R8_10 & R8_18 & Q128 & Q120 & Qobj & Q104 & Q96 & Q88 & Q80 & Q72 & Q39 & Q55 & Q47 & Q56 & Q112 & Q32 & Q24 & Q16 & Q8 & FR8 & GR8).
        unfold SYSERR. eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5. exact MS8.
        (* [comment removed for export] *)
        assert (AG8: forall a k, (a + k <= sp - 1312 \/ sp - 32 <= a) -> (a + k <= A + 128 \/ A + 136 <= a) -> (a + k <= 459668 \/ 459672 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M7 M8 a k).
        { intros a k H1a H2a H3a Ha Hk i Hi. apply FR8; rewrite BG.unsigned_lit by lia; lia. }
        assert (STAT8: forall a, stat_rd av a -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
        { intros a Ha. apply FR8; rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; lia. }
        pose proof (e1_statics_keep M7 M8 true fl av uid rnd canary hw ES7 STAT8) as ES8.
        assert (HH8: hi_heap HI ((A, 160) :: LB) (debit L cr2 160) M8 (m_vmmaps model5)).
        { eapply hi_heap_clientx. exact HH7. lia. 2: exact GR8. intros a Ha.
          destruct (Z_lt_le_dec a 459668) as [L0|G0']. 2: destruct (Z_lt_le_dec a 459672) as [L0'|G0'']. 2: { right; right; right. unfold statx, ERRNO. lia. }
          all: destruct (Z_lt_le_dec a (A + 128)) as [La|Ga]; [| destruct (Z_lt_le_dec a (A + 136)) as [La'|Ga']; [right; right; left; exists (A, 160); split; [left; reflexivity| cbn; lia] |]].
          all: destruct (Z_lt_le_dec a (sp - 1312)) as [L1|G1']; [left; apply FR8; rewrite BG.unsigned_lit by lia; lia|].
          all: destruct (Z_lt_le_dec a (sp - 32)) as [L2|G2]; [right; left; lia| left; apply FR8; rewrite BG.unsigned_lit by lia; lia]. }
        assert (DEF8: L5.defined M8 (sp - 8672) 8672) by (eapply L5.defined_grows; [exact GR8 | exact DEF7]).
        assert (DEFA8: L5.defined M8 A 160) by (eapply L5.defined_grows; [exact GR8 | exact DEFA7]).
        assert (R8i: forall i, In i [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R8 (reg i) = getr R (reg i)).
        { intros i Hi. rewrite (K8 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply R7i. pose proof Hi as H'. L5CoreKit.L5K.inlist H'. }
        assert (HQ8: L5C.hpres L LB sp STRCTOR_SCR Wf M M8).
        { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp STRCTOR_SCR Wf M M7 M8 [(sp - 32 + -1280, 1280); (A + 128 + 0, 8); (0 + 459668, 4)]). exact LBWF. uscr; lia. exact HQ7.
          intros x Hx. apply FR8; intros Hin. apply (Hx (sp - 32 + -1280, 1280)). left; reflexivity. unfold L5.in_rng; cbn. lia.
          apply (Hx (A + 128 + 0, 8)). right; left; reflexivity. unfold L5.in_rng; cbn. lia.
          apply (Hx (0 + 459668, 4)). right; right; left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR8.
          constructor. apply L5PK.wr_scratch; uscr; lia. constructor. eapply L5PK.wr_fresh. exact FRA. lia. lia.
          constructor. apply L5PK.wr_errno; rewrite (ly_errno L LY); lia. constructor. }
        pose proof (FRA0 M7 M8 P7 ltac:(apply AG8; lia) ltac:(apply AG8; lia)) as P8.
        (* [comment removed for export] *)
        pose proof (hio_malloc L SCFG HI HIok fx8 R8 M8 model5 ((A, 160) :: LB) (debit L cr2 160) 41 K) as HMA. rewrite (ly_segs L LY), (ly_malloc L LY), (ly_tp L LY) in HMA.
        apply HMA; clear HMA.
        -- exact HH8.
        -- exact Mh5. -- exact Ml5. -- exact Mm5.
        -- rewrite L5CoreKit.L5K.rl10. exact R8_10.
        -- lia.
        -- eapply credit_ok_mono. 2: exact CR41. apply debit_mono. exact CR2.
        -- rewrite L5CoreKit.L5K.rl4, (R8i 4%nat) by inl. exact H4.
        -- rewrite L5CoreKit.L5K.rl1, R8_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. lia. reflexivity.
        -- unfold stack_ok. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R8_2, BG.unsigned_lit by lia. split. { replace (sp - 32 - 128) with (sp + (-10) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
           uscr. split. lia. split. lia. split. lia.
           intros d m0 Hd Hm. assert (W8: L5.writable RSEGS M8 (sp - 8672) 8672). { apply (L5C.writable_of_defined RSEGS). exact DEF8. lia. lia. }
           replace (sp - 32 - 128 - 8224 + d) with (sp - 8672 + (288 + d)) by lia. apply W8. lia. lia.
        -- exact HK0.
        -- intros R9 M9 model9 ref HR10 RP9 BRr BAr DEFr PRES9 MBV9 HH9.
           rewrite L5CoreKit.L5K.rl1, R8_1. change (srealizes RSEGS SCFG (cfg R9 MALLOC_RET M9 model9) K).
           pose proof PRES9 as PRES9'. rewrite L5CoreKit.L5K.rl2, R8_2, BG.unsigned_lit in PRES9' by lia.
           pose proof (hpres_of_core ((A, 160) :: LB) (sp - 32 - 128) M8 M9 PRES9') as HP9. rewrite (ly_stack L LY) in HP9. unfold HEAP_STACK in HP9.
           assert (AG9: forall a k, sp - 160 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M8 M9 a k).
           { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP9. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
           assert (AGA9: L5C.agree_on M8 M9 A 160).
           { eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP9. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
           assert (STAT9: forall a, stat_rd av a -> M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
           { apply (stat_keep_hpres av ((A, 160) :: LB) (sp - 32 - 128) 8224 [] M8 M9 HP9). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
           pose proof (e1_statics_keep M8 M9 true fl av uid rnd canary hw ES8 STAT9) as ES9.
           assert (DEF9: L5.defined M9 (sp - 8672) 8672).
           { eapply (defined_across ((A, 160) :: LB) (sp - 32 - 128) 8224 [] M8 M9). exact HP9. lia. lia. lia. lia. exact DEF8. }
           assert (DEFA9: L5.defined M9 A 160) by (eapply (L5C.defined_agree M8 M9); [exact AGA9 | exact DEFA8]).
           assert (MOK9: model_ok model9).
           { destruct MOK5 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV9); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV9); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV9); exact Y3]]. }
           pose proof MOK9 as (Mh9 & Ml9 & Mm9).
           destruct BRr as (RR0 & RR1 & RR2 & RR3 & RR4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in RR1.
           pose proof (BAr (A, 160) ltac:(left; reflexivity)) as RA. cbn in RA.
           assert (R9i: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg i) = getr R8 (reg i)).
           { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R8 R9 i RP9). exact Hi. }
           pose proof ES9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC1t & IC2t & IC3t).
           assert (HQ9: L5C.hpres L LB sp STRCTOR_SCR Wf M M9).
           { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB ((A, 160) :: LB) sp STRCTOR_SCR Wf (sp - 32 - 128) 8224 [] M M8 M9). exact LBWF. uscr; lia. lia.
             exact HQ8. exact HP9. apply L5PK.lb_sub_cons. uscr; lia. lia. lia. constructor. }
           pose proof (FRA0 M8 M9 P8 ltac:(apply AG9; lia) ltac:(apply AG9; lia)) as P9.
           (* [comment removed for export] *)
           assert (T8: forall a v, sp - 160 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M8 a v -> L5.u64_at RSEGS M9 a v).
           { intros a v Ha Hn Hu. eapply (L5C.u64_at_agree RSEGS M8 M9). apply AG9; lia. lia. lia. exact Hu. }
           assert (J18: rdn RSEGS M9 (Z_to_bv 64 (sp - 32 - 56)) 18 = Some ([Z_to_bv 8 32] ++ word_to_le_bytes 8 (Z_to_bv 64 2334106421097295433) ++ word_to_le_bytes 8 (Z_to_bv 64 8389754676633367137) ++ [Z_to_bv 8 0])).
           { change 18%nat with (1 + (8 + (8 + 1)))%nat. apply (L5B.rdn_join RSEGS M9 1). lia. lia.
             { pose proof (L5C.u8_at_agree RSEGS M8 M9 (sp - 32 - 56) 32 ltac:(apply AG9; lia) ltac:(lia) ltac:(lia) Q56) as X. exact X. }
             replace (sp - 32 - 56 + Z.of_nat 1) with (sp - 32 - 55) by lia. apply (L5B.rdn_join RSEGS M9 8). lia. lia. exact (T8 (sp - 32 - 55) _ ltac:(lia) ltac:(lia) Q55).
             replace (sp - 32 - 55 + Z.of_nat 8) with (sp - 32 - 47) by lia. apply (L5B.rdn_join RSEGS M9 8). lia. lia. exact (T8 (sp - 32 - 47) _ ltac:(lia) ltac:(lia) Q47).
             replace (sp - 32 - 47 + Z.of_nat 8) with (sp - 32 - 39) by lia.
             pose proof (L5C.u8_at_agree RSEGS M8 M9 (sp - 32 - 39) 0 ltac:(apply AG9; lia) ltac:(lia) ltac:(lia) Q39) as X. exact X. }
           change 18%nat with (8 + 10)%nat in J18.
           destruct (L5B.rdn_split RSEGS M9 8 10 (sp - 32 - 56) _ ltac:(lia) ltac:(lia) J18) as [J8a Jr].
           replace (sp - 32 - 56 + Z.of_nat 8) with (sp - 32 - 48) in Jr by lia. change 10%nat with (8 + 2)%nat in Jr.
           destruct (L5B.rdn_split RSEGS M9 8 2 (sp - 32 - 48) _ ltac:(lia) ltac:(lia) Jr) as [J8b J2].
           replace (sp - 32 - 48 + Z.of_nat 8) with (sp - 32 - 40) in J2 by lia.
           assert (V56: L5.u64_at RSEGS M9 (sp - 32 - 56) 7235433442201979168). { unfold L5.u64_at. rewrite J8a. f_equal. all: apply L5B.list_bv_eq; vm_compute; reflexivity. }
           assert (V48: L5.u64_at RSEGS M9 (sp - 32 - 48) 7954884667833999648). { unfold L5.u64_at. rewrite J8b. f_equal. all: apply L5B.list_bv_eq; vm_compute; reflexivity. }
           assert (V40: L5KP.uw_at RSEGS 2 M9 (sp - 32 - 40) 116). { unfold L5KP.uw_at. rewrite J2. f_equal. all: apply L5B.list_bv_eq; vm_compute; reflexivity. }
           rewrite R7_8, BG.unsigned_lit in Q16 by lia. rewrite R7_9, BG.unsigned_lit in Q24 by lia.
           eapply (e1_mid2 fx8 R R9 M M9 model model9 K LB cr cr2 o sp fbo s fl av uid rnd canary hw A ref HK0 NP H2 H3 H4 A16 SLO SHI STOP Olo Ohi Hfbo AVTOP LBWF CR2).
           ++ rewrite (R9i 2%nat) by inl. exact R8_2.
           ++ rewrite (R9i 9%nat) by inl. exact R8_9.
           ++ rewrite <- L5CoreKit.L5K.rl10. exact HR10.
           ++ rewrite (R9i 18%nat) by inl. exact R8_18.
           ++ intros i Hi. rewrite (R9i i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply R8i. exact Hi.
           ++ exact DEF9. ++ exact DEFA9. ++ exact DEFr. ++ exact ES9. ++ exact P9.
           ++ intros i Hi Hr. eapply (L5C.u8_at_agree RSEGS M8 M9). eapply L5C.agree_on_sub. exact AGA9. lia. lia. lia. lia.
              eapply (L5C.u8_at_agree RSEGS M7 M8). apply AG8; lia. lia. lia. apply Z7. lia. lia.
           ++ exact (T8 (sp - 32 - 120) _ ltac:(lia) ltac:(lia) Q120). ++ exact (T8 (sp - 32 - 128) _ ltac:(lia) ltac:(lia) Q128).
           ++ exact V56. ++ exact V48. ++ exact V40.
           ++ exact (T8 (sp - 32 - 72) _ ltac:(lia) ltac:(lia) Q72). ++ exact (T8 (sp - 32 - 80) _ ltac:(lia) ltac:(lia) Q80). ++ exact (T8 (sp - 32 - 88) _ ltac:(lia) ltac:(lia) Q88).
           ++ exact (T8 (sp - 32 - 96) _ ltac:(lia) ltac:(lia) Q96).
           ++ rewrite (R7i 19%nat) in Q104 by inl. exact (T8 (sp - 32 - 104) _ ltac:(lia) ltac:(lia) Q104).
           ++ exact (T8 (sp - 32 - 8) _ ltac:(lia) ltac:(lia) Q8). ++ exact (T8 (sp - 32 - 16) _ ltac:(lia) ltac:(lia) Q16). ++ exact (T8 (sp - 32 - 24) _ ltac:(lia) ltac:(lia) Q24).
           ++ rewrite (R7i 18%nat) in Q32 by inl. exact (T8 (sp - 32 - 32) _ ltac:(lia) ltac:(lia) Q32).
           ++ exact HH9. ++ exact MOK9. ++ eapply L5C.model_but_vm_trans. exact MBV. exact MBV9.
           ++ lia. ++ exact BR1. ++ exact BR2. ++ lia. ++ exact BA. ++ lia. ++ exact RR1. ++ exact RR2. ++ lia. ++ exact BAr.
           ++ exact HQ9. ++ exact KE.
Qed.

End WithHeap.
End SCFG_2.

End L5STRM.
