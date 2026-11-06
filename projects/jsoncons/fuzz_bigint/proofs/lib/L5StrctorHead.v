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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5KnP L5ParseArith L5ParseKit L5ParseSpecs L5Bytes L5E1A L5E1B L5E1C L5StrctorKit L5StrctorTail L5StrctorMid.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module L5STRH.
Import L5CS L5PS L5E1 L5E1B L5E1C L5STRK L5STRT L5STRM.
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
Let e1_mid := e1_mid L HI LY LYX HIok.

(* [comment removed for export] *)
Lemma e1_head (fx3 : FPState) R R3 M M3 model model2 K LB cr cr2 (o sp fbo : Z) s (gd fl : bool) (av uid rnd canary hw : Z) :
  let ds := snd (split_sign s) in
  K [] -> no_parse s ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  sp mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 8672 <= sp -> sp <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> sp <= o -> o + 32 <= hl_sptop L -> 0 <= fbo < 256 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  credit_le (parse_debit L cr (length ds)) cr2 -> credit_ok L (parse_debit L cr (length ds)) 160 -> credit_ok L (debit L (parse_debit L cr (length ds)) 160) 41 ->
  getr R3 (reg 2) = Z_to_bv 64 (sp - 32) -> getr R3 (reg 9) = Z_to_bv 64 22 -> getr R3 (reg 10) = Z_to_bv 64 32 ->
  (forall i, In i [3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg i) = getr R (reg i)) ->
  L5.defined M3 (sp - 8672) 8672 -> e1_statics M3 gd fl av uid rnd canary hw ->
  hi_heap HI LB cr2 M3 (m_vmmaps model2) -> model_ok model2 -> model_but_vm model model2 ->
  (L5.u64_at RSEGS M3 (sp - 8) STRCTOR_RET /\ L5.u64_at RSEGS M3 (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M3 (sp - 24) (bv_unsigned (getr R (reg 9)))
   /\ L5.big_at RSEGS M3 o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))) ->
  L5C.hpres L LB sp STRCTOR_SCR [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)] M M3 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
      no_parse s -> e1_landing L LB cr M M' R R' o sp fbo (length ds) av uid rnd canary hw LB' cr' ->
      model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') -> srealizes RSEGS SCFG (cfg R' E1_LANDING M' model') K) ->
  srealizes RSEGS SCFG (cfg R3 THROW0 M3 model2) K.
Proof.
  intros ds HK0 NP H2 H3 H4 A16 SLO SHI STOP Olo Ohi Hfbo AVTOP LBWF CR2 CR160 CR41 R3_2 R3_9 R3_10 R3i DEF3 ES3 HH3 MOK2 MBV2 P3 HQ3 KE.
  pose proof MOK2 as (Mh2 & Ml2 & Mm2). assert (GPv: GP = 67584) by reflexivity. assert (TPv: TP = 459832) by reflexivity.
  set (Wf := [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)]) in *.
  pose proof ES3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  pose proof ES3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC1 & IC2 & IC3).
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
      (* [comment removed for export] *)
      destruct (e1a1_conc fx3 R3 M3 (sp - 32) (sp - 32 - 288)
                  R3_2 ltac:(rewrite (R3i 3%nat) by inl; rewrite H3, GPv; reflexivity) ltac:(rewrite (R3i 4%nat) by inl; rewrite H4, TPv; reflexivity) R3_10
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                  ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF3| uscr; lia| uscr; lia] | uscr; lia | uscr; lia])
                  ltac:(eapply L5.defined_sub; [exact DEF3 | uscr; lia | uscr; lia])
                  ltac:(lia) ltac:(replace (sp - 32 - 288) with (sp + (-20) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                  ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF3| uscr; lia| uscr; lia] | uscr; lia | uscr; lia])
                  ltac:(eapply L5.defined_sub; [exact DEF3 | uscr; lia | uscr; lia])
                  ltac:(right; lia) ltac:(right; lia)
                  IC1 IC2 IC3)
        as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_10 & R4_11 & D48 & D40 & D24 & D16 & D8 & FR4 & GR4).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS4.
      assert (AG4: forall a k, (a + k <= sp - 144 \/ sp - 32 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M3 M4 a k).
      { intros a k Hak Ha Hk i Hi. apply FR4. rewrite BG.unsigned_lit by lia. lia. }
      assert (STAT4: forall a, stat_rd av a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ha. apply FR4. rewrite BG.unsigned_lit. all: unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; lia. }
      pose proof (e1_statics_keep M3 M4 gd fl av uid rnd canary hw ES3 STAT4) as ES4.
      assert (HH4: hi_heap HI LB cr2 M4 (m_vmmaps model2)).
      { eapply hi_heap_clientx. exact HH3. lia. 2: exact GR4.
        intros a Ha. destruct (Z_lt_le_dec a (sp - 144)) as [L1|G1]. left. apply FR4. rewrite BG.unsigned_lit by lia. lia.
        destruct (Z_lt_le_dec a (sp - 32)) as [L2|G2]. right; left. lia. left. apply FR4. rewrite BG.unsigned_lit by lia. lia. }
      assert (HQ4: L5C.hpres L LB sp STRCTOR_SCR Wf M M4).
      { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp STRCTOR_SCR Wf M M3 M4 [(sp - 32 + -112, 112)]). exact LBWF. uscr; lia. exact HQ3.
        intros x Hx. apply FR4. intros Hin. apply (Hx (sp - 32 + -112, 112)). left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR4.
        constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
      pose proof (FRA0 M3 M4 P3 ltac:(apply AG4; lia) ltac:(apply AG4; lia)) as P4.
      (* [comment removed for export] *)
      pose proof (hio_aligned L SCFG HI HIok fx4 R4 M4 model2 LB cr2 160 K) as HA. rewrite (ly_segs L LY), (ly_aligned L LY), (ly_tp L LY) in HA.
      apply HA; clear HA.
      * exact HH4.
      * exact Mh2. * exact Ml2. * exact Mm2.
      * rewrite L5CoreKit.L5K.rl10. exact R4_10.
      * rewrite L5CoreKit.L5K.rl11. exact R4_11.
      * lia.
      * eapply credit_ok_mono. exact CR2. exact CR160.
      * rewrite L5CoreKit.L5K.rl4, (K4 4%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite (R3i 4%nat) by inl. exact H4.
      * rewrite L5CoreKit.L5K.rl1, R4_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. lia. reflexivity.
      * unfold stack_ok. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R4_2, BG.unsigned_lit by lia. split. { replace (sp - 32 - 48) with (sp + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
        uscr. split. lia. split. lia. split. lia.
        intros d m0 Hd Hm.
        assert (W4: L5.writable RSEGS M4 (sp - 8672) 8672).
        { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact GR4. exact DEF3. lia. lia. }
        replace (sp - 32 - 48 - 8224 + d) with (sp - 8672 + (368 + d)) by lia. apply W4. lia. lia.
      * exact HK0.
      * intros R5 M5 model5 A HA10 RP5 BR BA DEFA PRES5 MBV5 HH5.
        rewrite L5CoreKit.L5K.rl1, R4_1. change (srealizes RSEGS SCFG (cfg R5 AALLOC_RET M5 model5) K).
        pose proof PRES5 as PRES5'. rewrite L5CoreKit.L5K.rl2, R4_2, BG.unsigned_lit in PRES5' by lia.
        pose proof (hpres_of_core LB (sp - 32 - 48) M4 M5 PRES5') as HP5. rewrite (ly_stack L LY) in HP5. unfold HEAP_STACK in HP5.
        assert (AG5: forall a k, sp - 80 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M4 M5 a k).
        { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP5. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
        assert (STAT5: forall a, stat_rd av a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
        { apply (stat_keep_hpres av LB (sp - 32 - 48) 8224 [] M4 M5 HP5). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
        pose proof (e1_statics_keep M4 M5 gd fl av uid rnd canary hw ES4 STAT5) as ES5.
        assert (DEF5: L5.defined M5 (sp - 8672) 8672).
        { eapply (defined_across LB (sp - 32 - 48) 8224 [] M4 M5). exact HP5. lia. lia. lia. lia. eapply L5.defined_grows. exact GR4. exact DEF3. }
        assert (MOK5: model_ok model5).
        { destruct MOK2 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV5); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV5); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV5); exact Y3]]. }
        pose proof MOK5 as (Mh5 & Ml5 & Mm5).
        destruct BR as (BR0 & BR1 & BR2 & BR3 & BR4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1.
        assert (R5i: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg i) = getr R4 (reg i)).
        { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R4 R5 i RP5). exact Hi. }
        assert (R4i: forall i, In i [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg i) = getr R (reg i)).
        { intros i Hi. rewrite (K4 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply R3i. pose proof Hi as H'. L5CoreKit.L5K.inlist H'. }
        pose proof ES5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC1' & IC2' & IC3').
        rewrite R3_9, BG.unsigned_lit in D24 by lia.
        assert (HQ5: L5C.hpres L LB sp STRCTOR_SCR Wf M M5).
        { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp STRCTOR_SCR Wf (sp - 32 - 48) 8224 [] M M4 M5). exact LBWF. uscr; lia. lia.
          exact HQ4. exact HP5. apply L5PK.lb_sub_refl. uscr; lia. lia. lia. constructor. }
        pose proof (FRA0 M4 M5 P4 ltac:(apply AG5; lia) ltac:(apply AG5; lia)) as P5.
        (* [comment removed for export] *)
        destruct (e1a2_conc fx4 R5 M5 (sp - 32) (A + 128) (bv_unsigned (getr R3 (reg 8)))
                    ltac:(rewrite (R5i 2%nat) by inl; exact R4_2)
                    ltac:(rewrite (R5i 3%nat) by inl; rewrite (R4i 3%nat) by inl; rewrite H3, GPv; reflexivity)
                    ltac:(rewrite (R5i 4%nat) by inl; rewrite (R4i 4%nat) by inl; rewrite H4, TPv; reflexivity)
                    ltac:(replace (A + 128 - 128) with A by lia; rewrite <- L5CoreKit.L5K.rl10; exact HA10)
                    ltac:(lia) ltac:(lia) (wrange _) ltac:(lia) ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                    ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF5| lia| lia] | lia | lia])
                    ltac:(eapply L5.defined_sub; [exact DEF5 | lia | lia])
                    ltac:(lia) ltac:(replace (A + 128) with (A + 8 * 16) by lia; rewrite Z_mod_plus_full; exact BR2)
                    ltac:(replace (A + 128 - 128) with A by lia; apply (L5C.writable_of_defined RSEGS); [exact DEFA | lia | lia])
                    ltac:(replace (A + 128 - 128) with A by lia; exact DEFA)
                    ltac:(right; lia) ltac:(lia) IC1' IC2' IC3'
                    ltac:(eapply (L5C.u64_at_agree RSEGS M4 M5); [apply AG5; lia | lia | lia | exact D40])
                    ltac:(eapply (L5C.u64_at_agree RSEGS M4 M5); [apply AG5; lia | lia | lia | exact D48])
                    ltac:(eapply (L5C.u64_at_agree RSEGS M4 M5); [apply AG5; lia | lia | lia | exact D8])
                    ltac:(eapply (L5C.u64_at_agree RSEGS M4 M5); [apply AG5; lia | lia | lia | exact D16])
                    ltac:(eapply (L5C.u64_at_agree RSEGS M4 M5); [apply AG5; lia | lia | lia | exact D24]))
          as (fx6 & R6 & M6 & MS6 & K6 & R6_1 & R6_2 & R6_8 & R6_9 & R6_10 & Z6 & FR6 & GR6).
        unfold cfg, AALLOC_RET. eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5. exact MS6.
        (* [comment removed for export] *)
        assert (AG6: forall a k, (a + k <= sp - 144 \/ sp - 80 <= a) -> (a + k <= A \/ A + 160 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M5 M6 a k).
        { intros a k H1a H2a Ha Hk i Hi. apply FR6; rewrite BG.unsigned_lit by lia; lia. }
        assert (STAT6: forall a, stat_rd av a -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
        { intros a Ha. apply FR6; rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; lia. }
        pose proof (e1_statics_keep M5 M6 gd fl av uid rnd canary hw ES5 STAT6) as ES6.
        assert (HH6: hi_heap HI ((A, 160) :: LB) (debit L cr2 160) M6 (m_vmmaps model5)).
        { eapply hi_heap_clientx. exact HH5. lia. 2: exact GR6. intros a Ha.
          destruct (Z_lt_le_dec a A) as [L0|G0]. 2: destruct (Z_lt_le_dec a (A + 160)) as [L0'|G0']. 2: { right; right; left. exists (A, 160). split. left; reflexivity. cbn. lia. }
          all: destruct (Z_lt_le_dec a (sp - 144)) as [L1|G1]; [left; apply FR6; rewrite BG.unsigned_lit by lia; lia|].
          all: destruct (Z_lt_le_dec a (sp - 80)) as [L2|G2]; [right; left; lia| left; apply FR6; rewrite BG.unsigned_lit by lia; lia]. }
        assert (DEF6: L5.defined M6 (sp - 8672) 8672) by (eapply L5.defined_grows; [exact GR6 | exact DEF5]).
        assert (DEFA6: L5.defined M6 A 160) by (eapply L5.defined_grows; [exact GR6 | exact DEFA]).
        assert (R6i: forall i, In i [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg i) = getr R (reg i)).
        { intros i Hi. rewrite (K6 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). rewrite (R5i i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply R4i. exact Hi. }
        pose proof ES6 as (_ & _ & SG0 & SG1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC1'' & IC2'' & IC3'').
        assert (FRA: L5PK.fresh_rng L LB A 160). { split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. lia. exact BA. }
        assert (HQ6: L5C.hpres L LB sp STRCTOR_SCR Wf M M6).
        { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp STRCTOR_SCR Wf M M5 M6 [(sp - 32 + -112, 64); (A + 128 + -128, 160)]). exact LBWF. uscr; lia. exact HQ5.
          intros x Hx. apply FR6; intros Hin. apply (Hx (sp - 32 + -112, 64)). left; reflexivity. unfold L5.in_rng; cbn. lia.
          apply (Hx (A + 128 + -128, 160)). right; left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR6.
          constructor. apply L5PK.wr_scratch; uscr; lia. constructor. eapply L5PK.wr_fresh. exact FRA. lia. lia. constructor. }
        pose proof (FRA0 M5 M6 P5 ltac:(apply AG6; lia) ltac:(apply AG6; lia)) as P6.
        (* [comment removed for export] *)
        assert (STEPG: exists (fx7 : FPState) R7 M7,
           msteps RSEGS (st fx6 R6 CAT M6) (st fx7 R7 SYSERR M7)
           /\ (forall i, In i KS_G0 -> getr R7 (reg i) = getr R6 (reg i))
           /\ getr R7 (reg 1) = Z_to_bv 64 133696 /\ getr R7 (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R7 (reg 8) = getr R6 (reg 8) /\ getr R7 (reg 9) = getr R6 (reg 9)
           /\ getr R7 (reg 10) = getr R6 (reg 8) /\ getr R7 (reg 11) = getr R6 (reg 9) /\ getr R7 (reg 12) = Z_to_bv 64 390752
           /\ L5.u8_at RSEGS M7 457505 1 /\ L5.u8_at RSEGS M7 457504 1
           /\ (forall x : word, ~ (sp - 112 <= bv_unsigned x < sp - 32) -> ~ (457504 <= bv_unsigned x < 457506) -> M7 x = M6 x) /\ mem_grows M6 M7).
        { assert (WG8: L5.writable RSEGS M6 457504 8). { apply (writable_img M6 SYSCAT_GUARD 8 wseg_guard). unfold SYSCAT_GUARD; lia. lia. unfold SYSCAT_GUARD; lia. }
          unfold SYSCAT_GUARD in SG0, SG1. change (457504 + 1) with 457505 in SG1.
          destruct gd.
          - destruct (e1g1_g1_conc fx6 R6 M6 (sp - 32) (A + 128) (A + 128) R6_2
                        ltac:(rewrite (R6i 3%nat) by inl; rewrite H3, GPv; reflexivity) ltac:(rewrite (R6i 4%nat) by inl; rewrite H4, TPv; reflexivity) R6_10
                        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                        ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF6| lia| lia] | lia | lia]) ltac:(eapply L5.defined_sub; [exact DEF6 | lia | lia])
                        ltac:(lia) ltac:(replace (A + 128) with (A + 8 * 16) by lia; rewrite Z_mod_plus_full; exact BR2)
                        ltac:(replace (A + 128 - 128) with A by lia; apply (L5C.writable_of_defined RSEGS); [exact DEFA6 | lia | lia]) ltac:(replace (A + 128 - 128) with A by lia; exact DEFA6)
                        ltac:(right; lia) ltac:(lia) IC1'' IC2'' IC3'' ltac:(rewrite Z.add_0_l; exact SG0) ltac:(rewrite Z.add_0_l; exact SG1)
                        ltac:(rewrite Z.add_0_l; exact WG8) ltac:(rewrite Z.add_0_l; eapply L5.writable_sub; [exact WG8|lia|lia]) ltac:(rewrite Z.add_0_l; eapply L5.writable_sub; [exact WG8|lia|lia]))
              as (fx7 & R7 & M7 & MS7 & K7 & R7_1 & R7_2 & R7_8 & R7_9 & R7_10 & R7_11 & R7_12 & G1 & G0 & FR7 & GR7).
            exists fx7, R7, M7. split. unfold CAT, SYSERR. exact MS7. split. intros i Hi. apply K7. revert Hi. clear. intros Hi. exact Hi.
            split. exact R7_1. split. exact R7_2. split. exact R7_8. split. exact R7_9. split. exact R7_10. split. exact R7_11. split. exact R7_12.
            rewrite Z.add_0_l in G1, G0. split. first [exact G1 | exact G0]. split. first [exact G0 | exact G1]. split. intros x Hx Hy. apply FR7; lia. exact GR7.
          - destruct (e1g1_g0_conc fx6 R6 M6 (sp - 32) (A + 128) (A + 128) R6_2
                        ltac:(rewrite (R6i 3%nat) by inl; rewrite H3, GPv; reflexivity) ltac:(rewrite (R6i 4%nat) by inl; rewrite H4, TPv; reflexivity) R6_10
                        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact A16)
                        ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF6| lia| lia] | lia | lia]) ltac:(eapply L5.defined_sub; [exact DEF6 | lia | lia])
                        ltac:(lia) ltac:(replace (A + 128) with (A + 8 * 16) by lia; rewrite Z_mod_plus_full; exact BR2)
                        ltac:(replace (A + 128 - 128) with A by lia; apply (L5C.writable_of_defined RSEGS); [exact DEFA6 | lia | lia]) ltac:(replace (A + 128 - 128) with A by lia; exact DEFA6)
                        ltac:(right; lia) ltac:(lia) IC1'' IC2'' IC3'' ltac:(rewrite Z.add_0_l; exact SG0) ltac:(rewrite Z.add_0_l; exact SG1)
                        ltac:(rewrite Z.add_0_l; exact WG8) ltac:(rewrite Z.add_0_l; eapply L5.writable_sub; [exact WG8|lia|lia]) ltac:(rewrite Z.add_0_l; eapply L5.writable_sub; [exact WG8|lia|lia]))
              as (fx7 & R7 & M7 & MS7 & K7 & R7_1 & R7_2 & R7_8 & R7_9 & R7_10 & R7_11 & R7_12 & G1 & G0 & FR7 & GR7).
            exists fx7, R7, M7. split. unfold CAT, SYSERR. exact MS7. split. exact K7.
            split. exact R7_1. split. exact R7_2. split. exact R7_8. split. exact R7_9. split. exact R7_10. split. exact R7_11. split. exact R7_12.
            rewrite Z.add_0_l in G1, G0. split. first [exact G1 | exact G0]. split. first [exact G0 | exact G1]. split. intros x Hx Hy. apply FR7; lia. exact GR7. }
        destruct STEPG as (fx7 & R7 & M7 & MS7 & K7 & R7_1 & R7_2 & R7_8 & R7_9 & R7_10 & R7_11 & R7_12 & G1 & G0 & FR7 & GR7).
        unfold CAT in MS7. eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5. exact MS7.
        rewrite R6_8 in R7_10, R7_8. rewrite R6_9 in R7_11, R7_9.
        assert (AG7: forall a k, (a + k <= sp - 112 \/ sp - 32 <= a) -> (a + k <= 457504 \/ 457506 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M6 M7 a k).
        { intros a k H1a H2a Ha Hk i Hi. apply FR7; rewrite BG.unsigned_lit by lia; lia. }
        assert (ES7: e1_statics M7 true fl av uid rnd canary hw).
        { eapply (e1_statics_reguard M6 M7). exact ES6. exact G0. exact G1. intros a Ha Hna. apply FR7; rewrite BG.unsigned_lit.
          all: unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha, Hna; try lia. }
        assert (HH7: hi_heap HI ((A, 160) :: LB) (debit L cr2 160) M7 (m_vmmaps model5)).
        { eapply hi_heap_clientx. exact HH6. lia. 2: exact GR7. intros a Ha.
          destruct (Z_lt_le_dec a 457504) as [L0|G0']. left; apply FR7; rewrite BG.unsigned_lit by lia; lia.
          destruct (Z_lt_le_dec a 457506) as [L0'|G0'']. right; right; right. unfold statx, SYSCAT_GUARD. lia.
          destruct (Z_lt_le_dec a (sp - 112)) as [L1|G1']. left; apply FR7; rewrite BG.unsigned_lit by lia; lia.
          destruct (Z_lt_le_dec a (sp - 32)) as [L2|G2]. right; left; lia. left; apply FR7; rewrite BG.unsigned_lit by lia; lia. }
        assert (DEF7: L5.defined M7 (sp - 8672) 8672) by (eapply L5.defined_grows; [exact GR7 | exact DEF6]).
        assert (DEFA7: L5.defined M7 A 160) by (eapply L5.defined_grows; [exact GR7 | exact DEFA6]).
        assert (R7i: forall i, In i [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg i) = getr R (reg i)).
        { intros i Hi. rewrite (K7 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply R6i. exact Hi. }
        pose proof ES7 as (_ & _ & _ & _ & _ & TDL & LMC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC1s & IC2s & IC3s).
        unfold TD_LOCALE, GLOBAL_LOCALE in TDL. unfold LOCALE_MSGCAT in LMC.
        assert (HQ7: L5C.hpres L LB sp STRCTOR_SCR Wf M M7).
        { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp STRCTOR_SCR Wf M M6 M7 [(sp - 112, 80); (457504, 2)]). exact LBWF. uscr; lia. exact HQ6.
          intros x Hx. apply FR7; intros Hin. apply (Hx (sp - 112, 80)). left; reflexivity. unfold L5.in_rng; cbn. lia.
          apply (Hx (457504, 2)). right; left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR7.
          constructor. apply L5PK.wr_scratch; uscr; lia. constructor. eapply L5PK.wr_declared. right; right; left; reflexivity. unfold SYSCAT_GUARD; lia. unfold SYSCAT_GUARD; lia. constructor. }
        pose proof (FRA0 M6 M7 P6 ltac:(apply AG7; lia) ltac:(apply AG7; lia)) as P7.
        assert (Z7: forall i, 0 <= i < 160 -> (i < 8 \/ 48 <= i < 60) -> L5.u8_at RSEGS M7 (A + i) 0).
        { intros i Hi Hr. eapply (L5C.u8_at_agree RSEGS M6 M7). apply AG7; lia. lia. lia.
          replace (A + i) with (A + 128 - 128 + i) by lia. apply (u8_of_zeros M6 _ 160 i Z6). lia. }
        eapply (e1_mid fx7 R R7 M M7 model model5 K LB cr cr2 o sp fbo s fl av uid rnd canary hw A HK0 NP H2 H3 H4 A16 SLO SHI STOP Olo Ohi Hfbo AVTOP LBWF CR2 CR41
                  R7_2 R7_8 R7_9 R7_10 R7_11 R7_12 R7i DEF7 DEFA7 ES7 P7 Z7 HH7 MOK5 ltac:(eapply L5C.model_but_vm_trans; [exact MBV2 | exact MBV5]) ltac:(lia) BR1 BR2 ltac:(lia) BA HQ7 KE).
Qed.

End WithHeap.
End SCFG_2.

End L5STRH.
