(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_201fc_21084 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkDivBaseU BigModel BigFactsDigits BigFactsRun
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5KnP L5ParseArith L5ParseKit L5ParseSpecsU L5Bytes L5CstrAU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5CSTU.
Import L5CSU L5PSU L5CSAU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition CRET : Z := 0x20bbc.  Definition CAFT : Z := 0x20ba0.
Ltac uscr := unfold CSTR_SCR, TOBIG_SCR, DETAIL_SCR, ADDD_SCR, MUL10_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.

Lemma retc fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R CRET M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M CRET W_20bbc r F_20bbc eq_refl D_20bbc H1 Hr He). Qed.
Lemma lit_of_word (w : word) : Z_to_bv 64 (bv_unsigned w) = w.
Proof. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma wrange (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. Qed.
Lemma ra_ok_lit z : 0 <= z < 2 ^ 47 -> z mod 2 = 0 -> L5.ra_ok z.
Proof. intros; split; assumption. Qed.
Lemma land252_3 fb : 0 <= fb < 256 -> Z.land (Z.land fb 252) 3 = 0.
Proof. intros H. rewrite <- Z.land_assoc. change (Z.land 252 3) with 0. apply Z.land_0_r. Qed.

(* [comment removed for export] *)
Lemma alit_bytes M : L5.img_clear M 0x10000 0x20000 -> L5.bytes_at RSEGS M ALIT alit_digits.
Proof.
  intros IC i Hi. unfold L5.u8_at, ALIT. rewrite (L5B.rdn_S RSEGS). rewrite (IC (75691 + Z.of_nat i)) by (cbn in Hi; lia).
  cbn in Hi. do 38 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma alit_facts : Z.of_nat (length alit_digits) = 38 /\ split_sign alit_digits = (false, alit_digits) /\ Forall (fun c => 0 <= c < 256) alit_digits /\ digits_ok alit_digits
                   /\ nwords (dec alit_digits) = 2%nat /\ wlist (dec alit_digits) 2 = [A0; A1].
Proof.
  split. reflexivity. split. reflexivity.
  split. { unfold alit_digits. repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
  split. { unfold digits_ok, alit_digits. repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
  split. vm_compute. reflexivity. vm_compute. reflexivity.
Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis Htb4 : tobig4_spec L HI.

Lemma IMGHI : hl_img_hi L <= 0x7fff7f800000. Proof. rewrite (ly_img_hi L LY). lia. Qed.
Lemma ERR : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L. Proof. rewrite (ly_errno L LY), (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.

Theorem cstr_ok : cstr_spec L HI.
Proof.
  intros fx R M model K LB cr o sp r fbo HH MOK HK0 H10 H11 CRED H1 RA H2 H3 H4 STK IC Ufb Hfbo Ao Olo Ohi WO KN.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). pose proof RA as [Hr He]. uscr.
  pose proof (L5PK.lb_wf_of_heap L HI LB cr M _ HIok HH) as LBWF.
  rewrite L5CoreKit.L5K.rl10 in H10. rewrite L5CoreKit.L5K.rl11 in H11. rewrite L5CoreKit.L5K.rl1 in H1. rewrite L5CoreKit.L5K.rl2 in H2.
  rewrite L5CoreKit.L5K.rl3 in H3. rewrite L5CoreKit.L5K.rl4 in H4. unfold ALIT in H11.
  pose proof alit_facts as (AL & ASP & AR & ADG & ANW & AWL).
  assert (WR32: L5.writable RSEGS M (sp - 32) 32). { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct (pc1u_conc fx R M sp o (bv_unsigned (getr R (reg 12))) fbo H2 H10 H11 (eq_sym (lit_of_word _)) ltac:(lia) ltac:(lia) (wrange _) ltac:(lia) ltac:(lia) A16 WR32 WO Ufb
              ltac:(lia) ltac:(lia) Ao ltac:(lia) IC)
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & R1_12 & R1_13 & R1_18 & C24 & C16 & C8 & Cfb & F32 & F24 & F16 & F8 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { unfold CSTR. exact MS1. }
  assert (AG1: forall a k, (a + k <= sp - 32 \/ sp <= a) -> (a + k <= o \/ o + 32 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M1 a k).
  { intros a k H1a H2a Ha Hk i Hi. apply FR1; rewrite BG.unsigned_lit by lia; lia. }
  assert (HP1: L5C.hpres L LB sp CSTR_SCR [(o, 32)] M M1).
  { apply L5C.hpres_intro.
    - intros a (Ha & CA & NE & OW). apply FR1; rewrite BG.unsigned_lit by lia. 2: { intros Hin. apply (OW (o, 32)). left; reflexivity. unfold L5.in_rng; cbn. lia. }
      destruct CA as [IB|[[S1 S2]|IM]]. destruct IB as (bb & Hb & Hin). pose proof (LBWF bb Hb) as (Q0 & Q1 & Q2). lia. uscr. lia. rewrite (ly_img_hi L LY) in IM. lia.
    - uscr. intros i Hi. apply GR1. apply DEF. lia.
    - intros a _ _ _ Hd. apply GR1. exact Hd. }
  rewrite H1, BG.unsigned_lit in F8 by lia.
  eapply (Htb4 fx1 R1 M1 model K LB cr ALIT o (sp - 32) CAFT (Z.land fbo 252) alit_digits).
  - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M M1 (m_vmmaps model) [(sp - 32, 32); (o, 32)]). exact HIok. exact HH. exact (ly_ro L LY). lia.
    { intros x Hx. apply FR1; intros Hin. apply (Hx (sp - 32, 32)). left; reflexivity. unfold L5.in_rng; cbn. lia. apply (Hx (o, 32)). right; left; reflexivity. unfold L5.in_rng; cbn. lia. }
    exact GR1. constructor. left. cbn. lia. constructor. left. cbn. lia. constructor.
  - exact MOK.
  - exact HK0.
  - rewrite L5CoreKit.L5K.rl10. exact R1_10.
  - rewrite L5CoreKit.L5K.rl11, AL. exact R1_11.
  - rewrite L5CoreKit.L5K.rl12. exact R1_12.
  - replace (length alit_digits) with 38%nat by (apply Nat2Z.inj; rewrite AL; reflexivity). lia.
  - rewrite ASP. cbn [snd]. replace (length alit_digits) with 38%nat by (apply Nat2Z.inj; rewrite AL; reflexivity). exact CRED.
  - rewrite L5CoreKit.L5K.rl1. exact R1_1.
  - apply ra_ok_lit. unfold CAFT; lia. reflexivity.
  - rewrite L5CoreKit.L5K.rl2. exact R1_2.
  - rewrite L5CoreKit.L5K.rl3, (K1 3%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H3.
  - rewrite L5CoreKit.L5K.rl4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
  - split. { replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    uscr. split. lia. split. lia. split. lia. eapply L5.defined_grows. exact GR1. eapply L5.defined_sub. exact DEF. lia. lia.
  - unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st Z.of_nat]. rewrite Z.add_0_r in Cfb. split. exact Cfb. split. apply L5PA.land252_range. lia. split. exact C8.
    split. { pose proof (land252_3 fbo Hfbo) as X. apply (f_equal (fun x => Z.testbit x 0)) in X. rewrite Z.land_spec in X. change (Z.testbit 3 0) with true in X.
             rewrite Bool.andb_true_r in X. rewrite X. reflexivity. }
    split. exact C16. split. exact C24. repeat split; lia.
  - apply land252_3. lia.
  - exact Ao.
  - lia.
  - exact Ohi.
  - eapply L5.writable_grows. exact GR1. exact WO.
  - apply alit_bytes. intros i Hi. rewrite <- (IC i Hi). apply FR1; rewrite BG.unsigned_lit by lia; lia.
  - exact AR.
  - unfold ALIT; lia.
  - rewrite AL. unfold ALIT; lia.
  - right; right; right. rewrite AL. unfold ALIT. lia.
  - rewrite AL. unfold ALIT. lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 LB2 cr2 TP MBV2 HH2.
    unfold tobig_post in TP. rewrite ASP in TP. cbn [fst snd] in TP. destruct TP as (RP2 & TPc).
    destruct TPc as [(PAR & R2_11 & PP)|(NP & _ & _)].
    2: { exfalso. destruct NP as [NP|NP]. rewrite ASP in NP. cbn in NP. discriminate NP. apply NP. rewrite ASP. cbn [snd]. exact ADG. }
    assert (MOK2: model_ok model2).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV2); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV2); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV2); exact Y3]]. }
    pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    unfold parse_post in PP. cbv zeta in PP. rewrite ANW, AWL in PP. destruct PP as (st' & OB2 & OL2 & ST2 & CR2 & HPt).
    destruct st' as [v0 v1|cap q]. 2: { destruct ST2 as (X & _). lia. }
    destruct ST2 as (_ & ELB). subst LB2.
    destruct OL2 as (_ & _ & WL). cbn [L5.bo_st L5.bo_len firstn] in WL. injection WL as <- <-.
    replace (res_fb (Z.land fbo 252) 2 false) with (Z.land fbo 252) in OB2 by (unfold res_fb; cbn; lia).
    assert (AG2: forall a k, sp - 32 <= a -> a + k <= sp -> L5C.agree_on M1 M2 a k).
    { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HPt. uscr; lia. uscr; lia. lia. lia.
      intros i Hi r' [<-|[]]. unfold L5.in_rng; cbn. lia. }
    pose proof (RP2 2%bv ltac:(cbn; tauto)) as P2. rewrite L5CoreKit.L5K.rl2 in P2. rewrite L5CoreKit.L5K.rl11 in R2_11.
    destruct (pc2u_conc fx2 R2 M2 sp r (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr R (reg 18)))
                ltac:(rewrite P2; exact R1_2) R2_11 ltac:(lia) ltac:(lia) (wrange _) (wrange _) (wrange _) ltac:(lia) A16
                ltac:(eapply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2; lia | lia | lia | exact F8])
                ltac:(eapply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2; lia | lia | lia | exact F16])
                ltac:(eapply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2; lia | lia | lia | exact F24])
                ltac:(eapply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2; lia | lia | lia | exact F32]))
      as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & FR3 & GR3).
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2.
    { eapply msteps_trans. unfold CAFT in MS3. exact MS3. apply retc. exact R3_1. exact Hr. exact He. }
    assert (AG3: forall a k, L5C.agree_on M2 M3 a k) by (intros a k i Hi; apply FR3).
    apply (KN fx3 R3 M3 model2 cr2).
    + split.
      { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|Hi]. { rewrite R3_2, H2. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite (L5CoreKit.L5K.regs_preserved_index R1 R2 3%nat RP2) by (cbn; tauto). apply K1. apply L5KP.In_of_existsb; reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite (L5CoreKit.L5K.regs_preserved_index R1 R2 4%nat RP2) by (cbn; tauto). apply K1. apply L5KP.In_of_existsb; reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R3_8. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R3_9. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R3_18. apply lit_of_word. }
        assert (G: forall j, In j [19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
        { intros j Hj. assert (A3: In j KS_C2 /\ In j L5CoreKit.L5K.CS /\ In j KS_C1) by (pose proof Hj as H'; cbn in H'; repeat (destruct H' as [<-|H']; [repeat split; apply L5KP.In_of_existsb; reflexivity|]); destruct H').
          destruct A3 as (A3 & AC & A1). rewrite (K3 j A3), (L5CoreKit.L5K.regs_preserved_index R1 R2 j RP2 AC). apply K1. exact A1. }
        apply G. L5CoreKit.L5K.inlist Hi. }
      split. { eapply (L5C.big_at_agree RSEGS M2 M3). apply AG3. lia. lia. exact OB2. }
      split. exact CR2.
      eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp CSTR_SCR [(o,32)] M M2 M3 []). exact LBWF. uscr; lia.
      eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp CSTR_SCR [(o,32)] (sp - 32) TOBIG_SCR [(o,32)] M M1 M2). exact LBWF. uscr; lia. lia. exact HP1. exact HPt. apply L5PK.lb_sub_refl. uscr; lia. lia. uscr; lia.
      constructor. eapply L5PK.wr_declared. left; reflexivity. lia. lia. constructor.
      intros x Hx. apply FR3. exact GR3. constructor.
    + exact MBV2.
    + eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia. intros x Hx. apply FR3. exact GR3. constructor.
Qed.
End WithHeap.
End SCFG_1.

End L5CSTU.
