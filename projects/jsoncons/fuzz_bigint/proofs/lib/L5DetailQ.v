(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_20088_210bc BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce BigZskip
     BigModel BigFactsBase BigFactsOps BigFactsRun BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreSpecs L5KnP L5ParseArith L5ParseKit L5ParseSpecs L5DetailA L5DetailP ZskipAll L5DetailZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5DETQ.
Import L5CS L5PS L5DA L5DETZ L5DETP.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Ltac uscr := unfold DETAIL_SCR, ADDD_SCR, MUL10_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis Hres : reserve_spec L HI.
Hypothesis Hmul : mul10_spec L HI.
Hypothesis Hadd : addd_spec L HI.
Hypothesis Hasg : assign_spec L HI.
Hypothesis Hdel : opdel_sized_spec L HI.
(* [comment removed for export] *)
Hypothesis KPOS : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L.
(* [comment removed for export] *)
Local Abbreviation credit_le_refl := (L5DETP.credit_le_refl L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation credit_le_trans := (L5DETP.credit_le_trans L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation credit_le_debit := (L5DETP.credit_le_debit L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation debit_mono := (L5DETP.debit_mono L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation debit_le_amount := (L5DETP.debit_le_amount L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation vblk_pos := (L5DETP.vblk_pos L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation parse_debit_le := (L5DETP.parse_debit_le L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation IMGLO := (L5DETP.IMGLO L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation IMGHI := (L5DETP.IMGHI L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation SEGSB := (L5DETP.SEGSB L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation ERRNO_LO := (L5DETP.ERRNO_LO L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation ERR := (L5DETP.ERR L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fb3_facts := (L5DETP.fb3_facts L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fbN_land1 := (L5DETP.fbN_land1 L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fbN_land2 := (L5DETP.fbN_land2 L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fbN_range := (L5DETP.fbN_range L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fbN_bit0 := (L5DETP.fbN_bit0 L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation assign_fb_res := (L5DETP.assign_fb_res L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation big_at_reflag := (L5DETP.big_at_reflag L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation obj_limbs_reflag := (L5DETP.obj_limbs_reflag L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation hpres_defined := (L5DETP.hpres_defined L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation credit_ok_le := (L5DETP.credit_ok_le L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation round_up_Z := (L5DETP.round_up_Z L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation ws_is_wlist := (L5DETP.ws_is_wlist L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Section CTX.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit).
Variables (p o sp r fb : Z) (neg : bool) (ds : list Z).
Local Abbreviation m := (Z.of_nat (length ds)).   
Local Abbreviation negz := (if neg then 1 else 0).   
Local Abbreviation o' := (sp - 96).   (* [comment removed for export] *)
Hypothesis HK0 : K [].
Hypothesis MOK0 : model_ok model0.
Hypothesis RA : L5.ra_ok r.
Hypothesis H0_1 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis H0_2 : getr R0 (reg 2) = Z_to_bv 64 sp.
Hypothesis H0_4 : getr R0 (reg 4) = Z_to_bv 64 TP.
Hypothesis Hlen : (1 <= length ds <= 4999)%nat.
Hypothesis A16 : sp mod 16 = 0.
Hypothesis SLO : hl_sptop L - 2 ^ 23 + DETAIL_SCR <= sp.    (* [comment removed for export] *)
Hypothesis SHI : sp <= hl_sptop L.
Hypothesis STOP : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.   (* [comment removed for export] *)
Hypothesis Hfb : 0 <= fb < 256.
Hypothesis Hfb3 : Z.land fb 3 = 0.
Hypothesis Ao : o mod 8 = 0.
Hypothesis Olo : sp <= o.
Hypothesis Ohi : o + 32 <= hl_sptop L.
Hypothesis DSR : Forall (fun c => 0 <= c < 256) ds.
Hypothesis Plo : 4096 <= p.
Hypothesis Phi : p + m <= 2 ^ 47.
Hypothesis DAT : digits_at L LB sp p (length ds).
Hypothesis APO : p + m <= o \/ o + 32 <= p.
Hypothesis CRED : parse_credit L cr (length ds).
Hypothesis LBWF : L5PK.lb_wf L LB.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
    detail_post L LB cr M0 M' R0 R' o sp fb neg ds LB' cr' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (cfg R' r M' model') K.
(* [comment removed for export] *)
Local Abbreviation regsK := (L5DETP.regsK R0).
Local Abbreviation frameK := (L5DETP.frameK R0 sp r).
Local Abbreviation frameK_agree := (L5DETP.frameK_agree L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation vobj := (L5DETP.vobj L LB cr sp ds).
Local Abbreviation vb_dyn := (L5DETP.vb_dyn L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation vb_neg := (L5DETP.vb_neg L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation vobj_step := (L5DETP.vobj_step L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation dinvG := (L5DETP.dinvG L HI R0 M0 model0 LB cr p o sp r fb neg ds).
Local Abbreviation dinv := (L5DETP.dinv L HI R0 M0 model0 LB cr p o sp r fb neg ds).
Local Abbreviation vblk_bound := (L5DETP.vblk_bound L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation hpres_nil_o := (L5DETP.hpres_nil_o L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation not_digits_ok := (L5DETP.not_digits_ok L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation err_path := (L5DETP.err_path L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation vobj_agree := (L5DETP.vobj_agree L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation pow10_le_m := (L5DETP.pow10_le_m L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation firstn_digits_bound := (L5DETP.firstn_digits_bound L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation digits_ok_S := (L5DETP.digits_ok_S L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation digits_outside := (L5DETP.digits_outside L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation digits_agree := (L5DETP.digits_agree L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation bytes_agree := (L5DETP.bytes_agree L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation digit_step := (L5DETP.digit_step L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Lemma exit_path (fx : FPState) R M model LBc crc dyn sto ws :
  getr R (reg 2) = Z_to_bv 64 o' -> getr R (reg 4) = Z_to_bv 64 TP -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 19) = Z_to_bv 64 negz ->
  getr R (reg 8) = Z_to_bv 64 (p + m) ->
  regsK R -> frameK M -> vobj M LBc crc dyn sto ws (dec ds) ->
  L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) -> L5.writable RSEGS M o 32 ->
  hi_heap HI LBc crc M (m_vmmaps model) -> model_ok model -> model_but_vm model0 model ->
  L5C.hpres L LB sp DETAIL_SCR [] M0 M ->
  digits_ok ds -> 0 < dec ds ->
  srealizes RSEGS SCFG (cfg R DL_EXIT M model) K.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros H2 H4 H9 H19 H8 RK FK VO OB WO HH MOK MBV HP DOK VPOS.
  pose proof MOK as (Mh & Ml & Mm). pose proof RA as [Hr He]. pose proof SLO as SLO'. pose proof (hpres_defined _ _ _ _ _ _ HP) as DEF. uscr.
  assert (WR96: L5.writable RSEGS M (sp - 96) 96).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct FK as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof (wrange (getr R0 (reg 8))) as W8. pose proof (wrange (getr R0 (reg 9))) as W9. pose proof (wrange (getr R0 (reg 18))) as W18.
  pose proof (wrange (getr R0 (reg 19))) as W19. pose proof (wrange (getr R0 (reg 20))) as W20. pose proof (wrange (getr R0 (reg 21))) as W21.
  pose proof (wrange (getr R0 (reg 22))) as W22.
  destruct VO as (VB & VL & VV & VN & V0 & VI & VD).
  pose proof VB as (Vfb & _ & V8 & VS). cbn [L5.bo_fb L5.bo_len L5.bo_st vb] in Vfb, V8, VS.
  pose proof (land3_bits fb (proj1 Hfb) Hfb3) as [B0 B1].
  set (V := dec ds) in *. set (n := nwords V) in *.
  assert (NPOS: (1 <= n)%nat) by (subst n; apply nwords_pos; lia).
  assert (VBND: 0 <= V < 10 ^ m). { subst V; try try subst m. apply dec_bound. apply all_digits_Forall. exact DOK. }
  (* [comment removed for export] *)
  assert (STEP1: exists (fx1 : FPState) R1 M1,
     msteps RSEGS (st fx R DL_EXIT M) (st fx1 R1 ASSIGN M1)
     /\ (forall i, In i KS_A9P -> getr R1 (reg i) = getr R (reg i))
     /\ getr R1 (reg 1) = Z_to_bv 64 134372 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 96)
     /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 (sp - 96)
     /\ L5.u8_at RSEGS M1 (sp - 96) (fbN dyn neg)
     /\ (forall x : word, ~ (sp - 96 <= bv_unsigned x < sp - 96 + 1) -> M1 x = M x) /\ mem_grows M M1).
  { destruct neg.
    - assert (X1: 0 <= fbW dyn < 2 ^ 64) by (destruct dyn; cbn; lia). assert (X2: 0 <= fbW dyn <= 255) by (destruct dyn; cbn; lia).
      assert (WR1: L5.writable RSEGS M (sp - 96) 1) by (eapply L5.writable_sub; [exact WR96| lia | lia]).
      destruct (pa9n_conc fx R M sp o (fbW dyn) H2 H9 H19 ltac:(lia) ltac:(lia) X1 ltac:(lia) A16 WR1 Vfb X2)
        as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & U1 & FR1 & GR1).
      exists fx1, R1, M1. split. unfold DL_EXIT, ASSIGN. exact MS1. split. intros i Hi. apply K1. revert Hi. clear. intros Hi. exact Hi.
      split. exact R1_1. split. exact R1_2. split. exact R1_10. split. exact R1_11. split. unfold fbN. exact U1.
      split. intros x Hx. apply FR1. replace (sp + -96) with (sp - 96) by lia. exact Hx. exact GR1.
    - destruct (pa9p_conc fx R M sp o H2 H9 H19 ltac:(lia) ltac:(lia) ltac:(lia) A16)
        as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & FR1 & GR1).
      exists fx1, R1, M1. split. unfold DL_EXIT, ASSIGN. exact MS1. split. intros i Hi. apply K1. revert Hi. clear. intros Hi. exact Hi.
      split. exact R1_1. split. exact R1_2. split. exact R1_10. split. exact R1_11. split.
      { unfold fbN. unfold L5.u8_at. rewrite (L5C.rdn_agree RSEGS M M1 1 (sp - 96)). exact Vfb. lia. lia. intros i Hi. apply FR1. }
      split. intros x Hx. apply FR1. exact GR1. }
  clear H2 H9 H19.
  destruct STEP1 as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & U1 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  assert (AG1: forall a k, (a + k <= sp - 96 \/ sp - 95 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M1 a k).
  { intros a k Hak Ha Hk i Hi. apply FR1. rewrite BG.unsigned_lit by lia. lia. }
  assert (DEF1: L5.defined M1 (sp - DETAIL_SCR) DETAIL_SCR) by (eapply L5.defined_grows; [exact GR1| exact DEF]).
  assert (STDYN: forall cap q, sto = L5.BDyn cap q -> dyn = true).
  { intros cap q E. destruct dyn. reflexivity. exfalso. destruct (VI eq_refl) as ((v0 & v1 & E') & _). rewrite E' in E. discriminate E. }
  (* [comment removed for export] *)
  eapply (Hasg fx1 R1 M1 model K LBc crc o (sp - 96) (sp - 96) 134372 (L5.BO fb 0 (L5.BInl 0 0)) (L5.BO (fbN dyn neg) (length ws) sto) ws).
  - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LBc crc M M1 (m_vmmaps model) [(sp - 96, 1)]). exact HIok. exact HH. exact (ly_ro L LY). lia.
    { intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 96, 1)). left; reflexivity. unfold L5.in_rng; cbn. lia. } exact GR1.
    constructor. left. cbn. lia. constructor.
  - exact MOK.
  - exact HK0.
  - rewrite L5CoreKit.L5K.rl10. exact R1_10.
  - rewrite L5CoreKit.L5K.rl11. exact R1_11.
  - cbn [L5.bo_len]. rewrite VN. pose proof (nwords_bound V (length ds) VBND). pose proof (num_words_est_4999 (length ds) ltac:(lia)). lia.
  - intros D. exfalso. revert D. unfold L5.bo_dyn. cbn [L5.bo_fb]. rewrite B0. discriminate.
  - cbn [L5.bo_len]. intros H3 _. rewrite VN in H3.
    destruct (Nat.ltb_spec (length ds) 39) as [LT|GE].
    { exfalso. pose proof (nwords_le2 V (length ds) ltac:(lia) VBND). lia. }
    destruct dyn. 2: { exfalso. destruct (VI eq_refl) as (_ & _ & _ & M38). lia. }
    destruct (VD eq_refl) as (A & cap & EST & ELB & ECR & _). rewrite ECR.
    eapply credit_ok_le. exact (proj2 CRED). unfold vblk. replace (length ds <? 39)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    rewrite VN, round_up_Z. apply Z.mul_le_mono_nonneg_l. lia. apply Nat2Z.inj_le. apply BigFactsOps.round_up_mono.
    subst n V; try try subst m. apply nwords_bound. exact VBND.
  - rewrite L5CoreKit.L5K.rl1. exact R1_1.
  - apply ra_ok_lit. lia. reflexivity.
  - rewrite L5CoreKit.L5K.rl2. exact R1_2.
  - rewrite L5CoreKit.L5K.rl4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
  - split. { replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    uscr. split. lia. split. lia. split. lia. eapply L5.defined_sub. exact DEF1. lia. lia.
  - eapply (L5C.big_at_agree RSEGS M M1). apply AG1; lia. lia. lia. exact OB.
  - exact Ao.
  - lia.
  - exact Ohi.
  - eapply L5.writable_grows. exact GR1. exact WO.
  - cbn. intros cap q D. discriminate D.
  - (* [comment removed for export] *)
    eapply (big_at_reflag M M1 (sp - 96) (fbW dyn) (fbN dyn neg) (length ws) sto). exact VB. exact U1. pose proof (fbN_range dyn neg); lia.
    rewrite fbN_bit0. destruct dyn; reflexivity. apply AG1; lia. lia. lia.
  - eapply (obj_limbs_reflag M M1 (fbW dyn) (fbN dyn neg) (length ws) sto ws). exact VL.
    intros cap q E. pose proof (STDYN cap q E) as Hd. subst dyn. destruct (VD eq_refl) as (A & cap' & EST & ELB & ECR & ECAP & FRESH & AAL & CAPOK).
    rewrite EST in E. injection E as <- <-. destruct FRESH as (F0 & F1 & F2 & F3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in F1. pose proof vblk_bound.
    pose proof (CAPOK V VBND). rewrite VN. split. apply AG1. left. lia. lia. lia. lia.
  - replace (sp - 96) with (sp + 8 * (-12)) by lia. apply mod16_8. exact A16.
  - lia.
  - lia.
  - cbn [L5.bo_st]. intros cap q E. pose proof (STDYN cap q E) as Hd. subst dyn. destruct (VD eq_refl) as (A & cap' & EST & ELB & _).
    rewrite EST in E. injection E as <- <-. rewrite ELB. left. reflexivity.
  - right. lia.
  - cbn. intros c q c' q' D. discriminate D.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    (* [comment removed for export] *)
    assert (TAIL: forall (fx3 : FPState) R3 M3 model3 LB3 cr3 st',
       getr R3 (reg 2) = Z_to_bv 64 o' -> getr R3 (reg 4) = Z_to_bv 64 TP -> getr R3 (reg 9) = Z_to_bv 64 0 -> getr R3 (reg 8) = Z_to_bv 64 (p + m) ->
       regsK R3 -> frameK M3 ->
       L5.big_at RSEGS M3 o (L5.BO (res_fb fb n neg) n st') -> L5C.obj_limbs RSEGS M3 (L5.BO (res_fb fb n neg) n st') (wlist V n) ->
       match st' with
       | L5.BInl _ _ => (n <= 2)%nat /\ LB3 = LB
       | L5.BDyn cap A => (3 <= n)%nat /\ cap = Z.of_nat (BigModel.round_up n) /\ LB3 = (A, 8 * cap) :: LB /\ L5C.fresh_block L LB M3 A (8 * cap)
       end ->
       credit_le (parse_debit L cr (length ds)) cr3 ->
       hi_heap HI LB3 cr3 M3 (m_vmmaps model3) -> model_ok model3 -> model_but_vm model0 model3 ->
       L5C.hpres L LB sp DETAIL_SCR [(o, 32)] M0 M3 ->
       srealizes RSEGS SCFG (cfg R3 0x20d08 M3 model3) K).
    { intros fx3 R3 M3 model3 LB3 cr3 st' Q2 Q4 Q9 Q8 RK3 FK3 OB3 OL3 ST3 CR3 HH3 MOK3 MBV3 HP3.
      pose proof MOK3 as (Mh3 & Ml3 & Mm3). destruct FK3 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
      destruct (pa11_conc fx3 R3 M3 sp (p + m) 0 r (bv_unsigned (getr R0 (reg 8))) (bv_unsigned (getr R0 (reg 9)))
                  (bv_unsigned (getr R0 (reg 18))) (bv_unsigned (getr R0 (reg 19))) (bv_unsigned (getr R0 (reg 20))) (bv_unsigned (getr R0 (reg 21)))
                  (bv_unsigned (getr R0 (reg 22))) Q2 Q8 Q9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) W8 W9 W18 W19 W20 W21 W22 ltac:(lia) A16
                  D1 D2 D3 D4 D5 D6 D7 D8)
        as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_9 & R4_10 & R4_11 & R4_18 & R4_19 & R4_20 & R4_21 & R4_22 & FR4 & GR4).
      unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh3. exact Ml3.
      { eapply msteps_trans. exact MS4. apply ret_detail. exact R4_1. exact Hr. exact He. }
      assert (AG4: forall a k, L5C.agree_on M3 M4 a k) by (intros a k i Hi; apply FR4).
      apply (KONT fx4 R4 M4 model3 LB3 cr3).
      - split.
        { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
          destruct Hi as [<-|Hi]. { rewrite R4_2, H0_2. reflexivity. }
          destruct Hi as [<-|Hi]. { rewrite (K4 3%nat) by (apply L5KP.In_of_existsb; reflexivity). apply (RK3 3%nat). cbn; tauto. }
          destruct Hi as [<-|Hi]. { rewrite (K4 4%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite Q4, H0_4. reflexivity. }
          destruct Hi as [<-|Hi]. { rewrite R4_8. apply lit_of_word. }
          destruct Hi as [<-|Hi]. { rewrite R4_9. apply lit_of_word. }
          destruct Hi as [<-|Hi]. { rewrite R4_18. apply lit_of_word. }
          destruct Hi as [<-|Hi]. { rewrite R4_19. apply lit_of_word. }
          destruct Hi as [<-|Hi]. { rewrite R4_20. apply lit_of_word. }
          destruct Hi as [<-|Hi]. { rewrite R4_21. apply lit_of_word. }
          destruct Hi as [<-|Hi]. { rewrite R4_22. apply lit_of_word. }
          assert (G: forall j, In j [23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R0 (reg j)).
          { intros j Hj. assert (A2: In j KS_A11) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
            assert (AK: In j [3; 23; 24; 25; 26; 27]%nat) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
            rewrite (K4 j A2). apply (RK3 j AK). }
          apply G. L5CoreKit.L5K.inlist Hi. }
        left. split. lia. split. exact DOK. split. rewrite L5CoreKit.L5K.rl11. exact R4_11.
        unfold parse_post. change (dec ds) with V. change (nwords V) with n.
        exists st'. split.
        { eapply (L5C.big_at_agree RSEGS M3 M4). apply AG4. lia. lia. exact OB3. }
        split.
        { eapply (obj_limbs_reflag M3 M4). exact OL3. intros cap q E. subst st'.
          destruct OB3 as (_ & _ & _ & (_ & _ & _ & X4 & X5 & X6 & X7 & X8)). cbn [L5.bo_len] in X4. rewrite wlist_length. split. apply AG4. lia. }
        split.
        { destruct st' as [v0 v1|cap q]. exact ST3. destruct ST3 as (S1 & S2 & S3 & (S4 & S5 & S6)). split. exact S1. split. exact S2. split. exact S3.
          split. exact S4. split. exact S5. eapply (L5C.defined_agree M3 M4). apply AG4. exact S6. }
        split. exact CR3.
        eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [(o, 32)] M0 M3 M4 []). exact LBWF. uscr; lia. exact HP3.
        intros x Hx. apply FR4. exact GR4. constructor.
      - exact MBV3.
      - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB3 cr3 M3 M4 (m_vmmaps model3) []). exact HIok. exact HH3. exact (ly_ro L LY). lia.
        intros x Hx. apply FR4. exact GR4. constructor. }
    destruct POST as (RP & RA0 & PG). cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_data] in PG. rewrite VN in PG.
    pose proof (RP 2%bv ltac:(cbn; tauto)) as P2. pose proof (RP 8%bv ltac:(cbn; tauto)) as P8. pose proof (RP 4%bv ltac:(cbn; tauto)) as P4.
    rewrite L5CoreKit.L5K.rl2 in P2. rewrite L5CoreKit.L5K.rl8 in P8. rewrite L5CoreKit.L5K.rl4 in P4.
    assert (R2_2: getr R2 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite P2; exact R1_2).
    assert (R2_4: getr R2 (reg 4) = Z_to_bv 64 TP). { rewrite P4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4. }
    assert (R2_8: getr R2 (reg 8) = Z_to_bv 64 (p + m)). { rewrite P8, (K1 8%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H8. }
    assert (RK2: regsK R2).
    { intros i Hi. rewrite (L5CoreKit.L5K.regs_preserved_index R1 R2 i RP) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H').
      rewrite (K1 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK i Hi). }
    assert (MOK2: model_ok model2).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV2); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV2); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV2); exact Y3]]. }
    pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    assert (MBV02: model_but_vm model0 model2) by (eapply L5C.model_but_vm_trans; [exact MBV| exact MBV2]).
    (* [comment removed for export] *)
    assert (PGc: exists W' (grown : bool) str,
        L5C.hpres L LBc (sp - 96) ASSIGN_SCR W' M1 M2 /\ (forall i, i < o \/ o + 32 <= i -> L5.outside W' i) /\
        Forall (L5PK.wr_ok L LB sp DETAIL_SCR [(o, 32)]) W' /\
        (grown = true <-> (3 <= n)%nat) /\
        L5.big_at RSEGS M2 o (L5.BO (assign_fb fb (fbN dyn neg) n grown) n str) /\ L5C.obj_limbs RSEGS M2 (L5.BO (assign_fb fb (fbN dyn neg) n grown) n str) ws /\
        match str with
        | L5.BInl _ _ => grown = false /\ LB2 = LBc /\ cr2 = crc
        | L5.BDyn c a => grown = true /\ c = round_up (Z.of_nat n) /\ LB2 = (a, 8 * c) :: LBc /\ cr2 = debit L crc (8 * c) /\ L5C.fresh_block L LBc M2 a (8 * c)
        end).
    { destruct g as [|A2 cap2].
      - destruct PG as (SM & ELB & ECR & (str & OB2 & OL2 & ST2) & HP2).
        assert (N2: (n <= 2)%nat). { destruct SM as [SM|SM]. exfalso. revert SM. unfold L5.bo_dyn; cbn [L5.bo_fb]. rewrite B0. discriminate. exact SM. }
        eexists. exists false, str. split. exact HP2. split. { intros i Hi r' [<-|[<-|[]]]; unfold L5.in_rng; cbn; lia. }
        split. { constructor. eapply L5PK.wr_declared. left; reflexivity. lia. lia. constructor. eapply L5PK.wr_declared. left; reflexivity. lia. lia. constructor. }
        split. { split. intros X; discriminate X. intros H3. exfalso. lia. }
        split. exact OB2. split. exact OL2. destruct str as [w0 w1|c a]. split. reflexivity. split. exact ELB. exact ECR. destruct ST2.
      - destruct PG as (_ & H3 & ECAP & ELB & ECR & FB2 & OB2 & OL2 & HP2).
        exists [(o, 32)], true, (L5.BDyn cap2 A2).
        split. exact HP2. split. { intros i Hi r' [<-|[]]; unfold L5.in_rng; cbn; lia. }
        split. { constructor. eapply L5PK.wr_declared. left; reflexivity. lia. lia. constructor. }
        split. { split. intros _. exact H3. intros _. reflexivity. }
        split. exact OB2. split. exact OL2. split. reflexivity. split. exact ECAP. split. exact ELB. split. exact ECR. exact FB2. }
    clear PG. destruct PGc as (W' & grown & str & HP2 & WO' & WF' & HG & OB2 & OL2 & ST2).
    rewrite (assign_fb_res fb dyn neg n grown Hfb Hfb3 NPOS HG) in OB2, OL2.
    assert (AG2: forall a k, sp - 96 <= a -> a + k <= sp -> L5C.agree_on M1 M2 a k).
    { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP2. uscr; lia. uscr; lia. lia. lia.
      intros i Hi. apply WO'. lia. }
    assert (AG02: forall a k, sp - 95 <= a -> a + k <= sp -> L5C.agree_on M M2 a k).
    { intros a k Ha Hk. eapply L5C.agree_on_trans. apply AG1; lia. apply AG2; lia. }
    assert (FK2: frameK M2). { unfold frameK. repeat split; (eapply (L5C.u64_at_agree RSEGS M M2); [apply AG02; lia| lia | lia | assumption]). }
    destruct FK2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    assert (U2: L5.u8_at RSEGS M2 (sp - 96) (fbN dyn neg)). { eapply (L5C.u8_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact U1. }
    pose proof (hpres_defined _ _ _ _ _ _ HP2) as DEF2.
    assert (WSL: ws = wlist V n) by (subst n; apply ws_is_wlist; [exact (proj1 (proj2 VL)) | exact VV | exact VN]).
    (* [comment removed for export] *)
    assert (HP02: L5C.hpres L LB sp DETAIL_SCR [(o, 32)] M0 M2).
    { assert (HP01: L5C.hpres L LB sp DETAIL_SCR [(o, 32)] M0 M1).
      { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [(o,32)] M0 M M1 [(sp - 96, 1)]). exact LBWF. uscr; lia. apply hpres_nil_o. exact HP.
        intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 96, 1)). left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR1.
        constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
      assert (SUBc: L5PK.lb_sub LB LBc).
      { destruct dyn. destruct (VD eq_refl) as (A & cap & _ & -> & _). apply L5PK.lb_sub_cons. destruct (VI eq_refl) as (_ & -> & _). apply L5PK.lb_sub_refl. }
      eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LBc sp DETAIL_SCR [(o,32)] (sp - 96) ASSIGN_SCR W' M0 M1 M2). exact LBWF. uscr; lia. lia.
      exact HP01. exact HP2. exact SUBc. uscr; lia. lia. uscr; lia. exact WF'.
      }
    destruct dyn.
    + (* [comment removed for export] *)
      destruct (VD eq_refl) as (A & cap & EST & ELB & ECR & ECAP & FRESH & AAL & CAPOK). clear VI. subst sto.
      destruct VS as (Vb0 & V16 & V24 & Vlen & Vcap & Aq & QLO & QHI & HAP). destruct FRESH as (F0 & F1 & F2 & F3).
      pose proof vblk_bound as VBB. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in F1.
      assert (X7: L5.u64_at RSEGS M2 (sp - 72) A). { eapply (L5C.u64_at_agree RSEGS M M2). apply AG02; lia. lia. lia. replace (sp - 72) with (sp - 96 + 24) by lia; exact V24. }
      assert (X9: L5.u64_at RSEGS M2 (sp - 80) cap). { eapply (L5C.u64_at_agree RSEGS M M2). apply AG02; lia. lia. lia. replace (sp - 80) with (sp - 96 + 16) by lia; exact V16. }
      pose proof (fbN_range true neg) as FBR.
      assert (X6: 1 <= Z.land (fbN true neg) 1 <= 1) by (rewrite fbN_land1; cbn; lia).
      destruct (pa10d_conc fx2 R2 M2 sp (fbN true neg) A cap R2_2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 U2 ltac:(lia) X6 X7 ltac:(lia) X9 ltac:(lia))
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_9 & R3_10 & R3_11 & FR3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      assert (AG3: forall a k, L5C.agree_on M2 M3 a k) by (intros a k i Hi; apply FR3).
      assert (INA: In (A, 8 * cap) LB2).
      { destruct str as [w0 w1|c a]. destruct ST2 as (_ & -> & _). rewrite ELB. left; reflexivity. destruct ST2 as (_ & _ & -> & _). right. rewrite ELB. left; reflexivity. }
      eapply (Hdel fx3 R3 M3 model2 K LB2 cr2 A (8 * cap) (sp - 96) 0x20d08).
      * eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB2 cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia.
        intros x Hx. apply FR3. exact GR3. constructor.
      * exact MOK2.
      * exact HK0.
      * exact INA.
      * rewrite L5CoreKit.L5K.rl10. exact R3_10.
      * rewrite L5CoreKit.L5K.rl1. exact R3_1.
      * apply ra_ok_lit. lia. reflexivity.
      * rewrite L5CoreKit.L5K.rl2. exact R3_2.
      * rewrite L5CoreKit.L5K.rl4, (K3 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact R2_4.
      * uscr. split. { replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
        split. lia. split. lia. split. lia. eapply L5.defined_grows. exact GR3. eapply L5.defined_sub. exact DEF2. lia. lia.
      * intros fx4 R4 M4 model4 RP4 HP4 MBV4 HH4.
        (* [comment removed for export] *)
        assert (RM: match str with L5.BInl _ _ => lb_remove A LB2 = LB | L5.BDyn c a => lb_remove A LB2 = (a, 8 * c) :: LB /\ In (a, 8 * c) (lb_remove A LB2) end).
        { destruct str as [w0 w1|c a]. destruct ST2 as (_ & -> & _). rewrite ELB. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity.
          destruct ST2 as (_ & Hc & -> & _ & FBk). rewrite ELB. cbn [lb_remove fst].
          assert (NE: (a =? A) = false).
          { apply Z.eqb_neq. intros ->. destruct FBk as ((Y1 & Y2 & Y3 & Y4) & BA & _).
            pose proof (BA (A, 8 * cap) ltac:(rewrite ELB; left; reflexivity)) as Z1. cbn in Z1. lia. }
          rewrite NE, Z.eqb_refl. split. reflexivity. left; reflexivity. }
        assert (SUB4: L5PK.lb_sub LB (lb_remove A LB2)). { destruct str as [w0 w1|c a]. rewrite RM. apply L5PK.lb_sub_refl. rewrite (proj1 RM). apply L5PK.lb_sub_cons. }
        assert (AG4: forall a k, sp - 96 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M3 M4 a k).
        { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP4. uscr; lia. uscr; lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
        assert (AG24: forall a k, sp - 96 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M2 M4 a k).
        { intros a k Ha Hk. eapply L5C.agree_on_trans. apply AG3. apply AG4; lia. }
        pose proof (RP4 2%bv ltac:(cbn; tauto)) as T2. pose proof (RP4 8%bv ltac:(cbn; tauto)) as T8. pose proof (RP4 9%bv ltac:(cbn; tauto)) as T9. pose proof (RP4 4%bv ltac:(cbn; tauto)) as T4.
        rewrite L5CoreKit.L5K.rl2 in T2. rewrite L5CoreKit.L5K.rl8 in T8. rewrite L5CoreKit.L5K.rl9 in T9. rewrite L5CoreKit.L5K.rl4 in T4.
        assert (MOK4: model_ok model4).
        { destruct MOK2 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV4); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV4); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV4); exact Y3]]. }
        apply (TAIL fx4 R4 M4 model4 (lb_remove A LB2) cr2 str).
        -- rewrite T2. exact R3_2.
        -- rewrite T4, (K3 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact R2_4.
        -- rewrite T9. exact R3_9.
        -- rewrite T8, (K3 8%nat) by (apply L5KP.In_of_existsb; reflexivity). exact R2_8.
        -- intros i Hi. rewrite (L5CoreKit.L5K.regs_preserved_index R3 R4 i RP4) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H').
           rewrite (K3 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK2 i Hi).
        -- unfold frameK. repeat split; (eapply (L5C.u64_at_agree RSEGS M2 M4); [apply AG24; lia| lia | lia | assumption]).
        -- eapply (L5C.big_at_agree RSEGS M2 M4). apply AG24; lia. lia. lia. exact OB2.
        -- rewrite <- WSL. eapply (obj_limbs_reflag M2 M4). exact OL2. intros c q E. subst str. destruct ST2 as (_ & Hc & EL2 & _ & FBk).
           destruct FBk as ((Y0 & Y1 & Y2 & Y3 & Y4) & BA & _). pose proof Y1 as Y1h. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Y1. rewrite VN.
           assert (NC: 8 * Z.of_nat n <= 8 * c).
           { rewrite Hc. unfold round_up. pose proof (Z_div_mod_eq_full (Z.of_nat n) 8). pose proof (Z.mod_pos_bound (Z.of_nat n) 8 ltac:(lia)). lia. }
           split. 2: lia.
           eapply L5C.agree_on_trans. apply AG3. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP4. apply (proj2 RM). lia. exact Y1h. lia.
           lia. lia. intros i Hi. apply L5C.outside_nil.
        -- destruct str as [w0 w1|c a].
           ++ split. { destruct (Nat.lt_ge_cases n 3). lia. exfalso. destruct ST2 as (GF & _). pose proof (proj2 HG ltac:(lia)) as GT. rewrite GF in GT. discriminate GT. } exact RM.
           ++ destruct ST2 as (GT & Hc & EL2 & ECR2 & FBk). split. apply HG. exact GT. split. rewrite Hc. apply round_up_Z. split. exact (proj1 RM).
              destruct FBk as (BR & BA & BD). split. exact BR. split. { intros b Hb. apply BA. rewrite ELB. right. exact Hb. }
              destruct BR as (Y0 & Y1 & Y2 & Y3 & Y4). pose proof Y1 as Y1h. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Y1.
              eapply (L5C.defined_agree M2 M4). 2: exact BD.
              eapply L5C.agree_on_trans. apply AG3. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP4. apply (proj2 RM). lia. exact Y1h. lia.
              lia. lia. intros i Hi. apply L5C.outside_nil.
        -- destruct str as [w0 w1|c a].
           ++ destruct ST2 as (_ & _ & ->). rewrite ECR. unfold parse_debit. apply credit_le_debit. apply vblk_pos.
           ++ destruct ST2 as (GT & Hc & _ & -> & _). rewrite ECR. unfold parse_debit. apply debit_le_amount.
              pose proof (proj1 HG GT) as N3.
              destruct (Nat.ltb_spec (length ds) 39) as [LT|GE]. { exfalso. pose proof (nwords_le2 V (length ds) ltac:(lia) VBND). lia. }
              unfold vblk. replace (length ds <? 39)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
              rewrite Hc, round_up_Z. apply Z.mul_le_mono_nonneg_l. lia. apply Nat2Z.inj_le. apply BigFactsOps.round_up_mono. subst n V; try try subst m. apply nwords_bound. exact VBND.
        -- exact HH4.
        -- exact MOK4.
        -- eapply L5C.model_but_vm_trans. exact MBV02. exact MBV4.
        -- assert (HP03: L5C.hpres L LB sp DETAIL_SCR [(o, 32)] M0 M3).
           { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [(o,32)] M0 M2 M3 []). exact LBWF. uscr; lia. exact HP02. intros x Hx. apply FR3. exact GR3. constructor. }
           eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB (lb_remove A LB2) sp DETAIL_SCR [(o,32)] (sp - 96) OPDEL_SCR [] M0 M3 M4). exact LBWF. uscr; lia. lia.
           exact HP03. exact HP4. exact SUB4. uscr; lia. lia. uscr; lia. constructor.
       + (* [comment removed for export] *)
      destruct (VI eq_refl) as ((v0 & v1 & EST) & ELB & ECR & M38). clear VD. subst sto.
      assert (GF: grown = false). { destruct grown. 2: reflexivity. exfalso. pose proof (proj1 HG eq_refl). pose proof (nwords_le2 V (length ds) M38 VBND). lia. }
      subst grown. destruct str as [w0 w1|c a]. 2: { destruct ST2 as (X & _). discriminate X. }
      destruct ST2 as (_ & ELB2 & ECR2).
      assert (X6: 0 <= Z.land (fbN false neg) 1 <= 0) by (rewrite fbN_land1; cbn; lia).
      pose proof (fbN_range false neg) as FBR.
      destruct (pa10i_conc fx2 R2 M2 sp (fbN false neg) R2_2 ltac:(lia) ltac:(lia) ltac:(lia) A16 U2 ltac:(lia) X6)
        as (fx3 & R3 & M3 & MS3 & K3 & R3_2 & R3_9 & FR3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      assert (AG3: forall a k, L5C.agree_on M2 M3 a k) by (intros a k i Hi; apply FR3).
      apply (TAIL fx3 R3 M3 model2 LB cr2 (L5.BInl w0 w1)).
      * exact R3_2.
      * rewrite (K3 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact R2_4.
      * exact R3_9.
      * rewrite (K3 8%nat) by (apply L5KP.In_of_existsb; reflexivity). exact R2_8.
      * intros i Hi. rewrite (K3 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK2 i Hi).
      * unfold frameK. repeat split; (eapply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3| lia | lia | assumption]).
      * eapply (L5C.big_at_agree RSEGS M2 M3). apply AG3. lia. lia. exact OB2.
      * rewrite <- WSL. eapply (obj_limbs_reflag M2 M3). exact OL2. intros c q E. discriminate E.
      * split. 2: reflexivity. destruct (Nat.lt_ge_cases n 3). lia. exfalso. pose proof (proj2 HG ltac:(lia)). discriminate.
      * rewrite ECR2, ECR. apply parse_debit_le.
      * rewrite <- ELB, <- ELB2. eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB2 cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia.
        intros x Hx. apply FR3. exact GR3. constructor.
      * exact MOK2.
      * exact MBV02.
      * eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [(o,32)] M0 M2 M3 []). exact LBWF. uscr; lia. exact HP02. intros x Hx. apply FR3. exact GR3. constructor.
Qed.

(* [comment removed for export] *)
End CTX.
End WithHeap.
End SCFG_1.
End L5DETQ.
