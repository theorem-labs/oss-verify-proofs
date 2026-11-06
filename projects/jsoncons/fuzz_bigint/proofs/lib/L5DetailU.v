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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_201fc_21084 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU BigZskipUb0
     BigModel BigFactsBase BigFactsOps BigFactsRun BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5KnP L5ParseArith L5ParseKit L5ParseSpecsU L5DetailAU L5DetailPU L5DetailQU ZskipAllU L5DetailZU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5DETU.
Import L5CSU L5PSU L5DAU L5DETZU L5DETPU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
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
Local Abbreviation credit_le_refl := (L5DETPU.credit_le_refl L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation credit_le_trans := (L5DETPU.credit_le_trans L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation credit_le_debit := (L5DETPU.credit_le_debit L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation debit_mono := (L5DETPU.debit_mono L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation debit_le_amount := (L5DETPU.debit_le_amount L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation vblk_pos := (L5DETPU.vblk_pos L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation parse_debit_le := (L5DETPU.parse_debit_le L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation IMGLO := (L5DETPU.IMGLO L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation IMGHI := (L5DETPU.IMGHI L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation ERR := (L5DETPU.ERR L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation SEGSB := (L5DETPU.SEGSB L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation ERRNO_LO := (L5DETPU.ERRNO_LO L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fb3_facts := (L5DETPU.fb3_facts L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fbN_land1 := (L5DETPU.fbN_land1 L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fbN_land2 := (L5DETPU.fbN_land2 L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fbN_range := (L5DETPU.fbN_range L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation fbN_bit0 := (L5DETPU.fbN_bit0 L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation assign_fb_res := (L5DETPU.assign_fb_res L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation big_at_reflag := (L5DETPU.big_at_reflag L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation obj_limbs_reflag := (L5DETPU.obj_limbs_reflag L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation hpres_defined := (L5DETPU.hpres_defined L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation credit_ok_le := (L5DETPU.credit_ok_le L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation round_up_Z := (L5DETPU.round_up_Z L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Local Abbreviation ws_is_wlist := (L5DETPU.ws_is_wlist L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS).
Section CTX.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit).
Variables (p o sp r fb : Z) (neg : bool) (ds : list Z).
Local Abbreviation m := (Z.of_nat (length ds)).   
Local Abbreviation negz := (if neg then 1 else 0).   
Local Abbreviation o' := (sp - 112).   (* [comment removed for export] *)
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
Local Abbreviation regsK := (L5DETPU.regsK R0).
Local Abbreviation frameK := (L5DETPU.frameK R0 sp r).
Local Abbreviation frameK_agree := (L5DETPU.frameK_agree L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation vobj := (L5DETPU.vobj L LB cr sp ds).
Local Abbreviation vb_dyn := (L5DETPU.vb_dyn L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation vb_neg := (L5DETPU.vb_neg L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation vobj_step := (L5DETPU.vobj_step L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation dinvG := (L5DETPU.dinvG L HI R0 M0 model0 LB cr p o sp r fb neg ds).
Local Abbreviation dinv := (L5DETPU.dinv L HI R0 M0 model0 LB cr p o sp r fb neg ds).
Local Abbreviation vblk_bound := (L5DETPU.vblk_bound L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation hpres_nil_o := (L5DETPU.hpres_nil_o L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation not_digits_ok := (L5DETPU.not_digits_ok L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation err_path := (L5DETPU.err_path L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation vobj_agree := (L5DETPU.vobj_agree L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation pow10_le_m := (L5DETPU.pow10_le_m L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation firstn_digits_bound := (L5DETPU.firstn_digits_bound L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation digits_ok_S := (L5DETPU.digits_ok_S L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation digits_outside := (L5DETPU.digits_outside L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation digits_agree := (L5DETPU.digits_agree L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation bytes_agree := (L5DETPU.bytes_agree L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Local Abbreviation digit_step := (L5DETPU.digit_step L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
(* [comment removed for export] *)
Local Abbreviation exit_path := (L5DETQU.exit_path L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT).
Lemma dec_acc_shift acc cs : dec_acc acc cs = acc * 10 ^ Z.of_nat (length cs) + dec_acc 0 cs.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  revert acc. induction cs as [|c t IH]; intros acc.
  - cbn. lia.
  - cbn [dec_acc length]. rewrite (IH (acc * 10 + (c - 48))), (IH (0 * 10 + (c - 48))). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
Lemma dec_zero_all cs : digits_ok cs -> dec cs = 0 -> Forall (fun c => c = 48) cs.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  induction cs as [|c t IH]; intros D Z0. constructor.
  unfold digits_ok in D. inversion D; subst. unfold dec in Z0. cbn [dec_acc] in Z0. rewrite dec_acc_shift in Z0.
  pose proof (dec_bound t (all_digits_Forall t ltac:(assumption))) as B. unfold dec in B.
  pose proof (Z.pow_pos_nonneg 10 (Z.of_nat (length t)) ltac:(lia) ltac:(lia)).
  assert (c = 48) by nia. constructor. assumption. apply IH. assumption. unfold dec. nia.
Qed.
Lemma dec_pos_of_nonzero : digits_ok ds -> ~ Forall (fun c => c = 48) ds -> 0 < dec ds.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros D NZ. pose proof (dec_bound ds (all_digits_Forall ds D)) as B.
  destruct (Z.eq_dec (dec ds) 0) as [E|NE]. exfalso. apply NZ. apply dec_zero_all. exact D. exact E. lia.
Qed.

(* [comment removed for export] *)
Lemma nondigit_exit (fx : FPState) R M model LBc crc dyn sto ws (j : nat) :
  (j < length ds)%nat -> (nth j ds 0 < 48 \/ 57 < nth j ds 0) ->
  dinv R M model LBc crc dyn sto ws j -> srealizes RSEGS SCFG (cfg R DL_HEAD M model) K.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros Hj ND DI.
  destruct DI as (H2 & H4 & H18 & H20 & H23 & H9 & H19 & H8 & HJ & HNP & RK & FK & VO & BY & OB & WO & HH & MOK & MBV & HP).
  pose proof MOK as (Mh & Ml & Mm). pose proof SLO as SLO'. uscr.
  set (c := nth j ds 0) in *.
  assert (Uc: L5.u8_at RSEGS M (p + Z.of_nat j) c) by (apply BY; exact Hj).
  pose proof (proj1 (Forall_nth _ _) DSR j 0 Hj) as CR. cbn beta in CR. change (nth j ds 0) with c in CR.
  assert (STEP: exists (fx1 : FPState) R1 M1,
     msteps RSEGS (st fx R DL_HEAD M) (st fx1 R1 DL_ERR M1)
     /\ (forall i, In i KS_A13H -> getr R1 (reg i) = getr R (reg i))
     /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 112) /\ getr R1 (reg 18) = Z_to_bv 64 (p + Z.of_nat j)
     /\ (forall x : word, M1 x = M x) /\ mem_grows M M1).
  { destruct ND as [LT|GT].
    - destruct (pa13lu_conc fx R M sp (p + Z.of_nat j) (Z.of_nat j) (2 ^ 64 - 1 - p) c H2 H18 HJ HNP H23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) Uc ltac:(lia) ltac:(lia) ltac:(lia))
        as (fx1 & R1 & M1 & MS1 & K1 & R1_2 & R1_18 & R1_20 & R1_21 & R1_22 & R1_24 & FR1 & GR1).
      exists fx1, R1, M1. split. unfold DL_HEAD, DL_ERR. exact MS1. split. intros i Hi. apply K1. revert Hi. clear. intros Hi. exact Hi.
      split. exact R1_2. split. exact R1_18. split. exact FR1. exact GR1.
    - destruct (pa13hu_conc fx R M sp (p + Z.of_nat j) (Z.of_nat j) (2 ^ 64 - 1 - p) c H2 H18 HJ HNP H23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) Uc ltac:(lia) ltac:(lia) ltac:(lia))
        as (fx1 & R1 & M1 & MS1 & K1 & R1_2 & R1_18 & R1_20 & R1_21 & R1_22 & R1_24 & FR1 & GR1).
      exists fx1, R1, M1. split. unfold DL_HEAD, DL_ERR. exact MS1. split. exact K1.
      split. exact R1_2. split. exact R1_18. split. exact FR1. exact GR1. }
  destruct STEP as (fx1 & R1 & M1 & MS1 & K1 & R1_2 & R1_18 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  assert (AG1: forall a k, L5C.agree_on M M1 a k) by (intros a k i Hi; apply FR1).
  apply (err_path fx1 R1 M1 model LBc crc dyn sto ws (dec (firstn j ds)) (p + Z.of_nat j)).
  - exact R1_2.
  - rewrite (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
  - exact R1_18.
  - lia.
  - intros i Hi. rewrite (K1 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK i Hi).
  - revert FK. unfold frameK. intros FK. repeat split; (eapply (L5C.u64_at_agree RSEGS M M1); [apply AG1 | lia | lia | apply FK]).
  - apply (vobj_agree M M1). exact VO. exact AG1.
  - eapply (L5C.big_at_agree RSEGS M M1). apply AG1. lia. lia. exact OB.
  - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LBc crc M M1 (m_vmmaps model) []). exact HIok. exact HH. exact (ly_ro L LY). lia.
    intros x Hx. apply FR1. exact GR1. constructor.
  - exact MOK.
  - exact MBV.
  - eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M M1 []). exact LBWF. uscr; lia. exact HP. intros x Hx. apply FR1. exact GR1. constructor.
  - apply (not_digits_ok j c Hj). reflexivity. exact ND.
Qed.

(* [comment removed for export] *)
Lemma loop_ok (k : nat) : forall (fx : FPState) R M model LBc crc dyn sto ws (j : nat),
  (j + S k = length ds)%nat -> digits_ok (firstn j ds) -> ~ Forall (fun c => c = 48) ds ->
  dinv R M model LBc crc dyn sto ws j ->
  srealizes RSEGS SCFG (cfg R DL_HEAD M model) K.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  induction k as [|k IH]; intros fx R M model LBc crc dyn sto ws j Hj DOKj NZ DI.
  - (* [comment removed for export] *)
    destruct (Z_lt_le_dec (nth j ds 0) 48) as [LT|GE]. { apply (nondigit_exit fx R M model LBc crc dyn sto ws j). lia. left; exact LT. exact DI. }
    destruct (Z_lt_le_dec 57 (nth j ds 0)) as [GT|LE]. { apply (nondigit_exit fx R M model LBc crc dyn sto ws j). lia. right; exact GT. exact DI. }
    apply (digit_step fx R M model LBc crc dyn sto ws j). lia. lia. exact DOKj. exact DI.
    intros fx1 R1 M1 model1 LB1 cr1 dyn1 sto1 ws1 DG. clear DI.
    destruct DG as (H2 & H4 & H18 & H20 & H23 & H9 & H19 & H8 & HJ & HNP & RK & FK & VO & BY & OB & WO & HH & MOK & MBV & HP).
    pose proof MOK as (Mh & Ml & Mm). pose proof SLO as SLO'. uscr.
    assert (DSJ: firstn (S j) ds = ds). { replace (S j) with (length ds) by lia. apply firstn_all. }
    rewrite DSJ in VO.
    assert (DOK: digits_ok ds). { rewrite <- DSJ. apply digits_ok_S. lia. exact DOKj. lia. }
    replace (m - Z.of_nat j) with 1 in H20 by lia.
    destruct (pa8xu_conc fx1 R1 M1 sp (p + Z.of_nat j) (Z.of_nat j) (2 ^ 64 - 1 - p) H2 H18 H20 HJ HNP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia))
      as (fx2 & R2 & M2 & MS2 & K2 & R2_2 & R2_18 & R2_20 & R2_21 & R2_22 & FR2 & GR2).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
    assert (AG2: forall a0 k0, L5C.agree_on M1 M2 a0 k0) by (intros a0 k0 i Hi; apply FR2).
    apply (exit_path fx2 R2 M2 model1 LB1 cr1 dyn1 sto1 ws1).
    + exact R2_2.
    + rewrite (K2 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
    + rewrite (K2 9%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H9.
    + rewrite (K2 19%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H19.
    + rewrite (K2 8%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H8.
    + intros i Hi. rewrite (K2 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK i Hi).
    + revert FK. unfold frameK. intros FK. repeat split; (eapply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2 | lia | lia | apply FK]).
    + apply (vobj_agree M1 M2). exact VO. exact AG2.
    + eapply (L5C.big_at_agree RSEGS M1 M2). apply AG2. lia. lia. exact OB.
    + eapply (L5C.writable_agree RSEGS M1 M2). apply AG2. lia. lia. exact WO.
    + eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB1 cr1 M1 M2 (m_vmmaps model1) []). exact HIok. exact HH. exact (ly_ro L LY). lia.
      intros x Hx. apply FR2. exact GR2. constructor.
    + exact MOK.
    + exact MBV.
    + eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M1 M2 []). exact LBWF. uscr; lia. exact HP. intros x Hx. apply FR2. exact GR2. constructor.
    + exact DOK.
    + apply dec_pos_of_nonzero. exact DOK. exact NZ.
  - (* [comment removed for export] *)
    destruct (Z_lt_le_dec (nth j ds 0) 48) as [LT|GE]. { apply (nondigit_exit fx R M model LBc crc dyn sto ws j). lia. left; exact LT. exact DI. }
    destruct (Z_lt_le_dec 57 (nth j ds 0)) as [GT|LE]. { apply (nondigit_exit fx R M model LBc crc dyn sto ws j). lia. right; exact GT. exact DI. }
    apply (digit_step fx R M model LBc crc dyn sto ws j). lia. lia. exact DOKj. exact DI.
    intros fx1 R1 M1 model1 LB1 cr1 dyn1 sto1 ws1 DG. clear DI.
    destruct DG as (H2 & H4 & H18 & H20 & H23 & H9 & H19 & H8 & HJ & HNP & RK & FK & VO & BY & OB & WO & HH & MOK & MBV & HP).
    pose proof MOK as (Mh & Ml & Mm). pose proof SLO as SLO'. uscr.
    destruct (pa8hu_conc fx1 R1 M1 sp (p + Z.of_nat j) (m - Z.of_nat j) (Z.of_nat j) (2 ^ 64 - 1 - p) H2 H18 H20 HJ HNP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia) ltac:(lia))
      as (fx2 & R2 & M2 & MS2 & K2 & R2_2 & R2_18 & R2_20 & R2_21 & R2_22 & FR2 & GR2).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
    assert (AG2: forall a0 k0, L5C.agree_on M1 M2 a0 k0) by (intros a0 k0 i Hi; apply FR2).
    apply (IH fx2 R2 M2 model1 LB1 cr1 dyn1 sto1 ws1 (S j)). lia. { apply digits_ok_S. lia. exact DOKj. lia. } exact NZ.
    split. exact R2_2.
    split. { rewrite (K2 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4. }
    split. { rewrite R2_18. f_equal. lia. }
    split. { rewrite R2_20. f_equal. lia. }
    split. { rewrite (K2 23%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H23. }
    split. { rewrite (K2 9%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H9. }
    split. { rewrite (K2 19%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H19. }
    split. { rewrite (K2 8%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H8. }
    split. { rewrite R2_21. f_equal. lia. }
    split. { exact R2_22. }
    split. { intros i Hi. rewrite (K2 i) by (pose proof Hi as H'; L5CoreKit.L5K.inlist H'). apply (RK i Hi). }
    split. { revert FK. unfold frameK. intros FK. repeat split; (eapply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2 | lia | lia | apply FK]). }
    split. { apply (vobj_agree M1 M2). exact VO. exact AG2. }
    split. { apply (bytes_agree M1 M2). apply AG2. exact BY. }
    split. { eapply (L5C.big_at_agree RSEGS M1 M2). apply AG2. lia. lia. exact OB. }
    split. { eapply (L5C.writable_agree RSEGS M1 M2). apply AG2. lia. lia. exact WO. }
    split. { eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB1 cr1 M1 M2 (m_vmmaps model1) []). exact HIok. exact HH. exact (ly_ro L LY). lia.
             intros x Hx. apply FR2. exact GR2. constructor. }
    split. exact MOK. split. exact MBV.
    eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M1 M2 []). exact LBWF. uscr; lia. exact HP. intros x Hx. apply FR2. exact GR2. constructor.
Qed.

(* [comment removed for export] *)
Lemma first_nonzero (cs : list Z) : ~ Forall (fun c => c = 48) cs ->
  exists z, (z < length cs)%nat /\ (forall j, (j < z)%nat -> nth j cs 0 = 48) /\ nth z cs 0 <> 48.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  induction cs as [|c t IH]; intros NF. { exfalso. apply NF. constructor. }
  destruct (Z.eq_dec c 48) as [->|NE].
  - destruct (IH ltac:(intros F; apply NF; constructor; [reflexivity| exact F])) as (z & Hz & HZ & HNZ).
    exists (S z). split. cbn; lia. split. intros j Hj. destruct j. reflexivity. cbn. apply HZ. lia. cbn. exact HNZ.
  - exists 0%nat. split. cbn; lia. split. intros j Hj; lia. cbn. exact NE.
Qed.
Lemma nwe_le2 (n : nat) : (n <= 38)%nat -> (num_words_est n <= 2)%nat.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros H. unfold num_words_est. destruct (Nat.ltb_spec n 10) as [LT|GE]. lia.
  assert (B1: Z.of_nat n * 3402 / 1024 < 127) by (apply Z.div_lt_upper_bound; lia).
  assert (B0: 0 <= Z.of_nat n * 3402 / 1024) by (apply Z.div_pos; lia).
  assert (B2: (Z.of_nat n * 3402 / 1024 + 1 + 63) / 64 < 3) by (apply Z.div_lt_upper_bound; lia).
  assert (B3: 0 <= (Z.of_nat n * 3402 / 1024 + 1 + 63) / 64) by (apply Z.div_pos; lia). lia.
Qed.
Lemma nwe_ge3 (n : nat) : (39 <= n)%nat -> (3 <= num_words_est n)%nat.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros H. unfold num_words_est. destruct (Nat.ltb_spec n 10) as [LT|GE]. lia.
  assert (B1: 129 <= Z.of_nat n * 3402 / 1024) by (apply Z.div_le_lower_bound; lia).
  assert (B2: 3 <= (Z.of_nat n * 3402 / 1024 + 1 + 63) / 64) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma reg_neq (i j : nat) : i <> j -> (i < 32)%nat -> (j < 32)%nat -> reg i <> reg j.
Proof using L HI LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros Hij Hi Hj E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E.
  change (2 ^ Z.of_N 5) with 32 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma main_path (fx : FPState) R M model :
  ~ Forall (fun c => c = 48) ds ->
  hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> model_but_vm model0 model ->
  getr R (reg 2) = Z_to_bv 64 (sp - 112) -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 10) = Z_to_bv 64 p -> getr R (reg 11) = Z_to_bv 64 48 -> getr R (reg 12) = Z_to_bv 64 (2 ^ 64 - 1) -> getr R (reg 8) = Z_to_bv 64 (p + m) ->
  getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 18) = Z_to_bv 64 p -> getr R (reg 19) = Z_to_bv 64 negz -> getr R (reg 20) = Z_to_bv 64 m ->
  regsK R -> frameK M ->
  L5.bytes_at RSEGS M p ds -> L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) -> L5.writable RSEGS M o 32 ->
  L5C.hpres L LB sp DETAIL_SCR [] M0 M ->
  srealizes RSEGS SCFG (cfg R ZHEAD M model) K.
Proof using LY HIok Hres Hmul Hadd Hasg Hdel KPOS R0 M0 model0 K LB cr p o sp r fb neg ds HK0 MOK0 RA H0_1 H0_2 H0_4 Hlen A16 SLO SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT.
  intros NZ HH MOK MBV H2 H4 H10 H11 H12 H8 H9 H18 H19 H20 RK FK BY OB WO HP.
  pose proof MOK as (Mh & Ml & Mm). pose proof SLO as SLO'. pose proof (hpres_defined _ _ _ _ _ _ HP) as DEF. uscr.
  destruct (first_nonzero ds NZ) as (z & Hz & HZ & HNZ).
  (* [comment removed for export] *)
  destruct (@zskip_loop fx M (seg_rom RSEGS) p m ds eq_refl ltac:(lia)
              ltac:(intros i Hi; apply BY; exact Hi)
              ltac:(intros i Hi; apply (proj1 (Forall_nth _ _) DSR i 0 Hi)) R z
              ltac:(rewrite L5CoreKit.L5K.rl10; exact H10) ltac:(rewrite L5CoreKit.L5K.rl8; exact H8) ltac:(rewrite L5CoreKit.L5K.rl11; exact H11)
              ltac:(rewrite L5CoreKit.L5K.rl12; exact H12) Hz HZ HNZ)
    as (R1 & MS1 & Q10 & Q13 & QR).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml.
  { unfold ZHEAD. rewrite (BIU.pc_lit 134912 (0x20f00%bv : word)) by reflexivity. exact MS1. }
  rewrite <- (BIU.pc_lit ZBR (0x20f14%bv : word)) by reflexivity.
  (* [comment removed for export] *)
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { apply br_20ddc. }
  rewrite <- L5CoreKit.L5K.rl10, Q10. rewrite <- L5CoreKit.L5K.rl8, (QR 8%bv) by (intro X; discriminate X). rewrite L5CoreKit.L5K.rl8, H8.
  cbn [branch_taken]. unfold c_eq. change (bv_eqb (Z_to_bv 64 (p + Z.of_nat z)) (Z_to_bv 64 (p + m))) with (bv_unsigned (Z_to_bv 64 (p + Z.of_nat z)) =? bv_unsigned (Z_to_bv 64 (p + m))).
  rewrite !L5.unsigned_lit by lia. replace (p + Z.of_nat z =? p + m) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (R1i: forall i, i <> 10%nat -> i <> 13%nat -> (i < 32)%nat -> getr R1 (reg i) = getr R (reg i)).
  { intros i N10 N13 Hi. apply QR. rewrite L5CoreKit.L5K.rl10. apply reg_neq; lia. rewrite L5CoreKit.L5K.rl13. apply reg_neq; lia. }
  assert (R1_2: getr R1 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite (R1i 2%nat) by lia; exact H2).
  assert (R1_20: getr R1 (reg 20) = Z_to_bv 64 m) by (rewrite (R1i 20%nat) by lia; exact H20).
  assert (R1_18: getr R1 (reg 18) = Z_to_bv 64 p) by (rewrite (R1i 18%nat) by lia; exact H18).
  assert (WR112: L5.writable RSEGS M (sp - 112) 112).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  (* [comment removed for export] *)
  set (nw := Z.of_nat (num_words_est (length ds))).
  pose proof (num_words_est_4999 (length ds) ltac:(lia)) as NW260.
  assert (STEP3: exists (fx3 : FPState) R3 M3,
     msteps RSEGS (st fx R1 0x20f18 M) (st fx3 R3 RESERVE M3)
     /\ (forall i, In i KS_A4S -> getr R3 (reg i) = getr R1 (reg i))
     /\ getr R3 (reg 1) = Z_to_bv 64 135104 /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 112)
     /\ getr R3 (reg 10) = Z_to_bv 64 (sp - 112) /\ getr R3 (reg 11) = Z_to_bv 64 nw
     /\ L5.u64_at RSEGS M3 (sp - 88) 0 /\ L5.u64_at RSEGS M3 (sp - 96) 0 /\ L5.u64_at RSEGS M3 (sp - 104) 0 /\ L5.u8_at RSEGS M3 (sp - 112) 0
     /\ (forall x : word, ~ (sp - 112 <= bv_unsigned x < sp - 112 + 32) -> M3 x = M x) /\ mem_grows M M3).
  { destruct (Z_lt_le_dec m 10) as [SM|LG].
    - destruct (pa4su_conc fx R1 M sp m R1_2 R1_20 ltac:(lia) ltac:(lia) ltac:(lia) A16 WR112 ltac:(lia))
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_10 & R3_11 & T88 & T96 & T104 & T112 & FR3 & GR3).
      exists fx3, R3, M3. split. unfold RESERVE. exact MS3. split. exact K3. split. exact R3_1. split. exact R3_2. split. exact R3_10.
      split. { rewrite R3_11. subst nw. rewrite <- (L5PA.nwe_small m) by lia. try subst m. rewrite Nat2Z.id. reflexivity. }
      split. exact T88. split. exact T96. split. exact T104. split. exact T112. split. intros x Hx. apply FR3. lia. exact GR3.
    - destruct (pa4lu_conc fx R1 M sp m R1_2 R1_20 ltac:(lia) ltac:(lia) ltac:(lia) A16 WR112 ltac:(lia))
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_10 & R3_11 & T88 & T96 & T104 & T112 & FR3 & GR3).
      exists fx3, R3, M3. split. unfold RESERVE. exact MS3. split. intros i' Hi'. apply K3. revert Hi'. clear. intros Hi'. exact Hi'.
      split. exact R3_1. split. exact R3_2. split. exact R3_10.
      split. { rewrite R3_11. subst nw; try try subst m. rewrite Nat2Z.id. reflexivity. }
      split. exact T88. split. exact T96. split. exact T104. split. exact T112. split. intros x Hx. apply FR3. lia. exact GR3. }
  destruct STEP3 as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_10 & R3_11 & T88 & T96 & T104 & T112 & FR3 & GR3).
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS3.
  assert (AG3: forall a k, (a + k <= sp - 112 \/ sp - 80 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M3 a k).
  { intros a k Hak Ha Hk i Hi. apply FR3. rewrite BG.unsigned_lit by lia. lia. }
  assert (R3i: forall i, In i KS_A4S -> i <> 10%nat -> i <> 13%nat -> getr R3 (reg i) = getr R (reg i)).
  { intros i Hi N10 N13. rewrite (K3 i Hi). apply R1i. exact N10. exact N13.
    revert Hi. clear. intros Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [lia|]). destruct Hi. }
  assert (HP3: L5C.hpres L LB sp DETAIL_SCR [] M0 M3).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M M3 [(sp - 112, 32)]). exact LBWF. uscr; lia. exact HP.
    intros x Hx. apply FR3. intros Hin. apply (Hx (sp - 112, 32)). left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR3.
    constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
  pose proof (hpres_defined _ _ _ _ _ _ HP3) as DEF3.
  (* [comment removed for export] *)
  eapply (Hres fx3 R3 M3 model K LB cr (sp - 112) nw (sp - 112) 135104 (L5.BO 0 0 (L5.BInl 0 0))).
  - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M M3 (m_vmmaps model) [(sp - 112, 32)]). exact HIok. exact HH. exact (ly_ro L LY). lia.
    { intros x Hx. apply FR3. intros Hin. apply (Hx (sp - 112, 32)). left; reflexivity. unfold L5.in_rng; cbn. lia. } exact GR3.
    constructor. left. cbn. lia. constructor.
  - exact MOK.
  - exact HK0.
  - rewrite L5CoreKit.L5K.rl10. exact R3_10.
  - rewrite L5CoreKit.L5K.rl11. exact R3_11.
  - subst nw. lia.
  - cbn. intros D. discriminate D.
  - cbn. intros _ H3. subst nw.
    destruct (Nat.lt_ge_cases (length ds) 39) as [LT|GE]. { exfalso. pose proof (nwe_le2 (length ds) ltac:(lia)). lia. }
    replace (8 * round_up (Z.of_nat (num_words_est (length ds)))) with (vblk (length ds)). exact (proj1 CRED).
    unfold vblk. replace (length ds <? 39)%nat with false by (symmetry; apply Nat.ltb_ge; lia). rewrite round_up_Z. reflexivity.
  - rewrite L5CoreKit.L5K.rl1. exact R3_1.
  - apply ra_ok_lit. lia. reflexivity.
  - rewrite L5CoreKit.L5K.rl2. exact R3_2.
  - rewrite L5CoreKit.L5K.rl4, (R3i 4%nat) by (first [apply L5KP.In_of_existsb; reflexivity | lia]). exact H4. 
  - split. { replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    uscr. split. lia. split. lia. split. lia. eapply L5.defined_sub. exact DEF3. lia. lia.
  - apply big_at_zero. exact T112. replace (sp - 112 + 8) with (sp - 104) by lia; exact T104. replace (sp - 112 + 16) with (sp - 96) by lia; exact T96.
    replace (sp - 112 + 24) with (sp - 88) by lia; exact T88.
  - replace (sp - 112) with (sp + 8 * (-14)) by lia. apply mod16_8. exact A16.
  - lia.
  - lia.
  - eapply L5.writable_sub. eapply L5.writable_grows. exact GR3. exact WR112. lia. lia.
  - (* [comment removed for export] *)
    intros fx4 R4 M4 model4 g LB4 cr4 POST MBV4 HH4.
    destruct POST as (RP & PG).
    assert (MOK4: model_ok model4).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV4); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV4); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV4); exact Y3]]. }
    pose proof MOK4 as (Mh4 & Ml4 & Mm4).
    (* [comment removed for export] *)
    assert (PGc: exists W' dyn sto LBc crc,
       L5C.hpres L LB (sp - 112) RESERVE_SCR W' M3 M4 /\ (forall i, i < sp - 112 \/ sp - 80 <= i -> L5.outside W' i) /\
       Forall (L5PK.wr_ok L LB sp DETAIL_SCR []) W' /\ LB4 = LBc /\ cr4 = crc /\ vobj M4 LBc crc dyn sto [] 0).
    { destruct g as [|A cap].
      - destruct PG as (SM & -> & -> & OB4 & HP4). exists [], false, (L5.BInl 0 0), LB, cr.
        split. exact HP4. split. intros i _. apply L5C.outside_nil. split. constructor. split. reflexivity. split. reflexivity.
        assert (M38: (length ds <= 38)%nat).
        { destruct SM as [SM|SM]. cbn in SM. discriminate SM. destruct (Nat.lt_ge_cases (length ds) 39) as [LT|GE]. lia. exfalso. pose proof (nwe_ge3 (length ds) GE). subst nw. lia. }
        split. exact OB4. split. apply obj_limbs_zero. split. reflexivity. split. rewrite nwords_0. reflexivity. split. lia.
        split. { intros _. split. exists 0, 0; reflexivity. split. reflexivity. split. reflexivity. exact M38. }
        intros D; discriminate D.
      - destruct PG as (_ & N3 & ECAP & -> & -> & FB & _ & OB4 & HP4). cbn [L5.bo_fb L5.bo_len] in OB4. change (Z.lor 0 1) with 1 in OB4.
        exists [(sp - 112, 32)], true, (L5.BDyn cap A), ((A, 8 * cap) :: LB), (debit L cr (8 * cap)).
        split. exact HP4. split. { intros i Hi r' [<-|[]]; unfold L5.in_rng; cbn; lia. }
        split. { constructor. apply L5PK.wr_scratch; uscr; lia. constructor. } split. reflexivity. split. reflexivity.
        assert (M39: (39 <= length ds)%nat).
        { destruct (Nat.lt_ge_cases (length ds) 39) as [LT|GE]. exfalso. pose proof (nwe_le2 (length ds) ltac:(lia)). subst nw. lia. exact GE. }
        assert (V8: 8 * cap = vblk (length ds)).
        { unfold vblk. replace (length ds <? 39)%nat with false by (symmetry; apply Nat.ltb_ge; lia). rewrite ECAP. subst nw. rewrite round_up_Z. reflexivity. }
        split. exact OB4. split. { unfold L5C.obj_limbs; cbn. split. reflexivity. split. constructor. apply L5C.limbs_at_nil. }
        split. reflexivity. split. rewrite nwords_0. reflexivity. split. lia.
        split. intros D; discriminate D.
        intros _. exists A, cap. split. reflexivity. split. reflexivity. split. rewrite V8. reflexivity. split. exact V8.
        split. { eapply (L5PK.fresh_of_block L). apply L5PK.lb_sub_refl. exact FB. }
        split. { destruct FB as ((_ & _ & AM & _) & _). exact AM. }
        intros V' HV'. rewrite ECAP. subst nw. rewrite round_up_Z. apply cap_reserve_ok. exact HV'. }
    clear PG. destruct PGc as (W' & dyn & sto & LBc & crc & HP4 & WO4 & WF4 & -> & -> & VO4).
    assert (AG4: forall a k, sp - 80 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M3 M4 a k).
    { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP4. uscr; lia. uscr; lia. lia. lia. intros i Hi. apply WO4. lia. }
    assert (AG04: forall a k, sp - 80 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M4 a k).
    { intros a k Ha Hk. eapply L5C.agree_on_trans. apply AG3; lia. apply AG4; lia. }
    assert (HP04: L5C.hpres L LB sp DETAIL_SCR [] M0 M4).
    { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp DETAIL_SCR [] (sp - 112) RESERVE_SCR W' M0 M3 M4). exact LBWF. uscr; lia. lia. exact HP3. exact HP4. apply L5PK.lb_sub_refl. uscr; lia. lia. uscr; lia. exact WF4. }
    pose proof (RP 2%bv ltac:(cbn; tauto)) as P2. pose proof (RP 20%bv ltac:(cbn; tauto)) as P20. pose proof (RP 4%bv ltac:(cbn; tauto)) as P4.
    pose proof (RP 18%bv ltac:(cbn; tauto)) as P18.
    rewrite L5CoreKit.L5K.rl2 in P2. rewrite L5CoreKit.L5K.rl20 in P20. rewrite L5CoreKit.L5K.rl4 in P4. rewrite L5CoreKit.L5K.rl18 in P18.
    assert (R4_2: getr R4 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite P2; exact R3_2).
    assert (R4_20: getr R4 (reg 20) = Z_to_bv 64 m). { rewrite P20, (R3i 20%nat) by (first [apply L5KP.In_of_existsb; reflexivity | lia]). exact H20. }
    assert (R4_18: getr R4 (reg 18) = Z_to_bv 64 p). { rewrite P18, (R3i 18%nat) by (first [apply L5KP.In_of_existsb; reflexivity | lia]). exact H18. }
    destruct (pa5u_conc fx4 R4 M4 sp p m R4_2 R4_18 R4_20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia))
      as (fx5 & R5 & M5 & MS5 & K5 & R5_2 & R5_10 & R5_18 & R5_20 & R5_21 & R5_22 & R5_23 & FR5 & GR5).
    eapply (L5.cps_of_msteps RSEGS). exact Mh4. exact Ml4. exact MS5.
    assert (AG5: forall a k, L5C.agree_on M4 M5 a k) by (intros a k i Hi; apply FR5).
    assert (R5i: forall i, In i KS_A5 -> In i L5CoreKit.L5K.CS -> In i KS_A4S -> i <> 10%nat -> i <> 13%nat -> getr R5 (reg i) = getr R (reg i)).
    { intros i H5 HC H4S N10 N13. rewrite (K5 i H5), (L5CoreKit.L5K.regs_preserved_index R3 R4 i RP HC). apply R3i. exact H4S. exact N10. exact N13. }
    apply (loop_ok (length ds - 1) fx5 R5 M5 model4 LBc crc dyn sto [] 0). lia. constructor. exact NZ.
    unfold dinv, dinvG. cbn [firstn dec dec_acc]. rewrite Z.add_0_r, Z.sub_0_r.
    split. exact R5_2.
    split. { rewrite (R5i 4%nat); [exact H4 | apply L5KP.In_of_existsb; reflexivity | apply L5KP.In_of_existsb; reflexivity | apply L5KP.In_of_existsb; reflexivity | lia | lia]. }
    split. exact R5_18.
    split. exact R5_20.
    split. exact R5_23.
    split. { rewrite (R5i 9%nat); [exact H9 | apply L5KP.In_of_existsb; reflexivity | apply L5KP.In_of_existsb; reflexivity | apply L5KP.In_of_existsb; reflexivity | lia | lia]. }
    split. { rewrite (R5i 19%nat); [exact H19 | apply L5KP.In_of_existsb; reflexivity | apply L5KP.In_of_existsb; reflexivity | apply L5KP.In_of_existsb; reflexivity | lia | lia]. }
    split. { rewrite (R5i 8%nat); [exact H8 | apply L5KP.In_of_existsb; reflexivity | apply L5KP.In_of_existsb; reflexivity | apply L5KP.In_of_existsb; reflexivity | lia | lia]. }
    split. exact R5_21.
    split. exact R5_22.
    split. { intros i Hi. rewrite (R5i i). apply (RK i Hi). all: pose proof Hi as H'; cbn in H'.
             all: first [solve [L5CoreKit.L5K.inlist H'] | (repeat (destruct H' as [<-|H']; [lia|]); destruct H')]. }
    split. { revert FK. unfold frameK. intros FK. repeat split; (eapply (L5C.u64_at_agree RSEGS M M5); [eapply L5C.agree_on_trans; [apply AG04; lia| apply AG5] | lia | lia | apply FK]). }
    split. { apply (vobj_agree M4 M5). exact VO4. exact AG5. }
    split. { apply (bytes_agree M4 M5). apply AG5. apply (bytes_agree M3 M4). apply (digits_agree LB (sp - 112) RESERVE_SCR W' M3 M4 HP4 (L5PK.lb_sub_refl LB) ltac:(uscr; lia) ltac:(uscr; lia) ltac:(lia) WF4).
             apply (bytes_agree M M3). 2: exact BY.
             destruct DAT as [Z0|[(Ab & kb & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. exfalso; lia.
             pose proof (LBWF (Ab, kb) Hin) as (W0 & W1 & W2). cbn in W0, W1, W2. apply AG3; lia. apply AG3; lia. apply AG3. left. lia. lia. lia. }
    split. { eapply (L5C.big_at_agree RSEGS M M5). eapply L5C.agree_on_trans. apply AG04; lia. apply AG5. lia. lia. exact OB. }
    split. { eapply (L5C.writable_agree RSEGS M M5). eapply L5C.agree_on_trans. apply AG04; lia. apply AG5. lia. lia. exact WO. }
    split. { eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LBc crc M4 M5 (m_vmmaps model4) []). exact HIok. exact HH4. exact (ly_ro L LY). lia.
             intros x Hx. apply FR5. exact GR5. constructor. }
    split. exact MOK4. split. { eapply L5C.model_but_vm_trans. exact MBV. exact MBV4. }
    eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [] M0 M4 M5 []). exact LBWF. uscr; lia. exact HP04. intros x Hx. apply FR5. exact GR5. constructor.
Qed.

End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem detail_ok : detail_spec L HI.
Proof.
  intros fx R M model K LB cr p o sp r fb neg ds HH MOK HK0 H10 H11 H12 H13 Hlen CRED H1 RA H2 H3 H4 STK OB Hfb3 Ao Olo Ohi WO BY DSR Plo Phi DAT APO KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). pose proof RA as [Hr He].
  pose proof (L5PK.lb_wf_of_heap L HI LB cr M _ HIok HH) as LBWF.
  assert (Hfb: 0 <= fb < 256) by (destruct OB as (_ & Hf & _); cbn [L5.bo_fb] in Hf; exact Hf).
  rewrite L5CoreKit.L5K.rl10 in H10. rewrite L5CoreKit.L5K.rl11 in H11. rewrite L5CoreKit.L5K.rl12 in H12. rewrite L5CoreKit.L5K.rl13 in H13.
  rewrite L5CoreKit.L5K.rl1 in H1. rewrite L5CoreKit.L5K.rl2 in H2. rewrite L5CoreKit.L5K.rl3 in H3. rewrite L5CoreKit.L5K.rl4 in H4.
  destruct ds as [|d0 dt].
  { (* [comment removed for export] *)
    apply (detail_len0 L HI LY HIok KPOS fx R M model K LB cr p o sp r fb neg HH MOK).
    rewrite L5CoreKit.L5K.rl10; exact H10. rewrite L5CoreKit.L5K.rl11; exact H11. rewrite L5CoreKit.L5K.rl13; exact H13.
    rewrite L5CoreKit.L5K.rl1; exact H1. exact RA. rewrite L5CoreKit.L5K.rl2; exact H2. exact STK. exact OB. exact Olo. exact Ohi. exact Plo. cbn in Phi; lia. exact KONT. }
  remember (d0 :: dt) as ds eqn:Eds. assert (Hlen1: (1 <= length ds)%nat) by (subst ds; cbn; lia). clear Eds d0 dt.
  uscr.
  assert (WR112: L5.writable RSEGS M (sp - 112) 112).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  (* [comment removed for export] *)
  destruct (pa1u_conc fx R M sp p (Z.of_nat (length ds)) (if neg then 1 else 0) o H2 H10 H11 H12 H13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct neg; lia) ltac:(lia) Phi ltac:(lia) A16 WR112 ltac:(lia) ltac:(lia))
    as (fx1 & R1 & M1 & MS1 & K1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & R1_12 & R1_18 & R1_19 & R1_20 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { unfold DETAIL. exact MS1. }
  assert (AG1: forall a k, (a + k <= sp - 112 \/ sp <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M1 a k).
  { intros a k Hak Ha Hk i Hi. apply FR1. rewrite BG.unsigned_lit by lia. lia. }
  rewrite H1 in C8. rewrite BG.unsigned_lit in C8 by lia.
  assert (STK1: L5C.stk (hl_sptop L) M1 sp (112 + (112 + (64 + (48 + (64 + (16 + 8224))))))).
  { split. exact A16. split. lia. split. lia. split. lia. eapply L5.defined_grows. exact GR1. exact DEF. }
  assert (OB1: L5.big_at RSEGS M1 o (L5.BO fb 0 (L5.BInl 0 0))). { eapply (L5C.big_at_agree RSEGS M M1). apply AG1; lia. lia. lia. exact OB. }
  assert (WO1: L5.writable RSEGS M1 o 32) by (eapply L5.writable_grows; [exact GR1| exact WO]).
  assert (BY1: L5.bytes_at RSEGS M1 p ds).
  { eapply (L5C.bytes_at_agree RSEGS M M1). 2: lia. 2: lia. 2: exact BY.
    destruct DAT as [Z0|[(Ab & kb & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. exfalso; lia.
    pose proof (LBWF (Ab, kb) Hin) as (W0 & W1 & W2). cbn in W0, W1, W2. apply AG1; lia. apply AG1; lia. apply AG1. left. lia. lia. lia. }
  assert (HH1: hi_heap HI LB cr M1 (m_vmmaps model)).
  { eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M M1 (m_vmmaps model) [(sp - 112, 112)]). exact HIok. exact HH. exact (ly_ro L LY). lia.
    { intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 112, 112)). left; reflexivity. unfold L5.in_rng; cbn. lia. } exact GR1.
    constructor. left. cbn. lia. constructor. }
  destruct (Forall_dec (fun c => c = 48) (fun c => Z.eq_dec c 48) ds) as [ALLZ|NZ].
  - (* [comment removed for export] *)
    apply (detail_allzero L HI LY HIok Hasg KPOS fx1 R1 M M1 model K LB cr p o sp r fb neg ds R HH1 MOK HK0 Hlen1 Hlen ALLZ R1_2).
    + rewrite (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
    + exact R1_10. + exact R1_11. + exact R1_8. + exact R1_9. + exact R1_12. + exact H2. + exact H1. + exact RA.
    + exact C8. + exact C16. + exact C24. + exact C32. + exact C40. + exact C48. + exact C56. + exact C64. + exact C72. + exact C80.
    + intros i Hi. apply K1. revert Hi. clear. intros Hi. cbn in Hi. L5CoreKit.L5K.inlist Hi.
    + exact STK1.
    + exact OB1. + exact Hfb3. + exact Ao. + exact Olo. + exact Ohi. + exact WO1. + exact BY1. + exact Plo. + exact Phi.
    + (* [comment removed for export] *)
      split. { intros a (Ha & CA & NE & _). apply FR1. rewrite BG.unsigned_lit by lia.
               destruct CA as [IB|[[S1 S2]|IM]].
               * destruct IB as (bb & Hb & Hin). pose proof (LBWF bb Hb) as (Q0 & Q1 & Q2). lia.
               * uscr. lia.
               * rewrite (ly_img_hi L LY) in IM. lia. }
      split. { uscr. intros i Hi. apply GR1. apply DEF. lia. } intros a _ _ _ Hd. apply GR1. exact Hd.
    + exact KONT.
  - (* [comment removed for export] *)
    apply (main_path R M model K LB cr p o sp r fb neg ds HK0 MOK RA H1 H2 H4 (conj Hlen1 Hlen) A16 ltac:(uscr; lia) SHI STOP Hfb Hfb3 Ao Olo Ohi DSR Plo Phi DAT APO CRED LBWF KONT
             fx1 R1 M1 model NZ HH1 MOK (L5C.model_but_vm_refl model) R1_2).
    + rewrite (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
    + exact R1_10. + exact R1_11. + exact R1_12. + exact R1_8. + exact R1_9. + exact R1_18. + exact R1_19. + exact R1_20.
    + intros i Hi. apply K1. revert Hi. clear. intros Hi. cbn in Hi. L5CoreKit.L5K.inlist Hi.
    + unfold frameK. repeat split; assumption.
    + exact BY1. + exact OB1. + exact WO1.
    + split. { intros a (Ha & CA & NE & _). apply FR1. rewrite BG.unsigned_lit by lia.
               destruct CA as [IB|[[S1 S2]|IM]].
               * destruct IB as (bb & Hb & Hin). pose proof (LBWF bb Hb) as (Q0 & Q1 & Q2). lia.
               * uscr. lia.
               * rewrite (ly_img_hi L LY) in IM. lia. }
      split. { uscr. intros i Hi. apply GR1. apply DEF. lia. } intros a _ _ _ Hd. apply GR1. exact Hd.
Qed.


End WithHeap.
End SCFG_1.

End L5DETU.
