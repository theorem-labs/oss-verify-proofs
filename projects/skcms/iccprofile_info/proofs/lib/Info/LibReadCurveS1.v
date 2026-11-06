(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY17.  (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibWP1Spec LibCurveSpec LibRodata LibBswap LibFPLib LibTagsLib LibTagsCall LibReadCurveLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require SymDriveLB.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymDriveLZ.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module LibReadCurveS1K.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibCurveSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadCurveLib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := wp1_src1.

(* [comment removed for export] *)
Definition rc_untouched : list reg := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma abi_kept_split : forall (regs regs' : bvmap 5 word),
  getr regs' 2 = getr regs 2 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 ->
  (forall r, In r rc_untouched -> getr regs' r = getr regs r) ->
  regs_kept abi_kept regs regs'.
Proof.
  intros regs regs' H2 H8 H9 H18 H19 HU r Hr. unfold abi_kept in Hr.
  cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [first [assumption | apply HU; cbn; tauto]|]).
  destruct Hr.
Qed.

(* [comment removed for export] *)
Definition RCQ (regs : bvmap 5 word) (mem rom : word -> option byte) (ret : word) (FPI : FPState)
    (data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z)
    (st' : machine_state) : Prop :=
  exists (FPI' : FPState) regs' mem',
    st' = mkst (FP:=FPI') regs' ret mem' rom /\
    regs_kept abi_kept regs regs' /\
    fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
    rcurve_post SEGS W data len bs sp buf C cs size regs mem FPI' regs' mem'.

(* [comment removed for export] *)
Definition RSF (sp C cs : word) : list (word * Z) :=
  (Z_to_bv 64 (bv_unsigned sp - 64), 64%Z) :: (C, 32%Z)
    :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)]).

Section TailK.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  (* [comment removed for export] *)
  Hypothesis Hclassify : classify_contract SEGS W.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 64) 64.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x1048c.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 64)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 64)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (sp1 g a b cc d e f : word).
  Hypothesis Hsp1 : bv_unsigned sp1 = (bv_unsigned sp - 48)%Z.
  Hypothesis TR2 : getr R 2 = sp1.
  Hypothesis TR8 : getr R 8 = C.
  Hypothesis TRK : forall r, In r rc_untouched -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M (RSF sp C cs).
  Hypothesis S40 : cell64 SEGS M (bv_unsigned sp - 8) ret.
  Hypothesis S32 : cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8).
  Hypothesis S24 : cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9).
  Hypothesis S16 : cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18).
  Hypothesis S8 : cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19).
  Hypothesis C0 : cell SEGS M (bv_unsigned C) 4 (Z_to_bv 64 0).
  Hypothesis C4 : cell SEGS M (bv_unsigned C + 4) 4 g.
  Hypothesis C8 : cell SEGS M (bv_unsigned C + 8) 4 a.
  Hypothesis C12 : cell SEGS M (bv_unsigned C + 12) 4 b.
  Hypothesis C16 : cell SEGS M (bv_unsigned C + 16) 4 cc.
  Hypothesis C20 : cell SEGS M (bv_unsigned C + 20) 4 d.
  Hypothesis C24 : cell SEGS M (bv_unsigned C + 24) 4 e.
  Hypothesis C28 : cell SEGS M (bv_unsigned C + 28) 4 f.
  Hypothesis Hcsv : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v.

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                ++ [ret; getr regs 8; getr regs 9; getr regs 18; getr regs 19]))
                     (blobs_ev []).

  Definition knK : list kentry :=
    [KRange (EVar 2) 16 (2^64 - 48);
     KRange (EVar 8) 0 (2^64 - 32);
     KWord (SA (EVar 2) 40) 8 (EVar 64);
     KWord (SA (EVar 2) 32) 8 (EVar 65);
     KWord (SA (EVar 2) 24) 8 (EVar 66);
     KWord (SA (EVar 2) 16) 8 (EVar 67);
     KWord (SA (EVar 2) 8) 8 (EVar 68)].

  Lemma knK_ok : know_ok SEGS E M knK.
  Proof using FPc HSC HWC HWS Hcs Hsp1 S16 S24 S32 S40 S8 TR2 TR8 f rom.
    unfold knK. pose proof (u64_range sp). pose proof (u64_range C).
    destruct HWS as (W1 & W2 & W3 & W4). destruct HWC as (V1 & V2 & V3 & V4).
    unfold cell64, cell in S40, S32, S24, S16, S8.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - apply krange_intro; cbn. rewrite TR8. lia.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 40 8 (EVar 64) ret); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 40)%Z with (bv_unsigned sp - 8)%Z by lia. exact S40.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 32 8 (EVar 65) (getr regs 8)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 32)%Z with (bv_unsigned sp - 16)%Z by lia. exact S32.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 24 8 (EVar 66) (getr regs 9)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 24)%Z with (bv_unsigned sp - 24)%Z by lia. exact S24.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 16 8 (EVar 67) (getr regs 18)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 16)%Z with (bv_unsigned sp - 32)%Z by lia. exact S16.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 8 8 (EVar 68) (getr regs 19)); cbn; try lia; auto.
      replace (bv_unsigned sp1 + 8)%Z with (bv_unsigned sp - 40)%Z by lia. exact S8.
  Qed.

  (* [comment removed for export] *)
  Lemma apart_rodata : apart 0x103ec (0x1048c - 0x103ec) (RSF sp C cs).
  Proof using HWC HWS Hcs Hcsv Hro f rom.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof (writable_rodata_apart_S1 mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) HWS Hro).
    pose proof (writable_rodata_apart_S1 mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) HWC Hro).
    pose proof HWS as (W1 & W2 & W3 & W4).
    unfold RSF. destruct (Z.eq_dec (bv_unsigned cs) 0).
    - solve_apart.
    - destruct Hcs as [Hc0 | (HWcs & _)]; [lia|].
      pose proof (writable_rodata_apart_S1 mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) HWcs Hro).
      solve_apart.
  Qed.

  Lemma M_rodata : rodata_clear M 0x103ec 0x1048c.
  Proof using HM HWC HWS Hcs Hcsv Hro f rom. eapply rodata_clear_frame; [exact HM | exact Hro | lia | lia | apply apart_rodata]. Qed.

  Lemma M_writable_stk : writable SEGS M (bv_unsigned sp1 - 16) 16.
  Proof using HCal HM HSC HWS Hcs Hsp1 f rom.
    pose proof (u64_range sp).
    eapply writable_sub; [eapply writable_frame; [exact HM | exact HWS] | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma after_classify : forall M', frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp1 - 16), 16%Z)] ->
    frame_mod mem M' (RSF sp C cs) /\
    curve_ok SEGS M' data len (bv_unsigned C) /\
    (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M' (bv_unsigned cs) v).
  Proof using C0 C12 C16 C20 C8 HM HSC HWC HWS Hcs Hcsv Hsp1 f rom.
    intros M' Hf. pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    destruct HWS as (W1 & W2 & W3 & W4). destruct HWC as (V1 & V2 & V3 & V4).
    split; [|split].
    - eapply frame_mod_trans_same; [exact HM|]. eapply frame_mod_of_covered; [|exact Hf].
      unfold RSF. solve_covered.
    - apply (curve_ok_zero4 SEGS M' data len (bv_unsigned C) a b cc d); try lia;
        (eapply cell_frame; [exact Hf | eassumption | lia | cbn; lia | cbn; solve_apart]).
    - intros Hnz. destruct (Hcsv Hnz) as [v Hv]. exists v.
      destruct Hcs as [Hc0 | (HWcs & _ & _ & _ & Hcs3)]; [lia|]. destruct HWcs as (X1 & X2 & X3 & X4).
      eapply cell32_frame; [exact Hf | exact Hv | lia | lia | solve_apart].
  Qed.

  Lemma tailK_ok :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x14840) M rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using C0 C12 C16 C20 C24 C28 C4 C8 HCal HFK HM HSC HWC HWS Hclassify Hcs Hcsv Hret Hro Hsp Hsp1 S16 S24 S32 S40 S8 TR2 TR8 TRK.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knK_ok as HK.
    run_fp 20%nat [0x13274%Z] noscr false.
    (* [comment removed for export] *)
    lazymatch goal with
    | HR : regs_ok _ _ ?Rx |- runs_to _ (@mkst ?I ?Rx _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hclassify sp1 (Z_to_bv 64 (bv_unsigned C + 4)) I Rx Mx ro (Z_to_bv 64 0x14850));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | ]
        | ]
    end.
    { unfold classify_pre. cbv zeta. rewrite !u_small by lia.
      split; [regv HR (2%bv:reg); exact TR2|].
      split; [regv_lin HR (10%bv:reg); rewrite ?TR8; f_equal; lia|].
      split; [regv HR (11%bv:reg); reflexivity|].
      split; [regv HR (12%bv:reg); reflexivity|].
      split.
      { exists g, a, b, cc, d, e, f. unfold cell in *.
        rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
        repeat split; assumption. }
      split; [lia|].
      split; [apply M_writable_stk|].
      split; [apply M_rodata|].
      lia. }
    cbv beta. intros FQ rq mq (Hkeep & Hfkeep & Hfr). unfold classify_post in Hfr.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
    after_call Hkeep Hfkeep FQ. clear Hkeep Hfkeep.
    know_frame HK Hfr [(SA (EVar 2) (-16), 16%Z)];
      [rewrite TR2; unfold v_addi; repeat f_equal; lia|].
    destruct (after_classify mq Hfr) as (Hfr' & Hcurve & Hcsv'). clear Hfr.
    (* [comment removed for export] *)
    run_fp 30%nat (@nil Z) noscr false.
    fin_ret.
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2) |- _ =>
      exists FP2, R2, mq;
      split; [regv HR (1%bv:reg); reflexivity|];
      lift_hyp HR0; lift_hyp HF0;
      split; [ apply abi_kept_split;
               [ regv_lin HR (2%bv:reg); rewrite TR2, Hsp; apply bv_eq; rewrite u_small by lia; lia
               | regv HR (8%bv:reg); reflexivity
               | regv HR (9%bv:reg); reflexivity
               | regv HR (18%bv:reg); reflexivity
               | regv HR (19%bv:reg); reflexivity
               | intros r Hr; rewrite <- (TRK r Hr); revert r Hr;
                 eapply (regs_same_on _ _ _ R R2 rc_untouched); [exact HR0 | exact HR | vm_compute; reflexivity] ] |];
      split; [ eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept;
               eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |]
    end.
    unfold rcurve_post. cbv zeta. cbn [w1_rcurve_d wp1_src1].
    split; [exact Hfr'|].
    regv HR (10%bv:reg).
    rewrite alu_sltu. unfold v_sltu.
    match goal with |- exists r, (if ?cnd then _ else _) = _ /\ _ => destruct cnd end.
    - exists 1%Z. split; [reflexivity|]. split; [right; reflexivity|].
      split; [intros _; exact Hcurve|]. split; [intros _; exact Hcurve|]. intros Hnz _. exact (Hcsv' Hnz).
    - exists 0%Z. split; [reflexivity|]. split; [left; reflexivity|].
      split; [intros; lia|]. split; [intros _; exact Hcurve|]. intros Hnz Habs. lia.
  Qed.
End TailK.

(* [comment removed for export] *)
Lemma tailK : forall (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte)
    (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z)
    (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp1 g a b cc d e f : word),
  classify_contract SEGS W ->
  ret_ok ret ->
  getr regs 2 = sp ->
  writable SEGS mem (bv_unsigned C) 32 ->
  (bv_unsigned C mod 8 = 0)%Z ->
  writable SEGS mem (bv_unsigned sp - 64) 64 ->
  rodata_clear mem 0x103ec 0x1048c ->
  (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z ->
  (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 64)%Z ->
  (bv_unsigned data + len <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned data)%Z ->
  ((bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 64)%Z)) ->
  bv_unsigned sp1 = (bv_unsigned sp - 48)%Z ->
  getr R 2 = sp1 ->
  getr R 8 = C ->
  (forall r, In r rc_untouched -> getr R r = getr regs r) ->
  fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)) ->
  frame_mod mem M (RSF sp C cs) ->
  cell64 SEGS M (bv_unsigned sp - 8) ret ->
  cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8) ->
  cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9) ->
  cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18) ->
  cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19) ->
  cell SEGS M (bv_unsigned C) 4 (Z_to_bv 64 0) ->
  cell SEGS M (bv_unsigned C + 4) 4 g ->
  cell SEGS M (bv_unsigned C + 8) 4 a ->
  cell SEGS M (bv_unsigned C + 12) 4 b ->
  cell SEGS M (bv_unsigned C + 16) 4 cc ->
  cell SEGS M (bv_unsigned C + 20) 4 d ->
  cell SEGS M (bv_unsigned C + 24) 4 e ->
  cell SEGS M (bv_unsigned C + 28) 4 f ->
  (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v) ->
  runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x14840) M rom)
          (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
Proof.
  intros FPI regs mem rom ret data len bs sp buf C cs size FPc R M sp1 g a b cc d e f.
  intros Hcl Hret Hsp HWC HCal HWS Hro HDC HSC HDS Hcs Hsp1 TR2 TR8 TRK HFK HM S40 S32 S24 S16 S8 C0 C4 C8 C12 C16 C20 C24 C28 Hcsv.
  exact (tailK_ok FPI regs mem rom ret data len bs sp buf C cs size Hcl Hret Hsp HWC HCal HWS Hro HSC Hcs
           FPc R M sp1 g a b cc d e f Hsp1 TR2 TR8 TRK HFK HM S40 S32 S24 S16 S8 C0 C4 C8 C12 C16 C20 C24 C28 Hcsv).
Qed.
End LibReadCurveS1K.

Module LibReadCurveS1P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibCurveSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadCurveLib LibReadCurveS1K.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac kread_fact HK b k n H :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn b k n) in
    lazymatch r with
    | Some ?v =>
        let Hfl := fresh "Hfl" in
        assert (Hfl : flat E (SA b k) (Z.of_nat n));
        [ unfold flat, estart, elenZ; cbn [a_base a_off edenot Z.of_nat Pos.of_succ_nat Pos.succ]; ev_simpl E;
          rewrite_getr; try lia
        | pose proof (kread_rdn segs E M kn b k n v HK
                        ltac:(vm_cast_no_check (@eq_refl (option expr) (Some v)))
                        ltac:(repeat constructor) ltac:(repeat constructor) Hfl) as H;
          clear Hfl; unfold adenot in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H ]
    | None => fail "kread: no knowledge entry covers this range"
    end
  end.

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := wp1_src1.

Section TailP.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  (* [comment removed for export] *)
  Hypothesis Hmemset : memset20_contract SEGS W.
  Hypothesis Hclassify : classify_contract SEGS W.
  (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 64) 64.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x1048c.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 64)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 64)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (sp1 : word) (k : Z).
  Hypothesis Hsp1 : bv_unsigned sp1 = (bv_unsigned sp - 48)%Z.
  Hypothesis TR2 : getr R 2 = sp1.
  Hypothesis TR8 : getr R 8 = C.
  Hypothesis TR9 : getr R 9 = buf.
  Hypothesis TR18 : getr R 18 = Z_to_bv 64 k.
  Hypothesis Hk : (0 <= k <= 4)%Z.
  Hypothesis Hszk : (12 + cb k <= size)%Z.
  Hypothesis TRK : forall r, In r rc_untouched -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M ((Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)
                                    :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])).
  Hypothesis S40 : cell64 SEGS M (bv_unsigned sp - 8) ret.
  Hypothesis S32 : cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8).
  Hypothesis S24 : cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9).
  Hypothesis S16 : cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18).
  Hypothesis S8 : cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19).
  Hypothesis Hcsv : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v.

  #[local] Abbreviation off := (bv_unsigned buf - bv_unsigned data)%Z.
  #[local] Abbreviation Lk := (12 + cb k)%Z.

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                ++ [ret; getr regs 8; getr regs 9; getr regs 18; getr regs 19]))
                     (blobs_ev [sub bs off 16; sub bs off Lk]).

  Definition knP : list kentry :=
    [KRange (EVar 2) 16 (2^64 - 48);
     KRange (EVar 8) 0 (2^64 - 32);
     KRange (EVar 9) 1 (2^47);
     KWord (SA (EVar 2) 40) 8 (EVar 64);
     KWord (SA (EVar 2) 32) 8 (EVar 65);
     KWord (SA (EVar 2) 24) 8 (EVar 66);
     KWord (SA (EVar 2) 16) 8 (EVar 67);
     KWord (SA (EVar 2) 8) 8 (EVar 68);
     KWr (SA (EVar 2) (-16)) 64;
     KWr (SA (EVar 8) 0) 32;
     KDisj (SA (EVar 2) (-16)) 64 (SA (EVar 8) 0) 32;
     KDisj (SA (EVar 2) (-16)) 64 (SA (EVar 9) 0) 16;
     KDisj (SA (EVar 8) 0) 32 (SA (EVar 9) 0) 16;
     KBlob (SA (EVar 9) 0) (ELit 16) 0].

  Lemma knP_ok : know_ok SEGS E M knP.
  Proof.
    clear Hcsv HFK TRK Hro.
    unfold knP. pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range buf). pose proof (u64_range data).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof (cb_range k).
    unfold cell64, cell in S40, S32, S24, S16, S8. hide HDC. hide HSC. hide HDS. hide Hcs.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - apply krange_intro; cbn. rewrite TR8. lia.
    - apply krange_intro; cbn. rewrite TR9. lia.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 40 8 (EVar 64) ret);
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 40)%Z with (bv_unsigned sp - 8)%Z by lia. exact S40.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 32 8 (EVar 65) (getr regs 8));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 32)%Z with (bv_unsigned sp - 16)%Z by lia. exact S32.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 24 8 (EVar 66) (getr regs 9));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 24)%Z with (bv_unsigned sp - 24)%Z by lia. exact S24.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 16 8 (EVar 67) (getr regs 18));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 16)%Z with (bv_unsigned sp - 32)%Z by lia. exact S16.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 8 8 (EVar 68) (getr regs 19));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 8)%Z with (bv_unsigned sp - 40)%Z by lia. exact S8.
    - apply (kwr_intro SEGS E M (EVar 2) sp1 (-16) 64); [cbn; exact TR2 | lia | lia | lia |].
      replace (bv_unsigned sp1 + -16)%Z with (bv_unsigned sp - 64)%Z by lia.
      eapply frame_mod_store_ok; [exact HM | exact W4].
    - apply (kwr_intro SEGS E M (EVar 8) C 0 32); [cbn; exact TR8 | lia | lia | lia |].
      rewrite Z.add_0_r. eapply frame_mod_store_ok; [exact HM | exact V4].
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite TR2, TR8. unhide HSC. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite TR2, TR9. unhide HDS. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite TR8, TR9. unhide HDC. lia.
    - eapply (kblob_sub SEGS E M (EVar 9) buf data len bs off 16 0);
        [cbn; exact TR9 | reflexivity | | reflexivity | lia | lia | lia].
      eapply data_ok_frame; [exact HM | exact Hdok |].
      unhide HDS. unhide Hcs.
      destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
      destruct Hcs as [?|(X & _ & ? & _)]; [lia|]. destruct X as (X1 & X2 & X3 & X4). solve_apart.
  Qed.

  (* [comment removed for export] *)
  Lemma fixed_cells : forall M', frame_mod M M' [(C, 32%Z)] ->
    cell64 SEGS M' (bv_unsigned sp - 8) ret /\
    cell64 SEGS M' (bv_unsigned sp - 16) (getr regs 8) /\
    cell64 SEGS M' (bv_unsigned sp - 24) (getr regs 9) /\
    cell64 SEGS M' (bv_unsigned sp - 32) (getr regs 18) /\
    cell64 SEGS M' (bv_unsigned sp - 40) (getr regs 19) /\
    (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M' (bv_unsigned cs) v).
  Proof.
    intros M' Hf. clear HFK TRK HDC HDS Hro Hszk Hk.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    repeat match goal with |- _ /\ _ => split end;
      try (eapply cell64_frame; [exact Hf | eassumption | lia | lia | solve_apart]).
    intros Hnz. destruct (Hcsv Hnz) as [v Hv]. exists v.
    destruct Hcs as [Hc0 | (HWcs & _ & _ & Hcs2 & _)]; [lia|]. destruct HWcs as (X1 & X2 & X3 & X4).
    eapply cell32_frame; [exact Hf | exact Hv | lia | lia | solve_apart].
  Qed.

  Lemma frame_total : forall M', frame_mod M M' [(C, 32%Z)] -> frame_mod mem M' (RSF sp C cs).
  Proof.
    intros M' Hf. clear Hcsv HFK TRK HDC HDS HSC Hcs Hro Hszk Hk.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply frame_mod_trans_same.
    - eapply frame_mod_of_covered; [| exact HM]. unfold RSF.
      destruct (Z.eq_dec (bv_unsigned cs) 0); solve_covered.
    - eapply frame_mod_of_covered; [| exact Hf]. unfold RSF. solve_covered.
  Qed.

  Lemma dok_at : forall M', frame_mod M M' [(C, 32%Z)] -> data_ok M' data len bs.
  Proof.
    intros M' Hf. clear Hcsv HFK TRK HSC Hro Hszk Hk.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply data_ok_frame; [exact (frame_total M' Hf) | exact Hdok |].
    unfold RSF. destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
    destruct Hcs as [?|(X & _ & ? & _)]; [lia|]. destruct X as (? & ? & ? & ?). solve_apart.
  Qed.

  Lemma disj_stack_buf : forall L, (0 <= L)%Z -> (bv_unsigned buf + L <= bv_unsigned data + len)%Z ->
    (bv_unsigned sp1 + -16 + 64 <= bv_unsigned buf + 0 \/ bv_unsigned buf + 0 + L <= bv_unsigned sp1 + -16)%Z.
  Proof. intros L HL H. clear Hcs HDC HSC. pose proof Hin as (I1 & I2 & I3). lia. Qed.

  Lemma disj_C_buf : forall L, (0 <= L)%Z -> (bv_unsigned buf + L <= bv_unsigned data + len)%Z ->
    (bv_unsigned C + 0 + 32 <= bv_unsigned buf + 0 \/ bv_unsigned buf + 0 + L <= bv_unsigned C + 0)%Z.
  Proof. intros L HL H. clear Hcs HDS HSC. pose proof Hin as (I1 & I2 & I3). lia. Qed.

  (* [comment removed for export] *)
  Ltac fold_frame :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot ?Ex ?M0 ?log, HLF : log_flat _ _, HMt : frame_mod M ?M0' [(C, 32%Z)] |- _ =>
        let Hf := fresh "Hf" in
        assert (Hf : frame_mod M0 M1 [(C, 32%Z)]);
        [ rewrite EQM;
          replace [(C, 32%Z)] with (regions_denot Ex [(SA (EVar 8) 0, 32%Z)])
            by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl Ex;
                rewrite TR8; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
          apply (frame_mod_mem_denot Ex M0 log [(SA (EVar 8) 0, 32%Z)] HLF); [flats_auto | vm_compute; reflexivity]
        | let H2 := fresh "HMt" in
          pose proof (frame_mod_trans_same _ _ _ _ HMt Hf) as H2; clear HMt Hf EQM HLF; rename H2 into HMt ]
    | EQM : ?M1 = ?M0, HLF : log_flat _ _ |- _ =>
        (* [comment removed for export] *)
        subst M1; clear HLF
    end.

  (* [comment removed for export] *)
  Ltac call_memset :=
    lazymatch goal with
    | HR : regs_ok _ _ ?Rx, HMt : frame_mod M ?Mx [(C, 32%Z)] |- runs_to _ (@mkst ?I ?Rx _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hmemset (Z_to_bv 64 (bv_unsigned C + 12)) I Rx Mx ro (Z_to_bv 64 0x14338));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | unfold memset_pre; rewrite !u_small by lia;
            split; [regv_lin HR (10%bv:reg); rewrite TR8; f_equal; lia|];
            split; [regv HR (11%bv:reg); reflexivity|];
            split; [regv HR (12%bv:reg); reflexivity|];
            split; [apply mod8_mod4_12; exact HCal|];
            split; [eapply writable_sub; [eapply writable_frame; [exact HMt | eapply writable_frame; [exact HM | exact HWC]] | lia | lia | lia] | lia] ]
        | cbv beta ]
    end.

  Ltac post_memset :=
    let FQ := fresh "FQ" in let rq := fresh "rq" in let mq := fresh "mq" in
    let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in
    let Hz := fresh "Hz" in let Ha0 := fresh "Ha0" in
    intros FQ rq mq (Hkeep & Hfkeep & Hfr & Hz & Ha0);
    unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep;
    after_call Hkeep Hfkeep FQ; clear Hkeep Hfkeep;
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx _, HMt : frame_mod M ?Mx' [(C, 32%Z)] |- _ =>
        know_frame HK Hfr [(SA (EVar 8) 12, 20%Z)]; [rewrite TR8; unfold v_addi; reflexivity|];
        (* [comment removed for export] *)
        let H2 := fresh "HMt" in let Hfr2 := fresh "Hfr2" in
        lazymatch type of Hfr with frame_mod ?Ma ?Mb _ =>
          assert (Hfr2 : frame_mod Ma Mb [(C, 32%Z)]) by (eapply frame_mod_of_covered; [|exact Hfr]; solve_covered)
        end;
        pose proof (frame_mod_trans_same _ _ _ _ HMt Hfr2) as H2;
        clear HMt Hfr Hfr2; rename H2 into HMt;
        (* [comment removed for export] *)
        lazymatch goal with
        | HK : know_ok _ _ mq ?kn |- _ =>
          let HKz := fresh "HKz" in
          assert (HKz : know_ok SEGS Ex mq (KZero (SA (EVar 8) 12) (ELit 20) :: kn));
          [ apply know_ok_cons; [| exact HK];
            eapply (kzero_intro SEGS Ex mq (EVar 8) C 12 (ELit 20) 20);
            [ cbn; exact TR8 | reflexivity | lia | lia | lia
            | intros i Hi; rewrite <- (Hz i Hi); f_equal; f_equal; rewrite u_small by lia; lia ]
          | clear HK; rename HKz into HK ]
        end
    end.

  (* [comment removed for export] *)
  Ltac ccell HK off H :=
    kread_fact HK (EVar 8) off 4%nat H;
    rewrite TR8 in H; unfold v_addi in H; try rewrite Z.add_0_r in H.

  (* [comment removed for export] *)
  Ltac to_tailK :=
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx _, HR : regs_ok _ _ ?Rx, HF : fregs_ok _ _ _, HMt : frame_mod M ?Mx' [(C, 32%Z)],
      HR0 : id _, HF0 : id _ |- runs_to _ (@mkst _ ?Rx _ ?Mx _) _ =>
        let C0 := fresh "C0" in let C4 := fresh "C4" in let C8 := fresh "C8" in let C12 := fresh "C12" in
        let C16 := fresh "C16" in let C20 := fresh "C20" in let C24 := fresh "C24" in let C28 := fresh "C28" in
        ccell HK 0%Z C0; ccell HK 4%Z C4; ccell HK 8%Z C8; ccell HK 12%Z C12;
        ccell HK 16%Z C16; ccell HK 20%Z C20; ccell HK 24%Z C24; ccell HK 28%Z C28;
        let T := fresh "T" in
        pose proof (fixed_cells Mx HMt) as T;
        let T40 := fresh "T40" in let T32 := fresh "T32" in let T24 := fresh "T24" in
        let T16 := fresh "T16" in let T8 := fresh "T8" in let Tcs := fresh "Tcs" in
        destruct T as (T40 & T32 & T24 & T16 & T8 & Tcs);
        lift_hyp HR0; lift_hyp HF0;
        eapply (tailK FPI regs mem rom ret data len bs sp buf C cs size _ Rx Mx sp1);
        [ exact Hclassify | exact Hret | exact Hsp | exact HWC | exact HCal | exact HWS | exact Hro
        | exact HDC | exact HSC | exact HDS | exact Hcs | exact Hsp1
        | regv HR (2%bv:reg); exact TR2
        | regv HR (8%bv:reg); exact TR8
        | intros r Hr; rewrite <- (TRK r Hr); revert r Hr;
          eapply (regs_same_on _ _ _ R Rx rc_untouched); [exact HR0 | exact HR | vm_compute; reflexivity]
        | eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept;
          eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity]
        | apply frame_total; exact HMt
        | exact T40 | exact T32 | exact T24 | exact T16 | exact T8
        | exact C0 | exact C4 | exact C8 | exact C12 | exact C16 | exact C20 | exact C24 | exact C28
        | exact Tcs ]
    end.

  (* [comment removed for export] *)
  Ltac post_exit0 :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _,
      HMt : frame_mod M ?Mx' [(C, 32%Z)], HR0 : id _, HF0 : id _ |- _ =>
      let C0 := fresh "C0" in let C8 := fresh "C8" in let C12 := fresh "C12" in
      let C16 := fresh "C16" in let C20 := fresh "C20" in
      ccell HK 0%Z C0; ccell HK 8%Z C8; ccell HK 12%Z C12; ccell HK 16%Z C16; ccell HK 20%Z C20;
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); reflexivity|];
      lift_hyp HR0; lift_hyp HF0;
      split; [ apply abi_kept_split;
               [ regv_lin HR (2%bv:reg); rewrite TR2, Hsp; apply bv_eq; rewrite u_small by lia; lia
               | regv HR (8%bv:reg); reflexivity
               | regv HR (9%bv:reg); reflexivity
               | regv HR (18%bv:reg); reflexivity
               | regv HR (19%bv:reg); reflexivity
               | intros r Hr; rewrite <- (TRK r Hr); revert r Hr;
                 eapply (regs_same_on _ _ _ R R2 rc_untouched); [exact HR0 | exact HR | vm_compute; reflexivity] ] |];
      split; [ eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept;
               eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |];
      unfold rcurve_post; cbv zeta; cbn [w1_rcurve_d wp1_src1];
      split; [apply frame_total; exact HMt|];
      exists 0%Z; split; [regv HR (10%bv:reg); reflexivity|];
      split; [left; reflexivity|];
      split; [intros; lia|];
      split; [intros _; apply (curve_ok_zero4 SEGS M2 data len (bv_unsigned C) _ _ _ _ ltac:(lia) ltac:(lia) C0 C8 C12 C16 C20)|];
      intros; lia
    end.

  Ltac crawl n :=
    lazymatch n with
    | O => fail "crawl: out of depth"
    | S ?m =>
        run_fp 300%nat [0x14840%Z; 0x144c8%Z] noscr true; fold_frame;
        lazymatch goal with
        | |- runs_to _ (@mkst _ _ (Z_to_bv 64 0x14840) _ _) _ => to_tailK
        | _ => first [ post_exit0
                     | let Hc := fresh "Hc" in branch_case as Hc; [clear Hc; crawl m | clear Hc; crawl m] ]
        end
    end.

  (* [comment removed for export] *)
  Ltac k_case kv :=
    let L := eval vm_compute in (12 + cb kv)%Z in
    lazymatch goal with
    | Hkv : k = kv, HR : regs_ok ?Ex ?sr ?Rx, HK : know_ok _ _ ?Mx ?kn, HMt : frame_mod M ?Mx' [(C, 32%Z)] |- _ =>
        let Hsz := fresh "Hsz" in
        pose proof Hszk as Hsz; rewrite Hkv in Hsz; cbn [cb] in Hsz;
        pin_reg HR (18%bv:reg) (ELit kv) by (regv HR (18%bv:reg); rewrite TR18, Hkv; reflexivity);
        let HK2 := fresh "HK" in
        assert (HK2 : know_ok SEGS Ex Mx
                  (KBlob (SA (EVar 9) 0) (ELit L) 1
                   :: KDisj (SA (EVar 2) (-16)) 64 (SA (EVar 9) 0) L
                   :: KDisj (SA (EVar 8) 0) 32 (SA (EVar 9) 0) L :: kn));
        [ apply know_ok_cons;
          [ eapply (kblob_sub SEGS Ex Mx (EVar 9) buf data len bs off L 1);
            [ cbn; exact TR9 | cbn; rewrite Hkv; reflexivity
            | exact (dok_at Mx HMt)
            | reflexivity | lia | lia | lia ]
          | apply know_ok_cons;
            [ cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl Ex; rewrite TR2, TR9; apply disj_stack_buf; lia
            | apply know_ok_cons;
              [ cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl Ex; rewrite TR8, TR9; apply disj_C_buf; lia
              | exact HK ] ] ]
        | clear HK; rename HK2 into HK ];
        crawl 3%nat
    end.

  Lemma tailP_ok :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x1431c) M rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof.
    (* [comment removed for export] *)
    pose proof (Hmemset, Hclassify, Hret, Hsp, Hdok, Hsize, Hin, HWC, HCal, HWS, Hro, HDC, HSC, HDS, Hcs,
                Hsp1, TR2, TR8, TR9, TR18, Hk, Hszk, TRK, HFK, HM, S40, S32, S24, S16, S8, Hcsv) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof (u64_range buf) as Rbuf. pose proof (u64_range data) as Rdata.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof (cb_range k) as Rcb.
    hide HDC. hide HSC. hide HDS. hide Hcs.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [sub bs off 16; sub bs off Lk])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [sub bs off 16; sub bs off Lk])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knP_ok as HK.
    pose proof (frame_mod_refl M [(C, 32%Z)]) as HMt.
    run_fp 30%nat [0x1dfe4%Z] noscr true.
    fold_frame.
    call_memset.
    post_memset.
    run_fp 60%nat [0x1437c%Z] noscr true.
    fold_frame.
    assert (Hk5 : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4)%Z) by lia.
    destruct Hk5 as [Hkv | [Hkv | [Hkv | [Hkv | Hkv]]]].
    - k_case 0%Z.
    - k_case 1%Z.
    - k_case 2%Z.
    - k_case 3%Z.
    - k_case 4%Z.
  Qed.
End TailP.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EntryP.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hmemset : memset20_contract SEGS W.
  Hypothesis Hclassify : classify_contract SEGS W.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 64) 64.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x1048c.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 64)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 64)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (sp1 : word) (k : Z).
  Hypothesis Hsp1 : bv_unsigned sp1 = (bv_unsigned sp - 48)%Z.
  Hypothesis TR2 : getr R 2 = sp1.
  Hypothesis TR8 : getr R 8 = C.
  Hypothesis TR9 : getr R 9 = buf.
  Hypothesis TR13 : getr R 13 = cs.
  Hypothesis TR18 : getr R 18 = Z_to_bv 64 k.
  Hypothesis Hk : (0 <= k <= 4)%Z.
  Hypothesis Hszk : (12 + cb k <= size)%Z.
  Hypothesis TRK : forall r, In r rc_untouched -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)].
  Hypothesis S40 : cell64 SEGS M (bv_unsigned sp - 8) ret.
  Hypothesis S32 : cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8).
  Hypothesis S24 : cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9).
  Hypothesis S16 : cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18).
  Hypothesis S8 : cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19).

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                ++ [ret; getr regs 8; getr regs 9; getr regs 18; getr regs 19]))
                     (blobs_ev []).

  Definition knE : list kentry :=
    [KRange (EVar 2) 16 (2^64 - 48);
     KWord (SA (EVar 2) 40) 8 (EVar 64);
     KWord (SA (EVar 2) 32) 8 (EVar 65);
     KWord (SA (EVar 2) 24) 8 (EVar 66);
     KWord (SA (EVar 2) 16) 8 (EVar 67);
     KWord (SA (EVar 2) 8) 8 (EVar 68)].

  Lemma knE_ok : know_ok SEGS E M knE.
  Proof.
    clear HFK TRK Hro HDC HDS HSC Hcs Hszk Hk.
    unfold knE. pose proof (u64_range sp).
    pose proof HWS as (W1 & W2 & W3 & W4).
    unfold cell64, cell in S40, S32, S24, S16, S8.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 40 8 (EVar 64) ret);
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 40)%Z with (bv_unsigned sp - 8)%Z by lia. exact S40.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 32 8 (EVar 65) (getr regs 8));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 32)%Z with (bv_unsigned sp - 16)%Z by lia. exact S32.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 24 8 (EVar 66) (getr regs 9));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 24)%Z with (bv_unsigned sp - 24)%Z by lia. exact S24.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 16 8 (EVar 67) (getr regs 18));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 16)%Z with (bv_unsigned sp - 32)%Z by lia. exact S16.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 8 8 (EVar 68) (getr regs 19));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 8)%Z with (bv_unsigned sp - 40)%Z by lia. exact S8.
  Qed.

  (* [comment removed for export] *)
  Ltac to_tailP HMf Tcs :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HK : know_ok _ _ ?Mx _, HR0 : id _, HF0 : id _
      |- runs_to _ (@mkst ?I ?Rx _ ?Mx _) _ =>
      let T40 := fresh "T40" in let T32 := fresh "T32" in let T24 := fresh "T24" in
      let T16 := fresh "T16" in let T8 := fresh "T8" in
      kread_fact HK (EVar 2) 40%Z 8%nat T40; kread_fact HK (EVar 2) 32%Z 8%nat T32;
      kread_fact HK (EVar 2) 24%Z 8%nat T24; kread_fact HK (EVar 2) 16%Z 8%nat T16;
      kread_fact HK (EVar 2) 8%Z 8%nat T8;
      rewrite TR2 in T40, T32, T24, T16, T8; unfold v_addi in T40, T32, T24, T16, T8;
      unfold id in HR0, HF0;
      eapply (tailP_ok FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hclassify Hret Hsp Hdok Hsize Hin HWC HCal HWS
                Hro HDC HSC HDS Hcs I Rx Mx sp1 k Hsp1);
      [ regv HR (2%bv:reg); exact TR2
      | regv HR (8%bv:reg); exact TR8
      | regv HR (9%bv:reg); exact TR9
      | regv HR (18%bv:reg); exact TR18
      | exact Hk | exact Hszk
      | intros r Hr; rewrite <- (TRK r Hr); exact (regs_same_on _ _ _ R Rx rc_untouched HR0 HR ltac:(vm_compute; reflexivity) r Hr)
      | eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept; intros r Hr;
        exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
      | exact HMf
      | unfold cell64, cell; replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp1 + 40)%Z by lia; exact T40
      | unfold cell64, cell; replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp1 + 32)%Z by lia; exact T32
      | unfold cell64, cell; replace (bv_unsigned sp - 24)%Z with (bv_unsigned sp1 + 24)%Z by lia; exact T24
      | unfold cell64, cell; replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp1 + 16)%Z by lia; exact T16
      | unfold cell64, cell; replace (bv_unsigned sp - 40)%Z with (bv_unsigned sp1 + 8)%Z by lia; exact T8
      | exact Tcs ]
    end.

  Lemma tailP_entry :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x14314) M rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof.
    pose proof (Hmemset, Hclassify, Hret, Hsp, Hdok, Hsize, Hin, HWC, HCal, HWS, Hro, HDC, HSC, HDS, Hcs,
                Hsp1, TR2, TR8, TR9, TR13, TR18, Hk, Hszk, TRK, HFK, HM, S40, S32, S24, S16, S8) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range cs) as Rcs.
    pose proof HWS as (W1 & W2 & W3 & W4).
    hide HDC. hide HSC. hide HDS.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knE_ok as HK.
    destruct (Z.eq_dec (bv_unsigned cs) 0) as [Hcs0 | Hnz].
    - (* [comment removed for export] *)
      add_krange (EVar 13) 0%Z 0%Z by (rewrite TR13; lia).
      run_fp 3%nat [0x1431c%Z] noscr false.
      assert (HMf : frame_mod mem M ((Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)
                                     :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])))
        by (rewrite Hcs0; exact HM).
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v) by (intros; lia).
      to_tailP HMf Tcs.
    - (* [comment removed for export] *)
      destruct Hcs as [? | (HWcs & Hcsal & Hcs1 & Hcs2 & Hcs3)]; [lia|].
      pose proof HWcs as (X1 & X2 & X3 & X4). hide Hcs1. hide Hcs2.
      add_krange (EVar 13) 1%Z (2^64 - 4)%Z by (rewrite TR13; lia).
      lazymatch goal with
      | HK : know_ok _ _ _ ?kn |- _ =>
        let HK2 := fresh "HK" in
        assert (HK2 : know_ok SEGS E M (KWr (SA (EVar 13) 0) 4 :: KDisj (SA (EVar 2) (-16)) 64 (SA (EVar 13) 0) 4 :: kn));
        [ apply know_ok_cons;
          [ apply (kwr_intro SEGS E M (EVar 13) cs 0 4); [cbn; exact TR13 | lia | lia | lia |];
            rewrite Z.add_0_r; eapply frame_mod_store_ok; [exact HM | exact X4]
          | apply know_ok_cons; [| exact HK];
            cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite TR2, TR13; lia ]
        | clear HK; rename HK2 into HK ]
      end.
      run_fp 3%nat [0x1431c%Z] noscr true.
      assert (Hf : frame_mod M M0 [(cs, 4%Z)]).
      { rewrite EQM.
        replace [(cs, 4%Z)] with (regions_denot E [(SA (EVar 13) 0, 4%Z)])
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E;
              rewrite TR13; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
        apply (frame_mod_mem_denot E M _ [(SA (EVar 13) 0, 4%Z)] HLF); [flats_auto | vm_compute; reflexivity]. }
      clear EQM HLF.
      assert (HMf : frame_mod mem M0 ((Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)
                                      :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)]))).
      { destruct (Z.eq_dec (bv_unsigned cs) 0) as [|_]; [lia|].
        eapply frame_mod_trans_same.
        - eapply frame_mod_of_covered; [|exact HM]. solve_covered.
        - eapply frame_mod_of_covered; [|exact Hf]. solve_covered. }
      kread_fact HK (EVar 13) 0%Z 4%nat Tc. rewrite TR13 in Tc. unfold v_addi in Tc. rewrite ?Z.add_0_r in Tc.
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M0 (bv_unsigned cs) v)
        by (intros _; eexists; apply cell32_of_word; exact Tc).
      clear Tc Hf.
      to_tailP HMf Tcs.
  Qed.
End EntryP.
End LibReadCurveS1P.

Module LibReadCurveS1C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibCurveSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadCurveLib LibReadCurveS1K.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Local Ltac perf_el3_core := intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs;
  first [ Zify.zify_post_hook; xlia zchecker | lazymatch Zify.zify_convert_to_euclidean_division_equations_flag with true => idtac end; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook; xlia zchecker ].
Local Ltac perf_el3_clear_all := clear.  (* [comment removed for export] *)
Local Ltac perf_el3_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif perf_el3_has_var then perf_el3_core
  else first [ solve [perf_el3_clear_all; perf_el3_core] | perf_el3_core ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := wp1_src1.

Section TailC.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  (* [comment removed for export] *)
  Hypothesis Hmemset : memset20_contract SEGS W.
  (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 64) 64.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x1048c.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 64)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 64)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (sp1 X RAW : word) (vc : Z).
  Hypothesis Hsp1 : bv_unsigned sp1 = (bv_unsigned sp - 48)%Z.
  Hypothesis TR2 : getr R 2 = sp1.
  Hypothesis TR8 : getr R 8 = C.
  Hypothesis TR9 : getr R 9 = buf.
  Hypothesis TR10 : getr R 10 = X.
  Hypothesis TR18 : getr R 18 = RAW.
  Hypothesis HXv : (bv_unsigned X mod 2 ^ 32 = vc)%Z.
  Hypothesis HRv : (bv_unsigned RAW = 0 <-> vc = 0)%Z.
  Hypothesis Hvsz : (12 + 2 * vc <= size)%Z.
  Hypothesis TRK : forall r, In r rc_untouched -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M ((Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)
                                    :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])).
  Hypothesis S40 : cell64 SEGS M (bv_unsigned sp - 8) ret.
  Hypothesis S32 : cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8).
  Hypothesis S24 : cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9).
  Hypothesis S16 : cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18).
  Hypothesis S8 : cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19).
  Hypothesis Hcsv : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v.

  #[local] Abbreviation off := (bv_unsigned buf - bv_unsigned data)%Z.

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                ++ [ret; getr regs 8; getr regs 9; getr regs 18; getr regs 19]))
                     (blobs_ev [sub bs off 14]).

  Definition knC : list kentry :=
    [KRange (EVar 2) 16 (2^64 - 48);
     KRange (EVar 8) 0 (2^64 - 32);
     KRange (EVar 9) 1 (2^47);
     KWord (SA (EVar 2) 40) 8 (EVar 64);
     KWord (SA (EVar 2) 32) 8 (EVar 65);
     KWord (SA (EVar 2) 24) 8 (EVar 66);
     KWord (SA (EVar 2) 16) 8 (EVar 67);
     KWord (SA (EVar 2) 8) 8 (EVar 68);
     KWr (SA (EVar 2) (-16)) 64;
     KWr (SA (EVar 8) 0) 32;
     KDisj (SA (EVar 2) (-16)) 64 (SA (EVar 8) 0) 32].

  Lemma knC_ok : know_ok SEGS E M knC.
  Proof using FPc HM HSC HWC HWS Hdok Hin Hsp1 S16 S24 S32 S40 S8 TR2 TR8 TR9.
    clear Hcsv HFK TRK Hvsz HRv HXv HDC HDS Hcs Hro.
    unfold knC. pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range buf). pose proof (u64_range data).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    unfold cell64, cell in S40, S32, S24, S16, S8. hide HSC.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - apply krange_intro; cbn. rewrite TR8. lia.
    - apply krange_intro; cbn. rewrite TR9. lia.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 40 8 (EVar 64) ret);
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 40)%Z with (bv_unsigned sp - 8)%Z by lia. exact S40.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 32 8 (EVar 65) (getr regs 8));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 32)%Z with (bv_unsigned sp - 16)%Z by lia. exact S32.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 24 8 (EVar 66) (getr regs 9));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 24)%Z with (bv_unsigned sp - 24)%Z by lia. exact S24.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 16 8 (EVar 67) (getr regs 18));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 16)%Z with (bv_unsigned sp - 32)%Z by lia. exact S16.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 8 8 (EVar 68) (getr regs 19));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 8)%Z with (bv_unsigned sp - 40)%Z by lia. exact S8.
    - apply (kwr_intro SEGS E M (EVar 2) sp1 (-16) 64); [cbn; exact TR2 | lia | lia | lia |].
      replace (bv_unsigned sp1 + -16)%Z with (bv_unsigned sp - 64)%Z by lia.
      eapply frame_mod_store_ok; [exact HM | exact W4].
    - apply (kwr_intro SEGS E M (EVar 8) C 0 32); [cbn; exact TR8 | lia | lia | lia |].
      rewrite Z.add_0_r. eapply frame_mod_store_ok; [exact HM | exact V4].
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite TR2, TR8. unhide HSC. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fixed_cells : forall M', frame_mod M M' [(C, 32%Z)] ->
    cell64 SEGS M' (bv_unsigned sp - 8) ret /\
    cell64 SEGS M' (bv_unsigned sp - 16) (getr regs 8) /\
    cell64 SEGS M' (bv_unsigned sp - 24) (getr regs 9) /\
    cell64 SEGS M' (bv_unsigned sp - 32) (getr regs 18) /\
    cell64 SEGS M' (bv_unsigned sp - 40) (getr regs 19) /\
    (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M' (bv_unsigned cs) v).
  Proof using HSC HWS Hcs Hcsv S16 S24 S32 S40 S8.
    intros M' Hf. clear HFK TRK Hvsz HRv HXv HDC HDS Hro.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    repeat match goal with |- _ /\ _ => split end;
      try (eapply cell64_frame; [exact Hf | eassumption | lia | lia | solve_apart]).
    intros Hnz. destruct (Hcsv Hnz) as [v Hv]. exists v.
    destruct Hcs as [Hc0 | (HWcs & _ & _ & Hcs2 & _)]; [lia|]. destruct HWcs as (X1 & X2 & X3 & X4).
    eapply cell32_frame; [exact Hf | exact Hv | lia | lia | solve_apart].
  Qed.

  Lemma frame_total : forall M', frame_mod M M' [(C, 32%Z)] -> frame_mod mem M' (RSF sp C cs).
  Proof using HM HWS.
    intros M' Hf. clear Hcsv HFK TRK Hvsz HRv HXv HDC HDS HSC Hcs Hro.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply frame_mod_trans_same.
    - eapply frame_mod_of_covered; [| exact HM]. unfold RSF.
      destruct (Z.eq_dec (bv_unsigned cs) 0); solve_covered.
    - eapply frame_mod_of_covered; [| exact Hf]. unfold RSF. solve_covered.
  Qed.

  Lemma dok_at : forall M', frame_mod M M' [(C, 32%Z)] -> data_ok M' data len bs.
  Proof using HDC HDS HM HWS Hcs Hdok.
    intros M' Hf. clear Hcsv HFK TRK Hvsz HRv HXv HSC Hro.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply data_ok_frame; [exact (frame_total M' Hf) | exact Hdok |].
    unfold RSF. destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
    destruct Hcs as [?|(X0 & _ & ? & _)]; [lia|]. destruct X0 as (? & ? & ? & ?). solve_apart.
  Qed.

  (* [comment removed for export] *)
  Lemma disj_stack_buf : forall L, (0 <= L)%Z -> (bv_unsigned buf + L <= bv_unsigned data + len)%Z ->
    (bv_unsigned sp1 + -16 + 64 <= bv_unsigned buf + 0 \/ bv_unsigned buf + 0 + L <= bv_unsigned sp1 + -16)%Z.
  Proof using HDC HDS HRv HSC Hin Hsp1 Hvsz. intros L HL H. pose proof Hin as (I1 & I2 & I3). lia. Qed.

  Lemma disj_C_buf : forall L, (0 <= L)%Z -> (bv_unsigned buf + L <= bv_unsigned data + len)%Z ->
    (bv_unsigned C + 0 + 32 <= bv_unsigned buf + 0 \/ bv_unsigned buf + 0 + L <= bv_unsigned C + 0)%Z.
  Proof using HDC HDS HRv HSC Hin Hvsz. intros L HL H. pose proof Hin as (I1 & I2 & I3). lia. Qed.

  (* [comment removed for export] *)
  Lemma curve_kept : curve_ok SEGS mem data len (bv_unsigned C) -> curve_ok SEGS M data len (bv_unsigned C).
  Proof using HM HSC HWC HWS Hcs.
    intros Hc. clear Hcsv HFK TRK Hvsz HRv HXv HDC HDS Hro.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    eapply curve_ok_frame; [exact HM | exact Hc | lia | lia |].
    destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
    destruct Hcs as [?|(X0 & _ & _ & ? & _)]; [lia|]. destruct X0 as (? & ? & ? & ?). solve_apart.
  Qed.

  (* [comment removed for export] *)
  Ltac fold_frame :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot ?Ex ?M0 ?log, HLF : log_flat _ _, HMt : frame_mod M ?M0' [(C, 32%Z)] |- _ =>
        let Hf := fresh "Hf" in
        assert (Hf : frame_mod M0 M1 [(C, 32%Z)]);
        [ rewrite EQM;
          replace [(C, 32%Z)] with (regions_denot Ex [(SA (EVar 8) 0, 32%Z)])
            by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl Ex;
                rewrite TR8; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
          apply (frame_mod_mem_denot Ex M0 log [(SA (EVar 8) 0, 32%Z)] HLF); [flats_auto | vm_compute; reflexivity]
        | let H2 := fresh "HMt" in
          pose proof (frame_mod_trans_same _ _ _ _ HMt Hf) as H2; clear HMt Hf EQM HLF; rename H2 into HMt ]
    | EQM : ?M1 = ?M0, HLF : log_flat _ _ |- _ =>
        (* [comment removed for export] *)
        subst M1; clear HLF
    end.

  (* [comment removed for export] *)
  Ltac call_memset :=
    lazymatch goal with
    | HR : regs_ok _ _ ?Rx, HMt : frame_mod M ?Mx [(C, 32%Z)] |- runs_to _ (@mkst ?I ?Rx _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hmemset (Z_to_bv 64 (bv_unsigned C + 12)) I Rx Mx ro (Z_to_bv 64 0x14514));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | unfold memset_pre; rewrite !u_small by lia;
            split; [regv_lin HR (10%bv:reg); rewrite TR8; f_equal; lia|];
            split; [regv HR (11%bv:reg); reflexivity|];
            split; [regv HR (12%bv:reg); reflexivity|];
            split; [apply mod8_mod4_12; exact HCal|];
            split; [eapply writable_sub; [eapply writable_frame; [exact HMt | eapply writable_frame; [exact HM | exact HWC]] | lia | lia | lia] | lia] ]
        | cbv beta ]
    end.

  Ltac post_memset :=
    let FQ := fresh "FQ" in let rq := fresh "rq" in let mq := fresh "mq" in
    let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in
    let Hz := fresh "Hz" in let Ha0 := fresh "Ha0" in
    intros FQ rq mq (Hkeep & Hfkeep & Hfr & Hz & Ha0);
    unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep;
    after_call Hkeep Hfkeep FQ; clear Hkeep Hfkeep;
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx _, HMt : frame_mod M ?Mx' [(C, 32%Z)] |- _ =>
        know_frame HK Hfr [(SA (EVar 8) 12, 20%Z)]; [rewrite TR8; unfold v_addi; reflexivity|];
        (* [comment removed for export] *)
        let H2 := fresh "HMt" in let Hfr2 := fresh "Hfr2" in
        lazymatch type of Hfr with frame_mod ?Ma ?Mb _ =>
          assert (Hfr2 : frame_mod Ma Mb [(C, 32%Z)]) by (eapply frame_mod_of_covered; [|exact Hfr]; solve_covered)
        end;
        pose proof (frame_mod_trans_same _ _ _ _ HMt Hfr2) as H2;
        clear HMt Hfr Hfr2; rename H2 into HMt;
        (* [comment removed for export] *)
        lazymatch goal with
        | HK : know_ok _ _ mq ?kn |- _ =>
          let HKz := fresh "HKz" in
          assert (HKz : know_ok SEGS Ex mq (KZero (SA (EVar 8) 12) (ELit 20) :: kn));
          [ apply know_ok_cons; [| exact HK];
            eapply (kzero_intro SEGS Ex mq (EVar 8) C 12 (ELit 20) 20);
            [ cbn; exact TR8 | reflexivity | lia | lia | lia
            | intros i Hi; rewrite <- (Hz i Hi); f_equal; f_equal; rewrite u_small by lia; lia ]
          | clear HK; rename HKz into HK ]
        end
    end.

  (* [comment removed for export] *)
  Ltac ccell HK off H :=
    kread_fact HK (EVar 8) off 4%nat H;
    rewrite TR8 in H; unfold v_addi in H; try rewrite Z.add_0_r in H.

  (* [comment removed for export] *)
  Ltac post_common :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _,
      HMt : frame_mod M ?Mx' [(C, 32%Z)], HR0 : id _, HF0 : id _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); reflexivity|];
      lift_hyp HR0; lift_hyp HF0;
      split; [ apply abi_kept_split;
               [ regv_lin HR (2%bv:reg); rewrite TR2, Hsp; apply bv_eq; rewrite u_small by lia; lia
               | regv HR (8%bv:reg); reflexivity
               | regv HR (9%bv:reg); reflexivity
               | regv HR (18%bv:reg); reflexivity
               | regv HR (19%bv:reg); reflexivity
               | intros r Hr; rewrite <- (TRK r Hr); revert r Hr;
                 eapply (regs_same_on _ _ _ R R2 rc_untouched); [exact HR0 | exact HR | vm_compute; reflexivity] ] |];
      split; [ eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept;
               eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |];
      unfold rcurve_post; cbv zeta; cbn [w1_rcurve_d wp1_src1];
      split; [apply frame_total; exact HMt|]
    end.

  (* [comment removed for export] *)
  Ltac post_small :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ _ ?Rx, HK : know_ok _ _ ?M2 _, HMt : frame_mod M ?Mx' [(C, 32%Z)] |- _ =>
      let C0 := fresh "C0" in let C8 := fresh "C8" in let C12 := fresh "C12" in
      let C16 := fresh "C16" in let C20 := fresh "C20" in
      ccell HK 0%Z C0; ccell HK 8%Z C8; ccell HK 12%Z C12; ccell HK 16%Z C16; ccell HK 20%Z C20;
      let T := fresh "T" in pose proof (fixed_cells M2 HMt) as T;
      let Tcs := fresh "Tcs" in destruct T as (_ & _ & _ & _ & _ & Tcs);
      let HC := fresh "HC" in
      assert (HC : curve_ok SEGS M2 data len (bv_unsigned C))
        by (apply (curve_ok_zero4 SEGS M2 data len (bv_unsigned C) _ _ _ _ ltac:(lia) ltac:(lia) C0 C8 C12 C16 C20));
      post_common;
      exists 1%Z; split; [regv HR (10%bv:reg); reflexivity|];
      split; [right; reflexivity|];
      split; [intros _; exact HC|]; split; [intros _; exact HC|];
      let Hnz := fresh "Hnz" in intros Hnz _; exact (Tcs Hnz)
    end.

  Lemma tailC_ok :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x144f0) M rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using HCal HDC HDS HFK HM HRv HSC HWC HWS HXv Hcs Hcsv Hdok Hin Hmemset Hret Hsize Hsp Hsp1 Hvsz S16 S24 S32 S40 S8 TR10 TR18 TR2 TR8 TR9 TRK.
    (* [comment removed for export] *)
    pose proof (Hmemset, Hret, Hsp, Hdok, Hsize, Hin, HWC, HCal, HWS, HDC, HSC, HDS, Hcs, Hsp1, TR2, TR8, TR9, TR10, TR18,
                HXv, HRv, Hvsz, TRK, HFK, HM, S40, S32, S24, S16, S8, Hcsv) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof (u64_range buf) as Rbuf. pose proof (u64_range data) as Rdata.
    pose proof (u64_range X) as RX. pose proof (u64_range RAW) as RRAW.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    assert (Hvc0 : (0 <= vc)%Z) by (rewrite <- HXv; apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    hide HDC. hide HSC. hide HDS. hide Hcs. hide HRv. hide HXv.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [sub bs off 14])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [sub bs off 14])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knC_ok as HK.
    pose proof (frame_mod_refl M [(C, 32%Z)]) as HMt.
    run_fp 10%nat (@nil Z) noscr true. fold_frame.
    (* [comment removed for export] *)
    branch_case as Hc1.
    - (* [comment removed for export] *)
      br_simpl_in E Hc1. rewrite TR10 in Hc1. rewrite ?Z.mod_small in Hc1 by lia. apply Z.ltb_lt in Hc1.
      run_fp 10%nat (@nil Z) noscr true. fold_frame.
      branch_case as Hc2.
      + (* [comment removed for export] *)
        clear Hc2.
        run_fp 30%nat (@nil Z) noscr true. fold_frame.
        fin_ret. post_common.
        exists 0%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [left; reflexivity|].
        split; [intros; lia|]. split; [| intros; lia].
        intros Hc. exact (curve_kept Hc).
      + (* [comment removed for export] *)
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        br_simpl_in E Hc2. rewrite TR10 in Hc2. rewrite ?Z.mod_small in Hc2 by lia. apply Z.ltb_ge in Hc2.
        run_fp 40%nat (@nil Z) noscr true. fold_frame.
        unhide HXv.
        kread_fact HK (EVar 8) 0%Z 4%nat C0. rewrite TR8, TR10 in C0. unfold v_addi in C0. rewrite Z.add_0_r in C0.
        kread_fact HK (EVar 8) 8%Z 8%nat C8. rewrite TR8 in C8. unfold v_addi in C8.
        kread_fact HK (EVar 8) 16%Z 8%nat C16. rewrite TR8, TR9, alu_add_lit in C16. unfold v_addi in C16.
        lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mx _) _ =>
          destruct (fixed_cells Mx HMt) as (_ & _ & _ & _ & _ & Tcs);
          assert (HC : curve_ok SEGS Mx data len (bv_unsigned C))
        end.
        { apply (curve_ok_table16 SEGS _ data len (bv_unsigned C) vc (Z_to_bv 64 (bv_unsigned buf + 12))).
          - rewrite ext_val_4_word, HXv in C0. split; [| exact C0]. rewrite <- HXv. apply Z.mod_pos_bound. lia.
          - exact C8.
          - exact C16.
          - lia.
          - rewrite u_small by lia. lia.
          - unfold inDATA. rewrite u_small by lia. lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        fin_ret. post_common.
        exists 1%Z. split; [regv HR (10%bv:reg); reflexivity|]. split; [right; reflexivity|].
        split; [intros _; exact HC|]. split; [intros _; exact HC|]. intros Hnz _; exact (Tcs Hnz).
    - (* [comment removed for export] *)
      br_simpl_in E Hc1. rewrite TR10 in Hc1. rewrite ?Z.mod_small in Hc1 by lia. apply Z.ltb_ge in Hc1.
      run_fp 30%nat [0x1dfe4%Z] noscr true. fold_frame.
      call_memset. post_memset.
      run_fp 10%nat (@nil Z) noscr true. fold_frame.
      (* [comment removed for export] *)
      branch_case as Hc3.
      + (* [comment removed for export] *)
        clear Hc3.
        run_fp 40%nat (@nil Z) noscr true. fold_frame. post_small.
      + (* [comment removed for export] *)
        br_simpl_in E Hc3. rewrite TR18 in Hc3.
        assert (Hsz14 : (14 <= size)%Z).
        { unhide HRv. rewrite ?Z.mod_small in Hc3 by lia. apply Z.eqb_neq in Hc3. lia. }
        clear Hc3. hide HRv.
        lazymatch goal with
        | HK : know_ok _ ?Ex ?Mx ?kn |- _ =>
          let HK2 := fresh "HK" in
          assert (HK2 : know_ok SEGS Ex Mx
                    (KBlob (SA (EVar 9) 0) (ELit 14) 0
                     :: KDisj (SA (EVar 2) (-16)) 64 (SA (EVar 9) 0) 14
                     :: KDisj (SA (EVar 8) 0) 32 (SA (EVar 9) 0) 14 :: kn));
          [ apply know_ok_cons;
            [ eapply (kblob_sub SEGS Ex Mx (EVar 9) buf data len bs off 14 0);
              [ cbn; exact TR9 | reflexivity | exact (dok_at Mx HMt) | reflexivity | lia | lia | lia ]
            | apply know_ok_cons;
              [ cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl Ex; rewrite TR2, TR9; apply disj_stack_buf; lia
              | apply know_ok_cons;
                [ cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl Ex; rewrite TR8, TR9; apply disj_C_buf; lia
                | exact HK ] ] ]
          | clear HK; rename HK2 into HK ]
        end.
        run_fp 40%nat (@nil Z) noscr true. fold_frame. post_small.
  Qed.
End TailC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EntryC.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hmemset : memset20_contract SEGS W.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 64) 64.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x1048c.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 64)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 64)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (sp1 X RAW : word) (vc : Z).
  Hypothesis Hsp1 : bv_unsigned sp1 = (bv_unsigned sp - 48)%Z.
  Hypothesis TR2 : getr R 2 = sp1.
  Hypothesis TR8 : getr R 8 = C.
  Hypothesis TR9 : getr R 9 = buf.
  Hypothesis TR13 : getr R 13 = cs.
  Hypothesis TR10 : getr R 10 = X.
  Hypothesis TR18 : getr R 18 = RAW.
  Hypothesis HXv : (bv_unsigned X mod 2 ^ 32 = vc)%Z.
  Hypothesis HRv : (bv_unsigned RAW = 0 <-> vc = 0)%Z.
  Hypothesis Hvsz : (12 + 2 * vc <= size)%Z.
  Hypothesis TRK : forall r, In r rc_untouched -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)].
  Hypothesis S40 : cell64 SEGS M (bv_unsigned sp - 8) ret.
  Hypothesis S32 : cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8).
  Hypothesis S24 : cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9).
  Hypothesis S16 : cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18).
  Hypothesis S8 : cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19).

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc))
                                ++ [ret; getr regs 8; getr regs 9; getr regs 18; getr regs 19]))
                     (blobs_ev []).

  Definition knE : list kentry :=
    [KRange (EVar 2) 16 (2^64 - 48);
     KWord (SA (EVar 2) 40) 8 (EVar 64);
     KWord (SA (EVar 2) 32) 8 (EVar 65);
     KWord (SA (EVar 2) 24) 8 (EVar 66);
     KWord (SA (EVar 2) 16) 8 (EVar 67);
     KWord (SA (EVar 2) 8) 8 (EVar 68)].

  Lemma knE_ok : know_ok SEGS E M knE.
  Proof using FPc HWS Hsp1 S16 S24 S32 S40 S8 TR2.
    clear HFK TRK Hro HDC HDS HSC Hcs HXv HRv Hvsz.
    unfold knE. pose proof (u64_range sp).
    pose proof HWS as (W1 & W2 & W3 & W4).
    unfold cell64, cell in S40, S32, S24, S16, S8.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 40 8 (EVar 64) ret);
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 40)%Z with (bv_unsigned sp - 8)%Z by lia. exact S40.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 32 8 (EVar 65) (getr regs 8));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 32)%Z with (bv_unsigned sp - 16)%Z by lia. exact S32.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 24 8 (EVar 66) (getr regs 9));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 24)%Z with (bv_unsigned sp - 24)%Z by lia. exact S24.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 16 8 (EVar 67) (getr regs 18));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 16)%Z with (bv_unsigned sp - 32)%Z by lia. exact S16.
    - eapply (kword_intro SEGS E M (EVar 2) sp1 8 8 (EVar 68) (getr regs 19));
        [cbn; exact TR2 | cbn; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
      replace (bv_unsigned sp1 + 8)%Z with (bv_unsigned sp - 40)%Z by lia. exact S8.
  Qed.

  (* [comment removed for export] *)
  Ltac to_tailC HMf Tcs :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HK : know_ok _ _ ?Mx _, HR0 : id _, HF0 : id _
      |- runs_to _ (@mkst ?I ?Rx _ ?Mx _) _ =>
      let T40 := fresh "T40" in let T32 := fresh "T32" in let T24 := fresh "T24" in
      let T16 := fresh "T16" in let T8 := fresh "T8" in
      kread_fact HK (EVar 2) 40%Z 8%nat T40; kread_fact HK (EVar 2) 32%Z 8%nat T32;
      kread_fact HK (EVar 2) 24%Z 8%nat T24; kread_fact HK (EVar 2) 16%Z 8%nat T16;
      kread_fact HK (EVar 2) 8%Z 8%nat T8;
      rewrite TR2 in T40, T32, T24, T16, T8; unfold v_addi in T40, T32, T24, T16, T8;
      unfold id in HR0, HF0;
      eapply (tailC_ok FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hret Hsp Hdok Hsize Hin HWC HCal HWS
                HDC HSC HDS Hcs I Rx Mx sp1 X RAW vc Hsp1);
      [ regv HR (2%bv:reg); exact TR2
      | regv HR (8%bv:reg); exact TR8
      | regv HR (9%bv:reg); exact TR9
      | regv HR (10%bv:reg); exact TR10
      | regv HR (18%bv:reg); exact TR18
      | exact HXv | exact HRv | exact Hvsz
      | intros r Hr; rewrite <- (TRK r Hr); exact (regs_same_on _ _ _ R Rx rc_untouched HR0 HR ltac:(vm_compute; reflexivity) r Hr)
      | eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept; intros r Hr;
        exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
      | exact HMf
      | unfold cell64, cell; replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp1 + 40)%Z by lia; exact T40
      | unfold cell64, cell; replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp1 + 32)%Z by lia; exact T32
      | unfold cell64, cell; replace (bv_unsigned sp - 24)%Z with (bv_unsigned sp1 + 24)%Z by lia; exact T24
      | unfold cell64, cell; replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp1 + 16)%Z by lia; exact T16
      | unfold cell64, cell; replace (bv_unsigned sp - 40)%Z with (bv_unsigned sp1 + 8)%Z by lia; exact T8
      | exact Tcs ]
    end.

  Lemma tailC_entry :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x144e8) M rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using HCal HDC HDS HFK HM HRv HSC HWC HWS HXv Hcs Hdok Hin Hmemset Hret Hsize Hsp Hsp1 Hvsz S16 S24 S32 S40 S8 TR10 TR13 TR18 TR2 TR8 TR9 TRK.
    pose proof (Hmemset, Hret, Hsp, Hdok, Hsize, Hin, HWC, HCal, HWS, HDC, HSC, HDS, Hcs, Hsp1, TR2, TR8, TR9, TR13, TR10, TR18,
                HXv, HRv, Hvsz, TRK, HFK, HM, S40, S32, S24, S16, S8) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range cs) as Rcs.
    pose proof HWS as (W1 & W2 & W3 & W4).
    hide HDC. hide HSC. hide HDS. hide HXv. hide HRv.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knE_ok as HK.
    destruct (Z.eq_dec (bv_unsigned cs) 0) as [Hcs0 | Hnz].
    - (* [comment removed for export] *)
      add_krange (EVar 13) 0%Z 0%Z by (rewrite TR13; lia).
      run_fp 3%nat [0x144f0%Z] noscr false.
      assert (HMf : frame_mod mem M ((Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)
                                     :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])))
        by (rewrite Hcs0; exact HM).
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v) by (intros; lia).
      to_tailC HMf Tcs.
    - (* [comment removed for export] *)
      destruct Hcs as [? | (HWcs & Hcsal & Hcs1 & Hcs2 & Hcs3)]; [lia|].
      pose proof HWcs as (X1 & X2 & X3 & X4). hide Hcs1. hide Hcs2.
      add_krange (EVar 13) 1%Z (2^64 - 4)%Z by (rewrite TR13; lia).
      lazymatch goal with
      | HK : know_ok _ _ _ ?kn |- _ =>
        let HK2 := fresh "HK" in
        assert (HK2 : know_ok SEGS E M (KWr (SA (EVar 13) 0) 4 :: KDisj (SA (EVar 2) (-16)) 64 (SA (EVar 13) 0) 4 :: kn));
        [ apply know_ok_cons;
          [ apply (kwr_intro SEGS E M (EVar 13) cs 0 4); [cbn; exact TR13 | lia | lia | lia |];
            rewrite Z.add_0_r; eapply frame_mod_store_ok; [exact HM | exact X4]
          | apply know_ok_cons; [| exact HK];
            cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite TR2, TR13; lia ]
        | clear HK; rename HK2 into HK ]
      end.
      run_fp 3%nat [0x144f0%Z] noscr true.
      assert (Hf : frame_mod M M0 [(cs, 4%Z)]).
      { rewrite EQM.
        replace [(cs, 4%Z)] with (regions_denot E [(SA (EVar 13) 0, 4%Z)])
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E;
              rewrite TR13; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
        apply (frame_mod_mem_denot E M _ [(SA (EVar 13) 0, 4%Z)] HLF); [flats_auto | vm_compute; reflexivity]. }
      clear EQM HLF.
      assert (HMf : frame_mod mem M0 ((Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)
                                      :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)]))).
      { destruct (Z.eq_dec (bv_unsigned cs) 0) as [|_]; [lia|].
        eapply frame_mod_trans_same.
        - eapply frame_mod_of_covered; [|exact HM]. solve_covered.
        - eapply frame_mod_of_covered; [|exact Hf]. solve_covered. }
      kread_fact HK (EVar 13) 0%Z 4%nat Tc. rewrite TR13 in Tc. unfold v_addi in Tc. rewrite ?Z.add_0_r in Tc.
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M0 (bv_unsigned cs) v)
        by (intros _; eexists; apply cell32_of_word; exact Tc).
      clear Tc Hf.
      to_tailC HMf Tcs.
  Qed.
End EntryC.
End LibReadCurveS1C.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibWP1Spec LibCurveSpec LibRodata LibBswap LibFPLib LibTagsLib LibTagsCall LibReadCurveLib. Import LibReadCurveS1K. Import LibReadCurveS1P. Import LibReadCurveS1C.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := wp1_src1.

Section Main.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hmemset : memset20_contract SEGS W.
  Hypothesis Hclassify : classify_contract SEGS W.
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hbuf : getr regs 10 = buf.
  Hypothesis Hsz : getr regs 11 = Z_to_bv 64 size.
  Hypothesis HC : getr regs 12 = C.
  Hypothesis Hcs13 : getr regs 13 = cs.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis Hspal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 64) 64.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x1048c.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 64)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 64)%Z).

  #[local] Abbreviation off := (bv_unsigned buf - bv_unsigned data)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ []))
                     (blobs_ev [sub bs off 4; sub bs off 12]).

  Definition kn0 : list kentry :=
    [KImg 0x103ec 0x1048c;
     KRange (EVar 2) 64 (2^64 - 1);
     KRange (EVar 10) 1 (2^47);
     KRange (EVar 11) 0 (2^32 - 1);
     KRange (EVar 12) 0 (2^64 - 32);
     KWr (SA (EVar 2) (-64)) 64;
     KDisj (SA (EVar 2) (-64)) 64 (SA (ELit 0) 0x103ec) 160].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using FPI HC HWC HWS Hbuf Hdok Hin Hro Hsize Hsp Hsz cs.
    unfold kn0. pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range buf). pose proof (u64_range data).
    pose proof (u64_range cs).
    pose proof (writable_rodata_apart_S1 mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) HWS Hro) as Hsro.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    clear HDC HDS HSC.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply kimg_intro; [lia|lia|exact Hro].
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply krange_intro; cbn. rewrite Hbuf. lia.
    - apply krange_intro; cbn. rewrite Hsz, u_small by lia. lia.
    - apply krange_intro; cbn. rewrite HC. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-64) 64); [cbn; exact Hsp | lia | lia | lia |].
      replace (bv_unsigned sp + -64)%Z with (bv_unsigned sp - 64)%Z by lia. exact W4.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
  Qed.

  (* [comment removed for export] *)
  Definition nuoff (j : nat) : Z := match j with 8%nat => 8 | 9%nat => 9 | 10%nat => 10 | _ => 11 end.
  Definition nu (j : nat) : Z := bs_byte bs (off + nuoff j).
  Definition atoms : list (expr * (bool * nat)) :=
    [(EBlob false 1 8 1, (false, 8%nat)); (EBlob false 1 9 1, (false, 9%nat));
     (EBlob false 1 10 1, (false, 10%nat)); (EBlob false 1 11 1, (false, 11%nat))].
  Lemma nu_range : forall j, (0 <= nu j < 256)%Z.
  Proof using . intros j. unfold nu. apply bs_byte_range. Qed.
  Lemma atoms_ok12 : (12 <= size)%Z -> atoms_ok E nu atoms.
  Proof using FPI HDC HDS HSC Hcs Hdok Hin regs.
    intros H12. pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    unfold atoms, atoms_ok. repeat (apply Forall_cons); [..|apply Forall_nil];
      unfold atom_ok; cbn [edenot eb E blobs_ev nth]; unfold nu; cbn [nuoff];
      (rewrite blob_val_sub_u8; [reflexivity | lia | lia | lia]).
  Qed.
  #[local] Abbreviation vc := (be32 bs (off + 8)).

  (* [comment removed for export] *)
  Definition RAWe : expr :=
    EAlu ALU_ADD (EBlob false 1 8 1)
      (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EBlob false 1 9 1))
         (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EBlob false 1 10 1))
            (EMd M_MUL (ELit 16777216) (EBlob false 1 11 1)))).
  Definition Xe : expr :=
    EAlu ALU_OR
      (EAlu ALU_OR (EAluw ALU_SLL (EBlob false 1 8 1) (ELit 24))
         (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EBlob false 1 10 1)) (EBlob false 1 11 1)))
      (EMd M_MUL (ELit 256) (EAlu ALU_AND RAWe (ELit 65280))).
  Definition X11e : expr :=
    EAlu ALU_ADD (EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) Xe) (ELit 31)) (ELit 12).

  Lemma be32_nu : vc = (nu 11 + 256 * (nu 10 + 256 * (nu 9 + 256 * nu 8)))%Z.
  Proof using C cs sp.
    unfold be32, nu. cbn [nuoff].
    replace (off + 8 + 1)%Z with (off + 9)%Z by lia.
    replace (off + 8 + 2)%Z with (off + 10)%Z by lia.
    replace (off + 8 + 3)%Z with (off + 11)%Z by lia. lia.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma Xe_low32 : (12 <= size)%Z -> (bv_unsigned (edenot E Xe) mod 2 ^ 32 = vc)%Z.
  Proof using FPI HDC HDS HSC Hcs Hdok Hin Hsize regs rom.
    intros H12.
    pose proof (beval_bytes E nu nu_range atoms (EExt false 0 4 Xe) [11; 10; 9; 8]%nat (atoms_ok12 H12)
                  ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as B.
    cbn [edenot bytes_val] in B. fold (edenot E Xe) in B.
    rewrite ext_val_4_word in B. pose proof (u64_range (edenot E Xe)).
    rewrite u_small in B by lia. rewrite be32_nu. lia.
  Qed.

  Lemma RAWe_val : (12 <= size)%Z ->
    bv_unsigned (edenot E RAWe) = (nu 8 + 256 * (nu 9 + 256 * (nu 10 + 256 * nu 11)))%Z.
  Proof using FPI HDC HDS HSC Hcs Hdok Hin Hsize regs rom.
    intros H12.
    pose proof (beval_bytes E nu nu_range atoms RAWe [8; 9; 10; 11]%nat (atoms_ok12 H12)
                  ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as B.
    cbn [bytes_val] in B. lia.
  Qed.

  Lemma RAW_zero : (12 <= size)%Z -> (bv_unsigned (edenot E RAWe) = 0 <-> vc = 0)%Z.
  Proof using FPI HDC HDS HSC Hcs Hdok Hin Hsize regs rom.
    intros H12. rewrite RAWe_val by exact H12. rewrite be32_nu.
    pose proof (nu_range 8). pose proof (nu_range 9). pose proof (nu_range 10). pose proof (nu_range 11). lia.
  Qed.

  Lemma X11e_val : (12 <= size)%Z -> bv_unsigned (edenot E X11e) = (2 * vc + 12)%Z.
  Proof using FPI HDC HDS HSC Hcs Hdok Hin Hsize regs rom.
    intros H12. rewrite <- (Xe_low32 H12).
    change (edenot E X11e) with
      (alu64 ALU_ADD (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) (edenot E Xe)) (Z_to_bv 64 31)) (Z_to_bv 64 12)).
    pose proof (u_mul32_srl31 (edenot E Xe)) as U.
    pose proof (Z.mod_pos_bound (bv_unsigned (edenot E Xe)) (2 ^ 32) ltac:(lia)).
    rewrite alu_add_lit, u_small by lia. lia.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma exit_facts : forall M', frame_mod mem M' [(Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)] ->
    frame_mod mem M' (RSF sp C cs) /\
    (curve_ok SEGS mem data len (bv_unsigned C) -> curve_ok SEGS M' data len (bv_unsigned C)).
  Proof using HSC HWC HWS Hcs.
    intros M' HMs. clear Hro HDC HDS.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    split.
    - eapply frame_mod_of_covered; [| exact HMs]. unfold RSF.
      destruct (Z.eq_dec (bv_unsigned cs) 0);
        [ solve_covered | destruct Hcs as [?|(X & ?)]; [lia|]; destruct X as (?&?&?&?); solve_covered ].
    - intros Hc. eapply curve_ok_frame; [exact HMs | exact Hc | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Ltac post_exit HMs :=
    fin_ret;
    let XF1 := fresh "XF1" in let XF2 := fresh "XF2" in
    lazymatch type of HMs with frame_mod mem ?M1 _ => destruct (exit_facts M1 HMs) as [XF1 XF2] end;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _, HR0 : id _, HF0 : id _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      unfold id in HR0, HF0;
      split; [ unfold regs_kept; eapply (regs_same_on _ _ _ regs R2 abi_kept); [exact HR0 | exact HR | vm_compute; reflexivity] |];
      split; [ unfold fregs_kept; eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |];
      unfold rcurve_post; cbv zeta; cbn [w1_rcurve_d wp1_src1]; unfold RSF in XF1;
      split; [ exact XF1 |];
      exists 0%Z; split; [regv HR (10%bv:reg); reflexivity|];
      split; [left; reflexivity|];
      split; [intros; lia|];
      split; [ exact XF2 |];
      intros; lia
    end.

  (* [comment removed for export] *)
  Ltac fold_stack HMs :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot ?Ex ?M0 ?log, HLF : log_flat _ _ |- _ =>
        let Hf := fresh "Hf" in
        assert (Hf : frame_mod M0 M1 [(Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)]);
        [ rewrite EQM;
          replace [(Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)] with (regions_denot Ex [(SA (EVar 2) (-64), 64%Z)])
            by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl Ex;
                rewrite Hsp; unfold v_addi; repeat f_equal; lia);
          apply (frame_mod_mem_denot Ex M0 log [(SA (EVar 2) (-64), 64%Z)] HLF); [flats_auto | vm_compute; reflexivity]
        | let H2 := fresh "HMs" in
          pose proof (frame_mod_trans_same _ _ _ _ HMs Hf) as H2; clear HMs Hf EQM HLF; rename H2 into HMs ]
    | EQM : ?M1 = ?M0, HLF : log_flat _ _ |- _ => subst M1; clear HLF
    end.

  (* [comment removed for export] *)
  Ltac add_blob L idx Hsz :=
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx ?kn, HMs : frame_mod mem ?Mx _ |- _ =>
      let HK2 := fresh "HK" in
      assert (HK2 : know_ok SEGS Ex Mx (KBlob (SA (EVar 10) 0) (ELit L) idx :: kn));
      [ apply know_ok_cons; [| exact HK];
        eapply (kblob_sub SEGS Ex Mx (EVar 10) buf data len bs off L idx);
        [ cbn; exact Hbuf | reflexivity
        | eapply data_ok_frame; [exact HMs | exact Hdok | unhide HDS; solve_apart]
        | reflexivity | lia | lia | lia ]
      | clear HK; rename HK2 into HK ]
    end.

  (* [comment removed for export] *)
  Ltac stack_cells S40 S32 S24 S16 S8 :=
    lazymatch goal with
    | HK : know_ok _ _ ?Mx _ |- _ =>
      kread_fact HK (EVar 2) (-8)%Z 8%nat S40; kread_fact HK (EVar 2) (-16)%Z 8%nat S32;
      kread_fact HK (EVar 2) (-24)%Z 8%nat S24; kread_fact HK (EVar 2) (-32)%Z 8%nat S16;
      kread_fact HK (EVar 2) (-40)%Z 8%nat S8;
      rewrite Hsp in S40, S32, S24, S16, S8; unfold v_addi in S40, S32, S24, S16, S8;
      rewrite Hra in S40
    end.

  (* [comment removed for export] *)
  Ltac hand_C Hc3 Hc4 :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HMs : frame_mod mem ?Mx [_], HR0 : id _, HF0 : id _,
      T40 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -8)) 8 = _,
      T32 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -16)) 8 = _,
      T24 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -24)) 8 = _,
      T16 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -32)) 8 = _,
      T8 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -40)) 8 = _
      |- runs_to _ (@mkst ?I ?Rx _ ?Mx _) _ =>
      unfold id in HR0, HF0;
      eapply (tailC_entry FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hret Hsp Hdok Hsize Hin HWC HCal HWS
                HDC HSC HDS Hcs I Rx Mx (Z_to_bv 64 (bv_unsigned sp - 48)) (edenot E Xe) (edenot E RAWe) vc);
      [ rewrite u_small by lia; reflexivity
      | regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia
      | regv HR (8%bv:reg); exact HC
      | regv HR (9%bv:reg); exact Hbuf
      | regv HR (13%bv:reg); exact Hcs13
      | rewrite (reg_val _ _ _ (10%bv:reg) HR); reflexivity
      | rewrite (reg_val _ _ _ (18%bv:reg) HR); reflexivity
      | apply Xe_low32; exact Hc3
      | apply RAW_zero; exact Hc3
      | let HX11 := fresh "HX11" in
        pose proof (X11e_val Hc3) as HX11; unfold X11e, Xe, RAWe in HX11;
        rewrite branch_taken_Z in Hc4; cbv beta iota in Hc4; rewrite HX11 in Hc4;
        cbn [edenot] in Hc4; ev_simpl_in E Hc4; rewrite Hsz, u_small in Hc4 by lia;
        apply Bool.negb_true_iff in Hc4; apply Z.ltb_ge in Hc4; clear -Hc4; lia
      | intros r Hr; exact (regs_same_on _ _ _ regs Rx rc_untouched HR0 HR ltac:(vm_compute; reflexivity) r Hr)
      | unfold fregs_kept; intros r Hr; exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
      | exact HMs
      | unfold cell64, cell; replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp + -8)%Z by lia; exact T40
      | unfold cell64, cell; replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp + -16)%Z by lia; exact T32
      | unfold cell64, cell; replace (bv_unsigned sp - 24)%Z with (bv_unsigned sp + -24)%Z by lia; exact T24
      | unfold cell64, cell; replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp + -32)%Z by lia; exact T16
      | unfold cell64, cell; replace (bv_unsigned sp - 40)%Z with (bv_unsigned sp + -40)%Z by lia; exact T8 ]
    end.

  (* [comment removed for export] *)
  Ltac hand_P Hb9 Hc4 :=
    lazymatch type of Hb9 with _ = ?kv =>
      lazymatch goal with
      | HR : regs_ok _ _ _ |- _ =>
        pin_reg HR (12%bv:reg) (ELit kv) by (regv HR (12%bv:reg); rewrite blob_val_sub_u8w by lia; rewrite Hb9; reflexivity)
      end;
      run_fp 30%nat [0x14314%Z] noscr false;
      (* [comment removed for export] *)
      let Hc5 := fresh "Hc5" in
      branch_case as Hc5;
      [ lazymatch goal with HMs : frame_mod mem _ [_] |- _ => run_fp 20%nat (@nil Z) noscr false; post_exit HMs end
      | br_simpl_in E Hc5; rewrite Hsz, u_small in Hc5 by lia; rewrite ?Z.mod_small in Hc5 by lia; apply Z.ltb_ge in Hc5;
        lazymatch goal with
        | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HMs : frame_mod mem ?Mx [_], HR0 : id _, HF0 : id _,
          T40 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -8)) 8 = _,
          T32 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -16)) 8 = _,
          T24 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -24)) 8 = _,
          T16 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -32)) 8 = _,
          T8 : rdn _ ?Mx (Z_to_bv 64 (bv_unsigned sp + -40)) 8 = _
          |- runs_to _ (@mkst ?I ?Rx _ ?Mx _) _ =>
          unfold id in HR0, HF0;
          eapply (tailP_entry FPI regs mem rom ret data len bs sp buf C cs size Hmemset Hclassify Hret Hsp Hdok Hsize Hin HWC HCal HWS
                    Hro HDC HSC HDS Hcs I Rx Mx (Z_to_bv 64 (bv_unsigned sp - 48)) kv);
          [ rewrite u_small by lia; reflexivity
          | regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia
          | regv HR (8%bv:reg); exact HC
          | regv HR (9%bv:reg); exact Hbuf
          | regv HR (13%bv:reg); exact Hcs13
          | regv HR (18%bv:reg); reflexivity
          | lia
          | cbn [cb]; exact Hc5
          | intros r Hr; exact (regs_same_on _ _ _ regs Rx rc_untouched HR0 HR ltac:(vm_compute; reflexivity) r Hr)
          | unfold fregs_kept; intros r Hr; exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
          | exact HMs
          | unfold cell64, cell; replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp + -8)%Z by lia; exact T40
          | unfold cell64, cell; replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp + -16)%Z by lia; exact T32
          | unfold cell64, cell; replace (bv_unsigned sp - 24)%Z with (bv_unsigned sp + -24)%Z by lia; exact T24
          | unfold cell64, cell; replace (bv_unsigned sp - 32)%Z with (bv_unsigned sp + -32)%Z by lia; exact T16
          | unfold cell64, cell; replace (bv_unsigned sp - 40)%Z with (bv_unsigned sp + -40)%Z by lia; exact T8 ]
        end ]
    end.

  Lemma main_ok :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x1424c) mem rom)
            (RCQ regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using HC HCal HDC HDS HSC HWC HWS Hbuf Hclassify Hcs Hcs13 Hdok Hin Hmemset Hra Hret Hro Hsize Hsp Hspal Hsz.
    (* [comment removed for export] *)
    pose proof (Hmemset, Hclassify, Hra, Hret, Hsp, Hbuf, Hsz, HC, Hcs13, Hdok, Hsize, Hin, HWC, HCal, Hspal, HWS, Hro,
                HDC, HSC, HDS, Hcs) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof (u64_range buf) as Rbuf. pose proof (u64_range data) as Rdata.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    hide HDC. hide HSC. hide HDS. hide Hcs.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [sub bs off 4; sub bs off 12])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [sub bs off 4; sub bs off 12])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK.
    pose proof (frame_mod_refl mem [(Z_to_bv 64 (bv_unsigned sp - 64), 64%Z)]) as HMs.
    (* [comment removed for export] *)
    run_fp 10%nat [0x14264%Z] noscr true. fold_stack HMs.
    stack_cells T40 T32 T24 T16 T8.
    (* [comment removed for export] *)
    run_fp 20%nat (@nil Z) noscr false.
    branch_case as Hc1.
    { run_fp 20%nat (@nil Z) noscr false. post_exit HMs. }
    br_simpl_in E Hc1. rewrite Hsz, u_small in Hc1 by lia. rewrite ?Z.mod_small in Hc1 by lia. apply Z.ltb_ge in Hc1.
    add_blob 4%Z 0%nat Hc1.
    (* [comment removed for export] *)
    run_fp 40%nat (@nil Z) noscr false.
    branch_case as Hc2.
    { (* [comment removed for export] *)
      clear Hc2.
      run_fp 10%nat (@nil Z) noscr false.
      branch_case as Hc3.
      { run_fp 20%nat (@nil Z) noscr false. post_exit HMs. }
      br_simpl_in E Hc3. rewrite Hsz, u_small in Hc3 by lia. rewrite ?Z.mod_small in Hc3 by lia. apply Z.ltb_ge in Hc3.
      add_blob 12%Z 1%nat Hc3.
      run_fp 60%nat (@nil Z) noscr false.
      (* [comment removed for export] *)
      branch_case as Hc4.
      2:{ run_fp 20%nat (@nil Z) noscr false. post_exit HMs. }
      hand_C Hc3 Hc4. }
    run_fp 10%nat (@nil Z) noscr false.
    branch_case as Hc3.
    { run_fp 20%nat (@nil Z) noscr false. post_exit HMs. }
    clear Hc2 Hc3.
    (* [comment removed for export] *)
    run_fp 10%nat (@nil Z) noscr false.
    branch_case as Hc4.
    { run_fp 20%nat (@nil Z) noscr false. post_exit HMs. }
    br_simpl_in E Hc4. rewrite Hsz, u_small in Hc4 by lia. rewrite ?Z.mod_small in Hc4 by lia. apply Z.ltb_ge in Hc4.
    add_blob 12%Z 1%nat Hc4.
    (* [comment removed for export] *)
    run_fp 20%nat [0x142d0%Z] noscr false.
    pose proof (bs_byte_range bs (off + 8)) as Rb8. pose proof (bs_byte_range bs (off + 9)) as Rb9.
    assert (Hft : ((bs_byte bs (off + 8) = 0 /\ (bs_byte bs (off + 9) = 0 \/ bs_byte bs (off + 9) = 1 \/ bs_byte bs (off + 9) = 2
                                             \/ bs_byte bs (off + 9) = 3 \/ bs_byte bs (off + 9) = 4))
                   \/ 4 < 256 * bs_byte bs (off + 8) + bs_byte bs (off + 9))%Z) by lia.
    destruct Hft as [[Hb8 Hb9] | Hbig].
    2:{ (* [comment removed for export] *)
        run_fp 40%nat (@nil Z) (dirs [true]) false by (rewrite ?blob_val_sub_u8 by lia; lia).
        post_exit HMs. }
    pin_reg HR (10%bv:reg) (ELit 0) by (regv HR (10%bv:reg); rewrite blob_val_sub_u8w by lia; rewrite Hb8; reflexivity).
    destruct Hb9 as [Hb9 | [Hb9 | [Hb9 | [Hb9 | Hb9]]]].
    all: hand_P Hb9 Hc4.
  Qed.
End Main.

Theorem read_curve_S1_ok :
  memset20_contract SEGS W -> classify_contract SEGS W -> read_curve_contract SEGS W.
Proof.
  intros Hm Hcl data len bs sp buf C cs size FPI regs mem rom ret Hra Hret PRE.
  unfold rcurve_pre in PRE. cbv zeta in PRE. cbn [w1_rcurve_d w1_ro_lo w1_ro_hi wp1_src1] in PRE.
  destruct PRE as (Hsp & Hbuf & Hsz & HC & Hcs13 & Hdok & Hsize & Hin & HWC & HCal & Hspal & HWS & Hro & HDC & HSC & HDS & Hcs).
  apply runs_to_contract with
    (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
            /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
            /\ rcurve_post SEGS W data len bs sp buf C cs size regs mem FPI' regs' mem').
  exact (main_ok FPI regs mem rom ret data len bs sp buf C cs size Hm Hcl Hra Hret Hsp Hbuf Hsz HC Hcs13
           Hdok Hsize Hin HWC HCal Hspal HWS Hro HDC HSC HDS Hcs).
Qed.
