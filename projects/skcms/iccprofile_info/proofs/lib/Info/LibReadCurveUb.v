(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibWP1Spec LibCurveSpec LibRodata LibBswap LibFPLib LibTagsLib LibTagsCall LibReadCurveLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require SymDriveLB.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)

Module LibReadCurveUbK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibCurveSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadCurveLib.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.
#[local] Abbreviation W := wp1_infoub.

(* [comment removed for export] *)
Definition abi_kept_nosp : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma abi_kept_split2 : forall (regs regs' : bvmap 5 word),
  getr regs' 2 = getr regs 2 ->
  (forall r, In r abi_kept_nosp -> getr regs' r = getr regs r) ->
  regs_kept abi_kept regs regs'.
Proof.
  intros regs regs' H2 HU r Hr. unfold abi_kept in Hr.
  cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [first [assumption | apply HU; cbn; tauto]|]).
  destruct Hr.
Qed.

(* [comment removed for export] *)
Definition RCQU (regs : bvmap 5 word) (mem rom : word -> option byte) (ret : word) (FPI : FPState)
    (data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z)
    (st' : machine_state) : Prop :=
  exists (FPI' : FPState) regs' mem',
    st' = mkst (FP:=FPI') regs' ret mem' rom /\
    regs_kept abi_kept regs regs' /\
    fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
    rcurve_post SEGS W data len bs sp buf C cs size regs mem FPI' regs' mem'.

(* [comment removed for export] *)
Definition RSFU (sp C cs : word) : list (word * Z) :=
  (Z_to_bv 64 (bv_unsigned sp - 32), 32%Z) :: (C, 32%Z)
    :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)]).

Section TailK.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hclassify : classify_contract SEGS W.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 32) 32.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x10490.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 32)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 32)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (g a b cc d e f : word).
  Hypothesis TR1 : getr R 1 = ret.
  Hypothesis TR12 : getr R 12 = C.
  Hypothesis TRK : forall r, In r abi_kept -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M (RSFU sp C cs).
  Hypothesis C0 : cell SEGS M (bv_unsigned C) 4 (Z_to_bv 64 0).
  Hypothesis C4 : cell SEGS M (bv_unsigned C + 4) 4 g.
  Hypothesis C8 : cell SEGS M (bv_unsigned C + 8) 4 a.
  Hypothesis C12 : cell SEGS M (bv_unsigned C + 12) 4 b.
  Hypothesis C16 : cell SEGS M (bv_unsigned C + 16) 4 cc.
  Hypothesis C20 : cell SEGS M (bv_unsigned C + 20) 4 d.
  Hypothesis C24 : cell SEGS M (bv_unsigned C + 24) 4 e.
  Hypothesis C28 : cell SEGS M (bv_unsigned C + 28) 4 f.
  Hypothesis Hcsv : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v.

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [])) (blobs_ev []).

  Definition knKU : list kentry :=
    [KRange (EVar 2) 32 (2^64 - 1);
     KRange (EVar 12) 0 (2^64 - 32);
     KWr (SA (EVar 2) (-32)) 32;
     KDisj (SA (EVar 2) (-32)) 32 (SA (EVar 12) 0) 32].

  Lemma TR2 : getr R 2 = sp.
  Proof using Hsp TRK. clear - TRK Hsp. rewrite (TRK 2%bv) by (cbn; tauto). exact Hsp. Qed.

  Lemma knKU_ok : know_ok SEGS E M knKU.
  Proof using FPc HM HSC HWC HWS Hsp TR12 TRK f rom.
    clear Hcsv HFK Hro Hcs.
    unfold knKU. pose proof (u64_range sp). pose proof (u64_range C). pose proof TR2 as TR2.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR2. lia.
    - apply krange_intro; cbn. rewrite TR12. lia.
    - apply (kwr_intro SEGS E M (EVar 2) sp (-32) 32); [cbn; exact TR2 | lia | lia | lia |].
      replace (bv_unsigned sp + -32)%Z with (bv_unsigned sp - 32)%Z by lia.
      eapply frame_mod_store_ok; [exact HM | exact W4].
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite TR2, TR12. lia.
  Qed.

  Lemma apart_rodata : apart 0x103ec (0x10490 - 0x103ec) (RSFU sp C cs).
  Proof using HWC HWS Hcs Hro f rom.
    clear Hcsv HFK TRK.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof (writable_rodata_apart_Ub mem _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) HWS Hro).
    pose proof (writable_rodata_apart_Ub mem _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) HWC Hro).
    pose proof HWS as (W1 & W2 & W3 & W4).
    unfold RSFU. destruct (Z.eq_dec (bv_unsigned cs) 0).
    - solve_apart.
    - destruct Hcs as [Hc0 | (HWcs & _)]; [lia|].
      pose proof (writable_rodata_apart_Ub mem _ _ 0x103ec 0x10490 ltac:(lia) ltac:(lia) ltac:(lia) HWcs Hro).
      solve_apart.
  Qed.

  (* [comment removed for export] *)
  Lemma M_rodata : forall M', frame_mod mem M' (RSFU sp C cs) -> rodata_clear M' 0x103ec 0x10490.
  Proof using HWC HWS Hcs Hro f rom. intros M' Hf. eapply rodata_clear_frame; [exact Hf | exact Hro | lia | lia | apply apart_rodata]. Qed.

  Lemma stack16 : forall M', frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)] -> frame_mod mem M' (RSFU sp C cs).
  Proof using HM HWS f rom.
    intros M' Hf. clear Hcsv HFK TRK Hro Hcs HSC.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof HWS as (W1 & W2 & W3 & W4).
    eapply frame_mod_trans_same; [exact HM|]. eapply frame_mod_of_covered; [|exact Hf]. unfold RSFU. solve_covered.
  Qed.

  Lemma cells_after : forall M', frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)] ->
    curve_ok SEGS M' data len (bv_unsigned C) /\
    (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M' (bv_unsigned cs) v).
  Proof using C0 C12 C16 C20 C8 HSC HWC HWS Hcs Hcsv f rom.
    intros M' Hf. clear HFK TRK Hro.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    split.
    - apply (curve_ok_zero4 SEGS M' data len (bv_unsigned C) a b cc d); try lia;
        (eapply cell_frame; [exact Hf | eassumption | lia | cbn; lia | cbn; solve_apart]).
    - intros Hnz. destruct (Hcsv Hnz) as [v Hv]. exists v.
      destruct Hcs as [Hc0 | (HWcs & _ & _ & _ & Hcs3)]; [lia|]. destruct HWcs as (X1 & X2 & X3 & X4).
      eapply cell32_frame; [exact Hf | exact Hv | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Ltac fold_frame :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot ?Ex ?M0 ?log, HLF : log_flat _ _, HMt : frame_mod M ?M0' _ |- _ =>
        let Hf := fresh "Hf" in
        assert (Hf : frame_mod M0 M1 [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)]);
        [ rewrite EQM;
          replace [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)] with (regions_denot Ex [(SA (EVar 2) (-32), 32%Z)])
            by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl Ex;
                rewrite TR2; unfold v_addi; repeat f_equal; lia);
          apply (frame_mod_mem_denot Ex M0 log [(SA (EVar 2) (-32), 32%Z)] HLF); [flats_auto | vm_compute; reflexivity]
        | let H2 := fresh "HMt" in
          pose proof (frame_mod_trans_same _ _ _ _ HMt Hf) as H2; clear HMt Hf EQM HLF; rename H2 into HMt ]
    | EQM : ?M1 = ?M0, HLF : log_flat _ _ |- _ => subst M1; clear HLF
    end.

  Lemma tailK_ok :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x14cd4) M rom)
            (RCQU regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using C0 C12 C16 C20 C24 C28 C4 C8 HFK HM HSC HWC HWS Hclassify Hcs Hcsv Hret Hro Hsp TR1 TR12 TRK.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4). pose proof TR2 as TR2.
    hide HSC. hide Hcs.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knKU_ok as HK.
    pose proof (frame_mod_refl M [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)]) as HMt.
    run_fp 20%nat [0x133b8%Z] noscr true. fold_frame.
    (* [comment removed for export] *)
    lazymatch goal with
    | HR : regs_ok _ _ ?Rx |- runs_to _ (@mkst ?I ?Rx _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hclassify (Z_to_bv 64 (bv_unsigned sp - 16)) (Z_to_bv 64 (bv_unsigned C + 4)) I Rx Mx ro (Z_to_bv 64 0x14cec));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | ]
        | ]
    end.
    { unfold classify_pre. cbv zeta. rewrite !u_small by lia.
      split; [regv_lin HR (2%bv:reg); rewrite TR2; f_equal; lia|].
      split; [regv_lin HR (10%bv:reg); rewrite ?TR12; f_equal; lia|].
      split; [regv HR (11%bv:reg); reflexivity|].
      split; [regv HR (12%bv:reg); reflexivity|].
      split.
      { exists g, a, b, cc, d, e, f. unfold cell in *.
        rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
        repeat split; (eapply cell_frame; [exact HMt | eassumption | lia | cbn; lia | cbn; unhide HSC; solve_apart]). }
      split; [lia|].
      split; [eapply writable_sub; [eapply writable_frame; [exact HMt | eapply writable_frame; [exact HM | exact HWS]] | lia | lia | lia]|].
      split; [apply M_rodata; apply stack16; exact HMt|].
      unhide HSC. lia. }
    cbv beta. intros FQ rq mq (Hkeep & Hfkeep & Hfr). unfold classify_post in Hfr.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
    after_call Hkeep Hfkeep FQ. clear Hkeep Hfkeep.
    rewrite u_small in Hfr by lia.
    know_frame HK Hfr [(SA (EVar 2) (-32), 16%Z)];
      [rewrite TR2; unfold v_addi; repeat f_equal; lia|].
    lazymatch type of HMt with frame_mod M ?M1 _ =>
      assert (HMt2 : frame_mod M mq [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)])
        by (eapply frame_mod_trans_same; [exact HMt|]; eapply frame_mod_of_covered; [|exact Hfr]; solve_covered)
    end.
    clear HMt Hfr. rename HMt2 into HMt.
    destruct (cells_after mq HMt) as [Hcurve Hcsv'].
    (* [comment removed for export] *)
    run_fp 30%nat (@nil Z) noscr true. fold_frame.
    fin_ret.
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite TR1; reflexivity|];
      lift_hyp HR0; lift_hyp HF0;
      split; [ apply abi_kept_split2;
               [ regv_lin HR (2%bv:reg); rewrite TR2, Hsp; apply bv_eq; rewrite u_small by lia; lia
               | intros r Hr; rewrite <- (TRK r ltac:(revert Hr; clear; unfold abi_kept_nosp, abi_kept; cbn; tauto)); revert r Hr;
                 eapply (regs_same_on _ _ _ R R2 abi_kept_nosp); [exact HR0 | exact HR | vm_compute; reflexivity] ] |];
      split; [ eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept;
               eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |]
    end.
    unfold rcurve_post. cbv zeta. cbn [w1_rcurve_d wp1_infoub].
    split; [apply stack16; exact HMt|].
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
    (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte) (g a b cc d e f : word),
  classify_contract SEGS W ->
  ret_ok ret ->
  getr regs 2 = sp ->
  writable SEGS mem (bv_unsigned C) 32 ->
  writable SEGS mem (bv_unsigned sp - 32) 32 ->
  rodata_clear mem 0x103ec 0x10490 ->
  (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 32)%Z ->
  ((bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 32)%Z)) ->
  getr R 1 = ret ->
  getr R 12 = C ->
  (forall r, In r abi_kept -> getr R r = getr regs r) ->
  fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)) ->
  frame_mod mem M (RSFU sp C cs) ->
  cell SEGS M (bv_unsigned C) 4 (Z_to_bv 64 0) ->
  cell SEGS M (bv_unsigned C + 4) 4 g ->
  cell SEGS M (bv_unsigned C + 8) 4 a ->
  cell SEGS M (bv_unsigned C + 12) 4 b ->
  cell SEGS M (bv_unsigned C + 16) 4 cc ->
  cell SEGS M (bv_unsigned C + 20) 4 d ->
  cell SEGS M (bv_unsigned C + 24) 4 e ->
  cell SEGS M (bv_unsigned C + 28) 4 f ->
  (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v) ->
  runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x14cd4) M rom)
          (RCQU regs mem rom ret FPI data len bs sp buf C cs size).
Proof.
  intros FPI regs mem rom ret data len bs sp buf C cs size FPc R M g a b cc d e f.
  intros Hcl Hret Hsp HWC HWS Hro HSC Hcs TR1 TR12 TRK HFK HM C0 C4 C8 C12 C16 C20 C24 C28 Hcsv.
  exact (tailK_ok FPI regs mem rom ret data len bs sp buf C cs size Hcl Hret Hsp HWC HWS Hro HSC Hcs
           FPc R M g a b cc d e f TR1 TR12 TRK HFK HM C0 C4 C8 C12 C16 C20 C24 C28 Hcsv).
Qed.
End LibReadCurveUbK.

Module LibReadCurveUbP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibCurveSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadCurveLib LibReadCurveUbK.
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

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.
#[local] Abbreviation W := wp1_infoub.

Section TailP.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hclassify : classify_contract SEGS W.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 32) 32.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x10490.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 32)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 32)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variable k : Z.
  Hypothesis TR1 : getr R 1 = ret.
  Hypothesis TR10 : getr R 10 = buf.
  Hypothesis TR12 : getr R 12 = C.
  Hypothesis TR14 : getr R 14 = Z_to_bv 64 k.
  Hypothesis Hk : (0 <= k <= 4)%Z.
  Hypothesis Hszk : (12 + cb k <= size)%Z.
  Hypothesis TRK : forall r, In r abi_kept -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)]).
  Hypothesis Hcsv : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v.

  #[local] Abbreviation off := (bv_unsigned buf - bv_unsigned data)%Z.
  #[local] Abbreviation Lk := (12 + cb k)%Z.

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ []))
                     (blobs_ev [sub bs off 16; sub bs off Lk]).

  Definition knPU : list kentry :=
    [KRange (EVar 10) 1 (2^47);
     KRange (EVar 12) 0 (2^64 - 32);
     KAlign (EVar 12) 8;
     KWr (SA (EVar 12) 0) 32;
     KDisj (SA (EVar 12) 0) 32 (SA (EVar 10) 0) 16;
     KBlob (SA (EVar 10) 0) (ELit 16) 0].

  Lemma knPU_ok : know_ok SEGS E M knPU.
  Proof.
    clear Hcsv HFK TRK Hro HDS HSC.
    unfold knPU. pose proof (u64_range C). pose proof (u64_range buf). pose proof (u64_range data).
    pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof (cb_range k).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR10. lia.
    - apply krange_intro; cbn. rewrite TR12. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite TR12. exact HCal.
    - apply (kwr_intro SEGS E M (EVar 12) C 0 32); [cbn; exact TR12 | lia | lia | lia |].
      rewrite Z.add_0_r. eapply frame_mod_store_ok; [exact HM | exact V4].
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite TR12, TR10. lia.
    - eapply (kblob_sub SEGS E M (EVar 10) buf data len bs off 16 0);
        [cbn; exact TR10 | reflexivity | | reflexivity | lia | lia | lia].
      eapply data_ok_frame; [exact HM | exact Hdok |].
      destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
      destruct Hcs as [?|(X & _ & ? & _)]; [lia|]. destruct X as (X1 & X2 & X3 & X4). solve_apart.
  Qed.

  Lemma fixed_cells : forall M', frame_mod M M' [(C, 32%Z)] ->
    (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M' (bv_unsigned cs) v).
  Proof.
    intros M' Hf Hnz. clear HFK TRK HDC HDS Hro Hszk Hk.
    pose proof (u64_range C). pose proof (u64_range cs).
    destruct (Hcsv Hnz) as [v Hv]. exists v.
    destruct Hcs as [Hc0 | (HWcs & _ & _ & Hcs2 & _)]; [lia|]. destruct HWcs as (X1 & X2 & X3 & X4).
    eapply cell32_frame; [exact Hf | exact Hv | lia | lia | solve_apart].
  Qed.

  Lemma frame_total : forall M', frame_mod M M' [(C, 32%Z)] -> frame_mod mem M' (RSFU sp C cs).
  Proof.
    intros M' Hf. clear Hcsv HFK TRK HDC HDS HSC Hro Hszk Hk.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply frame_mod_trans_same.
    - eapply frame_mod_of_covered; [| exact HM]. unfold RSFU.
      destruct (Z.eq_dec (bv_unsigned cs) 0); [apply Forall_nil|].
      destruct Hcs as [?|(X & _)]; [lia|]. destruct X as (X1 & X2 & X3 & X4). solve_covered.
    - eapply frame_mod_of_covered; [| exact Hf]. unfold RSFU. solve_covered.
  Qed.

  Lemma dok_at : forall M', frame_mod M M' [(C, 32%Z)] -> data_ok M' data len bs.
  Proof.
    intros M' Hf. clear Hcsv HFK TRK HSC Hro Hszk Hk.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply data_ok_frame; [exact (frame_total M' Hf) | exact Hdok |].
    unfold RSFU. destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
    destruct Hcs as [?|(X & _ & ? & _)]; [lia|]. destruct X as (? & ? & ? & ?). solve_apart.
  Qed.

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
          replace [(C, 32%Z)] with (regions_denot Ex [(SA (EVar 12) 0, 32%Z)])
            by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl Ex;
                rewrite TR12; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
          apply (frame_mod_mem_denot Ex M0 log [(SA (EVar 12) 0, 32%Z)] HLF); [flats_auto | vm_compute; reflexivity]
        | let H2 := fresh "HMt" in
          pose proof (frame_mod_trans_same _ _ _ _ HMt Hf) as H2; clear HMt Hf EQM HLF; rename H2 into HMt ]
    | EQM : ?M1 = ?M0, HLF : log_flat _ _ |- _ => subst M1; clear HLF
    end.

  (* [comment removed for export] *)
  Ltac ccell HK off H :=
    kread_fact HK (EVar 12) off 4%nat H;
    rewrite TR12 in H; unfold v_addi in H; try rewrite Z.add_0_r in H.

  (* [comment removed for export] *)
  Ltac to_tailK :=
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx _, HR : regs_ok _ _ ?Rx, HF : fregs_ok _ _ _, HMt : frame_mod M ?Mx' [(C, 32%Z)],
      HR0 : id _, HF0 : id _ |- runs_to _ (@mkst _ ?Rx _ ?Mx _) _ =>
        let C0 := fresh "C0" in let C4 := fresh "C4" in let C8 := fresh "C8" in let C12 := fresh "C12" in
        let C16 := fresh "C16" in let C20 := fresh "C20" in let C24 := fresh "C24" in let C28 := fresh "C28" in
        ccell HK 0%Z C0; ccell HK 4%Z C4; ccell HK 8%Z C8; ccell HK 12%Z C12;
        ccell HK 16%Z C16; ccell HK 20%Z C20; ccell HK 24%Z C24; ccell HK 28%Z C28;
        let Tcs := fresh "Tcs" in
        pose proof (fixed_cells Mx HMt) as Tcs;
        unfold id in HR0, HF0;
        eapply (tailK FPI regs mem rom ret data len bs sp buf C cs size _ Rx Mx);
        [ exact Hclassify | exact Hret | exact Hsp | exact HWC | exact HWS | exact Hro | exact HSC | exact Hcs
        | regv HR (1%bv:reg); exact TR1
        | regv HR (12%bv:reg); exact TR12
        | intros r Hr; rewrite <- (TRK r Hr);
          exact (regs_same_on _ _ _ R Rx abi_kept HR0 HR ltac:(vm_compute; reflexivity) r Hr)
        | eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept; intros r Hr;
          exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
        | apply frame_total; exact HMt
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
      split; [regv HR (1%bv:reg); rewrite TR1; reflexivity|];
      unfold id in HR0, HF0;
      split; [ intros r Hr; rewrite <- (TRK r Hr);
               exact (regs_same_on _ _ _ R R2 abi_kept HR0 HR ltac:(vm_compute; reflexivity) r Hr) |];
      split; [ eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept; intros r Hr;
               exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr) |];
      unfold rcurve_post; cbv zeta; cbn [w1_rcurve_d wp1_infoub];
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
        run_fp 300%nat [0x14cd4%Z; 0x148dc%Z] noscr true; fold_frame;
        lazymatch goal with
        | |- runs_to _ (@mkst _ _ (Z_to_bv 64 0x14cd4) _ _) _ => to_tailK
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
        pin_reg HR (14%bv:reg) (ELit kv) by (regv HR (14%bv:reg); rewrite TR14, Hkv; reflexivity);
        let HK2 := fresh "HK" in
        assert (HK2 : know_ok SEGS Ex Mx
                  (KBlob (SA (EVar 10) 0) (ELit L) 1
                   :: KDisj (SA (EVar 12) 0) 32 (SA (EVar 10) 0) L :: kn));
        [ apply know_ok_cons;
          [ eapply (kblob_sub SEGS Ex Mx (EVar 10) buf data len bs off L 1);
            [ cbn; exact TR10 | cbn; rewrite Hkv; reflexivity
            | exact (dok_at Mx HMt)
            | reflexivity | lia | lia | lia ]
          | apply know_ok_cons;
            [ cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl Ex; rewrite TR12, TR10; apply disj_C_buf; lia
            | exact HK ] ]
        | clear HK; rename HK2 into HK ];
        crawl 3%nat
    end.

  Lemma tailP_ok :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x146fc) M rom)
            (RCQU regs mem rom ret FPI data len bs sp buf C cs size).
  Proof.
    pose proof (Hclassify, Hret, Hsp, Hdok, Hsize, Hin, HWC, HCal, HWS, Hro, HDC, HSC, HDS, Hcs, TR1, TR10, TR12, TR14, Hk, Hszk, TRK, HFK, HM, Hcsv) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof (u64_range buf) as Rbuf. pose proof (u64_range data) as Rdata.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof (cb_range k) as Rcb.
    hide HDC. hide HSC. hide HDS. hide Hcs.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [sub bs off 16; sub bs off Lk])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [sub bs off 16; sub bs off Lk])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knPU_ok as HK.
    pose proof (frame_mod_refl M [(C, 32%Z)]) as HMt.
    run_fp 60%nat [0x1476c%Z] noscr true.
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
(* [comment removed for export] *)
Section EntryP.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hclassify : classify_contract SEGS W.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 32) 32.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x10490.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 32)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 32)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word).
  Variable k : Z.
  Hypothesis TR1 : getr R 1 = ret.
  Hypothesis TR10 : getr R 10 = buf.
  Hypothesis TR12 : getr R 12 = C.
  Hypothesis TR13 : getr R 13 = cs.
  Hypothesis TR14 : getr R 14 = Z_to_bv 64 k.
  Hypothesis TR15 : (0 < bv_unsigned (getr R 15))%Z.
  Hypothesis Hk : (0 <= k <= 4)%Z.
  Hypothesis Hszk : (12 + cb k <= size)%Z.
  Hypothesis TRK : forall r, In r abi_kept -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [])) (blobs_ev []).

  Definition knEU : list kentry := [KRange (EVar 15) 1 (2^64 - 1)].

  Lemma knEU_ok : know_ok SEGS E mem knEU.
  Proof.
    clear HFK TRK Hro HDC HDS HSC Hcs Hszk Hk.
    unfold knEU, know_ok. pose proof (u64_range (getr R 15)).
    repeat (apply Forall_cons); [..|apply Forall_nil].
    apply krange_intro; cbn. lia.
  Qed.

  Ltac to_tailP Mx HMf Tcs :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HR0 : id _, HF0 : id _ |- runs_to _ (@mkst ?I ?Rx _ Mx _) _ =>
      unfold id in HR0, HF0;
      eapply (tailP_ok FPI regs mem rom ret data len bs sp buf C cs size Hclassify Hret Hsp Hdok Hsize Hin HWC HCal HWS
                Hro HDC HSC HDS Hcs I Rx Mx k);
      [ regv HR (1%bv:reg); exact TR1
      | regv HR (10%bv:reg); exact TR10
      | regv HR (12%bv:reg); exact TR12
      | regv HR (14%bv:reg); exact TR14
      | exact Hk | exact Hszk
      | intros r Hr; rewrite <- (TRK r Hr); exact (regs_same_on _ _ _ R Rx abi_kept HR0 HR ltac:(vm_compute; reflexivity) r Hr)
      | eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept; intros r Hr;
        exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
      | exact HMf
      | exact Tcs ]
    end.

  Lemma tailP_entry :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x146e8) mem rom)
            (RCQU regs mem rom ret FPI data len bs sp buf C cs size).
  Proof.
    pose proof (Hclassify, Hret, Hsp, Hdok, Hsize, Hin, HWC, HCal, HWS, Hro, HDC, HSC, HDS, Hcs, TR1, TR10, TR12, TR13, TR14, TR15, Hk, Hszk, TRK, HFK) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range cs) as Rcs.
    hide HDC. hide HSC. hide HDS.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knEU_ok as HK.
    destruct (Z.eq_dec (bv_unsigned cs) 0) as [Hcs0 | Hnz].
    - (* [comment removed for export] *)
      add_krange (EVar 13) 0%Z 0%Z by (rewrite TR13; lia).
      run_fp 3%nat [0x146fc%Z] noscr false.
      assert (HMf : frame_mod mem mem (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])) by apply frame_mod_refl.
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS mem (bv_unsigned cs) v) by (intros; lia).
      to_tailP mem HMf Tcs.
    - (* [comment removed for export] *)
      destruct Hcs as [? | (HWcs & Hcsal & Hcs1 & Hcs2 & Hcs3)]; [lia|].
      pose proof HWcs as (X1 & X2 & X3 & X4). hide Hcs1. hide Hcs2. hide Hcs3.
      add_krange (EVar 13) 1%Z (2^64 - 4)%Z by (rewrite TR13; lia).
      lazymatch goal with
      | HK : know_ok _ _ _ ?kn |- _ =>
        let HK2 := fresh "HK" in
        assert (HK2 : know_ok SEGS E mem (KWr (SA (EVar 13) 0) 4 :: KAlign (EVar 13) 4 :: kn));
        [ apply know_ok_cons;
          [ apply (kwr_intro SEGS E mem (EVar 13) cs 0 4); [cbn; exact TR13 | lia | lia | lia |];
            rewrite Z.add_0_r; exact X4
          | apply know_ok_cons; [| exact HK];
            apply kalign_intro; [lia|]; cbn; rewrite TR13; exact Hcsal ]
        | clear HK; rename HK2 into HK ]
      end.
      run_fp 6%nat [0x146fc%Z] noscr true.
      assert (Hf : frame_mod mem M [(cs, 4%Z)]).
      { rewrite EQM.
        replace [(cs, 4%Z)] with (regions_denot E [(SA (EVar 13) 0, 4%Z)])
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E;
              rewrite TR13; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
        apply (frame_mod_mem_denot E mem _ [(SA (EVar 13) 0, 4%Z)] HLF); [flats_auto | vm_compute; reflexivity]. }
      clear EQM HLF.
      assert (HMf : frame_mod mem M (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])).
      { destruct (Z.eq_dec (bv_unsigned cs) 0) as [|_]; [lia|]. exact Hf. }
      kread_fact HK (EVar 13) 0%Z 4%nat Tc. rewrite TR13 in Tc. unfold v_addi in Tc. rewrite ?Z.add_0_r in Tc.
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v)
        by (intros _; eexists; apply cell32_of_word; exact Tc).
      clear Tc Hf.
      to_tailP M HMf Tcs.
  Qed.
End EntryP.
End LibReadCurveUbP.

Module LibReadCurveUbC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibCurveSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibRodata OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibReadCurveLib LibReadCurveUbK.
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

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.
#[local] Abbreviation W := wp1_infoub.

Section TailC.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 32) 32.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x10490.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 32)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 32)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word) (M : word -> option byte).
  Variables (X RAW : word) (vc : Z).
  Hypothesis TR1 : getr R 1 = ret.
  Hypothesis TR10 : getr R 10 = buf.
  Hypothesis TR12 : getr R 12 = C.
  Hypothesis TR14 : getr R 14 = X.
  Hypothesis TR11 : getr R 11 = RAW.
  Hypothesis HXv : (bv_unsigned X mod 2 ^ 32 = vc)%Z.
  Hypothesis HRv : (bv_unsigned RAW = 0 <-> vc = 0)%Z.
  Hypothesis Hvsz : (12 + 2 * vc <= size)%Z.
  Hypothesis TRK : forall r, In r abi_kept -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).
  Hypothesis HM : frame_mod mem M (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)]).
  Hypothesis Hcsv : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v.

  #[local] Abbreviation off := (bv_unsigned buf - bv_unsigned data)%Z.

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ []))
                     (blobs_ev [sub bs off 14]).

  Definition knCU : list kentry :=
    [KRange (EVar 10) 1 (2^47);
     KRange (EVar 12) 0 (2^64 - 32);
     KAlign (EVar 12) 8;
     KWr (SA (EVar 12) 0) 32].

  Lemma knCU_ok : know_ok SEGS E M knCU.
  Proof.
    clear Hcsv HFK TRK Hro HDS HSC HDC Hcs HXv HRv Hvsz.
    unfold knCU. pose proof (u64_range C). pose proof (u64_range buf). pose proof (u64_range data).
    pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite TR10. lia.
    - apply krange_intro; cbn. rewrite TR12. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite TR12. exact HCal.
    - apply (kwr_intro SEGS E M (EVar 12) C 0 32); [cbn; exact TR12 | lia | lia | lia |].
      rewrite Z.add_0_r. eapply frame_mod_store_ok; [exact HM | exact V4].
  Qed.

  Lemma fixed_cells : forall M', frame_mod M M' [(C, 32%Z)] ->
    (bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M' (bv_unsigned cs) v).
  Proof.
    intros M' Hf Hnz. clear HFK TRK HDC HDS Hro HXv HRv Hvsz.
    pose proof (u64_range C). pose proof (u64_range cs).
    destruct (Hcsv Hnz) as [v Hv]. exists v.
    destruct Hcs as [Hc0 | (HWcs & _ & _ & Hcs2 & _)]; [lia|]. destruct HWcs as (X1 & X2 & X3 & X4).
    eapply cell32_frame; [exact Hf | exact Hv | lia | lia | solve_apart].
  Qed.

  Lemma frame_total : forall M', frame_mod M M' [(C, 32%Z)] -> frame_mod mem M' (RSFU sp C cs).
  Proof.
    intros M' Hf. clear Hcsv HFK TRK HDC HDS HSC Hro HXv HRv Hvsz.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply frame_mod_trans_same.
    - eapply frame_mod_of_covered; [| exact HM]. unfold RSFU.
      destruct (Z.eq_dec (bv_unsigned cs) 0); [apply Forall_nil|].
      destruct Hcs as [?|(X0 & _)]; [lia|]. destruct X0 as (X1 & X2 & X3 & X4). solve_covered.
    - eapply frame_mod_of_covered; [| exact Hf]. unfold RSFU. solve_covered.
  Qed.

  Lemma dok_at : forall M', frame_mod M M' [(C, 32%Z)] -> data_ok M' data len bs.
  Proof.
    intros M' Hf. clear Hcsv HFK TRK HSC Hro HXv HRv Hvsz.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWS as (W1 & W2 & W3 & W4).
    eapply data_ok_frame; [exact (frame_total M' Hf) | exact Hdok |].
    unfold RSFU. destruct (Z.eq_dec (bv_unsigned cs) 0); [solve_apart|].
    destruct Hcs as [?|(X0 & _ & ? & _)]; [lia|]. destruct X0 as (? & ? & ? & ?). solve_apart.
  Qed.

  Lemma disj_C_buf : forall L, (0 <= L)%Z -> (bv_unsigned buf + L <= bv_unsigned data + len)%Z ->
    (bv_unsigned C + 0 + 32 <= bv_unsigned buf + 0 \/ bv_unsigned buf + 0 + L <= bv_unsigned C + 0)%Z.
  Proof. intros L HL H. clear Hcs HDS HSC HRv. pose proof Hin as (I1 & I2 & I3). lia. Qed.

  (* [comment removed for export] *)
  Lemma curve_kept : curve_ok SEGS mem data len (bv_unsigned C) -> curve_ok SEGS M data len (bv_unsigned C).
  Proof.
    intros Hc. clear Hcsv HFK TRK HRv HXv Hvsz HDC HDS HSC Hro.
    pose proof (u64_range C). pose proof (u64_range cs).
    pose proof HWC as (V1 & V2 & V3 & V4).
    eapply curve_ok_frame; [exact HM | exact Hc | lia | lia |].
    destruct (Z.eq_dec (bv_unsigned cs) 0); [apply Forall_nil|].
    destruct Hcs as [?|(X0 & _ & _ & ? & _)]; [lia|]. destruct X0 as (? & ? & ? & ?). solve_apart.
  Qed.

  (* [comment removed for export] *)
  Ltac fold_frame :=
    lazymatch goal with
    | EQM : ?M1 = mem_denot ?Ex ?M0 ?log, HLF : log_flat _ _, HMt : frame_mod M ?M0' [(C, 32%Z)] |- _ =>
        let Hf := fresh "Hf" in
        assert (Hf : frame_mod M0 M1 [(C, 32%Z)]);
        [ rewrite EQM;
          replace [(C, 32%Z)] with (regions_denot Ex [(SA (EVar 12) 0, 32%Z)])
            by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl Ex;
                rewrite TR12; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
          apply (frame_mod_mem_denot Ex M0 log [(SA (EVar 12) 0, 32%Z)] HLF); [flats_auto | vm_compute; reflexivity]
        | let H2 := fresh "HMt" in
          pose proof (frame_mod_trans_same _ _ _ _ HMt Hf) as H2; clear HMt Hf EQM HLF; rename H2 into HMt ]
    | EQM : ?M1 = ?M0, HLF : log_flat _ _ |- _ => subst M1; clear HLF
    end.

  (* [comment removed for export] *)
  Ltac ccell HK off H :=
    kread_fact HK (EVar 12) off 4%nat H;
    rewrite TR12 in H; unfold v_addi in H; try rewrite Z.add_0_r in H.

  (* [comment removed for export] *)
  Ltac post_common :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _,
      HMt : frame_mod M ?Mx' [(C, 32%Z)], HR0 : id _, HF0 : id _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite TR1; reflexivity|];
      unfold id in HR0, HF0;
      split; [ intros r Hr; rewrite <- (TRK r Hr);
               exact (regs_same_on _ _ _ R R2 abi_kept HR0 HR ltac:(vm_compute; reflexivity) r Hr) |];
      split; [ eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept; intros r Hr;
               exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr) |];
      unfold rcurve_post; cbv zeta; cbn [w1_rcurve_d wp1_infoub];
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
      let Tcs := fresh "Tcs" in pose proof (fixed_cells M2 HMt) as Tcs;
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
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x148f8) M rom)
            (RCQU regs mem rom ret FPI data len bs sp buf C cs size).
  Proof.
    pose proof (Hret, Hdok, Hsize, Hin, HWC, HCal, HWS, HDC, HDS, Hcs, TR1, TR10, TR12, TR14, TR11, HXv, HRv, Hvsz, TRK, HFK, HM, Hcsv) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof (u64_range buf) as Rbuf. pose proof (u64_range data) as Rdata.
    pose proof (u64_range X) as RX. pose proof (u64_range RAW) as RRAW.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    assert (Hvc0 : (0 <= vc)%Z) by (rewrite <- HXv; apply Z.mod_pos_bound; lia).
    hide HDC. hide HSC. hide HDS. hide Hcs. hide HRv. hide HXv.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [sub bs off 14])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [sub bs off 14])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knCU_ok as HK.
    pose proof (frame_mod_refl M [(C, 32%Z)]) as HMt.
    run_fp 10%nat (@nil Z) noscr true. fold_frame.
    (* [comment removed for export] *)
    branch_case as Hc1.
    - (* [comment removed for export] *)
      br_simpl_in E Hc1. rewrite TR14 in Hc1. rewrite ?Z.mod_small in Hc1 by lia. apply Z.ltb_lt in Hc1.
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
        br_simpl_in E Hc2. rewrite TR14 in Hc2. rewrite ?Z.mod_small in Hc2 by lia. apply Z.ltb_ge in Hc2.
        run_fp 40%nat (@nil Z) noscr true. fold_frame.
        unhide HXv.
        kread_fact HK (EVar 12) 0%Z 4%nat C0. rewrite TR12, TR14 in C0. unfold v_addi in C0. rewrite Z.add_0_r in C0.
        kread_fact HK (EVar 12) 8%Z 8%nat C8. rewrite TR12 in C8. unfold v_addi in C8.
        kread_fact HK (EVar 12) 16%Z 8%nat C16. rewrite TR12, TR10, alu_add_lit in C16. unfold v_addi in C16.
        lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mx _) _ =>
          pose proof (fixed_cells Mx HMt) as Tcs;
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
      br_simpl_in E Hc1. rewrite TR14 in Hc1. rewrite ?Z.mod_small in Hc1 by lia. apply Z.ltb_ge in Hc1.
      run_fp 30%nat (@nil Z) noscr true. fold_frame.
      (* [comment removed for export] *)
      branch_case as Hc3.
      + (* [comment removed for export] *)
        clear Hc3.
        run_fp 40%nat (@nil Z) noscr true. fold_frame. post_small.
      + (* [comment removed for export] *)
        br_simpl_in E Hc3. rewrite TR11 in Hc3.
        assert (Hsz14 : (14 <= size)%Z).
        { unhide HRv. rewrite ?Z.mod_small in Hc3 by lia. apply Z.eqb_neq in Hc3. lia. }
        clear Hc3. hide HRv.
        lazymatch goal with
        | HK : know_ok _ ?Ex ?Mx ?kn |- _ =>
          let HK2 := fresh "HK" in
          assert (HK2 : know_ok SEGS Ex Mx
                    (KBlob (SA (EVar 10) 0) (ELit 14) 0
                     :: KDisj (SA (EVar 12) 0) 32 (SA (EVar 10) 0) 14 :: kn));
          [ apply know_ok_cons;
            [ eapply (kblob_sub SEGS Ex Mx (EVar 10) buf data len bs off 14 0);
              [ cbn; exact TR10 | reflexivity | exact (dok_at Mx HMt) | reflexivity | lia | lia | lia ]
            | apply know_ok_cons;
              [ cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl Ex; rewrite TR12, TR10; apply disj_C_buf; lia
              | exact HK ] ]
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
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hsize : (0 <= size < 2 ^ 32)%Z.
  Hypothesis Hin : inDATA data len (bv_unsigned buf) size.
  Hypothesis HWC : writable SEGS mem (bv_unsigned C) 32.
  Hypothesis HCal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 32) 32.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x10490.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 32)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 32)%Z).
  (* [comment removed for export] *)
  Variables (FPc : FPState) (R : bvmap 5 word).
  Variables (X RAW : word) (vc : Z).
  Hypothesis TR1 : getr R 1 = ret.
  Hypothesis TR10 : getr R 10 = buf.
  Hypothesis TR12 : getr R 12 = C.
  Hypothesis TR13 : getr R 13 = cs.
  Hypothesis TR14 : getr R 14 = X.
  Hypothesis TR11 : getr R 11 = RAW.
  Hypothesis HXv : (bv_unsigned X mod 2 ^ 32 = vc)%Z.
  Hypothesis HRv : (bv_unsigned RAW = 0 <-> vc = 0)%Z.
  Hypothesis Hvsz : (12 + 2 * vc <= size)%Z.
  Hypothesis TRK : forall r, In r abi_kept -> getr R r = getr regs r.
  Hypothesis HFK : fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPc)).

  Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [])) (blobs_ev []).

  Definition knEU : list kentry := [KRange (EVar 10) 1 (2^47)].

  Lemma knEU_ok : know_ok SEGS E mem knEU.
  Proof.
    clear HFK TRK Hro HDC HDS HSC Hcs HXv HRv Hvsz.
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3). pose proof (u64_range data).
    unfold knEU, know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    apply krange_intro; cbn. rewrite TR10. lia.
  Qed.

  Ltac to_tailC Mx HMf Tcs :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HR0 : id _, HF0 : id _ |- runs_to _ (@mkst ?I ?Rx _ Mx _) _ =>
      unfold id in HR0, HF0;
      eapply (tailC_ok FPI regs mem rom ret data len bs sp buf C cs size Hret Hdok Hsize Hin HWC HCal HWS
                HDC HDS Hcs I Rx Mx X RAW vc);
      [ regv HR (1%bv:reg); exact TR1
      | regv HR (10%bv:reg); exact TR10
      | regv HR (12%bv:reg); exact TR12
      | regv HR (14%bv:reg); exact TR14
      | regv HR (11%bv:reg); exact TR11
      | exact HXv | exact HRv | exact Hvsz
      | intros r Hr; rewrite <- (TRK r Hr); exact (regs_same_on _ _ _ R Rx abi_kept HR0 HR ltac:(vm_compute; reflexivity) r Hr)
      | eapply fregs_kept_trans; [exact HFK|]; unfold fregs_kept; intros r Hr;
        exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr)
      | exact HMf
      | exact Tcs ]
    end.

  Lemma tailC_entry :
    runs_to SEGS (mkst (FP:=FPc) R (Z_to_bv 64 0x148e8) mem rom)
            (RCQU regs mem rom ret FPI data len bs sp buf C cs size).
  Proof.
    pose proof (Hret, Hdok, Hsize, Hin, HWC, HCal, HWS, HDC, HDS, Hcs, TR1, TR10, TR12, TR13, TR14, TR11, HXv, HRv, Hvsz, TRK, HFK) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range cs) as Rcs.
    hide HDC. hide HSC. hide HDS. hide HXv. hide HRv.
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof knEU_ok as HK.
    destruct (Z.eq_dec (bv_unsigned cs) 0) as [Hcs0 | Hnz].
    - (* [comment removed for export] *)
      add_krange (EVar 13) 0%Z 0%Z by (rewrite TR13; lia).
      run_fp 3%nat [0x148f8%Z] noscr false.
      assert (HMf : frame_mod mem mem (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])) by apply frame_mod_refl.
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS mem (bv_unsigned cs) v) by (intros; lia).
      to_tailC mem HMf Tcs.
    - (* [comment removed for export] *)
      destruct Hcs as [? | (HWcs & Hcsal & Hcs1 & Hcs2 & Hcs3)]; [lia|].
      pose proof HWcs as (X1 & X2 & X3 & X4). hide Hcs1. hide Hcs2. hide Hcs3.
      add_krange (EVar 13) 1%Z (2^64 - 4)%Z by (rewrite TR13; lia).
      lazymatch goal with
      | HK : know_ok _ _ _ ?kn |- _ =>
        let HK2 := fresh "HK" in
        assert (HK2 : know_ok SEGS E mem (KWr (SA (EVar 13) 0) 4 :: KAlign (EVar 13) 4 :: kn));
        [ apply know_ok_cons;
          [ apply (kwr_intro SEGS E mem (EVar 13) cs 0 4); [cbn; exact TR13 | lia | lia | lia |];
            rewrite Z.add_0_r; exact X4
          | apply know_ok_cons; [| exact HK];
            apply kalign_intro; [lia|]; cbn; rewrite TR13; exact Hcsal ]
        | clear HK; rename HK2 into HK ]
      end.
      run_fp 5%nat [0x148f8%Z] noscr true.
      assert (Hf : frame_mod mem M [(cs, 4%Z)]).
      { rewrite EQM.
        replace [(cs, 4%Z)] with (regions_denot E [(SA (EVar 13) 0, 4%Z)])
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E;
              rewrite TR13; unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
        apply (frame_mod_mem_denot E mem _ [(SA (EVar 13) 0, 4%Z)] HLF); [flats_auto | vm_compute; reflexivity]. }
      clear EQM HLF.
      assert (HMf : frame_mod mem M (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4%Z)])).
      { destruct (Z.eq_dec (bv_unsigned cs) 0) as [|_]; [lia|]. exact Hf. }
      kread_fact HK (EVar 13) 0%Z 4%nat Tc. rewrite TR13 in Tc. unfold v_addi in Tc. rewrite ?Z.add_0_r in Tc.
      assert (Tcs : bv_unsigned cs <> 0%Z -> exists v, cell32 SEGS M (bv_unsigned cs) v)
        by (intros _; eexists; apply cell32_of_word; exact Tc).
      clear Tc Hf.
      to_tailC M HMf Tcs.
  Qed.
End EntryC.
End LibReadCurveUbC.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibWP1Spec LibCurveSpec LibRodata LibBswap LibFPLib LibTagsLib LibTagsCall LibReadCurveLib. Import LibReadCurveUbK. Import LibReadCurveUbP. Import LibReadCurveUbC.
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

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.
#[local] Abbreviation W := wp1_infoub.

Section Main.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret data : word) (len : Z) (bs : list byte) (sp buf C cs : word) (size : Z).
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
  Hypothesis HWS : writable SEGS mem (bv_unsigned sp - 32) 32.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x10490.
  Hypothesis HDC : (bv_unsigned data + len <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned data)%Z.
  Hypothesis HSC : (bv_unsigned sp <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 32)%Z.
  Hypothesis HDS : (bv_unsigned data + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned data)%Z.
  Hypothesis Hcs : (bv_unsigned cs = 0)%Z \/
   (writable SEGS mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0)%Z /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data)%Z /\
    (bv_unsigned C + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned C)%Z /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - 32)%Z).

  #[local] Abbreviation off := (bv_unsigned buf - bv_unsigned data)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ []))
                     (blobs_ev [sub bs off 4; sub bs off 12]).

  Definition kn0 : list kentry :=
    [KImg 0x103ec 0x10490;
     KRange (EVar 10) 1 (2^47);
     KRange (EVar 11) 0 (2^32 - 1);
     KRange (EVar 12) 0 (2^64 - 32)].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using FPI HC HWC Hbuf Hdok Hin Hro Hsize Hsz sp.
    unfold kn0. pose proof (u64_range C). pose proof (u64_range buf). pose proof (u64_range data).
    pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    clear HDC HDS HSC Hcs.
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply kimg_intro; [lia|lia|exact Hro].
    - apply krange_intro; cbn. rewrite Hbuf. lia.
    - apply krange_intro; cbn. rewrite Hsz, u_small by lia. lia.
    - apply krange_intro; cbn. rewrite HC. lia.
  Qed.

  Ltac add_blob L idx Hsz :=
    lazymatch goal with
    | HK : know_ok _ ?Ex ?Mx ?kn |- _ =>
      let HK2 := fresh "HK" in
      assert (HK2 : know_ok SEGS Ex Mx (KBlob (SA (EVar 10) 0) (ELit L) idx :: kn));
      [ apply know_ok_cons; [| exact HK];
        eapply (kblob_sub SEGS Ex Mx (EVar 10) buf data len bs off L idx);
        [ cbn; exact Hbuf | reflexivity | exact Hdok | reflexivity | lia | lia | lia ]
      | clear HK; rename HK2 into HK ]
    end.

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

  (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma exit_frame : frame_mod mem mem (RSFU sp C cs).
  Proof using . apply frame_mod_refl. Qed.

  Ltac post_exit :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _, HR0 : id _, HF0 : id _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      unfold id in HR0, HF0;
      split; [ unfold regs_kept; eapply (regs_same_on _ _ _ regs R2 abi_kept); [exact HR0 | exact HR | vm_compute; reflexivity] |];
      split; [ unfold fregs_kept; eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity] |];
      unfold rcurve_post; cbv zeta; cbn [w1_rcurve_d wp1_infoub];
      split; [ exact exit_frame |];
      exists 0%Z; split; [regv HR (10%bv:reg); reflexivity|];
      split; [left; reflexivity|];
      split; [intros; lia|];
      split; [ intros Hc; exact Hc |];
      intros; lia
    end.

  (* [comment removed for export] *)
  Ltac hand_C Hc3 Hc4 :=
    lazymatch goal with
    | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HR0 : id _, HF0 : id _ |- runs_to _ (@mkst ?I ?Rx _ _ _) _ =>
      unfold id in HR0, HF0;
      eapply (tailC_entry FPI regs mem rom ret data len bs sp buf C cs size Hret Hdok Hsize Hin HWC HCal HWS
                HDC HDS Hcs I Rx (edenot E Xe) (edenot E RAWe) vc);
      [ regv HR (1%bv:reg); exact Hra
      | regv HR (10%bv:reg); exact Hbuf
      | regv HR (12%bv:reg); exact HC
      | regv HR (13%bv:reg); exact Hcs13
      | rewrite (reg_val _ _ _ (14%bv:reg) HR); reflexivity
      | rewrite (reg_val _ _ _ (11%bv:reg) HR); reflexivity
      | apply Xe_low32; exact Hc3
      | apply RAW_zero; exact Hc3
      | let HX11 := fresh "HX11" in
        pose proof (X11e_val Hc3) as HX11; unfold X11e, Xe, RAWe in HX11;
        rewrite branch_taken_Z in Hc4; cbv beta iota in Hc4; rewrite HX11 in Hc4;
        cbn [edenot] in Hc4; ev_simpl_in E Hc4; rewrite Hsz, u_small in Hc4 by lia;
        apply Bool.negb_true_iff in Hc4; apply Z.ltb_ge in Hc4; clear -Hc4; lia
      | intros r Hr; exact (regs_same_on _ _ _ regs Rx abi_kept HR0 HR ltac:(vm_compute; reflexivity) r Hr)
      | unfold fregs_kept; intros r Hr; exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr) ]
    end.

  (* [comment removed for export] *)
  Ltac hand_P Hb9 Hc4 :=
    lazymatch type of Hb9 with _ = ?kv =>
      lazymatch goal with
      | HR : regs_ok _ _ _ |- _ =>
        pin_reg HR (15%bv:reg) (ELit kv) by (regv HR (15%bv:reg); rewrite blob_val_sub_u8w by lia; rewrite Hb9; reflexivity)
      end;
      run_fp 30%nat [0x146e8%Z] noscr false;
      (* [comment removed for export] *)
      let Hc5 := fresh "Hc5" in
      branch_case as Hc5;
      [ run_fp 20%nat (@nil Z) noscr false; post_exit
      | br_simpl_in E Hc5; rewrite Hsz, u_small in Hc5 by lia; rewrite ?Z.mod_small in Hc5 by lia; apply Z.ltb_ge in Hc5;
        lazymatch goal with
        | HR : regs_ok _ ?sr ?Rx, HF : fregs_ok _ _ _, HR0 : id _, HF0 : id _ |- runs_to _ (@mkst ?I ?Rx _ _ _) _ =>
          unfold id in HR0, HF0;
          eapply (tailP_entry FPI regs mem rom ret data len bs sp buf C cs size Hclassify Hret Hsp Hdok Hsize Hin HWC HCal HWS
                    Hro HDC HSC HDS Hcs I Rx kv);
          [ regv HR (1%bv:reg); exact Hra
          | regv HR (10%bv:reg); exact Hbuf
          | regv HR (12%bv:reg); exact HC
          | regv HR (13%bv:reg); exact Hcs13
          | regv HR (14%bv:reg); reflexivity
          | regv HR (15%bv:reg); rewrite u_small by lia; lia
          | lia
          | cbn [cb]; exact Hc5
          | intros r Hr; exact (regs_same_on _ _ _ regs Rx abi_kept HR0 HR ltac:(vm_compute; reflexivity) r Hr)
          | unfold fregs_kept; intros r Hr; exact (fregs_same_on _ _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr) ]
        end ]
    end.

  Lemma main_ok :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x1463c) mem rom)
            (RCQU regs mem rom ret FPI data len bs sp buf C cs size).
  Proof using HC HCal HDC HDS HSC HWC HWS Hbuf Hclassify Hcs Hcs13 Hdok Hin Hra Hret Hro Hsize Hsp Hspal Hsz.
    pose proof (Hclassify, Hra, Hret, Hsp, Hbuf, Hsz, HC, Hcs13, Hdok, Hsize, Hin, HWC, HCal, Hspal, HWS, Hro, HDC, HSC, HDS, Hcs) as HUSE; clear HUSE.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC. pose proof (u64_range cs) as Rcs.
    pose proof (u64_range buf) as Rbuf. pose proof (u64_range data) as Rdata.
    pose proof HWS as (W1 & W2 & W3 & W4). pose proof HWC as (V1 & V2 & V3 & V4).
    pose proof Hdok as (D1 & D2 & D3 & D4 & D5). pose proof Hin as (I1 & I2 & I3).
    hide HDC. hide HSC. hide HDS. hide Hcs.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [sub bs off 4; sub bs off 12])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [sub bs off 4; sub bs off 12])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK.
    (* [comment removed for export] *)
    run_fp 20%nat (@nil Z) noscr false.
    branch_case as Hc1.
    { run_fp 20%nat (@nil Z) noscr false. post_exit. }
    br_simpl_in E Hc1. rewrite Hsz, u_small in Hc1 by lia. rewrite ?Z.mod_small in Hc1 by lia. apply Z.ltb_ge in Hc1.
    add_blob 4%Z 0%nat Hc1.
    (* [comment removed for export] *)
    run_fp 40%nat (@nil Z) noscr false.
    branch_case as Hc2.
    { (* [comment removed for export] *)
      clear Hc2.
      run_fp 10%nat (@nil Z) noscr false.
      branch_case as Hc3.
      { run_fp 20%nat (@nil Z) noscr false. post_exit. }
      br_simpl_in E Hc3. rewrite Hsz, u_small in Hc3 by lia. rewrite ?Z.mod_small in Hc3 by lia. apply Z.ltb_ge in Hc3.
      add_blob 12%Z 1%nat Hc3.
      run_fp 60%nat (@nil Z) noscr false.
      (* [comment removed for export] *)
      branch_case as Hc4.
      2:{ run_fp 20%nat (@nil Z) noscr false. post_exit. }
      hand_C Hc3 Hc4. }
    run_fp 10%nat (@nil Z) noscr false.
    branch_case as Hc3.
    { run_fp 20%nat (@nil Z) noscr false. post_exit. }
    clear Hc2 Hc3.
    (* [comment removed for export] *)
    run_fp 10%nat (@nil Z) noscr false.
    branch_case as Hc4.
    { run_fp 20%nat (@nil Z) noscr false. post_exit. }
    br_simpl_in E Hc4. rewrite Hsz, u_small in Hc4 by lia. rewrite ?Z.mod_small in Hc4 by lia. apply Z.ltb_ge in Hc4.
    add_blob 12%Z 1%nat Hc4.
    (* [comment removed for export] *)
    run_fp 20%nat [0x146a0%Z] noscr false.
    pose proof (bs_byte_range bs (off + 8)) as Rb8. pose proof (bs_byte_range bs (off + 9)) as Rb9.
    assert (Hft : ((bs_byte bs (off + 8) = 0 /\ (bs_byte bs (off + 9) = 0 \/ bs_byte bs (off + 9) = 1 \/ bs_byte bs (off + 9) = 2
                                             \/ bs_byte bs (off + 9) = 3 \/ bs_byte bs (off + 9) = 4))
                   \/ 4 < 256 * bs_byte bs (off + 8) + bs_byte bs (off + 9))%Z) by lia.
    destruct Hft as [[Hb8 Hb9] | Hbig].
    2:{ (* [comment removed for export] *)
        run_fp 40%nat (@nil Z) (dirs [true]) false by (rewrite ?blob_val_sub_u8 by lia; lia).
        post_exit. }
    pin_reg HR (14%bv:reg) (ELit 0) by (regv HR (14%bv:reg); rewrite blob_val_sub_u8w by lia; rewrite Hb8; reflexivity).
    destruct Hb9 as [Hb9 | [Hb9 | [Hb9 | [Hb9 | Hb9]]]].
    all: hand_P Hb9 Hc4.
  Qed.
End Main.

Theorem read_curve_Ub_ok :
  classify_contract SEGS W -> read_curve_contract SEGS W.
Proof.
  intros Hcl data len bs sp buf C cs size FPI regs mem rom ret Hra Hret PRE.
  unfold rcurve_pre in PRE. cbv zeta in PRE. cbn [w1_rcurve_d w1_ro_lo w1_ro_hi wp1_infoub] in PRE.
  destruct PRE as (Hsp & Hbuf & Hsz & HC & Hcs13 & Hdok & Hsize & Hin & HWC & HCal & Hspal & HWS & Hro & HDC & HSC & HDS & Hcs).
  apply runs_to_contract with
    (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
            /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
            /\ rcurve_post SEGS W data len bs sp buf C cs size regs mem FPI' regs' mem').
  exact (main_ok FPI regs mem rom ret data len bs sp buf C cs size Hcl Hra Hret Hsp Hbuf Hsz HC Hcs13
           Hdok Hsize Hin HWC HCal Hspal HWS Hro HDC HSC HDS Hcs).
Qed.
