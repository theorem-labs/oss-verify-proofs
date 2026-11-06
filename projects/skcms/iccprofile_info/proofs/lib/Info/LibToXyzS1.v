(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibTagsSpec LibTagsLib LibTagsCall.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require SymDriveLB.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)

Module LibTagXyzS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib.
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

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

Section TX.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret T X Y Zc data buf : word) (ty sz len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HT : getr regs 10 = T.
  Hypothesis HX : getr regs 11 = X.
  Hypothesis HY : getr regs 12 = Y.
  Hypothesis HZ : getr regs 13 = Zc.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdnz : (0 < bv_unsigned data)%Z.
  Hypothesis Hdata : (bv_unsigned data + len < 2 ^ 47)%Z.
  Hypothesis Hblob : forall k, (0 <= k < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0)).
  Hypothesis Hty : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 ty)).
  Hypothesis Htyr : (0 <= ty < 2 ^ 32)%Z.
  Hypothesis Hsz : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sz)).
  Hypothesis Hszr : (0 <= sz < 2 ^ 32)%Z.
  Hypothesis Hbuf : rdn SEGS mem (Z_to_bv 64 (bv_unsigned T + 16)) 8 = Some (word_to_le_bytes 8 buf).
  Hypothesis Hin1 : (bv_unsigned data <= bv_unsigned buf)%Z.
  Hypothesis Hin2 : (bv_unsigned buf + sz <= bv_unsigned data + len)%Z.
  Hypothesis Ht24 : (bv_unsigned T + 24 <= 2 ^ 64)%Z.
  Hypothesis HXst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned X)) (Z.to_nat 4) = true.
  Hypothesis HX0 : (0 < bv_unsigned X)%Z.
  Hypothesis HX4 : (bv_unsigned X + 4 <= 2 ^ 64)%Z.
  Hypothesis HXD : (bv_unsigned data + len <= bv_unsigned X \/ bv_unsigned X + 4 <= bv_unsigned data)%Z.
  Hypothesis HYst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned Y)) (Z.to_nat 4) = true.
  Hypothesis HY0 : (0 < bv_unsigned Y)%Z.
  Hypothesis HY4 : (bv_unsigned Y + 4 <= 2 ^ 64)%Z.
  Hypothesis HYD : (bv_unsigned data + len <= bv_unsigned Y \/ bv_unsigned Y + 4 <= bv_unsigned data)%Z.
  Hypothesis HZst : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned Zc)) (Z.to_nat 4) = true.
  Hypothesis HZ0 : (0 < bv_unsigned Zc)%Z.
  Hypothesis HZ4 : (bv_unsigned Zc + 4 <= 2 ^ 64)%Z.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [buf; Z_to_bv 64 ty; Z_to_bv 64 sz; Z_to_bv 64 len; data])) (blobs_ev [bs]).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition kn0 : list kentry :=
    [KRange (EVar 10) 0 (2^64 - 24);
     KRange (EVar 11) 1 (2^64 - 4);
     KRange (EVar 12) 1 (2^64 - 4);
     KRange (EVar 13) 1 (2^64 - 4);
     KRange (EVar 64) 1 (2^47);
     KRange (EVar 68) 1 (2^47);
     KWord (SA (EVar 10) 4) 4 (EVar 65);
     KWord (SA (EVar 10) 8) 4 (EVar 66);
     KWord (SA (EVar 10) 16) 8 (EVar 64);
     KWr (SA (EVar 11) 0) 4;
     KWr (SA (EVar 12) 0) 4;
     KWr (SA (EVar 13) 0) 4;
     KBlobD (SA (EVar 68) 0) (EVar 67) 0].

  Lemma kblob_ok : kentry_ok SEGS E mem (KBlobD (SA (EVar 68) 0) (EVar 67) 0).
  Proof using FPI Hblob Hbs Hdata Hdnz Hlen Hszr Htyr buf regs rom.
    pose proof (u64_range data).
    cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
    split; [lia|]. split; [exact Hbs|]. intros k Hk. rewrite Z.add_0_r. apply Hblob. exact Hk.
  Qed.

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using FPI HT HX HX0 HX4 HXst HY HY0 HY4 HYst HZ HZ0 HZ4 HZst Hblob Hbs Hbuf Hdata Hdnz Hin1 Hin2 Hlen Hsz Hszr Ht24 Hty Htyr rom.
    unfold kn0. pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range buf).
    pose proof (u64_range X). pose proof (u64_range Y). pose proof (u64_range Zc).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite HT. lia.
    - apply krange_intro; cbn. rewrite HX. lia.
    - apply krange_intro; cbn. rewrite HY. lia.
    - apply krange_intro; cbn. rewrite HZ. lia.
    - apply krange_intro; cbn. lia.
    - apply krange_intro; cbn. lia.
    - eapply (kword_intro SEGS E mem (EVar 10) T 4 4 (EVar 65) (Z_to_bv 64 ty)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) T 8 4 (EVar 66) (Z_to_bv 64 sz)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) T 16 8 (EVar 64) buf); cbn; try lia; auto.
    - apply (kwr_intro SEGS E mem (EVar 11) X 0 4); cbn; try lia. exact HX. rewrite Z.add_0_r. exact HXst.
    - apply (kwr_intro SEGS E mem (EVar 12) Y 0 4); cbn; try lia. exact HY. rewrite Z.add_0_r. exact HYst.
    - apply (kwr_intro SEGS E mem (EVar 13) Zc 0 4); cbn; try lia. exact HZ. rewrite Z.add_0_r. exact HZst.
    - apply kblob_ok.
  Qed.

  (* [comment removed for export] *)
  Definition knA : list kentry :=
    KRange (EVar 66) 20 (2^26) ::
    KDisj (SA (EVar 11) 0) 4 (SA (EVar 64) 8) 12 ::
    KDisj (SA (EVar 12) 0) 4 (SA (EVar 64) 8) 12 :: kn0.
  Definition knB : list kentry := KRange (EVar 66) 0 19 :: kn0.

  Lemma knA_ok : (20 <= sz)%Z -> know_ok SEGS E mem knA.
  Proof using FPI HT HX HX0 HX4 HXD HXst HY HY0 HY4 HYD HYst HZ HZ0 HZ4 HZst Hblob Hbs Hbuf Hdata Hdnz Hin1 Hin2 Hlen Hsz Hszr Ht24 Hty Htyr rom.
    intros Hc. pose proof (u64_range buf).
    apply know_ok_cons; [| apply know_ok_cons; [| apply know_ok_cons; [| apply kn0_ok]]].
    - apply krange_intro; cbn. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HX. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite HY. lia.
  Qed.

  Lemma knB_ok : (sz < 20)%Z -> know_ok SEGS E mem knB.
  Proof using FPI HT HX HX0 HX4 HXst HY HY0 HY4 HYst HZ HZ0 HZ4 HZst Hblob Hbs Hbuf Hdata Hdnz Hin1 Hin2 Hlen Hsz Hszr Ht24 Hty Htyr rom.
    intros Hc. apply know_ok_cons; [| apply kn0_ok].
    apply krange_intro; cbn. rewrite u_small by lia. lia.
  Qed.

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' [(X, 4%Z); (Y, 4%Z); (Zc, 4%Z)] /\
    exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z.

  Definition RS : list (saddr * Z) := [(SA (EVar 11) 0, 4%Z); (SA (EVar 12) 0, 4%Z); (SA (EVar 13) 0, 4%Z)].

  Lemma RS_denot : regions_denot E RS = [(X, 4%Z); (Y, 4%Z); (Zc, 4%Z)].
  Proof using FPI HX HY HZ bs buf data len sz ty.
    unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite HX, HY, HZ. unfold v_addi. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac finish HR0 HF0 :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      split; [exact (regs_same_on E _ _ regs _ abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|];
      unfold POST; split; [| eexists; split; [regv HR (10%bv:reg); reflexivity | lia]]
    end.

  Lemma tagxyz_run :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x138e8) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST regs' mem').
  Proof using E HT HX HX0 HX4 HXD HXst HY HY0 HY4 HYD HYst HZ HZ0 HZ4 HZst Hblob Hbs Hbuf Hdata Hdnz Hin1 Hin2 Hlen Hra Hret Hsz Hszr Ht24 Hty Htyr.
    pose proof (u64_range data) as Rd. pose proof (u64_range T) as RT. pose proof (u64_range buf) as Rb.
    pose proof (u64_range X) as RX. pose proof (u64_range Y) as RY. pose proof (u64_range Zc) as RZ.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    destruct (Z_lt_le_dec sz 20) as [Hc|Hc].
    - (* [comment removed for export] *)
      pose proof (knB_ok Hc) as HK.
      run_fp 20%nat (@nil Z) noscr false.
      branch_case as Hbr.
      + run_fp 20%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_mod_refl.
      + run_fp 20%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_mod_refl.
    - pose proof (knA_ok Hc) as HK.
      run_fp 20%nat (@nil Z) noscr false.
      branch_case as Hbr.
      + run_fp 20%nat (@nil Z) noscr false. finish HR0 HF0. apply frame_mod_refl.
      + run_fp 100%nat (@nil Z) noscr true.
        finish HR0 HF0.
        rewrite EQM, <- RS_denot. apply (frame_mod_mem_denot E _ _ RS HLF); [flats_auto | vm_compute; reflexivity].
  Qed.
End TX.

Theorem tagxyz_S1_ok : tagxyz_contract SEGS tags_src1.
Proof.
  intros data len bs T X Y Zc FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (HT & HX & HY & HZ & (Hlen & Hbs & Hdnz & Hdata & Hblob) & [ty [Htyr Hty]] &
                   (sz & buf & [Hszr Hsz] & Hbuf & Hsz4 & (Hin1 & _ & Hin2)) & Htal & Ht24 &
                   ((_ & _ & HX4 & HXst) & HXal & HX0 & HXD & HXT) &
                   ((_ & _ & HY4 & HYst) & HYal & HY0 & HYD & HYT) &
                   ((_ & _ & HZ4 & HZst) & HZal & HZ0 & HZD & HZT)).
  unfold cell64, cell in Hbuf. unfold cell in Hty, Hsz.
  destruct (tagxyz_run FPI regs mem rom ret T X Y Zc data buf ty sz len bs Hra Hret HT HX HY HZ
              Hlen Hbs Hdnz Hdata Hblob Hty Htyr Hsz Hszr Hbuf Hin1 Hin2 Ht24
              HXst HX0 HX4 HXD HYst HY0 HY4 HYD HZst HZ0 HZ4)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.
End LibTagXyzS1.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibTagsSpec LibTagsLib LibTagsCall. Import LibTagXyzS1.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require Import SymDriveLB.
From Stdlib Require Import Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
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

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.

Section TO.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp T1 T2 T3 M data : word) (len : Z) (bs : list byte).

  Hypothesis Hxyz : tagxyz_contract SEGS W.
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HT1 : getr regs 10 = T1.
  Hypothesis HT2 : getr regs 11 = T2.
  Hypothesis HT3 : getr regs 12 = T3.
  Hypothesis HM : getr regs 13 = M.
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis HX1 : xtag_ok SEGS W mem data len sp (bv_unsigned M) T1.
  Hypothesis HX2 : xtag_ok SEGS W mem data len sp (bv_unsigned M) T2.
  Hypothesis HX3 : xtag_ok SEGS W mem data len sp (bv_unsigned M) T3.
  Hypothesis HW : writable SEGS mem (bv_unsigned M) 36.
  Hypothesis HMal : (bv_unsigned M mod 4 = 0)%Z.
  Hypothesis HM0 : (0 < bv_unsigned M)%Z.
  Hypothesis HWsp : writable SEGS mem (bv_unsigned sp - 32) 32.
  Hypothesis HDM : (bv_unsigned data + len <= bv_unsigned M \/ bv_unsigned M + 36 <= bv_unsigned data)%Z.
  Hypothesis HspM : (bv_unsigned sp <= bv_unsigned M \/ bv_unsigned M + 36 <= bv_unsigned sp - 32)%Z.
  Hypothesis HDsp : (bv_unsigned data + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned data)%Z.

  Definition BIG : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z); (M, 36%Z)].

  (* [comment removed for export] *)
  Lemma pre_at : forall Mx (FP : FPState) R T (o1 o2 o3 : Z),
    frame_mod mem Mx BIG ->
    xtag_ok SEGS W mem data len sp (bv_unsigned M) T ->
    getr R 10 = T ->
    getr R 11 = Z_to_bv 64 (bv_unsigned M + o1) ->
    getr R 12 = Z_to_bv 64 (bv_unsigned M + o2) ->
    getr R 13 = Z_to_bv 64 (bv_unsigned M + o3) ->
    (o1 = 0 \/ o1 = 4 \/ o1 = 8)%Z -> o2 = (o1 + 12)%Z -> o3 = (o1 + 24)%Z ->
    tagxyz_pre SEGS data len bs T (Z_to_bv 64 (bv_unsigned M + o1)) (Z_to_bv 64 (bv_unsigned M + o2))
               (Z_to_bv 64 (bv_unsigned M + o3)) FP R Mx.
  Proof using HDM HDsp HM0 HMal HW HWsp Hdok HspM rom.
    intros Mx FP R T o1 o2 o3 Hf (Hty & Htag & Htal & Ht24 & HTsp & HTM) R10 R11 R12 R13 Ho1 -> ->.
    cbn [t_xyzd50_d tags_src1] in HTsp.
    pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range M). pose proof (u64_range sp).
    destruct Hdok as (D1 & D2 & D3 & D4 & D5). destruct HW as (W1 & W2 & W3 & W4). destruct HWsp as (S1 & S2 & S3 & S4).
    unfold tagxyz_pre. cbv zeta.
    split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split.
    { eapply data_ok_frame; [exact Hf | exact (conj D1 (conj D2 (conj D3 (conj D4 D5)))) | unfold BIG; solve_apart]. }
    split.
    { destruct Hty as [ty Hty]. exists ty. eapply cell32_frame; [exact Hf | exact Hty | lia | lia | unfold BIG; solve_apart]. }
    split.
    { eapply tag_ok_frame; [exact Hf | exact Htag | lia | lia | unfold BIG; solve_apart]. }
    split; [exact Htal|]. split; [exact Ht24|].
    assert (FC : forall o, (0 <= o <= 32)%Z -> (o mod 4 = 0)%Z ->
              fcell_ok SEGS Mx data len (bv_unsigned T) (Z_to_bv 64 (bv_unsigned M + o))).
    { intros o Ho Hom. unfold fcell_ok. cbv zeta. rewrite u_small_frame by lia.
      split.
      { eapply writable_frame; [exact Hf|].
        eapply writable_sub; [exact (conj W1 (conj W2 (conj W3 W4))) | lia | lia | lia]. }
      split; [lia|]. split; [lia|]. split; lia. }
    split; [apply FC; lia|]. split; apply FC; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma post_frame : forall Mx My (o1 o2 o3 : Z),
    (o1 = 0 \/ o1 = 4 \/ o1 = 8)%Z -> o2 = (o1 + 12)%Z -> o3 = (o1 + 24)%Z ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned M + o1), 4%Z); (Z_to_bv 64 (bv_unsigned M + o2), 4%Z);
                     (Z_to_bv 64 (bv_unsigned M + o3), 4%Z)] ->
    frame_mod Mx My BIG.
  Proof using HM0 HMal HW HWsp HspM data rom.
    intros Mx My o1 o2 o3 Ho1 -> -> Hf. pose proof (u64_range M). pose proof (u64_range sp).
    destruct HW as (W1 & W2 & W3 & W4). destruct HWsp as (S1 & S2 & S3 & S4).
    eapply frame_mod_of_covered; [| exact Hf]. unfold BIG. solve_covered.
  Qed.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

  Definition kn0 : list kentry :=
    [KRange (EVar 2) 32 (2^64 - 1);
     KRange (EVar 13) 1 (2^64 - 36);
     KWr (SA (EVar 2) (-32)) 32;
     KDisj (SA (EVar 2) (-32)) 32 (SA (EVar 13) 0) 36].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using FPI HM HM0 HW HWsp Hsp HspM bs data rom.
    unfold kn0. pose proof (u64_range M). pose proof (u64_range sp).
    destruct HWsp as (S1 & S2 & S3 & S4). destruct HW as (W1 & W2 & W3 & W4).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply krange_intro; cbn. rewrite HM. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-32) 32); cbn; try lia. exact Hsp.
      replace (bv_unsigned sp + -32)%Z with (bv_unsigned sp - 32)%Z by lia. exact S4.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp, HM. lia.
  Qed.

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' BIG /\
    exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z.

  (* [comment removed for export] *)
  Ltac call_xyz Tn HXn o1 o2 o3 retw Hf :=
    lazymatch goal with
    | HR : regs_ok _ _ ?R |- runs_to _ (@mkst ?I ?R _ ?Mx ?ro) _ =>
      eapply rt_call;
      [ eapply (Hxyz data len bs Tn _ _ _ I R Mx ro retw);
        [ regv HR (1%bv:reg); rewrite ?Hra; reflexivity
        | first [exact Hret | apply ret_ok_even; rewrite u_small by lia; reflexivity]
        | apply (pre_at Mx I R Tn o1 o2 o3 Hf HXn);
          [ regv HR (10%bv:reg); rewrite_getr; reflexivity
          | regv_lin HR (11%bv:reg); rewrite ?HM; f_equal; lia
          | regv_lin HR (12%bv:reg); rewrite ?HM; f_equal; lia
          | regv_lin HR (13%bv:reg); rewrite ?HM; f_equal; lia
          | lia | reflexivity | reflexivity ] ]
      | cbv beta ]
    end.

  (* [comment removed for export] *)
  Ltac fin0 HR0 HF0 Hf :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      lift_hyp HR0; lift_hyp HF0; unfold regs_kept, fregs_kept;
      split; [eapply (regs_same_on _ _ _ regs R2 abi_kept); [exact HR0 | exact HR | vm_compute; reflexivity]|];
      split; [eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity]|];
      unfold POST; split; [exact Hf | eexists; split; [regv HR (10%bv:reg); reflexivity | lia]]
    end.

  Lemma xyzd50_run :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x1485c) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST regs' mem').
  Proof using E HDM HDsp HM HM0 HMal HT1 HT2 HT3 HW HWsp HX1 HX2 HX3 Hdok Hra Hret Hsp HspM Hxyz.
    pose proof (u64_range data) as Rd. pose proof (u64_range M) as RM. pose proof (u64_range sp) as Rsp.
    pose proof HW as HW'. destruct HW' as (W1 & W2 & W3 & W4). pose proof HWsp as HWsp'. destruct HWsp' as (S1 & S2 & S3 & S4).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK.
    (* [comment removed for export] *)
    run_fp 30%nat [0x138e8%Z] noscr true.
    assert (Hf1 : frame_mod mem M0 BIG).
    { rewrite EQM. eapply frame_mod_of_covered;
        [| apply (frame_mod_mem_denot E mem _ [(SA (EVar 2) (-32), 32%Z)] HLF); [flats_auto | vm_compute; reflexivity]].
      unfold BIG, regions_denot. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp.
      unfold v_addi. solve_covered. }
    clear EQM HLF.
    (* [comment removed for export] *)
    call_xyz T1 HX1 0%Z 12%Z 24%Z (Z_to_bv 64 0x1488c) Hf1.
    intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01).
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
    after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
    know_frame HK Hfr [(SA (EVar 13) 0, 4%Z); (SA (EVar 13) 12, 4%Z); (SA (EVar 13) 24, 4%Z)];
      [rewrite HM; reflexivity|].
    pose proof (frame_mod_trans_same _ _ _ _ Hf1 (post_frame _ _ 0 12 24 ltac:(lia) eq_refl eq_refl Hfr)) as Hf2.
    clear Hfr Hf1.
    destruct Hr01 as [-> | ->].
    { add_krange (EVar 74) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      run_fp 30%nat [0x138e8%Z] noscr false.
      fin0 HR0 HF0 Hf2. }
    add_krange (EVar 74) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
    run_fp 30%nat [0x138e8%Z] noscr false.
    (* [comment removed for export] *)
    call_xyz T2 HX2 4%Z 16%Z 28%Z (Z_to_bv 64 0x148a4) Hf2.
    intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02).
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
    after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
    know_frame HK Hfr [(SA (EVar 13) 4, 4%Z); (SA (EVar 13) 16, 4%Z); (SA (EVar 13) 28, 4%Z)];
      [rewrite HM; reflexivity|].
    pose proof (frame_mod_trans_same _ _ _ _ Hf2 (post_frame _ _ 4 16 28 ltac:(lia) eq_refl eq_refl Hfr)) as Hf3.
    clear Hfr Hf2.
    destruct Hr02 as [-> | ->].
    { add_krange (EVar 138) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      run_fp 30%nat [0x138e8%Z] noscr false.
      fin0 HR0 HF0 Hf3. }
    add_krange (EVar 138) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
    (* [comment removed for export] *)
    run_fp 30%nat [0x138e8%Z] noscr false.
    call_xyz T3 HX3 8%Z 20%Z 32%Z ret Hf3.
    intros FQ3 rq3 mq3 (Hkeep & Hfkeep & Hfr & r3 & Hr3 & Hr03).
    apply runs_to_here.
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2) |- _ =>
      exists FQ3, rq3, mq3;
      split; [reflexivity|];
      lift_hyp HR0; lift_hyp HF0; unfold regs_kept, fregs_kept in *;
      split; [intros r Hin; rewrite (Hkeep r Hin); revert r Hin;
              eapply (regs_same_on _ _ _ regs R2 abi_kept); [exact HR0 | exact HR | vm_compute; reflexivity]|];
      split; [intros r Hin; rewrite (Hfkeep r Hin); revert r Hin;
              eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity]|]
    end.
    unfold POST. split.
    - eapply frame_mod_trans_same; [exact Hf3|]. eapply (post_frame _ _ 8 20 32); [lia|reflexivity|reflexivity|exact Hfr].
    - exists r3. split; [exact Hr3 | exact Hr03].
  Qed.
End TO.

Theorem xyzd50_S1_from_tagxyz : tagxyz_contract SEGS W -> xyzd50_contract SEGS W.
Proof.
  intros Hxyz data len bs sp T1 T2 T3 M FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & HT1 & HT2 & HT3 & HM & Hdok & HX1 & HX2 & HX3 & HW & HMal & HM0 & Hspal & HWsp & HDM & HspM & HDsp).
  cbn [t_xyzd50_d tags_src1] in HWsp, HspM, HDsp.
  destruct (xyzd50_run FPI regs mem rom ret sp T1 T2 T3 M data len bs Hxyz Hra Hret Hsp HT1 HT2 HT3 HM Hdok
              HX1 HX2 HX3 HW HMal HM0 HWsp HDM HspM HDsp)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.

Theorem xyzd50_S1_ok : xyzd50_contract SEGS W.
Proof. exact (xyzd50_S1_from_tagxyz tagxyz_S1_ok). Qed.
