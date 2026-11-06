(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim Hoare Frame LibDefs LibFPSpec.
From Stdlib Require NArith.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Run.
From LinuxProcessSemantics.Riscv Require Decode DecodeC Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SeqExec StoreOk SymExec PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require FpuFacts FpuGlue.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require SymDriveLB.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)

Module LibEvalCurveS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FpuFacts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FpuGlue.
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

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition eval_curve_kept : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20;
   21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

(* [comment removed for export] *)
Definition eval_curve_pre (data : word) (len : Z) (bs : list byte)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  exists (c t8 t16 : word) (n : Z),
    getr regs 10 = c /\ (bv_unsigned c + 24 <= 2 ^ 64)%Z /\
    cell32 SEGS mem (bv_unsigned c) n /\ cell64 SEGS mem (bv_unsigned c + 8) t8 /\ cell64 SEGS mem (bv_unsigned c + 16) t16 /\
    (2 <= n <= 2 ^ 24)%Z /\
    (bv_unsigned t8 <> 0%Z -> inDATA data len (bv_unsigned t8) n) /\
    (bv_unsigned t16 <> 0%Z -> inDATA data len (bv_unsigned t16) (2 * n)) /\
    (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z) /\
    data_ok mem data len bs /\ rodata_clear mem 0x103ec 0x1044c.

Definition eval_curve_post (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  mem' = mem /\ regs_kept eval_curve_kept regs regs'.

Definition eval_curve_S1_contract : Prop :=
  forall data len bs, fn_contract SEGS 0x136d8 (eval_curve_pre data len bs) eval_curve_post.

Section Proof.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret c data t8 t16 : word) (n len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hc : getr regs 10 = c.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hc24 : (bv_unsigned c + 24 <= 2 ^ 64)%Z.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdata : (bv_unsigned data + len < 2 ^ 64)%Z.
  Hypothesis Hblob : forall i, (0 <= i < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  Hypothesis Hro : forall i, (0x103ec <= i < 0x1044c)%Z -> mem (Z_to_bv 64 i) = None.
  Hypothesis Hnr : (2 <= n <= 2 ^ 24)%Z.
  Hypothesis H8 : (bv_unsigned t8 <> 0%Z -> bv_unsigned data <= bv_unsigned t8 /\ bv_unsigned t8 + n <= bv_unsigned data + len)%Z.
  Hypothesis H16 : (bv_unsigned t16 <> 0%Z -> bv_unsigned data <= bv_unsigned t16 /\ bv_unsigned t16 + 2 * n <= bv_unsigned data + len)%Z.
  Hypothesis Hsome : (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 n; t8; t16; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  Definition kn0 : list kentry :=
    [KImg 0x103ec 0x1044c;
     KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 8) 8 (EVar 65); KWord (SA (EVar 10) 16) 8 (EVar 66);
     KBlobD (SA (EVar 67) 0) (EVar 68) 0].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof.
    unfold kn0. pose proof (u64_range c). pose proof (u64_range data).
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    - apply kimg_intro; [lia|lia|exact Hro].
    - eapply (kword_intro SEGS E mem (EVar 10) c 0 4 (EVar 64) (Z_to_bv 64 n)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 8 8 (EVar 65) t8); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 16 8 (EVar 66) t16); cbn; try lia; auto.
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros i Hi. rewrite Z.add_0_r. apply Hblob. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Definition wN1 : word := alu64 ALU_ADD (Z_to_bv 64 n) (Z_to_bv 64 (-1)).
  Definition w1  : word := fmv_fx_res FMT_S (Z_to_bv 64 1065353216).
  Definition w0  : word := fmv_fx_res FMT_S (Z_to_bv 64 0).
  Definition wix (wc : word) : word := fari_res F_MUL FMT_S RNE wc (fcvt_if_res FMT_S false 32 RNE wN1).
  Definition wp (wc : word) : word :=
    alu64 ALU_ADD (ext_val true 0 4 (fari_res F_ADD FMT_S RNE (wix wc) w1)) (Z_to_bv 64 (-1)).

  Lemma wN1_val : bv_unsigned wN1 = (n - 1)%Z.
  Proof.
    unfold wN1. rewrite alu_add. unfold v_add. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small n) by lia.
    change ((-1) mod 2 ^ 64)%Z with (2^64 - 1)%Z.
    replace (n + (2 ^ 64 - 1))%Z with ((n - 1) + 1 * 2^64)%Z by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  Lemma index_facts (b : bool) (wc : word) :
    fcmp_bool F_LT FMT_S (fminmax_res F_MIN FMT_S (reg_get (fp_regs (FPState:=FPI)) 10) w1) w0 = b ->
    wc = (if b then w0 else fsgnj_res F_SGNJ FMT_S (fminmax_res F_MIN FMT_S (reg_get (fp_regs (FPState:=FPI)) 10) w1)
                                                (fminmax_res F_MIN FMT_S (reg_get (fp_regs (FPState:=FPI)) 10) w1)) ->
    (0 <= bv_unsigned (fcvt_fi_res FMT_S true 32 RTZ (wix wc)) <= n - 1)%Z /\
    (0 <= bv_unsigned (fcvt_fi_res FMT_S true 32 RTZ (fmv_fx_res FMT_S (wp wc))) <= n - 1)%Z.
  Proof.
    intros Hb Hwc.
    assert (Hm : (1 <= n - 1 <= 2^24 - 1)%Z) by lia.
    assert (Hw1 : fval FMT_S w1 = 0x3f800000%Z) by (unfold w1; rewrite fval_fmv_fx_S; reflexivity).
    assert (Hw0 : fval FMT_S w0 = 0%Z) by (unfold w0; rewrite fval_fmv_fx_S; reflexivity).
    (* [comment removed for export] *)
    pose proof (ec_xs_val (reg_get (fp_regs (FPState:=FPI)) 10) wN1 w1 w0 (n-1) Hm wN1_val Hw1 Hw0) as XS.
    assert (Hp : bv_unsigned (wp wc) =
                 (bv_unsigned (ec_xs (reg_get (fp_regs (FPState:=FPI)) 10) wN1 w1 w0) - 1)%Z).
    { unfold wp. rewrite alu_add. unfold v_add. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
      rewrite <- fmv_xf_s_ext.
      assert (Ewc : wc = ec_c (reg_get (fp_regs (FPState:=FPI)) 10) w1 w0).
      { unfold ec_c, ec_b, ec_t. rewrite Hb. exact Hwc. }
      rewrite Ewc. unfold wix. fold (ec_F wN1). 
      change (fari_res F_MUL FMT_S RNE (ec_c (reg_get fp_regs 10) w1 w0) (ec_F wN1)) with (ec_ix (reg_get (fp_regs (FPState:=FPI)) 10) wN1 w1 w0).
      change (fari_res F_ADD FMT_S RNE (ec_ix (reg_get fp_regs 10) wN1 w1 w0) w1) with (ec_s (reg_get (fp_regs (FPState:=FPI)) 10) wN1 w1 w0).
      change (fmv_xf_res FMT_S (ec_s (reg_get fp_regs 10) wN1 w1 w0)) with (ec_xs (reg_get (fp_regs (FPState:=FPI)) 10) wN1 w1 w0).
      destruct XS as (_ & U & R). rewrite U.
      rewrite Z_to_bv_unsigned, bv_wrap64_mod. change ((-1) mod 2 ^ 64)%Z with (2^64 - 1)%Z.
      replace (_ + (2 ^ 64 - 1))%Z with ((bv_unsigned (ec_xs (reg_get fp_regs 10) wN1 w1 w0) - 1) + 1 * 2^64)%Z by lia.
      rewrite Z.mod_add by lia. rewrite U. apply Z.mod_small. lia. }
    pose proof (eval_curve_word_ranges (reg_get (fp_regs (FPState:=FPI)) 10) wN1 w1 w0 (n-1) Hm wN1_val Hw1 Hw0
                  (wp wc) Hp b wc Hb Hwc) as F.
    cbv zeta in F. destruct F as (A & _ & _ & C).
    unfold wix. split; [exact A | exact C].
  Qed.

  Ltac post :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?FPI ?R _ ?M _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E _ R, HF : fregs_ok _ _ (@fp_regs FPI), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr) |- _ =>
        exists FPI, R, M; split; [| split; [reflexivity | split; [|split]]]; unfold regs_kept, fregs_kept;
        [ regv HR (1%bv:reg); rewrite_getr; reflexivity
        | eapply (regs_same_on E sr0 _ regs R abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
        | eapply (fregs_same_on E sfr0 _ fr _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ]
        | eapply (regs_same_on E sr0 _ regs R eval_curve_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ] ]
      end
    end.

  Theorem eval_curve_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x136d8) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ mem' = mem
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ regs_kept eval_curve_kept regs regs'.
  Proof.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => mem' = mem /\ regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\ regs_kept eval_curve_kept regs regs').
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range t8). pose proof (u64_range t16). pose proof (u64_range data).
    assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 2 (2^24))).
    { apply krange_intro; cbn; rewrite u_small by lia; lia. }
    assert (HK : know_ok SEGS E mem (KRange (EVar 64) 2 (2^24) :: kn0)).
    { constructor; [exact K64| apply kn0_ok]. }
    (* [comment removed for export] *)
    assert (Kcase : forall (i : nat) (t : word) (z : {bv_unsigned t = 0%Z} + {bv_unsigned t <> 0%Z}),
              edenot E (EVar i) = t ->
              kentry_ok SEGS E mem (if z then KRange (EVar i) 0 0 else KRange (EVar i) 1 (2^64 - 1))).
    { intros i t z Hi. pose proof (u64_range t). destruct z; apply krange_intro; rewrite Hi; lia. }
    pose proof (Kcase 65%nat t8 (Z.eq_dec (bv_unsigned t8) 0) eq_refl) as K65. clear Kcase.
    destruct (Z.eq_dec (bv_unsigned t8) 0) as [Ht8z | Ht8nz];
      [ assert (bv_unsigned t16 <> 0%Z) as Ht16nz by lia; specialize (H16 Ht16nz)
      | specialize (H8 Ht8nz) ];
      (eassert (HK' : know_ok SEGS E mem (_ :: KRange (EVar 64) 2 (2^24) :: kn0)) by (constructor; [exact K65| exact HK]));
      clear HK K65; rename HK' into HK.
    - (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr false.
      branch_case as Hb; br_simpl_in E Hb;
        [ pose proof (index_facts true w0 Hb eq_refl) as [HLO HHI]
        | pose proof (index_facts false _ Hb eq_refl) as [HLO HHI] ];
        unfold wp in HLO, HHI; unfold wix in HLO, HHI; unfold wN1, w1, w0 in HLO, HHI;
        run_fp 100%nat (@nil Z) noscr false; fin_ret; post.
    - (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr false.
      branch_case as Hb; br_simpl_in E Hb;
        [ pose proof (index_facts true w0 Hb eq_refl) as [HLO HHI]
        | pose proof (index_facts false _ Hb eq_refl) as [HLO HHI] ];
        unfold wp in HLO, HHI; unfold wix in HLO, HHI; unfold wN1, w1, w0 in HLO, HHI;
        run_fp 100%nat (@nil Z) noscr false; fin_ret; post.
  Qed.

End Proof.

Theorem eval_curve_S1_ok : eval_curve_S1_contract.
Proof.
  intros data len bs FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (c & t8 & t16 & n & Hc & Hc24 & [Hn32 Hn] & H8c & H16c & Hnr & H8 & H16 & Hsome & (Hlen & Hbs & Hdnz & Hdata & Hblob) & Hro).
  unfold inDATA in H8, H16. unfold cell64, cell in H8c, H16c. unfold cell in Hn.
  destruct (eval_curve_ok FPI regs mem rom ret c data t8 t16 n len bs Hra Hret Hc
              ltac:(rewrite Z.add_0_r; exact Hn) H8c H16c Hc24 Hlen Hbs ltac:(lia) Hblob Hro Hnr
              ltac:(intros Hz; destruct (H8 Hz) as (A & _ & B); split; [exact A|exact B])
              ltac:(intros Hz; destruct (H16 Hz) as (A & _ & B); split; [exact A|exact B]) Hsome)
    as (FPI' & regs' & mem' & Hms & Hmem & Hk1 & Hk2 & Hk3).
  exists FPI', regs', mem'. unfold eval_curve_post. auto.
Qed.
End LibEvalCurveS1.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs LibFPSpec. Import LibEvalCurveS1.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Theorem eval_curve_src1 : eval_curve_contract Plain.M.loaded_segments wp3_src1.
Proof.
  intros data len bs FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (c & t8 & t16 & n & Hc & Hal & Hc24 & (Hn & H8c & H16c & Hnr & H8 & H16 & Hsome) & Hd & Hro).
  destruct (eval_curve_S1_ok data len bs FPI regs mem rom ret Hra Hret) as (FPI' & regs' & mem' & Hms & K1 & K2 & [Hmem _]).
  { exists c, t8, t16, n. repeat (split; [assumption|]).
    intros i Hi. apply Hro. cbn in Hi |- *. lia. }
  exists FPI', regs', mem'. repeat (split; [assumption|]). exact Hmem.
Qed.
