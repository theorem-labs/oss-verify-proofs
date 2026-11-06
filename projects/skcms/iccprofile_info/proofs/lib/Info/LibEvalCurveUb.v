(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFPSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import FpuFacts FpuGlue.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require Import SymDriveLB.
From Stdlib Require Import Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma addw_small : forall (x : word) (k s : Z),
  bv_unsigned x = s -> (0 <= s < 2^32)%Z -> (0 <= s + k < 2^31)%Z -> (-2^31 <= k <= 0)%Z ->
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 k))) = Z_to_bv 64 (s + k).
Proof.
  intros x k s Hx Hs Hsk Hk. apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
  change (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 k))) with (low32 x + low32 (Z_to_bv 64 k))%bv.
  rewrite bv_add_unsigned, low32_unsigned, low32_Z_to_bv, Z_to_bv_unsigned, Hx.
  unfold bv_swrap. rewrite !bv_wrap32_mod, !bv_wrap64_mod.
  change (bv_half_modulus 32) with (2^31)%Z. nia.
Qed.


Local Open Scope Z_scope.
Lemma w_sltu : forall x y : word, alu64 ALU_SLTU x y = Z_to_bv 64 (if bv_unsigned x <? bv_unsigned y then 1 else 0).
Proof. intros. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. destruct (bv_unsigned x <? bv_unsigned y); reflexivity. Qed.
Lemma w_slt0 : forall x : word, bv_unsigned x < 2^63 -> alu64 ALU_SLT x (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof.
  intros x Hx. rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite bv_signed_small by lia.
  change (bv_signed (Z_to_bv 64 0)) with 0.
  destruct (Z.ltb_spec (bv_unsigned x) 0); [pose proof (u64_range x); lia| reflexivity].
Qed.
Lemma u_add_mul2 : forall (t off : word), bv_unsigned t + 2 * bv_unsigned off < 2^64 ->
  bv_unsigned (alu64 ALU_ADD t (mul_div M_MUL (Z_to_bv 64 2) off)) = bv_unsigned t + 2 * bv_unsigned off.
Proof.
  intros t off H. pose proof (u64_range t). pose proof (u64_range off).
  rewrite alu_add, m_mul. unfold v_add, v_mul. change (bv_unsigned (Z_to_bv 64 2)) with 2.
  rewrite (u_small (2 * _)) by lia. apply u_small. lia.
Qed.
Lemma u_add_nowrap : forall (t off : word), bv_unsigned t + bv_unsigned off < 2^64 ->
  bv_unsigned (alu64 ALU_ADD t off) = bv_unsigned t + bv_unsigned off.
Proof.
  intros t off H. pose proof (u64_range t). pose proof (u64_range off).
  rewrite alu_add. unfold v_add. apply u_small. lia.
Qed.

(* [comment removed for export] *)
Lemma povn16 : forall (t off : word), 1 <= bv_unsigned t -> bv_unsigned t + 2 * bv_unsigned off < 2^64 ->
  (bv_unsigned (alu64 ALU_SLTU (Z_to_bv 64 0) t) =?
   bv_unsigned (alu64 ALU_SLTU (alu64 ALU_ADD t (mul_div M_MUL (Z_to_bv 64 2) off)) (Z_to_bv 64 1))) = false.
Proof.
  intros t off H1 H2. pose proof (u64_range off).
  rewrite !w_sltu, u_add_mul2 by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  destruct (Z.ltb_spec 0 (bv_unsigned t)); [|lia].
  destruct (Z.ltb_spec (bv_unsigned t + 2 * bv_unsigned off) 1); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma povs16 : forall (t off : word), bv_unsigned t + 2 * bv_unsigned off < 2^64 -> bv_unsigned off < 2^62 ->
  (bv_unsigned (alu64 ALU_XOR (alu64 ALU_XOR
      (alu64 ALU_SLTU (alu64 ALU_ADD t (mul_div M_MUL (Z_to_bv 64 2) off)) t)
      (alu64 ALU_SLT off (Z_to_bv 64 0))) (Z_to_bv 64 1)) =? 0) = false.
Proof.
  intros t off H1 H2. pose proof (u64_range off). pose proof (u64_range t).
  rewrite w_sltu, u_add_mul2, w_slt0 by lia.
  destruct (Z.ltb_spec (bv_unsigned t + 2 * bv_unsigned off) (bv_unsigned t)); [lia|]. reflexivity.
Qed.

Lemma povs8 : forall (t off : word), bv_unsigned t + bv_unsigned off < 2^64 -> bv_unsigned off < 2^63 ->
  (bv_unsigned (alu64 ALU_XOR (alu64 ALU_XOR
      (alu64 ALU_SLTU (alu64 ALU_ADD t off) t)
      (alu64 ALU_SLT off (Z_to_bv 64 0))) (Z_to_bv 64 1)) =? 0) = false.
Proof.
  intros t off H1 H2. pose proof (u64_range off). pose proof (u64_range t).
  rewrite w_sltu, u_add_nowrap, w_slt0 by lia.
  destruct (Z.ltb_spec (bv_unsigned t + bv_unsigned off) (bv_unsigned t)); [lia|]. reflexivity.
Qed.
Local Close Scope Z_scope.

Section Proof.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret c data t8 t16 : word) (n len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hc : getr regs 10 = c.
  Hypothesis Hcal : (bv_unsigned c mod 8 = 0)%Z.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hc24 : (bv_unsigned c + 24 <= 2 ^ 64)%Z.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdata : (bv_unsigned data + len < 2 ^ 64)%Z.
  Hypothesis Hblob : forall i, (0 <= i < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  Hypothesis Hro : forall i, (0x103ec <= i < 0x10490)%Z -> mem (Z_to_bv 64 i) = None.
  Hypothesis Hnr : (2 <= n <= 2 ^ 24)%Z.
  Hypothesis H8 : (bv_unsigned t8 <> 0%Z -> bv_unsigned data <= bv_unsigned t8 /\ bv_unsigned t8 + n <= bv_unsigned data + len)%Z.
  Hypothesis H16 : (bv_unsigned t16 <> 0%Z -> bv_unsigned data <= bv_unsigned t16 /\ bv_unsigned t16 + 2 * n <= bv_unsigned data + len)%Z.
  Hypothesis Hsome : (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 n; t8; t16; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  Definition kn0 : list kentry :=
    [KImg 0x103ec 0x10490; KAlign (EVar 10) 8;
     KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 8) 8 (EVar 65); KWord (SA (EVar 10) 16) 8 (EVar 66);
     KBlobD (SA (EVar 67) 0) (EVar 68) 0].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using FPI Hblob Hbs Hc Hc24 Hcal Hdata Hlen Hn Hro Hsome Ht16 Ht8 rom.
    unfold kn0. pose proof (u64_range c). pose proof (u64_range data).
    constructor; [apply kimg_intro; [lia|lia|exact Hro]|].
    constructor; [apply kalign_intro; [lia | cbn; rewrite Hc; exact Hcal]|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    - eapply (kword_intro SEGS E mem (EVar 10) c 0 4 (EVar 64) (Z_to_bv 64 n)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 8 8 (EVar 65) t8); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 16 8 (EVar 66) t16); cbn; try lia; auto.
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros i Hi. rewrite Z.add_0_r. apply Hblob. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Definition eN1 : expr := EAlu ALU_ADD (EVar 64) (ELit (-1)).
  Definition e1 : expr := EFop1 FO_BoxS (ELit 1065353216).
  Definition e0 : expr := EFop1 FO_BoxS (ELit 0).
  Definition et : expr := EFop2 (FO_Minmax F_MIN FMT_S) (EVar 42) e1.
  Definition ewc (b : bool) : expr := if b then e0 else EFop2 (FO_Sgnj F_SGNJ FMT_S) et et.
  Definition eix (b : bool) : expr := EFop2 (FO_Ari F_MUL FMT_S RNE) (ewc b) (EFop1 (FO_CvtIF FMT_S false 32 RNE) eN1).
  Definition elo (b : bool) : expr := EFop1 (FO_CvtFI FMT_S true 32 RTZ) (eix b).
  Definition es (b : bool) : expr := EFop2 (FO_Ari F_ADD FMT_S RNE) (eix b) e1.
  Definition exs (b : bool) : expr := EExt true 0 4 (es b).
  Definition ep (b : bool) : expr := EAluw ALU_ADD (exs b) (ELit (-1)).
  Definition ehi (b : bool) : expr := EFop1 (FO_CvtFI FMT_S true 32 RTZ) (EFop1 FO_BoxS (ep b)).

  (* [comment removed for export] *)
  Definition wN1 : word := alu64 ALU_ADD (Z_to_bv 64 n) (Z_to_bv 64 (-1)).
  Definition w1  : word := fmv_fx_res FMT_S (Z_to_bv 64 1065353216).
  Definition w0  : word := fmv_fx_res FMT_S (Z_to_bv 64 0).
  Definition wK  : word := fmv_fx_res FMT_S (Z_to_bv 64 3472883713).
  Definition w31 : word := fmv_fx_res FMT_S (Z_to_bv 64 1325400064).
  Definition wt  : word := fminmax_res F_MIN FMT_S (reg_get (fp_regs (FPState:=FPI)) 10) w1.
  Definition wwc (b : bool) : word := if b then w0 else fsgnj_res F_SGNJ FMT_S wt wt.
  Definition wix (wc : word) : word := fari_res F_MUL FMT_S RNE wc (fcvt_if_res FMT_S false 32 RNE wN1).
  Definition wxs (wc : word) : word := ext_val true 0 4 (fari_res F_ADD FMT_S RNE (wix wc) w1).
  Definition wp (wc : word) : word := sext 64 (alu32 ALU_ADD (low32 (wxs wc)) (low32 (Z_to_bv 64 (-1)))).

  Lemma wN1_val : bv_unsigned wN1 = (n - 1)%Z.
  Proof using H16 Hlen Hnr Hsome bs c rom.
    unfold wN1. rewrite alu_add. unfold v_add. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small n) by lia. nia.
  Qed.

  Lemma facts (b : bool) :
    fcmp_bool F_LT FMT_S wt w0 = b ->
    let wc := wwc b in
    (0 <= bv_unsigned (fcvt_fi_res FMT_S true 32 RTZ (wix wc)) <= n - 1)%Z /\
    (0 <= bv_unsigned (fcvt_fi_res FMT_S true 32 RTZ (fmv_fx_res FMT_S (wp wc))) <= n - 1)%Z /\
    fcmp_bool F_LT FMT_S wK (wix wc) = true /\ fcmp_bool F_LT FMT_S (wix wc) w31 = true /\
    fcmp_bool F_LT FMT_S wK (fmv_fx_res FMT_S (wp wc)) = true /\
    fcmp_bool F_LT FMT_S (fmv_fx_res FMT_S (wp wc)) w31 = true /\
    wp wc = Z_to_bv 64 (bv_unsigned (wxs wc) - 1) /\ (1 <= bv_unsigned (wxs wc) < 2 ^ 31)%Z.
  Proof using H16 Hlen Hnr Hsome bs c rom.
    intros Hb. cbv zeta.
    assert (Hm : (1 <= n - 1 <= 2^24 - 1)%Z) by lia.
    assert (Hw1 : fval FMT_S w1 = 0x3f800000%Z) by (unfold w1; rewrite fval_fmv_fx_S; reflexivity).
    assert (Hw0 : fval FMT_S w0 = 0%Z) by (unfold w0; rewrite fval_fmv_fx_S; reflexivity).
    assert (HwK : fval FMT_S wK = 0xcf000001%Z) by (unfold wK; rewrite fval_fmv_fx_S; reflexivity).
    assert (Hw31 : fval FMT_S w31 = 0x4f000000%Z) by (unfold w31; rewrite fval_fmv_fx_S; reflexivity).
    pose (X := reg_get (fp_regs (FPState:=FPI)) 10).
    assert (Hwc : wwc b = (if b then w0 else fsgnj_res F_SGNJ FMT_S (fminmax_res F_MIN FMT_S X w1) (fminmax_res F_MIN FMT_S X w1)))
      by reflexivity.
    pose proof (ec_xs_val X wN1 w1 w0 (n-1) Hm wN1_val Hw1 Hw0) as (XS1 & XS2 & XS3).
    assert (Ewc : wwc b = ec_c X w1 w0).
    { unfold ec_c, ec_b, ec_t. change (fminmax_res F_MIN FMT_S X w1) with wt. rewrite Hb. reflexivity. }
    assert (Exs : wxs (wwc b) = ec_xs X wN1 w1 w0).
    { unfold wxs, wix. rewrite <- fmv_xf_s_ext. rewrite Ewc. reflexivity. }
    assert (Hp : bv_unsigned (wp (wwc b)) = (bv_unsigned (ec_xs X wN1 w1 w0) - 1)%Z).
    { unfold wp. rewrite Exs, XS2.
      rewrite (addw_small (ec_xs X wN1 w1 w0) (-1) _ XS2) by lia. rewrite u_small by lia. lia. }
    pose proof (eval_curve_word_ranges X wN1 w1 w0 (n-1) Hm wN1_val Hw1 Hw0 (wp (wwc b)) Hp b (wwc b) Hb Hwc) as F.
    cbv zeta in F. destruct F as (A & _ & _ & C).
    pose proof (eval_curve_word_checks X wN1 w1 w0 (n-1) Hm wN1_val Hw1 Hw0 (wp (wwc b)) Hp wK w31 HwK Hw31 b (wwc b) Hb Hwc) as G.
    cbv zeta in G. destruct G as (G1 & G2 & G3 & G4).
    split; [exact A|]. split; [exact C|]. split; [exact G1|]. split; [exact G2|].
    split; [exact G3|]. split; [exact G4|]. split.
    - unfold wp. rewrite Exs, XS2. rewrite (addw_small (ec_xs X wN1 w1 w0) (-1) _ XS2) by lia. f_equal; lia.
    - rewrite Exs, XS2. lia.
  Qed.

  Ltac post :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?FPI ?R _ ?M _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E _ R, HF : fregs_ok _ _ (@fp_regs FPI), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr) |- _ =>
        exists FPI, R, M; split; [| split; [|split; [|reflexivity]]]; unfold regs_kept, fregs_kept;
        [ regv HR (1%bv:reg); rewrite_getr; reflexivity
        | eapply (regs_same_on E sr0 _ regs R abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
        | eapply (fregs_same_on E sfr0 _ fr _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ] ]
      end
    end.

  (* [comment removed for export] *)
  Ltac casts C1 C2 C3 C4 HP HXS :=
    first [ rewrite C1; reflexivity | rewrite C2; reflexivity | rewrite C3; reflexivity | rewrite C4; reflexivity
          | rewrite HP, !bv_signed_small by (rewrite ?u_small by lia; lia); rewrite u_small by lia;
            rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity ].

  (* [comment removed for export] *)
  Ltac povs :=
    idtac;
    lazymatch goal with
    | |- context [alu64 ALU_XOR] =>
        lazymatch goal with
        | |- context [mul_div M_MUL] => apply povs16; lia
        | |- _ => apply povs8; lia
        end
    | |- context [alu64 ALU_SLTU] => apply povn16; lia
    | |- (_ =? _)%Z = false => apply (proj2 (Z.eqb_neq _ _)); lia
    end.

  (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Theorem eval_curve_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x138a4) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ mem' = mem.
  Proof using E H16 H8 Hblob Hbs Hc Hc24 Hcal Hdata Hlen Hn Hnr Hra Hret Hro Hsome Ht16 Ht8.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\ mem' = mem).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range t8). pose proof (u64_range t16). pose proof (u64_range data).
    assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 2 (2^24))).
    { apply krange_intro; cbn; rewrite u_small by lia; lia. }
    assert (HK : know_ok SEGS E mem (KRange (EVar 64) 2 (2^24) :: kn0)).
    { constructor; [exact K64| apply kn0_ok]. }
    assert (Kcase : forall (i : nat) (t : word) (z : {bv_unsigned t = 0%Z} + {bv_unsigned t <> 0%Z}),
              edenot E (EVar i) = t ->
              kentry_ok SEGS E mem (if z then KRange (EVar i) 0 0 else KRange (EVar i) 1 (2^64 - 1))).
    { intros i t z Hi. pose proof (u64_range t). destruct z; apply krange_intro; rewrite Hi; lia. }
    pose proof (Kcase 65%nat t8 (Z.eq_dec (bv_unsigned t8) 0) eq_refl) as K65. clear Kcase.
    (* [comment removed for export] *)
    assert (KIX : forall b kn, fcmp_bool F_LT FMT_S wt w0 = b -> know_ok SEGS E mem kn ->
              know_ok SEGS E mem (KRange (elo b) 0 16777215 :: KRange (ehi b) 0 16777215 :: kn)).
    { intros b kn Hb HKb. pose proof (facts b Hb) as (A & B & _). cbv zeta in A, B.
      apply know_ok_cons; [|apply know_ok_cons; [|exact HKb]];
        apply krange_intro; destruct b; cbn [edenot fop1_denot fop2_denot elo ehi eix ewc ep exs es e0 e1 et eN1]; ev_simpl E;
        unfold wp, wxs, wix, wwc, wt, w0, w1, wN1 in A, B; lia. }
    destruct (Z.eq_dec (bv_unsigned t8) 0) as [Ht8z | Ht8nz];
      [ assert (bv_unsigned t16 <> 0%Z) as Ht16nz by lia; pose proof (H16 Ht16nz) as H16'
      | pose proof (H8 Ht8nz) as H8' ];
      (eassert (HK' : know_ok SEGS E mem (_ :: KRange (EVar 64) 2 (2^24) :: kn0)) by (constructor; [exact K65| exact HK]));
      clear HK K65; rename HK' into HK.
    - (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr false.
      branch_case as Hb; br_simpl_in E Hb;
        [ pose proof (facts true Hb) as (HLO & HHI & C1 & C2 & C3 & C4 & HP & HXS);
          apply (KIX true _ Hb) in HK
        | pose proof (facts false Hb) as (HLO & HHI & C1 & C2 & C3 & C4 & HP & HXS);
          apply (KIX false _ Hb) in HK ];
        unfold wp, wxs, wix, wwc, wt, w0, w1, wK, w31, wN1 in HLO, HHI, C1, C2, C3, C4, HP, HXS;
        run_fp 100%nat (@nil Z) (dirs [false;false;false;false;false]) false by (casts C1 C2 C3 C4 HP HXS).
      + run_fp 100%nat (@nil Z) (dirs [false;false;false;false]) false by povs.
        fin_ret. post.
      + run_fp 100%nat (@nil Z) (dirs [false;false;false;false]) false by povs.
        fin_ret. post.
    - (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr false.
      branch_case as Hb; br_simpl_in E Hb;
        [ pose proof (facts true Hb) as (HLO & HHI & C1 & C2 & C3 & C4 & HP & HXS);
          apply (KIX true _ Hb) in HK
        | pose proof (facts false Hb) as (HLO & HHI & C1 & C2 & C3 & C4 & HP & HXS);
          apply (KIX false _ Hb) in HK ];
        unfold wp, wxs, wix, wwc, wt, w0, w1, wK, w31, wN1 in HLO, HHI, C1, C2, C3, C4, HP, HXS;
        run_fp 100%nat (@nil Z) (dirs [false;false;false;false;false]) false by (casts C1 C2 C3 C4 HP HXS).
      + run_fp 100%nat (@nil Z) (dirs [false;false;false;false]) false by povs.
        fin_ret. post.
      + run_fp 100%nat (@nil Z) (dirs [false;false;false;false]) false by povs.
        fin_ret. post.
  Qed.
End Proof.

Theorem eval_curve_infoub : eval_curve_contract SEGS wp3_infoub.
Proof.
  intros data len bs FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (c & t8 & t16 & n & Hc & Hal & Hc24 & ([Hn32 Hn] & H8c & H16c & Hnr & H8 & H16 & Hsome) & (Hlen & Hbs & Hdnz & Hdata & Hblob) & Hro).
  unfold inDATA in H8, H16. unfold cell64, cell in H8c, H16c. unfold cell in Hn.
  destruct (eval_curve_ok FPI regs mem rom ret c data t8 t16 n len bs Hra Hret Hc Hal
              ltac:(rewrite Z.add_0_r; exact Hn) H8c H16c Hc24 Hlen Hbs ltac:(lia) Hblob Hro Hnr
              ltac:(intros Hz; destruct (H8 Hz) as (A & _ & B); split; [exact A|exact B])
              ltac:(intros Hz; destruct (H16 Hz) as (A & _ & B); split; [exact A|exact B]) Hsome)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hmem).
  exists FPI', regs', mem'. unfold eval_curve_post. auto.
Qed.
