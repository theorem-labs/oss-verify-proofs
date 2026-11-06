(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptRecs LeptArith LeptArith2 LeptNuma LeptEdgeFP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9_code_edC.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac fpn := cbn [fp_regs fp_csr]; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by reg_neq_tac ].

(* [comment removed for export] *)
Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac snez1 F D := sn F D; fixv' (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).

(* [comment removed for export] *)
Local Abbreviation ld8 z := (bv_unsigned (bv_extract 0 64 (le_bytes_to_word (Z_to_le_bytes 8 z)))) (only parsing).
Local Abbreviation ngi_cm v := (bv_unsigned (Z_to_bv 32 (f32i v))) (only parsing).
Local Abbreviation ngi_dm v := (bv_unsigned (Z_to_bv 64 (fst (fp_convert (fp_format FMT_S) (fp_format FMT_D) RNE (ngi_cm v))))) (only parsing).
Local Abbreviation ngi_rm v := (bv_unsigned (Z_to_bv 64 (fst (fpv_fma F_MADD FMT_D RNE (ld8 D_ONE) (ld8 D_HALF) (ngi_dm v))))) (only parsing).

Definition ngi_okm (v : Z) : bool :=
  let r := ngi_rm v in
  negb (fst (fpv_cmp F_LT FMT_S (ngi_cm v) (bv_unsigned (low32 (Z_to_bv 64 0)))))
  && fst (fpv_cmp F_LT FMT_D (ld8 D_LO) r)
  && fst (fpv_cmp F_LT FMT_D r (ld8 D_HI))
  && (bv_unsigned (fpv_x_of_f FMT_D RTZ true 32 r) =? v)%Z.

Lemma ngi_allm : all_upto ngi_okm (Z.to_nat 20000) 0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ngi_tablem : forall v, (0 <= v <= 19999)%Z ->
  fst (fpv_cmp F_LT FMT_S (ngi_cm v) (bv_unsigned (low32 (Z_to_bv 64 0)))) = false /\
  fst (fpv_cmp F_LT FMT_D (ld8 D_LO) (ngi_rm v)) = true /\
  fst (fpv_cmp F_LT FMT_D (ngi_rm v) (ld8 D_HI)) = true /\
  fpv_x_of_f FMT_D RTZ true 32 (ngi_rm v) = Z_to_bv 64 v.
Proof.
  intros v Hv. pose proof (all_upto_spec ngi_okm _ 0%Z ngi_allm v ltac:(rewrite Z2Nat.id; lia)) as H.
  unfold ngi_okm in H. cbv zeta in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  match goal with H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H; rename H into E end.
  match goal with H : negb ?b = true |- _ => destruct b eqn:EN; [discriminate H|] end.
  repeat split; try assumption.
  apply bv_eq. rewrite E. rewrite u_Z2bv by lia. reflexivity.
Qed.

Section Ngi.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  Lemma ngi_run : forall (fx : FPState) regs m (na nalloc n rc arr i pv v : Z) (ret : word),
    frm_zero (@fp_csr fx) ->
    RECat m na (numa_flds nalloc n rc arr) -> (0 <= i < n)%Z -> (n < 2 ^ 31)%Z -> (1 <= na)%Z -> (0x100000 <= pv)%Z -> (pv + 4 < 2 ^ 64)%Z ->
    (1 <= arr)%Z -> (arr + 4 * n < 2 ^ 64)%Z ->
    (pv + 4 <= na \/ na + 32 <= pv)%Z -> (pv + 4 <= arr + 4 * i \/ arr + 4 * i + 4 <= pv)%Z ->
    (pv mod 4 = 0)%Z -> (na mod 8 = 0)%Z -> (arr mod 4 = 0)%Z ->
    (0 <= v <= 19999)%Z ->
    rdn SEGS m (Z_to_bv 64 (arr + 4 * i)) 4 = Some (Z_to_le_bytes 4 (f32i v)) ->
    rdn SEGS m (Z_to_bv 64 0x1c680) 8 = Some (Z_to_le_bytes 8 D_ONE) ->
    rdn SEGS m (Z_to_bv 64 0x1c430) 8 = Some (Z_to_le_bytes 8 D_HALF) ->
    rdn SEGS m (Z_to_bv 64 0x1c478) 8 = Some (Z_to_le_bytes 8 D_LO) ->
    rdn SEGS m (Z_to_bv 64 0x1c348) 8 = Some (Z_to_le_bytes 8 D_HI) ->
    store_ok SEGS m (Z_to_bv 64 pv) 4 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na -> getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 pv ->
    exists fr' cs' regs',
      msteps SEGS (@mkst fx regs (0x61bc0 : word) m rom)
                  (@mkst (mkFP fr' cs') regs' ret (wbytes (wbytes m (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 v))) rom)
      /\ frm_zero cs'
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 13; 14]%list) regs regs'.
  Proof.
    intros fx regs m na nalloc n rc arr i pv v ret Hz R Hi Hn Hna Hpv Hpv64 Harr Harr64 D1 D2 ALpv ALna ALarr Hv RC RT1 RTH RTLO RTHI SOK Hret H1 H10 H11 H12.
    pose proof (NUMA_wf m na nalloc n rc arr R) as (Wna & Wn & Wrc & Warr & Wna0 & Wna64).
    pose proof (NUMA_rd_n SEGS m na nalloc n rc arr R) as Cn. pose proof (NUMA_rd_arr SEGS m na nalloc n rc arr R) as Carr.
    assert (ALc : ((arr + 4 * i) mod 4 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALarr).
    destruct (ngi_tablem v Hv) as (Tneg & Tlo & Thi & Tint). destruct (ngi_table v Hv) as (Tc & _).
    eexists _, _, _. split.
    - stepb_ft F_61b68 D_61b68 ltac:(condZ).
      zand F_61b6c D_61b6c andi_3 ALpv. stepb_ft F_61b70 D_61b70 ltac:(condZ).
      stepST F_61b74 D_61b74 (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
      stepb_ft F_61b78 D_61b78 ltac:(condZ).
      stepb_ft F_61b7c D_61b7c ltac:(condZ).
      zand F_61b80 D_61b80 andi_7 ALna. stepb_ft F_61b84 D_61b84 ltac:(condZ).
      stepLD F_61b88 D_61b88 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepb_ft F_61b8c D_61b8c ltac:(condZ).
      stepLD F_61b90 D_61b90 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; repeat rdn_peel1; exact Carr) ltac:(apply lez8; lia).
      stepiv F_61b94 D_61b94 (Z_to_bv 64 (4 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_61b98 D_61b98 (Z_to_bv 64 (arr + 4 * i)).
      stepb_ft F_61b9c D_61b9c ltac:(condZ).
      snez1 F_61ba0 D_61ba0.
      seqz0 F_61ba4 D_61ba4.
      sn F_61ba8 D_61ba8.
      stepb_ft F_61bac D_61bac ltac:(condR).
      stepb_ft F_61bb0 D_61bb0 ltac:(condZ).
      zand F_61bb4 D_61bb4 andi_3 ALc. stepb_ft F_61bb8 D_61bb8 ltac:(condZ).
      chain_step; [ reflexivity
                  | eapply fp_step_flw with (a := Z_to_bv 64 (arr + 4 * i)) (bs := Z_to_le_bytes 4 (f32i v)); [exact F_61bbc | reflexivity | exact D_61bbc | gres; imm_norm; addr_tac | repeat rdn_peel1; exact RC]
                  | step_simpl ]; fpn.
      rewrite (fpv_cell_load (f32i v)) by (exact Tc).
      chain_step; [ reflexivity | eapply fp_step_fmv_w_x; [exact F_61bc0 | reflexivity | exact D_61bc0] | step_simpl ]; fpn.
      sn F_61bc4 D_61bc4. sn F_61bc8 D_61bc8. sn F_61bcc D_61bcc.
      chain_step; [ reflexivity
                  | eapply fp_step_fld with (a := Z_to_bv 64 0x1c430) (bs := Z_to_le_bytes 8 D_HALF);
                    [exact F_61bd0 | reflexivity | exact D_61bd0 | gres; imm_norm; addr_tac | repeat rdn_peel1; assumption]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_61bd4 | reflexivity | exact D_61bd4] | step_simpl ]; fpn.
      stepiv F_61bd8 D_61bd8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite Tneg; apply bv_eq; reflexivity).
      stepat F_61bdc D_61bdc (Z_to_bv 64 0x1c680) ltac:(gres; pin; apply bv_eq; reflexivity).
      chain_step; [ reflexivity
                  | eapply fp_step_fld with (a := Z_to_bv 64 0x1c680) (bs := Z_to_le_bytes 8 D_ONE);
                    [exact F_61be0 | reflexivity | exact D_61be0 | gres; imm_norm; addr_tac | repeat rdn_peel1; assumption]
                  | step_simpl ]; fpn.
      sn F_61be4 D_61be4.
      chain_step; [ reflexivity
                  | eapply fp_step_fld with (a := Z_to_bv 64 0x1c478) (bs := Z_to_le_bytes 8 D_LO);
                    [exact F_61be8 | reflexivity | exact D_61be8 | gres; imm_norm; addr_tac | repeat rdn_peel1; assumption]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity
                  | eapply fpv_step_fcvt_f_of_f; [exact F_61bec | reflexivity | exact D_61bec | right; split; reflexivity | left; split; reflexivity
                                                 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity
                  | eapply fpv_step_fma; [exact F_61bf0 | reflexivity | exact D_61bf0 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_61bf4 | reflexivity | exact D_61bf4] | step_simpl ]; fpn.
      rewrite Tlo.
      stepb_ft F_61bf8 D_61bf8 ltac:(condR).
      sn F_61bfc D_61bfc.
      chain_step; [ reflexivity
                  | eapply fp_step_fld with (a := Z_to_bv 64 0x1c348) (bs := Z_to_le_bytes 8 D_HI);
                    [exact F_61c00 | reflexivity | exact D_61c00 | gres; imm_norm; addr_tac | repeat rdn_peel1; assumption]
                  | step_simpl ]; fpn.
      chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_61c04 | reflexivity | exact D_61c04] | step_simpl ]; fpn.
      rewrite Thi.
      stepb_ft F_61c08 D_61c08 ltac:(condR).
      sn F_61c0c D_61c0c.
      chain_step; [ reflexivity
                  | eapply fpv_step_fcvt_x_of_f; [exact F_61c10 | reflexivity | exact D_61c10 | left; repeat split; reflexivity | right; split; reflexivity
                                                 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity]
                  | step_simpl ]; fpn.
      rewrite Tint.
      stepST F_61c14 D_61c14 (Z_to_bv 64 pv) (Z_to_bv 64 v) ltac:(store_ok_peel; exact SOK).
      stepret F_61c18 D_61c18 ret ltac:(exact H1).
      apply mst_refl.
    - split; [cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz|]. repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Ngi.
