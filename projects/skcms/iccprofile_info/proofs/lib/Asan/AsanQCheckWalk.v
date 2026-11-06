(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare WalkTac RefMemcpyLib RefEnframeArith
  AsanRegionPoisoned AsanReadCheck Utf8Lib AsanUtf8Spec AsanUtf8Lib Asan_code_qc.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.
Open Scope bv_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section WithFP1. Context {FP : PropExec.FPState}.
(* [comment removed for export] *)
Definition qc_entry (src : bool) : word := if src then (0x51a74 : word) else (0x51abc : word).
Definition qc_exit (src : bool) : word := if src then (0x51aac : word) else (0x51af4 : word).
Definition qc_rb (src : bool) : bv 5 := if src then 11%bv else 10%bv.
Definition qc_re (src : bool) : bv 5 := if src then 19%bv else 20%bv.
Definition qc_clob (src : bool) (r : bv 5) : bool :=
  (bv_eqb r 13%bv || bv_eqb r 14%bv || bv_eqb r 15%bv || bv_eqb r 16%bv || bv_eqb r 17%bv || bv_eqb r (qc_re src))%bool.

(* [comment removed for export] *)
Lemma ld_any : forall m (a : word) bs,
  rdn SEGS m a 8 = Some bs -> bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros m a bs H. pose proof (rdn_length _ _ _ _ _ H) as Hl.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. pose proof (bytes_le_to_Z_nonneg bs).
  rewrite u_Z2bv; [reflexivity | lia | exact Hb].
Qed.

Lemma rdn1_of_some' : forall (m : word -> option byte) (a : word) b, m a = Some b -> rdn SEGS m a 1 = Some [b].
Proof. intros m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Section QC.
  Variables (mem rom : word -> option byte) (beg en : Z) (kb : byte).
  Hypothesis Hbeg : (1 <= beg)%Z.
  Hypothesis Hbe : (beg <= en - 1)%Z.
  Hypothesis Hen : (en <= 2 ^ 47)%Z.
  Hypothesis C1 : cell mem 0x9eaf0 0xa6bb8.
  Hypothesis C2 : cell mem 0xa6bb8 SB.
  Hypothesis Hw1 : exists bs1, rdn SEGS mem (Z_to_bv 64 ((SB + beg / 8) / 8 * 8)) 8 = Some bs1.
  Hypothesis Hw2 : exists bs2, rdn SEGS mem (Z_to_bv 64 ((SB + (en - 1) / 8) / 8 * 8)) 8 = Some bs2.
  Hypothesis Hz : forall g, (beg / 8 <= g < (en - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
  Hypothesis Hk : rdn SEGS mem (Z_to_bv 64 (SB + (en - 1) / 8)) 1 = Some [kb].
  Hypothesis Hkok : (bv_signed kb = 0 \/ (en - 1) mod 8 < bv_signed kb)%Z.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma qc_arith :
    (0 <= beg < 2 ^ 64)%Z /\ (0 <= en - 1 < 2 ^ 64)%Z
    /\ (0 <= beg / 8)%Z /\ (beg / 8 <= (en - 1) / 8)%Z /\ ((en - 1) / 8 < 2 ^ 44)%Z
    /\ (0 <= (en - 1) mod 8 < 8)%Z
    /\ (0 <= (SB + beg / 8) / 8 * 8 < 2 ^ 64)%Z /\ (0 <= (SB + (en - 1) / 8) / 8 * 8 < 2 ^ 64)%Z.
  Proof. pose proof SB_val. unfold SB. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Section CPS.
  Variables (src : bool) (regs0 : bvmap 5 word).
  Definition AG (regs : bvmap 5 word) : Prop := forall r, qc_clob src r = false -> getr regs r = getr regs0 r.
  Definition QF (P : word) (regs : bvmap 5 word) : Prop :=
    exists regs', msteps SEGS (mkst regs P mem rom) (mkst regs' (qc_exit src) mem rom)
      /\ getr regs' (qc_re src) = Z_to_bv 64 (en - 1) /\ AG regs'.

  Lemma ag_upd : forall regs (rd : bv 5) v, AG regs -> qc_clob src rd = true -> AG (regupd regs rd v).
  Proof.
    intros regs rd v A Hc r Hr. rewrite getr_other; [apply A, Hr|]. intros ->. rewrite Hc in Hr. discriminate Hr.
  Qed.
  Lemma qf_steps : forall (P Q : word) regs regs1,
    msteps SEGS (mkst regs P mem rom) (mkst regs1 Q mem rom) -> QF Q regs1 -> QF P regs.
  Proof.
    intros P Q regs regs1 Hrun (regs' & Hrun' & K). exists regs'. split; [eapply msteps_trans; eassumption | exact K].
  Qed.
  Lemma qf_exit : forall regs, getr regs (qc_re src) = Z_to_bv 64 (en - 1) -> AG regs -> QF (qc_exit src) regs.
  Proof. intros regs H A. exists regs. split; [apply mst_refl | split; assumption]. Qed.
  Lemma qf_branch : forall (P : word) regs w c (rs1 rs2 : reg) (imm : bv 13) (v1 v2 : word),
    fetch_word SEGS P = Some w -> is_ecall w = false ->
    decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = v1 -> getr regs rs2 = v2 ->
    (branch_taken c v1 v2 = true -> QF (btgt P (bv_signed imm)) regs) ->
    (branch_taken c v1 v2 = false -> QF (v_addi P 4) regs) ->
    QF P regs.
  Proof.
    intros P regs w c rs1 rs2 imm v1 v2 Hf He Hd H1 H2 Htk Hft.
    destruct (branch_taken c v1 v2) eqn:Hb.
    - destruct (Htk eq_refl) as (regs' & Hrun & K). exists regs'. split; [|exact K].
      eapply mst_step; [reflexivity | | exact Hrun].
      apply (step_branch_tk_gen SEGS regs P mem rom w c rs1 rs2 imm Hf He Hd). rewrite H1, H2. exact Hb.
    - destruct (Hft eq_refl) as (regs' & Hrun & K). exists regs'. split; [|exact K].
      eapply mst_step; [reflexivity | | exact Hrun].
      apply (step_branch_ft_gen SEGS regs P mem rom w c rs1 rs2 imm Hf He Hd). rewrite H1, H2. exact Hb.
  Qed.
  End CPS.

  Ltac solve_ag := repeat (apply ag_upd; [| reflexivity]); assumption.
  Ltac qrun tac := eapply qf_steps; [ tac; apply mst_refl | ].
  Ltac qbr F D :=
    eapply qf_branch;
    [ exact F | reflexivity | exact D | gres; reflexivity | gres; reflexivity
    | cbn [branch_taken]; rwH; intros ?Hc; wlits | cbn [branch_taken]; rwH; intros ?Hc; wlits ].
  (* [comment removed for export] *)
  Ltac mldc F D vv Hcell :=
    chain_step; [reflexivity
      | eapply step_ld with (v := Z_to_bv 64 vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; rewrite ?v_addi_0, ?v_addi_Z;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of Hcell with cell _ ?c _ =>
              first [ change a with (Z_to_bv 64 c : word) | replace a with (Z_to_bv 64 c : word) by (first [apply bv_eq; reflexivity | f_equal; lia]) ] end end;
          exact Hcell
        | apply bytes_le_to_Z_8 ]
      | step_simpl]; vnorm.
  Ltac mlda F D Hbs :=
    chain_step; [reflexivity
      | eapply step_ld;
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; rewrite ?v_addi_0, ?v_addi_Z;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of Hbs with rdn _ _ ?c _ = _ =>
              first [ constr_eq a c | replace a with c by (f_equal; lia) ] end end;
          exact Hbs
        | exact (ld_any _ _ _ Hbs) ]
      | step_simpl]; vnorm.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition p_d24 (src : bool) : word := if src then (0x51d90 : word) else (0x51e90 : word).
  Lemma blk_d24 : forall src regs0 regs, AG src regs0 regs -> getr regs (qc_re src) = Z_to_bv 64 (en - 1) ->
    getr regs 15 = Z_to_bv 64 0 -> QF src regs0 (p_d24 src) regs.
  Proof.
    intros src regs0 regs A Hre H15. unfold p_d24. destruct src; cbn [qc_re] in *.
    - qrun ltac:(sn F_51d90 D_51d90; pin 0%Z ltac:(rewrite v_andi_Z by lia; reflexivity)).   (* [comment removed for export] *)
      qbr F_51d94 D_51d94; [| exfalso; cbv in Hc; discriminate Hc].                          (* [comment removed for export] *)
      apply qf_exit; [gres; exact Hre | solve_ag].
    - qrun ltac:(sn F_51e90 D_51e90; pin 0%Z ltac:(rewrite v_andi_Z by lia; reflexivity)).   (* [comment removed for export] *)
      qbr F_51e94 D_51e94; [| exfalso; cbv in Hc; discriminate Hc].                          (* [comment removed for export] *)
      apply qf_exit; [gres; exact Hre | solve_ag].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition p_lp (src : bool) : word := if src then (0x51d80 : word) else (0x51e80 : word).
  Lemma blk_loop : forall src regs0 (cnt : nat) regs g, AG src regs0 regs -> getr regs (qc_re src) = Z_to_bv 64 (en - 1) ->
    getr regs 13 = Z_to_bv 64 (SB + g) -> getr regs 14 = Z_to_bv 64 (SB + (en - 1) / 8) ->
    getr regs 15 = Z_to_bv 64 0 -> (beg / 8 <= g < (en - 1) / 8)%Z -> Z.of_nat cnt = ((en - 1) / 8 - g)%Z ->
    QF src regs0 (p_lp src) regs.
  Proof.
    pose proof qc_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof SB_val as HSB.
    intros src regs0 cnt. induction cnt as [|cnt IH]; intros regs g A Hre H13 H14 H15 Hg Hcnt; [lia|].
    pose proof (rdn1_of_some' mem _ _ (Hz g Hg)) as Hb.
    unfold p_lp in *. destruct src; cbn [qc_re] in *.
    - qrun ltac:(
        ldb F_51d80 D_51d80 Hb;                         (* [comment removed for export] *)
        sn F_51d84 D_51d84; pinZ (SB + (g + 1))%Z;      (* [comment removed for export] *)
        sn F_51d88 D_51d88).                            (* [comment removed for export] *)
      qbr F_51d8c D_51d8c.                              (* [comment removed for export] *)
      + condZ. apply (IH _ (g + 1)%Z); [solve_ag | hreg | hreg | hreg | hreg | unfold SB in *; lia | lia].
      + condZ. apply (blk_d24 true); [solve_ag | hreg | hreg].
    - qrun ltac:(
        ldb F_51e80 D_51e80 Hb;                         (* [comment removed for export] *)
        sn F_51e84 D_51e84; pinZ (SB + (g + 1))%Z;      (* [comment removed for export] *)
        sn F_51e88 D_51e88).                            (* [comment removed for export] *)
      qbr F_51e8c D_51e8c.                              (* [comment removed for export] *)
      + condZ. apply (IH _ (g + 1)%Z); [solve_ag | hreg | hreg | hreg | hreg | unfold SB in *; lia | lia].
      + condZ. apply (blk_d24 false); [solve_ag | hreg | hreg].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition p_slow (src : bool) : word := if src then (0x51d64 : word) else (0x51e64 : word).
  Lemma blk_slow : forall src regs0 regs, AG src regs0 regs -> getr regs (qc_re src) = Z_to_bv 64 (en - 1) ->
    getr regs 13 = Z_to_bv 64 (SB + beg / 8) -> getr regs 14 = Z_to_bv 64 (SB + (en - 1) / 8) ->
    QF src regs0 (p_slow src) regs.
  Proof.
    pose proof qc_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof SB_val as HSB.
    intros src regs0 regs A Hre H13 H14. pose proof (sbyte_range kb) as Hkr. unfold sbyte in Hkr.
    unfold p_slow. destruct src; cbn [qc_re] in *.
    - (* [comment removed for export] *)
      qrun ltac:(
        ldbs F_51d64 D_51d64 Hk;                        (* [comment removed for export] *)
        sn F_51d68 D_51d68; pin_andi7 (en - 1)%Z).      (* [comment removed for export] *)
      unfold sbyte in *.
      destruct Hkok as [Hk0 | Hklt].
      + rewrite Hk0.
        qrun ltac:(
          sn F_51d6c D_51d6c;                                      (* [comment removed for export] *)
          sn F_51d70 D_51d70; pin 0%Z ltac:(unfold v_slt, c_lts; rewrite lts_ZZ by lia; decide_cmp; reflexivity);  (* [comment removed for export] *)
          sn F_51d74 D_51d74;                                      (* [comment removed for export] *)
          sn F_51d78 D_51d78).                                     (* [comment removed for export] *)
        qbr F_51d7c D_51d7c.                                       (* [comment removed for export] *)
        * condZ. apply (blk_d24 true); [solve_ag | hreg | hreg].
        * condZ. apply (blk_loop true _ (Z.to_nat ((en - 1) / 8 - beg / 8)) _ (beg / 8)); [solve_ag | hreg | hreg | hreg | hreg | lia | lia].
      + qrun ltac:(
          sn F_51d6c D_51d6c; pin 1%Z ltac:(rewrite v_sltu_val, ltu_ZZ by lia; decide_cmp; reflexivity);   (* [comment removed for export] *)
          sn F_51d70 D_51d70; pin 1%Z ltac:(unfold v_slt, c_lts; rewrite lts_ZZ by lia; decide_cmp; reflexivity);  (* [comment removed for export] *)
          sn F_51d74 D_51d74;                                      (* [comment removed for export] *)
          sn F_51d78 D_51d78).                                     (* [comment removed for export] *)
        qbr F_51d7c D_51d7c.
        * condZ. apply (blk_d24 true); [solve_ag | hreg | hreg].
        * condZ. apply (blk_loop true _ (Z.to_nat ((en - 1) / 8 - beg / 8)) _ (beg / 8)); [solve_ag | hreg | hreg | hreg | hreg | lia | lia].
    - (* [comment removed for export] *)
      qrun ltac:(
        ldbs F_51e64 D_51e64 Hk;                        (* [comment removed for export] *)
        sn F_51e68 D_51e68; pin_andi7 (en - 1)%Z).      (* [comment removed for export] *)
      unfold sbyte in *.
      destruct Hkok as [Hk0 | Hklt].
      + rewrite Hk0.
        qrun ltac:(
          sn F_51e6c D_51e6c;                                      (* [comment removed for export] *)
          sn F_51e70 D_51e70; pin 0%Z ltac:(unfold v_slt, c_lts; rewrite lts_ZZ by lia; decide_cmp; reflexivity);  (* [comment removed for export] *)
          sn F_51e74 D_51e74;                                      (* [comment removed for export] *)
          sn F_51e78 D_51e78).                                     (* [comment removed for export] *)
        qbr F_51e7c D_51e7c.                                       (* [comment removed for export] *)
        * condZ. apply (blk_d24 false); [solve_ag | hreg | hreg].
        * condZ. apply (blk_loop false _ (Z.to_nat ((en - 1) / 8 - beg / 8)) _ (beg / 8)); [solve_ag | hreg | hreg | hreg | hreg | lia | lia].
      + qrun ltac:(
          sn F_51e6c D_51e6c; pin 1%Z ltac:(rewrite v_sltu_val, ltu_ZZ by lia; decide_cmp; reflexivity);   (* [comment removed for export] *)
          sn F_51e70 D_51e70; pin 1%Z ltac:(unfold v_slt, c_lts; rewrite lts_ZZ by lia; decide_cmp; reflexivity);  (* [comment removed for export] *)
          sn F_51e74 D_51e74;                                      (* [comment removed for export] *)
          sn F_51e78 D_51e78).                                     (* [comment removed for export] *)
        qbr F_51e7c D_51e7c.
        * condZ. apply (blk_d24 false); [solve_ag | hreg | hreg].
        * condZ. apply (blk_loop false _ (Z.to_nat ((en - 1) / 8 - beg / 8)) _ (beg / 8)); [solve_ag | hreg | hreg | hreg | hreg | lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem quick_check_cps : forall src regs0, getr regs0 (qc_rb src) = Z_to_bv 64 beg -> getr regs0 (qc_re src) = Z_to_bv 64 en ->
    QF src regs0 (qc_entry src) regs0.
  Proof.
    pose proof qc_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof SB_val as HSB.
    intros src regs0 Hb He. assert (A : AG src regs0 regs0) by (intros r _; reflexivity).
    destruct Hw1 as [bs1 Hbs1]. destruct Hw2 as [bs2 Hbs2].
    unfold qc_entry. destruct src; cbn [qc_rb qc_re] in *.
    - qrun ltac:(
        sn F_51a74 D_51a74;                              (* [comment removed for export] *)
        mldc F_51a78 D_51a78 0xa6bb8%Z C1;              (* [comment removed for export] *)
        mldc F_51a7c D_51a7c SB C2;                      (* [comment removed for export] *)
        sn F_51a80 D_51a80; pinZ (en - 1)%Z;             (* [comment removed for export] *)
        sn F_51a84 D_51a84; pin_srli3 beg;               (* [comment removed for export] *)
        sn F_51a88 D_51a88; pin_srli3 (en - 1)%Z;        (* [comment removed for export] *)
        sn F_51a8c D_51a8c; pinZ (SB + beg / 8)%Z;       (* [comment removed for export] *)
        sn F_51a90 D_51a90; pinZ (SB + (en - 1) / 8)%Z; (* [comment removed for export] *)
        sn F_51a94 D_51a94; pin ((SB + beg / 8) / 8 * 8)%Z ltac:(rewrite v_andi_m8 by lia; reflexivity);        (* [comment removed for export] *)
        sn F_51a98 D_51a98; pin ((SB + (en - 1) / 8) / 8 * 8)%Z ltac:(rewrite v_andi_m8 by lia; reflexivity);  (* [comment removed for export] *)
        mlda F_51a9c D_51a9c Hbs1;                       (* [comment removed for export] *)
        mlda F_51aa0 D_51aa0 Hbs2;                       (* [comment removed for export] *)
        sn F_51aa4 D_51aa4).                             (* [comment removed for export] *)
      qbr F_51aa8 D_51aa8.                               (* [comment removed for export] *)
      + apply (blk_slow true); [solve_ag | hreg | hreg | hreg].
      + apply qf_exit; [hreg | solve_ag].
    - qrun ltac:(
        sn F_51abc D_51abc;                              (* [comment removed for export] *)
        mldc F_51ac0 D_51ac0 0xa6bb8%Z C1;              (* [comment removed for export] *)
        mldc F_51ac4 D_51ac4 SB C2;                      (* [comment removed for export] *)
        sn F_51ac8 D_51ac8; pinZ (en - 1)%Z;             (* [comment removed for export] *)
        sn F_51acc D_51acc; pin_srli3 beg;               (* [comment removed for export] *)
        sn F_51ad0 D_51ad0; pin_srli3 (en - 1)%Z;        (* [comment removed for export] *)
        sn F_51ad4 D_51ad4; pinZ (SB + beg / 8)%Z;       (* [comment removed for export] *)
        sn F_51ad8 D_51ad8; pinZ (SB + (en - 1) / 8)%Z; (* [comment removed for export] *)
        sn F_51adc D_51adc; pin ((SB + beg / 8) / 8 * 8)%Z ltac:(rewrite v_andi_m8 by lia; reflexivity);        (* [comment removed for export] *)
        sn F_51ae0 D_51ae0; pin ((SB + (en - 1) / 8) / 8 * 8)%Z ltac:(rewrite v_andi_m8 by lia; reflexivity);  (* [comment removed for export] *)
        mlda F_51ae4 D_51ae4 Hbs1;                       (* [comment removed for export] *)
        mlda F_51ae8 D_51ae8 Hbs2;                       (* [comment removed for export] *)
        sn F_51aec D_51aec).                             (* [comment removed for export] *)
      qbr F_51af0 D_51af0.                               (* [comment removed for export] *)
      + apply (blk_slow false); [solve_ag | hreg | hreg | hreg].
      + apply qf_exit; [hreg | solve_ag].
  Qed.
End QC.

(* [comment removed for export] *)
Theorem quick_check : forall (src : bool) mem rom (beg en : Z) (regs : bvmap 5 word) (kb : byte),
  (1 <= beg)%Z -> (beg <= en - 1)%Z -> (en <= 2 ^ 47)%Z ->
  getr regs (qc_rb src) = Z_to_bv 64 beg -> getr regs (qc_re src) = Z_to_bv 64 en ->
  cell mem 0x9eaf0 0xa6bb8 -> cell mem 0xa6bb8 SB ->
  (exists bs1, rdn SEGS mem (Z_to_bv 64 ((SB + beg / 8) / 8 * 8)) 8 = Some bs1) ->
  (exists bs2, rdn SEGS mem (Z_to_bv 64 ((SB + (en - 1) / 8) / 8 * 8)) 8 = Some bs2) ->
  (forall g, (beg / 8 <= g < (en - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0)) ->
  rdn SEGS mem (Z_to_bv 64 (SB + (en - 1) / 8)) 1 = Some [kb] ->
  (bv_signed kb = 0 \/ (en - 1) mod 8 < bv_signed kb)%Z ->
  exists regs',
    msteps SEGS (mkst regs (qc_entry src) mem rom) (mkst regs' (qc_exit src) mem rom)
    /\ getr regs' (qc_re src) = Z_to_bv 64 (en - 1)
    /\ (forall r, qc_clob src r = false -> getr regs' r = getr regs r).
Proof.
  intros src mem rom beg en regs kb Hbeg Hbe Hen Hb He C1 C2 Hw1 Hw2 Hz Hk Hkok.
  exact (quick_check_cps mem rom beg en kb Hbeg Hbe Hen C1 C2 Hw1 Hw2 Hz Hk Hkok src regs Hb He).
Qed.
End WithFP1.

