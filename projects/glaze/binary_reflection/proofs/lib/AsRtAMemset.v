(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsRtQC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition qc1f_words (rb : reg) : list (option (bv 32)) :=
  [None; None; Some (if bv_eqb rb 10 then W_6cc5c else W_6cea0); Some W_6cc60;
   Some (if bv_eqb rb 10 then W_6cc64 else W_6cea8); Some W_6cc68; Some W_6cc6c; Some W_6cc70; Some W_6cc74;
   Some W_6cc78; Some W_6cc7c; Some W_6cc80; Some W_6cc84; Some W_6cc88; None]%list.
Definition qc1s_words : list (option (bv 32)) :=
  [Some W_6cda0; Some W_6cda4; Some W_6cda8; Some W_6cdac; Some W_6cdb0; Some W_6cdb4; Some W_6cdb8;
   Some W_6cdbc; Some W_6cdc0; Some W_6cdc4; Some W_6cdc8; Some W_6cdcc; None]%list.

Definition qc1_clob : list reg := [13; 14; 15; 16; 17]%list.

(* [comment removed for export] *)
Definition gbnez (segs : list Segment) (p : word) (r : reg) (tgt : word) : Prop :=
  forall regs mem rom,
    (getr regs r <> Z_to_bv 64 0 -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs tgt mem rom))
    /\ (getr regs r = Z_to_bv 64 0 -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs (v_addi p 4) mem rom)).
Definition gbeqz (segs : list Segment) (p : word) (r : reg) (tgt : word) : Prop :=
  forall regs mem rom,
    (getr regs r = Z_to_bv 64 0 -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs tgt mem rom))
    /\ (getr regs r <> Z_to_bv 64 0 -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs (v_addi p 4) mem rom)).

Lemma gbnez_of : forall segs (p : word) w (r : reg) (imm : bv 13) tgt,
  fetch_word segs p = Some w -> is_ecall w = false -> decode_any w = Some (Branch BC_NE r 0 imm, 4%Z) ->
  btgt p (bv_signed imm) = tgt -> gbnez segs p r tgt.
Proof using.
  intros segs p w r imm tgt F E D T regs mem rom. split; intros Hr.
  - rewrite <- T. eapply step_bne_tk; [exact F | exact E | exact D |].
    unfold getr at 2. rewrite bv_eqb_refl. (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end). apply bv_eqb_neq. exact Hr.
  - eapply step_bne_ft; [exact F | exact E | exact D |].
    unfold getr at 2. rewrite bv_eqb_refl. rewrite Hr. apply c_eq_refl.
Qed.

Lemma gbeqz_of : forall segs (p : word) w (r : reg) (imm : bv 13) tgt,
  fetch_word segs p = Some w -> is_ecall w = false -> decode_any w = Some (Branch BC_EQ r 0 imm, 4%Z) ->
  btgt p (bv_signed imm) = tgt -> gbeqz segs p r tgt.
Proof using.
  intros segs p w r imm tgt F E D T regs mem rom. split; intros Hr.
  - rewrite <- T. eapply step_beq_tk; [exact F | exact E | exact D |].
    unfold getr at 2. rewrite bv_eqb_refl. rewrite Hr. apply c_eq_refl.
  - eapply step_beq_ft; [exact F | exact E | exact D |].
    unfold getr at 2. rewrite bv_eqb_refl. (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end). apply bv_eqb_neq. exact Hr.
Qed.

(* [comment removed for export] *)
Record qc1H (segs : list Segment) (mem : word -> option byte) (b : word) (n : Z) (g_shoff p_shoff : Z)
       (w0 w1 : list byte) (s1 : byte) : Prop := QC1H {
  q_n : (1 <= n)%Z;
  q_end : (U b + n <= 2 ^ 47)%Z;
  q_g : rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (LE8 p_shoff);
  q_p : rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (LE8 0x7fff8000);
  q_gp : (0 <= g_shoff < 2 ^ 64)%Z /\ (0 <= p_shoff < 2 ^ 64)%Z;
  q_w0 : rdn segs mem (Z_to_bv 64 (down8 (Sh (U b)))) 8 = Some w0;          (* [comment removed for export] *)
  q_w1 : rdn segs mem (Z_to_bv 64 (down8 (Sh (U b + n - 1)))) 8 = Some w1;  (* [comment removed for export] *)
  q_s1 : rdn segs mem (Z_to_bv 64 (Sh (U b + n - 1))) 1 = Some [s1];
  q_s1ok : (U s1 = 0 \/ ((U b + n - 1) mod 8 < U s1 /\ U s1 < 128))%Z;
  q_zero : forall a : word, (Sh (U b) <= U a < Sh (U b + n - 1))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0] }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QC1.
  Variable segs : list Segment.
  Variables pF pS pK : word.          (* [comment removed for export] *)
  Variable rb : reg.                  (* [comment removed for export] *)
  Variables g_shoff p_shoff : Z.      (* [comment removed for export] *)
  Hypothesis HF : code_ato segs pF 0 (qc1f_words rb).
  Hypothesis HS : code_ato segs pS 0 qc1s_words.
  Hypothesis G0 : gload segs pF 0 13 g_shoff.
  Hypothesis BNE : gbnez segs (at_ pF 56) 16 pS.
  Hypothesis BEQ : gbeqz segs (at_ pS 48) 13 pK.
  Hypothesis HK : at_ pF 60 = pK.
  Hypothesis Hrb : rb = 10 \/ rb = 11.

  (* [comment removed for export] *)
  Lemma Ff12 : fetch_word segs (at_ pF 12) = Some W_6cc60. Proof using HF rb. exact (code_ato_get segs pF 0 _ 3 _ HF eq_refl). Qed.
  Lemma Ff20 : fetch_word segs (at_ pF 20) = Some W_6cc68. Proof using HF rb. exact (code_ato_get segs pF 0 _ 5 _ HF eq_refl). Qed.
  Lemma Ff24 : fetch_word segs (at_ pF 24) = Some W_6cc6c. Proof using HF rb. exact (code_ato_get segs pF 0 _ 6 _ HF eq_refl). Qed.
  Lemma Ff28 : fetch_word segs (at_ pF 28) = Some W_6cc70. Proof using HF rb. exact (code_ato_get segs pF 0 _ 7 _ HF eq_refl). Qed.
  Lemma Ff32 : fetch_word segs (at_ pF 32) = Some W_6cc74. Proof using HF rb. exact (code_ato_get segs pF 0 _ 8 _ HF eq_refl). Qed.
  Lemma Ff36 : fetch_word segs (at_ pF 36) = Some W_6cc78. Proof using HF rb. exact (code_ato_get segs pF 0 _ 9 _ HF eq_refl). Qed.
  Lemma Ff40 : fetch_word segs (at_ pF 40) = Some W_6cc7c. Proof using HF rb. exact (code_ato_get segs pF 0 _ 10 _ HF eq_refl). Qed.
  Lemma Ff44 : fetch_word segs (at_ pF 44) = Some W_6cc80. Proof using HF rb. exact (code_ato_get segs pF 0 _ 11 _ HF eq_refl). Qed.
  Lemma Ff48 : fetch_word segs (at_ pF 48) = Some W_6cc84. Proof using HF rb. exact (code_ato_get segs pF 0 _ 12 _ HF eq_refl). Qed.
  Lemma Ff52 : fetch_word segs (at_ pF 52) = Some W_6cc88. Proof using HF rb. exact (code_ato_get segs pF 0 _ 13 _ HF eq_refl). Qed.
  Lemma Fs0 : fetch_word segs (at_ pS 0) = Some W_6cda0. Proof using HS. exact (code_ato_get segs pS 0 _ 0 _ HS eq_refl). Qed.
  Lemma Fs4 : fetch_word segs (at_ pS 4) = Some W_6cda4. Proof using HS. exact (code_ato_get segs pS 0 _ 1 _ HS eq_refl). Qed.
  Lemma Fs8 : fetch_word segs (at_ pS 8) = Some W_6cda8. Proof using HS. exact (code_ato_get segs pS 0 _ 2 _ HS eq_refl). Qed.
  Lemma Fs12 : fetch_word segs (at_ pS 12) = Some W_6cdac. Proof using HS. exact (code_ato_get segs pS 0 _ 3 _ HS eq_refl). Qed.
  Lemma Fs16 : fetch_word segs (at_ pS 16) = Some W_6cdb0. Proof using HS. exact (code_ato_get segs pS 0 _ 4 _ HS eq_refl). Qed.
  Lemma Fs20 : fetch_word segs (at_ pS 20) = Some W_6cdb4. Proof using HS. exact (code_ato_get segs pS 0 _ 5 _ HS eq_refl). Qed.
  Lemma Fs24 : fetch_word segs (at_ pS 24) = Some W_6cdb8. Proof using HS. exact (code_ato_get segs pS 0 _ 6 _ HS eq_refl). Qed.
  Lemma Fs28 : fetch_word segs (at_ pS 28) = Some W_6cdbc. Proof using HS. exact (code_ato_get segs pS 0 _ 7 _ HS eq_refl). Qed.
  Lemma Fs32 : fetch_word segs (at_ pS 32) = Some W_6cdc0. Proof using HS. exact (code_ato_get segs pS 0 _ 8 _ HS eq_refl). Qed.
  Lemma Fs36 : fetch_word segs (at_ pS 36) = Some W_6cdc4. Proof using HS. exact (code_ato_get segs pS 0 _ 9 _ HS eq_refl). Qed.
  Lemma Fs40 : fetch_word segs (at_ pS 40) = Some W_6cdc8. Proof using HS. exact (code_ato_get segs pS 0 _ 10 _ HS eq_refl). Qed.
  Lemma Fs44 : fetch_word segs (at_ pS 44) = Some W_6cdcc. Proof using HS. exact (code_ato_get segs pS 0 _ 11 _ HS eq_refl). Qed.

  (* [comment removed for export] *)
  Lemma qc1_loop : forall (k : nat) regs mem rom (cur e : Z),
    (e - cur = Z.of_nat k)%Z -> (0 < Z.of_nat k)%Z -> (0 <= cur)%Z -> (e < 2 ^ 64)%Z ->
    getr regs 13 = Z_to_bv 64 cur -> getr regs 14 = Z_to_bv 64 e -> getr regs 15 = Z_to_bv 64 0 ->
    (forall a : word, (cur <= U a < e)%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ pS 28) mem rom) (mkst r (at_ pS 44) mem rom)
      /\ getr r 13 = Z_to_bv 64 e /\ getr r 14 = Z_to_bv 64 e /\ getr r 15 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r qc1_clob) regs r.
  Proof using HS.
    induction k as [|k IH]; intros regs mem rom cur e Hk Hpos Hc He R13 R14 R15 Hz; [cbn in Hpos; lia|].
    pose proof (u64_range pS) as HpSr.
    assert (Rd : rdn segs mem (v_addi (getr regs 13) 0) 1 = Some [Z_to_bv 8 0]).
    { rewrite R13, v_addi_0. apply Hz. unorm. lia. }
    destruct (Z.eq_dec (Z.of_nat k) 0) as [K0 | Kpos].
    - (* [comment removed for export] *)
      wd_eexists. split.
      + chain_step; [reflexivity | eapply step_lbu; [exact Fs28 | reflexivity | exact D_6cdbc | exact Rd] | step_simpl]; vn.
        av Fs32 D_6cdc0 (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).          (* [comment removed for export] *)
        an Fs36 D_6cdc4.                                                                       (* [comment removed for export] *)
        ab_ft Fs40 D_6cdc8 ltac:(condz).                                                      (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold qc1_clob in G in change_no_check G' end). ra_solve.
    - set (r1 := regupd (regupd (regupd regs 16 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (cur + 1))) 15 (Z_to_bv 64 0)).
      destruct (IH r1 mem rom (cur + 1)%Z e ltac:(lia) ltac:(lia) ltac:(lia) He) as (r2 & RUN & A13 & A14 & A15 & AG);
        [subst r1; gres; reflexivity | subst r1; gres; exact R14 | subst r1; gres; reflexivity | intros a Ha; apply Hz; lia | ].
      exists r2. split.
      + chain_step; [reflexivity | eapply step_lbu; [exact Fs28 | reflexivity | exact D_6cdbc | exact Rd] | step_simpl]; vn.
        av Fs32 D_6cdc0 (Z_to_bv 64 (cur + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
        an Fs36 D_6cdc4.                                                                       (* [comment removed for export] *)
        ab_tk Fs40 D_6cdc8 ltac:(condz).                                                      (* [comment removed for export] *)
        replace (at_ pS (40 + -12)) with (at_ pS 28) by (f_equal; lia).
        exact RUN.
      + split; [exact A13 | split; [exact A14 | split; [exact A15 |]]].
        intros x Hx. rewrite (AG x Hx). subst r1.
        assert (x <> 16 /\ x <> 13 /\ x <> 15) as (X1 & X2 & X3).
        { unfold qc1_clob in Hx. repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
        rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma v_sltu_0_l : forall z, (0 <= z < 2 ^ 64)%Z ->
    v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 (if (0 <? z)%Z then 1 else 0).
  Proof using.
    intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end). unorm. destruct (0 <? z)%Z; reflexivity.
  Qed.
  Lemma v_slt_smallZ : forall x y, (0 <= x < 2 ^ 63)%Z -> (0 <= y < 2 ^ 63)%Z ->
    v_slt (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if (x <? y)%Z then 1 else 0).
  Proof using.
    intros x y Hx Hy. (lazymatch goal with |- ?G => let G' := eval unfold v_slt in G in change_no_check G' end). rewrite c_lts_smallZ by lia. destruct (x <? y)%Z; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma qc1_slow : forall regs mem rom (b : word) (n : Z) (s1 : byte),
    (1 <= n)%Z -> (U b + n <= 2 ^ 47)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b + n - 1))) 1 = Some [s1] ->
    (U s1 = 0 \/ ((U b + n - 1) mod 8 < U s1 /\ U s1 < 128))%Z ->
    (forall a : word, (Sh (U b) <= U a < Sh (U b + n - 1))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 13 = Z_to_bv 64 (Sh (U b)) -> getr regs 14 = Z_to_bv 64 (Sh (U b + n - 1)) ->
    getr regs 15 = Z_to_bv 64 (U b + n - 1) ->
    exists r,
      msteps segs (mkst regs (at_ pS 0) mem rom) (mkst r pK mem rom)
      /\ regs_agree (fun r => In r qc1_clob) regs r.
  Proof using BEQ HS.
    intros regs mem rom b n s1 Hn Hend Rs1 Hs1 Hz R13 R14 R15.
    pose proof (u64_range pS) as HpSr. pose proof (u64_range b) as Hbr. pose proof (u8_range s1) as Hs1r.
    set (last := (U b + n - 1)%Z) in *.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). split; [|]. 1: pose proof (Z.div_pos a 8). all: try lia.
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh last ltac:(lia)) as S1.
    assert (SLE : (Sh (U b) <= Sh last)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end); apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
    pose proof (Z.mod_pos_bound last 8 ltac:(lia)) as M8.
    assert (Rd1 : rdn segs mem (v_addi (getr regs 14) 0) 1 = Some [s1]) by (rewrite R14, v_addi_0; exact Rs1).
    (* [comment removed for export] *)
    assert (A5 : v_and (Z_to_bv 64 (if (0 <? U s1)%Z then 1 else 0))
                       (v_xori (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)) 1) = Z_to_bv 64 0).
    { destruct Hs1 as [Z0 | [L1 L2]].
      - rewrite Z0. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply bv_eq. vm_compute. reflexivity.
      - replace (0 <? U s1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (last mod 8 <? U s1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        apply bv_eq. vm_compute. reflexivity. }
    destruct (Z.eq_dec (Sh (U b)) (Sh last)) as [EQ | NE].
    - (* [comment removed for export] *)
      wd_eexists. split.
      + chain_step; [reflexivity | eapply step_lb; [exact Fs0 | reflexivity | exact D_6cda0 | exact Rd1] | step_simpl]; vn.
        rewrite (v_lb_small s1) by lia.                                                         (* [comment removed for export] *)
        av Fs4 D_6cda4 (Z_to_bv 64 (last mod 8)) ltac:(rewrite v_andi_7; unorm; reflexivity).  (* [comment removed for export] *)
        an Fs8 D_6cda8. rewrite v_sltu_0_l by lia.                                         (* [comment removed for export] *)
        an Fs12 D_6cdac. rewrite v_slt_smallZ by lia.                                       (* [comment removed for export] *)
        an Fs16 D_6cdb0.                                                                     (* [comment removed for export] *)
        an Fs20 D_6cdb4. rewrite A5.                                                         (* [comment removed for export] *)
        ab_tk Fs24 D_6cdb8 ltac:(condz).                                                    (* [comment removed for export] *)
        replace (at_ pS (24 + 20)) with (at_ pS 44) by (f_equal; lia).
        an Fs44 D_6cdcc.                                                                     (* [comment removed for export] *)
        eapply mst_step; [reflexivity | apply (proj1 (BEQ _ _ _)); gres; reflexivity |].      (* [comment removed for export] *)
        wd_refl.
      + (lazymatch goal with |- ?G => let G' := eval unfold qc1_clob in G in change_no_check G' end). ra_solve.
    - (* [comment removed for export] *)
      set (r1 := regupd (regupd (regupd (regupd (regupd (regupd regs
                   16 (Z_to_bv 64 (U s1))) 15 (Z_to_bv 64 (last mod 8))) 17 (Z_to_bv 64 (if (0 <? U s1)%Z then 1 else 0)))
                   15 (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)))
                   15 (v_xori (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)) 1)) 15 (Z_to_bv 64 0)).
      destruct (qc1_loop (Z.to_nat (Sh last - Sh (U b))) r1 mem rom (Sh (U b)) (Sh last)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A13 & A14 & A15 & AG);
        [subst r1; gres; exact R13 | subst r1; gres; exact R14 | subst r1; gres; reflexivity | exact Hz |].
      wd_eexists. split.
      + chain_step; [reflexivity | eapply step_lb; [exact Fs0 | reflexivity | exact D_6cda0 | exact Rd1] | step_simpl]; vn.
        rewrite (v_lb_small s1) by lia.                                                         (* [comment removed for export] *)
        av Fs4 D_6cda4 (Z_to_bv 64 (last mod 8)) ltac:(rewrite v_andi_7; unorm; reflexivity).  (* [comment removed for export] *)
        an Fs8 D_6cda8. rewrite v_sltu_0_l by lia.                                         (* [comment removed for export] *)
        an Fs12 D_6cdac. rewrite v_slt_smallZ by lia.                                       (* [comment removed for export] *)
        an Fs16 D_6cdb0.                                                                     (* [comment removed for export] *)
        an Fs20 D_6cdb4. rewrite A5.                                                         (* [comment removed for export] *)
        ab_ft Fs24 D_6cdb8 ltac:(condz).                                                    (* [comment removed for export] *)
        change (regupd _ 15 (Z_to_bv 64 0)) with r1.
        eapply msteps_trans; [exact RUN|].
        an Fs44 D_6cdcc.                                                                     (* [comment removed for export] *)
        eapply mst_step; [reflexivity | apply (proj1 (BEQ _ _ _)); gres; reflexivity |].      (* [comment removed for export] *)
        wd_refl.
      + apply regs_agree_upd; [clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto|].
        intros x Hx. rewrite (AG x Hx). subst r1.
        assert (x <> 16 /\ x <> 15 /\ x <> 17) as (X1 & X2 & X3).
        { unfold qc1_clob in Hx. repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
        rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma qc1_fast : forall regs mem rom (b : word) (n : Z) w0 w1 s1,
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 ->
    getr regs rb = b -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (at_ pF 0) mem rom) (mkst r (at_ pF 56) mem rom)
      /\ getr r 13 = Z_to_bv 64 (Sh (U b)) /\ getr r 14 = Z_to_bv 64 (Sh (U b + n - 1))
      /\ getr r 15 = Z_to_bv 64 (U b + n - 1) /\ getr r 16 = v_or (Z_to_bv 64 (bytes_le_to_Z w1)) (Z_to_bv 64 (bytes_le_to_Z w0))
      /\ regs_agree (fun r => In r qc1_clob) regs r.
  Proof using Hrb G0 HF.
    intros regs mem rom b n w0 w1 s1 QH Rb R12.
    destruct QH as [Hn Hend Rg Rp [Hg Hp] Rw0 Rw1 Rs1 Hs1 Hz].
    pose proof (u64_range pF) as HpFr. pose proof (u64_range b) as Hbr.
    set (last := (U b + n - 1)%Z) in *.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh last ltac:(lia)) as S1.
    assert (Dv0 : (0 <= U b / 8 < 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Dv1 : (0 <= last / 8 < 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (D0 : (down8 (Sh (U b)) <= Sh (U b))%Z /\ (Sh (U b) < down8 (Sh (U b)) + 8)%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b)) 8 ltac:(lia)); lia).
    assert (D1 : (down8 (Sh last) <= Sh last)%Z /\ (Sh last < down8 (Sh last) + 8)%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh last) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh last) 8 ltac:(lia)); lia).
    (* [comment removed for export] *)
    assert (F8D8F16D16 :
      exists w8 w16, fetch_word segs (at_ pF 8) = Some w8 /\ is_ecall w8 = false /\ decode_any w8 = Some (Op ALU_ADD 15 rb 12, 4%Z)
                  /\ fetch_word segs (at_ pF 16) = Some w16 /\ is_ecall w16 = false /\ decode_any w16 = Some (ShiftImm ALU_SRL 13 rb 3, 4%Z)).
    { destruct Hrb as [-> | ->].
      - exists W_6cc5c, W_6cc64. repeat split.
        + exact (code_ato_get segs pF 0 (qc1f_words 10) 2 _ HF eq_refl).
        + exact D_6cc5c.
        + exact (code_ato_get segs pF 0 (qc1f_words 10) 4 _ HF eq_refl).
        + exact D_6cc64.
      - exists W_6cea0, W_6cea8. repeat split.
        + exact (code_ato_get segs pF 0 (qc1f_words 11) 2 _ HF eq_refl).
        + exact D_6cea0.
        + exact (code_ato_get segs pF 0 (qc1f_words 11) 4 _ HF eq_refl).
        + exact D_6cea8. }
    destruct F8D8F16D16 as (w8 & w16 & F8 & E8 & D8 & F16 & E16 & D16).
    assert (Hrb0 : rb <> 0) by (destruct Hrb as [-> | ->]; intros X; discriminate X).
    wd_eexists. split.
    - (* [comment removed for export] *)
      eapply msteps_trans; [eapply (G0 regs mem rom (Z_to_bv 64 p_shoff)); exact Rg |]. zlit_at.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | exact (step_add _ _ _ _ _ _ _ _ _ F8 E8 D8) | step_simpl]; vn.
      rewrite (getr_other _ 13 _ rb) by (destruct Hrb as [-> | ->]; intros X; discriminate X). rewrite Rb.
      replace (v_add b (Z_to_bv 64 n)) with (Z_to_bv 64 (U b + n)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 0x7fff8000) (v := Z_to_bv 64 0x7fff8000);
          [exact Ff12 | reflexivity | exact D_6cc60 | gres; rewrite v_addi_0; exact Rp | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F16 E16 D16) | step_simpl]; vn.
      rewrite !(getr_other _ _ _ rb) by (destruct Hrb as [-> | ->]; intros X; discriminate X). rewrite Rb, v_srli_3.
      av Ff20 D_6cc68 (Z_to_bv 64 last) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).                 (* [comment removed for export] *)
      av Ff24 D_6cc6c (Z_to_bv 64 (last / 8)) ltac:(rewrite v_srli_3; unorm; reflexivity).          (* [comment removed for export] *)
      av Ff28 D_6cc70 (Z_to_bv 64 (Sh (U b))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, Sh in G in change_no_check G' end); unorm; f_equal; lia).         (* [comment removed for export] *)
      av Ff32 D_6cc74 (Z_to_bv 64 (Sh last)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, Sh in G in change_no_check G' end); unorm; f_equal; lia).          (* [comment removed for export] *)
      av Ff36 D_6cc78 (Z_to_bv 64 (down8 (Sh (U b)))) ltac:(rewrite v_andi_m8; unorm; reflexivity). (* [comment removed for export] *)
      av Ff40 D_6cc7c (Z_to_bv 64 (down8 (Sh last))) ltac:(rewrite v_andi_m8; unorm; reflexivity).  (* [comment removed for export] *)
      pose proof (rdn_length _ _ _ _ _ Rw0) as L0. pose proof (rdn_length _ _ _ _ _ Rw1) as L1.
      pose proof (bytes_le_to_Z_nonneg w0) as N0. pose proof (bytes_le_to_Z_bound w0) as B0. rewrite L0 in B0.
      pose proof (bytes_le_to_Z_nonneg w1) as N1. pose proof (bytes_le_to_Z_bound w1) as B1. rewrite L1 in B1.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in B0, B1.
      chain_step; [reflexivity
        | eapply step_ld with (bs := w0) (v := Z_to_bv 64 (bytes_le_to_Z w0));
          [exact Ff44 | reflexivity | exact D_6cc80 | gres; rewrite v_addi_0; exact Rw0 | rewrite u_Z2bv by lia; reflexivity]
        | step_simpl]; vn.                                                                            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := w1) (v := Z_to_bv 64 (bytes_le_to_Z w1));
          [exact Ff48 | reflexivity | exact D_6cc84 | gres; rewrite v_addi_0; exact Rw1 | rewrite u_Z2bv by lia; reflexivity]
        | step_simpl]; vn.                                                                            (* [comment removed for export] *)
      an Ff52 D_6cc88.                                                                                (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold qc1_clob in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Theorem qc1_pass : forall regs mem rom (b : word) (n : Z) w0 w1 s1,
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 ->
    getr regs rb = b -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (at_ pF 0) mem rom) (mkst r pK mem rom)
      /\ regs_agree (fun r => In r qc1_clob) regs r.
  Proof using Hrb HK BEQ BNE G0 HS HF pS.
    intros regs mem rom b n w0 w1 s1 QH Rb R12.
    destruct (qc1_fast regs mem rom b n w0 w1 s1 QH Rb R12) as (r1 & RUN1 & A13 & A14 & A15 & A16 & AG1).
    destruct QH as [Hn Hend Rg Rp [Hg Hp] Rw0 Rw1 Rs1 Hs1 Hz].
    destruct (decide (v_or (Z_to_bv 64 (bytes_le_to_Z w1)) (Z_to_bv 64 (bytes_le_to_Z w0)) = Z_to_bv 64 0)) as [Z0 | NZ].
    - (* [comment removed for export] *)
      exists r1. split; [|exact AG1].
      eapply msteps_trans; [exact RUN1|].
      eapply mst_step; [reflexivity | apply (proj2 (BNE _ _ _)); rewrite A16; exact Z0 |].
      rewrite at_addi. replace (at_ pF (56 + 4)) with pK by (rewrite <- HK; f_equal; lia).
      wd_refl.
    - (* [comment removed for export] *)
      destruct (qc1_slow r1 mem rom b n s1 Hn Hend Rs1 Hs1 Hz A13 A14 A15) as (r2 & RUN2 & AG2).
      exists r2. split.
      + eapply msteps_trans; [exact RUN1|].
        eapply mst_step; [reflexivity | apply (proj1 (BNE _ _ _)); rewrite A16; exact NZ |].
        rewrite <- (at_0 pS) at 1. exact RUN2.
      + intros x Hx. rewrite (AG2 x Hx). exact (AG1 x Hx).
  Qed.
End QC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qc2f_words (rb sE : reg) : list (option (bv 32)) :=
  [None; None; Some W_6c7dc;
   Some (if bv_eqb sE 21 then W_6c7e0 else if bv_eqb sE 19 then W_6c828 else W_6da28);
   Some (if bv_eqb rb 10 then W_6c82c else W_6c7e4);
   Some (if bv_eqb sE 21 then W_6c7e8 else if bv_eqb sE 19 then W_6c830 else W_6da30);
   Some W_6c7ec; Some W_6c7f0; Some W_6c7f4; Some W_6c7f8; Some W_6c7fc; Some W_6c800; Some W_6c804; None]%list.
Definition qc2s_words (sE : reg) : list (option (bv 32)) :=
  [Some W_6cabc; Some (if bv_eqb sE 21 then W_6cac0 else if bv_eqb sE 19 then W_6cb64 else W_6ddc8);
   Some W_6cac4; Some W_6cac8; Some W_6cacc; Some W_6cad0; Some W_6cad4;
   Some W_6cad8; Some W_6cadc; Some W_6cae0; Some W_6cae4; Some W_6cae8; None]%list.

Section QC2.
  Variable segs : list Segment.
  Variables pF pS pK : word.
  Variables rb sE : reg.
  Variables g_shoff p_shoff : Z.
  Hypothesis HF : code_ato segs pF 0 (qc2f_words rb sE).
  Hypothesis HS : code_ato segs pS 0 (qc2s_words sE).
  Hypothesis G0 : gload segs pF 0 13 g_shoff.
  Hypothesis BNE : gbnez segs (at_ pF 52) 15 pS.
  Hypothesis BEQ : gbeqz segs (at_ pS 48) 13 pK.
  Hypothesis HK : at_ pF 56 = pK.
  Hypothesis Hrb : rb = 10 \/ rb = 11.
  Hypothesis HsE : sE = 19 \/ sE = 20 \/ sE = 21.

  Lemma Gf8 : fetch_word segs (at_ pF 8) = Some W_6c7dc. Proof using HF sE rb. exact (code_ato_get segs pF 0 _ 2 _ HF eq_refl). Qed.
  Lemma Gf24 : fetch_word segs (at_ pF 24) = Some W_6c7ec. Proof using HF sE rb. exact (code_ato_get segs pF 0 _ 6 _ HF eq_refl). Qed.
  Lemma Gf28 : fetch_word segs (at_ pF 28) = Some W_6c7f0. Proof using HF sE rb. exact (code_ato_get segs pF 0 _ 7 _ HF eq_refl). Qed.
  Lemma Gf32 : fetch_word segs (at_ pF 32) = Some W_6c7f4. Proof using HF sE rb. exact (code_ato_get segs pF 0 _ 8 _ HF eq_refl). Qed.
  Lemma Gf36 : fetch_word segs (at_ pF 36) = Some W_6c7f8. Proof using HF sE rb. exact (code_ato_get segs pF 0 _ 9 _ HF eq_refl). Qed.
  Lemma Gf40 : fetch_word segs (at_ pF 40) = Some W_6c7fc. Proof using HF sE rb. exact (code_ato_get segs pF 0 _ 10 _ HF eq_refl). Qed.
  Lemma Gf44 : fetch_word segs (at_ pF 44) = Some W_6c800. Proof using HF sE rb. exact (code_ato_get segs pF 0 _ 11 _ HF eq_refl). Qed.
  Lemma Gf48 : fetch_word segs (at_ pF 48) = Some W_6c804. Proof using HF sE rb. exact (code_ato_get segs pF 0 _ 12 _ HF eq_refl). Qed.
  Lemma Gs0 : fetch_word segs (at_ pS 0) = Some W_6cabc. Proof using HS sE. exact (code_ato_get segs pS 0 _ 0 _ HS eq_refl). Qed.
  Lemma Gs8 : fetch_word segs (at_ pS 8) = Some W_6cac4. Proof using HS sE. exact (code_ato_get segs pS 0 _ 2 _ HS eq_refl). Qed.
  Lemma Gs12 : fetch_word segs (at_ pS 12) = Some W_6cac8. Proof using HS sE. exact (code_ato_get segs pS 0 _ 3 _ HS eq_refl). Qed.
  Lemma Gs16 : fetch_word segs (at_ pS 16) = Some W_6cacc. Proof using HS sE. exact (code_ato_get segs pS 0 _ 4 _ HS eq_refl). Qed.
  Lemma Gs20 : fetch_word segs (at_ pS 20) = Some W_6cad0. Proof using HS sE. exact (code_ato_get segs pS 0 _ 5 _ HS eq_refl). Qed.
  Lemma Gs24 : fetch_word segs (at_ pS 24) = Some W_6cad4. Proof using HS sE. exact (code_ato_get segs pS 0 _ 6 _ HS eq_refl). Qed.
  Lemma Gs28 : fetch_word segs (at_ pS 28) = Some W_6cad8. Proof using HS sE. exact (code_ato_get segs pS 0 _ 7 _ HS eq_refl). Qed.
  Lemma Gs32 : fetch_word segs (at_ pS 32) = Some W_6cadc. Proof using HS sE. exact (code_ato_get segs pS 0 _ 8 _ HS eq_refl). Qed.
  Lemma Gs36 : fetch_word segs (at_ pS 36) = Some W_6cae0. Proof using HS sE. exact (code_ato_get segs pS 0 _ 9 _ HS eq_refl). Qed.
  Lemma Gs40 : fetch_word segs (at_ pS 40) = Some W_6cae4. Proof using HS sE. exact (code_ato_get segs pS 0 _ 10 _ HS eq_refl). Qed.
  Lemma Gs44 : fetch_word segs (at_ pS 44) = Some W_6cae8. Proof using HS sE. exact (code_ato_get segs pS 0 _ 11 _ HS eq_refl). Qed.

  Definition qc2_clob : list reg := [13; 14; 15; 16; 17]%list.

  (* [comment removed for export] *)
  Lemma qc2_loop : forall (k : nat) regs mem rom (cur e : Z),
    (e - cur = Z.of_nat k)%Z -> (0 < Z.of_nat k)%Z -> (0 <= cur)%Z -> (e < 2 ^ 64)%Z ->
    getr regs 13 = Z_to_bv 64 cur -> getr regs 14 = Z_to_bv 64 e -> getr regs 15 = Z_to_bv 64 0 ->
    (forall a : word, (cur <= U a < e)%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ pS 28) mem rom) (mkst r (at_ pS 44) mem rom)
      /\ getr r 13 = Z_to_bv 64 e /\ getr r 14 = Z_to_bv 64 e /\ getr r 15 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r qc2_clob) regs r.
  Proof using HS sE.
    induction k as [|k IH]; intros regs mem rom cur e Hk Hpos Hc He R13 R14 R15 Hz; [cbn in Hpos; lia|].
    pose proof (u64_range pS) as HpSr.
    assert (Rd : rdn segs mem (v_addi (getr regs 13) 0) 1 = Some [Z_to_bv 8 0]).
    { rewrite R13, v_addi_0. apply Hz. unorm. lia. }
    destruct (Z.eq_dec (Z.of_nat k) 0) as [K0 | Kpos].
    - wd_eexists. split.
      + chain_step; [reflexivity | eapply step_lbu; [exact Gs28 | reflexivity | exact D_6cad8 | exact Rd] | step_simpl]; vn.
        av Gs32 D_6cadc (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
        an Gs36 D_6cae0.
        ab_ft Gs40 D_6cae4 ltac:(condz).
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold qc2_clob in G in change_no_check G' end). ra_solve.
    - set (r1 := regupd (regupd (regupd regs 16 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (cur + 1))) 15 (Z_to_bv 64 0)).
      destruct (IH r1 mem rom (cur + 1)%Z e ltac:(lia) ltac:(lia) ltac:(lia) He) as (r2 & RUN & A13 & A14 & A15 & AG);
        [subst r1; gres; reflexivity | subst r1; gres; exact R14 | subst r1; gres; reflexivity | intros a Ha; apply Hz; lia | ].
      exists r2. split.
      + chain_step; [reflexivity | eapply step_lbu; [exact Gs28 | reflexivity | exact D_6cad8 | exact Rd] | step_simpl]; vn.
        av Gs32 D_6cadc (Z_to_bv 64 (cur + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
        an Gs36 D_6cae0.
        ab_tk Gs40 D_6cae4 ltac:(condz).
        replace (at_ pS (40 + -12)) with (at_ pS 28) by (f_equal; lia).
        exact RUN.
      + split; [exact A13 | split; [exact A14 | split; [exact A15 |]]].
        intros x Hx. rewrite (AG x Hx). subst r1.
        assert (x <> 16 /\ x <> 13 /\ x <> 15) as (X1 & X2 & X3).
        { unfold qc2_clob in Hx. repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
        rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma qc2_slow : forall regs mem rom (b : word) (n : Z) (s1 : byte),
    (1 <= n)%Z -> (U b + n <= 2 ^ 47)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b + n - 1))) 1 = Some [s1] ->
    (U s1 = 0 \/ ((U b + n - 1) mod 8 < U s1 /\ U s1 < 128))%Z ->
    (forall a : word, (Sh (U b) <= U a < Sh (U b + n - 1))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 13 = Z_to_bv 64 (Sh (U b)) -> getr regs 14 = Z_to_bv 64 (Sh (U b + n - 1)) ->
    getr regs sE = Z_to_bv 64 (U b + n - 1) ->
    exists r,
      msteps segs (mkst regs (at_ pS 0) mem rom) (mkst r pK mem rom)
      /\ regs_agree (fun r => In r qc2_clob) regs r.
  Proof using HsE BEQ HS HF rb pF.
    intros regs mem rom b n s1 Hn Hend Rs1 Hs1 Hz R13 R14 RE.
    pose proof (u64_range pS) as HpSr. pose proof (u64_range b) as Hbr. pose proof (u8_range s1) as Hs1r.
    set (last := (U b + n - 1)%Z) in *.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh last ltac:(lia)) as S1.
    assert (SLE : (Sh (U b) <= Sh last)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end); apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
    pose proof (Z.mod_pos_bound last 8 ltac:(lia)) as M8.
    assert (Rd1 : rdn segs mem (v_addi (getr regs 14) 0) 1 = Some [s1]) by (rewrite R14, v_addi_0; exact Rs1).
    (* [comment removed for export] *)
    assert (I4 : exists w4, fetch_word segs (at_ pS 4) = Some w4 /\ is_ecall w4 = false /\ decode_any w4 = Some (OpImm ALU_AND 16 sE 7, 4%Z)).
    { destruct HsE as [-> | [-> | ->]].
      - exists W_6cb64. repeat split; [exact (code_ato_get segs pS 0 (qc2s_words 19) 1 _ HS eq_refl) | exact D_6cb64].
      - exists W_6ddc8. repeat split; [exact (code_ato_get segs pS 0 (qc2s_words 20) 1 _ HS eq_refl) | exact D_6ddc8].
      - exists W_6cac0. repeat split; [exact (code_ato_get segs pS 0 (qc2s_words 21) 1 _ HS eq_refl) | exact D_6cac0]. }
    destruct I4 as (w4 & F4 & E4 & D4).
    assert (HsE' : sE <> 15 /\ sE <> 16 /\ sE <> 0) by (destruct HsE as [-> | [-> | ->]]; repeat split; intros X; discriminate X).
    destruct HsE' as (NE15 & NE16 & NE0).
    assert (A5 : v_and (Z_to_bv 64 (if (0 <? U s1)%Z then 1 else 0))
                       (v_xori (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)) 1) = Z_to_bv 64 0).
    { destruct Hs1 as [Z0 | [L1 L2]].
      - rewrite Z0. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply bv_eq. vm_compute. reflexivity.
      - replace (0 <? U s1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (last mod 8 <? U s1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        apply bv_eq. vm_compute. reflexivity. }
    (* [comment removed for export] *)
    Ltac head2 Rd1 F4 E4 D4 NE15 RE A5 s1 last :=
      chain_step; [reflexivity | eapply step_lb; [exact Gs0 | reflexivity | exact D_6cabc | exact Rd1] | step_simpl]; vn;
      rewrite (v_lb_small s1) by lia;                                                            (* [comment removed for export] *)
      eapply mst_step; [reflexivity | exact (step_andi _ _ _ _ _ _ _ _ _ F4 E4 D4) | step_simpl]; vn;   (* [comment removed for export] *)
      rewrite (getr_other _ 15 _ sE NE15), RE, v_andi_7; unorm;
      an Gs8 D_6cac4; rewrite v_sltu_0_l by lia;                                                 (* [comment removed for export] *)
      an Gs12 D_6cac8; rewrite v_slt_smallZ by lia;                                              (* [comment removed for export] *)
      an Gs16 D_6cacc;                                                                           (* [comment removed for export] *)
      an Gs20 D_6cad0; rewrite A5.                                                               (* [comment removed for export] *)
    destruct (Z.eq_dec (Sh (U b)) (Sh last)) as [EQ | NE].
    - wd_eexists. split.
      + head2 Rd1 F4 E4 D4 NE15 RE A5 s1 last.
        ab_tk Gs24 D_6cad4 ltac:(condz).
        replace (at_ pS (24 + 20)) with (at_ pS 44) by (f_equal; lia).
        an Gs44 D_6cae8.
        eapply mst_step; [reflexivity | apply (proj1 (BEQ _ _ _)); gres; reflexivity |].
        wd_refl.
      + (lazymatch goal with |- ?G => let G' := eval unfold qc2_clob in G in change_no_check G' end). ra_solve.
    - set (r1 := regupd (regupd (regupd (regupd (regupd (regupd regs
                   15 (Z_to_bv 64 (U s1))) 16 (Z_to_bv 64 (last mod 8))) 17 (Z_to_bv 64 (if (0 <? U s1)%Z then 1 else 0)))
                   15 (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)))
                   15 (v_xori (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)) 1)) 15 (Z_to_bv 64 0)).
      destruct (qc2_loop (Z.to_nat (Sh last - Sh (U b))) r1 mem rom (Sh (U b)) (Sh last)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A13 & A14 & A15 & AG);
        [subst r1; gres; exact R13 | subst r1; gres; exact R14 | subst r1; gres; reflexivity | exact Hz |].
      wd_eexists. split.
      + head2 Rd1 F4 E4 D4 NE15 RE A5 s1 last.
        ab_ft Gs24 D_6cad4 ltac:(condz).
        change (regupd _ 15 (Z_to_bv 64 0)) with r1.
        eapply msteps_trans; [exact RUN|].
        an Gs44 D_6cae8.
        eapply mst_step; [reflexivity | apply (proj1 (BEQ _ _ _)); gres; reflexivity |].
        wd_refl.
      + apply regs_agree_upd; [clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto|].
        intros x Hx. rewrite (AG x Hx). subst r1.
        assert (x <> 16 /\ x <> 15 /\ x <> 17) as (X1 & X2 & X3).
        { unfold qc2_clob in Hx. repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
        rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma qc2_fast : forall regs mem rom (b : word) (n : Z) w0 w1 s1,
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 ->
    getr regs rb = b -> getr regs sE = Z_to_bv 64 (U b + n) ->
    exists r,
      msteps segs (mkst regs (at_ pF 0) mem rom) (mkst r (at_ pF 52) mem rom)
      /\ getr r 13 = Z_to_bv 64 (Sh (U b)) /\ getr r 14 = Z_to_bv 64 (Sh (U b + n - 1))
      /\ getr r sE = Z_to_bv 64 (U b + n - 1) /\ getr r 15 = v_or (Z_to_bv 64 (bytes_le_to_Z w1)) (Z_to_bv 64 (bytes_le_to_Z w0))
      /\ regs_agree (fun r => In r qc2_clob \/ r = sE) regs r.
  Proof using HsE Hrb G0 HS HF pS.
    intros regs mem rom b n w0 w1 s1 QH Rb RE.
    destruct QH as [Hn Hend Rg Rp [Hg Hp] Rw0 Rw1 Rs1 Hs1 Hz].
    pose proof (u64_range pF) as HpFr. pose proof (u64_range b) as Hbr.
    set (last := (U b + n - 1)%Z) in *.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh last ltac:(lia)) as S1.
    assert (Dv0 : (0 <= U b / 8 < 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Dv1 : (0 <= last / 8 < 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (D0 : (down8 (Sh (U b)) <= Sh (U b))%Z /\ (Sh (U b) < down8 (Sh (U b)) + 8)%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b)) 8 ltac:(lia)); lia).
    assert (D1 : (down8 (Sh last) <= Sh last)%Z /\ (Sh last < down8 (Sh last) + 8)%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh last) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh last) 8 ltac:(lia)); lia).
    (* [comment removed for export] *)
    assert (I12 : exists w, fetch_word segs (at_ pF 12) = Some w /\ is_ecall w = false /\ decode_any w = Some (OpImm ALU_ADD sE sE 4095, 4%Z)).
    { destruct HsE as [-> | [-> | ->]].
      - exists W_6c828. repeat split; [exact (code_ato_get segs pF 0 (qc2f_words rb 19) 3 _ HF eq_refl) | exact D_6c828].
      - exists W_6da28. repeat split; [exact (code_ato_get segs pF 0 (qc2f_words rb 20) 3 _ HF eq_refl) | exact D_6da28].
      - exists W_6c7e0. repeat split; [exact (code_ato_get segs pF 0 (qc2f_words rb 21) 3 _ HF eq_refl) | exact D_6c7e0]. }
    assert (I16 : exists w, fetch_word segs (at_ pF 16) = Some w /\ is_ecall w = false /\ decode_any w = Some (ShiftImm ALU_SRL 13 rb 3, 4%Z)).
    { destruct Hrb as [-> | ->].
      - exists W_6c82c. repeat split; [exact (code_ato_get segs pF 0 (qc2f_words 10 sE) 4 _ HF eq_refl) | exact D_6c82c].
      - exists W_6c7e4. repeat split; [exact (code_ato_get segs pF 0 (qc2f_words 11 sE) 4 _ HF eq_refl) | exact D_6c7e4]. }
    assert (I20 : exists w, fetch_word segs (at_ pF 20) = Some w /\ is_ecall w = false /\ decode_any w = Some (ShiftImm ALU_SRL 15 sE 3, 4%Z)).
    { destruct HsE as [-> | [-> | ->]].
      - exists W_6c830. repeat split; [exact (code_ato_get segs pF 0 (qc2f_words rb 19) 5 _ HF eq_refl) | exact D_6c830].
      - exists W_6da30. repeat split; [exact (code_ato_get segs pF 0 (qc2f_words rb 20) 5 _ HF eq_refl) | exact D_6da30].
      - exists W_6c7e8. repeat split; [exact (code_ato_get segs pF 0 (qc2f_words rb 21) 5 _ HF eq_refl) | exact D_6c7e8]. }
    destruct I12 as (w12 & F12 & E12 & D12). destruct I16 as (w16 & F16 & E16 & D16). destruct I20 as (w20 & F20 & E20 & D20).
    (* [comment removed for export] *)
    pose proof (rdn_length _ _ _ _ _ Rw0) as L0. pose proof (rdn_length _ _ _ _ _ Rw1) as L1.
    pose proof (bytes_le_to_Z_nonneg w0) as N0. pose proof (bytes_le_to_Z_bound w0) as B0. rewrite L0 in B0.
    pose proof (bytes_le_to_Z_nonneg w1) as N1. pose proof (bytes_le_to_Z_bound w1) as B1. rewrite L1 in B1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in B0, B1.
    destruct Hrb as [Erb | Erb]; destruct HsE as [EsE | [EsE | EsE]]; rewrite Erb in D16, Rb; rewrite EsE in D12, D20, RE |- *.
    all: wd_eexists; split;
      [ eapply msteps_trans; [eapply (G0 regs mem rom (Z_to_bv 64 p_shoff)); exact Rg |]; zlit_at;
        (chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 0x7fff8000) (v := Z_to_bv 64 0x7fff8000);
            [exact Gf8 | reflexivity | exact D_6c7dc | gres; rewrite v_addi_0; exact Rp | apply bytes_le_to_Z_8]
          | step_simpl]); vn;
        (eapply mst_step; [reflexivity | exact (step_addi _ _ _ _ _ _ _ _ _ F12 E12 D12) | step_simpl]); vn;
        replace (v_addi (Z_to_bv 64 (U b + n)) (-1)) with (Z_to_bv 64 last) by ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; subst last; f_equal; lia);
        (eapply mst_step; [reflexivity | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F16 E16 D16) | step_simpl]); vn; rewrite v_srli_3;
        (eapply mst_step; [reflexivity | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F20 E20 D20) | step_simpl]); vn; rewrite v_srli_3; unorm;
        av Gf24 D_6c7ec (Z_to_bv 64 (Sh (U b))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, Sh in G in change_no_check G' end); unorm; f_equal; lia);
        av Gf28 D_6c7f0 (Z_to_bv 64 (Sh last)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, Sh in G in change_no_check G' end); unorm; f_equal; lia);
        av Gf32 D_6c7f4 (Z_to_bv 64 (down8 (Sh (U b)))) ltac:(rewrite v_andi_m8; unorm; reflexivity);
        av Gf36 D_6c7f8 (Z_to_bv 64 (down8 (Sh last))) ltac:(rewrite v_andi_m8; unorm; reflexivity);
        (chain_step; [reflexivity
          | eapply step_ld with (bs := w0) (v := Z_to_bv 64 (bytes_le_to_Z w0));
            [exact Gf40 | reflexivity | exact D_6c7fc | gres; rewrite v_addi_0; exact Rw0 | rewrite u_Z2bv by lia; reflexivity]
          | step_simpl]); vn;
        (chain_step; [reflexivity
          | eapply step_ld with (bs := w1) (v := Z_to_bv 64 (bytes_le_to_Z w1));
            [exact Gf44 | reflexivity | exact D_6c800 | gres; rewrite v_addi_0; exact Rw1 | rewrite u_Z2bv by lia; reflexivity]
          | step_simpl]); vn;
        an Gf48 D_6c804;
        wd_refl
      | post; intros x Hx;
        repeat match goal with |- getr (regupd _ ?k _) x = _ =>
          rewrite (getr_other _ k _ x) by (intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto) end; reflexivity ].
  Qed.

  Theorem qc2_pass : forall regs mem rom (b : word) (n : Z) w0 w1 s1,
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 ->
    getr regs rb = b -> getr regs sE = Z_to_bv 64 (U b + n) ->
    exists r,
      msteps segs (mkst regs (at_ pF 0) mem rom) (mkst r pK mem rom)
      /\ getr r sE = Z_to_bv 64 (U b + n - 1)
      /\ regs_agree (fun r => In r qc2_clob \/ r = sE) regs r.
  Proof using HsE Hrb HK BEQ BNE G0 HS HF pS.
    intros regs mem rom b n w0 w1 s1 QH Rb RE.
    destruct (qc2_fast regs mem rom b n w0 w1 s1 QH Rb RE) as (r1 & RUN1 & A13 & A14 & AE & A15 & AG1).
    destruct QH as [Hn Hend Rg Rp [Hg Hp] Rw0 Rw1 Rs1 Hs1 Hz].
    destruct (decide (v_or (Z_to_bv 64 (bytes_le_to_Z w1)) (Z_to_bv 64 (bytes_le_to_Z w0)) = Z_to_bv 64 0)) as [Z0 | NZ].
    - exists r1. split; [|split; [exact AE | exact AG1]].
      eapply msteps_trans; [exact RUN1|].
      eapply mst_step; [reflexivity | apply (proj2 (BNE _ _ _)); rewrite A15; exact Z0 |].
      rewrite at_addi. replace (at_ pF (52 + 4)) with pK by (rewrite <- HK; f_equal; lia).
      wd_refl.
    - destruct (qc2_slow r1 mem rom b n s1 Hn Hend Rs1 Hs1 Hz A13 A14 AE) as (r2 & RUN2 & AG2).
      exists r2. split; [|split].
      + eapply msteps_trans; [exact RUN1|].
        eapply mst_step; [reflexivity | apply (proj1 (BNE _ _ _)); rewrite A15; exact NZ |].
        rewrite <- (at_0 pS) at 1. exact RUN2.
      + rewrite (AG2 sE). exact AE. (lazymatch goal with |- ?G => let G' := eval unfold qc2_clob in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). destruct HsE as [-> | [-> | ->]]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.
      + intros x Hx. rewrite (AG2 x) by (intros Hc; apply Hx; left; exact Hc). exact (AG1 x Hx).
  Qed.
End QC2.
End FPGen1.
End AsRtQC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpy. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpy AsRtQC.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Definition amset_words : list (option (bv 32)) :=
  [
   Some W_6cc00; Some W_6cc04; Some W_6cc08; Some W_6cc0c; Some W_6cc10; Some W_6cc14; Some W_6cc18; Some W_6cc1c;
   Some W_6cc20; Some W_6cc24; None; None; Some W_6cc30; Some W_6cc34; Some W_6cc38; Some W_6cc3c; Some W_6cc40;
   Some W_6cc44; Some W_6cc48; Some W_6cc4c; Some W_6cc50; None; None; Some W_6cc5c; Some W_6cc60; Some W_6cc64;
   Some W_6cc68; Some W_6cc6c; Some W_6cc70; Some W_6cc74; Some W_6cc78; Some W_6cc7c; Some W_6cc80; Some W_6cc84;
   Some W_6cc88; Some W_6cc8c; None; None; Some W_6cc98; Some W_6cc9c; Some W_6cca0; Some W_6cca4; Some W_6cca8;
   Some W_6ccac; Some W_6ccb0; Some W_6ccb4; Some W_6ccb8; Some W_6ccbc; Some W_6ccc0; Some W_6ccc4; Some W_6ccc8;
   Some W_6cccc; Some W_6ccd0; Some W_6ccd4; Some W_6ccd8; Some W_6ccdc; Some W_6cce0; Some W_6cce4; Some W_6cce8;
   Some W_6ccec; Some W_6ccf0; Some W_6ccf4; Some W_6ccf8; Some W_6ccfc; Some W_6cd00; Some W_6cd04; Some W_6cd08;
   Some W_6cd0c; Some W_6cd10; Some W_6cd14; Some W_6cd18; Some W_6cd1c; Some W_6cd20; Some W_6cd24; Some W_6cd28;
   Some W_6cd2c; Some W_6cd30; Some W_6cd34; Some W_6cd38; Some W_6cd3c; Some W_6cd40; None; None; Some W_6cd4c;
   Some W_6cd50; Some W_6cd54; Some W_6cd58; Some W_6cd5c; Some W_6cd60; Some W_6cd64; Some W_6cd68; Some W_6cd6c;
   Some W_6cd70; Some W_6cd74; Some W_6cd78; Some W_6cd7c; Some W_6cd80; Some W_6cd84; Some W_6cd88; Some W_6cd8c;
   Some W_6cd90; Some W_6cd94; Some W_6cd98; Some W_6cd9c; Some W_6cda0; Some W_6cda4; Some W_6cda8; Some W_6cdac;
   Some W_6cdb0; Some W_6cdb4; Some W_6cdb8; Some W_6cdbc; Some W_6cdc0; Some W_6cdc4; Some W_6cdc8; Some W_6cdcc;
   Some W_6cdd0; Some W_6cdd4; Some W_6cdd8; Some W_6cddc; Some W_6cde0; Some W_6cde4; Some W_6cde8; Some W_6cdec;
   Some W_6cdf0; Some W_6cdf4; Some W_6cdf8; Some W_6cdfc; None; None; Some W_6ce08; Some W_6ce0c; Some W_6ce10;
   Some W_6ce14; Some W_6ce18; Some W_6ce1c; Some W_6ce20; Some W_6ce24; Some W_6ce28; Some W_6ce2c; Some W_6ce30;
   Some W_6ce34; Some W_6ce38; Some W_6ce3c
  ]%list.


(* [comment removed for export] *)
Definition amset_saved : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list.

(* [comment removed for export] *)
Record amset_tab : Type := AMST {
  am_base : word;          (* [comment removed for export] *)
  am_rip : rip_tab;        (* [comment removed for export] *)
  am_mset : word;          (* [comment removed for export] *)
  am_g_flag : Z; am_p_flag : Z;   (* [comment removed for export] *)
  am_c_rms : Z }.          (* [comment removed for export] *)

Record amset_tab_ok (segs : list Segment) (t : amset_tab) : Prop := AMSTOK {
  ato_code : code_ato segs (am_base t) 0 amset_words;
  ato_rip : rip_tab_ok segs (am_rip t);
  ato_rip_base : rt_base (am_rip t) = at_ (am_base t) 13200;
  ato_mset : code_at segs (am_mset t) 0 mmemset_words;
  ato_qcf : code_ato segs (at_ (am_base t) 84) 0 (qc1f_words 10);
  ato_qcs : code_ato segs (at_ (am_base t) 416) 0 qc1s_words;
  ato_g40 : gload segs (am_base t) 40 13 (am_g_flag t);
  ato_g84 : gload segs (at_ (am_base t) 84) 0 13 (mt_g_shoff (rt_m2s (am_rip t)));
  ato_g144 : gload segs (am_base t) 144 13 (am_c_rms t);
  ato_b140 : gbnez segs (at_ (am_base t) 140) 16 (at_ (am_base t) 416);
  ato_b464 : gbeqz segs (at_ (am_base t) 464) 13 (at_ (am_base t) 144);
  ato_base : (U (am_base t) mod 2 = 0)%Z /\ (U (am_base t) + 20000 < 2 ^ 64)%Z;
  ato_mset_ok : ret_ok (am_mset t) }.

Section AMSET.
  Variable segs : list Segment.
  Variable base : word.
  Variable rt : rip_tab.
  Variable mset : word.
  Variables g_flag p_flag c_rms : Z.
  #[local] Abbreviation g_shoff := (mt_g_shoff (rt_m2s rt)).
  #[local] Abbreviation p_shoff := (mt_p_shoff (rt_m2s rt)).
  Hypothesis HCODE : code_ato segs base 0 amset_words.
  Hypothesis RTOK : rip_tab_ok segs rt.
  Hypothesis RTB : rt_base rt = at_ base 13200.
  Hypothesis MSC : code_at segs mset 0 mmemset_words.
  Hypothesis QCF : code_ato segs (at_ base 84) 0 (qc1f_words 10).
  Hypothesis QCS : code_ato segs (at_ base 416) 0 qc1s_words.
  Hypothesis G40 : gload segs base 40 13 g_flag.
  Hypothesis G84 : gload segs (at_ base 84) 0 13 g_shoff.
  Hypothesis G144 : gload segs base 144 13 c_rms.
  Hypothesis B140 : gbnez segs (at_ base 140) 16 (at_ base 416).
  Hypothesis B464 : gbeqz segs (at_ base 464) 13 (at_ base 144).
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 20000 < 2 ^ 64)%Z.
  Hypothesis Hmset : ret_ok mset.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6cc00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6cc04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6cc08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6cc0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6cc10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6cc14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6cc18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6cc1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6cc20.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_6cc24.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 9 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_6cc30.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_6cc34.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_6cc38.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6cc3c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6cc40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6cc44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6cc48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6cc4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6cc50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 20 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_6cc5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_6cc60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo100 : fetch_word segs (at_ base 100) = Some W_6cc64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_6cc68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_6cc6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo112 : fetch_word segs (at_ base 112) = Some W_6cc70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 28 _ HCODE eq_refl). Qed.
  Lemma Fo116 : fetch_word segs (at_ base 116) = Some W_6cc74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 29 _ HCODE eq_refl). Qed.
  Lemma Fo120 : fetch_word segs (at_ base 120) = Some W_6cc78.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 30 _ HCODE eq_refl). Qed.
  Lemma Fo124 : fetch_word segs (at_ base 124) = Some W_6cc7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 31 _ HCODE eq_refl). Qed.
  Lemma Fo128 : fetch_word segs (at_ base 128) = Some W_6cc80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 32 _ HCODE eq_refl). Qed.
  Lemma Fo132 : fetch_word segs (at_ base 132) = Some W_6cc84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 33 _ HCODE eq_refl). Qed.
  Lemma Fo136 : fetch_word segs (at_ base 136) = Some W_6cc88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 34 _ HCODE eq_refl). Qed.
  Lemma Fo140 : fetch_word segs (at_ base 140) = Some W_6cc8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 35 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo152 : fetch_word segs (at_ base 152) = Some W_6cc98.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 38 _ HCODE eq_refl). Qed.
  Lemma Fo156 : fetch_word segs (at_ base 156) = Some W_6cc9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 39 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_6cca0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_6cca4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_6cca8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_6ccac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_6ccb0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_6ccb4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo184 : fetch_word segs (at_ base 184) = Some W_6ccb8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 46 _ HCODE eq_refl). Qed.
  Lemma Fo188 : fetch_word segs (at_ base 188) = Some W_6ccbc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 47 _ HCODE eq_refl). Qed.
  Lemma Fo192 : fetch_word segs (at_ base 192) = Some W_6ccc0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 48 _ HCODE eq_refl). Qed.
  Lemma Fo196 : fetch_word segs (at_ base 196) = Some W_6ccc4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 49 _ HCODE eq_refl). Qed.
  Lemma Fo200 : fetch_word segs (at_ base 200) = Some W_6ccc8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 50 _ HCODE eq_refl). Qed.
  Lemma Fo204 : fetch_word segs (at_ base 204) = Some W_6cccc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 51 _ HCODE eq_refl). Qed.
  Lemma Fo208 : fetch_word segs (at_ base 208) = Some W_6ccd0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 52 _ HCODE eq_refl). Qed.
  Lemma Fo212 : fetch_word segs (at_ base 212) = Some W_6ccd4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 53 _ HCODE eq_refl). Qed.
  Lemma Fo216 : fetch_word segs (at_ base 216) = Some W_6ccd8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 54 _ HCODE eq_refl). Qed.
  Lemma Fo220 : fetch_word segs (at_ base 220) = Some W_6ccdc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 55 _ HCODE eq_refl). Qed.
  Lemma Fo224 : fetch_word segs (at_ base 224) = Some W_6cce0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 56 _ HCODE eq_refl). Qed.
  Lemma Fo228 : fetch_word segs (at_ base 228) = Some W_6cce4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo232 : fetch_word segs (at_ base 232) = Some W_6cce8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo236 : fetch_word segs (at_ base 236) = Some W_6ccec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo240 : fetch_word segs (at_ base 240) = Some W_6ccf0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo244 : fetch_word segs (at_ base 244) = Some W_6ccf4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 61 _ HCODE eq_refl). Qed.
  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_6ccf8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_6ccfc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_6cd00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_6cd04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_6cd08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_6cd0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_6cd10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_6cd14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 69 _ HCODE eq_refl). Qed.
  Lemma Fo280 : fetch_word segs (at_ base 280) = Some W_6cd18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 70 _ HCODE eq_refl). Qed.
  Lemma Fo284 : fetch_word segs (at_ base 284) = Some W_6cd1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 71 _ HCODE eq_refl). Qed.
  Lemma Fo288 : fetch_word segs (at_ base 288) = Some W_6cd20.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 72 _ HCODE eq_refl). Qed.
  Lemma Fo292 : fetch_word segs (at_ base 292) = Some W_6cd24.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 73 _ HCODE eq_refl). Qed.
  Lemma Fo296 : fetch_word segs (at_ base 296) = Some W_6cd28.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 74 _ HCODE eq_refl). Qed.
  Lemma Fo300 : fetch_word segs (at_ base 300) = Some W_6cd2c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 75 _ HCODE eq_refl). Qed.
  Lemma Fo304 : fetch_word segs (at_ base 304) = Some W_6cd30.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 76 _ HCODE eq_refl). Qed.
  Lemma Fo308 : fetch_word segs (at_ base 308) = Some W_6cd34.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 77 _ HCODE eq_refl). Qed.







  Lemma Fo348 : fetch_word segs (at_ base 348) = Some W_6cd5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 87 _ HCODE eq_refl). Qed.

  Lemma Fo356 : fetch_word segs (at_ base 356) = Some W_6cd64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 89 _ HCODE eq_refl). Qed.

  Lemma Fo364 : fetch_word segs (at_ base 364) = Some W_6cd6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 91 _ HCODE eq_refl). Qed.



  Lemma Fo380 : fetch_word segs (at_ base 380) = Some W_6cd7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 95 _ HCODE eq_refl). Qed.
  Lemma Fo384 : fetch_word segs (at_ base 384) = Some W_6cd80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 96 _ HCODE eq_refl). Qed.
  Lemma Fo388 : fetch_word segs (at_ base 388) = Some W_6cd84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 97 _ HCODE eq_refl). Qed.

  Lemma Fo396 : fetch_word segs (at_ base 396) = Some W_6cd8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 99 _ HCODE eq_refl). Qed.
  Lemma Fo400 : fetch_word segs (at_ base 400) = Some W_6cd90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 100 _ HCODE eq_refl). Qed.
  Lemma Fo404 : fetch_word segs (at_ base 404) = Some W_6cd94.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 101 _ HCODE eq_refl). Qed.
  Lemma Fo408 : fetch_word segs (at_ base 408) = Some W_6cd98.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 102 _ HCODE eq_refl). Qed.
  Lemma Fo412 : fetch_word segs (at_ base 412) = Some W_6cd9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 103 _ HCODE eq_refl). Qed.
  Lemma Fo416 : fetch_word segs (at_ base 416) = Some W_6cda0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 104 _ HCODE eq_refl). Qed.
  Lemma Fo420 : fetch_word segs (at_ base 420) = Some W_6cda4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 105 _ HCODE eq_refl). Qed.
  Lemma Fo424 : fetch_word segs (at_ base 424) = Some W_6cda8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 106 _ HCODE eq_refl). Qed.
  Lemma Fo428 : fetch_word segs (at_ base 428) = Some W_6cdac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 107 _ HCODE eq_refl). Qed.
  Lemma Fo432 : fetch_word segs (at_ base 432) = Some W_6cdb0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 108 _ HCODE eq_refl). Qed.
  Lemma Fo436 : fetch_word segs (at_ base 436) = Some W_6cdb4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 109 _ HCODE eq_refl). Qed.
  Lemma Fo440 : fetch_word segs (at_ base 440) = Some W_6cdb8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 110 _ HCODE eq_refl). Qed.
  Lemma Fo444 : fetch_word segs (at_ base 444) = Some W_6cdbc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 111 _ HCODE eq_refl). Qed.
  Lemma Fo448 : fetch_word segs (at_ base 448) = Some W_6cdc0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 112 _ HCODE eq_refl). Qed.
  Lemma Fo452 : fetch_word segs (at_ base 452) = Some W_6cdc4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 113 _ HCODE eq_refl). Qed.
  Lemma Fo456 : fetch_word segs (at_ base 456) = Some W_6cdc8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 114 _ HCODE eq_refl). Qed.
  Lemma Fo460 : fetch_word segs (at_ base 460) = Some W_6cdcc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 115 _ HCODE eq_refl). Qed.
  Lemma Fo464 : fetch_word segs (at_ base 464) = Some W_6cdd0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 116 _ HCODE eq_refl). Qed.
  Lemma Fo468 : fetch_word segs (at_ base 468) = Some W_6cdd4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 117 _ HCODE eq_refl). Qed.
  Lemma Fo472 : fetch_word segs (at_ base 472) = Some W_6cdd8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 118 _ HCODE eq_refl). Qed.
  Lemma Fo476 : fetch_word segs (at_ base 476) = Some W_6cddc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 119 _ HCODE eq_refl). Qed.
  Lemma Fo480 : fetch_word segs (at_ base 480) = Some W_6cde0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 120 _ HCODE eq_refl). Qed.
  Lemma Fo484 : fetch_word segs (at_ base 484) = Some W_6cde4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 121 _ HCODE eq_refl). Qed.
  Lemma Fo488 : fetch_word segs (at_ base 488) = Some W_6cde8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 122 _ HCODE eq_refl). Qed.
  Lemma Fo492 : fetch_word segs (at_ base 492) = Some W_6cdec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 123 _ HCODE eq_refl). Qed.
  Lemma Fo496 : fetch_word segs (at_ base 496) = Some W_6cdf0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 124 _ HCODE eq_refl). Qed.
  Lemma Fo500 : fetch_word segs (at_ base 500) = Some W_6cdf4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 125 _ HCODE eq_refl). Qed.
  Lemma Fo504 : fetch_word segs (at_ base 504) = Some W_6cdf8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 126 _ HCODE eq_refl). Qed.
  Lemma Fo508 : fetch_word segs (at_ base 508) = Some W_6cdfc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 127 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo520 : fetch_word segs (at_ base 520) = Some W_6ce08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 130 _ HCODE eq_refl). Qed.

  Lemma Fo528 : fetch_word segs (at_ base 528) = Some W_6ce10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 132 _ HCODE eq_refl). Qed.
  Lemma Fo532 : fetch_word segs (at_ base 532) = Some W_6ce14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 133 _ HCODE eq_refl). Qed.



  Lemma Fo548 : fetch_word segs (at_ base 548) = Some W_6ce24.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 137 _ HCODE eq_refl). Qed.
  Lemma Fo552 : fetch_word segs (at_ base 552) = Some W_6ce28.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 138 _ HCODE eq_refl). Qed.
  Lemma Fo556 : fetch_word segs (at_ base 556) = Some W_6ce2c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 139 _ HCODE eq_refl). Qed.
  Lemma Fo560 : fetch_word segs (at_ base 560) = Some W_6ce30.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 amset_words 140 _ HCODE eq_refl). Qed.




  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables dst cv ra sp : word.
  Variable n : Z.
  Variable fl : byte.
  Variable regs : bvmap 5 word.
  Hypothesis Hsp : (0x10007fff8000 + 2304 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  (* [comment removed for export] *)
  Definition AM1 : word -> option byte :=
    ps_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21).
  (* [comment removed for export] *)
  Definition AM2 : word -> option byte :=
    rip_mem rt AM1 (at_ sp (-2128)) (at_ base 488) sp dst (Z_to_bv 64 n) (getr regs 19) (at_ sp (-2128)) cv dst (Z_to_bv 64 n).
  (* [comment removed for export] *)
  Definition amset_post (M : word -> option byte) : word -> option byte := wbytes M dst (repeat (cbyte cv) (Z.to_nat n)).

  Lemma AM1_out : forall x : word, (U x < U sp - 56 \/ U sp <= U x)%Z -> AM1 x = mem x.
  Proof using Hsp base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold AM1, ps_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma AM1_low : forall x : word, (U x < U sp - 2208)%Z -> AM1 x = mem x.
  Proof using Hsp base. intros x Hx. apply AM1_out. lia. Qed.
  Lemma AM1_grows : mem_grows mem AM1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold AM1, ps_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma AM2_low : forall x : word, (U x < U sp - 2208)%Z -> AM2 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold AM2 in G in change_no_check G' end). rewrite rip_mem_outside; [apply AM1_low; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.
  Lemma AM2_grows : mem_grows mem AM2.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold AM2, rip_mem, ps_frame in G in change_no_check G' end). eapply mem_grows_trans; [apply AM1_grows|].
    destruct (Z.ltb _ _);
      repeat (lazymatch goal with
              | |- mem_grows ?a ?a => apply mem_grows_refl
              | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
              end).
  Qed.

  Lemma rd_o : forall (M : word -> option byte) (B : Z) (a : word) k bs0,
    (forall x : word, (U x < B)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= B)%Z -> (B <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M B a k bs0 HM Ha HB Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply HM. lia.
  Qed.

  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hend : (U dst + n <= 2 ^ 47)%Z.
  Hypothesis Rgf : rdn segs mem (Z_to_bv 64 g_flag) 8 = Some (LE8 (Z_to_bv 64 p_flag)).
  Hypothesis Rfl : rdn segs mem (Z_to_bv 64 p_flag) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Rrms : rdn segs mem (Z_to_bv 64 c_rms) 8 = Some (LE8 mset).
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2208)%Z (g_flag :: p_flag :: c_rms :: m2s_cells (rt_m2s rt)).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2208)) 2208 = true.
  Hypothesis Hdok : store_ok segs mem dst (Z.to_nat n) = true.
  Hypothesis Hdst_stk : (n = 0 \/ U dst + n <= U sp - 2208 \/ U sp <= U dst)%Z.   (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ra.
  Hypothesis R1 : getr regs 1 = ra.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = dst.
  Hypothesis R11 : getr regs 11 = cv.
  Hypothesis R12 : getr regs 12 = Z_to_bv 64 n.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold m2s_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-2208)) _ 2208);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close LOW Hr :=
    apply (rd_o _ _ _ _ _ LOW);
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | lia
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cldb F D bb LOW Hr :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := bb);
        [exact F | reflexivity | exact D | addr_n; rd_close LOW Hr]
      | step_simpl]; vn.
  Ltac gl G LOW Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_o _ _ _ _ _ LOW); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | lia | exact Hr] | ]; zlit_at.

  #[local] Abbreviation CLX := (fun r : reg => In r [2; 8; 20; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31; 1; 9; 18; 19; 21]%list).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkA0 :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 72) AM1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-2128) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = cv
      /\ getr r 12 = Z_to_bv 64 n /\ getr r 20 = at_ sp (-2128)
      /\ (forall i : reg, In i [9; 18; 19; 21; 22; 23; 24; 25; 26; 27; 3; 4]%list -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using R12 R11 R10 R2 R1 Hstk Hcells Hfl Rfl Rgf Hend Hn Hsp fl G40 HCODE c_rms p_flag g_flag rt.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hd. pose proof (u8_range fl) as Hflr.
    cells_split.
    wd_eexists. split.
    - an Fo0 D_6cc00.                                    (* [comment removed for export] *)
      fsd Fo4 D_6cc04 (at_ sp (-8)).                     (* [comment removed for export] *)
      fsd Fo8 D_6cc08 (at_ sp (-16)).                    (* [comment removed for export] *)
      fsd Fo12 D_6cc0c (at_ sp (-24)).                   (* [comment removed for export] *)
      fsd Fo16 D_6cc10 (at_ sp (-32)).                   (* [comment removed for export] *)
      fsd Fo20 D_6cc14 (at_ sp (-40)).                   (* [comment removed for export] *)
      fsd Fo24 D_6cc18 (at_ sp (-48)).                   (* [comment removed for export] *)
      fsd Fo28 D_6cc1c (at_ sp (-56)).                   (* [comment removed for export] *)
      change (wbytes _ _ _) with AM1.
      an Fo32 D_6cc20.                                   (* [comment removed for export] *)
      an Fo36 D_6cc24.                                   (* [comment removed for export] *)
      gl G40 AM1_low Rgf.                                  (* [comment removed for export] *)
      cldb Fo48 D_6cc30 fl AM1_low Rfl.                  (* [comment removed for export] *)
      ab_ft Fo52 D_6cc34 ltac:(condz).                 (* [comment removed for export] *)
      av Fo56 D_6cc38 (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).   (* [comment removed for export] *)
      an Fo60 D_6cc3c. an Fo64 D_6cc40.                  (* [comment removed for export] *)
      ab_ft Fo68 D_6cc44 ltac:(condz).                 (* [comment removed for export] *)
      wd_refl.
    - post; rewrite ?at_0; try reflexivity.
      + intros i Hi. cbn [In] in Hi. repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]). destruct Hi.
      + ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkA1s : forall r0, (1 <= n <= 64)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 72) AM1 rom) (mkst r (at_ base 84) AM1 rom)
      /\ regs_agree (fun x => In x [13; 14]%list) r0 r.
  Proof using Hn HCODE.
    intros r0 Hs R12'. wd_eexists. split.
    - av Fo72 D_6cc48 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).  (* [comment removed for export] *)
      an Fo76 D_6cc4c.                                   (* [comment removed for export] *)
      ab_ft Fo80 D_6cc50 ltac:(condz).                 (* [comment removed for export] *)
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkA1z : forall r0, n = 0%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 72) AM1 rom) (mkst r (at_ base 144) AM1 rom)
      /\ regs_agree (fun x => In x [13; 14]%list) r0 r.
  Proof using Hn HCODE.
    intros r0 Hz R12'. wd_eexists. split.
    - av Fo72 D_6cc48 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).  (* [comment removed for export] *)
      an Fo76 D_6cc4c.                                   (* [comment removed for export] *)
      ab_tk Fo80 D_6cc50 ltac:(condz).                 (* [comment removed for export] *)
      ab_ft Fo408 D_6cd98 ltac:(condz).                (* [comment removed for export] *)
      an Fo412 D_6cd9c.                                  (* [comment removed for export] *)
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkA1b : forall r0, (65 <= n)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 72) AM1 rom) (mkst r (at_ base 468) AM1 rom)
      /\ regs_agree (fun x => In x [13; 14]%list) r0 r.
  Proof using Hend Hn Hsp dst HCODE.
    intros r0 Hb R12'. pose proof (u64_range dst) as Hd.
    wd_eexists. split.
    - av Fo72 D_6cc48 (Z_to_bv 64 (n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      an Fo76 D_6cc4c.                                   (* [comment removed for export] *)
      ab_tk Fo80 D_6cc50 ltac:(condz).                 (* [comment removed for export] *)
      ab_tk Fo408 D_6cd98 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma qc1H_AM1 : forall w0 w1 s1,
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 -> qc1H segs AM1 dst n g_shoff p_shoff w0 w1 s1.
  Proof using Hcells Hend Hsp c_rms p_flag g_flag base.
    intros w0 w1 s1 [Q1 Q2 Q3 Q4 [Q5 Q6] Q7 Q8 Q9 Q10 Q11].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hd. cells_split.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U dst) ltac:(lia)) as S0. pose proof (HSh (U dst + n - 1)%Z ltac:(lia)) as S1.
    assert (D0 : (Sh (U dst) - 7 <= down8 (Sh (U dst)) <= Sh (U dst))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U dst)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U dst)) 8 ltac:(lia)); lia).
    assert (D1 : (Sh (U dst + n - 1) - 7 <= down8 (Sh (U dst + n - 1)) <= Sh (U dst + n - 1))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U dst + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U dst + n - 1)) 8 ltac:(lia)); lia).
    Ltac ro Hr := apply (rd_o _ _ _ _ _ AM1_low); [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | lia | exact Hr].
    split; try assumption.
    - ro Q3. - ro Q4. - split; assumption. - ro Q7. - ro Q8. - ro Q9.
    - intros a Ha. pose proof (u64_range a). apply (rd_o _ _ _ _ _ AM1_low); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia | exact (Q11 a Ha)].
  Qed.

  Lemma blkQ : forall r0 w0 w1 s1,
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 ->
    getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 84) AM1 rom) (mkst r (at_ base 144) AM1 rom)
      /\ regs_agree (fun x => In x qc1_clob) r0 r.
  Proof using Hcells Hend Hsp B464 B140 G84 QCS QCF c_rms p_flag g_flag.
    intros r0 w0 w1 s1 QH R10' R12'. pose proof (u64_range base).
    pose proof (qc1_pass segs (at_ base 84) (at_ base 416) (at_ base 144) 10 g_shoff p_shoff QCF QCS G84
             ltac:(rewrite at_at; exact B140) ltac:(rewrite at_at; exact B464) ltac:(rewrite at_at; reflexivity)
             (or_introl eq_refl)
             r0 AM1 rom dst n w0 w1 s1 (qc1H_AM1 _ _ _ QH) R10' R12') as X.
    rewrite at_at, Z.add_0_r in X. exact X.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rd_outF : forall (M : word -> option byte) (a : word) k bs0,
    (forall x : word, (U x < U sp - 2208 \/ U sp <= U x)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= U sp - 2208 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M a k bs0 HM Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outZ : forall (M : word -> option byte) (c : Z) k bs0,
    (forall x : word, (U x < U sp - 2208 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= U sp - 2208)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using Hsp base.
    intros M c k bs0 HM Hc Hk Hr. pose proof (u64_range sp). apply (rd_outF M); try assumption; wd_ulia.
  Qed.
  Lemma AM1_agree : forall x : word, (U x < U sp - 2208 \/ U sp <= U x)%Z -> AM1 x = mem x.
  Proof using Hsp base. intros x Hx. apply AM1_out. lia. Qed.

  (* [comment removed for export] *)
  Lemma ripH_on : forall (M : word -> option byte) (raX : word) (s0 s1 : byte) (midend : word),
    (forall x : word, (U x < U sp - 2208 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0] -> (U s0 = 0 \/ U dst mod 8 < U s0 < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1] -> (U s1 = 0 \/ (U dst + n - 1) mod 8 < U s1 < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok raX ->
    ripH segs rt M dst (Z_to_bv 64 n) raX (at_ sp (-2128)) s0 s1 midend.
  Proof using Hdst_stk Hstk Hcells Hend Hn Hsp c_rms p_flag g_flag base.
    intros M raX s0 s1 midend HM HG Hn65 CH Hhi R0 H0 R1' H1' RZ HR.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hb.
    destruct CH as [C1 C2 C3 C4 C5 C6 C7 C8 CC Clo Chi]. cells_split.
    assert (SH : forall x, (0 <= x < 0x800000000000)%Z -> (0x7fff8000 <= Sh x < 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8). pose proof (Z.div_lt_upper_bound x 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
    pose proof (SH (U dst) ltac:(lia)) as S0.
    pose proof (SH (U dst + n - 1)%Z ltac:(lia)) as S1.
    assert (UP : (U dst <= up8 (U dst) <= U dst + 7)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); pose proof (Z.div_mod (U dst + 7) 8); pose proof (Z.mod_pos_bound (U dst + 7) 8); lia).
    assert (DN : (U dst + n - 7 <= down8 (U dst + n) <= U dst + n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (U dst + n) 8); pose proof (Z.mod_pos_bound (U dst + n) 8); lia).
    pose proof (SH (up8 (U dst)) ltac:(lia)) as S2. pose proof (SH (down8 (U dst + n)) ltac:(lia)) as S3.
    assert (Un : U (Z_to_bv 64 n) = n) by (apply u_Z2bv; lia).
    Ltac rdo HMx Hr := apply (rd_outZ _ _ _ _ HMx); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
    split.
    - split; [rdo HM C1 | rdo HM C2 | rdo HM C3 | rdo HM C4 | rdo HM C5 | rdo HM C6 | rdo HM C7 | rdo HM C8 | exact CC | lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat constructor; rewrite ?at_u; lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rdo HM R0.
    - exact H0.
    - rewrite Un. rdo HM R1'.
    - rewrite Un. exact H1'.
    - rewrite Un. intros a Ha. pose proof (u64_range a). pose proof (RZ a Ha) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ra |- *. rdo HM Ra.
    - rewrite at_u by lia. lia.
    - rewrite at_at. replace (-2128 + -80)%Z with (-2208)%Z by lia. eapply store_ok_mono; [exact HG|].
      eapply (store_ok_sub segs mem (at_ sp (-2208)) _ 2208); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - exact HR.
  Qed.

  Lemma blkR : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0b] -> (U s0b = 0 \/ U dst mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U dst + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2128) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = cv -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 19 = getr regs 19 -> getr r0 20 = at_ sp (-2128) ->
    exists r, msteps segs (mkst r0 (at_ base 468) AM1 rom) (mkst r (at_ base 144) AM2 rom)
      /\ getr r 2 = at_ sp (-2128) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = cv /\ getr r 12 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x ([1; 9; 18; 19; 21]%list ++ rip_clob)) r0 r.
  Proof using Hdst_stk Hstk Hcells Hend Hn Hsp Hbase RTB RTOK HCODE c_rms p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hhi Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R19' R20'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 488)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    (* [comment removed for export] *)
    set (r1 := regupd (regupd (regupd (regupd (regupd r0 9 dst) 21 cv) 11 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 1 (at_ base 488)).
    destruct (region_clear segs rt RTOK AM1 rom dst (Z_to_bv 64 n) (at_ base 488) (at_ sp (-2128)) s0b s1b midend r1
                (ripH_on AM1 (at_ base 488) s0b s1b midend AM1_agree AM1_grows Hn65 CH Hhi Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; exact R10' | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo468 D_6cdd4.                                  (* [comment removed for export] *)
      an Fo472 D_6cdd8.                                  (* [comment removed for export] *)
      an Fo476 D_6cddc.                                  (* [comment removed for export] *)
      an Fo480 D_6cde0.                                  (* [comment removed for export] *)
      an Fo484 D_6cde4.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt AM1 (at_ sp (-2128)) (at_ base 488) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) dst (Z_to_bv 64 n))
         with AM2.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold AM2 in G in change_no_check G' end). subst r1. gres. rewrite R8', R19', R20'. reflexivity. }
      assert (A9 : getr r2 9 = dst) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      assert (A21 : getr r2 21 = cv) by (rewrite (AG2 21) by notin; subst r1; gres; reflexivity).
      assert (A18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (AG2 18) by notin; subst r1; gres; reflexivity).
      an Fo488 D_6cde8.                                  (* [comment removed for export] *)
      an Fo492 D_6cdec.                                  (* [comment removed for export] *)
      an Fo496 D_6cdf0.                                  (* [comment removed for export] *)
      an Fo500 D_6cdf4.                                  (* [comment removed for export] *)
      ab_tk Fo504 D_6cdf8 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2128)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      assert (A8 : getr r2 8 = sp) by (rewrite (AG2 8) by notin; subst r1; gres; exact R8').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 19 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 18 /\ x <> 11 /\ x <> 21 /\ x <> 9) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition am_slots : list (Z * word) :=
    [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21)]%Z.

  Lemma slots_AM1 : forall (k : Z) (v : word), In (k, v) am_slots -> rdn segs AM1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp base.
    intros k v Hin. pose proof (u64_range sp). unfold am_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold AM1, ps_frame in G in change_no_check G' end); rd8_chain|]). destruct Hin.
  Qed.

  Lemma slots_AM2 : forall (k : Z) (v : word), In (k, v) am_slots -> rdn segs AM2 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp).
    assert (Hk : (-56 <= k /\ k + 8 <= 0)%Z).
    { unfold am_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_AM1 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold AM2 in G in change_no_check G' end). apply rip_mem_outside; rewrite at_u; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma slots_post : forall (M : word -> option byte) (k : Z) (v : word),
    (forall k' v', In (k', v') am_slots -> rdn segs M (at_ sp k') 8 = Some (word_to_le_bytes 8 v')) ->
    In (k, v) am_slots -> rdn segs (amset_post M) (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hdst_stk Hend Hn Hsp base.
    intros M k v HM Hin. pose proof (u64_range sp). pose proof (u64_range dst).
    assert (Hk : (-56 <= k /\ k + 8 <= 0)%Z).
    { unfold am_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    (lazymatch goal with |- ?G => let G' := eval unfold amset_post in G in change_no_check G' end). destruct (Z.eq_dec n 0) as [E0 | NZ0].
    { rewrite E0. (lazymatch goal with |- ?G => let G' := eval cbn [Z.to_nat repeat wbytes] in G in change_no_check G' end). exact (HM k v Hin). }
    rewrite rdn_wbytes_out; [exact (HM k v Hin) | rewrite repeat_length, at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite repeat_length; lia].
  Qed.

  Lemma blkC : forall (M : word -> option byte) r0,
    (forall x : word, (U x < U sp - 2208)%Z -> M x = mem x) -> mem_grows mem M ->
    (forall k v, In (k, v) am_slots -> rdn segs M (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    getr r0 2 = at_ sp (-2128) -> getr r0 10 = dst -> getr r0 11 = cv -> getr r0 12 = Z_to_bv 64 n ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 144) M rom) (mkst r ra (amset_post M) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R2 Hret Hdst_stk Hdok Hcells Rrms Hend Hn Hsp Hmset Hbase G144 MSC HCODE c_rms p_flag g_flag mset rt.
    intros M r0 HM HG SL R2' R10' R11' R12' AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range dst) as Hd. cells_split.
    assert (RA : ret_ok (at_ base 156)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    assert (OKM : store_ok segs M dst (Z.to_nat n) = true) by (eapply store_ok_mono; [exact HG | exact Hdok]).
    (* [comment removed for export] *)
    set (r1 := regupd (regupd r0 13 mset) 1 (at_ base 156)).
    destruct (memset_summary segs mset MSC M dst cv (at_ base 156) n rom Hn ltac:(lia) OKM RA r1)
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; exact R10' | subst r1; gres; exact R11' | subst r1; gres; exact R12' | subst r1; gres; reflexivity |].
    assert (A2 : getr r2 2 = at_ sp (-2128)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
    pose proof (fun k v H => slots_post M k v SL H) as SLP. unfold am_slots in SLP.
    Ltac fldM F D vv SLP :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply SLP; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - gl G144 HM Rrms.                                   (* [comment removed for export] *)
      aret Fo152 D_6cc98 mset.                           (* [comment removed for export] *)
      rewrite at_addi; zlit_at. change (regupd _ 1 _) with r1. rewrite <- (at_0 mset).
      eapply msteps_trans; [exact RUN2|].
      an Fo156 D_6cc9c.                                  (* [comment removed for export] *)
      fldM Fo160 D_6cca0 ra SLP.                         (* [comment removed for export] *)
      fldM Fo164 D_6cca4 (getr regs 8) SLP.              (* [comment removed for export] *)
      fldM Fo168 D_6cca8 (getr regs 9) SLP.
      fldM Fo172 D_6ccac (getr regs 18) SLP.
      fldM Fo176 D_6ccb0 (getr regs 19) SLP.
      fldM Fo180 D_6ccb4 (getr regs 20) SLP.
      fldM Fo184 D_6ccb8 (getr regs 21) SLP.
      an Fo188 D_6ccbc.                                  (* [comment removed for export] *)
      aret Fo192 D_6ccc0 ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact A10.
    - intros x Hx. unfold amset_saved in Hx. cbn [In] in Hx. gres.
      repeat (destruct Hx as [<-|Hx];
        [ gres; rwH; rewrite ?at_addi, ?at_0; first
            [ reflexivity
            | f_equal; lia
            | rewrite (AG2 _) by notin; subst r1; gres; rewrite ?(AG0 _) by notin; first [reflexivity | assumption | rwH; rewrite ?at_addi; f_equal; lia] ]
        |]).
      destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac regx AG x := rewrite (AG x) by notin.

  (* [comment removed for export] *)
  Theorem amset_zero : n = 0%Z ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (amset_post AM1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hdok Hstk Hcells Rrms Hfl Rfl Rgf Hend Hn Hsp fl Hmset Hbase G144 G40 MSC HCODE c_rms p_flag g_flag mset rt.
    intros Hz.
    destruct blkA0 as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & AK & AG1).
    destruct (blkA1z r1 Hz A12) as (r2 & RUN2 & AG2).
    destruct (blkC AM1 r2 AM1_low AM1_grows slots_AM1) as (r3 & RUN3 & B10 & BK);
      [regx AG2 (2 : reg); exact A2 | regx AG2 (10 : reg); exact A10 | regx AG2 (11 : reg); exact A11 | regx AG2 (12 : reg); exact A12
      | intros x Hx; rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; clear - Hc; cbn in Hc |- *; tauto] |].
    exists r3. split; [|split; [exact B10 | exact BK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
  Qed.

  (* [comment removed for export] *)
  Theorem amset_small : forall w0 w1 s1, (1 <= n <= 64)%Z ->
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (amset_post AM1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hdok Hstk Hcells Rrms Hfl Rfl Rgf Hend Hn Hsp fl Hmset Hbase B464 B140 G144 G84 G40 QCS QCF MSC HCODE c_rms p_flag g_flag mset.
    intros w0 w1 s1 Hs QH.
    destruct blkA0 as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & AK & AG1).
    destruct (blkA1s r1 Hs A12) as (r2 & RUN2 & AG2).
    destruct (blkQ r2 w0 w1 s1 QH) as (r3 & RUN3 & AG3); [regx AG2 (10 : reg); exact A10 | regx AG2 (12 : reg); exact A12 |].
    destruct (blkC AM1 r3 AM1_low AM1_grows slots_AM1) as (r4 & RUN4 & B10 & BK);
      [ regx AG3 (2 : reg); regx AG2 (2 : reg); exact A2 | regx AG3 (10 : reg); regx AG2 (10 : reg); exact A10
      | regx AG3 (11 : reg); regx AG2 (11 : reg); exact A11 | regx AG3 (12 : reg); regx AG2 (12 : reg); exact A12
      | intros x Hx; rewrite (AG3 x); [rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; clear - Hc; cbn in Hc |- *; tauto]
                               | intros Hc; apply Hx; clear - Hc; cbn in Hc |- *; tauto] |].
    exists r4. split; [|split; [exact B10 | exact BK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.

  (* [comment removed for export] *)
  Theorem amset_big : forall (s0b s1b : byte) (midend : word), (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0b] -> (U s0b = 0 \/ U dst mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U dst + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (amset_post AM2) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hdok Hstk Hcells Rrms Hfl Rfl Rgf Hend Hn Hsp fl Hmset Hbase G144 G40 MSC RTB RTOK HCODE c_rms p_flag g_flag mset.
    intros s0b s1b midend Hb CH Hhi Rs0 Hs0 Rs1 Hs1 Rz.
    destruct blkA0 as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & AK & AG1).
    destruct (blkA1b r1 ltac:(lia) A12) as (r2 & RUN2 & AG2).
    destruct (blkR r2 s0b s1b midend Hb CH Hhi Rs0 Hs0 Rs1 Hs1 Rz) as (r3 & RUN3 & B2 & B8 & B10 & B11 & B12 & AG3);
      [ regx AG2 (2 : reg); exact A2 | regx AG2 (8 : reg); exact A8 | regx AG2 (10 : reg); exact A10 | regx AG2 (11 : reg); exact A11 | regx AG2 (12 : reg); exact A12
      | regx AG2 (19 : reg); apply AK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | regx AG2 (20 : reg); exact A20 |].
    destruct (blkC AM2 r3 AM2_low AM2_grows slots_AM2 B2 B10 B11 B12) as (r4 & RUN4 & C10 & CK).
    { intros x Hx. rewrite (AG3 x). 1: rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; clear - Hc; cbn in Hc |- *; tauto].
      intros Hc. apply Hx. clear - Hc. apply in_app_or in Hc. cbn in Hc |- *. tauto. }
    exists r4. split; [|split; [exact C10 | exact CK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.

End AMSET.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record amsetH (segs : list Segment) (t : amset_tab) (mem : word -> option byte)
       (dst cv : word) (n : Z) (ra sp : word) (fl : byte) : Prop := AMSETH {
  amh_n : (0 <= n)%Z;
  amh_end : (bv_unsigned dst + n <= 2 ^ 47)%Z;
  amh_gf : rdn segs mem (Z_to_bv 64 (am_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (am_p_flag t)));
  amh_fl : rdn segs mem (Z_to_bv 64 (am_p_flag t)) 1 = Some [fl];
  amh_flnz : bv_unsigned fl <> 0%Z;
  amh_rms : rdn segs mem (Z_to_bv 64 (am_c_rms t)) 8 = Some (word_to_le_bytes 8 (am_mset t));
  amh_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 2208)%Z
                (am_g_flag t :: am_p_flag t :: am_c_rms t :: m2s_cells (rt_m2s (am_rip t)));
  amh_sp : (0x10007fff8000 + 2304 <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 <= 2 ^ 47)%Z;
  amh_stk : store_ok segs mem (at_ sp (-2208)) 2208 = true;
  amh_dok : store_ok segs mem dst (Z.to_nat n) = true;
  amh_dst_stk : (n = 0 \/ bv_unsigned dst + n <= bv_unsigned sp - 2208 \/ bv_unsigned sp <= bv_unsigned dst)%Z;
  amh_ret : ret_ok ra }.

Section PKG.
  Variable segs : list Segment.
  Variable t : amset_tab.
  Hypothesis TOK : amset_tab_ok segs t.
  #[local] Abbreviation PM1 mem ra sp regs := (AM1 mem ra sp regs).
  #[local] Abbreviation PM2 mem dst cv ra sp n regs := (AM2 (am_base t) (am_rip t) mem dst cv ra sp n regs).

  Theorem asan_memset_intrin_zero : forall mem rom (dst cv ra sp : word) (n : Z) (fl : byte) regs,
    amsetH segs t mem dst cv n ra sp fl -> n = 0%Z ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (am_base t) mem rom) (mkst r ra (amset_post dst cv n (AM1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst cv ra sp n fl regs [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hz R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].
    replace (mkst regs (am_base t) mem rom) with (mkst regs (at_ (am_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply amset_zero.
    all: lazymatch goal with
         | |- store_ok _ _ (at_ _ _) _ = true => exact P9
         | |- store_ok _ _ _ _ = true => exact P10
         | |- Forall _ _ => exact P7
         | _ => first [eassumption | reflexivity]
         end.
  Qed.

  Theorem asan_memset_intrin_small : forall mem rom (dst cv ra sp : word) (n : Z) (fl : byte) regs w0 w1 s1,
    amsetH segs t mem dst cv n ra sp fl -> (1 <= n <= 64)%Z ->
    qc1H segs mem dst n (mt_g_shoff (rt_m2s (am_rip t))) (mt_p_shoff (rt_m2s (am_rip t))) w0 w1 s1 ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (am_base t) mem rom) (mkst r ra (amset_post dst cv n (AM1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst cv ra sp n fl regs w0 w1 s1 [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hs QH R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].
    replace (mkst regs (am_base t) mem rom) with (mkst regs (at_ (am_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply amset_small.
    all: lazymatch goal with
         | |- store_ok _ _ (at_ _ _) _ = true => exact P9
         | |- store_ok _ _ _ _ = true => exact P10
         | |- Forall _ _ => exact P7
         | _ => first [eassumption | reflexivity]
         end.
  Qed.

  Theorem asan_memset_intrin_big : forall mem rom (dst cv ra sp : word) (n : Z) (fl : byte) regs (s0b s1b : byte) (midend : word),
    amsetH segs t mem dst cv n ra sp fl -> (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s (am_rip t)) mem dst midend ->
    ((0x10007fff8000 <= bv_unsigned dst /\ bv_unsigned dst + n + 1 <= 0x800000000000) \/ bv_unsigned dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned dst))) 1 = Some [s0b] -> (bv_unsigned s0b = 0 \/ bv_unsigned dst mod 8 < bv_unsigned s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned dst + n - 1))) 1 = Some [s1b] ->
    (bv_unsigned s1b = 0 \/ (bv_unsigned dst + n - 1) mod 8 < bv_unsigned s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (bv_unsigned dst)) <= bv_unsigned a < Sh (down8 (bv_unsigned dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (am_base t) mem rom)
                  (mkst r ra (amset_post dst cv n (AM2 (am_base t) (am_rip t) mem dst cv ra sp n regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst cv ra sp n fl regs s0b s1b midend [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12] Hb CH Hhi Rs0 Hs0 Rs1 Hs1 Rz R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].
    replace (mkst regs (am_base t) mem rom) with (mkst regs (at_ (am_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply amset_big.
    all: lazymatch goal with
         | |- store_ok _ _ (at_ _ _) _ = true => exact P9
         | |- store_ok _ _ _ _ = true => exact P10
         | |- Forall _ _ => exact P7
         | _ => first [eassumption | reflexivity]
         end.
  Qed.
End PKG.
End FPGen1.
