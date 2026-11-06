(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero.
Import ListNotations.
Open Scope bv_scope.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

Lemma Z_to_bv64_addm' : forall z m, Z_to_bv 64 (z + 2 ^ 64 * m)%Z = Z_to_bv 64 z.
Proof using.
  intros z m. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.mul_comm, Z.mod_add by lia. reflexivity.
Qed.
Lemma ct_andi_m8 : forall x : word, v_andi x (-8) = Z_to_bv 64 (U x / 8 * 8)%Z.
Proof using.
  intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite land_m8 by lia. f_equal. pose proof (Z.div_mod (U x) 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition gbgeu (segs : list Segment) (p : word) (r1 r2 : reg) (tgt : word) : Prop :=
  forall regs mem rom,
    ((U (getr regs r1) < U (getr regs r2))%Z -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs (v_addi p 4) mem rom))
    /\ ((U (getr regs r2) <= U (getr regs r1))%Z -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs tgt mem rom)).
Lemma gbgeu_of : forall segs (p : word) w (r1 r2 : reg) (imm : bv 13) tgt,
  fetch_word segs p = Some w -> is_ecall w = false -> decode_any w = Some (Branch BC_GEU r1 r2 imm, 4%Z) ->
  btgt p (bv_signed imm) = tgt -> gbgeu segs p r1 r2 tgt.
Proof using.
  intros segs p w r1 r2 imm tgt F E D T regs mem rom. split; intros Hr.
  - eapply step_bgeu_ft; [exact F | exact E | exact D |]. (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end). apply Z.ltb_lt. exact Hr.
  - rewrite <- T. eapply step_bgeu_tk; [exact F | exact E | exact D |]. (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end). apply Z.ltb_ge. lia.
Qed.
Definition gbnez (segs : list Segment) (p : word) (r : reg) (tgt : word) : Prop :=
  forall regs mem rom,
    (getr regs r <> Z_to_bv 64 0 -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs tgt mem rom))
    /\ (getr regs r = Z_to_bv 64 0 -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs (v_addi p 4) mem rom)).
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
Definition gbeqz (segs : list Segment) (p : word) (r : reg) (tgt : word) : Prop :=
  forall regs mem rom,
    (getr regs r = Z_to_bv 64 0 -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs tgt mem rom))
    /\ (getr regs r <> Z_to_bv 64 0 -> RiscvSemantics.step segs (mkst regs p mem rom) = MachineOk (mkst regs (v_addi p 4) mem rom)).
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
Definition ctB_words : list (option (bv 32)) :=
  [
   Some W_5c884; Some W_5c888; None; None; None; Some W_5c898; Some W_5c89c; Some W_5c8a0; Some W_5c8a4;
   Some W_5c8a8; Some W_5c8ac; Some W_5c8b0; Some W_5c8b4; Some W_5c8b8; Some W_5c8bc; Some W_5c8c0; Some W_5c8c4;
   None
  ]%list.

(* [comment removed for export] *)
Definition ctA_words : list (option (bv 32)) :=
  [
   Some W_5f3a4; Some W_5f3a8; None; None; None; Some W_5f3b8; Some W_5f3bc; Some W_5f3c0; Some W_5f3c4;
   Some W_5f3c8; Some W_5f3cc; Some W_5f3d0; Some W_5f3d4; Some W_5f3d8; Some W_5f3dc; Some W_5f3e0; Some W_5f3e4;
   None
  ]%list.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section KB.
  Variables (segs : list Segment) (base : word) (g_shoff p_shoff : Z) (tbig tslow : word).
  Hypothesis HCODE : code_ato segs base 0 ctB_words.
  Hypothesis B8 : gbgeu segs (at_ base 8) 12 11 tbig.
  Hypothesis G12 : gload segs base 12 11 g_shoff.
  Hypothesis B68 : gbnez segs (at_ base 68) 14 tslow.
  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_5c884.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_5c888.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 1 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_5c898.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_5c89c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_5c8a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_5c8a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_5c8a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_5c8ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_5c8b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_5c8b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_5c8b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_5c8bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_5c8c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_5c8c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctB_words 16 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)

  Theorem chk_tail_B : forall regs mem rom (b : word) (n : Z),
    getr regs 18 = b -> getr regs 9 = Z_to_bv 64 n -> (1 <= n <= 64)%Z -> (U b + n <= 140737488355328)%Z ->
    (0 <= g_shoff /\ g_shoff + 8 <= 2 ^ 64)%Z -> (0 <= p_shoff /\ p_shoff + 8 <= 2 ^ 64)%Z ->
    rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (LE8 p_shoff) ->
    rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (LE8 2147450880) ->
    rdn segs mem (Z_to_bv 64 ((2147450880 + U b / 8) / 8 * 8)) 8 = Some (LE8 0) ->
    rdn segs mem (Z_to_bv 64 ((2147450880 + (U b + n - 1) / 8) / 8 * 8)) 8 = Some (LE8 0) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 72) mem rom)
      /\ regs_agree (fun x => In x [11; 12; 13; 14; 15]%list) regs r.
  Proof using B68 G12 B8 HCODE tslow tbig.
    intros regs mem rom b n Hb Hn Hn64 Hhi Gr Pr Rg Rp W0 W1.
    pose proof (u64_range b) as Hbr.
    pose proof (Z.div_pos (U b) 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_pos (U b + n - 1) 8 ltac:(lia) ltac:(lia)) as D1.
    pose proof (Z.div_lt_upper_bound (U b) 8 17592186044416 ltac:(lia) ltac:(lia)) as D2.
    pose proof (Z.div_lt_upper_bound (U b + n - 1) 8 17592186044416 ltac:(lia) ltac:(lia)) as D3.
    pose proof (Z.div_mod (2147450880 + U b / 8) 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound (2147450880 + U b / 8) 8 ltac:(lia)) as D5.
    pose proof (Z.div_mod (2147450880 + (U b + n - 1) / 8) 8 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound (2147450880 + (U b + n - 1) / 8) 8 ltac:(lia)) as D7.
    wd_eexists. split.
    - av Fo0 D_5c884 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm' (2 ^ 64 + n - 65) (-1)); f_equal; lia).  (* [comment removed for export] *)
      an Fo4 D_5c888.                                    (* [comment removed for export] *)
      chain_step; [reflexivity | apply (proj1 (B8 _ _ _)); gres; rwH; wd_ulia | ]; vn.                            (* [comment removed for export] *)
      eapply msteps_trans; [eapply G12; exact Rg|]; zlit_at.                                                           (* [comment removed for export] *)
      av Fo20 D_5c898 (Z_to_bv 64 (U b + n)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).                                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 2147450880) (v := Z_to_bv 64 2147450880);
          [exact Fo24 | reflexivity | exact D_5c89c | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rp | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                                                                (* [comment removed for export] *)
      av Fo28 D_5c8a0 (Z_to_bv 64 (U b / 8)) ltac:(apply v_srli_3).                                                    (* [comment removed for export] *)
      av Fo32 D_5c8a4 (Z_to_bv 64 (U b + n - 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).                            (* [comment removed for export] *)
      av Fo36 D_5c8a8 (Z_to_bv 64 ((U b + n - 1) / 8)) ltac:(rewrite v_srli_3; unorm; reflexivity).                   (* [comment removed for export] *)
      av Fo40 D_5c8ac (Z_to_bv 64 (2147450880 + U b / 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).                   (* [comment removed for export] *)
      av Fo44 D_5c8b0 (Z_to_bv 64 (2147450880 + (U b + n - 1) / 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).         (* [comment removed for export] *)
      av Fo48 D_5c8b4 (Z_to_bv 64 ((2147450880 + U b / 8) / 8 * 8)) ltac:(rewrite ct_andi_m8; unorm; reflexivity).   (* [comment removed for export] *)
      av Fo52 D_5c8b8 (Z_to_bv 64 ((2147450880 + (U b + n - 1) / 8) / 8 * 8)) ltac:(rewrite ct_andi_m8; unorm; reflexivity).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 0) (v := Z_to_bv 64 0);
          [exact Fo56 | reflexivity | exact D_5c8bc | gres; rwH; imm_norm; rewrite ?v_addi_0; exact W0 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                                                                (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 0) (v := Z_to_bv 64 0);
          [exact Fo60 | reflexivity | exact D_5c8c0 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact W1 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                                                                (* [comment removed for export] *)
      an Fo64 D_5c8c4.                                                                                                   (* [comment removed for export] *)
      chain_step; [reflexivity | apply (proj2 (B68 _ _ _)); gres; reflexivity | ]; vn.                                (* [comment removed for export] *)
      wd_refl.
    - ra_solve.
  Qed.
End KB.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KA.
  Variables (segs : list Segment) (base : word) (g_shoff p_shoff : Z) (tbig tok : word).
  Hypothesis HCODE : code_ato segs base 0 ctA_words.
  Hypothesis B8 : gbgeu segs (at_ base 8) 11 10 tbig.
  Hypothesis G12 : gload segs base 12 10 g_shoff.
  Hypothesis B68 : gbeqz segs (at_ base 68) 13 tok.
  Lemma Fa0 : fetch_word segs (at_ base 0) = Some W_5f3a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 0 _ HCODE eq_refl). Qed.
  Lemma Fa4 : fetch_word segs (at_ base 4) = Some W_5f3a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 1 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fa20 : fetch_word segs (at_ base 20) = Some W_5f3b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 5 _ HCODE eq_refl). Qed.
  Lemma Fa24 : fetch_word segs (at_ base 24) = Some W_5f3bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 6 _ HCODE eq_refl). Qed.
  Lemma Fa28 : fetch_word segs (at_ base 28) = Some W_5f3c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 7 _ HCODE eq_refl). Qed.
  Lemma Fa32 : fetch_word segs (at_ base 32) = Some W_5f3c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 8 _ HCODE eq_refl). Qed.
  Lemma Fa36 : fetch_word segs (at_ base 36) = Some W_5f3c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 9 _ HCODE eq_refl). Qed.
  Lemma Fa40 : fetch_word segs (at_ base 40) = Some W_5f3cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 10 _ HCODE eq_refl). Qed.
  Lemma Fa44 : fetch_word segs (at_ base 44) = Some W_5f3d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 11 _ HCODE eq_refl). Qed.
  Lemma Fa48 : fetch_word segs (at_ base 48) = Some W_5f3d4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 12 _ HCODE eq_refl). Qed.
  Lemma Fa52 : fetch_word segs (at_ base 52) = Some W_5f3d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 13 _ HCODE eq_refl). Qed.
  Lemma Fa56 : fetch_word segs (at_ base 56) = Some W_5f3dc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 14 _ HCODE eq_refl). Qed.
  Lemma Fa60 : fetch_word segs (at_ base 60) = Some W_5f3e0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 15 _ HCODE eq_refl). Qed.
  Lemma Fa64 : fetch_word segs (at_ base 64) = Some W_5f3e4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ctA_words 16 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)

  Theorem chk_tail_A : forall regs mem rom (b : word) (n : Z),
    getr regs 22 = b -> getr regs 23 = Z_to_bv 64 n -> (1 <= n <= 64)%Z -> (U b + n <= 140737488355328)%Z ->
    (0 <= g_shoff /\ g_shoff + 8 <= 2 ^ 64)%Z -> (0 <= p_shoff /\ p_shoff + 8 <= 2 ^ 64)%Z ->
    rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (LE8 p_shoff) ->
    rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (LE8 2147450880) ->
    rdn segs mem (Z_to_bv 64 ((2147450880 + U b / 8) / 8 * 8)) 8 = Some (LE8 0) ->
    rdn segs mem (Z_to_bv 64 ((2147450880 + (U b + n - 1) / 8) / 8 * 8)) 8 = Some (LE8 0) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r tok mem rom)
      /\ regs_agree (fun x => In x [10; 11; 12; 13; 14]%list) regs r.
  Proof using B68 G12 B8 HCODE tbig.
    intros regs mem rom b n Hb Hn Hn64 Hhi Gr Pr Rg Rp W0 W1.
    pose proof (u64_range b) as Hbr.
    pose proof (Z.div_pos (U b) 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_pos (U b + n - 1) 8 ltac:(lia) ltac:(lia)) as D1.
    pose proof (Z.div_lt_upper_bound (U b) 8 17592186044416 ltac:(lia) ltac:(lia)) as D2.
    pose proof (Z.div_lt_upper_bound (U b + n - 1) 8 17592186044416 ltac:(lia) ltac:(lia)) as D3.
    pose proof (Z.div_mod (2147450880 + U b / 8) 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound (2147450880 + U b / 8) 8 ltac:(lia)) as D5.
    pose proof (Z.div_mod (2147450880 + (U b + n - 1) / 8) 8 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound (2147450880 + (U b + n - 1) / 8) 8 ltac:(lia)) as D7.
    wd_eexists. split.
    - av Fa0 D_5f3a4 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm' (2 ^ 64 + n - 65) (-1)); f_equal; lia).  (* [comment removed for export] *)
      an Fa4 D_5f3a8.                                    (* [comment removed for export] *)
      chain_step; [reflexivity | apply (proj1 (B8 _ _ _)); gres; rwH; wd_ulia | ]; vn.                            (* [comment removed for export] *)
      eapply msteps_trans; [eapply G12; exact Rg|]; zlit_at.                                                           (* [comment removed for export] *)
      av Fa20 D_5f3b8 (Z_to_bv 64 (U b + n)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).                                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 2147450880) (v := Z_to_bv 64 2147450880);
          [exact Fa24 | reflexivity | exact D_5f3bc | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rp | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                                                                (* [comment removed for export] *)
      av Fa28 D_5f3c0 (Z_to_bv 64 (U b / 8)) ltac:(apply v_srli_3).                                                    (* [comment removed for export] *)
      av Fa32 D_5f3c4 (Z_to_bv 64 (U b + n - 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).                            (* [comment removed for export] *)
      av Fa36 D_5f3c8 (Z_to_bv 64 ((U b + n - 1) / 8)) ltac:(rewrite v_srli_3; unorm; reflexivity).                   (* [comment removed for export] *)
      av Fa40 D_5f3cc (Z_to_bv 64 (2147450880 + U b / 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).                   (* [comment removed for export] *)
      av Fa44 D_5f3d0 (Z_to_bv 64 (2147450880 + (U b + n - 1) / 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).         (* [comment removed for export] *)
      av Fa48 D_5f3d4 (Z_to_bv 64 ((2147450880 + U b / 8) / 8 * 8)) ltac:(rewrite ct_andi_m8; unorm; reflexivity).   (* [comment removed for export] *)
      av Fa52 D_5f3d8 (Z_to_bv 64 ((2147450880 + (U b + n - 1) / 8) / 8 * 8)) ltac:(rewrite ct_andi_m8; unorm; reflexivity).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 0) (v := Z_to_bv 64 0);
          [exact Fa56 | reflexivity | exact D_5f3dc | gres; rwH; imm_norm; rewrite ?v_addi_0; exact W0 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                                                                (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 0) (v := Z_to_bv 64 0);
          [exact Fa60 | reflexivity | exact D_5f3e0 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact W1 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                                                                (* [comment removed for export] *)
      an Fa64 D_5f3e4.                                                                                                   (* [comment removed for export] *)
      chain_step; [reflexivity | apply (proj1 (B68 _ _ _)); gres; reflexivity | ].                                    (* [comment removed for export] *)
      wd_refl.
    - ra_solve.
  Qed.
End KA.
End FPGen1.
