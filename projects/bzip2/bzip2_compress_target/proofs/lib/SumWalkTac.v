(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Lia. 
From Stdlib Require ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec SeqExec StepTac.
Module LibAtomic.
(* [comment removed for export] *)
(* [comment removed for export] *)

 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StepTac.
Import ListNotations.
Local Open Scope bv_scope.

(* [comment removed for export] *)
Definition mkst_r (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : word)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := Some r; ms_fcsr := Z_to_bv 32 0;
     ms_mem := mem; ms_rom := rom |}.

(* [comment removed for export] *)

Ltac atomic_pipeline Hfetch Hecall Hdecode :=
  unfold mkst_r;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Ltac norm_pc_r :=
  try lazymatch goal with
      | |- CatSim.msteps _ (mkst_r _ ?p _ _ _) _ => wlit p
      end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_lr_w : forall segs regs pc mem rom w aq rl rd rs bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AW aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
                    (v_addi pc 4) mem rom (getr regs rs)).
Proof.
  intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sc_w_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  subst r. rewrite Z.eqb_refl. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_branch_ft_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma step_bne_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End LibAtomic.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_4 : forall v : word, (bv_unsigned v < 2^32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : forall z, (0 <= z < 2147483648)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia.
  apply (bv_swrap_small 32). change (bv_half_modulus 32) with 2147483648%Z. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_eq_Z : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof. intros x. unfold c_eq. apply bv_eqb_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zlen :=
  repeat match goal with
         | |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
         end;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
Ltac zsimp := zlen; u_norm.

(* [comment removed for export] *)
Ltac sok_stack SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia_fast := first [ solve [ clear_disj; lia ] | lia ].
(* [comment removed for export] *)
Lemma rdn_wbytes_out_Z : forall segs bs m (zb za : Z) n,
  (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
   zb + Z.of_nat (length bs) <= 2^64 /\
   (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  (intros segs bs m zb za n; cps_intros (Ha & Han & Hb & Hbn & Hd)).
  apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
Ltac rdn_peel1 :=
  first [ rewrite rdn_wbytes_out_Z by (zlen; lia_fast)
        | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].  (* [comment removed for export] *)
Ltac rdn_by H := repeat rdn_peel1; exact H.
(* [comment removed for export] *)
Ltac rdn_hyp :=
  match goal with
  | H : rdn _ _ ?a ?n = Some _ |- rdn _ _ ?a ?n = Some _ => exact H
  end.
Ltac rdn_solve :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; rdn_solve)
  | |- _ => rdn_hyp
  end.

(* [comment removed for export] *)
Ltac zbv_target x i :=
  lazymatch x with
  | Z_to_bv 64 (?a - ?b)%Z => let d := eval cbv in (b - i)%Z in constr:(Z_to_bv 64 (a - d))
  | Z_to_bv 64 (?a + ?b)%Z => let d := eval cbv in (b + i)%Z in constr:(Z_to_bv 64 (a + d))
  | Z_to_bv 64 ?a =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (a - d))
      | _ => constr:(Z_to_bv 64 (a + i))
      end
  | _ =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (bv_unsigned x - d))
      | _ => constr:(Z_to_bv 64 (bv_unsigned x + i))
      end
  end.

(* [comment removed for export] *)
Ltac addr_norm :=
  match goal with
  | |- context [v_addi ?x ?i] =>
      let e := constr:(v_addi x i) in
      tryif check_closed_term e then wlit_closed e
      else first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sp_renorm :=
  match goal with
  | |- context [regupd _ 2 (v_addi ?x ?i)] =>
      let e := constr:(v_addi x i) in
      first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  end.

(* [comment removed for export] *)
Ltac getr_hyps :=
  repeat match goal with
         | H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H
         end.
Ltac addr_tac := getr_hyps; unfold v_addi; u_norm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia].
Ltac val_tac := first [reflexivity | assumption | symmetry; assumption].

(* [comment removed for export] *)
Ltac stepST F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepLD F D bsv vv rdtac vtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
Ltac stepLD8 F D vv := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).

(* [comment removed for export] *)
Ltac stepLBU F D bb rdtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu with (b := bb);
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Ltac zaddr H :=
  repeat match type of H with
  | context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
  end.

(* [comment removed for export] *)
Ltac zaddr_goal :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in
      lazymatch c with
      | Zpos _ => change (a + b)%Z with c
      end
  end.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
