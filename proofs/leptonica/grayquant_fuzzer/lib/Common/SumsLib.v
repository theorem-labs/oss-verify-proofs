(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Export StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint code_at (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : Prop :=
  match ws with
  | [] => True
  | w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_at segs base (off + 4)%Z ws'
  end.

(* [comment removed for export] *)
Ltac code_at_vm :=
  cbn [code_at Z.add Pos.add Pos.succ];
  repeat split;
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Ltac zlit_at :=
  repeat match goal with
  | |- context [at_ ?b (?x + ?y)%Z] =>
      is_Z_lit x; is_Z_lit y;
      let z := eval cbv in (x + y)%Z in change (at_ b (x + y)%Z) with (at_ b z)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac fold_at_vars :=
  repeat match goal with
         | |- context [v_addi ?b ?e] => is_var b; change (v_addi b e) with (at_ b e)
         end.

(* [comment removed for export] *)
Ltac vn :=
  gres; rwH; imm_norm; unfold btgt;
  rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
  fold_at_vars; rewrite ?at_addi; zlit_at; vals_lit.
Ltac pcn := vn.

(* [comment removed for export] *)
Ltac an F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vn
  | _ => stepi F D; vn
  end.

(* [comment removed for export] *)
Ltac av F D v tac := stepiv F D v ltac:(gres; rwH; imm_norm; tac); vn.

(* [comment removed for export] *)
Ltac ab_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

Ltac ab_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

(* [comment removed for export] *)
Ltac aret F D k :=
  stepjr F D k ltac:(gres; rwH; reflexivity);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      end.

(* [comment removed for export] *)
Ltac condz :=
  rwH; unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.

(* [comment removed for export] *)
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_fold : forall (a : word) d, Z_to_bv 64 (bv_unsigned a + d) = at_ a d.
Proof. reflexivity. Qed.

Lemma v_add_at : forall (a : word) z, (0 <= z < 2 ^ 64)%Z -> v_add a (Z_to_bv 64 z) = at_ a z.
Proof. intros a z Hz. unfold v_add, at_. rewrite (u_Z2bv z) by lia. reflexivity. Qed.

Lemma at_eq_u : forall (a : word) d e,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z -> (0 <= bv_unsigned a + e < 2 ^ 64)%Z ->
  at_ a d = at_ a e -> d = e.
Proof.
  intros a d e Hd He H. apply (f_equal bv_unsigned) in H. rewrite !at_u in H by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record cpyH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := CPYH {
  cHn : (0 <= n)%Z;
  cHlen : length bs = Z.to_nat n;
  cHsrc : rdn segs mem0 src (length bs) = Some bs;
  cHdst : store_ok segs mem0 dst (length bs) = true;
  cHdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  cHnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  cHnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MEMK.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : cpyH segs mem0 dst src n bs.

  Let Hn := cHn _ _ _ _ _ _ HOK.
  Let Hlen := cHlen _ _ _ _ _ _ HOK.
  Let Hsrc := cHsrc _ _ _ _ _ _ HOK.
  Let Hdst := cHdst _ _ _ _ _ _ HOK.
  Let Hdisj := cHdisj _ _ _ _ _ _ HOK.
  Let Hnws := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  Lemma memk_0 : memk 0 = mem0.
  Proof. reflexivity. Qed.

  Lemma memk_n : memk n = wbytes mem0 dst bs.
  Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.

  Lemma rd_src1 : forall k j,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
      rdn segs (memk k) (at_ src j) 1 = Some [b_ j].
  Proof.
    intros k j Hk Hj H1. unfold memk, b_.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite rdn_wbytes_out.
    - replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      rewrite (rdn_sub segs mem0 (length bs) src bs (Z.to_nat j) 1 Hsrc) by (rewrite Hlen; lia).
      rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
    - rewrite length_firstn, Hlen, at_u; cbn; lia.
    - rewrite at_u; cbn; lia.
    - rewrite length_firstn, Hlen. lia.
  Qed.

  Lemma wr_dst : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (memk k) (at_ dst j) m = true.
  Proof.
    intros k j m Hj Hm. unfold memk.
    apply (store_ok_at segs mem0 dst (length bs)); try assumption; rewrite ?Hlen; lia.
  Qed.

  Lemma memk_extend1 : forall k,
      (0 <= k)%Z -> (k + 1 <= n)%Z ->
      wbytes (memk k) (at_ dst k) [b_ k] = memk (k + 1).
  Proof.
    intros k Hk H1. unfold memk, b_.
    replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite <- sub_nth by (rewrite Hlen; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned (b_ j)))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ k ->
    (0 <= k)%Z -> (k + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 1)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
    rewrite <- (memk_extend1 k) by lia.
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; cbn; lia.
  Qed.

End MEMK.

Lemma sb_val_b : forall bs j, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned (b_ bs j)))) = b_ bs j.
Proof.
  intros bs j. pose proof (u8_range (b_ bs j)). rewrite u_Z2bv by lia. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSETK.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable s : word.
  Variable n : Z.
  Variable b : byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.

  Definition msetk (k : Z) : word -> option byte := wbytes mem0 s (repeat b (Z.to_nat k)).

  Lemma msetk_0 : msetk 0 = mem0.
  Proof. reflexivity. Qed.

  Lemma wr_s : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (msetk k) (at_ s j) m = true.
  Proof.
    intros k j m Hj Hm. unfold msetk.
    apply (store_ok_at segs mem0 s (Z.to_nat n)); try assumption; lia.
  Qed.

  Lemma msetk_extend : forall k m,
      (0 <= k)%Z ->
      wbytes (msetk k) (at_ s k) (repeat b m) = msetk (k + Z.of_nat m).
  Proof.
    intros k m Hk. unfold msetk.
    replace (Z.to_nat (k + Z.of_nat m)) with (Z.to_nat k + m)%nat by lia.
    rewrite repeat_app, wbytes_app, repeat_length. f_equal. f_equal. lia.
  Qed.

  Lemma msetk_extend1 : forall k, (0 <= k)%Z -> wbytes (msetk k) (at_ s k) [b] = msetk (k + 1).
  Proof. intros k Hk. apply (msetk_extend k 1). exact Hk. Qed.
End MSETK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma v_slli_mul : forall (x : word) k, (0 <= k)%Z -> v_slli x k = Z_to_bv 64 (bv_unsigned x * 2 ^ k).
Proof. intros x k Hk. unfold v_slli. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma v_or_shl : forall (x : word) a k, (0 <= a)%Z -> (0 <= k)%Z -> (a * 2 ^ k < 2 ^ 64)%Z ->
  (bv_unsigned x < 2 ^ k)%Z ->
  v_or (Z_to_bv 64 (a * 2 ^ k)) x = Z_to_bv 64 (a * 2 ^ k + bv_unsigned x).
Proof.
  intros x a k Ha Hk Hak Hx. pose proof (u64_range x). unfold v_or.
  pose proof (Z.pow_nonneg 2 k ltac:(lia)).
  rewrite u_Z2bv by nia. rewrite lor_shl_disjoint by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition M8 : Z := 72340172838076673.

Lemma M8_digit : forall c k, (0 <= c < 256)%Z ->
  (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z ->
  (Z.shiftr (c * M8) (8 * k) mod 256 = c)%Z.
Proof.
  intros c k Hc Hk. unfold M8. rewrite Z.shiftr_div_pow2 by lia.
  assert (G : forall Mhi Mlo B, (0 < B)%Z -> (Mhi * B + Mlo = 72340172838076673)%Z -> (0 <= Mlo)%Z ->
             (255 * Mlo < B)%Z -> (Mhi mod 256 = 1)%Z ->
             (c * 72340172838076673 / B mod 256 = c)%Z).
  { intros Mhi Mlo B HB HM Hlo Hlt Hm1.
    replace (c * 72340172838076673)%Z with (c * Mhi * B + c * Mlo)%Z by nia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (c * Mlo) B) by nia.
    rewrite Z.add_0_r, <- Zmult_mod_idemp_r, Hm1, Z.mul_1_r. apply Z.mod_small. lia. }
  destruct Hk as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
  - apply (G 72340172838076673 0 1)%Z; reflexivity || lia.
  - apply (G 282578800148737 1 (2^8))%Z; try reflexivity; lia.
  - apply (G 1103823438081 257 (2^16))%Z; try reflexivity; lia.
  - apply (G 4311810305 65793 (2^24))%Z; try reflexivity; lia.
  - apply (G 16843009 16843009 (2^32))%Z; try reflexivity; lia.
  - apply (G 65793 4311810305 (2^40))%Z; try reflexivity; lia.
  - apply (G 257 1103823438081 (2^48))%Z; try reflexivity; lia.
  - apply (G 1 282578800148737 (2^56))%Z; try reflexivity; lia.
Qed.

Lemma byte_eq_mod : forall x y, (x mod 256 = y mod 256)%Z -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

(* [comment removed for export] *)
Lemma rep8_bytes : forall c, (0 <= c < 256)%Z ->
  word_to_le_bytes 8 (Z_to_bv 64 (c * M8)) = repeat (Z_to_bv 8 c) 8.
Proof.
  intros c Hc. unfold word_to_le_bytes. rewrite u_Z2bv by (unfold M8; lia).
  cbn [Z_to_le_bytes repeat]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
  pose proof (M8_digit c) as D.
  repeat match goal with
  | |- (_ :: _) = (_ :: _) => f_equal
  | |- Z_to_bv 8 _ = Z_to_bv 8 _ => apply byte_eq_mod; rewrite (Z.mod_small c 256) by lia
  | |- [] = [] => reflexivity
  end.
  - rewrite <- (D 0%Z) at 2 by lia. rewrite Z.shiftr_0_r || (cbn [Z.mul]; rewrite Z.shiftr_0_r). reflexivity.
  - apply (D 1%Z); lia.
  - apply (D 2%Z); lia.
  - apply (D 3%Z); lia.
  - apply (D 4%Z); lia.
  - apply (D 5%Z); lia.
  - apply (D 6%Z); lia.
  - apply (D 7%Z); lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_u : forall c : word, Z_to_bv 8 (bv_unsigned c) = Z_to_bv 8 (bv_unsigned c mod 256).
Proof. intros c. apply byte_eq_mod. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac av_or F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
