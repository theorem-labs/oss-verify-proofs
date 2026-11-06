(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SumLib Sum_code.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Record mcH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
  Hn : (0 <= n < 2 ^ 64)%Z;
  Hlen : length bs = Z.to_nat n;
  Hsrc : rdn segs mem0 src (length bs) = Some bs;
  Hdst : store_ok segs mem0 dst (length bs) = true;
  Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MC.
Context {fx : FPState}.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  Let Hn := Hn _ _ _ _ _ _ HOK.
  Let Hlen := Hlen _ _ _ _ _ _ HOK.
  Let Hsrc := Hsrc _ _ _ _ _ _ HOK.
  Let Hdst := Hdst _ _ _ _ _ _ HOK.
  Let Hdisj := Hdisj _ _ _ _ _ _ HOK.
  Let Hnws := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd := Hnwd _ _ _ _ _ _ HOK.

  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).

  Definition sb_ (j : Z) (m : nat) : list byte := sub bs (Z.to_nat j) m.

  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  Lemma lenZ : Z.of_nat (length bs) = n.
  Proof. rewrite Hlen. lia. Qed.

  Lemma memk_n : memk n = wbytes mem0 dst bs.
  Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.

  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. rewrite Hlen. lia. Qed.

  Lemma rd_src : forall k j m,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      rdn segs (memk k) (at_ src j) m = Some (sb_ j m).
  Proof.
    intros k j m Hk Hj Hm. unfold memk, sb_.
    pose proof (u64_range src). pose proof (u64_range dst).
    destruct m as [|m'].
    { cbn. unfold sub. cbn. reflexivity. }
    rewrite rdn_wbytes_out.
    - replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      apply (rdn_sub segs mem0 (length bs)); [exact Hsrc | rewrite Hlen; lia].
    - rewrite length_firstn, Hlen, at_u; lia.
    - rewrite at_u; lia.
    - rewrite length_firstn, Hlen. lia.
  Qed.

  Lemma rd_src1 : forall k j,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
      rdn segs (memk k) (at_ src j) 1 = Some [b_ j].
  Proof.
    intros k j Hk Hj H1. rewrite (rd_src k j 1) by lia. unfold sb_, b_.
    rewrite sub_nth; [reflexivity | rewrite Hlen; lia].
  Qed.

  Lemma wr_dst : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (memk k) (at_ dst j) m = true.
  Proof.
    intros k j m Hj Hm. unfold memk.
    apply (store_ok_at segs mem0 dst (length bs)); try assumption; rewrite ?lenZ; lia.
  Qed.

  Lemma memk_extend : forall k l m,
      (0 <= k)%Z -> (k + Z.of_nat m <= n)%Z -> l = sb_ k m ->
      wbytes (memk k) (at_ dst k) l = memk (k + Z.of_nat m).
  Proof.
    intros k l m Hk Hm ->. unfold memk, sb_.
    replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  Lemma memk_extend1 : forall k (b : byte),
      (0 <= k)%Z -> (k + 1 <= n)%Z -> b = b_ k ->
      wbytes (memk k) (at_ dst k) [b] = memk (k + 1).
  Proof.
    intros k b Hk H1 ->.
    replace (k + 1)%Z with (k + Z.of_nat 1)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 1) 1); try lia; [|reflexivity].
    unfold sb_, b_. rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
  Qed.

  Lemma sb4_split : forall j (q : nat), (0 <= j)%Z -> (q <= 4)%nat ->
      sb_ j 4 = sb_ j q ++ sb_ (j + Z.of_nat q) (4 - q).
  Proof.
    intros j q Hj Hq. unfold sb_.
    replace 4%nat with (q + (4 - q))%nat at 1 by lia. rewrite sub_split. f_equal. f_equal. lia.
  Qed.

  Lemma skipn_sb : forall j (q m : nat), (0 <= j)%Z ->
      skipn q (sb_ j m) = sb_ (j + Z.of_nat q) (m - q).
  Proof.
    intros j q m Hj. unfold sb_, sub. rewrite skipn_firstn_comm, <- skipn_add. f_equal. f_equal. lia.
  Qed.

  Lemma firstn_sb : forall j (q m : nat), (q <= m)%nat -> firstn q (sb_ j m) = sb_ j q.
  Proof. intros j q m Hq. unfold sb_, sub. rewrite firstn_firstn. f_equal. lia. Qed.

  Lemma merge_sb : forall j (q : nat) (v : word),
      (0 <= j)%Z -> (j + 8 <= n)%Z -> (1 <= q <= 3)%nat ->
      v = v_or (v_slli (LWv (sb_ (j + 4) 4)) (32 - 8 * Z.of_nat q)) (v_srliw (LWv (sb_ j 4)) (8 * Z.of_nat q)) ->
      word_to_le_bytes 4 v = sb_ (j + Z.of_nat q) 4.
  Proof.
    intros j q v Hj H8 Hq Hv.
    rewrite (sw_bytes_merge (sb_ j 4) (sb_ (j + 4) 4) q v); try (apply sb_len; lia); try assumption.
    rewrite skipn_sb, firstn_sb by lia.
    rewrite (sb4_split (j + Z.of_nat q) (4 - q)) by lia.
    f_equal. f_equal; lia.
  Qed.

  Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
  Qed.

  Lemma mc_lw : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 4 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LWv (sb_ j 4))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj4.
    eapply step_lw; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_src k j 4); lia.
    - symmetry. apply u_lez4. apply sb_len; lia.
  Qed.

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
    rewrite <- (memk_extend1 k (b_ k)) by (lia || reflexivity).
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  Lemma mc_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = sb_ k 4 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 4)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk4.
    replace (k + 4)%Z with (k + Z.of_nat 4)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 4) 4) by (lia || reflexivity).
    rewrite <- Hb.
    eapply step_sw_at; [exact Hf | exact He | exact Hd | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  Lemma sw_val_plain : forall k, (0 <= k)%Z -> (k + 4 <= n)%Z ->
    word_to_le_bytes 4 (LWv (sb_ k 4)) = sb_ k 4.
  Proof. intros k Hk H4. apply sw_bytes_LWv. apply sb_len; lia. Qed.

  Lemma sb_val_plain : forall k, Z_to_bv 8 (bv_unsigned (LBv (b_ k))) = b_ k.
  Proof. intros k. apply sb_byte_LBv. Qed.

  Lemma sb_val_srli : forall j (q : nat), (0 <= j)%Z -> (j + 4 <= n)%Z -> (q <= 3)%nat ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) (8 * Z.of_nat q))) = b_ (j + Z.of_nat q).
  Proof.
    intros j q Hj H4 Hq. rewrite sb_byte_srli_LWv; [| apply sb_len; lia | exact Hq].
    unfold sb_, b_, sub.
    rewrite nth_firstn. replace (q <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_skipn. f_equal. lia.
  Qed.

  Lemma sb_val_word0 : forall j, (0 <= j)%Z -> (j + 4 <= n)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ j.
  Proof.
    intros j Hj H4.
    pose proof (sb_val_srli j 0 Hj H4 ltac:(lia)) as E.
    rewrite Z.add_0_r in E. rewrite <- E. f_equal. f_equal.
    unfold v_srli. rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

  Lemma merge_s16 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 16) (v_srliw (LWv (sb_ j1 4)) 16) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 2)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 2)%Z with (j1 + Z.of_nat 2)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma merge_s8 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 24) (v_srliw (LWv (sb_ j1 4)) 8) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 1)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 1)%Z with (j1 + Z.of_nat 1)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma merge_s24 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 8) (v_srliw (LWv (sb_ j1 4)) 24) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 3)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 3)%Z with (j1 + Z.of_nat 3)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma sb_val_srli8 : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j + 1)%Z ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) 8)) = b_ k.
  Proof.
    intros j k Hj H4 ->. replace (j + 1)%Z with (j + Z.of_nat 1)%Z by lia.
    rewrite <- (sb_val_srli j 1) by lia. reflexivity.
  Qed.

  Lemma sb_val_srli16 : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j + 2)%Z ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) 16)) = b_ k.
  Proof.
    intros j k Hj H4 ->. replace (j + 2)%Z with (j + Z.of_nat 2)%Z by lia.
    rewrite <- (sb_val_srli j 2) by lia. reflexivity.
  Qed.

  Lemma sb_val_word0' : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ k.
  Proof. intros j k Hj H4 ->. apply sb_val_word0; lia. Qed.

End MC.

Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.

Ltac cond_lia :=
  rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb; imm_norm; unorm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

Lemma u_andi : forall (x : word) imm, (0 <= imm < 2 ^ 64)%Z ->
  bv_unsigned (v_andi x imm) = Z.land (bv_unsigned x) imm.
Proof.
  intros x imm Hi. unfold v_andi. rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 imm) with imm by (symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. apply Z_land_range; [apply u64_range|lia].
Qed.

Lemma land_3 : forall a, (0 <= a)%Z -> Z.land a 3 = (a mod 4)%Z.
Proof. intros a Ha. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_1 : forall a, (0 <= a)%Z -> Z.land a 1 = (a mod 2)%Z.
Proof. intros a Ha. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma bits_lt32 : forall m, (0 <= m < 32)%Z ->
  (Z.land m 16 = 0 \/ Z.land m 16 = 16)%Z /\ (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z /\
  (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z /\ (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z /\
  (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z /\
  (m = Z.land m 16 + Z.land m 8 + Z.land m 4 + Z.land m 2 + Z.land m 1)%Z.
Proof.
  intros m Hm.
  assert (E : exists k : nat, m = Z.of_nat k /\ (k < 32)%nat).
  { exists (Z.to_nat m). split; lia. }
  destruct E as (k & -> & Hk).
  do 32 (destruct k as [|k]; [vm_compute; intuition lia|]). lia.
Qed.

Section MF.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.

  Lemma MF_000 : fetch_word segs (at_ base 0) = Some W_118ac0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 0 _ HCODE eq_refl). Qed.
  Lemma MF_004 : fetch_word segs (at_ base 4) = Some W_118ac4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 1 _ HCODE eq_refl). Qed.
  Lemma MF_008 : fetch_word segs (at_ base 8) = Some W_118ac8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 2 _ HCODE eq_refl). Qed.
  Lemma MF_00c : fetch_word segs (at_ base 12) = Some W_118acc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 3 _ HCODE eq_refl). Qed.
  Lemma MF_010 : fetch_word segs (at_ base 16) = Some W_118ad0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 4 _ HCODE eq_refl). Qed.
  Lemma MF_014 : fetch_word segs (at_ base 20) = Some W_118ad4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 5 _ HCODE eq_refl). Qed.
  Lemma MF_018 : fetch_word segs (at_ base 24) = Some W_118ad8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 6 _ HCODE eq_refl). Qed.
  Lemma MF_01c : fetch_word segs (at_ base 28) = Some W_118adc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 7 _ HCODE eq_refl). Qed.
  Lemma MF_020 : fetch_word segs (at_ base 32) = Some W_118ae0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 8 _ HCODE eq_refl). Qed.
  Lemma MF_024 : fetch_word segs (at_ base 36) = Some W_118ae4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 9 _ HCODE eq_refl). Qed.
  Lemma MF_028 : fetch_word segs (at_ base 40) = Some W_118ae8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 10 _ HCODE eq_refl). Qed.
  Lemma MF_02c : fetch_word segs (at_ base 44) = Some W_118aec.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 11 _ HCODE eq_refl). Qed.
  Lemma MF_030 : fetch_word segs (at_ base 48) = Some W_118af0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 12 _ HCODE eq_refl). Qed.
  Lemma MF_034 : fetch_word segs (at_ base 52) = Some W_118af4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 13 _ HCODE eq_refl). Qed.
  Lemma MF_038 : fetch_word segs (at_ base 56) = Some W_118af8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 14 _ HCODE eq_refl). Qed.
  Lemma MF_03c : fetch_word segs (at_ base 60) = Some W_118afc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 15 _ HCODE eq_refl). Qed.
  Lemma MF_040 : fetch_word segs (at_ base 64) = Some W_118b00.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 16 _ HCODE eq_refl). Qed.
  Lemma MF_044 : fetch_word segs (at_ base 68) = Some W_118b04.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 17 _ HCODE eq_refl). Qed.
  Lemma MF_048 : fetch_word segs (at_ base 72) = Some W_118b08.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 18 _ HCODE eq_refl). Qed.
  Lemma MF_04c : fetch_word segs (at_ base 76) = Some W_118b0c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 19 _ HCODE eq_refl). Qed.
  Lemma MF_050 : fetch_word segs (at_ base 80) = Some W_118b10.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 20 _ HCODE eq_refl). Qed.
  Lemma MF_054 : fetch_word segs (at_ base 84) = Some W_118b14.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 21 _ HCODE eq_refl). Qed.
  Lemma MF_058 : fetch_word segs (at_ base 88) = Some W_118b18.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 22 _ HCODE eq_refl). Qed.
  Lemma MF_05c : fetch_word segs (at_ base 92) = Some W_118b1c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 23 _ HCODE eq_refl). Qed.
  Lemma MF_060 : fetch_word segs (at_ base 96) = Some W_118b20.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 24 _ HCODE eq_refl). Qed.
  Lemma MF_064 : fetch_word segs (at_ base 100) = Some W_118b24.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 25 _ HCODE eq_refl). Qed.
  Lemma MF_068 : fetch_word segs (at_ base 104) = Some W_118b28.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 26 _ HCODE eq_refl). Qed.
  Lemma MF_06c : fetch_word segs (at_ base 108) = Some W_118b2c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 27 _ HCODE eq_refl). Qed.
  Lemma MF_070 : fetch_word segs (at_ base 112) = Some W_118b30.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 28 _ HCODE eq_refl). Qed.
  Lemma MF_074 : fetch_word segs (at_ base 116) = Some W_118b34.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 29 _ HCODE eq_refl). Qed.
  Lemma MF_078 : fetch_word segs (at_ base 120) = Some W_118b38.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 30 _ HCODE eq_refl). Qed.
  Lemma MF_07c : fetch_word segs (at_ base 124) = Some W_118b3c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 31 _ HCODE eq_refl). Qed.
  Lemma MF_080 : fetch_word segs (at_ base 128) = Some W_118b40.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 32 _ HCODE eq_refl). Qed.
  Lemma MF_084 : fetch_word segs (at_ base 132) = Some W_118b44.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 33 _ HCODE eq_refl). Qed.
  Lemma MF_088 : fetch_word segs (at_ base 136) = Some W_118b48.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 34 _ HCODE eq_refl). Qed.
  Lemma MF_08c : fetch_word segs (at_ base 140) = Some W_118b4c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 35 _ HCODE eq_refl). Qed.
  Lemma MF_090 : fetch_word segs (at_ base 144) = Some W_118b50.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 36 _ HCODE eq_refl). Qed.
  Lemma MF_094 : fetch_word segs (at_ base 148) = Some W_118b54.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 37 _ HCODE eq_refl). Qed.
  Lemma MF_098 : fetch_word segs (at_ base 152) = Some W_118b58.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 38 _ HCODE eq_refl). Qed.
  Lemma MF_09c : fetch_word segs (at_ base 156) = Some W_118b5c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 39 _ HCODE eq_refl). Qed.
  Lemma MF_0a0 : fetch_word segs (at_ base 160) = Some W_118b60.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 40 _ HCODE eq_refl). Qed.
  Lemma MF_0a4 : fetch_word segs (at_ base 164) = Some W_118b64.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 41 _ HCODE eq_refl). Qed.
  Lemma MF_0a8 : fetch_word segs (at_ base 168) = Some W_118b68.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 42 _ HCODE eq_refl). Qed.
  Lemma MF_0ac : fetch_word segs (at_ base 172) = Some W_118b6c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 43 _ HCODE eq_refl). Qed.
  Lemma MF_0b0 : fetch_word segs (at_ base 176) = Some W_118b70.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 44 _ HCODE eq_refl). Qed.
  Lemma MF_0b4 : fetch_word segs (at_ base 180) = Some W_118b74.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 45 _ HCODE eq_refl). Qed.
  Lemma MF_0b8 : fetch_word segs (at_ base 184) = Some W_118b78.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 46 _ HCODE eq_refl). Qed.
  Lemma MF_0bc : fetch_word segs (at_ base 188) = Some W_118b7c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 47 _ HCODE eq_refl). Qed.
  Lemma MF_0c0 : fetch_word segs (at_ base 192) = Some W_118b80.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 48 _ HCODE eq_refl). Qed.
  Lemma MF_0c4 : fetch_word segs (at_ base 196) = Some W_118b84.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 49 _ HCODE eq_refl). Qed.
  Lemma MF_0c8 : fetch_word segs (at_ base 200) = Some W_118b88.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 50 _ HCODE eq_refl). Qed.
  Lemma MF_0cc : fetch_word segs (at_ base 204) = Some W_118b8c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 51 _ HCODE eq_refl). Qed.
  Lemma MF_0d0 : fetch_word segs (at_ base 208) = Some W_118b90.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 52 _ HCODE eq_refl). Qed.
  Lemma MF_0d4 : fetch_word segs (at_ base 212) = Some W_118b94.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 53 _ HCODE eq_refl). Qed.
  Lemma MF_0d8 : fetch_word segs (at_ base 216) = Some W_118b98.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 54 _ HCODE eq_refl). Qed.
  Lemma MF_0dc : fetch_word segs (at_ base 220) = Some W_118b9c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 55 _ HCODE eq_refl). Qed.
  Lemma MF_0e0 : fetch_word segs (at_ base 224) = Some W_118ba0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 56 _ HCODE eq_refl). Qed.
  Lemma MF_0e4 : fetch_word segs (at_ base 228) = Some W_118ba4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 57 _ HCODE eq_refl). Qed.
  Lemma MF_0e8 : fetch_word segs (at_ base 232) = Some W_118ba8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 58 _ HCODE eq_refl). Qed.
  Lemma MF_0ec : fetch_word segs (at_ base 236) = Some W_118bac.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 59 _ HCODE eq_refl). Qed.
  Lemma MF_0f0 : fetch_word segs (at_ base 240) = Some W_118bb0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 60 _ HCODE eq_refl). Qed.
  Lemma MF_0f4 : fetch_word segs (at_ base 244) = Some W_118bb4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 61 _ HCODE eq_refl). Qed.
  Lemma MF_0f8 : fetch_word segs (at_ base 248) = Some W_118bb8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 62 _ HCODE eq_refl). Qed.
  Lemma MF_0fc : fetch_word segs (at_ base 252) = Some W_118bbc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 63 _ HCODE eq_refl). Qed.
  Lemma MF_100 : fetch_word segs (at_ base 256) = Some W_118bc0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 64 _ HCODE eq_refl). Qed.
  Lemma MF_104 : fetch_word segs (at_ base 260) = Some W_118bc4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 65 _ HCODE eq_refl). Qed.
  Lemma MF_108 : fetch_word segs (at_ base 264) = Some W_118bc8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 66 _ HCODE eq_refl). Qed.
  Lemma MF_10c : fetch_word segs (at_ base 268) = Some W_118bcc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 67 _ HCODE eq_refl). Qed.
  Lemma MF_110 : fetch_word segs (at_ base 272) = Some W_118bd0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 68 _ HCODE eq_refl). Qed.
  Lemma MF_114 : fetch_word segs (at_ base 276) = Some W_118bd4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 69 _ HCODE eq_refl). Qed.
  Lemma MF_118 : fetch_word segs (at_ base 280) = Some W_118bd8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 70 _ HCODE eq_refl). Qed.
  Lemma MF_11c : fetch_word segs (at_ base 284) = Some W_118bdc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 71 _ HCODE eq_refl). Qed.
  Lemma MF_120 : fetch_word segs (at_ base 288) = Some W_118be0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 72 _ HCODE eq_refl). Qed.
  Lemma MF_124 : fetch_word segs (at_ base 292) = Some W_118be4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 73 _ HCODE eq_refl). Qed.
  Lemma MF_128 : fetch_word segs (at_ base 296) = Some W_118be8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 74 _ HCODE eq_refl). Qed.
  Lemma MF_12c : fetch_word segs (at_ base 300) = Some W_118bec.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 75 _ HCODE eq_refl). Qed.
  Lemma MF_130 : fetch_word segs (at_ base 304) = Some W_118bf0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 76 _ HCODE eq_refl). Qed.
  Lemma MF_134 : fetch_word segs (at_ base 308) = Some W_118bf4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 77 _ HCODE eq_refl). Qed.
  Lemma MF_138 : fetch_word segs (at_ base 312) = Some W_118bf8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 78 _ HCODE eq_refl). Qed.
  Lemma MF_13c : fetch_word segs (at_ base 316) = Some W_118bfc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 79 _ HCODE eq_refl). Qed.
  Lemma MF_140 : fetch_word segs (at_ base 320) = Some W_118c00.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 80 _ HCODE eq_refl). Qed.
  Lemma MF_144 : fetch_word segs (at_ base 324) = Some W_118c04.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 81 _ HCODE eq_refl). Qed.
  Lemma MF_148 : fetch_word segs (at_ base 328) = Some W_118c08.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 82 _ HCODE eq_refl). Qed.
  Lemma MF_14c : fetch_word segs (at_ base 332) = Some W_118c0c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 83 _ HCODE eq_refl). Qed.
  Lemma MF_150 : fetch_word segs (at_ base 336) = Some W_118c10.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 84 _ HCODE eq_refl). Qed.
  Lemma MF_154 : fetch_word segs (at_ base 340) = Some W_118c14.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 85 _ HCODE eq_refl). Qed.
  Lemma MF_158 : fetch_word segs (at_ base 344) = Some W_118c18.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 86 _ HCODE eq_refl). Qed.
  Lemma MF_15c : fetch_word segs (at_ base 348) = Some W_118c1c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 87 _ HCODE eq_refl). Qed.
  Lemma MF_160 : fetch_word segs (at_ base 352) = Some W_118c20.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 88 _ HCODE eq_refl). Qed.
  Lemma MF_164 : fetch_word segs (at_ base 356) = Some W_118c24.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 89 _ HCODE eq_refl). Qed.
  Lemma MF_168 : fetch_word segs (at_ base 360) = Some W_118c28.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 90 _ HCODE eq_refl). Qed.
  Lemma MF_16c : fetch_word segs (at_ base 364) = Some W_118c2c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 91 _ HCODE eq_refl). Qed.
  Lemma MF_170 : fetch_word segs (at_ base 368) = Some W_118c30.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 92 _ HCODE eq_refl). Qed.
  Lemma MF_174 : fetch_word segs (at_ base 372) = Some W_118c34.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 93 _ HCODE eq_refl). Qed.
  Lemma MF_178 : fetch_word segs (at_ base 376) = Some W_118c38.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 94 _ HCODE eq_refl). Qed.
  Lemma MF_17c : fetch_word segs (at_ base 380) = Some W_118c3c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 95 _ HCODE eq_refl). Qed.
  Lemma MF_180 : fetch_word segs (at_ base 384) = Some W_118c40.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 96 _ HCODE eq_refl). Qed.
  Lemma MF_184 : fetch_word segs (at_ base 388) = Some W_118c44.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 97 _ HCODE eq_refl). Qed.
  Lemma MF_188 : fetch_word segs (at_ base 392) = Some W_118c48.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 98 _ HCODE eq_refl). Qed.
  Lemma MF_18c : fetch_word segs (at_ base 396) = Some W_118c4c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 99 _ HCODE eq_refl). Qed.
  Lemma MF_190 : fetch_word segs (at_ base 400) = Some W_118c50.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 100 _ HCODE eq_refl). Qed.
  Lemma MF_194 : fetch_word segs (at_ base 404) = Some W_118c54.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 101 _ HCODE eq_refl). Qed.
  Lemma MF_198 : fetch_word segs (at_ base 408) = Some W_118c58.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 102 _ HCODE eq_refl). Qed.
  Lemma MF_19c : fetch_word segs (at_ base 412) = Some W_118c5c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 103 _ HCODE eq_refl). Qed.
  Lemma MF_1a0 : fetch_word segs (at_ base 416) = Some W_118c60.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 104 _ HCODE eq_refl). Qed.
  Lemma MF_1a4 : fetch_word segs (at_ base 420) = Some W_118c64.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 105 _ HCODE eq_refl). Qed.
  Lemma MF_1a8 : fetch_word segs (at_ base 424) = Some W_118c68.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 106 _ HCODE eq_refl). Qed.
  Lemma MF_1ac : fetch_word segs (at_ base 428) = Some W_118c6c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 107 _ HCODE eq_refl). Qed.
  Lemma MF_1b0 : fetch_word segs (at_ base 432) = Some W_118c70.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 108 _ HCODE eq_refl). Qed.
  Lemma MF_1b4 : fetch_word segs (at_ base 436) = Some W_118c74.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 109 _ HCODE eq_refl). Qed.
  Lemma MF_1b8 : fetch_word segs (at_ base 440) = Some W_118c78.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 110 _ HCODE eq_refl). Qed.
  Lemma MF_1bc : fetch_word segs (at_ base 444) = Some W_118c7c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 111 _ HCODE eq_refl). Qed.
  Lemma MF_1c0 : fetch_word segs (at_ base 448) = Some W_118c80.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 112 _ HCODE eq_refl). Qed.
  Lemma MF_1c4 : fetch_word segs (at_ base 452) = Some W_118c84.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 113 _ HCODE eq_refl). Qed.
  Lemma MF_1c8 : fetch_word segs (at_ base 456) = Some W_118c88.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 114 _ HCODE eq_refl). Qed.
  Lemma MF_1cc : fetch_word segs (at_ base 460) = Some W_118c8c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 115 _ HCODE eq_refl). Qed.
  Lemma MF_1d0 : fetch_word segs (at_ base 464) = Some W_118c90.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 116 _ HCODE eq_refl). Qed.
  Lemma MF_1d4 : fetch_word segs (at_ base 468) = Some W_118c94.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 117 _ HCODE eq_refl). Qed.
  Lemma MF_1d8 : fetch_word segs (at_ base 472) = Some W_118c98.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 118 _ HCODE eq_refl). Qed.
  Lemma MF_1dc : fetch_word segs (at_ base 476) = Some W_118c9c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 119 _ HCODE eq_refl). Qed.
  Lemma MF_1e0 : fetch_word segs (at_ base 480) = Some W_118ca0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 120 _ HCODE eq_refl). Qed.
  Lemma MF_1e4 : fetch_word segs (at_ base 484) = Some W_118ca4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 121 _ HCODE eq_refl). Qed.
  Lemma MF_1e8 : fetch_word segs (at_ base 488) = Some W_118ca8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 122 _ HCODE eq_refl). Qed.
  Lemma MF_1ec : fetch_word segs (at_ base 492) = Some W_118cac.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 123 _ HCODE eq_refl). Qed.
  Lemma MF_1f0 : fetch_word segs (at_ base 496) = Some W_118cb0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 124 _ HCODE eq_refl). Qed.
  Lemma MF_1f4 : fetch_word segs (at_ base 500) = Some W_118cb4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 125 _ HCODE eq_refl). Qed.
  Lemma MF_1f8 : fetch_word segs (at_ base 504) = Some W_118cb8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 126 _ HCODE eq_refl). Qed.
  Lemma MF_1fc : fetch_word segs (at_ base 508) = Some W_118cbc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 127 _ HCODE eq_refl). Qed.
  Lemma MF_200 : fetch_word segs (at_ base 512) = Some W_118cc0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 128 _ HCODE eq_refl). Qed.
  Lemma MF_204 : fetch_word segs (at_ base 516) = Some W_118cc4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 129 _ HCODE eq_refl). Qed.
  Lemma MF_208 : fetch_word segs (at_ base 520) = Some W_118cc8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 130 _ HCODE eq_refl). Qed.
  Lemma MF_20c : fetch_word segs (at_ base 524) = Some W_118ccc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 131 _ HCODE eq_refl). Qed.
  Lemma MF_210 : fetch_word segs (at_ base 528) = Some W_118cd0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 132 _ HCODE eq_refl). Qed.
  Lemma MF_214 : fetch_word segs (at_ base 532) = Some W_118cd4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 133 _ HCODE eq_refl). Qed.
  Lemma MF_218 : fetch_word segs (at_ base 536) = Some W_118cd8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 134 _ HCODE eq_refl). Qed.
  Lemma MF_21c : fetch_word segs (at_ base 540) = Some W_118cdc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 135 _ HCODE eq_refl). Qed.
  Lemma MF_220 : fetch_word segs (at_ base 544) = Some W_118ce0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 136 _ HCODE eq_refl). Qed.
  Lemma MF_224 : fetch_word segs (at_ base 548) = Some W_118ce4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 137 _ HCODE eq_refl). Qed.
  Lemma MF_228 : fetch_word segs (at_ base 552) = Some W_118ce8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 138 _ HCODE eq_refl). Qed.
  Lemma MF_22c : fetch_word segs (at_ base 556) = Some W_118cec.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 139 _ HCODE eq_refl). Qed.
  Lemma MF_230 : fetch_word segs (at_ base 560) = Some W_118cf0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 140 _ HCODE eq_refl). Qed.
  Lemma MF_234 : fetch_word segs (at_ base 564) = Some W_118cf4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 141 _ HCODE eq_refl). Qed.
  Lemma MF_238 : fetch_word segs (at_ base 568) = Some W_118cf8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 142 _ HCODE eq_refl). Qed.
  Lemma MF_23c : fetch_word segs (at_ base 572) = Some W_118cfc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 143 _ HCODE eq_refl). Qed.
  Lemma MF_240 : fetch_word segs (at_ base 576) = Some W_118d00.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 144 _ HCODE eq_refl). Qed.
  Lemma MF_244 : fetch_word segs (at_ base 580) = Some W_118d04.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 145 _ HCODE eq_refl). Qed.
  Lemma MF_248 : fetch_word segs (at_ base 584) = Some W_118d08.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 146 _ HCODE eq_refl). Qed.
  Lemma MF_24c : fetch_word segs (at_ base 588) = Some W_118d0c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 147 _ HCODE eq_refl). Qed.
  Lemma MF_250 : fetch_word segs (at_ base 592) = Some W_118d10.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 148 _ HCODE eq_refl). Qed.
  Lemma MF_254 : fetch_word segs (at_ base 596) = Some W_118d14.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 149 _ HCODE eq_refl). Qed.
  Lemma MF_258 : fetch_word segs (at_ base 600) = Some W_118d18.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 150 _ HCODE eq_refl). Qed.
  Lemma MF_25c : fetch_word segs (at_ base 604) = Some W_118d1c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 151 _ HCODE eq_refl). Qed.
  Lemma MF_260 : fetch_word segs (at_ base 608) = Some W_118d20.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 152 _ HCODE eq_refl). Qed.
  Lemma MF_264 : fetch_word segs (at_ base 612) = Some W_118d24.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 153 _ HCODE eq_refl). Qed.
  Lemma MF_268 : fetch_word segs (at_ base 616) = Some W_118d28.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 154 _ HCODE eq_refl). Qed.
  Lemma MF_26c : fetch_word segs (at_ base 620) = Some W_118d2c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 155 _ HCODE eq_refl). Qed.
  Lemma MF_270 : fetch_word segs (at_ base 624) = Some W_118d30.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 156 _ HCODE eq_refl). Qed.
  Lemma MF_274 : fetch_word segs (at_ base 628) = Some W_118d34.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 157 _ HCODE eq_refl). Qed.
  Lemma MF_278 : fetch_word segs (at_ base 632) = Some W_118d38.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 158 _ HCODE eq_refl). Qed.
  Lemma MF_27c : fetch_word segs (at_ base 636) = Some W_118d3c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 159 _ HCODE eq_refl). Qed.
  Lemma MF_280 : fetch_word segs (at_ base 640) = Some W_118d40.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 160 _ HCODE eq_refl). Qed.
  Lemma MF_284 : fetch_word segs (at_ base 644) = Some W_118d44.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 161 _ HCODE eq_refl). Qed.
  Lemma MF_288 : fetch_word segs (at_ base 648) = Some W_118d48.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 162 _ HCODE eq_refl). Qed.
  Lemma MF_28c : fetch_word segs (at_ base 652) = Some W_118d4c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 163 _ HCODE eq_refl). Qed.
  Lemma MF_290 : fetch_word segs (at_ base 656) = Some W_118d50.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 164 _ HCODE eq_refl). Qed.
  Lemma MF_294 : fetch_word segs (at_ base 660) = Some W_118d54.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 165 _ HCODE eq_refl). Qed.
  Lemma MF_298 : fetch_word segs (at_ base 664) = Some W_118d58.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 166 _ HCODE eq_refl). Qed.
  Lemma MF_29c : fetch_word segs (at_ base 668) = Some W_118d5c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 167 _ HCODE eq_refl). Qed.
  Lemma MF_2a0 : fetch_word segs (at_ base 672) = Some W_118d60.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 168 _ HCODE eq_refl). Qed.
  Lemma MF_2a4 : fetch_word segs (at_ base 676) = Some W_118d64.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 169 _ HCODE eq_refl). Qed.
  Lemma MF_2a8 : fetch_word segs (at_ base 680) = Some W_118d68.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 170 _ HCODE eq_refl). Qed.
  Lemma MF_2ac : fetch_word segs (at_ base 684) = Some W_118d6c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 171 _ HCODE eq_refl). Qed.
  Lemma MF_2b0 : fetch_word segs (at_ base 688) = Some W_118d70.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 172 _ HCODE eq_refl). Qed.
  Lemma MF_2b4 : fetch_word segs (at_ base 692) = Some W_118d74.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 173 _ HCODE eq_refl). Qed.
  Lemma MF_2b8 : fetch_word segs (at_ base 696) = Some W_118d78.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 174 _ HCODE eq_refl). Qed.
  Lemma MF_2bc : fetch_word segs (at_ base 700) = Some W_118d7c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 175 _ HCODE eq_refl). Qed.
  Lemma MF_2c0 : fetch_word segs (at_ base 704) = Some W_118d80.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 176 _ HCODE eq_refl). Qed.
  Lemma MF_2c4 : fetch_word segs (at_ base 708) = Some W_118d84.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 177 _ HCODE eq_refl). Qed.
  Lemma MF_2c8 : fetch_word segs (at_ base 712) = Some W_118d88.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 178 _ HCODE eq_refl). Qed.
  Lemma MF_2cc : fetch_word segs (at_ base 716) = Some W_118d8c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 179 _ HCODE eq_refl). Qed.
  Lemma MF_2d0 : fetch_word segs (at_ base 720) = Some W_118d90.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 180 _ HCODE eq_refl). Qed.
  Lemma MF_2d4 : fetch_word segs (at_ base 724) = Some W_118d94.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 181 _ HCODE eq_refl). Qed.
  Lemma MF_2d8 : fetch_word segs (at_ base 728) = Some W_118d98.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 182 _ HCODE eq_refl). Qed.
  Lemma MF_2dc : fetch_word segs (at_ base 732) = Some W_118d9c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 183 _ HCODE eq_refl). Qed.
  Lemma MF_2e0 : fetch_word segs (at_ base 736) = Some W_118da0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 184 _ HCODE eq_refl). Qed.
  Lemma MF_2e4 : fetch_word segs (at_ base 740) = Some W_118da4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 185 _ HCODE eq_refl). Qed.
  Lemma MF_2e8 : fetch_word segs (at_ base 744) = Some W_118da8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 186 _ HCODE eq_refl). Qed.
  Lemma MF_2ec : fetch_word segs (at_ base 748) = Some W_118dac.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 187 _ HCODE eq_refl). Qed.
  Lemma MF_2f0 : fetch_word segs (at_ base 752) = Some W_118db0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 188 _ HCODE eq_refl). Qed.
  Lemma MF_2f4 : fetch_word segs (at_ base 756) = Some W_118db4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 189 _ HCODE eq_refl). Qed.
  Lemma MF_2f8 : fetch_word segs (at_ base 760) = Some W_118db8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 190 _ HCODE eq_refl). Qed.
  Lemma MF_2fc : fetch_word segs (at_ base 764) = Some W_118dbc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 191 _ HCODE eq_refl). Qed.
  Lemma MF_300 : fetch_word segs (at_ base 768) = Some W_118dc0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 192 _ HCODE eq_refl). Qed.
  Lemma MF_304 : fetch_word segs (at_ base 772) = Some W_118dc4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 193 _ HCODE eq_refl). Qed.
  Lemma MF_308 : fetch_word segs (at_ base 776) = Some W_118dc8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 194 _ HCODE eq_refl). Qed.
  Lemma MF_30c : fetch_word segs (at_ base 780) = Some W_118dcc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 195 _ HCODE eq_refl). Qed.
  Lemma MF_310 : fetch_word segs (at_ base 784) = Some W_118dd0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 196 _ HCODE eq_refl). Qed.
  Lemma MF_314 : fetch_word segs (at_ base 788) = Some W_118dd4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 197 _ HCODE eq_refl). Qed.
  Lemma MF_318 : fetch_word segs (at_ base 792) = Some W_118dd8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 198 _ HCODE eq_refl). Qed.
  Lemma MF_31c : fetch_word segs (at_ base 796) = Some W_118ddc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 199 _ HCODE eq_refl). Qed.
  Lemma MF_320 : fetch_word segs (at_ base 800) = Some W_118de0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 200 _ HCODE eq_refl). Qed.
  Lemma MF_324 : fetch_word segs (at_ base 804) = Some W_118de4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 201 _ HCODE eq_refl). Qed.
  Lemma MF_328 : fetch_word segs (at_ base 808) = Some W_118de8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 202 _ HCODE eq_refl). Qed.
  Lemma MF_32c : fetch_word segs (at_ base 812) = Some W_118dec.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 203 _ HCODE eq_refl). Qed.
  Lemma MF_330 : fetch_word segs (at_ base 816) = Some W_118df0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 204 _ HCODE eq_refl). Qed.
  Lemma MF_334 : fetch_word segs (at_ base 820) = Some W_118df4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 205 _ HCODE eq_refl). Qed.
  Lemma MF_338 : fetch_word segs (at_ base 824) = Some W_118df8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 206 _ HCODE eq_refl). Qed.
  Lemma MF_33c : fetch_word segs (at_ base 828) = Some W_118dfc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 207 _ HCODE eq_refl). Qed.
  Lemma MF_340 : fetch_word segs (at_ base 832) = Some W_118e00.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 208 _ HCODE eq_refl). Qed.
  Lemma MF_344 : fetch_word segs (at_ base 836) = Some W_118e04.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 209 _ HCODE eq_refl). Qed.
  Lemma MF_348 : fetch_word segs (at_ base 840) = Some W_118e08.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 210 _ HCODE eq_refl). Qed.
  Lemma MF_34c : fetch_word segs (at_ base 844) = Some W_118e0c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 211 _ HCODE eq_refl). Qed.
  Lemma MF_350 : fetch_word segs (at_ base 848) = Some W_118e10.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 212 _ HCODE eq_refl). Qed.
  Lemma MF_354 : fetch_word segs (at_ base 852) = Some W_118e14.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 213 _ HCODE eq_refl). Qed.
  Lemma MF_358 : fetch_word segs (at_ base 856) = Some W_118e18.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 214 _ HCODE eq_refl). Qed.
  Lemma MF_35c : fetch_word segs (at_ base 860) = Some W_118e1c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 215 _ HCODE eq_refl). Qed.
  Lemma MF_360 : fetch_word segs (at_ base 864) = Some W_118e20.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 216 _ HCODE eq_refl). Qed.
  Lemma MF_364 : fetch_word segs (at_ base 868) = Some W_118e24.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 217 _ HCODE eq_refl). Qed.
  Lemma MF_368 : fetch_word segs (at_ base 872) = Some W_118e28.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 218 _ HCODE eq_refl). Qed.
  Lemma MF_36c : fetch_word segs (at_ base 876) = Some W_118e2c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 219 _ HCODE eq_refl). Qed.
  Lemma MF_370 : fetch_word segs (at_ base 880) = Some W_118e30.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 220 _ HCODE eq_refl). Qed.
  Lemma MF_374 : fetch_word segs (at_ base 884) = Some W_118e34.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 221 _ HCODE eq_refl). Qed.
  Lemma MF_378 : fetch_word segs (at_ base 888) = Some W_118e38.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 222 _ HCODE eq_refl). Qed.
  Lemma MF_37c : fetch_word segs (at_ base 892) = Some W_118e3c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 223 _ HCODE eq_refl). Qed.
  Lemma MF_380 : fetch_word segs (at_ base 896) = Some W_118e40.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 224 _ HCODE eq_refl). Qed.
  Lemma MF_384 : fetch_word segs (at_ base 900) = Some W_118e44.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 225 _ HCODE eq_refl). Qed.
  Lemma MF_388 : fetch_word segs (at_ base 904) = Some W_118e48.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 226 _ HCODE eq_refl). Qed.
  Lemma MF_38c : fetch_word segs (at_ base 908) = Some W_118e4c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 227 _ HCODE eq_refl). Qed.
  Lemma MF_390 : fetch_word segs (at_ base 912) = Some W_118e50.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 228 _ HCODE eq_refl). Qed.
  Lemma MF_394 : fetch_word segs (at_ base 916) = Some W_118e54.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 229 _ HCODE eq_refl). Qed.
  Lemma MF_398 : fetch_word segs (at_ base 920) = Some W_118e58.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 230 _ HCODE eq_refl). Qed.
  Lemma MF_39c : fetch_word segs (at_ base 924) = Some W_118e5c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 231 _ HCODE eq_refl). Qed.
  Lemma MF_3a0 : fetch_word segs (at_ base 928) = Some W_118e60.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 232 _ HCODE eq_refl). Qed.
  Lemma MF_3a4 : fetch_word segs (at_ base 932) = Some W_118e64.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 233 _ HCODE eq_refl). Qed.
  Lemma MF_3a8 : fetch_word segs (at_ base 936) = Some W_118e68.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 234 _ HCODE eq_refl). Qed.
  Lemma MF_3ac : fetch_word segs (at_ base 940) = Some W_118e6c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 235 _ HCODE eq_refl). Qed.
  Lemma MF_3b0 : fetch_word segs (at_ base 944) = Some W_118e70.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 236 _ HCODE eq_refl). Qed.
  Lemma MF_3b4 : fetch_word segs (at_ base 948) = Some W_118e74.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 237 _ HCODE eq_refl). Qed.
  Lemma MF_3b8 : fetch_word segs (at_ base 952) = Some W_118e78.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 238 _ HCODE eq_refl). Qed.
  Lemma MF_3bc : fetch_word segs (at_ base 956) = Some W_118e7c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 239 _ HCODE eq_refl). Qed.
  Lemma MF_3c0 : fetch_word segs (at_ base 960) = Some W_118e80.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 240 _ HCODE eq_refl). Qed.
  Lemma MF_3c4 : fetch_word segs (at_ base 964) = Some W_118e84.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 241 _ HCODE eq_refl). Qed.
  Lemma MF_3c8 : fetch_word segs (at_ base 968) = Some W_118e88.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 242 _ HCODE eq_refl). Qed.
  Lemma MF_3cc : fetch_word segs (at_ base 972) = Some W_118e8c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 243 _ HCODE eq_refl). Qed.
  Lemma MF_3d0 : fetch_word segs (at_ base 976) = Some W_118e90.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 244 _ HCODE eq_refl). Qed.
  Lemma MF_3d4 : fetch_word segs (at_ base 980) = Some W_118e94.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 245 _ HCODE eq_refl). Qed.
  Lemma MF_3d8 : fetch_word segs (at_ base 984) = Some W_118e98.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 246 _ HCODE eq_refl). Qed.
  Lemma MF_3dc : fetch_word segs (at_ base 988) = Some W_118e9c.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 247 _ HCODE eq_refl). Qed.
  Lemma MF_3e0 : fetch_word segs (at_ base 992) = Some W_118ea0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 248 _ HCODE eq_refl). Qed.
  Lemma MF_3e4 : fetch_word segs (at_ base 996) = Some W_118ea4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 249 _ HCODE eq_refl). Qed.
  Lemma MF_3e8 : fetch_word segs (at_ base 1000) = Some W_118ea8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 250 _ HCODE eq_refl). Qed.
  Lemma MF_3ec : fetch_word segs (at_ base 1004) = Some W_118eac.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 251 _ HCODE eq_refl). Qed.
  Lemma MF_3f0 : fetch_word segs (at_ base 1008) = Some W_118eb0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 252 _ HCODE eq_refl). Qed.
  Lemma MF_3f4 : fetch_word segs (at_ base 1012) = Some W_118eb4.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 253 _ HCODE eq_refl). Qed.
  Lemma MF_3f8 : fetch_word segs (at_ base 1016) = Some W_118eb8.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 254 _ HCODE eq_refl). Qed.
  Lemma MF_3fc : fetch_word segs (at_ base 1020) = Some W_118ebc.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 255 _ HCODE eq_refl). Qed.
  Lemma MF_400 : fetch_word segs (at_ base 1024) = Some W_118ec0.
  Proof. exact (code_at_get segs base 0 mmemcpy_words 256 _ HCODE eq_refl). Qed.
End MF.

