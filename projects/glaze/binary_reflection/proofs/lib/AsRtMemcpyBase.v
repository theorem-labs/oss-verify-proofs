(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.


(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition mmemcpy_words : list (bv 32) :=
  [W_f52e4; W_f52e8; W_f52ec; W_f52f0; W_f52f4; W_f52f8; W_f52fc; W_f5300; W_f5304; W_f5308; W_f530c; W_f5310; W_f5314; W_f5318; W_f531c; W_f5320; W_f5324; W_f5328; W_f532c; W_f5330; W_f5334; W_f5338; W_f533c; W_f5340; W_f5344; W_f5348; W_f534c; W_f5350; W_f5354; W_f5358; W_f535c; W_f5360; W_f5364; W_f5368; W_f536c; W_f5370; W_f5374; W_f5378; W_f537c; W_f5380; W_f5384; W_f5388; W_f538c; W_f5390; W_f5394; W_f5398; W_f539c; W_f53a0; W_f53a4; W_f53a8; W_f53ac; W_f53b0; W_f53b4; W_f53b8; W_f53bc; W_f53c0; W_f53c4; W_f53c8; W_f53cc; W_f53d0; W_f53d4; W_f53d8; W_f53dc; W_f53e0; W_f53e4; W_f53e8; W_f53ec; W_f53f0; W_f53f4; W_f53f8; W_f53fc; W_f5400; W_f5404; W_f5408; W_f540c; W_f5410; W_f5414; W_f5418; W_f541c; W_f5420; W_f5424; W_f5428; W_f542c; W_f5430; W_f5434; W_f5438; W_f543c; W_f5440; W_f5444; W_f5448; W_f544c; W_f5450; W_f5454; W_f5458; W_f545c; W_f5460; W_f5464; W_f5468; W_f546c; W_f5470; W_f5474; W_f5478; W_f547c; W_f5480; W_f5484; W_f5488; W_f548c; W_f5490; W_f5494; W_f5498; W_f549c; W_f54a0; W_f54a4; W_f54a8; W_f54ac; W_f54b0; W_f54b4; W_f54b8; W_f54bc; W_f54c0; W_f54c4; W_f54c8; W_f54cc; W_f54d0; W_f54d4; W_f54d8; W_f54dc; W_f54e0; W_f54e4; W_f54e8; W_f54ec; W_f54f0; W_f54f4; W_f54f8; W_f54fc; W_f5500; W_f5504; W_f5508; W_f550c; W_f5510; W_f5514; W_f5518; W_f551c; W_f5520; W_f5524; W_f5528; W_f552c; W_f5530; W_f5534; W_f5538; W_f553c; W_f5540; W_f5544; W_f5548; W_f554c; W_f5550; W_f5554; W_f5558; W_f555c; W_f5560; W_f5564; W_f5568; W_f556c; W_f5570; W_f5574; W_f5578; W_f557c; W_f5580; W_f5584; W_f5588; W_f558c; W_f5590; W_f5594; W_f5598; W_f559c; W_f55a0; W_f55a4; W_f55a8; W_f55ac; W_f55b0; W_f55b4; W_f55b8; W_f55bc; W_f55c0; W_f55c4; W_f55c8; W_f55cc; W_f55d0; W_f55d4; W_f55d8; W_f55dc; W_f55e0; W_f55e4; W_f55e8; W_f55ec; W_f55f0; W_f55f4; W_f55f8; W_f55fc; W_f5600; W_f5604; W_f5608; W_f560c; W_f5610; W_f5614; W_f5618; W_f561c; W_f5620; W_f5624; W_f5628; W_f562c; W_f5630; W_f5634; W_f5638; W_f563c; W_f5640; W_f5644; W_f5648; W_f564c; W_f5650; W_f5654; W_f5658; W_f565c; W_f5660; W_f5664; W_f5668; W_f566c; W_f5670; W_f5674; W_f5678; W_f567c; W_f5680; W_f5684; W_f5688; W_f568c; W_f5690; W_f5694; W_f5698; W_f569c; W_f56a0; W_f56a4; W_f56a8; W_f56ac; W_f56b0; W_f56b4; W_f56b8; W_f56bc; W_f56c0; W_f56c4; W_f56c8; W_f56cc; W_f56d0; W_f56d4; W_f56d8; W_f56dc; W_f56e0; W_f56e4]%list.

(* [comment removed for export] *)
Record mcH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
  Hn : (0 <= n < 2 ^ 64)%Z;
  Hlen : length bs = Z.to_nat n;
  Hsrc : rdn segs mem0 src (length bs) = Some bs;
  Hdst : store_ok segs mem0 dst (length bs) = true;
  Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MC.
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

  (* [comment removed for export] *)
  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition sb_ (j : Z) (m : nat) : list byte := sub bs (Z.to_nat j) m.
  (* [comment removed for export] *)
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  Lemma lenZ : Z.of_nat (length bs) = n.
  Proof using Hlen Hn HOK src dst mem0 segs. rewrite Hlen. lia. Qed.


  Lemma memk_n : memk n = wbytes mem0 dst bs.
  Proof using Hlen HOK src segs. (lazymatch goal with |- ?G => let G' := eval unfold memk in G in change_no_check G' end). rewrite <- Hlen, firstn_all. reflexivity. Qed.

  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> length (sb_ j m) = m.
  Proof using Hlen Hn HOK src dst mem0 segs. intros j m Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold sb_ in G in change_no_check G' end). apply sub_length. rewrite Hlen. lia. Qed.

  (* [comment removed for export] *)
  Lemma rd_src : forall k j m,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      rdn segs (memk k) (at_ src j) m = Some (sb_ j m).
  Proof using Hnwd Hnws Hdisj Hsrc Hlen Hn HOK.
    intros k j m Hk Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold memk, sb_ in G in change_no_check G' end).
    pose proof (u64_range src). pose proof (u64_range dst).
    destruct m as [|m'].
    { (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold sub in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). reflexivity. }
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
  Proof using Hnwd Hnws Hdisj Hsrc Hlen Hn HOK.
    intros k j Hk Hj H1. rewrite (rd_src k j 1) by lia. (lazymatch goal with |- ?G => let G' := eval unfold sb_, b_ in G in change_no_check G' end).
    rewrite sub_nth; [reflexivity | rewrite Hlen; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma wr_dst : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (memk k) (at_ dst j) m = true.
  Proof using Hnwd Hdst Hlen Hn HOK src.
    intros k j m Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold memk in G in change_no_check G' end).
    apply (store_ok_at segs mem0 dst (length bs)); try assumption; rewrite ?lenZ; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memk_extend : forall k l m,
      (0 <= k)%Z -> (k + Z.of_nat m <= n)%Z -> l = sb_ k m ->
      wbytes (memk k) (at_ dst k) l = memk (k + Z.of_nat m).
  Proof using Hlen Hn HOK src segs.
    intros k l m Hk Hm ->. (lazymatch goal with |- ?G => let G' := eval unfold memk, sb_ in G in change_no_check G' end).
    replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  Lemma memk_extend1 : forall k (b : byte),
      (0 <= k)%Z -> (k + 1 <= n)%Z -> b = b_ k ->
      wbytes (memk k) (at_ dst k) [b] = memk (k + 1).
  Proof using Hlen Hn HOK src segs.
    intros k b Hk H1 ->.
    replace (k + 1)%Z with (k + Z.of_nat 1)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 1) 1); try lia; [|reflexivity].
    (lazymatch goal with |- ?G => let G' := eval unfold sb_, b_ in G in change_no_check G' end). rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sb4_split : forall j (q : nat), (0 <= j)%Z -> (q <= 4)%nat ->
      sb_ j 4 = sb_ j q ++ sb_ (j + Z.of_nat q) (4 - q).
  Proof using Hlen Hn HOK n src dst mem0 segs.
    intros j q Hj Hq. (lazymatch goal with |- ?G => let G' := eval unfold sb_ in G in change_no_check G' end).
    replace 4%nat with (q + (4 - q))%nat at 1 by lia. rewrite sub_split. f_equal. f_equal. lia.
  Qed.

  Lemma skipn_sb : forall j (q m : nat), (0 <= j)%Z ->
      skipn q (sb_ j m) = sb_ (j + Z.of_nat q) (m - q).
  Proof using Hlen Hn HOK n src dst mem0 segs.
    intros j q m Hj. (lazymatch goal with |- ?G => let G' := eval unfold sb_, sub in G in change_no_check G' end). rewrite skipn_firstn_comm, <- skipn_add. f_equal. f_equal. lia.
  Qed.

  Lemma firstn_sb : forall j (q m : nat), (q <= m)%nat -> firstn q (sb_ j m) = sb_ j q.
  Proof using Hlen Hn HOK n src dst mem0 segs. intros j q m Hq. (lazymatch goal with |- ?G => let G' := eval unfold sb_, sub in G in change_no_check G' end). rewrite firstn_firstn. f_equal. lia. Qed.

  (* [comment removed for export] *)
  Lemma merge_sb : forall j (q : nat) (v : word),
      (0 <= j)%Z -> (j + 8 <= n)%Z -> (1 <= q <= 3)%nat ->
      v = v_or (v_slli (LWv (sb_ (j + 4) 4)) (32 - 8 * Z.of_nat q)) (v_srliw (LWv (sb_ j 4)) (8 * Z.of_nat q)) ->
      word_to_le_bytes 4 v = sb_ (j + Z.of_nat q) 4.
  Proof using Hlen Hn HOK src dst mem0 segs.
    intros j q v Hj H8 Hq Hv.
    rewrite (sw_bytes_merge (sb_ j 4) (sb_ (j + 4) 4) q v); try (apply sb_len; lia); try assumption.
    rewrite skipn_sb, firstn_sb by lia.
    rewrite (sb4_split (j + Z.of_nat q) (4 - q)) by lia.
    f_equal. f_equal; lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) (memk k) rom).
  Proof using Hnwd Hnws Hdisj Hsrc Hlen Hn HOK.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_lw : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 4 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LWv (sb_ j 4))) (v_addi pc 4) (memk k) rom).
  Proof using Hnwd Hnws Hdisj Hsrc Hlen Hn HOK.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj4.
    eapply step_lw; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_src k j 4); lia.
    - symmetry. apply u_lez4. apply sb_len; lia.
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
  Proof using Hnwd Hdst Hlen Hn HOK src.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
    rewrite <- (memk_extend1 k (b_ k)) by (lia || reflexivity).
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = sb_ k 4 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 4)) rom).
  Proof using Hnwd Hdst Hlen Hn HOK src.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk4.
    replace (k + 4)%Z with (k + Z.of_nat 4)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 4) 4) by (lia || reflexivity).
    rewrite <- Hb.
    eapply step_sw_at; [exact Hf | exact He | exact Hd | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sw_val_plain : forall k, (0 <= k)%Z -> (k + 4 <= n)%Z ->
    word_to_le_bytes 4 (LWv (sb_ k 4)) = sb_ k 4.
  Proof using Hlen Hn HOK src dst mem0 segs. intros k Hk H4. apply sw_bytes_LWv. apply sb_len; lia. Qed.

  (* [comment removed for export] *)
  Lemma sb_val_plain : forall k, Z_to_bv 8 (bv_unsigned (LBv (b_ k))) = b_ k.
  Proof using. intros k. apply sb_byte_LBv. Qed.

  Lemma sb_val_srli : forall j (q : nat), (0 <= j)%Z -> (j + 4 <= n)%Z -> (q <= 3)%nat ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) (8 * Z.of_nat q))) = b_ (j + Z.of_nat q).
  Proof using Hlen Hn HOK src dst mem0 segs.
    intros j q Hj H4 Hq. rewrite sb_byte_srli_LWv; [| apply sb_len; lia | exact Hq].
    (lazymatch goal with |- ?G => let G' := eval unfold sb_, b_, sub in G in change_no_check G' end).
    rewrite nth_firstn. replace (q <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_skipn. f_equal. lia.
  Qed.

  Lemma sb_val_word0 : forall j, (0 <= j)%Z -> (j + 4 <= n)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ j.
  Proof using Hlen Hn HOK src dst mem0 segs.
    intros j Hj H4.
    pose proof (sb_val_srli j 0 Hj H4 ltac:(lia)) as E.
    rewrite Z.add_0_r in E. rewrite <- E. f_equal. f_equal.
    (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma merge_s16 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 16) (v_srliw (LWv (sb_ j1 4)) 16) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 2)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof using Hlen Hn HOK src dst mem0 segs.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 2)%Z with (j1 + Z.of_nat 2)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma merge_s8 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 24) (v_srliw (LWv (sb_ j1 4)) 8) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 1)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof using Hlen Hn HOK src dst mem0 segs.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 1)%Z with (j1 + Z.of_nat 1)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma merge_s24 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 8) (v_srliw (LWv (sb_ j1 4)) 24) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 3)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof using Hlen Hn HOK src dst mem0 segs.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 3)%Z with (j1 + Z.of_nat 3)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma sb_val_srli8 : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j + 1)%Z ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) 8)) = b_ k.
  Proof using Hlen Hn HOK src dst mem0 segs.
    intros j k Hj H4 ->. replace (j + 1)%Z with (j + Z.of_nat 1)%Z by lia.
    rewrite <- (sb_val_srli j 1) by lia. reflexivity.
  Qed.

  Lemma sb_val_srli16 : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j + 2)%Z ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) 16)) = b_ k.
  Proof using Hlen Hn HOK src dst mem0 segs.
    intros j k Hj H4 ->. replace (j + 2)%Z with (j + Z.of_nat 2)%Z by lia.
    rewrite <- (sb_val_srli j 2) by lia. reflexivity.
  Qed.

  Lemma sb_val_word0' : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ k.
  Proof using Hlen Hn HOK src dst mem0 segs. intros j k Hj H4 ->. apply sb_val_word0; lia. Qed.

End MC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End FPGen1.

Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

(* [comment removed for export] *)
Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.

(* [comment removed for export] *)
Ltac cond_lia :=
  rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, c_eq, bv_ltu, bv_eqb in G in change_no_check G' end); imm_norm; unorm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.


Lemma u_andi : forall (x : word) imm, (0 <= imm < 2 ^ 64)%Z ->
  bv_unsigned (v_andi x imm) = Z.land (bv_unsigned x) imm.
Proof using.
  intros x imm Hi. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 imm) with imm by (symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. apply Z_land_range; [apply u64_range|lia].
Qed.

Lemma land_3 : forall a, (0 <= a)%Z -> Z.land a 3 = (a mod 4)%Z.
Proof using. intros a Ha. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.


(* [comment removed for export] *)
Lemma bits_lt32 : forall m, (0 <= m < 32)%Z ->
  (Z.land m 16 = 0 \/ Z.land m 16 = 16)%Z /\ (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z /\
  (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z /\ (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z /\
  (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z /\
  (m = Z.land m 16 + Z.land m 8 + Z.land m 4 + Z.land m 2 + Z.land m 1)%Z.
Proof using.
  intros m Hm.
  assert (E : exists k : nat, m = Z.of_nat k /\ (k < 32)%nat).
  { exists (Z.to_nat m). split; lia. }
  destruct E as (k & -> & Hk).
  do 32 (destruct k as [|k]; [vm_compute; intuition lia|]). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MF.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.

  Lemma MF_000 : fetch_word segs (at_ base 0) = Some W_f52e4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 0 _ HCODE eq_refl). Qed.
  Lemma MF_004 : fetch_word segs (at_ base 4) = Some W_f52e8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 1 _ HCODE eq_refl). Qed.
  Lemma MF_008 : fetch_word segs (at_ base 8) = Some W_f52ec.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 2 _ HCODE eq_refl). Qed.
  Lemma MF_00c : fetch_word segs (at_ base 12) = Some W_f52f0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 3 _ HCODE eq_refl). Qed.
  Lemma MF_010 : fetch_word segs (at_ base 16) = Some W_f52f4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 4 _ HCODE eq_refl). Qed.
  Lemma MF_014 : fetch_word segs (at_ base 20) = Some W_f52f8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 5 _ HCODE eq_refl). Qed.
  Lemma MF_018 : fetch_word segs (at_ base 24) = Some W_f52fc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 6 _ HCODE eq_refl). Qed.
  Lemma MF_01c : fetch_word segs (at_ base 28) = Some W_f5300.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 7 _ HCODE eq_refl). Qed.
  Lemma MF_020 : fetch_word segs (at_ base 32) = Some W_f5304.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 8 _ HCODE eq_refl). Qed.
  Lemma MF_024 : fetch_word segs (at_ base 36) = Some W_f5308.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 9 _ HCODE eq_refl). Qed.
  Lemma MF_028 : fetch_word segs (at_ base 40) = Some W_f530c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 10 _ HCODE eq_refl). Qed.
  Lemma MF_02c : fetch_word segs (at_ base 44) = Some W_f5310.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 11 _ HCODE eq_refl). Qed.
  Lemma MF_030 : fetch_word segs (at_ base 48) = Some W_f5314.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 12 _ HCODE eq_refl). Qed.
  Lemma MF_034 : fetch_word segs (at_ base 52) = Some W_f5318.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 13 _ HCODE eq_refl). Qed.
  Lemma MF_038 : fetch_word segs (at_ base 56) = Some W_f531c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 14 _ HCODE eq_refl). Qed.
  Lemma MF_03c : fetch_word segs (at_ base 60) = Some W_f5320.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 15 _ HCODE eq_refl). Qed.
  Lemma MF_040 : fetch_word segs (at_ base 64) = Some W_f5324.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 16 _ HCODE eq_refl). Qed.
  Lemma MF_044 : fetch_word segs (at_ base 68) = Some W_f5328.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 17 _ HCODE eq_refl). Qed.
  Lemma MF_048 : fetch_word segs (at_ base 72) = Some W_f532c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 18 _ HCODE eq_refl). Qed.
  Lemma MF_04c : fetch_word segs (at_ base 76) = Some W_f5330.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 19 _ HCODE eq_refl). Qed.
  Lemma MF_050 : fetch_word segs (at_ base 80) = Some W_f5334.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 20 _ HCODE eq_refl). Qed.
  Lemma MF_054 : fetch_word segs (at_ base 84) = Some W_f5338.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 21 _ HCODE eq_refl). Qed.
  Lemma MF_058 : fetch_word segs (at_ base 88) = Some W_f533c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 22 _ HCODE eq_refl). Qed.
  Lemma MF_05c : fetch_word segs (at_ base 92) = Some W_f5340.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 23 _ HCODE eq_refl). Qed.
  Lemma MF_060 : fetch_word segs (at_ base 96) = Some W_f5344.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 24 _ HCODE eq_refl). Qed.
  Lemma MF_064 : fetch_word segs (at_ base 100) = Some W_f5348.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 25 _ HCODE eq_refl). Qed.
  Lemma MF_068 : fetch_word segs (at_ base 104) = Some W_f534c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 26 _ HCODE eq_refl). Qed.
  Lemma MF_06c : fetch_word segs (at_ base 108) = Some W_f5350.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 27 _ HCODE eq_refl). Qed.
  Lemma MF_070 : fetch_word segs (at_ base 112) = Some W_f5354.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 28 _ HCODE eq_refl). Qed.
  Lemma MF_074 : fetch_word segs (at_ base 116) = Some W_f5358.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 29 _ HCODE eq_refl). Qed.
  Lemma MF_078 : fetch_word segs (at_ base 120) = Some W_f535c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 30 _ HCODE eq_refl). Qed.
  Lemma MF_07c : fetch_word segs (at_ base 124) = Some W_f5360.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 31 _ HCODE eq_refl). Qed.
  Lemma MF_080 : fetch_word segs (at_ base 128) = Some W_f5364.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 32 _ HCODE eq_refl). Qed.
  Lemma MF_084 : fetch_word segs (at_ base 132) = Some W_f5368.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 33 _ HCODE eq_refl). Qed.
  Lemma MF_088 : fetch_word segs (at_ base 136) = Some W_f536c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 34 _ HCODE eq_refl). Qed.
  Lemma MF_08c : fetch_word segs (at_ base 140) = Some W_f5370.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 35 _ HCODE eq_refl). Qed.
  Lemma MF_090 : fetch_word segs (at_ base 144) = Some W_f5374.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 36 _ HCODE eq_refl). Qed.
  Lemma MF_094 : fetch_word segs (at_ base 148) = Some W_f5378.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 37 _ HCODE eq_refl). Qed.
  Lemma MF_098 : fetch_word segs (at_ base 152) = Some W_f537c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 38 _ HCODE eq_refl). Qed.
  Lemma MF_09c : fetch_word segs (at_ base 156) = Some W_f5380.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 39 _ HCODE eq_refl). Qed.
  Lemma MF_0a0 : fetch_word segs (at_ base 160) = Some W_f5384.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 40 _ HCODE eq_refl). Qed.
  Lemma MF_0a4 : fetch_word segs (at_ base 164) = Some W_f5388.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 41 _ HCODE eq_refl). Qed.
  Lemma MF_0a8 : fetch_word segs (at_ base 168) = Some W_f538c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 42 _ HCODE eq_refl). Qed.
  Lemma MF_0ac : fetch_word segs (at_ base 172) = Some W_f5390.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 43 _ HCODE eq_refl). Qed.
  Lemma MF_0b0 : fetch_word segs (at_ base 176) = Some W_f5394.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 44 _ HCODE eq_refl). Qed.
  Lemma MF_0b4 : fetch_word segs (at_ base 180) = Some W_f5398.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 45 _ HCODE eq_refl). Qed.
  Lemma MF_0b8 : fetch_word segs (at_ base 184) = Some W_f539c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 46 _ HCODE eq_refl). Qed.
  Lemma MF_0bc : fetch_word segs (at_ base 188) = Some W_f53a0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 47 _ HCODE eq_refl). Qed.
  Lemma MF_0c0 : fetch_word segs (at_ base 192) = Some W_f53a4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 48 _ HCODE eq_refl). Qed.
  Lemma MF_0c4 : fetch_word segs (at_ base 196) = Some W_f53a8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 49 _ HCODE eq_refl). Qed.
  Lemma MF_0c8 : fetch_word segs (at_ base 200) = Some W_f53ac.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 50 _ HCODE eq_refl). Qed.
  Lemma MF_0cc : fetch_word segs (at_ base 204) = Some W_f53b0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 51 _ HCODE eq_refl). Qed.
  Lemma MF_0d0 : fetch_word segs (at_ base 208) = Some W_f53b4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 52 _ HCODE eq_refl). Qed.
  Lemma MF_0d4 : fetch_word segs (at_ base 212) = Some W_f53b8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 53 _ HCODE eq_refl). Qed.
  Lemma MF_0d8 : fetch_word segs (at_ base 216) = Some W_f53bc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 54 _ HCODE eq_refl). Qed.
  Lemma MF_0dc : fetch_word segs (at_ base 220) = Some W_f53c0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 55 _ HCODE eq_refl). Qed.
  Lemma MF_0e0 : fetch_word segs (at_ base 224) = Some W_f53c4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 56 _ HCODE eq_refl). Qed.
  Lemma MF_0e4 : fetch_word segs (at_ base 228) = Some W_f53c8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 57 _ HCODE eq_refl). Qed.
  Lemma MF_0e8 : fetch_word segs (at_ base 232) = Some W_f53cc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 58 _ HCODE eq_refl). Qed.
  Lemma MF_0ec : fetch_word segs (at_ base 236) = Some W_f53d0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 59 _ HCODE eq_refl). Qed.
  Lemma MF_0f0 : fetch_word segs (at_ base 240) = Some W_f53d4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 60 _ HCODE eq_refl). Qed.
  Lemma MF_0f4 : fetch_word segs (at_ base 244) = Some W_f53d8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 61 _ HCODE eq_refl). Qed.
  Lemma MF_0f8 : fetch_word segs (at_ base 248) = Some W_f53dc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 62 _ HCODE eq_refl). Qed.
  Lemma MF_0fc : fetch_word segs (at_ base 252) = Some W_f53e0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 63 _ HCODE eq_refl). Qed.
  Lemma MF_100 : fetch_word segs (at_ base 256) = Some W_f53e4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 64 _ HCODE eq_refl). Qed.
  Lemma MF_104 : fetch_word segs (at_ base 260) = Some W_f53e8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 65 _ HCODE eq_refl). Qed.
  Lemma MF_108 : fetch_word segs (at_ base 264) = Some W_f53ec.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 66 _ HCODE eq_refl). Qed.
  Lemma MF_10c : fetch_word segs (at_ base 268) = Some W_f53f0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 67 _ HCODE eq_refl). Qed.
  Lemma MF_110 : fetch_word segs (at_ base 272) = Some W_f53f4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 68 _ HCODE eq_refl). Qed.
  Lemma MF_114 : fetch_word segs (at_ base 276) = Some W_f53f8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 69 _ HCODE eq_refl). Qed.
  Lemma MF_118 : fetch_word segs (at_ base 280) = Some W_f53fc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 70 _ HCODE eq_refl). Qed.
  Lemma MF_11c : fetch_word segs (at_ base 284) = Some W_f5400.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 71 _ HCODE eq_refl). Qed.
  Lemma MF_120 : fetch_word segs (at_ base 288) = Some W_f5404.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 72 _ HCODE eq_refl). Qed.
  Lemma MF_124 : fetch_word segs (at_ base 292) = Some W_f5408.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 73 _ HCODE eq_refl). Qed.
  Lemma MF_128 : fetch_word segs (at_ base 296) = Some W_f540c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 74 _ HCODE eq_refl). Qed.
  Lemma MF_12c : fetch_word segs (at_ base 300) = Some W_f5410.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 75 _ HCODE eq_refl). Qed.
  Lemma MF_130 : fetch_word segs (at_ base 304) = Some W_f5414.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 76 _ HCODE eq_refl). Qed.
  Lemma MF_134 : fetch_word segs (at_ base 308) = Some W_f5418.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 77 _ HCODE eq_refl). Qed.
  Lemma MF_138 : fetch_word segs (at_ base 312) = Some W_f541c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 78 _ HCODE eq_refl). Qed.
  Lemma MF_13c : fetch_word segs (at_ base 316) = Some W_f5420.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 79 _ HCODE eq_refl). Qed.
  Lemma MF_140 : fetch_word segs (at_ base 320) = Some W_f5424.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 80 _ HCODE eq_refl). Qed.
  Lemma MF_144 : fetch_word segs (at_ base 324) = Some W_f5428.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 81 _ HCODE eq_refl). Qed.
  Lemma MF_148 : fetch_word segs (at_ base 328) = Some W_f542c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 82 _ HCODE eq_refl). Qed.
  Lemma MF_14c : fetch_word segs (at_ base 332) = Some W_f5430.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 83 _ HCODE eq_refl). Qed.
  Lemma MF_150 : fetch_word segs (at_ base 336) = Some W_f5434.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 84 _ HCODE eq_refl). Qed.
  Lemma MF_154 : fetch_word segs (at_ base 340) = Some W_f5438.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 85 _ HCODE eq_refl). Qed.
  Lemma MF_158 : fetch_word segs (at_ base 344) = Some W_f543c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 86 _ HCODE eq_refl). Qed.
  Lemma MF_15c : fetch_word segs (at_ base 348) = Some W_f5440.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 87 _ HCODE eq_refl). Qed.
  Lemma MF_160 : fetch_word segs (at_ base 352) = Some W_f5444.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 88 _ HCODE eq_refl). Qed.
  Lemma MF_164 : fetch_word segs (at_ base 356) = Some W_f5448.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 89 _ HCODE eq_refl). Qed.
  Lemma MF_168 : fetch_word segs (at_ base 360) = Some W_f544c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 90 _ HCODE eq_refl). Qed.
  Lemma MF_16c : fetch_word segs (at_ base 364) = Some W_f5450.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 91 _ HCODE eq_refl). Qed.
  Lemma MF_170 : fetch_word segs (at_ base 368) = Some W_f5454.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 92 _ HCODE eq_refl). Qed.
  Lemma MF_174 : fetch_word segs (at_ base 372) = Some W_f5458.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 93 _ HCODE eq_refl). Qed.
  Lemma MF_178 : fetch_word segs (at_ base 376) = Some W_f545c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 94 _ HCODE eq_refl). Qed.
  Lemma MF_17c : fetch_word segs (at_ base 380) = Some W_f5460.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 95 _ HCODE eq_refl). Qed.
  Lemma MF_180 : fetch_word segs (at_ base 384) = Some W_f5464.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 96 _ HCODE eq_refl). Qed.
  Lemma MF_184 : fetch_word segs (at_ base 388) = Some W_f5468.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 97 _ HCODE eq_refl). Qed.
  Lemma MF_188 : fetch_word segs (at_ base 392) = Some W_f546c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 98 _ HCODE eq_refl). Qed.
  Lemma MF_18c : fetch_word segs (at_ base 396) = Some W_f5470.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 99 _ HCODE eq_refl). Qed.
  Lemma MF_190 : fetch_word segs (at_ base 400) = Some W_f5474.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 100 _ HCODE eq_refl). Qed.
  Lemma MF_194 : fetch_word segs (at_ base 404) = Some W_f5478.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 101 _ HCODE eq_refl). Qed.
  Lemma MF_198 : fetch_word segs (at_ base 408) = Some W_f547c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 102 _ HCODE eq_refl). Qed.
  Lemma MF_19c : fetch_word segs (at_ base 412) = Some W_f5480.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 103 _ HCODE eq_refl). Qed.
  Lemma MF_1a0 : fetch_word segs (at_ base 416) = Some W_f5484.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 104 _ HCODE eq_refl). Qed.
  Lemma MF_1a4 : fetch_word segs (at_ base 420) = Some W_f5488.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 105 _ HCODE eq_refl). Qed.
  Lemma MF_1a8 : fetch_word segs (at_ base 424) = Some W_f548c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 106 _ HCODE eq_refl). Qed.
  Lemma MF_1ac : fetch_word segs (at_ base 428) = Some W_f5490.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 107 _ HCODE eq_refl). Qed.
  Lemma MF_1b0 : fetch_word segs (at_ base 432) = Some W_f5494.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 108 _ HCODE eq_refl). Qed.
  Lemma MF_1b4 : fetch_word segs (at_ base 436) = Some W_f5498.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 109 _ HCODE eq_refl). Qed.
  Lemma MF_1b8 : fetch_word segs (at_ base 440) = Some W_f549c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 110 _ HCODE eq_refl). Qed.
  Lemma MF_1bc : fetch_word segs (at_ base 444) = Some W_f54a0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 111 _ HCODE eq_refl). Qed.
  Lemma MF_1c0 : fetch_word segs (at_ base 448) = Some W_f54a4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 112 _ HCODE eq_refl). Qed.
  Lemma MF_1c4 : fetch_word segs (at_ base 452) = Some W_f54a8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 113 _ HCODE eq_refl). Qed.
  Lemma MF_1c8 : fetch_word segs (at_ base 456) = Some W_f54ac.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 114 _ HCODE eq_refl). Qed.
  Lemma MF_1cc : fetch_word segs (at_ base 460) = Some W_f54b0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 115 _ HCODE eq_refl). Qed.
  Lemma MF_1d0 : fetch_word segs (at_ base 464) = Some W_f54b4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 116 _ HCODE eq_refl). Qed.
  Lemma MF_1d4 : fetch_word segs (at_ base 468) = Some W_f54b8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 117 _ HCODE eq_refl). Qed.
  Lemma MF_1d8 : fetch_word segs (at_ base 472) = Some W_f54bc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 118 _ HCODE eq_refl). Qed.
  Lemma MF_1dc : fetch_word segs (at_ base 476) = Some W_f54c0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 119 _ HCODE eq_refl). Qed.
  Lemma MF_1e0 : fetch_word segs (at_ base 480) = Some W_f54c4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 120 _ HCODE eq_refl). Qed.
  Lemma MF_1e4 : fetch_word segs (at_ base 484) = Some W_f54c8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 121 _ HCODE eq_refl). Qed.
  Lemma MF_1e8 : fetch_word segs (at_ base 488) = Some W_f54cc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 122 _ HCODE eq_refl). Qed.
  Lemma MF_1ec : fetch_word segs (at_ base 492) = Some W_f54d0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 123 _ HCODE eq_refl). Qed.
  Lemma MF_1f0 : fetch_word segs (at_ base 496) = Some W_f54d4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 124 _ HCODE eq_refl). Qed.
  Lemma MF_1f4 : fetch_word segs (at_ base 500) = Some W_f54d8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 125 _ HCODE eq_refl). Qed.
  Lemma MF_1f8 : fetch_word segs (at_ base 504) = Some W_f54dc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 126 _ HCODE eq_refl). Qed.
  Lemma MF_1fc : fetch_word segs (at_ base 508) = Some W_f54e0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 127 _ HCODE eq_refl). Qed.
  Lemma MF_200 : fetch_word segs (at_ base 512) = Some W_f54e4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 128 _ HCODE eq_refl). Qed.
  Lemma MF_204 : fetch_word segs (at_ base 516) = Some W_f54e8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 129 _ HCODE eq_refl). Qed.
  Lemma MF_208 : fetch_word segs (at_ base 520) = Some W_f54ec.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 130 _ HCODE eq_refl). Qed.
  Lemma MF_20c : fetch_word segs (at_ base 524) = Some W_f54f0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 131 _ HCODE eq_refl). Qed.
  Lemma MF_210 : fetch_word segs (at_ base 528) = Some W_f54f4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 132 _ HCODE eq_refl). Qed.
  Lemma MF_214 : fetch_word segs (at_ base 532) = Some W_f54f8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 133 _ HCODE eq_refl). Qed.
  Lemma MF_218 : fetch_word segs (at_ base 536) = Some W_f54fc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 134 _ HCODE eq_refl). Qed.
  Lemma MF_21c : fetch_word segs (at_ base 540) = Some W_f5500.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 135 _ HCODE eq_refl). Qed.
  Lemma MF_220 : fetch_word segs (at_ base 544) = Some W_f5504.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 136 _ HCODE eq_refl). Qed.
  Lemma MF_224 : fetch_word segs (at_ base 548) = Some W_f5508.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 137 _ HCODE eq_refl). Qed.
  Lemma MF_228 : fetch_word segs (at_ base 552) = Some W_f550c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 138 _ HCODE eq_refl). Qed.
  Lemma MF_22c : fetch_word segs (at_ base 556) = Some W_f5510.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 139 _ HCODE eq_refl). Qed.
  Lemma MF_230 : fetch_word segs (at_ base 560) = Some W_f5514.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 140 _ HCODE eq_refl). Qed.
  Lemma MF_234 : fetch_word segs (at_ base 564) = Some W_f5518.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 141 _ HCODE eq_refl). Qed.
  Lemma MF_238 : fetch_word segs (at_ base 568) = Some W_f551c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 142 _ HCODE eq_refl). Qed.
  Lemma MF_23c : fetch_word segs (at_ base 572) = Some W_f5520.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 143 _ HCODE eq_refl). Qed.
  Lemma MF_240 : fetch_word segs (at_ base 576) = Some W_f5524.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 144 _ HCODE eq_refl). Qed.
  Lemma MF_244 : fetch_word segs (at_ base 580) = Some W_f5528.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 145 _ HCODE eq_refl). Qed.
  Lemma MF_248 : fetch_word segs (at_ base 584) = Some W_f552c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 146 _ HCODE eq_refl). Qed.
  Lemma MF_24c : fetch_word segs (at_ base 588) = Some W_f5530.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 147 _ HCODE eq_refl). Qed.
  Lemma MF_250 : fetch_word segs (at_ base 592) = Some W_f5534.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 148 _ HCODE eq_refl). Qed.
  Lemma MF_254 : fetch_word segs (at_ base 596) = Some W_f5538.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 149 _ HCODE eq_refl). Qed.
  Lemma MF_258 : fetch_word segs (at_ base 600) = Some W_f553c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 150 _ HCODE eq_refl). Qed.
  Lemma MF_25c : fetch_word segs (at_ base 604) = Some W_f5540.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 151 _ HCODE eq_refl). Qed.
  Lemma MF_260 : fetch_word segs (at_ base 608) = Some W_f5544.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 152 _ HCODE eq_refl). Qed.
  Lemma MF_264 : fetch_word segs (at_ base 612) = Some W_f5548.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 153 _ HCODE eq_refl). Qed.
  Lemma MF_268 : fetch_word segs (at_ base 616) = Some W_f554c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 154 _ HCODE eq_refl). Qed.
  Lemma MF_26c : fetch_word segs (at_ base 620) = Some W_f5550.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 155 _ HCODE eq_refl). Qed.
  Lemma MF_270 : fetch_word segs (at_ base 624) = Some W_f5554.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 156 _ HCODE eq_refl). Qed.
  Lemma MF_274 : fetch_word segs (at_ base 628) = Some W_f5558.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 157 _ HCODE eq_refl). Qed.
  Lemma MF_278 : fetch_word segs (at_ base 632) = Some W_f555c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 158 _ HCODE eq_refl). Qed.
  Lemma MF_27c : fetch_word segs (at_ base 636) = Some W_f5560.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 159 _ HCODE eq_refl). Qed.
  Lemma MF_280 : fetch_word segs (at_ base 640) = Some W_f5564.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 160 _ HCODE eq_refl). Qed.
  Lemma MF_284 : fetch_word segs (at_ base 644) = Some W_f5568.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 161 _ HCODE eq_refl). Qed.
  Lemma MF_288 : fetch_word segs (at_ base 648) = Some W_f556c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 162 _ HCODE eq_refl). Qed.
  Lemma MF_28c : fetch_word segs (at_ base 652) = Some W_f5570.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 163 _ HCODE eq_refl). Qed.
  Lemma MF_290 : fetch_word segs (at_ base 656) = Some W_f5574.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 164 _ HCODE eq_refl). Qed.
  Lemma MF_294 : fetch_word segs (at_ base 660) = Some W_f5578.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 165 _ HCODE eq_refl). Qed.
  Lemma MF_298 : fetch_word segs (at_ base 664) = Some W_f557c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 166 _ HCODE eq_refl). Qed.
  Lemma MF_29c : fetch_word segs (at_ base 668) = Some W_f5580.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 167 _ HCODE eq_refl). Qed.
  Lemma MF_2a0 : fetch_word segs (at_ base 672) = Some W_f5584.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 168 _ HCODE eq_refl). Qed.
  Lemma MF_2a4 : fetch_word segs (at_ base 676) = Some W_f5588.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 169 _ HCODE eq_refl). Qed.
  Lemma MF_2a8 : fetch_word segs (at_ base 680) = Some W_f558c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 170 _ HCODE eq_refl). Qed.
  Lemma MF_2ac : fetch_word segs (at_ base 684) = Some W_f5590.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 171 _ HCODE eq_refl). Qed.
  Lemma MF_2b0 : fetch_word segs (at_ base 688) = Some W_f5594.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 172 _ HCODE eq_refl). Qed.
  Lemma MF_2b4 : fetch_word segs (at_ base 692) = Some W_f5598.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 173 _ HCODE eq_refl). Qed.
  Lemma MF_2b8 : fetch_word segs (at_ base 696) = Some W_f559c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 174 _ HCODE eq_refl). Qed.
  Lemma MF_2bc : fetch_word segs (at_ base 700) = Some W_f55a0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 175 _ HCODE eq_refl). Qed.
  Lemma MF_2c0 : fetch_word segs (at_ base 704) = Some W_f55a4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 176 _ HCODE eq_refl). Qed.
  Lemma MF_2c4 : fetch_word segs (at_ base 708) = Some W_f55a8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 177 _ HCODE eq_refl). Qed.
  Lemma MF_2c8 : fetch_word segs (at_ base 712) = Some W_f55ac.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 178 _ HCODE eq_refl). Qed.
  Lemma MF_2cc : fetch_word segs (at_ base 716) = Some W_f55b0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 179 _ HCODE eq_refl). Qed.
  Lemma MF_2d0 : fetch_word segs (at_ base 720) = Some W_f55b4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 180 _ HCODE eq_refl). Qed.
  Lemma MF_2d4 : fetch_word segs (at_ base 724) = Some W_f55b8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 181 _ HCODE eq_refl). Qed.
  Lemma MF_2d8 : fetch_word segs (at_ base 728) = Some W_f55bc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 182 _ HCODE eq_refl). Qed.
  Lemma MF_2dc : fetch_word segs (at_ base 732) = Some W_f55c0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 183 _ HCODE eq_refl). Qed.
  Lemma MF_2e0 : fetch_word segs (at_ base 736) = Some W_f55c4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 184 _ HCODE eq_refl). Qed.
  Lemma MF_2e4 : fetch_word segs (at_ base 740) = Some W_f55c8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 185 _ HCODE eq_refl). Qed.
  Lemma MF_2e8 : fetch_word segs (at_ base 744) = Some W_f55cc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 186 _ HCODE eq_refl). Qed.
  Lemma MF_2ec : fetch_word segs (at_ base 748) = Some W_f55d0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 187 _ HCODE eq_refl). Qed.
  Lemma MF_2f0 : fetch_word segs (at_ base 752) = Some W_f55d4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 188 _ HCODE eq_refl). Qed.
  Lemma MF_2f4 : fetch_word segs (at_ base 756) = Some W_f55d8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 189 _ HCODE eq_refl). Qed.
  Lemma MF_2f8 : fetch_word segs (at_ base 760) = Some W_f55dc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 190 _ HCODE eq_refl). Qed.
  Lemma MF_2fc : fetch_word segs (at_ base 764) = Some W_f55e0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 191 _ HCODE eq_refl). Qed.
  Lemma MF_300 : fetch_word segs (at_ base 768) = Some W_f55e4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 192 _ HCODE eq_refl). Qed.
  Lemma MF_304 : fetch_word segs (at_ base 772) = Some W_f55e8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 193 _ HCODE eq_refl). Qed.
  Lemma MF_308 : fetch_word segs (at_ base 776) = Some W_f55ec.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 194 _ HCODE eq_refl). Qed.
  Lemma MF_30c : fetch_word segs (at_ base 780) = Some W_f55f0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 195 _ HCODE eq_refl). Qed.
  Lemma MF_310 : fetch_word segs (at_ base 784) = Some W_f55f4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 196 _ HCODE eq_refl). Qed.
  Lemma MF_314 : fetch_word segs (at_ base 788) = Some W_f55f8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 197 _ HCODE eq_refl). Qed.
  Lemma MF_318 : fetch_word segs (at_ base 792) = Some W_f55fc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 198 _ HCODE eq_refl). Qed.
  Lemma MF_31c : fetch_word segs (at_ base 796) = Some W_f5600.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 199 _ HCODE eq_refl). Qed.
  Lemma MF_320 : fetch_word segs (at_ base 800) = Some W_f5604.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 200 _ HCODE eq_refl). Qed.
  Lemma MF_324 : fetch_word segs (at_ base 804) = Some W_f5608.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 201 _ HCODE eq_refl). Qed.
  Lemma MF_328 : fetch_word segs (at_ base 808) = Some W_f560c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 202 _ HCODE eq_refl). Qed.
  Lemma MF_32c : fetch_word segs (at_ base 812) = Some W_f5610.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 203 _ HCODE eq_refl). Qed.
  Lemma MF_330 : fetch_word segs (at_ base 816) = Some W_f5614.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 204 _ HCODE eq_refl). Qed.
  Lemma MF_334 : fetch_word segs (at_ base 820) = Some W_f5618.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 205 _ HCODE eq_refl). Qed.
  Lemma MF_338 : fetch_word segs (at_ base 824) = Some W_f561c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 206 _ HCODE eq_refl). Qed.
  Lemma MF_33c : fetch_word segs (at_ base 828) = Some W_f5620.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 207 _ HCODE eq_refl). Qed.
  Lemma MF_340 : fetch_word segs (at_ base 832) = Some W_f5624.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 208 _ HCODE eq_refl). Qed.
  Lemma MF_344 : fetch_word segs (at_ base 836) = Some W_f5628.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 209 _ HCODE eq_refl). Qed.
  Lemma MF_348 : fetch_word segs (at_ base 840) = Some W_f562c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 210 _ HCODE eq_refl). Qed.
  Lemma MF_34c : fetch_word segs (at_ base 844) = Some W_f5630.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 211 _ HCODE eq_refl). Qed.
  Lemma MF_350 : fetch_word segs (at_ base 848) = Some W_f5634.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 212 _ HCODE eq_refl). Qed.
  Lemma MF_354 : fetch_word segs (at_ base 852) = Some W_f5638.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 213 _ HCODE eq_refl). Qed.
  Lemma MF_358 : fetch_word segs (at_ base 856) = Some W_f563c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 214 _ HCODE eq_refl). Qed.
  Lemma MF_35c : fetch_word segs (at_ base 860) = Some W_f5640.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 215 _ HCODE eq_refl). Qed.
  Lemma MF_360 : fetch_word segs (at_ base 864) = Some W_f5644.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 216 _ HCODE eq_refl). Qed.
  Lemma MF_364 : fetch_word segs (at_ base 868) = Some W_f5648.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 217 _ HCODE eq_refl). Qed.
  Lemma MF_368 : fetch_word segs (at_ base 872) = Some W_f564c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 218 _ HCODE eq_refl). Qed.
  Lemma MF_36c : fetch_word segs (at_ base 876) = Some W_f5650.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 219 _ HCODE eq_refl). Qed.
  Lemma MF_370 : fetch_word segs (at_ base 880) = Some W_f5654.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 220 _ HCODE eq_refl). Qed.
  Lemma MF_374 : fetch_word segs (at_ base 884) = Some W_f5658.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 221 _ HCODE eq_refl). Qed.
  Lemma MF_378 : fetch_word segs (at_ base 888) = Some W_f565c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 222 _ HCODE eq_refl). Qed.
  Lemma MF_37c : fetch_word segs (at_ base 892) = Some W_f5660.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 223 _ HCODE eq_refl). Qed.
  Lemma MF_380 : fetch_word segs (at_ base 896) = Some W_f5664.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 224 _ HCODE eq_refl). Qed.
  Lemma MF_384 : fetch_word segs (at_ base 900) = Some W_f5668.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 225 _ HCODE eq_refl). Qed.
  Lemma MF_388 : fetch_word segs (at_ base 904) = Some W_f566c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 226 _ HCODE eq_refl). Qed.
  Lemma MF_38c : fetch_word segs (at_ base 908) = Some W_f5670.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 227 _ HCODE eq_refl). Qed.
  Lemma MF_390 : fetch_word segs (at_ base 912) = Some W_f5674.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 228 _ HCODE eq_refl). Qed.
  Lemma MF_394 : fetch_word segs (at_ base 916) = Some W_f5678.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 229 _ HCODE eq_refl). Qed.
  Lemma MF_398 : fetch_word segs (at_ base 920) = Some W_f567c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 230 _ HCODE eq_refl). Qed.
  Lemma MF_39c : fetch_word segs (at_ base 924) = Some W_f5680.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 231 _ HCODE eq_refl). Qed.
  Lemma MF_3a0 : fetch_word segs (at_ base 928) = Some W_f5684.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 232 _ HCODE eq_refl). Qed.
  Lemma MF_3a4 : fetch_word segs (at_ base 932) = Some W_f5688.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 233 _ HCODE eq_refl). Qed.
  Lemma MF_3a8 : fetch_word segs (at_ base 936) = Some W_f568c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 234 _ HCODE eq_refl). Qed.
  Lemma MF_3ac : fetch_word segs (at_ base 940) = Some W_f5690.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 235 _ HCODE eq_refl). Qed.
  Lemma MF_3b0 : fetch_word segs (at_ base 944) = Some W_f5694.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 236 _ HCODE eq_refl). Qed.
  Lemma MF_3b4 : fetch_word segs (at_ base 948) = Some W_f5698.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 237 _ HCODE eq_refl). Qed.
  Lemma MF_3b8 : fetch_word segs (at_ base 952) = Some W_f569c.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 238 _ HCODE eq_refl). Qed.
  Lemma MF_3bc : fetch_word segs (at_ base 956) = Some W_f56a0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 239 _ HCODE eq_refl). Qed.
  Lemma MF_3c0 : fetch_word segs (at_ base 960) = Some W_f56a4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 240 _ HCODE eq_refl). Qed.
  Lemma MF_3c4 : fetch_word segs (at_ base 964) = Some W_f56a8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 241 _ HCODE eq_refl). Qed.
  Lemma MF_3c8 : fetch_word segs (at_ base 968) = Some W_f56ac.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 242 _ HCODE eq_refl). Qed.
  Lemma MF_3cc : fetch_word segs (at_ base 972) = Some W_f56b0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 243 _ HCODE eq_refl). Qed.
  Lemma MF_3d0 : fetch_word segs (at_ base 976) = Some W_f56b4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 244 _ HCODE eq_refl). Qed.
  Lemma MF_3d4 : fetch_word segs (at_ base 980) = Some W_f56b8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 245 _ HCODE eq_refl). Qed.
  Lemma MF_3d8 : fetch_word segs (at_ base 984) = Some W_f56bc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 246 _ HCODE eq_refl). Qed.
  Lemma MF_3dc : fetch_word segs (at_ base 988) = Some W_f56c0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 247 _ HCODE eq_refl). Qed.
  Lemma MF_3e0 : fetch_word segs (at_ base 992) = Some W_f56c4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 248 _ HCODE eq_refl). Qed.
  Lemma MF_3e4 : fetch_word segs (at_ base 996) = Some W_f56c8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 249 _ HCODE eq_refl). Qed.
  Lemma MF_3e8 : fetch_word segs (at_ base 1000) = Some W_f56cc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 250 _ HCODE eq_refl). Qed.
  Lemma MF_3ec : fetch_word segs (at_ base 1004) = Some W_f56d0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 251 _ HCODE eq_refl). Qed.
  Lemma MF_3f0 : fetch_word segs (at_ base 1008) = Some W_f56d4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 252 _ HCODE eq_refl). Qed.
  Lemma MF_3f4 : fetch_word segs (at_ base 1012) = Some W_f56d8.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 253 _ HCODE eq_refl). Qed.
  Lemma MF_3f8 : fetch_word segs (at_ base 1016) = Some W_f56dc.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 254 _ HCODE eq_refl). Qed.
  Lemma MF_3fc : fetch_word segs (at_ base 1020) = Some W_f56e0.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 255 _ HCODE eq_refl). Qed.
  Lemma MF_400 : fetch_word segs (at_ base 1024) = Some W_f56e4.
  Proof using HCODE. exact (code_at_get segs base 0 mmemcpy_words 256 _ HCODE eq_refl). Qed.
End MF.
End FPGen2.


