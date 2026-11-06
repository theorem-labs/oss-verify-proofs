(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_7ff10_80b0c.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.










































































































































































































































































































































































































(* [comment removed for export] *)
Definition W_80afc : bv 32 := @BV 32 0x00000593%Z I.

Lemma D_80afc : decode_any W_80afc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b00 : bv 32 := @BV 32 0x00b50633%Z I.

Lemma D_80b00 : decode_any W_80b00 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b04 : bv 32 := @BV 32 0x00064603%Z I.

Lemma D_80b04 : decode_any W_80b04 = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b08 : bv 32 := @BV 32 0x00158593%Z I.

Lemma D_80b08 : decode_any W_80b08 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_7ff10_80b0c.
Module Bo_code_80b0c_815a0.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_80b0c : bv 32 := @BV 32 0xfe061ae3%Z I.

Lemma D_80b0c : decode_any W_80b0c = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b10 : bv 32 := @BV 32 0xfff58513%Z I.

Lemma D_80b10 : decode_any W_80b10 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80b14 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_80b14 : decode_any W_80b14 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81188 : bv 32 := @BV 32 0xfffff637%Z I.
Lemma F_81188 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x81188%Z I : word) = Some W_81188.
Proof. vm_refl. Qed.
Lemma D_81188 : decode_any W_81188 = Some (Lui (@BV 5 12%Z I) (@BV 20 1048575%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8118c : bv 32 := @BV 32 0x0016069b%Z I.
Lemma F_8118c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8118c%Z I : word) = Some W_8118c.
Proof. vm_refl. Qed.
Lemma D_8118c : decode_any W_8118c = Some (OpImm32 (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81190 : bv 32 := @BV 32 0x00d56863%Z I.
Lemma F_81190 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x81190%Z I : word) = Some W_81190.
Proof. vm_refl. Qed.
Lemma D_81190 : decode_any W_81190 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 13%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81194 : bv 32 := @BV 32 0x00058663%Z I.
Lemma F_81194 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x81194%Z I : word) = Some W_81194.
Proof. vm_refl. Qed.
Lemma D_81194 : decode_any W_81194 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81198 : bv 32 := @BV 32 0x40a006bb%Z I.
Lemma F_81198 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x81198%Z I : word) = Some W_81198.
Proof. vm_refl. Qed.
Lemma D_81198 : decode_any W_81198 = Some (Op32 ALU_SUB (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8119c : bv 32 := @BV 32 0x00d5a023%Z I.
Lemma F_8119c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8119c%Z I : word) = Some W_8119c.
Proof. vm_refl. Qed.
Lemma D_8119c : decode_any W_8119c = Some (Store SZ4 (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811a0 : bv 32 := @BV 32 0x00a63533%Z I.
Lemma F_811a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811a0%Z I : word) = Some W_811a0.
Proof. vm_refl. Qed.
Lemma D_811a0 : decode_any W_811a0 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811a4 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_811a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811a4%Z I : word) = Some W_811a4.
Proof. vm_refl. Qed.
Lemma D_811a4 : decode_any W_811a4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811a8 : bv 32 := @BV 32 0x0de00893%Z I.
Lemma F_811a8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811a8%Z I : word) = Some W_811a8.
Proof. vm_refl. Qed.
Lemma D_811a8 : decode_any W_811a8 = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 222%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811ac : bv 32 := @BV 32 0x00000073%Z I.
Lemma F_811ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811ac%Z I : word) = Some W_811ac.
Proof. vm_refl. Qed.

Lemma E_811ac : is_ecall W_811ac = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_811b0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_811b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811b0%Z I : word) = Some W_811b0.
Proof. vm_refl. Qed.
Lemma D_811b0 : decode_any W_811b0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811b4 : bv 32 := @BV 32 0x0d700893%Z I.
Lemma F_811b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811b4%Z I : word) = Some W_811b4.
Proof. vm_refl. Qed.
Lemma D_811b4 : decode_any W_811b4 = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 215%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811b8 : bv 32 := @BV 32 0x00000073%Z I.
Lemma F_811b8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811b8%Z I : word) = Some W_811b8.
Proof. vm_refl. Qed.

Lemma E_811b8 : is_ecall W_811b8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_811bc : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_811bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811bc%Z I : word) = Some W_811bc.
Proof. vm_refl. Qed.
Lemma D_811bc : decode_any W_811bc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.






End Bo_code_80b0c_815a0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct Bo_code_7ff10_80b0c Bo_code_80b0c_815a0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.

Definition istrlen_words : list (bv 32) := [W_80afc; W_80b00; W_80b04; W_80b08; W_80b0c; W_80b10; W_80b14]%list.
Definition istrlen_clob : list reg := [10; 11; 12].

Section ISTRLEN.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem : word -> option byte.
  Variable s : word.
  Variable K : Z.                 (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 istrlen_words.
  Hypothesis HK : (0 <= K)%Z /\ (bv_unsigned s + K + 1 < 2 ^ 64)%Z.
  Hypothesis Hnz : forall j, (0 <= j < K)%Z -> exists b : byte, rdn segs mem (at_ s j) 1 = Some [b] /\ bv_unsigned b <> 0%Z.
  Hypothesis Hz : rdn segs mem (at_ s K) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation CL := (fun r => In r istrlen_clob).

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at istrlen_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D bb Hrd :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := bb);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi, ?at_add_0_r; exact Hrd]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma istrlen_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 11 = Z_to_bv 64 j ->
    (0 <= j <= K)%Z -> Z.of_nat i = (K - j)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 4) mem rom) (mkst regs' ret mem rom)
      /\ regs_agree CL regs regs'
      /\ getr regs' 10 = Z_to_bv 64 K /\ getr regs' 11 = Z_to_bv 64 (K + 1) /\ getr regs' 12 = Z_to_bv 64 0.
  Proof.
    get_code. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H11 Hj Hi.
    - assert (j = K) by lia. subst j.
      eexists. split; [|split].
      + av C4 D_80b00 (at_ s K) ltac:(unfold at_, v_add; unorm; f_equal; lia).            (* [comment removed for export] *)
        mlbu C8 D_80b04 (Z_to_bv 8 0) Hz.                                         (* [comment removed for export] *)
        av C12 D_80b08 (Z_to_bv 64 (K + 1)) ltac:(unfold v_addi; unorm; f_equal; lia).   (* [comment removed for export] *)
        ab_ft C16 D_80b0c ltac:(condz).                                           (* [comment removed for export] *)
        av C20 D_80b10 (Z_to_bv 64 K) ltac:(unfold v_addi; unorm; f_equal; lia).  (* [comment removed for export] *)
        aret C24 D_80b14 ret.
        apply mst_refl.
      + unfold istrlen_clob. solve_regs_agree.
      + post.
    - destruct (Hnz j ltac:(lia)) as (b & Hb & Hb0). pose proof (u8_range b) as Rb.
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 4) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 (j + 1) /\ regs_agree CL regs r)).
      + eexists. split.
        * av C4 D_80b00 (at_ s j) ltac:(unfold at_, v_add; unorm; f_equal; lia).
          mlbu C8 D_80b04 b Hb.
          av C12 D_80b08 (Z_to_bv 64 (j + 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
          ab_tk C16 D_80b0c ltac:(condz).                                         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold istrlen_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R10 & R11 & AG).
        destruct (IH r1 ret (j + 1)%Z Hret R1 R10 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P).
        exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  Theorem istrlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret mem rom)
      /\ regs_agree CL regs regs'
      /\ getr regs' 10 = Z_to_bv 64 K /\ getr regs' 11 = Z_to_bv 64 (K + 1) /\ getr regs' 12 = Z_to_bv 64 0.
  Proof.
    get_code. intros regs ret Hret H1 H10.
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 4) mem rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ regs_agree CL regs r)).
    - eexists. split.
      + an C0 D_80afc.                                                            (* [comment removed for export] *)
        apply mst_refl.
      + post. unfold istrlen_clob. solve_regs_agree.
    - cbv beta. intros r1 (R1 & R10 & R11 & AG).
      destruct (istrlen_loop (Z.to_nat K) r1 ret 0 Hret R1 R10 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P).
      exists r2. split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.
End ISTRLEN.

(* [comment removed for export] *)
Lemma both_istrlen_code : code_at AsanUbsan.M.loaded_segments (0x80afc : word) 0 istrlen_words.
Proof. unfold istrlen_words. code_at_vm. Qed.

End FPGen1.
