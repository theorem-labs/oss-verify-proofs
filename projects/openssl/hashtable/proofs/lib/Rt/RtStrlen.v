(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk
  RefMemcpyLib SumsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_istrlen_0 : bv 32 := 0x00000593.
Lemma D_istrlen_0 : decode_any W_istrlen_0 = Some (OpImm ALU_ADD 11 0 0, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_istrlen_4 : bv 32 := 0x00b50633.
Lemma D_istrlen_4 : decode_any W_istrlen_4 = Some (Op ALU_ADD 12 10 11, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_istrlen_8 : bv 32 := 0x00064603.
Lemma D_istrlen_8 : decode_any W_istrlen_8 = Some (Load SZ1 false 12 12 0, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_istrlen_12 : bv 32 := 0x00158593.
Lemma D_istrlen_12 : decode_any W_istrlen_12 = Some (OpImm ALU_ADD 11 11 1, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_istrlen_16 : bv 32 := 0xfe061ae3.
Lemma D_istrlen_16 : decode_any W_istrlen_16 = Some (Branch BC_NE 12 0 8180, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_istrlen_20 : bv 32 := 0xfff58513.
Lemma D_istrlen_20 : decode_any W_istrlen_20 = Some (OpImm ALU_ADD 10 11 4095, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_istrlen_24 : bv 32 := 0x00008067.
Lemma D_istrlen_24 : decode_any W_istrlen_24 = Some (Jalr 0 1 0, 4%Z). Proof. vm_refl. Qed.

Definition istrlen_words : list (bv 32) :=
  [W_istrlen_0; W_istrlen_4; W_istrlen_8; W_istrlen_12; W_istrlen_16; W_istrlen_20; W_istrlen_24].

(* [comment removed for export] *)
Definition istrlen_clob : list reg := [10; 11; 12].

(* [comment removed for export] *)
Record strH (segs : list Segment) (mem : word -> option byte) (s : word) (buf : list byte) (K : Z) : Prop := STRH {
  sHrd  : rdn segs mem s (length buf) = Some buf;
  sHnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  sHK   : (0 <= K)%Z;
  sHKlt : (Z.to_nat K < length buf)%nat;
  sHnul : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  sHnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z }.

Lemma istrlen_code_of_code_at : forall segs base,
  code_at segs base 0 istrlen_words ->
  fetch_word segs (at_ base 0) = Some W_istrlen_0 /\ fetch_word segs (at_ base 4) = Some W_istrlen_4 /\
  fetch_word segs (at_ base 8) = Some W_istrlen_8 /\ fetch_word segs (at_ base 12) = Some W_istrlen_12 /\
  fetch_word segs (at_ base 16) = Some W_istrlen_16 /\ fetch_word segs (at_ base 20) = Some W_istrlen_20 /\
  fetch_word segs (at_ base 24) = Some W_istrlen_24.
Proof. intros segs base H. cbn [code_at istrlen_words] in H. cbn in H. tauto. Qed.

Section ISTRLEN.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem : word -> option byte.
  Variable s : word.
  Variable buf : list byte.
  Variable K : Z.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Hypothesis HCODE :
    fetch_word segs (at_ base 0) = Some W_istrlen_0 /\ fetch_word segs (at_ base 4) = Some W_istrlen_4 /\
    fetch_word segs (at_ base 8) = Some W_istrlen_8 /\ fetch_word segs (at_ base 12) = Some W_istrlen_12 /\
    fetch_word segs (at_ base 16) = Some W_istrlen_16 /\ fetch_word segs (at_ base 20) = Some W_istrlen_20 /\
    fetch_word segs (at_ base 24) = Some W_istrlen_24.
  Hypothesis HOK : strH segs mem s buf K.

  #[local] Abbreviation CL := (fun r => In r istrlen_clob).

  Let Hrd := sHrd _ _ _ _ _ HOK.
  Let Hnw := sHnw _ _ _ _ _ HOK.
  Let HK := sHK _ _ _ _ _ HOK.
  Let HKlt := sHKlt _ _ _ _ _ HOK.
  Let Hnul := sHnul _ _ _ _ _ HOK.
  Let Hnz := sHnz _ _ _ _ _ HOK.

  Definition b_ (j : Z) : byte := nth (Z.to_nat j) buf (Z_to_bv 8 0).

  Lemma rd1 : forall j, (0 <= j)%Z -> (Z.to_nat j < length buf)%nat ->
    rdn segs mem (at_ s j) 1 = Some [b_ j].
  Proof.
    intros j Hj Hlt. unfold b_.
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    rewrite (rdn_sub segs mem (length buf) s buf (Z.to_nat j) 1 Hrd) by lia.
    rewrite sub_nth by lia. reflexivity.
  Qed.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24).

  (* [comment removed for export] *)
  Lemma istrlen_loop : forall (d : nat) regs (ret : word) (i : Z),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 11 = Z_to_bv 64 i ->
    (0 <= i <= K)%Z -> Z.of_nat d = (K - i)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 4) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. pose proof (u64_range s) as Hs.
    assert (HKb : (K < 2 ^ 64)%Z) by lia.
    induction d as [|d IH]; intros regs ret i Hret H1 H10 H11 Hi Hd.
    - (* [comment removed for export] *)
      assert (EK : i = K) by lia. subst i.
      eexists. split; [|split].
      + stepiv C4 D_istrlen_4 (at_ s K) ltac:(gres; rwH; rewrite v_add_at by lia; reflexivity); vn.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lbu with (b := b_ K); [exact C8 | reflexivity | exact D_istrlen_8
            | gres; rwH; imm_norm; rewrite v_addi_0; apply rd1; [lia | exact HKlt] ]
          | step_simpl]; vn.                                                                                (* [comment removed for export] *)
        stepiv C12 D_istrlen_12 (Z_to_bv 64 (K + 1)) ltac:(gres; rwH; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity); vn. (* [comment removed for export] *)
        ab_ft C16 D_istrlen_16 ltac:(pose proof (u8_range (b_ K)) as HB8; pose proof Hnul as HN; fold (b_ K) in HN; condz). (* [comment removed for export] *)
        stepiv C20 D_istrlen_20 (Z_to_bv 64 K) ltac:(gres; rwH; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; apply f_equal; lia); vn.   (* [comment removed for export] *)
        aret C24 D_istrlen_24 ret. apply mst_refl.
      + gres. reflexivity.
      + unfold istrlen_clob. solve_regs_agree.
    - (* [comment removed for export] *)
      assert (Hlt : (i < K)%Z) by lia.
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 4) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 (i + 1) /\ regs_agree CL regs r)).
      + eexists. split.
        * stepiv C4 D_istrlen_4 (at_ s i) ltac:(gres; rwH; rewrite v_add_at by lia; reflexivity); vn.
          chain_step; [reflexivity
            | eapply step_lbu with (b := b_ i); [exact C8 | reflexivity | exact D_istrlen_8
              | gres; rwH; imm_norm; rewrite v_addi_0; apply rd1; lia ]
            | step_simpl]; vn.
          stepiv C12 D_istrlen_12 (Z_to_bv 64 (i + 1)) ltac:(gres; rwH; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity); vn.
          ab_tk C16 D_istrlen_16 ltac:(pose proof (u8_range (b_ i)) as HB8; pose proof (Hnz (Z.to_nat i) ltac:(lia)) as HN; fold (b_ i) in HN; condz).
          apply mst_refl.
        * post. unfold istrlen_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R10 & R11 & AG).
        destruct (IH r1 ret (i + 1)%Z Hret R1 R10 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & AG2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply regs_agree_trans; eassumption]].
  Qed.

  Theorem istrlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K
      /\ regs_agree CL regs regs'.
  Proof.
    intros regs ret Hret H1 H10. get_code.
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 4) mem rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ regs_agree CL regs r)).
    - eexists. split; [an C0 D_istrlen_0; apply mst_refl | post; unfold istrlen_clob; solve_regs_agree].
    - cbv beta. intros r1 (R1 & R10 & R11 & AG).
      destruct (istrlen_loop (Z.to_nat K) r1 ret 0 Hret R1 R10 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & AG2).
      exists r2. split; [exact RUN | split; [exact A10 | eapply regs_agree_trans; eassumption]].
  Qed.
End ISTRLEN.
