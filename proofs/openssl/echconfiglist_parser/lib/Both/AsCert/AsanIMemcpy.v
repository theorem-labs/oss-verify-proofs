(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SumsLib Sums_code.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition imemcpy_words : list (bv 32) :=
  [W_a9a8c; W_a9a90; W_a9a94; W_a9a98; W_a9a9c; W_a9aa0; W_a9aa4; W_a9aa8; W_a9aac].

(* [comment removed for export] *)
Definition imemcpy_clob : list reg := [11; 12; 13; 14].

Section IMEMCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 imemcpy_words.
  Hypothesis HOK : cpyH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation B := (b_ bs).
  #[local] Abbreviation CL := (fun r => In r imemcpy_clob).
  Let Hn0 : (0 <= n)%Z := cHn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemcpy_words Z.add Pos.add Pos.succ] in HC;
    (* [comment removed for export] *)
    code_nth HC HCODE imemcpy_words 0%nat C0; code_nth HC HCODE imemcpy_words 1%nat C4; code_nth HC HCODE imemcpy_words 2%nat C8;
    code_nth HC HCODE imemcpy_words 3%nat C12; code_nth HC HCODE imemcpy_words 4%nat C16; code_nth HC HCODE imemcpy_words 5%nat C20;
    code_nth HC HCODE imemcpy_words 6%nat C24; code_nth HC HCODE imemcpy_words 7%nat C28; code_nth HC HCODE imemcpy_words 8%nat C32;
    clear HC.

  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | apply sb_val_b | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma imemcpy_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = at_ dst n ->
    (0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 12) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - (* [comment removed for export] *)
      eexists. split.
      + mlbu C12 D_a9a98 k.                       (* [comment removed for export] *)
        msb C16 D_a9a9c k.                        (* [comment removed for export] *)
        an C20 D_a9aa0.                           (* [comment removed for export] *)
        an C24 D_a9aa4.                           (* [comment removed for export] *)
        ab_ft C28 D_a9aa8 ltac:(condz).           (* [comment removed for export] *)
        aret C32 D_a9aac ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemcpy_clob. solve_regs_agree.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C12 D_a9a98 k.
          msb C16 D_a9a9c k.
          an C20 D_a9aa0.
          an C24 D_a9aa4.
          ab_tk C28 D_a9aa8 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Theorem imemcpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    rewrite <- (memk_n _ _ _ _ _ _ HOK). change mem0 with (MK 0).
    destruct (Z.eq_dec n 0) as [Hz|Hnz].
    - (* [comment removed for export] *)
      eexists. split.
      + ab_tk C0 D_a9a8c ltac:(condz).            (* [comment removed for export] *)
        aret C32 D_a9aac ret.
        rewrite Hz. apply mst_refl.
      + apply regs_agree_refl.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_ft C0 D_a9a8c ltac:(condz).          (* [comment removed for export] *)
          av C4 D_a9a90 (at_ dst n) ltac:(apply v_add_at; lia).  (* [comment removed for export] *)
          an C8 D_a9a94.                          (* [comment removed for export] *)
          apply mst_refl.
        * post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_imemcpy_entry : word := 0x1d0fa0.

Lemma asan_imemcpy_code :
  code_at AsanUbsan.M.loaded_segments asan_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem asan_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
  cpyH AsanUbsan.M.loaded_segments mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs asan_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 asan_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom asan_imemcpy_code HOK).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
