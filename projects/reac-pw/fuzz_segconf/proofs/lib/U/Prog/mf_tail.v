(** m_file (UBSan build, image 1696d6c34ffd): the piece S_MF_TAIL of U/Prog/m_file_c.v (family F3).
    The tail 0x146b4-0x146bc: `lbu a0, 0(s2)` reads the first byte of the text left (its NUL when it is empty:
    cstr_at), `bnez` goes back to the head 0x14348 with the same state (H_MF_HEAD n: the text is nonempty and still
    shorter than n), else `j` the epilogue 0x14980 (H_MF_EXIT with the loop's post, whose final model is the state
    itself: lines [] = []). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_tok_bridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c.
Import ListNotations.
Open Scope Z_scope.

(** The first byte of a C string: its first character, or its NUL. *)
Lemma mf_cstr_first : forall m p s, cstr_at rsegs m p s ->
  exists b : byte, ov_read_bytes rsegs m (wa (p + Z.of_nat 0)) 1 = Some [b] /\
    (s = [] -> bv_unsigned b = 0) /\ (s <> [] -> bv_unsigned b <> 0).
Proof.
  intros m p s HC.
  destruct (cstr_cut rsegs m p s HC) as (bs & sl & HB & Hz & Hnz & Hn & Hlen & _ & _).
  destruct bs as [|b0 bs].
  - exists ZERO. rewrite (bytes_at_ov_read rsegs m p _ 0 1 HB) by (cbn; lia). cbn.
    split; [reflexivity|]. split; [intros _; reflexivity|]. intros Hs. exfalso. apply Hs. rewrite <- Hz. reflexivity.
  - exists b0. rewrite (bytes_at_ov_read rsegs m p _ 0 1 HB) by (cbn; lia). cbn.
    split; [reflexivity|]. split; [intros Hs; rewrite <- Hz in Hs; discriminate Hs|].
    intros _ E. apply Hnz. rewrite <- Hz. cbn. left. exact E.
Qed.

Lemma mf_tail_holds : S_MF_TAIL.
Proof.
  unfold S_MF_TAIL, H_MF_TAIL. intros n HH HX.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest Hn HL HR.
  pose proof HL as HL0.
  destruct HL as (Hsp & HS & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  Hp0 & _ & HC & _ & _ & HPE & _ & _ & HSO & MI).
  pose proof HR as (E0 & E2 & E3 & E4 & E6 & E7 & E8 & E9 & E10 & E11).
  destruct (mf_cstr_first m p rest HC) as (b & RD & Hb0 & Hb1).
  rewrite E2. unfold M_FILE_TAIL.
  step.
  destruct rest as [|r0 rs].
  - (* the text is empty: the epilogue *)
    specialize (Hb0 eq_refl).
    step. if_cases K; cbv iota.
    + exfalso. zify_cond K. pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
      rewrite unsigned_lit in K by lia. lia.
    + step. unfold M_FILE_EXIT in HX.
      destruct HPE as (HF & TM & _ & _ & _). destruct HSO as (ST & _ & _ & _).
      eapply HX; [exact Hsp | exact HS | exact HF | exact MI | exact TM | exact ST | exact HM].
  - (* a line follows: the head *)
    assert (Hne : r0 :: rs <> []) by discriminate. specialize (Hb1 Hne).
    step. if_cases K; cbv iota.
    + rewrite <- E2. eapply HH; [exact Hn | exact Hne | exact HL0 | exact HR].
    + exfalso. zify_cond K. pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
      rewrite unsigned_lit in K by lia. lia.
Qed.
