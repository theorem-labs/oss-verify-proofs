(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibTail SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1RwWindow U1KnCells S1Spec U1ExitBase U1Cells U1RKn U1MainEntry.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1ReadErr_defs U1ReadErr_tail.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXALL1.
Context {fx : FPState}.

Definition re_ivs : list (Z * Z) := Eval cbv in rimg_ivs.
Lemma re_ivs_eq : re_ivs = rimg_ivs. Proof. reflexivity. Qed.

Section ReadErr.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Theorem re_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV BL vals) srRE0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65a68) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
    unfold t_die.
    eapply (re_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    eapply (re_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
  Qed.

  Variables (pp : word) (tid can : Z) (R : bvmap 5 word) (M : word -> option byte).

  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x102418.
  Hypothesis Rs2 : getr R 18 = pp.

  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0x102370 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0x102350 8 0x102350.
  Hypothesis Mcanary : cell M 0x122688 8 can.
  Hypothesis Hcan : (0 <= can < 2 ^ 64)%Z.
  Hypothesis Mpagesz : cell M 0x1226d8 8 4096.
  Hypothesis Mnlocks : cell M 0x1226ab 1 0.
  Hypothesis Mcells : drv_cells_ok M.

  Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.

  Definition valsRE : list word :=
    [sp0; pp; pp; pp; Z_to_bv 64 can; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 0].
  Let E : env := ENV BL valsRE.

  Lemma valsRE_len : length valsRE = 39%nat.
  Proof. unfold valsRE. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma evRE_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRE.
    change (6 + i)%nat with (length [sp0; pp; pp; pp; Z_to_bv 64 can; Z_to_bv 64 tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spxRE_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Ltac reg_caseRE :=
    cbn [nth srRE0 all_regs];
    first [ rewrite spxRE_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRE_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp | exact Rs2
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRE : regs_ok E srRE0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply U1MainEntry.regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRE.
  Qed.

  Lemma img_clear_of : forall lo hi, In (lo, hi) re_ivs -> img_clear M lo hi.
  Proof. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.

  Fixpoint ivs_index (lo hi : Z) (l : list (Z * Z)) (k : nat) : option nat :=
    match l with
    | [] => None
    | (a, b) :: r => if ((a =? lo) && (b =? hi))%Z%bool then Some k else ivs_index lo hi r (S k)
    end.
  Lemma img_clear_nth : forall k lo hi, nth_error re_ivs k = Some (lo, hi) -> img_clear M lo hi.
  Proof. intros k lo hi Hk. apply img_clear_of. eapply nth_error_In. exact Hk. Qed.

  Ltac kimg := split; [lia|]; split; [lia|];
    lazymatch goal with |- forall i, (?lo <= i < ?hi)%Z -> _ =>
      let r := eval vm_compute in (ivs_index lo hi re_ivs 0) in
      lazymatch r with Some ?k => apply (img_clear_nth k); vm_compute; reflexivity end end.
  Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                 rewrite adenot_lit0; cbn [edenot];
                 first [exact H | rewrite H; reflexivity].

  Lemma know_okRE : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knRE0.
  Proof.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold knRE0. unfold know_ok. rewrite Forall_app. split; [|apply know_drv_cells; exact Mcells].
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    1:{   split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal. }
    1:{ change (edenot E (EVar 0)) with sp0. lia. }
    1:{   split; [apply flat_intro; cbn; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
        replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia.
        apply Mstack; lia. }
    1:{ change (edenot E (EVar 2)) with pp. lia. }
    1:{   split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
        apply store_ok_rwZ; lia. }
    all: first [ kimg | kcell Mself | kcell Mtid | kcell Mnlocks | kcell Mpagesz
               | (split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                  rewrite adenot_lit0; change (edenot E (EVar 4)) with (Z_to_bv 64 can : word); exact Mcanary)
               | change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word); rewrite u_small by lia; lia ].
  Qed.

  Theorem ref_read_error : forall (path : list byte) (t8 : list byte),
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65a68) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
  Proof.
    intros path t8 Hnonul HPl Hpp2 Hstr Ht8.
    eapply (re_tail path pp t8 valsRE R M); try eassumption.
    - apply valsRE_len.
    - reflexivity.
    - reflexivity.
    - apply regs_okRE.
    - apply know_okRE. lia.
  Qed.

  Corollary ref_read_error_dot : forall (t8 : list byte),
    (bv_unsigned pp + 9 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0] ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8 ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65a68) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
  Proof.
    intros t8 Hpp2 Hstr Ht8.
    apply (ref_read_error dot_path t8).
    - cbn. intros [E0|[]]. apply (f_equal bv_unsigned) in E0. vm_compute in E0. lia.
    - cbn. lia.
    - cbn [length dot_path Z.of_nat Pos.of_succ_nat]. lia.
    - exact Hstr.
    - exact Ht8.
  Qed.
End ReadErr.

End FXALL1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
