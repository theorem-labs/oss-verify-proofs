(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Hoare Frame
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  Spec. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0ExitBase_u Bs0MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibTail.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0ReadErr_defs_u Bs0ReadErr_tail_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.


(* [comment removed for export] *)
Definition re_ivs : list (Z * Z) :=
  [(0x10000,0xb8500); (0xb8501,0xb8549); (0xc8549,0xc9ef0); (0xe9fc8,0xe9fe8); (0xc9f24,0xc9f70); (0xc9f78,0xc9f90);
   (0xc9f98,0xc9fb0); (0xc9fc0,0xc9fd0); (0xc9fd8,0xe9fc8); (0xea000,0xea230); (0xea238,0xea240); (0xea251,0xea258);
   (0xea260,0xea268); (0xea278,0xea280); (0xea288,0xea2b8);
   (0xea788,0xeb000)]%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.
Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, (lo <= i < hi)%Z -> M (Z_to_bv 64 i) = None.

Section ReadErr.
  Context {RE : RunEnv}.
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

  (* [comment removed for export] *)
  Theorem re_tail : forall (path : list byte) (pp : word) (t8 : list byte) vals R M,
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    (bv_unsigned sp0 <= bv_unsigned pp)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    regs_ok (ENV BL vals) srRE0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x344a8) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error path) (m_fs model)).
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
    unfold t_die.
    eapply (re_segBC scfg sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    eapply (re_segF scfg sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid : Z) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0xc9fc0.
  Hypothesis Rs2 : getr R 18 = pp.
  (* [comment removed for export] *)
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mtid : cell M 0xc9f18 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mself : cell M 0xc9ef8 8 0xc9ef8.
  (* [comment removed for export] *)
  Hypothesis Mcanary : forall i, (0 <= i < 8)%Z -> M (Z_to_bv 64 (0xea230 + i)) = Some (nth (Z.to_nat i) (nth 2 BL []) (Z_to_bv 8 0)).
  Hypothesis Lcanary : length (nth 2 BL []) = 8%nat.
  Hypothesis Mpagesz : cell M 0xea280 8 4096.
  (* [comment removed for export] *)
  Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.

  Definition valsRE : list word :=
    [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 0].
  Let E : env := ENV BL valsRE.

  Lemma valsRE_len : length valsRE = 39%nat.
  Proof. unfold valsRE. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  Lemma evRE_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRE.
    change (6 + i)%nat with (length [sp0; pp; pp; pp; pp; Z_to_bv 64 tid] + i)%nat.
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
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRE.
  Qed.

  Lemma img_clear_of : forall lo hi, In (lo, hi) re_ivs -> img_clear M lo hi.
  Proof. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.

  Ltac kimg := split; [lia|]; split; [lia|]; apply img_clear_of; cbn; tauto.
  Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                 rewrite adenot_lit0; cbn [edenot];
                 first [exact H | rewrite H; reflexivity | idtac].

  Lemma know_okRE : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knRE0.
  Proof.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold know_ok, knRE0.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - (* [comment removed for export] *) split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
    - change (edenot E (EVar 0)) with sp0. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
      replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia.
      apply Mstack; lia.
    - change (edenot E (EVar 2)) with pp. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mself.
    - kcell Mtid.
    - kimg. - kimg. - kimg. - kimg. - kimg. - kimg.
    - (* [comment removed for export] *)
      unfold elenZ, estart. cbn [edenot a_base a_off eb E ENV blobs_ev]. rewrite ?(u_small 8), ?(u_small 0) by lia.
      split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?(u_small 0) by lia; lia|].
      split; [unfold blobs_ev; rewrite Lcanary; reflexivity|].
      intros i Hi. replace (0 + 959024 + i)%Z with (959024 + i)%Z by lia. unfold blobs_ev. apply Mcanary. lia.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mpagesz.
    - kimg.
    - kimg.
    - change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_read_error : forall (path : list byte) (t8 : list byte),
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) <= 60)%Z ->
    (bv_unsigned pp + Z.of_nat (length path) + 8 <= bv_unsigned sp0 + 4194304)%Z ->
    rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8 ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x344a8) M (seg_rom RSEGS)) model)
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
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x344a8) M (seg_rom RSEGS)) model)
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
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
