(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr MState Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Ey6n DA_Eg3i DA_Cells DA_Entry DA_Mib4 DA_Inv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition RA_MAIN : Z := 0x982ac.     (* [comment removed for export] *)
Definition MAIN_PC : Z := 0x86918.

Section S.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  (* [comment removed for export] *)
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation argc := (e_argc argv).

  (* [comment removed for export] *)
  Definition main_cfg (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) : config :=
    mkCfg (MS (mkR (wz RA_MAIN) (wz (SPM usp)) gp (wz TPV) t0 t1 t2 s0 s1 (wz argc) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz MAIN_PC) fc None m rom) md.

  (* [comment removed for export] *)
  Definition usage_stmt : Prop :=
    forall gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A,
      dinv usp argv envp fs A m md usp fds_std SO_pristine 0 -> entry_A0 usp (e_span argv envp) A ->
      argc <> 2 ->
      srealizes rsegs (main_cfg gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md)
                (t_die (msg_usage (hd [] argv)) fs).

  Definition open_fail_stmt' : Prop :=
    forall gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A a0s path,
      dinv usp argv envp fs A m md usp fds_std SO_pristine 0 -> entry_A0 usp (e_span argv envp) A ->
      argv = [a0s; path] ->
      (   (4096 <= length path)%nat
       \/ path = []
       \/ (path <> [] /\ path <> dot_path /\ (length path <= 4095)%nat /\ fs_lookup fs path = None)) ->
      srealizes rsegs (main_cfg gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md)
                (t_die (msg_cannot_open path) fs).

  Definition dir_stmt : Prop :=
    forall gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A a0s,
      dinv usp argv envp fs A m md usp fds_std SO_pristine 0 -> entry_A0 usp (e_span argv envp) A ->
      argv = [a0s; dot_path] ->
      srealizes rsegs (main_cfg gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md)
                (t_alt2 (t_die (msg_cannot_open dot_path) fs) (t_opened_dir dot_path fs)).

  Definition file_stmt : Prop :=
    forall gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A a0s path data,
      dinv usp argv envp fs A m md usp fds_std SO_pristine 0 -> entry_A0 usp (e_span argv envp) A ->
      argv = [a0s; path] -> path <> [] -> path <> dot_path -> (length path <= 4095)%nat ->
      fs_lookup fs path = Some data ->
      srealizes rsegs (main_cfg gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md)
                (t_alt2 (t_die (msg_cannot_open path) fs) (t_opened data fs)).

  Hypothesis USAGE : usage_stmt.
  Hypothesis OPENFAIL : open_fail_stmt'.
  Hypothesis DIR : dir_stmt.
  Hypothesis FILE : file_stmt.
  Hypothesis Hva : valid_argv argv.

  Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
  Proof.
    induction p as [|a p IH]; intros [|b q]; cbn; split; intros H; try discriminate; try reflexivity.
    - apply andb_prop in H as [H1 H2]. apply bv_eqb_eq in H1. apply IH in H2. subst. reflexivity.
    - injection H as <- <-. apply andb_true_iff. split; [apply bv_eqb_refl| apply IH; reflexivity].
  Qed.

  Lemma len2 : forall l : list (list byte), length l = 2%nat -> l = [nth 0 l []; nth 1 l []].
  Proof. intros [|a [|b [|c l]]] H; cbn in H; try lia. reflexivity. Qed.
  Lemma spec_usage : forall (l : list (list byte)) fs0, length l <> 2%nat -> spec l fs0 = t_die (msg_usage (hd [] l)) fs0.
  Proof. intros [|a [|b [|c l]]] fs0 H; cbn in H |- *; try reflexivity. lia. Qed.

  Theorem main_realizes :
    forall gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A,
      dinv usp argv envp fs A m md usp fds_std SO_pristine 0 -> entry_A0 usp (e_span argv envp) A ->
      srealizes rsegs (main_cfg gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md)
                (spec argv fs).
  Proof.
    intros until md. intros A DI EA.
    destruct (Nat.eq_dec (length argv) 2) as [L2|N2].
    2:{ rewrite (spec_usage argv fs N2). eapply USAGE; [exact DI| exact EA| unfold e_argc; lia]. }
    pose proof (len2 argv L2) as AV. set (a0s := nth 0 argv []) in AV. set (path := nth 1 argv []) in AV.
    replace (spec argv fs) with (spec [a0s; path] fs) by (rewrite <- AV; reflexivity).
    cbn [spec].
    destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
    - eapply OPENFAIL; [exact DI| exact EA| exact AV|]. left. exact Hlong.
    - destruct (list_byte_eqb path []) eqn:Hemp.
      + apply list_byte_eqb_eq in Hemp.
        eapply OPENFAIL; [exact DI| exact EA| exact AV|]. right. left. exact Hemp.
      + assert (Hne : path <> []) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
        destruct (list_byte_eqb path dot_path) eqn:Hdot.
        * apply list_byte_eqb_eq in Hdot. rewrite Hdot in AV |- *.
          eapply DIR; [exact DI| exact EA| exact AV].
        * assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
          destruct (fs_lookup fs path) as [data|] eqn:Hlk.
          -- eapply FILE; [exact DI| exact EA| exact AV| exact Hne| exact Hnd| lia| exact Hlk].
          -- eapply OPENFAIL; [exact DI| exact EA| exact AV|].
             right. right. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. lia.
  Qed.
End S.
