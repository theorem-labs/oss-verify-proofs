(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from E2/Equiv/ExitStdio.v and E2/Equiv/ExitProg.v: the program tree of a run whose argv has not two entries has only writev, ioctl, set_tid_address, exit and lseek nodes. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog HeapFull. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import ExitBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.BudgetWit Require Import NoAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** * The usage path's tree makes no allocation call

    [UNodes__Equiv.EquivPlan.ptree] is the program tree the released proofs
    of both builds run ([Final_ubsan.IMPL_S_final] over [ssegs],
    [Final_ubsan.IMPL_T_final] over [usegs]): [Prog.prog_itree] of
    [Prog.prog], which is [startup_model] (set_tid_address), then
    [Prog.main_prog] ([Driver.main_model]), then [exit_model]
    ([Stdio.stdio_exit], then exit).  With argc <> 2, [main_model] is
    [diag (DUsage argv0) ;;; mret 2], and [diag (DUsage _)] is
    [Stdio.diag_usage], [Stdio.eprintf] of the usage pieces: a writev loop
    on fd 2, after an ioctl when the stream asks for one.  [stdio_exit]
    flushes every open stream, which is a writev loop and an lseek, and
    exits.

    [ExitBase.tall] and [ExitBase.mall] are indexed by a node predicate, and
    are used here at [NoAlloc.NAn]; the lemmas of [ExitStdio] and [ExitProg]
    built on them are stated at [ExitBase.noexit] ([mne]), so each one the
    usage path needs is restated at [NAn] ([mna]) with the same proof. *)

Definition mna {St A : Type} (m : M St A) : Prop := mall NAn m (fun _ => True).

Lemma mna_ret {St A} (a : A) : mna (St:=St) (mret a).
Proof. apply mall_ret. exact I. Qed.
Lemma mna_unr {St A} : mna (St:=St) (munr (A:=A)).
Proof. apply mall_unr. Qed.
Lemma mna_get {St} : mna (St:=St) mget.
Proof. apply mall_get. intros; exact I. Qed.
Lemma mna_upd {St} f : mna (St:=St) (mupd f).
Proof. apply mall_upd. exact I. Qed.
Lemma mna_bind {St A B} (m : M St A) (f : A -> M St B) : mna m -> (forall a, mna (f a)) -> mna (mbind m f).
Proof. intros Hm Hf. apply mall_bind_true; assumption. Qed.
Lemma mna_sys {St A} n (dec : resp -> option A) : NAn n -> mna (St:=St) (msys n dec).
Proof. intros Hn. apply mall_sys_true. exact Hn. Qed.

Create HintDb mna discriminated.

Ltac na_node :=
  first [ exact (eq_refl true)
        | cbn; exact (eq_refl true)
        | repeat (lazymatch goal with |- NAn (match ?x with _ => _ end) => destruct_inner x end);
          first [exact (eq_refl true) | cbn; exact (eq_refl true)] ].
Ltac mna_extra := fail.
Ltac mna_step :=
  lazymatch goal with
  | |- mna (mbind _ _) => apply mna_bind; [| intros ?]
  | |- mna (mret _) => apply mna_ret
  | |- mna munr => apply mna_unr
  | |- mna mget => apply mna_get
  | |- mna (mupd _) => apply mna_upd
  | |- mna (msys _ _) => apply mna_sys; na_node
  | |- mna (match ?x with _ => _ end) => destruct x
  | |- mna (let _ := _ in _) => cbv zeta
  | |- mna _ => first [ mna_extra | solve [auto with mna nocore] ]
  end.
Ltac mna_go := repeat (cbv beta; mna_step).

Section Core.
Context {St : Type}.

Lemma mna_towrite f : mna (St:=St) (towrite f).
Proof. unfold towrite. mna_go. Qed.
Hint Resolve mna_towrite : mna.

Lemma mna_ensure_w f : mna (St:=St) (ensure_w f).
Proof. unfold ensure_w. mna_go. Qed.
Hint Resolve mna_ensure_w : mna.

Lemma NA_wnode f iovs : NAn (wnode f iovs).
Proof. unfold wnode. destruct (f_chan f); exact (eq_refl true). Qed.

Lemma mna_writev_loop fuel : forall f iovs rem, mna (St:=St) (writev_loop fuel f iovs rem).
Proof.
  induction fuel as [|fuel IH]; intros f iovs rem; cbn [writev_loop]; [apply mna_unr|].
  apply mna_bind; [apply mna_sys; apply NA_wnode|]. intros cnt. cbv beta.
  destruct (cnt =? rem); [apply mna_ret | apply IH].
Qed.
Hint Resolve mna_writev_loop : mna.

Lemma mna_stdio_write f s : mna (St:=St) (stdio_write f s).
Proof. unfold stdio_write. mna_go. Qed.
Hint Resolve mna_stdio_write : mna.

Lemma mna_file_writefn f s : mna (St:=St) (file_writefn f s).
Proof. unfold file_writefn. mna_go. Qed.
Hint Resolve mna_file_writefn : mna.

Lemma mna_fwritex f s : mna (St:=St) (fwritex f s).
Proof. unfold fwritex. mna_go. Qed.
Hint Resolve mna_fwritex : mna.

Lemma mna_out_pieces ps : forall f, mna (St:=St) (out_pieces f ps).
Proof.
  induction ps as [|p ps IH]; intros f; cbn [out_pieces]; [apply mna_ret|].
  apply mna_bind; [apply mna_fwritex | intros f'; apply IH].
Qed.
Hint Resolve mna_out_pieces : mna.

Lemma mna_vfprintf f ps : mna (St:=St) (vfprintf f ps).
Proof. unfold vfprintf. mna_go. Qed.
Hint Resolve mna_vfprintf : mna.

Lemma mna_sync_read_pos f : mna (St:=St) (sync_read_pos f).
Proof. unfold sync_read_pos. mna_go. Qed.
Hint Resolve mna_sync_read_pos : mna.

Lemma mna_close_file f : mna (St:=St) (close_file f).
Proof. unfold close_file. mna_go. Qed.
End Core.

#[export] Hint Resolve mna_towrite mna_ensure_w mna_writev_loop mna_stdio_write mna_file_writefn
  mna_fwritex mna_out_pieces mna_vfprintf mna_sync_read_pos mna_close_file : mna.

Section Stdio.
Context {St ptr : Type}.
Context (get_lc : St -> libc_st ptr) (set_lc : libc_st ptr -> St -> St).

Lemma mna_rd_lc : mna (rd_lc get_lc).
Proof. unfold rd_lc. mna_go. Qed.
Hint Resolve mna_rd_lc : mna.

Lemma mna_upd_lc g : mna (upd_lc get_lc set_lc g).
Proof. unfold upd_lc. mna_go. Qed.
Hint Resolve mna_upd_lc : mna.

Lemma mna_eprintf ps : mna (eprintf get_lc set_lc ps).
Proof. unfold eprintf. mna_go. Qed.

Lemma mna_diag_usage a : mna (diag_usage get_lc set_lc a).
Proof. unfold diag_usage. apply mna_eprintf. Qed.

Lemma mna_close_files (fs : list (ptr * file_st)) : mna (St:=St) (close_files fs).
Proof. induction fs as [|[q f] fs IH]; cbn [close_files]; mna_go. Qed.
Hint Resolve mna_close_files : mna.

Lemma mna_stdio_exit : mna (stdio_exit get_lc).
Proof. unfold stdio_exit. mna_go. Qed.
End Stdio.

Section WithCeil.
Context {CE : CEIL}.

Lemma mna_startup {St} (set_tls : Z -> St -> St) tb : mna (startup_model set_tls tb).
Proof. unfold startup_model. mna_go. Qed.

Section Prog.
Context {H hptr : Type} (HO : HeapOps H hptr).
Variable FO : FrameOps (H:=H) (hptr:=hptr).
Variable stk : stack_site -> Z.

Lemma mna_exit_model code : mna (exit_model (s_stdio_exit (H:=H) (hptr:=hptr)) code).
Proof.
  unfold exit_model. apply mna_bind; [unfold s_stdio_exit; apply mna_stdio_exit|].
  intros _. apply mna_sys. exact (eq_refl true).
Qed.

(** The whole program, when argv has not two entries. *)
Lemma prog_na tb argv : Z.of_nat (length argv) <> 2 -> mna (prog HO tb FO stk argv).
Proof.
  intros Hlen. unfold prog.
  apply mna_bind; [apply mna_startup|]. intros _. cbv beta.
  apply mna_bind; [| intros code; cbv beta; apply mna_exit_model].
  unfold main_prog, main_model.
  destruct (negb (Z.of_nat (length argv) =? 2)) eqn:E.
  - apply mna_bind; [cbn [diag]; apply mna_diag_usage | intros _; apply mna_ret].
  - exfalso. apply Bool.negb_false_iff, Z.eqb_eq in E. exact (Hlen E).
Qed.

Lemma prog_itree_na tb h0 argv : (length argv <> 2)%nat -> tna (prog_itree HO tb h0 FO stk argv).
Proof.
  intros Hlen. unfold tna, prog_itree, ebind. apply tall_bind.
  assert (Hz : Z.of_nat (length (argv_Z argv)) <> 2) by (unfold argv_Z; rewrite length_map; lia).
  eapply tall_mono; [intros n Hn; exact Hn | | exact (prog_na tb (argv_Z argv) Hz (ps_init h0))].
  intros [|[a s]] _; cbn; [exact I | destruct a].
Qed.

End Prog.
End WithCeil.

(** The released tree of either build, when argv has not two entries. *)
Lemma ptree_na : forall segs tb stk sec inp en,
  (length (in_argv inp) <> 2)%nat -> tna (ptree segs tb stk sec inp en).
Proof. intros segs tb stk sec inp en Hlen. unfold ptree. cbv beta. apply prog_itree_na. exact Hlen. Qed.
