(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (27 recorded proofs replaced by written proofs (tall_mono, tall_ebind, impl_tall and 24 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio Driver PState.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Keeps () := "c59OSSVerify5KrLib6Common5Keeps4tallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9tall_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps:tall_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps5keepsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps:keeps_bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_unrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec5Monad5mwhenC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib6Common5Keeps9impl_tallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree?impl_epost_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio@stdio_write_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState9set_so_psC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio5rd_soC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib5Lists7ListDef3mapK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9iov_totalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode:dec_writevC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec5Stdio;iov_advanceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_sysC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps8keeps_ifC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5KeepsBstdio_write_loop_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9WRITE_MAXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_lbf_nlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5Stdio9stdout_st01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBstdout_stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps7rd_so_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps8upd_so_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps=stdio_write_kC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec5Stdio9so_activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_writefnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5KeepsDstdout_stdio_write_kC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:TIOCGWINSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_ioctlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_towriteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec5Stdio=after_last_nlC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec5Stdio>stdout_fwritexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps@stdout_writefn_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps@stdout_towrite_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=STDOUT_BUFSIZC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec5Stdio:out_piecesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps@stdout_fwritex_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_vprintfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps<out_pieces_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps@stdout_vprintf_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioAstdout_exit_flushC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps7ps_heapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps8s_emit_kC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tall {R} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
  match t with
  | Ret Unr => True
  | Ret (Ok r) => P r
  | Vis _ k => forall rsp, tall P (k rsp)
  end.

Lemma tall_mono : forall {R} (P P' : R -> Prop) t, tall P t -> (forall r, P r -> P' r) -> tall P' t.
Proof.
  induction t as [[|r]|n k IH]; cbn; intros H HP.
  - exact I.
  - apply HP. exact H.
  - intros rsp. eapply IH; [apply H| exact HP].
Qed.

Lemma tall_ebind : forall {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ebind t f).
Proof.
  induction t as [[|a]|n k IH]; cbn; intros f H HF; [exact I| apply HF; exact H|].
  intros rsp. apply IH; [apply H| exact HF].
Qed.

(* [comment removed for export] *)
Lemma impl_tall : forall segs {R} (t : itree node (exc R)) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
  impl segs (at_node segs) t (epost Q) ms -> tall P t ->
  impl segs (at_node segs) t (epost (fun r ms' => Q r ms' /\ P r)) ms.
Proof.
  intros segs R t. induction t as [[|r]|n k IH]; cbn; intros P Q ms H HP.
  - exact H.
  - eapply evt_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply Hk| apply HP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Keeps.
  Context {St B : Type} (f : St -> B).
  Local Notation M := (@Monad.M St).

  Definition keeps {A} (c : M A) : Prop := forall s : St, tall (fun p => f (snd p) = f s) (c s).

  Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
  Proof. intros A a s. reflexivity. Qed.
  Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
  Proof. intros A s. exact I. Qed.
  Lemma keeps_get : keeps mget.
  Proof. intros s. reflexivity. Qed.
  Lemma keeps_upd : forall g, (forall s, f (g s) = f s) -> keeps (mupd g).
  Proof. intros g Hg s. cbn. apply Hg. Qed.
  Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
  Proof. intros A n dec s. cbn. intros rsp. destruct (dec rsp); cbn; [reflexivity| exact I]. Qed.
  Lemma keeps_bind : forall {A C} (m : M A) (k : A -> M C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
  Proof.
    intros A C m k Hm Hk s. unfold mbind. eapply tall_ebind; [apply Hm|]. cbn. intros [a s1] E. cbn in E.
    eapply tall_mono; [apply Hk|]. cbn. intros [c s2] E2. cbn in E2 |- *. congruence.
  Qed.
  (* [comment removed for export] *)
  Lemma keeps_getk : forall {C} (k : St -> M C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
  Proof. intros C k Hk s. unfold mbind, mget. cbn. apply Hk. Qed.
  Lemma keeps_loop : forall {X R} fuel (body : X -> M (X + R)), (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
  Proof.
    induction fuel as [|fuel IH]; intros body HB x; cbn; [apply keeps_unr|].
    apply keeps_bind; [apply HB|]. intros [x'|r]; [apply IH; exact HB| apply keeps_ret].
  Qed.
  Lemma keeps_if : forall {A} (b : bool) (m1 m2 : M A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
  Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
  Lemma keeps_when : forall (b : bool) (m1 : M unit), keeps m1 -> keeps (mwhen b m1).
  Proof. intros [|] m1 H1; [exact H1| apply keeps_ret]. Qed.
End Keeps.
Arguments keeps {St B} f {A} c.

Ltac keeps_step :=
  first [ apply keeps_ret | apply keeps_unr | apply keeps_sys | apply keeps_get
        | apply keeps_getk | apply keeps_bind | apply keeps_if | apply keeps_when
        | apply keeps_upd; [intros; reflexivity] ].
(* [comment removed for export] *)
Ltac keeps_tac :=
  repeat (intros; cbn beta;
          first [ solve [auto]
                | keeps_step
                | lazymatch goal with
                  | |- keeps _ (match ?x with _ => _ end) => destruct x
                  end ]).

(* [comment removed for export] *)
Lemma implM_keeps : forall segs {St B A} (f : St -> B) (c : @Monad.M St A) s Q ms,
  implM segs c s Q ms -> keeps f c -> implM segs c s (fun r s' ms' => Q r s' ms' /\ f s' = f s) ms.
Proof.
  intros segs St B A f c s Q ms H K. unfold implM in *.
  eapply impl_epost_mono; [eapply impl_tall; [exact H| apply K]|]. cbn. intros [a s'] ms' [HQ E]. split; [exact HQ| exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ps_heap (s : PState) : _ := (ps_m s, ps_brk s, ps_fa s).

Section StdoutKeeps.
  Context {B : Type} (f : PState -> B).
  Hypothesis FSO : forall v s, f (set_so_ps v s) = f s.

  Lemma upd_so_k : forall g, keeps f (upd_so ps_so set_so_ps g).
  Proof. intros g. unfold upd_so. apply keeps_upd. intros s. apply FSO. Qed.
  Lemma rd_so_k : keeps f (rd_so (St:=PState) ps_so).
  Proof. unfold rd_so. keeps_tac. Qed.
  Lemma stdio_write_loop_k : forall fuel fd iov, keeps f (stdio_write_loop (St:=PState) fuel fd iov).
  Proof. induction fuel as [|fuel IH]; intros fd iov; cbn; keeps_tac. Qed.
  Lemma stdio_write_k : forall fd buf s, keeps f (stdio_write (St:=PState) fd buf s).
  Proof. intros fd buf s. unfold stdio_write. pose proof stdio_write_loop_k. keeps_tac. Qed.
  Lemma stdout_stdio_write_k : forall s, keeps f (stdout_stdio_write ps_so set_so_ps s).
  Proof. intros s. unfold stdout_stdio_write. pose proof rd_so_k. pose proof upd_so_k. pose proof stdio_write_k. keeps_tac. Qed.
  Lemma stdout_writefn_k : forall s, keeps f (stdout_writefn ps_so set_so_ps s).
  Proof. intros s. unfold stdout_writefn. pose proof rd_so_k. pose proof upd_so_k. pose proof stdout_stdio_write_k. keeps_tac. Qed.
  Lemma stdout_towrite_k : keeps f (stdout_towrite ps_so set_so_ps).
  Proof. unfold stdout_towrite. apply upd_so_k. Qed.
  Lemma stdout_fwritex_k : forall s, keeps f (stdout_fwritex ps_so set_so_ps s).
  Proof. intros s. unfold stdout_fwritex. pose proof rd_so_k. pose proof upd_so_k. pose proof stdout_writefn_k. pose proof stdout_towrite_k. keeps_tac. Qed.
  Lemma out_pieces_k : forall ps, keeps f (out_pieces ps_so set_so_ps ps).
  Proof. induction ps as [|p ps IH]; cbn; [apply keeps_ret|]. pose proof stdout_fwritex_k. keeps_tac. Qed.
  Lemma stdout_vprintf_k : forall ps, keeps f (stdout_vprintf ps_so set_so_ps ps).
  Proof. intros ps. unfold stdout_vprintf. pose proof stdout_towrite_k. pose proof out_pieces_k. keeps_tac. Qed.
  Lemma s_emit_k : forall v, keeps f (s_emit ps_so set_so_ps v).
  Proof. intros v. unfold s_emit. apply stdout_vprintf_k. Qed.
  Lemma stdout_exit_flush_k : keeps f (stdout_exit_flush ps_so set_so_ps).
  Proof. unfold stdout_exit_flush. pose proof rd_so_k. pose proof stdout_writefn_k. keeps_tac. Qed.
End StdoutKeeps.

Lemma s_emit_heap : forall v, keeps ps_heap (s_emit ps_so set_so_ps v).
Proof. intros v. apply s_emit_k. intros; reflexivity. Qed.
