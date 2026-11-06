(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv LB_Inv LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt StdioCore Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapSim NodeSim ProgSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module SimStdio.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv LB_Inv LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW HeapSim NodeSim ProgSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition file_ok (f : file_st) : Prop := 0 <= f_bufsize f < 2^62.

Definition LCI (l : libc_st hptr) : Prop :=
  file_ok (lc_stdout l) /\ file_ok (lc_stderr l) /\ Forall (fun pf => file_ok (snd pf)) (lc_files l).

#[using="Type"] Lemma LCI_init : LCI libc_init.
Proof. unfold LCI, libc_init, file_ok, stdout_init, stderr_init, BUFSIZ. cbn. split; [lia|]. split; [lia|]. constructor. Qed.

#[using="Type"] Lemma LCI_errno e l : LCI l -> LCI (set_errno_lc e l).
Proof. intros (A & B & C). exact (conj A (conj B C)). Qed.
#[using="Type"] Lemma LCI_stdout f l : file_ok f -> LCI l -> LCI (set_stdout f l).
Proof. intros Hf (A & B & C). exact (conj Hf (conj B C)). Qed.
#[using="Type"] Lemma LCI_stderr f l : file_ok f -> LCI l -> LCI (set_stderr f l).
Proof. intros Hf (A & B & C). exact (conj A (conj Hf C)). Qed.

#[using="Type"] Lemma files_lookup_ok (fs : list (hptr * file_st)) h f : Forall (fun pf => file_ok (snd pf)) fs -> files_lookup N.eqb fs h = Some f -> file_ok f.
Proof.
  induction fs as [|[k v] fs IH]; intros HF H; cbn in H; [discriminate|].
  apply Forall_cons_iff in HF as [Hv HF]. destruct (N.eqb k h); [injection H as <-; exact Hv| exact (IH HF H)].
Qed.
#[using="Type"] Lemma files_update_ok (fs : list (hptr * file_st)) h f : Forall (fun pf => file_ok (snd pf)) fs -> file_ok f ->
  Forall (fun pf => file_ok (snd pf)) (files_update N.eqb fs h f).
Proof.
  induction fs as [|[k v] fs IH]; intros HF Hf; cbn; [constructor|].
  apply Forall_cons_iff in HF as [Hv HF]. destruct (N.eqb k h); constructor; auto.
Qed.
#[using="Type"] Lemma files_remove_ok (fs : list (hptr * file_st)) h : Forall (fun pf => file_ok (snd pf)) fs ->
  Forall (fun pf => file_ok (snd pf)) (files_remove N.eqb fs h).
Proof.
  induction fs as [|[k v] fs IH]; intros HF; cbn; [constructor|].
  apply Forall_cons_iff in HF as [Hv HF]. destruct (N.eqb k h); [exact HF| constructor; auto].
Qed.
#[using="Type"] Lemma LCI_files_update h f l : file_ok f -> LCI l -> LCI (set_files (files_update N.eqb (lc_files l) h f) l).
Proof. intros Hf (A & B & C). exact (conj A (conj B (files_update_ok _ _ _ C Hf))). Qed.
#[using="Type"] Lemma LCI_files_remove h l : LCI l -> LCI (set_files (files_remove N.eqb (lc_files l) h) l).
Proof. intros (A & B & C). exact (conj A (conj B (files_remove_ok _ _ C))). Qed.
#[using="Type"] Lemma LCI_files_cons p f l : file_ok f -> LCI l -> LCI (set_files ((p, f) :: lc_files l) l).
Proof. intros Hf (A & B & C). split; [exact A|]. split; [exact B|]. constructor; [exact Hf| exact C]. Qed.

#[using="Type"] Lemma fdopen_file_ok fd wr : file_ok (fdopen_file fd wr).
Proof. unfold file_ok, fdopen_file, BUFSIZ. cbn. lia. Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac fok := unfold file_ok in *; cbn [f_bufsize set_w set_rbuf set_eof set_bufsize after_ioctl fdopen_file fst snd] in *;
            unfold INTERNAL_BUFSIZ, BUFSIZ in *; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
Section SimStdio.
Variable segs : list Segment.
Variable P : Z -> Z.
#[local] Notation npk := (npeek segs).
#[local] Notation RQ := (ProgSim.RQ (CEG:=CEG) (CEC:=CEC) P LCI).

(* [comment removed for export] *)
Definition postI {A} (I : A -> Prop) (tm : gmap N Z) (nx : N) : A -> A -> @rel PS PS :=
  eqpost (fun a => fun sG moG sC moC => I a /\ RQ tm nx sG moG sC moC).

#[using="Type"] Lemma rq_pure {A} (phi : Prop) (R : @rel PS PS) (m m' : Monad.M PS A) Q :
  (phi -> fsimw npk R m m' Q) -> fsimw npk (fun sG moG sC moC => phi /\ R sG moG sC moC) m m' Q.
Proof. apply fsimw_pure. Qed.

#[using="Type"] Lemma rq_retI {A} (I : A -> Prop) tm nx (a : A) : I a -> fsimw npk (RQ tm nx) (mret a) (mret a) (postI I tm nx).
Proof. intros Ha. apply rq_ret. intros; split; [exact Ha| assumption]. Qed.

#[using="Type"] Lemma rq_bindI {A B} (I1 : A -> Prop) (I2 : B -> Prop) tm nx tm1 nx1 tm2 nx2 (m m' : Monad.M PS A) (k k' : A -> Monad.M PS B) :
  fsimw npk (RQ tm nx) m m' (postI I1 tm1 nx1) -> (forall a, I1 a -> fsimw npk (RQ tm1 nx1) (k a) (k' a) (postI I2 tm2 nx2)) ->
  fsimw npk (RQ tm nx) (mbind m k) (mbind m' k') (postI I2 tm2 nx2).
Proof.
  intros H1 H2. eapply rq_bind; [exact H1|]. intros a. apply rq_pure. exact (H2 a).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rq_postI {A} (I I' : A -> Prop) tm nx tm1 nx1 (m m' : Monad.M PS A) :
  fsimw npk (RQ tm nx) m m' (postI I tm1 nx1) -> (forall a, I a -> I' a) -> fsimw npk (RQ tm nx) m m' (postI I' tm1 nx1).
Proof. intros H HI. eapply rq_post; [exact H|]. intros a ? ? ? ? [Ha HR]. split; [apply HI; exact Ha| exact HR]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rq_msysI {A} tm nx n (dec : resp -> option A) : fdnode n ->
  fsimw npk (RQ tm nx) (msys n dec) (msys n dec) (postI (decoded dec) tm nx).
Proof. intros Hn. apply rq_msys. exact Hn. Qed.

#[using="Type"] Lemma rq_rd_lcI tm nx : fsimw npk (RQ tm nx) (rd_lc ps_libc) (rd_lc ps_libc) (postI LCI tm nx).
Proof. eapply rq_post; [apply rq_rd_lc|]. intros a ? ? ? ? (Ha & _ & HR). split; [exact Ha| exact HR]. Qed.

#[using="Type"] Lemma rq_upd_lcI tm nx g : (forall l, LCI l -> LCI (g l)) ->
  fsimw npk (RQ tm nx) (upd_lc ps_libc set_libc g) (upd_lc ps_libc set_libc g) (postI (fun _ => True) tm nx).
Proof. intros Hg. eapply rq_post; [apply rq_upd_lc; exact Hg|]. intros; split; [exact I| assumption]. Qed.

#[using="Type"] Lemma rq_munrI {A} (I : A -> Prop) tm nx tm1 nx1 (m' : Monad.M PS A) : fsimw npk (RQ tm nx) munr m' (postI I tm1 nx1).
Proof. apply rq_munr. Qed.

(* [comment removed for export] *)
Create HintDb rq.
Hint Resolve rq_rd_lcI : rq.
Hint Extern 1 (fsimw _ _ (msys _ _) (msys _ _) _) => apply rq_msysI; exact I : rq.
Hint Extern 1 (fsimw _ _ munr _ _) => apply rq_munrI : rq.
Hint Extern 2 (file_ok _) => fok : rq.

Ltac cong_leaf := first [eassumption| exact I| fok| solve [auto]].

(* [comment removed for export] *)
#[using="Type"] Lemma rq_bind_retl {A B} (R : @rel PS PS) (a : A) (k k' : A -> Monad.M PS B) Q :
  fsimw npk R (k a) (k' a) Q -> fsimw npk R (mbind (mret a) k) (mbind (mret a) k') Q.
Proof. intros H. exact H. Qed.

Ltac cong :=
  cbv zeta;
  lazymatch goal with
  | |- fsimw _ _ munr _ _ => apply rq_munrI
  | |- fsimw _ _ (mret _) (mret _) _ => apply rq_retI; cong_leaf
  | |- fsimw _ _ (mbind (mret _) _) _ _ => apply rq_bind_retl; cong
  | |- fsimw _ _ (mbind (match ?x with _ => _ end) _) _ _ => destruct x eqn:?; cong
  | |- fsimw _ _ (mbind (if ?b then _ else _) _) _ _ => destruct b eqn:?; cong
  | |- fsimw _ _ (mbind _ _) (mbind _ _) _ => eapply rq_bindI; [solve [eauto 4 with rq]| intros ? ?; cong]
  | |- fsimw _ _ (match ?x with _ => _ end) _ _ => destruct x eqn:?; cong
  | |- fsimw _ _ (if ?b then _ else _) _ _ => destruct b eqn:?; cong
  | |- _ => first [solve [eauto 4 with rq]| eapply rq_postI; [solve [eauto 4 with rq]| intros; cong_leaf]]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma cg_towrite tm nx f : file_ok f -> fsimw npk (RQ tm nx) (towrite f) (towrite f) (postI file_ok tm nx).
Proof. intros Hf. unfold towrite. cong. Qed.
Hint Resolve cg_towrite : rq.

#[using="Type"] Lemma cg_ensure_w tm nx f : file_ok f -> fsimw npk (RQ tm nx) (ensure_w f) (ensure_w f) (postI file_ok tm nx).
Proof. intros Hf. unfold ensure_w. cong. Qed.
Hint Resolve cg_ensure_w : rq.

#[using="Type"] Lemma wnode_fd f iovs : fdnode (wnode f iovs).
Proof. unfold wnode. destruct (f_chan f); exact I. Qed.

#[using="Type"] Lemma cg_writev_loop tm nx fuel : forall f iovs rem,
  fsimw npk (RQ tm nx) (writev_loop fuel f iovs rem) (writev_loop fuel f iovs rem) (postI (fun _ => True) tm nx).
Proof.
  induction fuel as [|fuel IH]; intros f iovs rem; cbn [writev_loop]; [apply rq_munrI|].
  eapply rq_bindI; [apply rq_msysI; apply wnode_fd|]. intros cnt _. cong.
Qed.
Hint Resolve cg_writev_loop : rq.

#[using="Type"] Lemma cg_stdio_write tm nx f s : file_ok f -> fsimw npk (RQ tm nx) (stdio_write f s) (stdio_write f s) (postI file_ok tm nx).
Proof. intros Hf. unfold stdio_write. cong. Qed.
Hint Resolve cg_stdio_write : rq.

#[using="Type"] Lemma cg_file_writefn tm nx f s : file_ok f -> fsimw npk (RQ tm nx) (file_writefn f s) (file_writefn f s) (postI file_ok tm nx).
Proof. intros Hf. unfold file_writefn. cong. Qed.
Hint Resolve cg_file_writefn : rq.

#[using="Type"] Lemma cg_fwritex tm nx f s : file_ok f -> fsimw npk (RQ tm nx) (fwritex f s) (fwritex f s) (postI file_ok tm nx).
Proof. intros Hf. unfold fwritex. cong. Qed.
Hint Resolve cg_fwritex : rq.

#[using="Type"] Lemma cg_fwrite_file tm nx f s : file_ok f -> fsimw npk (RQ tm nx) (fwrite_file f s) (fwrite_file f s) (postI file_ok tm nx).
Proof. intros Hf. unfold fwrite_file. cong. Qed.
Hint Resolve cg_fwrite_file : rq.

#[using="Type"] Lemma cg_out_pieces tm nx ps : forall f, file_ok f -> fsimw npk (RQ tm nx) (out_pieces f ps) (out_pieces f ps) (postI file_ok tm nx).
Proof. induction ps as [|p ps IH]; intros f Hf; cbn [out_pieces]; cong. Qed.
Hint Resolve cg_out_pieces : rq.

#[using="Type"] Lemma cg_vfprintf tm nx f ps : file_ok f -> fsimw npk (RQ tm nx) (vfprintf f ps) (vfprintf f ps) (postI file_ok tm nx).
Proof. intros Hf. unfold vfprintf. cong. Qed.
Hint Resolve cg_vfprintf : rq.

#[using="Type"] Lemma cg_toread tm nx f : file_ok f -> fsimw npk (RQ tm nx) (toread f) (toread f) (postI (fun r => file_ok (snd r)) tm nx).
Proof. intros Hf. unfold toread. cong. Qed.
Hint Resolve cg_toread : rq.

(* [comment removed for export] *)
#[using="Type"] Lemma cg_stdio_read tm nx f bufG bufC destG destC len :
  file_ok f -> 1 <= len < 2^62 ->
  fsimw npk (RQ tm nx) (stdio_read f bufG destG len) (stdio_read f bufC destC len) (postI (fun r => file_ok (snd r)) tm nx).
Proof.
  intros Hf Hl. unfold stdio_read. cbv zeta.
  apply (rq_bindI (fun _ => True) (fun r => file_ok (snd r)) tm nx tm nx tm nx).
  - destruct (len - (if f_bufsize f =? 0 then 0 else 1) =? 0).
    + eapply rq_post; [apply rq_read|]. intros a ? ? ? ? [_ HR]; split; [exact I| exact HR].
    + eapply rq_post; [apply rq_readv; [reflexivity|]|]; [| intros a ? ? ? ? [_ HR]; split; [exact I| exact HR]].
      unfold lens_ok. constructor; [cbn [snd]; destruct (f_bufsize f =? 0); lia|]. constructor; [cbn [snd]; fok| constructor].
  - intros a _. cong.
Qed.
Hint Resolve cg_stdio_read : rq.
Hint Extern 2 (_ <= _ < _) => lia : rq.
Hint Extern 2 (_ < _) => lia : rq.
Hint Extern 2 (_ <= _) => lia : rq.

#[using="Type"] Lemma cg_fread_loop tm nx fuel : forall f bufG bufC destG destC l acc,
  file_ok f -> l < 2^62 ->
  fsimw npk (RQ tm nx) (fread_loop fuel f bufG destG l acc) (fread_loop fuel f bufC destC l acc) (postI (fun r => file_ok (snd r)) tm nx).
Proof.
  induction fuel as [|fuel IH]; intros f bufG bufC destG destC l acc Hf Hl; cbn [fread_loop]; [apply rq_munrI|].
  destruct (l <=? 0) eqn:El; [cong|]. apply Z.leb_gt in El.
  eapply rq_bindI; [solve [eauto 4 with rq]|]. intros ef Hef.
  eapply rq_bindI with (I1 := fun r => file_ok (snd r)).
  - destruct (fst ef); [cong| apply cg_stdio_read; [exact Hef| lia]].
  - intros bf Hbf. destruct (fst bf) eqn:Eb; [cong|]. apply IH; [exact Hbf| unfold zlength; lia].
Qed.
Hint Resolve cg_fread_loop : rq.

#[using="Type"] Lemma cg_fread_file tm nx f bufG bufC destG destC n :
  file_ok f -> n < 2^62 ->
  fsimw npk (RQ tm nx) (fread_file f bufG destG n) (fread_file f bufC destC n) (postI (fun r => file_ok (snd r)) tm nx).
Proof. intros Hf Hn. unfold fread_file. cbv zeta. apply cg_fread_loop; [fok| unfold zlength; lia]. Qed.
Hint Resolve cg_fread_file : rq.

#[using="Type"] Lemma cg_sync_read_pos tm nx f : fsimw npk (RQ tm nx) (sync_read_pos f) (sync_read_pos f) (postI (fun _ => True) tm nx).
Proof. unfold sync_read_pos. cong. Qed.
Hint Resolve cg_sync_read_pos : rq.

#[using="Type"] Lemma cg_fflush_file tm nx f : file_ok f -> fsimw npk (RQ tm nx) (fflush_file f) (fflush_file f) (postI file_ok tm nx).
Proof. intros Hf. unfold fflush_file. cong. Qed.
Hint Resolve cg_fflush_file : rq.

#[using="Type"] Lemma cg_close_file tm nx f : file_ok f -> fsimw npk (RQ tm nx) (close_file f) (close_file f) (postI (fun _ => True) tm nx).
Proof. intros Hf. unfold close_file. cong. Qed.
Hint Resolve cg_close_file : rq.

#[using="Type"] Lemma cg_fclose_file tm nx f : file_ok f -> fsimw npk (RQ tm nx) (fclose_file f) (fclose_file f) (postI (fun _ => True) tm nx).
Proof. intros Hf. unfold fclose_file. cong. Qed.
Hint Resolve cg_fclose_file : rq.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation lookup_fileP := (@lookup_file PS hptr ps_libc N.eqb).
#[local] Notation store_fileP := (@store_file PS hptr ps_libc set_libc N.eqb).
#[local] Notation with_fileP := (@with_file PS hptr ps_libc set_libc N.eqb _).
#[local] Notation with_file_P := (@with_file_ PS hptr ps_libc set_libc N.eqb).

#[using="Type"] Lemma cg_set_errno tm nx e :
  fsimw npk (RQ tm nx) (set_errno ps_libc set_libc e) (set_errno ps_libc set_libc e) (postI (fun _ => True) tm nx).
Proof. unfold set_errno. apply rq_upd_lcI. intros l Hl. apply LCI_errno. exact Hl. Qed.
Hint Resolve cg_set_errno : rq.

#[using="Type"] Lemma cg_get_errno tm nx :
  fsimw npk (RQ tm nx) (get_errno ps_libc) (get_errno ps_libc) (postI (fun _ => True) tm nx).
Proof. unfold get_errno. cong. Qed.
Hint Resolve cg_get_errno : rq.

#[using="Type"] Lemma cg_lookup_file tm nx h :
  fsimw npk (RQ tm nx) (lookup_fileP h) (lookup_fileP h) (postI file_ok tm nx).
Proof.
  unfold lookup_file. eapply rq_bindI; [apply rq_rd_lcI|]. intros l Hl.
  lazymatch goal with |- fsimw _ _ (match ?x with _ => _ end) _ _ => destruct x eqn:E end; [| apply rq_munrI].
  apply rq_retI. eapply files_lookup_ok; [exact (proj2 (proj2 Hl))| exact E].
Qed.
Hint Resolve cg_lookup_file : rq.

#[using="Type"] Lemma cg_store_file tm nx h f : file_ok f ->
  fsimw npk (RQ tm nx) (store_fileP h f) (store_fileP h f) (postI (fun _ => True) tm nx).
Proof. intros Hf. unfold store_file. apply rq_upd_lcI. intros l Hl. apply LCI_files_update; [exact Hf| exact Hl]. Qed.
Hint Resolve cg_store_file : rq.

#[using="Type"] Lemma cg_with_file {A} (I : A -> Prop) tm nx h (op op' : file_st -> Monad.M PS (A * file_st)) :
  (forall f, file_ok f -> fsimw npk (RQ tm nx) (op f) (op' f) (postI (fun r => I (fst r) /\ file_ok (snd r)) tm nx)) ->
  fsimw npk (RQ tm nx) (with_fileP h op) (with_fileP h op') (postI I tm nx).
Proof.
  intros Hop. unfold with_file. eapply rq_bindI; [apply cg_lookup_file|]. intros f Hf.
  eapply rq_bindI; [apply Hop; exact Hf|]. intros r [Hr1 Hr2].
  eapply rq_bindI; [apply cg_store_file; exact Hr2|]. intros _ _. apply rq_retI. exact Hr1.
Qed.

#[using="Type"] Lemma cg_with_file_ tm nx h (op op' : file_st -> Monad.M PS file_st) :
  (forall f, file_ok f -> fsimw npk (RQ tm nx) (op f) (op' f) (postI file_ok tm nx)) ->
  fsimw npk (RQ tm nx) (with_file_P h op) (with_file_P h op') (postI (fun _ => True) tm nx).
Proof.
  intros Hop. unfold with_file_. eapply rq_bindI; [apply cg_lookup_file|]. intros f Hf.
  eapply rq_bindI; [apply Hop; exact Hf|]. intros r Hr. apply cg_store_file. exact Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem cg_fopen tm nx name wr :
  ROOMN (sizes tm) P FILE_ALLOC -> PHI P + R63N (sizes tm) <= BLIVE ->
  fsimw npk (RQ tm nx) (s_fopen fopsG name wr) (s_fopen fopsC name wr)
        (eqpost (fun r => fun sG moG sC moC =>
                   match r with
                   | None => RQ tm nx sG moG sC moC
                   | Some p => p = nx /\ RQ (<[nx := FILE_ALLOC]> tm) (N.succ nx) sG moG sC moC
                   end)).
Proof.
  intros HR HB. unfold s_fopen, fopen.
  apply (rq_bind segs (RQ tm nx) (fun _ => fun sG moG sC moC => True /\ RQ tm nx sG moG sC moC)).
  { destruct wr; (eapply rq_post; [apply rq_msys; exact I|]); intros a ? ? ? ? [_ H]; exact (conj I H). }
  intros r. apply rq_pure; intros _. destruct r as [e|fd].
  - eapply rq_bind; [apply cg_set_errno|]. intros ?. apply rq_pure; intros _. apply rq_ret. intros; assumption.
  - eapply rq_bind.
    { apply rq_pmalloc; [unfold FILE_ALLOC; lia| reflexivity| unfold bigb, FILE_ALLOC, MMAP_THRESHOLD, QMAX; cbn; lia| exact HR| unfold bigb, FILE_ALLOC, MMAP_THRESHOLD; cbn; lia]. }
    intros po. apply rq_pure. intros ->.
    apply (rq_bind segs (RQ (<[nx := FILE_ALLOC]> tm) (N.succ nx)) (fun _ => fun sG moG sC moC => True /\ RQ (<[nx := FILE_ALLOC]> tm) (N.succ nx) sG moG sC moC)).
    { destruct wr; [| apply rq_retI; exact I].
      eapply rq_bindI; [apply rq_msysI; exact I|]. intros [e|v] _; [apply rq_retI; exact I| apply rq_munrI]. }
    intros ?. apply rq_pure; intros _.
    eapply rq_bind; [apply rq_upd_lcI; intros l Hl; apply LCI_files_cons; [apply fdopen_file_ok| exact Hl]|].
    intros ?. apply rq_pure; intros _. apply rq_ret. intros; split; [reflexivity| assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem cg_fclose tm nx h n :
  tm !! h = Some n -> PHI P + R63N (sizes tm) <= BLIVE ->
  fsimw npk (RQ tm nx) (s_fclose fopsG h) (s_fclose fopsC h) (postI (fun _ => True) (delete h tm) nx).
Proof.
  intros Hh HB. unfold s_fclose, fclose. cbn [ho_eqb full_ops].
  eapply rq_bindI; [apply cg_lookup_file|]. intros f Hf.
  eapply rq_bindI; [apply cg_fclose_file; exact Hf|]. intros _ _.
  eapply rq_bindI; [apply rq_upd_lcI; intros l Hl; apply LCI_files_remove; exact Hl|]. intros _ _.
  eapply rq_post; [apply (rq_pfree segs P LCI tm nx h n Hh HB)|]. intros a ? ? ? ? H. exact (conj I H).
Qed.

#[using="Type"] Lemma cg_fwrite tm nx h s :
  fsimw npk (RQ tm nx) (s_fwrite fopsG h s) (s_fwrite fopsC h s) (postI (fun _ => True) tm nx).
Proof.
  unfold s_fwrite, fwrite. cbn [ho_eqb full_ops].
  eapply rq_bindI; [apply cg_with_file_; intros f Hf; apply cg_fwrite_file; exact Hf|]. intros _ _. apply rq_retI. exact I.
Qed.
Hint Resolve cg_fwrite : rq.

(* [comment removed for export] *)
#[using="Type"] Theorem cg_fread tm nx h destG destC n : n < 2^62 ->
  fsimw npk (RQ tm nx) (s_fread fopsG h destG n) (s_fread fopsC h destC n) (postI (fun _ => True) tm nx).
Proof.
  intros Hn. unfold s_fread, fread. cbn [ho_eqb full_ops].
  eapply fsimw_bind; [apply rq_get|]. intros a b. apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 (-> & -> & EL & EO & HRQ).
  eapply rq_pre; [| intros ? ? ? ? (-> & -> & -> & ->); exact HRQ].
  eapply rq_postI; [apply (cg_with_file (fun _ => True))| intros; exact I].
  intros f Hf. eapply rq_postI; [apply cg_fread_file; [exact Hf| exact Hn]|]. intros r Hr. exact (conj I Hr).
Qed.
Hint Resolve cg_fread : rq.

#[using="Type"] Lemma cg_ferror tm nx h : fsimw npk (RQ tm nx) (s_ferror fopsG h) (s_ferror fopsC h) (postI (fun _ => True) tm nx).
Proof. unfold s_ferror, ferror. cbn [ho_eqb full_ops]. cong. Qed.
#[using="Type"] Lemma cg_fileno tm nx h : fsimw npk (RQ tm nx) (s_fileno fopsG h) (s_fileno fopsC h) (postI (fun _ => True) tm nx).
Proof. unfold s_fileno, fileno. cbn [ho_eqb full_ops]. cong. Qed.
Hint Resolve cg_ferror cg_fileno : rq.

#[using="Type"] Lemma cg_fprintf tm nx h ps : fsimw npk (RQ tm nx) (s_fprintf fopsG h ps) (s_fprintf fopsC h ps) (postI (fun _ => True) tm nx).
Proof. unfold s_fprintf, fprintf. cbn [ho_eqb full_ops]. apply cg_with_file_. intros f Hf. apply cg_vfprintf. exact Hf. Qed.
Hint Resolve cg_fprintf : rq.

#[using="Type"] Lemma cg_printf tm nx ps : fsimw npk (RQ tm nx) (s_printf ps : Monad.M PS unit) (s_printf ps) (postI (fun _ => True) tm nx).
Proof.
  unfold s_printf, printf. eapply rq_bindI; [apply rq_rd_lcI|]. intros l Hl.
  eapply rq_bindI; [apply cg_vfprintf; exact (proj1 Hl)|]. intros f' Hf'. apply rq_upd_lcI. intros l0 Hl0. apply LCI_stdout; assumption.
Qed.
Hint Resolve cg_printf : rq.

#[using="Type"] Lemma cg_eprintf tm nx ps : fsimw npk (RQ tm nx) (eprintf ps_libc set_libc ps : Monad.M PS unit) (eprintf ps_libc set_libc ps) (postI (fun _ => True) tm nx).
Proof.
  unfold eprintf. eapply rq_bindI; [apply rq_rd_lcI|]. intros l Hl.
  eapply rq_bindI; [apply cg_vfprintf; exact (proj1 (proj2 Hl))|]. intros f' Hf'. apply rq_upd_lcI. intros l0 Hl0. apply LCI_stderr; assumption.
Qed.
#[using="Type"] Lemma cg_efwrite tm nx bs : fsimw npk (RQ tm nx) (efwrite ps_libc set_libc bs : Monad.M PS unit) (efwrite ps_libc set_libc bs) (postI (fun _ => True) tm nx).
Proof.
  unfold efwrite. eapply rq_bindI; [apply rq_rd_lcI|]. intros l Hl.
  eapply rq_bindI; [apply cg_fwrite_file; exact (proj1 (proj2 Hl))|]. intros f' Hf'. apply rq_upd_lcI. intros l0 Hl0. apply LCI_stderr; assumption.
Qed.
Hint Resolve cg_eprintf cg_efwrite : rq.

#[using="Type"] Lemma cg_remove tm nx path : fsimw npk (RQ tm nx) (s_remove path : Monad.M PS Z) (s_remove path) (postI (fun _ => True) tm nx).
Proof. unfold s_remove, remove. cong. Qed.
#[using="Type"] Lemma cg_unlink tm nx path : fsimw npk (RQ tm nx) (s_unlink path : Monad.M PS Z) (s_unlink path) (postI (fun _ => True) tm nx).
Proof. unfold s_unlink, unlink. cong. Qed.
#[using="Type"] Lemma cg_mkstemp tm nx t : fsimw npk (RQ tm nx) (s_mkstemp t : Monad.M PS (list Z * Z)) (s_mkstemp t) (postI (fun _ => True) tm nx).
Proof. unfold s_mkstemp, mkstemp. cong. Qed.
#[using="Type"] Lemma cg_close tm nx fd : fsimw npk (RQ tm nx) (s_close fd : Monad.M PS Z) (s_close fd) (postI (fun _ => True) tm nx).
Proof. unfold s_close, close. cong. Qed.
Hint Resolve cg_remove cg_unlink cg_mkstemp cg_close : rq.

#[using="Type"] Lemma cg_close_files tm nx (fs : list (hptr * file_st)) : Forall (fun pf => file_ok (snd pf)) fs ->
  fsimw npk (RQ tm nx) (close_files fs : Monad.M PS unit) (close_files fs) (postI (fun _ => True) tm nx).
Proof.
  induction fs as [|[p f] fs IH]; intros HF; cbn [close_files]; [apply rq_retI; exact I|].
  apply Forall_cons_iff in HF as [Hf HF]. cbn [snd] in Hf.
  eapply rq_bindI; [apply cg_close_file; exact Hf|]. intros _ _. apply IH. exact HF.
Qed.

#[using="Type"] Lemma cg_stdio_exit tm nx : fsimw npk (RQ tm nx) (s_stdio_exit : Monad.M PS unit) s_stdio_exit (postI (fun _ => True) tm nx).
Proof.
  unfold s_stdio_exit, stdio_exit. eapply rq_bindI; [apply rq_rd_lcI|]. intros l (H1 & H2 & H3).
  eapply rq_bindI; [apply cg_close_files; exact H3|]. intros _ _.
  eapply rq_bindI; [apply cg_close_file; exact H1|]. intros _ _. apply cg_close_file. exact H2.
Qed.
Hint Resolve cg_stdio_exit : rq.

(* [comment removed for export] *)
#[using="Type"] Theorem cg_exit_model tm nx code (Q : Empty_set -> Empty_set -> @rel PS PS) :
  fsimw npk (RQ tm nx) (exit_model s_stdio_exit code : Monad.M PS Empty_set) (exit_model s_stdio_exit code) Q.
Proof.
  unfold exit_model. eapply fsimw_bind; [apply cg_stdio_exit|]. intros a b. apply rq_pure; intros _. apply rq_pure; intros _. apply rq_exit.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cg_diag tm nx d : fsimw npk (RQ tm nx) (Prog.diag d : Monad.M PS unit) (Prog.diag d) (postI (fun _ => True) tm nx).
Proof.
  destruct d; cbn [Prog.diag]; unfold diag_usage, diag_cannot_open, diag_read_error, diag_oom, diag_too_big, diag_short_hdr, diag_cfg_overrun; auto with rq.
Qed.
#[using="Type"] Lemma cg_emit_d tm nx rc : fsimw npk (RQ tm nx) (emit_d ps_libc set_libc rc : Monad.M PS unit) (emit_d ps_libc set_libc rc) (postI (fun _ => True) tm nx).
Proof. unfold emit_d. apply cg_printf. Qed.
Hint Resolve cg_diag cg_emit_d : rq.

End SimStdio.

End WithCeil.
End SimStdio.

(* [comment removed for export] *)
Module SimDriver.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapSim NodeSim ProgSim. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
Definition P9 : Z -> Z := fun _ => 9.
#[using="Type"] Lemma P9_ok c : 0 <= P9 c <= PMAX. Proof. unfold P9, PMAX. lia. Qed.
#[using="Type"] Lemma PHI_P9 : PHI P9 = 239392768. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition B26 : Z := 2^26 + 2 * PGSZ + 20.
(* [comment removed for export] *)
Definition RUNMAX : Z := BLIVE - 239392768.

#[using="Type"] Lemma bigb_B26 n : 0 <= n <= MAX_INPUT -> bigb n <= B26.
Proof. intros Hn. pose proof (bigb_le n (proj1 Hn)). unfold B26, MAX_INPUT in *. lia. Qed.
#[using="Type"] Lemma B26_QMAX : B26 <= QMAX. Proof. unfold B26, QMAX, PGSZ. lia. Qed.

Section SimDriver.
Variable segs : list Segment.
Variables (stkG stkC : stack_site -> Z).          (* [comment removed for export] *)
#[local] Notation npk := (npeek segs).
#[local] Notation RQ := (ProgSim.RQ (CEG:=CEG) (CEC:=CEC) P9 LCI).
#[local] Notation runG := (Prog.run fopsG fo_nop stkG).
#[local] Notation runC := (Prog.run fopsC fo_nop stkC).

(* [comment removed for export] *)
Definition EXT (tm tm' : gmap N Z) : Prop := forall k n, tm !! k = Some n -> tm' !! k = Some n.

(* [comment removed for export] *)
Hypothesis cg_run : forall tm nx config payload,
  zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> zlength payload < MAX_INPUT ->
  fsimw npk (RQ tm nx) (runG config payload) (runC config payload)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx',
                   EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ RQ tm' nx' sG moG sC moC)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[local] Notation read_loop_bodyG := (read_loop_body (@Prog.diag fheap hptr) (pmalloc fopsG) (pfree fopsG) (stkG SiteReadStage)).
#[local] Notation read_loop_bodyC := (read_loop_body (@Prog.diag fheap hptr) (pmalloc fopsC) (pfree fopsC) (stkC SiteReadStage)).

(* [comment removed for export] *)
Definition RD (st : @rd_st hptr) (tm : gmap N Z) : Prop :=
  tm = {[ rd_buf st := rd_cap st ]} /\ 65536 <= rd_cap st <= MAX_INPUT /\ 0 <= rd_len st <= rd_cap st
  /\ zlength (rd_content st) = rd_len st /\ exists k, 0 <= k /\ rd_cap st = 65536 * 2 ^ k.

(* [comment removed for export] *)
#[using="Type"] Lemma cap_double c k : 0 <= k -> c = 65536 * 2 ^ k -> c < MAX_INPUT -> c * 2 <= MAX_INPUT /\ c * 2 = 65536 * 2 ^ (k + 1).
Proof.
  intros Hk -> Hc. unfold MAX_INPUT in *.
  assert (K : k < 10). { destruct (Z_lt_le_dec k 10) as [|GE]; [lia|]. exfalso. pose proof (Z.pow_le_mono_r 2 10 k ltac:(lia) GE). change (2 ^ 10) with 1024 in H. nia. }
  rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
  pose proof (Z.pow_le_mono_r 2 (k + 1) 10 ltac:(lia) ltac:(lia)) as L. rewrite Z.pow_add_r in L by lia. change (2 ^ 10) with 1024 in L. change (2 ^ 1) with 2 in L. nia.
Qed.

#[using="Type"] Lemma sizes_single k n : sizes {[ k := n ]} = [n].
Proof. unfold sizes. rewrite map_to_list_singleton. reflexivity. Qed.

#[using="Type"] Lemma RD_budget st tm n : RD st tm -> 0 <= n <= MAX_INPUT ->
  ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE /\ bigb n <= QMAX.
Proof.
  intros (-> & Hc & Hl & _) Hn. split; [| split].
  - apply (ROOMN_of_len P9). intros c. rewrite sizes_single. unfold zlen, P9. cbn. lia.
  - rewrite sizes_single, PHI_P9. unfold R63N. cbn [zsum map fold_right]. pose proof (bigb_B26 (rd_cap st) ltac:(lia)). pose proof (bigb_B26 n Hn).
    unfold B26, BLIVE, PGSZ in *. lia.
  - pose proof (bigb_B26 n Hn). pose proof B26_QMAX. lia.
Qed.

#[using="Type"] Lemma zlength_app {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
#[using="Type"] Lemma rd_content_app (st : @rd_st hptr) (buf : hptr) cap len ch : rd_content (mkRd buf cap len (rd_chunks st ++ [ch])) = rd_content st ++ ch.
Proof. unfold rd_content. cbn. rewrite concat_app. cbn. rewrite app_nil_r. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rq_use {A} tm nx (m m' : Monad.M PS A) Q :
  (forall sG moG sC moC, RQ tm nx sG moG sC moC -> fsimw npk (RQ tm nx) m m' Q) -> fsimw npk (RQ tm nx) m m' Q.
Proof. intros H sG moG sC moC HR. exact (H _ _ _ _ HR _ _ _ _ HR). Qed.

(* [comment removed for export] *)
Definition RDpost (r : @rd_st hptr + @rd_result hptr) : @rel PS PS := fun sG moG sC moC =>
  exists tm' nx', RQ tm' nx' sG moG sC moC /\
  match r with
  | inl st' => RD st' tm'
  | inr RdExit => True
  | inr (RdDone buf content) => exists cap, tm' = {[ buf := cap ]} /\ zlength content < cap <= MAX_INPUT
  end.

#[using="Type"] Lemma cg_read_loop_body fd path nx st tm :
  RD st tm ->
  fsimw npk (RQ tm nx) (read_loop_bodyG fd path st) (read_loop_bodyC fd path st) (eqpost RDpost).
Proof.
  intros HRD. pose proof HRD as (Etm & Hcap & Hlen & Hcont & kc & Hk & Ek). unfold read_loop_body. cbv zeta.
  apply rq_use. intros sG0 moG0 sC0 moC0 HR0. pose proof (RQ_fresh P9 LCI tm nx _ _ _ _ HR0) as FR. clear HR0 sG0 moG0 sC0 moC0.
  assert (NEb : rd_buf st <> nx) by (intros E; rewrite <- E, Etm in FR; apply lookup_singleton_None in FR; exact (FR eq_refl)).
  (* [comment removed for export] *)
  apply (rq_bind segs (RQ tm nx) (fun g => fun sG moG sC moC => exists tm' nx',
      RQ tm' nx' sG moG sC moC /\ match g with None => True | Some st1 => RD st1 tm' /\ rd_len st1 = rd_len st /\ rd_len st1 < rd_cap st1 /\ rd_content st1 = rd_content st /\ rd_cap st <= rd_cap st1 end)).
  { destruct (rd_len st =? rd_cap st) eqn:EL.
    - apply Z.eqb_eq in EL. destruct (MAX_INPUT <=? rd_cap st) eqn:EM.
      + eapply rq_bind; [apply (cg_diag segs P9)|]. intros []. apply rq_pure; intros _.
        apply rq_ret. intros ? ? ? ? HR. exists tm, nx. split; [exact HR| exact I].
      + apply Z.leb_gt in EM. destruct (cap_double _ _ Hk Ek EM) as [C2 E2].
        destruct (RD_budget st tm (rd_cap st * 2) HRD ltac:(lia)) as (R1 & R2 & R3).
        eapply rq_bind; [apply (rq_pmalloc segs P9 LCI tm nx); [lia| unfold size_overflows; apply Z.leb_gt; unfold MAX_INPUT in *; lia| exact R3| exact R1| exact R2]|].
        intros a. apply rq_pure; intros ->.
        assert (Hold : <[nx := rd_cap st * 2]> tm !! rd_buf st = Some (rd_cap st)).
        { rewrite lookup_insert_ne by (intros E; exact (NEb (eq_sym E))). rewrite Etm. apply lookup_singleton_eq. }
        eapply rq_bind.
        { eapply rq_post; [apply (rq_pfree segs P9 LCI _ (N.succ nx) (rd_buf st) (rd_cap st) Hold)|].
          - rewrite (R63N_insert tm nx _ FR). rewrite PHI_P9. rewrite Etm, sizes_single. unfold R63N. cbn [zsum map fold_right].
            pose proof (bigb_B26 (rd_cap st) ltac:(lia)). pose proof (bigb_B26 (rd_cap st * 2) ltac:(lia)). unfold B26, BLIVE, PGSZ in *. lia.
          - intros u ? ? ? ? H. exact H. }
        intros []. cbn beta. apply rq_ret. intros ? ? ? ? HR. exists (delete (rd_buf st) (<[nx := rd_cap st * 2]> tm)), (N.succ nx).
        split; [exact HR|].
        assert (EC : rd_content (mkRd nx (rd_cap st * 2) (rd_len st) (rd_chunks st)) = rd_content st) by reflexivity.
        unfold RD. cbn [rd_buf rd_cap rd_len rd_chunks]. rewrite EC.
        split; [| repeat split; lia].
        split; [| split; [lia| split; [lia| split; [exact Hcont| exists (kc + 1); split; [lia| exact E2]]]]].
        rewrite delete_insert_ne by exact NEb. rewrite Etm. rewrite delete_singleton_eq. reflexivity.
    - apply Z.eqb_neq in EL. apply rq_ret. intros ? ? ? ? HR. exists tm, nx. split; [exact HR|]. split; [exact HRD|]. repeat split; lia.
  }
  intros g. destruct g as [st1|].
  2:{ apply fsimw_exI; intros tm'. apply fsimw_exI; intros nx'. eapply rq_pre; [| intros ? ? ? ? [H _]; exact H].
      apply rq_ret. intros ? ? ? ? HR. exists tm', nx'. split; [exact HR| exact I]. }
  apply fsimw_exI; intros tm1. apply fsimw_exI; intros nx1.
  eapply (rq_pre segs _ (fun sG moG sC moC => (RD st1 tm1 /\ rd_len st1 = rd_len st /\ rd_len st1 < rd_cap st1 /\ rd_content st1 = rd_content st /\ rd_cap st <= rd_cap st1) /\ RQ tm1 nx1 sG moG sC moC));
    [| intros ? ? ? ? [H1 H2]; split; [exact H2| exact H1]].
  apply rq_pure. intros (HRD1 & EL1 & LT1 & EC1 & LC1). pose proof HRD1 as (Etm1 & Hcap1 & Hlen1 & Hcont1 & k1 & Hk1 & Ek1).
  (* [comment removed for export] *)
  eapply fsimw_bind; [apply rq_get|]. intros sG sC. apply fsimw_pointwise. intros ? ? ? ? (-> & -> & EL & EO & HRQ).
  eapply rq_pre; [| intros ? ? ? ? (-> & -> & -> & ->); exact HRQ]. cbv zeta.
  eapply rq_bind; [apply rq_read|]. intros a. cbv beta. apply rq_pure. intros [rsp Hdec].
  set (want := if READ_CHUNK <? rd_cap st1 - rd_len st then READ_CHUNK else rd_cap st1 - rd_len st) in *.
  assert (Hwant : 0 <= want <= rd_cap st1 - rd_len st) by (subst want; unfold READ_CHUNK; destruct (65536 <? rd_cap st1 - rd_len st) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; lia).
  pose proof (dec_read_Some _ _ _ _ (proj1 Hwant) Hdec) as DF.
  destruct a as [e|bs].
  - eapply rq_bind; [apply (cg_diag segs P9)|]. intros []. apply rq_pure; intros _.
    apply rq_ret. intros ? ? ? ? HR. exists tm1, nx1. split; [exact HR| exact I].
  - destruct DF as [_ HL0].
    assert (HL : zlength (of_bytes bs) = Z.of_nat (length bs)) by (unfold zlength, of_bytes; rewrite length_map; reflexivity).
    assert (HLb : zlength bs = Z.of_nat (length bs)) by reflexivity.
    destruct (length bs =? 0)%nat eqn:EB.
    + apply rq_ret. intros ? ? ? ? HR. exists tm1, nx1. split; [exact HR|]. exists (rd_cap st1). split; [exact Etm1| rewrite Hcont1; lia].
    + apply rq_ret. intros ? ? ? ? HR. exists tm1, nx1. split; [exact HR|].
      unfold RD. cbn [rd_cap rd_len rd_buf rd_chunks]. split; [exact Etm1|]. split; [lia|].
      split; [lia|]. split; [rewrite rd_content_app, zlength_app, Hcont1; lia| exists k1; auto].
Qed.

(* [comment removed for export] *)
Definition RApost (r : @rd_result hptr) : @rel PS PS := fun sG moG sC moC =>
  exists tm' nx', RQ tm' nx' sG moG sC moC /\
  match r with
  | RdExit => True
  | RdDone buf content => exists cap, tm' = {[ buf := cap ]} /\ zlength content < cap <= MAX_INPUT
  end.

#[local] Notation read_allG := (read_all (@Prog.diag fheap hptr) (pmalloc fopsG) (pfree fopsG) (stkG SiteReadStage)).
#[local] Notation read_allC := (read_all (@Prog.diag fheap hptr) (pmalloc fopsC) (pfree fopsC) (stkC SiteReadStage)).

#[using="Type"] Lemma cg_read_all nx path :
  fsimw npk (RQ ∅ nx) (read_allG path) (read_allC path) (eqpost RApost).
Proof.
  unfold read_all.
  eapply rq_bind; [apply rq_msys; exact I|]. intros r. apply rq_pure; intros _.
  destruct r as [e|fd].
  - eapply rq_bind; [apply (cg_diag segs P9)|]. intros []. apply rq_pure; intros _.
    apply rq_ret. intros ? ? ? ? HR. exists ∅, nx. split; [exact HR| exact I].
  - eapply rq_bind.
    { apply (rq_pmalloc segs P9 LCI ∅ nx 65536); [lia| reflexivity| unfold bigb, MMAP_THRESHOLD, QMAX; cbn; lia| |].
      - apply (ROOMN_of_len P9). intros c. rewrite sizes_empty. unfold zlen, P9. cbn. lia.
      - rewrite sizes_empty, PHI_P9. unfold R63N, bigb, MMAP_THRESHOLD, BLIVE. cbn. lia. }
    intros b. apply rq_pure; intros ->.
    eapply rq_bind.
    { eapply fsimw_pre.
      - eapply fsimw_post.
        + apply (fsimw_loop (npeek segs)
                 (fun (x y : @rd_st hptr) => fun sG moG sC moC => y = x /\ exists tm1 nx1, RD x tm1 /\ RQ tm1 nx1 sG moG sC moC)
                 (fun (a b : @rd_result hptr) => fun sG moG sC moC => b = a /\ RApost a sG moG sC moC)).
          intros x y. apply rq_pure; intros ->. apply fsimw_exI; intros tm1. apply fsimw_exI; intros nx1. apply rq_pure; intros HRD.
          eapply fsimw_post; [apply (cg_read_loop_body fd path nx1 x tm1 HRD)|].
          intros [x'|a] [y'|b'] ? ? ? ? [E H]; try discriminate E.
          * injection E as <-. split; [reflexivity|]. destruct H as (tm' & nx' & HR & HRD'). exists tm', nx'. split; assumption.
          * injection E as <-. split; [reflexivity|]. destruct H as (tm' & nx' & HR & HP). exists tm', nx'. split; [exact HR|]. destruct a; exact HP.
        + intros a b' ? ? ? ? [<- H]. split; [reflexivity| exact H].
      - intros ? ? ? ? HR. split; [reflexivity|]. exists (<[nx := 65536]> ∅), (N.succ nx). split; [| exact HR].
        unfold RD. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [rewrite insert_empty; reflexivity|]. unfold MAX_INPUT, rd_content, zlength. cbn. repeat split; try lia. exists 0. split; [lia| reflexivity]. }
    intros res. cbv beta. destruct res as [|buf' content].
    + apply fsimw_exI; intros tm'. apply fsimw_exI; intros nx'. eapply rq_pre; [| intros ? ? ? ? [H _]; exact H].
      apply rq_ret. intros ? ? ? ? HR. exists tm', nx'. split; [exact HR| exact I].
    + apply fsimw_exI; intros tm'. apply fsimw_exI; intros nx'.
      eapply (rq_pre segs _ (fun sG moG sC moC => (exists cap, tm' = {[buf' := cap]} /\ zlength content < cap <= MAX_INPUT) /\ RQ tm' nx' sG moG sC moC)); [| intros ? ? ? ? [H1 H2]; split; assumption].
      apply rq_pure; intros HC.
      eapply rq_bind; [apply rq_msys; exact I|]. intros ?. apply rq_pure; intros _.
      apply rq_ret. intros ? ? ? ? HR. exists tm', nx'. split; [exact HR| exact HC].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma zlength_skipn {A} n (l : list A) : zlength (skipn n l) <= zlength l.
Proof. unfold zlength. rewrite length_skipn. lia. Qed.

#[using="Type"] Lemma budget_single buf cap : 65536 <= cap <= MAX_INPUT ->
  zlen (sizes {[buf := cap]}) <= 1 /\ R63N (sizes {[buf := cap]}) <= B26 /\ PHI P9 + R63N (sizes {[buf := cap]}) <= BLIVE.
Proof.
  intros Hc. rewrite sizes_single. unfold zlen, R63N. cbn [length zsum map fold_right Z.of_nat]. rewrite PHI_P9.
  pose proof (bigb_B26 cap ltac:(lia)). unfold B26, BLIVE, PGSZ in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="cg_run"] Theorem cg_main_prog nx argv :
  fsimw npk (RQ ∅ nx) (main_prog fopsG fo_nop stkG argv) (main_prog fopsC fo_nop stkC argv)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx', RQ tm' nx' sG moG sC moC)).
Proof.
  unfold main_prog, main_model.
  destruct (negb (Z.of_nat (length argv) =? 2)).
  { eapply rq_bind; [apply (cg_diag segs P9)|]. intros []. apply rq_pure; intros _. apply rq_ret. intros ? ? ? ? HR. exists ∅, nx. exact HR. }
  eapply rq_bind; [apply cg_read_all|]. intros ra.
  apply fsimw_exI; intros tm. apply fsimw_exI; intros nx1.
  destruct ra as [|buf content].
  { eapply rq_pre; [| intros ? ? ? ? [H _]; exact H]. apply rq_ret. intros ? ? ? ? HR. exists tm, nx1. exact HR. }
  eapply (rq_pre segs _ (fun sG moG sC moC => (exists cap, tm = {[buf := cap]} /\ zlength content < cap <= MAX_INPUT) /\ RQ tm nx1 sG moG sC moC)); [| intros ? ? ? ? [H1 H2]; split; assumption].
  apply rq_pure. intros (cap & -> & Hcap). cbv zeta.
  pose proof (bigb_B26 cap) as HB26.
  assert (BUD : zlen (sizes {[buf := cap]}) <= 1 /\ R63N (sizes {[buf := cap]}) <= B26 /\ PHI P9 + R63N (sizes {[buf := cap]}) <= BLIVE).
  { rewrite sizes_single. unfold zlen, R63N. cbn [length zsum map fold_right Z.of_nat]. rewrite PHI_P9.
    pose proof (zlen_nonneg content). specialize (HB26 ltac:(unfold zlength in *; lia)). unfold B26, BLIVE, PGSZ in *. repeat split; lia. }
  destruct BUD as (BUD1 & BUD2 & BUD3).
  assert (FREE : forall tm' nx', EXT {[buf := cap]} tm' -> PHI P9 + R63N (sizes tm') <= BLIVE ->
            fsimw npk (RQ tm' nx') (pfree fopsG buf) (pfree fopsC buf) (eqpost (fun _ => RQ (delete buf tm') nx'))).
  { intros tm' nx' HE HB. apply (rq_pfree segs P9 LCI tm' nx' buf cap); [apply HE; apply lookup_singleton_eq| exact HB]. }
  destruct (zlength content <? HDR_MIN).
  { eapply rq_bind; [apply (cg_diag segs P9)|]. intros []. apply rq_pure; intros _.
    eapply rq_bind; [apply (FREE _ nx1); [intros k n H; exact H| exact BUD3]|]. intros []. apply rq_ret. intros ? ? ? ? HR. eexists _, _. exact HR. }
  destruct (zlength content <? HDR_MIN + Z.land (le16 content) 32767).
  { eapply rq_bind; [apply (cg_diag segs P9)|]. intros []. apply rq_pure; intros _.
    eapply rq_bind; [apply (FREE _ nx1); [intros k n H; exact H| exact BUD3]|]. intros []. apply rq_ret. intros ? ? ? ? HR. eexists _, _. exact HR. }
  eapply rq_bind.
  { apply cg_run; [exact BUD1| exact BUD2|]. pose proof (zlength_skipn (Z.to_nat (6 + Z.land (le16 content) 32767)) content). lia. }
  intros status. apply fsimw_exI; intros tm'. apply fsimw_exI; intros nx'.
  eapply (rq_pre segs _ (fun sG moG sC moC => (EXT {[buf := cap]} tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE) /\ RQ tm' nx' sG moG sC moC)); [| intros ? ? ? ? (H1 & H2 & H3); split; [split; [exact H1| exact H2]| exact H3]].
  apply rq_pure. intros [HE HB].
  eapply rq_bind; [apply (FREE _ nx' HE HB)|]. intros []. apply rq_ret. intros ? ? ? ? HR. eexists _, _. exact HR.
Qed.

End SimDriver.

End WithCeil.
End SimDriver.
