(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import PropExec MState ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad MSafe MSafeR STree Malloc Prog KInv KStep KStepC MallocNS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

Section WithCeiling. Context {CE__ : Ceiling}.

Lemma twfR_of_twf_tpath : forall {R} (t : itree node R) mo (P Q : R -> Model -> Prop),
  twf t mo P -> (forall tr r mo', tpath nstepR t mo tr r mo' -> Q r mo') -> twfR t mo (fun r mo' => P r mo' /\ Q r mo').
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P Q HT HQ; cbn in *.
  - split; [exact HT|]. apply (HQ []). repeat split; reflexivity.
  - destruct HT as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH.
    + apply (Hk rsp mo' evs). exact (proj1 Hst).
    + intros tr r mo'' Hp. apply (HQ (evs ++ tr)). exists rsp, mo', evs, tr. split; [exact Hst|]. split; [exact Hp | reflexivity].
Qed.

Lemma mspecR_strengthen : forall {St A} (P : assn St) (m : Monad.M St A) (Q : A -> assn St) (Q2 : A -> St -> Model -> Prop),
  mspec P m Q ->
  (forall s mo, P s mo -> forall tr a s' mo', tpath nstepR (m s) mo tr (Ok (a, s')) mo' -> Q2 a s' mo') ->
  mspecR P m (fun a s mo => Q a s mo /\ Q2 a s mo).
Proof.
  intros St A P m Q Q2 Hm HQ s mo HP. unfold etwfR.
  eapply twfR_mono.
  - apply (twfR_of_twf_tpath (m s) mo (fun r mo1 => match r with Unr => False | Ok p => Q (fst p) (snd p) mo1 end)
                               (fun r mo' => match r with Unr => True | Ok p => Q2 (fst p) (snd p) mo' end)).
    + exact (Hm s mo HP).
    + intros tr [|[a s']] mo' Hp; [exact I|]. cbn. exact (HQ s mo HP tr a s' mo' Hp).
  - intros [|[a s']] mo1; cbn; [intros [F _]; exact F | intros [H1 H2]; split; assumption].
Qed.

Lemma dec_mmap_ok_ret : forall len avoid rsp x, dec_mmap len avoid rsp = Some (MmOk x) -> x = bv_unsigned (eff_ret rsp).
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (errno_of r); discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (_ && _); [|discriminate]. injection H as <-. reflexivity.
Qed.

Lemma dec_mmap_none_ok_ret : forall len avoid rsp x, dec_mmap_none len avoid rsp = Some (MmOk x) -> x = bv_unsigned (eff_ret rsp).
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate; destruct cs; try discriminate; destruct ci; try discriminate.
  - destruct (errno_of r); discriminate.
  - destruct (_ && _); [|discriminate]. injection H as <-. reflexivity.
Qed.

Lemma dec_mmap_err_ret : forall len avoid rsp e, dec_mmap len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros len avoid [r ws zs us cs ci] e H. unfold dec_mmap in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (errno_of r); [injection H as ->; reflexivity | discriminate].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (_ && _); discriminate.
Qed.

Lemma dec_mmap_none_err_ret : forall len avoid rsp e, dec_mmap_none len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros len avoid [r ws zs us cs ci] e H. unfold dec_mmap_none in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate; destruct cs; try discriminate; destruct ci; try discriminate.
  - destruct (errno_of r); [injection H as ->; reflexivity | discriminate].
  - destruct (_ && _); discriminate.
Qed.

Lemma dec_mprotect_err_ret : forall addr len rsp e, dec_mprotect addr len rsp = Some (RgErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros addr len [r ws zs us cs ci] e H. unfold dec_mprotect in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (errno_of r); [injection H as ->; reflexivity |].
    destruct (bv_unsigned r =? 0); discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (_ && _); discriminate.
Qed.

Lemma noerr_not_err : forall r, errno_of r = None -> is_err (bv_unsigned r) = false.
Proof.
  intros r H. unfold errno_of in H. destruct (Z.leb_spec (2 ^ 64 - 4095) (bv_unsigned r)); [discriminate H|].
  unfold is_err, TWO64. destruct (Z.ltb_spec (2 ^ 64 - 4096) (bv_unsigned r)); [exfalso; lia | reflexivity].
Qed.

Lemma tpath_sys_ret : forall {St A B} n (dec : resp -> option A) (g : A -> B) (s : St) mo tr b s' mo',
  tpath nstepR (mbind (msys n dec) (fun a => mret (g a)) s) mo tr (Ok (b, s')) mo' ->
  exists rsp a, nstepR n mo rsp mo' tr /\ dec rsp = Some a /\ b = g a /\ s' = s.
Proof.
  intros St A B n dec g s mo tr b s' mo' Hp. unfold mbind, msys, mret in Hp.
  apply tpath_ebind in Hp. destruct Hp as [[_ E]|(tr1 & [a s1] & mo1 & tr2 & H1 & H2 & ->)]; [discriminate E|].
  cbn in H2. destruct H2 as (E & -> & ->). rewrite app_nil_r.
  apply tpath_enode in H1. destruct H1 as (rsp & Hst & Er).
  destruct (dec rsp) as [a'|] eqn:Ed; [|discriminate Er].
  exists rsp, a'. injection Er as -> ->. injection E as -> ->. auto.
Qed.

Theorem ev_step_okR : forall e (s : PState) mo tr z s' mo', tpath nstepR (ev_step e s) mo tr (Ok (z, s')) mo' -> ev_okR e z.
Proof.
  intros e s mo tr z s' mo' Hp. destruct e as [req|addr len prot flags|addr len|addr len prot|p caddr hint|why]; cbn [ev_okR]; try exact I.
  -   intros Hfix. unfold ev_step in Hp.
    assert (EQ : Prog.MAP_FIXED_Z = MAP_FIXED) by reflexivity.
    rewrite EQ in Hp. rewrite Hfix in Hp. cbn [Z.eqb negb] in Hp.
    destruct (prot =? 0).
    + destruct (tpath_sys_ret _ _ _ _ _ _ _ _ _ Hp) as (rsp & a & [_ Hok] & Hd & -> & ->). cbn [okR] in Hok. rewrite <- EQ in Hfix. specialize (Hok Hfix).
      destruct a as [e0|x]; [exfalso; rewrite (dec_mmap_none_err_ret _ _ _ _ Hd) in Hok; discriminate Hok|].
      rewrite (dec_mmap_none_ok_ret _ _ _ _ Hd). apply noerr_not_err. exact Hok.
    + destruct (tpath_sys_ret _ _ _ _ _ _ _ _ _ Hp) as (rsp & a & [_ Hok] & Hd & -> & ->). cbn [okR] in Hok. rewrite <- EQ in Hfix. specialize (Hok Hfix).
      destruct a as [e0|x]; [exfalso; rewrite (dec_mmap_err_ret _ _ _ _ Hd) in Hok; discriminate Hok|].
      rewrite (dec_mmap_ok_ret _ _ _ _ Hd). apply noerr_not_err. exact Hok.
  -   unfold ev_step in Hp.
    destruct (tpath_sys_ret _ _ _ _ _ _ _ _ _ Hp) as (rsp & a & [_ Hok] & Hd & -> & ->). cbn [okR] in Hok.
    unfold dec_mprotect_rw in Hd. destruct (dec_mprotect addr len rsp) as [[e0|[|]]|] eqn:Ed; try discriminate Hd.
    + exfalso. destruct (e0 =? ENOSYS); [discriminate Hd|]. rewrite (dec_mprotect_err_ret _ _ _ _ Ed) in Hok. discriminate Hok.
    + injection Hd as <-. reflexivity.
  -   unfold ev_step, munr in Hp. cbn in Hp. destruct Hp as (E & _). discriminate E.
Qed.

Theorem membed_rpath : forall {R} (t : stree ev Z R) (s : PState) mo tr r s' mo',
  tpath nstepR (membed t s) mo tr (Ok (r, s')) mo' -> rpath t r.
Proof.
  intros R t. induction t as [r0|e k IH]; intros s mo tr r s' mo' Hp.
  - cbn in Hp. destruct Hp as (E & _). injection E as -> ->. constructor.
  - cbn [membed] in Hp. unfold mbind in Hp. apply tpath_ebind in Hp.
    destruct Hp as [[_ E]|(tr1 & [z s1] & mo1 & tr2 & H1 & H2 & ->)]; [discriminate E|].
    cbn [fst snd] in H2. econstructor; [exact (ev_step_okR e s mo tr1 z s1 mo1 H1) | exact (IH z s1 mo1 tr2 r s' mo' H2)].
Qed.

Theorem raw_malloc_someR : forall n (s : PState) mo tr r s' mo',
  size_overflows n = false -> tpath nstepR (raw_malloc n s) mo tr (Ok (r, s')) mo' -> exists p, r = Some p.
Proof.
  intros n s mo tr r s' mo' Hov Hp. unfold raw_malloc, mbind, mget, mupd, mret in Hp.
  apply tpath_ebind in Hp. destruct Hp as [[Hu _]|(tr1 & [s0 s0'] & mo1 & tr2 & H1 & H2 & ->)]; [cbn in Hu; destruct Hu as (E & _); discriminate E|].
  cbn in H1. destruct H1 as (E1 & -> & ->). injection E1 as <- <-.
  apply tpath_ebind in H2. destruct H2 as [[_ E]|(tr3 & [[st' p] s2] & mo3 & tr4 & H3 & H4 & ->)]; [discriminate E|].
  apply tpath_ebind in H4. destruct H4 as [[_ E]|(tr5 & [u s3] & mo5 & tr6 & H5 & H6 & ->)]; [discriminate E|].
  cbn in H5. destruct H5 as (E5 & -> & ->). cbn in H6. destruct H6 as (E6 & -> & ->).
  cbn [fst snd] in H3. destruct (cmalloc_rpath_some _ _ _ _ Hov (membed_rpath _ _ _ _ _ _ _ H3)) as [c ->].
  injection E6 as <- E. eexists. reflexivity.
Qed.

Theorem raw_malloc_spec_R : forall X G n, frame_ok G -> 0 <= n -> size_overflows n = false ->
  mspecR (OWN X G) (raw_malloc n)
         (fun r s mo => exists p, r = Some p /\ OWN (p :: X) G s mo /\ n < 2 ^ 63).
Proof.
  intros X G n HG Hn Hov.
  pose proof (mspecR_strengthen (OWN X G) (raw_malloc n)
                (fun r s mo => match r with Some p => OWN (p :: X) G s mo /\ n < 2 ^ 63 | None => OWN X G s mo end)
                (fun r _ _ => exists p, r = Some p)
                (raw_malloc_spec_c X G n HG Hn)
                (fun s mo _ tr a s' mo' Hp => raw_malloc_someR n s mo tr a s' mo' Hov Hp)) as M.
  eapply mspecR_conseq; [exact M | intros s mo H; exact H |].
  intros r s mo [HQ [p ->]]. cbn in HQ. exists p. split; [reflexivity | exact HQ].
Qed.

End WithCeiling.
