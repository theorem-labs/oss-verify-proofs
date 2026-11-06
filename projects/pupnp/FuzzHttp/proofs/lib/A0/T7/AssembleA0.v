(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim DriverSim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import MSafe.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import TSimS RealizeS RealizeS2 A0Prog TopA0 DriverModelA.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit) (only parsing).

Section FdTree.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  #[using="Type"] Lemma fdtree_mret {A} : forall (a : A) (s : St), fdtree (mret a s). Proof. intros; exact I. Qed.
  #[using="Type"] Lemma fdtree_munr {A} : forall (s : St), fdtree (munr (A:=A) s). Proof. intros; exact I. Qed.
  #[using="Type"] Lemma fdtree_mbind {A B} : forall (m : Monad.M St A) (f : A -> Monad.M St B) s,
    fdtree (m s) -> (forall a s', fdtree (f a s')) -> fdtree (mbind m f s).
  Proof. intros m f s Hm Hf. unfold mbind, ebind. apply fdtree_bind; [exact Hm|]. intros [|[a s']]; cbn; [exact I| apply Hf]. Qed.
  #[using="Type"] Lemma fdtree_msys {A} : forall n (dec : resp -> option A) (s : St), fdn n -> fdtree (msys n dec s).
  Proof. intros n dec s Hn. unfold msys, enode. cbn. split; [exact Hn|]. intros r. destruct (dec r); exact I. Qed.
  #[using="Type"] Lemma fdtree_mloop {X R} : forall fuel (body : X -> Monad.M St (X + R)%type) x s,
    (forall x s, fdtree (body x s)) -> fdtree (mloop fuel body x s).
  Proof.
    induction fuel as [|fuel IH]; intros body x s HB; cbn [mloop]; [apply fdtree_munr|].
    apply fdtree_mbind; [apply HB|]. intros [x'|r] s'; [apply IH; exact HB| apply fdtree_mret].
  Qed.
End FdTree.

Lemma fdtree_stdio_wloop {St} : forall fuel fd bufs (s : St), fdtree (stdio_wloop fuel fd bufs s).
Proof.
  induction fuel as [|fuel IH]; intros fd bufs s; cbn [stdio_wloop]; [apply fdtree_munr|].
  apply fdtree_mbind; [apply fdtree_msys; left; exact I|]. intros j s'. destruct (j =? _); [apply fdtree_mret| apply IH].
Qed.

Lemma fdtree_stderr_pieces {St} : forall ps buf (s : St), fdtree (stderr_pieces buf ps s).
Proof.
  induction ps as [|p ps IH]; intros buf s; cbn [stderr_pieces]; [apply fdtree_mret|].
  destruct (_ <? _); [| apply IH]. apply fdtree_mbind; [unfold stdio_writev; apply fdtree_stdio_wloop|]. intros; apply IH.
Qed.

Ltac fdt :=
  lazymatch goal with
  | |- fdtree (mret _ _) => apply fdtree_mret
  | |- fdtree (munr _) => apply fdtree_munr
  | |- fdtree (mget _) => exact I
  | |- fdtree (mupd _ _) => exact I
  | |- fdtree (msys _ _ _) => apply fdtree_msys; first [left; exact I | right; exact I]
  | |- fdtree (mbind _ _ _) => apply fdtree_mbind; [fdt | intros; fdt]
  | |- fdtree (mloop _ _ _ _) => apply fdtree_mloop; intros; fdt
  | |- fdtree ((if ?b then _ else _) _) => destruct b; fdt
  | |- fdtree (if ?b then _ else _) => destruct b; fdt
  | |- fdtree ((match ?x with _ => _ end) _) => destruct x; fdt
  | |- fdtree (match ?x with _ => _ end) => destruct x; fdt
  | |- fdtree (upd_so _ _ _ _) => exact I
  | |- fdtree (rd_so _ _) => exact I
  | |- fdtree (stdio_wloop _ _ _ _) => apply fdtree_stdio_wloop
  | |- fdtree (stdio_writev _ _ _ _) => unfold stdio_writev; fdt
  | |- fdtree (stdout_stdio_write _ _ _ _) => unfold stdout_stdio_write; fdt
  | |- fdtree (stdout_writefn _ _ _ _) => unfold stdout_writefn; fdt
  | |- fdtree (stdout_exit_flush _ _ _) => unfold stdout_exit_flush; fdt
  | |- fdtree (stderr_pieces _ _ _) => apply fdtree_stderr_pieces
  | |- fdtree (stderr_fprintf _ _) => unfold stderr_fprintf; fdt
  | |- fdtree (stderr_fwrite _ _) => unfold stderr_fwrite; fdt
  | |- fdtree (io_diag _ _ _) => cbn [io_diag io_S ioA s_diag]; fdt
  | |- fdtree (io_exit _ _) => cbn [io_exit io_S ioA]; fdt
  | |- fdtree (s_diag _ _ _ _) => unfold s_diag; fdt
  | |- fdtree (exit_k _ _ _) => unfold exit_k; fdt
  | |- fdtree (exit_model _ _ _) => unfold exit_model; fdt
  | |- fdtree (read_all _ _ _ _ _ _) => unfold read_all; fdt
  | |- fdtree (read_loop_body _ _ _ _ _ _ _ _) => unfold read_loop_body; fdt
  | |- fdtree (amalloc0 _ _) => unfold amalloc0; fdt
  | |- fdtree (afree0 _ _) => unfold afree0; fdt
  | |- fdtree ?t => fail 100 "fdt: unknown tree" t
  end.

Lemma fdtree_drv_preA : forall rs argv so, fdtree (drv_preA rs argv so).
Proof. intros rs argv so. unfold drv_preA, drv_pre. fdt. Qed.

Section AssembleA0.
  Variable RS_A : Z.
  Variable H_MAIN_A0 : ProcInput -> ExecEntry -> machine_state -> Model -> Prop.

  Variable AS : Type.
  Variable V : AS -> Model -> Model.
  Variable INV : config -> AS -> Prop.
  Variable ATN : node -> machine_state -> AS -> Prop.
  Variable GOOD : node -> resp -> Prop.
  Hypothesis V_meq : forall a mo, meq (V a mo) mo.
  Hypothesis V_fs : forall a mo, m_fs (V a mo) = m_fs mo.
  Hypothesis NODE : forall n ms mo a,
    fdn n -> ATN n ms a -> INV (mkCfg ms mo) a ->
    (forall e st, sstep_cfg asegs ACFG (mkCfg ms mo) e st ->
        (exists rsp mo', st = SNext (mkCfg (nret ms rsp) mo') /\ nstep n (V a mo) rsp (V a mo') e /\ INV (mkCfg (nret ms rsp) mo') a /\ GOOD n rsp)
     \/ (exists code mo', st = SNext (mkCfg ms mo') /\ nexit n (V a mo) code (V a mo')
           /\ e = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code))
    /\ (forall rsp moE' evs, nstep n (V a mo) rsp moE' evs ->
        exists mo', V a mo' = moE' /\ sstep_cfg asegs ACFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo')) /\ INV (mkCfg (nret ms rsp) mo') a /\ GOOD n rsp)
    /\ (forall code moE', nexit n (V a mo) code moE' ->
        exists mo', V a mo' = moE' /\ m_halted mo' = Some code
          /\ sstep_cfg asegs ACFG (mkCfg ms mo) [ExitEv code (m_fs moE')] (SNext (mkCfg ms mo')))
    /\ ((exists rsp moE' evs, nstep n (V a mo) rsp moE' evs) \/ (exists code moE', nexit n (V a mo) code moE')).
  Local Notation implS := (RealizeS.implS asegs AS V INV ATN GOOD).

  Hypothesis V_ok : forall ms mo a, INV (mkCfg ms mo) a -> exists mo', meq (V a mo) mo' /\ minv mo' /\ m_halted mo' = None.

  Variable QLEAF : ProcInput -> ExecEntry -> exc (at_parser (ptr:=unit) * ASt) -> machine_state -> AS -> Prop.

  Hypothesis DRIVER : forall inp en ms mo,
    valid_input inp -> valid_entry imgA0 en inp -> H_MAIN_A0 inp en ms mo ->
    exists a, INV (mkCfg ms mo) a /\ implS (drv_preA RS_A (argv_Z (in_argv inp)) stdout_init) (QLEAF inp en) ms a.

  Hypothesis LEAF : forall inp en ap so ms a mo,
    QLEAF inp en (Ok (ap, so)) ms a -> INV (mkCfg ms mo) a -> ap_factsA ap -> (length (so_buf so) <= 1024)%nat ->
    realizes asegs (mkCfg ms mo) (AssembleP0.PSH (Z.to_nat (ap_calls ap)) stdout_init (m_fs mo)).

  #[using="Type"] Lemma argvZ_small : forall argv, valid_argv argv -> Forall (fun a => Z.of_nat (length a) < 2^32) (argv_Z argv).
  Proof.
    intros argv (_ & _ & HL & _). unfold argv_Z. apply Forall_map.
    eapply Forall_impl; [| exact HL]. intros a Ha. cbn in Ha |- *. rewrite length_map. lia.
  Qed.

  #[using="AS V INV ATN GOOD V_meq V_fs NODE V_ok QLEAF DRIVER LEAF"] Theorem main_realizes : MAIN H_MAIN_A0 RS_A.
  Proof.
    intros inp en [ms mo] VI VE HM. unfold at_main in HM. cbn [cfg_ms cfg_model] in HM |- *.
    destruct (DRIVER inp en ms mo VI VE HM) as (a & HINV & HI).
    destruct (V_ok ms mo a HINV) as (mo1 & HM1 & MV & HV).
    unfold T_A0main.
    assert (KC : forall (r : exc (at_parser * ASt)) m1 m2, meq m1 m2 -> t_eq (KLEAF_A r m1) (KLEAF_A r m2)).
    { intros [|[ap so]] m1 m2 [EF ES]; cbn [KLEAF_A fst snd]; [apply t_eq_refl|]. rewrite ES. apply t_eq_refl. }
    apply (rz_conseq asegs _ (tsh (drv_preA RS_A (argv_Z (in_argv inp)) stdout_init) (V a mo) KLEAF_A)).
    2:{ apply (tsh_fdtree_cong _ KLEAF_A (V a mo) mo (fdtree_drv_preA _ _ _) (V_meq a mo) KC). }

    assert (TWF : twf (drv_preA RS_A (argv_Z (in_argv inp)) stdout_init) (V a mo)
                      (fun r mo' => match r with
                                    | Unr => False
                                    | Ok p => m_fs mo' = m_fs (V a mo) /\ (length (so_buf (snd p)) <= 1024)%nat /\ ap_factsA (fst p)
                                    end)).
    { apply (twf_fdtree_cong _ _ mo1 (V a mo) (fdtree_drv_preA _ _ _) (meq_sym _ _ HM1)).
      { intros [|[ap so]] m1 m2 [EF ES]; cbn [fst snd]; [intros F; exact F|]. intros (E1 & HB & HF). rewrite <- ES. auto. }
      eapply twf_mono.
      - apply (drv_preA_twf RS_A (m_fs (V a mo)) (argv_Z (in_argv inp)) stdout_init mo1); [apply argvZ_small; exact (proj1 VI)|].
        split; [exact MV|]. split; [exact HV|]. split; [symmetry; exact (proj2 HM1)| cbn; lia].
      - intros [|[ap so]] mo2; cbn [fst snd]; [intros F; exact F|]. intros ((_ & _ & EFS & HB) & HF). auto. }
    apply (implS_realizes_twf asegs AS V INV ATN GOOD V_fs NODE _ (QLEAF inp en) _ KLEAF_A ms a mo (fdtree_drv_preA _ _ _) HI HINV TWF).
    - intros [|[ap so]] m1 m2 [EF ES]; cbn [fst snd]; [intros F; exact F|]. intros (E1 & HB & HF). rewrite <- ES. auto.
    - intros [|[ap so]] ms' a' mo' HQ HINV' HP; cbn [KLEAF_A fst snd] in HP |- *; [destruct HP|].
      destruct HP as (_ & HB & HF).
      eapply rz_conseq; [exact (LEAF inp en ap so ms' a' mo' HQ HINV' HF HB)|]. cbn [KLEAF_A fst snd].
      rewrite (proj2 (V_meq a' mo')). apply t_eq_refl.
    - exact KC.
  Qed.
End AssembleA0.
