(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg ShapeAlg.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~je4TSet35stdpp9bitvectorbdefinitionso02bv3h5LinuxProcessSemanticsfLinuxProcessSem5Stateq25event03app04cons03nil3h5LinuxProcessSemanticsfLinuxProcessSem2Fsu82Fs37Corelib4Init5Logichh83andhh83notq26ExitEvq26KillEv36Stdlib5Lists4Listhkc2In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib6BridgeaMustExitIn~~~~~~hm58exits_inje4t_eqhh85Falsehh84Truehh82eqhm5ano_exit_ev37Corelib5Lists7ListDefhu16Forallje6t_exithh82exje6t_emitje6t_alt206option3h5LinuxProcessSemanticsfLinuxProcessSem3Runiib9cfg_model04Noneq28m_halted04Somehh82or3h5LinuxProcessSemanticsh5EquivalenceDefinition8MustExitio1h3must_exit_in_at_cfgiib6configq28m_killed69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~iu68the_scfgje8realizesiibbSpuriousCfgiibfrefusal_decidedq25Modelq2cSyscallInputio1cdecided_from3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejnd7Segmenthe1Zio1brun_decidedjnd5Imageiib9ExecEntryq29ProcInput3h5LinuxProcessSemanticsh5EquivalenceDefinitioncHaltsAllowedjv2hchalts_allowed_T_scfg_budgetsio1h1must_exit_in_scfgiib6cfg_leiibbvalid_entryiibbvalid_input" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exits_in : ltac2:(zQ "40!h8!j7!n9!pd>1S@1$0@1$3@1$1#k0>1T$2P") := ltac2:(zQ "e0!t0!j7!pd!h8!t8!td!u3!hh3!hic!hj3!hja!hk3!n9!hlf\1S@1$3@1$2@1$1#k0\1T$c@2$8>2tr@1$3$0>1k@1$2@1$1#k0>2fs$7>0@1^4@3$4$0^3@3$5$0@2$a^2^1@1$6$0@3$d@1$2@1$1#k0^3^6>2tr@1$3$0>1s@1$2@1$1#k0>2fs$7@1$9@1^4@3$4$0^3@3$5$0@2$b^2^1@1$6$0").

Lemma exits_in_eq : ltac2:(zQ "60!hq9!n9!h8!j7!hr5!pd>1S@1$2@1$5@1$3#k0>1T$1>2T'$1>0@2$4^2^1>0@2$0^4^2@2$0^5^4").
Proof.
  intros S T T' Heq [H1 H2]. split.
  - intros tr k fs HT. apply (H1 tr k fs). apply Heq. exact HT.
  - intros tr s fs HT. apply (H2 tr s fs). apply Heq. exact HT.
Qed.

Lemma is_prefix_exists {A} : forall (a l : list A), is_prefix a l -> exists m, l = a ++ m.
Proof.
  induction a as [|x a IH]; intros l H.
  - exists l. reflexivity.
  - destruct l as [|y l]; cbn in H; [contradiction|]. destruct H as [-> H].
    destruct (IH l H) as [m ->]. exists m. reflexivity.
Qed.

(* [comment removed for export] *)
Definition no_exit_ev : ltac2:(zQ "10!t0>1e$0P") := ltac2:(zQ "61!j7!pd!t0!hrc!hs5!hh3&\2ch@1$1@1$0#k0\1b@1$1@1$0#8$4\1e$2M2\1e$2P^1~0~0\4code@1$1@1$0#k0\2fs$5$3\3sig@1$1@1$0#k0\2fs$5$3").

Lemma no_exit_snoc : ltac2:(zQ "90!t0!h8!t8!hrc!hsd!ht3!td!u3!hv8>2tr@1$1$0>1e$0>1m@1$1$0>3evs@1$1$0>0@3$4P@1$5^3$3>0@3$4@1$1$0^2@3$2$0@3$2$0^5@3$6$0^4@1$7$0^3>0@3$8$0$5^3$3").
Proof.
  intros tr e m evs He -> H.
  apply Forall_app in H as [H _]. apply Forall_app in H as [_ H].
  inversion H as [| x l Hx Hl]; subst. rewrite He in Hx. exact Hx.
Qed.

Lemma t_exit_snoc : ltac2:(zQ "c0!t0!h8!u3!hsd!t8!td!hic!j7!hh3!hja!ig2!pd>4code@1$b@1$7#k0>2fs$8>2tr@1$1$0>1e$0>0@3$a^4^3@3$4$0^2@3$5$0^1@1$2$0@2$6@3$3@1$1$0^3@1$2$0@3$3$0^2@2$9^5^4").
Proof.
  intros code fs tr e H. unfold t_exit, t_emit, t_nil in H.
  destruct H as [Hp | (tr' & Heq & ->)].
  - apply is_prefix_exists in Hp as [m Hm].
    destruct tr as [|e' tr]; cbn in Hm.
    + injection Hm as He _. split; [reflexivity | first [exact He | symmetry; exact He]].
    + injection Hm as _ Hnil. exfalso. destruct tr; discriminate Hnil.
  - rewrite app_nil_r in Heq. destruct tr as [|e' tr]; cbn in Heq.
    + injection Heq as He. split; [reflexivity | first [exact He | symmetry; exact He]].
    + injection Heq as _ Hnil. exfalso. destruct tr; discriminate Hnil.
Qed.

Lemma exits_in_exit : ltac2:(zQ "70!j7!pd!h8!hh3!hq9!ig2!hlf>1S@1$2@1$1@1$0#k0>4code@1$1@1$0#k0>2fs$3>0@3$6@1$1@1$0#k0^2^3@2$4^4@2$5^3^2").
Proof.
  intros S code fs Hin. split.
  - intros tr k fs' H. destruct (t_exit_snoc _ _ _ _ H) as [_ He]. injection He as <- _. exact Hin.
  - intros tr s fs' H. destruct (t_exit_snoc _ _ _ _ H) as [_ He]. discriminate He.
Qed.

Lemma t_emit_snoc : ltac2:(zQ "c0!t0!h8!t8!td!u3!ht3!hrc!hsd!igb!hv8!n9!ih1>3evs@1$1$0>1T$a>2tr@1$1$0>1e$0>0@3$9$0$5^4>0@3$7P@1$5^2$6>0@3$b^6^5@3$2$0^4@3$3$0^3@1$4$0@2$8@1$1$0\3tr1@1$1$0@1^7@3$2$0^1@3$3$0^5@1$4$0").
Proof.
  intros evs T tr e Hne He [Hp | (tr' & Heq & HT')].
  - exfalso. apply is_prefix_exists in Hp as [m Hm]. exact (no_exit_snoc tr e m evs He Hm Hne).
  - destruct tr' as [| e0 tr0].
    + exfalso. rewrite app_nil_r in Heq.
      apply (no_exit_snoc tr e [] evs He); [rewrite app_nil_r; symmetry; exact Heq | exact Hne].
    + assert (Hne0 : e0 :: tr0 <> []) by discriminate.
      destruct (exists_last Hne0) as [tr1 [e1 Htr1]]. rewrite Htr1 in Heq, HT'.
      rewrite app_assoc in Heq. apply app_inj_tail in Heq as [_ <-].
      exists tr1. exact HT'.
Qed.

Lemma exits_in_emit : ltac2:(zQ "90!h8!t0!hq9!hv8!j7!ht3!n9!ih1!pd>1S@1$0@1$8@1$4#k0>3evs@1$0$1>1T$6>0@3$3$1$5^2>0@2$2^4^2@2$2^5@2$7^4^3").
Proof.
  intros S evs T Hne [HT1 HT2]. split.
  - intros tr k fs H. destruct (t_emit_snoc evs T tr (ExitEv k fs) Hne eq_refl H) as [tr1 H1]. exact (HT1 tr1 k fs H1).
  - intros tr s fs H. destruct (t_emit_snoc evs T tr (KillEv s fs) Hne eq_refl H) as [tr1 H1]. exact (HT2 tr1 s fs H1).
Qed.

Lemma exits_in_alt2 : ltac2:(zQ "60!hq9!n9!h8!j7!iha!pd>1S@1$2@1$5@1$3#k0>1A$1>1B$1>0@2$0^3^2>0@2$0^4^2@2$0^5@2$4^4^3").
Proof.
  intros S A B [HA1 HA2] [HB1 HB2]. split.
  - intros tr k fs [H|H]; [exact (HA1 _ _ _ H) | exact (HB1 _ _ _ H)].
  - intros tr s fs [H|H]; [exact (HA2 _ _ _ H) | exact (HB2 _ _ _ H)].
Qed.

(* [comment removed for export] *)

Section Bridge.
Context {SC : StepCfg}.
Variable segs : ltac2:(zQ "20!h8!jr2@1$0$1").

Theorem realizes_must_exit_in : ltac2:(zQ "h40!j7!pd!ii3!hsd!il7!im4!hic!ima!in5!h8!igb!inb!ir9!it1!itb!hq9!jhd!n9!ji9!hlf>1c$d>1T$h1>0@4$h2?4segs?2SC^2^1>1S@1$9@1$1@1$0#k0>0@2$b@3$3@1$2@1$1@1$0#k0@1$7@1$4^4@1$5@1$1@1$0#k0@2$a@1$1@1$0#k0\4code@1$1@1$0#k0@2$6@3$3@1$2@1$1@1$0#k0@1$7@1$4^5@2$8@1$1@1$0#k0^1@2$6@3$h3@1$1@1$0#k0^1^2@3$3@1$2@1$1@1$0#k0@1$e@1$4^5@1$5@1$1@1$0#k0>0@2$f^2^4@4$c@1$h0?2SC?4segs^3^6").
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros S Hc Hpin.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)).
    + exists (evs i0), (SNext (nx i0)). exact (Hcomp i0).
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Habs). discriminate Habs.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & -> & Heqc). injection Heqc as ->.
      apply (IH i S).
      * destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss)
          as [Hnone | [(evs0 & k & Hevs & Hk & Hnk) | (evs0 & sg & Hevs & Hk)]].
        -- left. exact Hnone.
        -- right. exists k. split; [exact Hk | split; [| exact Hnk]].
           apply (proj1 Hpin evs0 k (m_fs (cfg_model (nx i)))).
           exists i. left. rewrite <- Hevs. apply is_prefix_refl.
        -- exfalso. apply (proj2 Hpin evs0 sg (m_fs (cfg_model (nx i)))).
           exists i. left. rewrite <- Hevs. apply is_prefix_refl.
      * split.
        -- intros tr k fs HT. apply (proj1 Hpin (evs i ++ tr) k fs).
           exists i. right. exists (tr ++ [ExitEv k fs]). split; [symmetry; apply app_assoc | exact HT].
        -- intros tr s fs HT. apply (proj2 Hpin (evs i ++ tr) s fs).
           exists i. right. exists (tr ++ [KillEv s fs]). split; [symmetry; apply app_assoc | exact HT].
  - destruct Hc as [Hc | (code & Hc & Hin & Hk)]; [congruence |].
    exact (must_exit_in_at_cfg_halted _ _ _ _ _ Hc Hin Hk).
  - apply (IH S Hc). eapply exits_in_eq; [exact Heq | exact Hpin].
Qed.

End Bridge.

(* [comment removed for export] *)

Lemma refusal_decided_classic : ltac2:(zQ "40!jj4!jk3!jl6!jle>3cfg$0>1i$3>1m$2@3$1^3^2^1").
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
              syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H | H].
  - left. exact H.
  - right. intros eff' m' evs' Hs.
    destruct (refusal_b i m (eff_ret eff')) eqn:Hr; [reflexivity |].
    exfalso. apply H. exists eff', m', evs'. split; [exact Hs | exact Hr].
Qed.

Lemma decided_from_classic : ltac2:(zQ "50!h8!jmd!jr2!jj4!it1>3cfg$3>4segs@1$0$2>1c$4@3$1^3^2^1").
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma run_decided_classic : ltac2:(zQ "60!jrd!js1!jt0!jt9!jj4!ju6>3cfg$4>3img$2>3lim$0>2en$3>3inp$5@5$1^5^4^3^2^1").
Proof. intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn. apply decided_from_classic. Qed.

(* [comment removed for export] *)

Lemma halts_allowed_T_scfg_budgets_down : ltac2:(zQ "d0!jj4!h8!j7!jrd!kie!kkf!jt0!jt9!km5!kmf!kne!ju6!pd>4cfg1$0>4cfg2$0>3lim$3>1S@1$1@1$c@1$2#k0>3img$6>0@2$8^5^4>0>2en$7>3inp$b>0@3$9^4^2^1>0@1$a^2@6$5^9^7^6^8^4^3@4$4^7^5^4^3").
Proof.
  intros cfg1 cfg2 lim S img Hle H en inp Hen Hinp _.
  apply (must_exit_in_scfg_mono cfg1 cfg2 S img lim en inp Hle (run_decided_classic _ _ _ _ _)).
  exact (H en inp Hen Hinp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
