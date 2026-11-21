(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the hook table is one per CONFIG_RSEQ layout, read with the table the start-up is checked under (INFO_BOTH_at), and start_hooks_ok takes AsanInit's full launch. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanFO
  BothAsanPlanImages AsanInit SpinAlgCfg AsanPlanSoundCfg AsanNodesNRCfg DepotNodeBoth DepotNodeSoundBoth.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache.

#[local] Abbreviation LIM := AsanInit.LIMIT.
#[local] Abbreviation FPS0 := (@eq PropExec.FPState PropExec.fx0).

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id XDP.DEPOT_INTRO_ID then XDP.xn_intro ASEGS args cs
  else if Nat.eqb id GHOSTAS_ID then xn_ghostas NX0 LIM args cs else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

(* [comment removed for export] *)
Lemma xn_ghostas_cfg {r : Z} : forall (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) FS0 FPS,
  (forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a) ->
  (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) -> nx0_sp_ok NX0 ->
  forall args, APSC.node1_stmt_cfg ASEGS (INFO_BOTH_at r) NX0 LIM SINV argH FS0 FPS APS.always (xn_ghostas NX0 LIM args).
Proof.
  intros SINV argH FS0 FPS Hagree Hsagree Hsp args. apply APSC.node1_of_fp. intros FP _.
  intros cs cs' E R FULL model T HC _ Hn Hk.
  unfold xn_ghostas in Hn.
  (* [comment removed for export] *)
  destruct args as [|b [|n [|gb [|gn [|elo [|ehi [|? ?]]]]]]]; try discriminate Hn;
    (destruct elo as [lo| | | | | | |]; try discriminate Hn); (destruct ehi as [hi| | | | | | |]; try discriminate Hn).
  destruct (APS.ghostas_sound ASEGS (INFO_BOTH_at r) NX0 LIM (fun _ => None) (fun _ _ _ => None) XE0 XB0 asan_shadow_ok SINV argH
              Hagree Hsagree Hsp FS0 0%nat E cs R FULL model b n gb gn lo hi cs' HC Hn) as (E' & Hag & HC' & Hpc).
  rewrite <- Hpc. exact (Hk E' R FULL model Hag HC' eq_refl).
Qed.

(* [comment removed for export] *)
Lemma XN0_cfg {r : Z} : forall (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) FS0 FPS,
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) -> nx0_sp_ok NX0 ->
  APSC.ext_stmt_cfg ASEGS (INFO_BOTH_at r) NX0 LIM XN0 SINV argH FS0 FPS.
Proof.
  intros SINV argH FS0 FPS Hhigh Hagree Hframe Hsagree Hsp id args. unfold XN0.
  destruct (Nat.eqb id XDP.DEPOT_INTRO_ID).
  - eapply (xn_intro_sound_cfg (INFO_BOTH_at r)); first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok | eassumption ].
  - destruct (Nat.eqb id GHOSTAS_ID).
    + apply xn_ghostas_cfg; assumption.
    + intros FP _ cs cs' E R FULL model T _ _ H _. discriminate H.
Qed.
Lemma XE0_cfg : forall SEGS A nx0 LIMIT SINV argH FS0 FPS, APSC.emit_stmt_cfg SEGS A nx0 LIMIT XE0 SINV argH FS0 FPS.
Proof. intros SEGS A nx0 LIMIT SINV argH FS0 FPS FP _ id args cs fd ps cs' E R FULL model T _ H _ _. discriminate H. Qed.
Lemma XB0_cfg : forall SEGS A nx0 LIMIT SINV argH FS0 FPS, APSC.ext2_stmt_cfg SEGS A nx0 LIMIT XB0 SINV argH FS0 FPS.
Proof. intros SEGS A nx0 LIMIT SINV argH FS0 FPS FP _ id args cs csa csb E R FULL model TA TB _ H _ _. discriminate H. Qed.

(* [comment removed for export] *)
(* LPS 727298f3: one hook table per CONFIG_RSEQ layout, read with the table the start-up is checked
   under. *)
Definition XNS (r : Z) : nat -> list expr -> acs -> option acs := XN_nr ASEGS (INFO_BOTH_at r) LIM XN0.

(* [comment removed for export] *)
Definition start_hooks_ok (XNs : Z -> nat -> list expr -> acs -> option acs) : Prop :=
  forall apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default : bool),
    valid_sp sp -> valid_argv argv -> valid_envp envp ->
    (* see the note in StartHooks.v's twin: [argH0_sp] and friends are AsanInit Section lemmas,
       so their discharged signature is that Section's whole Hypothesis list in order, which
       includes [Hfit] (AsanInit.v:264) and [Hlaunch] (:281).  Supplied by the only consumer,
       InfoBothTop.v, from [valid_entry]'s own conjuncts, [kb_rseq] left FREE. *)
    entry_stack_fits sp argv envp ->
    (* see [AsanInit.pinned_kernel]: [recorded_kernel]'s eight fields; CONFIG_RSEQ free *)
    in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))
      = pinned_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))) ->
    valid_launch (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)) ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)) ->
    APSC.ext_stmt_cfg ASEGS (INFO_BOTH_at (rseq_z (kb_rseq kern))) NX0 LIM (XNs (rseq_z (kb_rseq kern))) (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))
      (argH0 sp rdraw argv envp kern execfn) fs FPS0.

Lemma XNS_ok : start_hooks_ok XNS.
Proof.
  intros apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sigpipe_default Hsp Hva Hve Hfit Hkernel Hlaunch Hlau.
  refine (XN_nr_cfg_OBL ASEGS (INFO_BOTH_at (rseq_z (kb_rseq kern))) NX0 LIM (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)) (argH0 sp rdraw argv envp kern execfn)
            fs FPS0 XN0 asan_wx asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok
            _ _ _ _ _ asan_res_cover NX0_sp0
            (XN0_cfg _ _ fs FPS0 _ _ _ _ NX0_sp0));
    (* NINE goals -- see the note in StartHooks.v's twin.  Five from XN_nr_cfg_OBL's
       underscores and FOUR more from the nested XN0_cfg (:47-50 here), which repeats
       argH_high, argH_agree, SINV_frame and SINV_agree.  5 + 4 = 9, read from both
       signatures. *)
    [ intros E a H; eapply argH0_high; eassumption
    | intros E E' a H; reflexivity
    | intros E M M' Hf HS; eapply SINV0_frame; eassumption
    | intros E E' M Hag HS; eapply SINV0_agree; eassumption
    | (* with [Hfit]/[Hlaunch] in context this is the form branches 1-4 use, so no
         argument position is hard-coded -- see StartHooks.v's twin. *)
      intros E M a HS Ha; eapply argH0_sp; first [eassumption | reflexivity]
    | intros E a H; eapply argH0_high; eassumption
    | intros E E' a H; reflexivity
    | intros E M M' Hf HS; eapply SINV0_frame; eassumption
    | intros E E' M Hag HS; eapply SINV0_agree; eassumption ].
Qed.

