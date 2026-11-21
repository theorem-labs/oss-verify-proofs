(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the boot is stated over the run's whole launch input with its CONFIG_RSEQ value free, and chains the start-up certificates the build computes (StartupRegenBoth) from the launch's start state to the main-entry hand-offs; taken in part from projects/simdjson/fuzz_utf8/proofs/lib/AS/BothBoot.v, 62 lines within its lines 17-200. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_minifyimpl.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanNodesWJoin BothStartup
  PlanRegen StartupRegenBoth.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* A certificate is stated over its wrapper ([run_0] .. [run_2], each one [check] call) and is used
   where [check] itself is named: the wrapper is unfolded first (explicitly, and as the conversion
   order of the kernel), so that [check] is never reduced at a free CONFIG_RSEQ value
   (fuzz_parser's AsanBoot form). *)
Local Strategy expand [run_0 run_A run_B run_C run_2].

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

(** the certificates' own test of their shapes ([StartupRegenBoth.only_holes]) gives [holes_only] *)
Lemma holes_only_of : forall s, only_holes s = true -> holes_only s = true.
Proof.
  induction s as [| |fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [only_holes holes_only]; intros Hs;
    try discriminate Hs; try reflexivity;
    apply andb_prop in Hs as [Ha Hb]; rewrite (IHa Ha), (IHb Hb); reflexivity.
Qed.

(** a computed hand-off table with one key holds one state, the one [hstate] reads *)
Lemma one_key : forall (L : list (nat * acs)) (h0 : nat) (d : acs), map fst L = [h0] ->
  forall h ch, hlookup L h = Some ch -> h = h0 /\ ch = hstate L d h0.
Proof.
  intros L h0 d HL h ch Hh. destruct L as [|[h1 a] [|q L']]; cbn in HL; try discriminate.
  injection HL as <-. cbn in Hh. unfold hstate. cbn. rewrite Nat.eqb_refl.
  destruct (Nat.eqb h h1) eqn:E; [|discriminate]. apply Nat.eqb_eq in E. injection Hh as <-. split; [exact E | reflexivity].
Qed.

Local Ltac both_side :=
  first [ exact both_wx | exact both_in_hull | exact both_res_len | exact both_res_hull | exact both_hull_ok
        | exact both_shadow_ok | exact both_hull_cov | exact both_img_facts | exact both_apc | exact AsanInit.LIMIT_ge33
        | exact (fun E M H => H) | apply le_n | eassumption ].

Section Boot.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  (** the run's WHOLE input *)
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).

  (** the run's CONFIG_RSEQ flag as the plan's 0 or 1: every certificate is proved at both *)
  Let RZ : Z := rseq_z (kb_rseq (in_kernel inp)).
  Let RZr : 0 <= RZ <= 1 := rseq_z_range _.

  #[local] Notation SINV := (SINV0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation fs := (in_fs inp).

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  Hypothesis MAIN : holes_stmt BSEGS BOTH LIM (hlookup (HSL_2 RZ)) SINV argH (fun _ => H) fs.

  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a HA. exact (argH0_high AsanUbsan.M.init_pc sp rdraw inp Hsp Hva E a HA). Defined.
  Let AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS HA. exact (argH0_high2 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau E M a HS HA). Defined.
  Let AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. reflexivity. Defined.
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf HS. exact (SINV0_frame BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp E M M' Hf HS). Defined.
  Let SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M Hag HS. exact (SINV0_agree BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp E E' M Hag HS). Defined.

  (* [comment removed for export] *)
  Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
  Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
  Proof. intros. unfold HH. apply H_agree. assumption. Qed.
  Lemma HH_nil : forall h E fs', HH h E fs' [].
  Proof. intros. unfold HH. apply H_nil. Qed.

  (* [comment removed for export] *)
  Lemma sd_allH : forall E fs' s, holes_only s = true -> t_eq (sd HH t_nil E fs' s) (H E fs').
  Proof.
    assert (ID : forall X Y Z : TSet, Z [] -> t_eq X Z -> t_eq Y Z -> t_eq (t_alt2 X Y) Z).
    { intros X Y Z HZ HX HY tr. unfold t_alt2. specialize (HX tr). specialize (HY tr). tauto. }
    intros E fs' s. induction s as [| |fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros Hs; try discriminate.
    - apply andb_prop in Hs as [Ha Hb]. apply ID; [apply H_nil | exact (IHa Ha) | exact (IHb Hb)].
    - apply andb_prop in Hs as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha) | exact (IHb Hb)].
    - unfold HH. apply t_eq_refl.
  Qed.

  (* [comment removed for export] *)
  Section Seg.
    Variable nx : nat.
    Hypothesis Hnx : (NX0 <= nx)%nat.
    Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
    Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
    Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
      fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
    Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
      fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).

    (* the extension nodes' soundness at [nx], closed as AS/BothStartup.v closes it at [NX0]: the
       launch's own hypotheses by [eassumption], never an image lemma tried against a goal that still
       holds the lemma's free [brk0]/[mbase]/[apc] (fuzz_parser's AsanBoot form) *)
    Lemma xall_nx : forall x, x_stmt BSEGS BOTH nx LIM RZ SINV argH fs x.
    Proof.
      intros x. eapply both_node_x_sound_all;
        first [ exact (fun E M H0 => H0) | exact SF | exact SAn | exact Hnx | eassumption
              | exact both_img_facts | exact both_apc ].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound BSEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt BSEGS BOTH LIM HSn SINV argH HH fs ->
      check BSEGS IT BOTH nx LIM RZ (XNS BSEGS BOTH nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
        srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      pose proof (check_sound BSEGS IT IT_ok BOTH nx Hnx LIM RZ HSn (XNS BSEGS BOTH nx LIM) XE0 XB0
                both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
                ltac:(eapply (AsanNodesMmB.node_sys_sound BSEGS BOTH nx LIM SINV argH fs); both_side)
                ltac:(eapply (AsanNodesMmB.node_brk2_sound BSEGS BOTH nx LIM SINV argH fs); both_side)
                ltac:(eapply (node_mmap2_sound_OBL BSEGS BOTH nx LIM SINV argH fs); both_side)
                ltac:(eapply (node_mmapin_sound_OBL BSEGS BOTH nx LIM SINV argH fs); both_side)
                ltac:(eapply (node_mprotect2_sound_OBL BSEGS BOTH nx LIM SINV argH fs); both_side)
                (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH fs)
                xall_nx
                (node_join_sound BSEGS BOTH nx LIM SINV argH fs)
                ltac:(eapply (XNS_sound BSEGS BOTH nx LIM SINV argH fs); both_side)
                (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
         srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt BSEGS BOTH LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* a certificate as the check it states, its run unfolded: the goal names [check] itself, and
     unifying [run_X] with [check] may reduce the check (fuzz_utf8's BothBoot form) *)
  Local Ltac cert_r C := let H := fresh "Hc" in pose proof C as H; cbv delta [run_0 run_A run_B run_C run_2] beta in H; exact H.

  (* [comment removed for export] *)
  Lemma S2_sound : holes_stmt BSEGS BOTH LIM (hlookup (HSL_C RZ)) SINV argH HH fs.
  Proof.
    apply (seg_holes (hlookup (HSL_C RZ)) 0%nat (ST_2 RZ) (one_key _ 0%nat (ST_C RZ) (keys_C RZ RZr))).
    apply (seg_sound (NX_2 RZ) (nx_2_ge RZ RZr) IT_2 IT_2_ok (hlookup (HSL_2 RZ)) FUEL BFUEL KC0 (PL_2 RZ) (ST_2 RZ) (SH_2 RZ));
      [| cert_r (cert_2 RZ RZr) | exact (holes_only_of _ (holes_2 RZ RZr))].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt BSEGS BOTH LIM (hlookup (HSL_B RZ)) SINV argH HH fs.
  Proof.
    apply (seg_holes (hlookup (HSL_B RZ)) 12%nat (ST_C RZ) (one_key _ 12%nat (ST_B RZ) (keys_B RZ RZr))).
    apply (seg_sound (NX_C RZ) (nx_C_ge RZ RZr) IT_C IT_C_ok (hlookup (HSL_C RZ)) FUEL BFUEL KC0 (PL_C RZ) (ST_C RZ) (SH_C RZ));
      [exact S2_sound | cert_r (cert_C RZ RZr) | exact (holes_only_of _ (holes_C RZ RZr))].
  Qed.
  Lemma C_sound : holes_stmt BSEGS BOTH LIM (hlookup (HSL_A RZ)) SINV argH HH fs.
  Proof.
    apply (seg_holes (hlookup (HSL_A RZ)) 11%nat (ST_B RZ) (one_key _ 11%nat (ST_A RZ) (keys_A RZ RZr))).
    apply (seg_sound (NX_B RZ) (nx_B_ge RZ RZr) IT_B IT_B_ok (hlookup (HSL_B RZ)) FUEL BFUEL KC0 (PL_B RZ) (ST_B RZ) (SH_B RZ));
      [exact D_sound | cert_r (cert_B RZ RZr) | exact (holes_only_of _ (holes_B RZ RZr))].
  Qed.
  Lemma B_sound : holes_stmt BSEGS BOTH LIM (hlookup (HSL_0 RZ)) SINV argH HH fs.
  Proof.
    apply (seg_holes (hlookup (HSL_0 RZ)) 10%nat (ST_A RZ) (one_key _ 10%nat (ST_0 RZ) (keys_0 RZ RZr))).
    apply (seg_sound (NX_A RZ) (nx_A_ge RZ RZr) IT_A IT_A_ok (hlookup (HSL_A RZ)) FUEL BFUEL KC0 (PL_A RZ) (ST_A RZ) (SH_A RZ));
      [exact C_sound | cert_r (cert_A RZ RZr) | exact (holes_only_of _ (holes_A RZ RZr))].
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot_shape :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM inp)
              (sd HH t_nil E0a fs (SH_0 RZ)).
  Proof.
    pose proof (cert_0 RZ RZr) as C0. unfold run_0, ST_0, NX_0 in C0.
    eapply (both_startup sp rdraw brk0 mbase inp);
      first [ exact C0 | exact B_sound | exact HH_agree | exact HH_nil | exact IT_0_ok
            | exact AsanInit.LIMIT_ge33 | eassumption ].
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM inp) (H E0a fs).
  Proof. eapply srz_conseq; [exact both_boot_shape | apply sd_allH; exact (holes_only_of _ (holes_0 RZ RZr))]. Qed.
End Boot.
