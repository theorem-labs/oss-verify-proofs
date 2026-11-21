(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed AA, AH, AH2 and 19 more; added Hlau, Hlaunch, Hrdr and 8 more; removed Hfit, abt, argv and 10 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanNodesWJoin AsanStartup
  PlanRegen StartupRegenAsan.
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

(** the certificates' own test of their shapes ([StartupRegenAsan.only_holes]) gives [holes_only] *)
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

Local Ltac asan_side :=
  first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_res_hull | exact asan_hull_ok
        | exact asan_shadow_ok | exact asan_hull_cov | exact asan_img_facts | exact asan_apc | exact asan_resx
        | exact (fun E M H => H) | apply le_n | eassumption ].

Section Boot.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  (** the run's WHOLE input *)
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
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

  #[local] Notation SINV := (SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation fs := (in_fs inp).

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  Hypothesis MAIN : holes_stmt ASEGS ASAN LIM (hlookup (HSL_2 RZ)) SINV argH (fun _ => H) fs.

  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a HA. exact (argH0_high Asan.M.init_pc sp rdraw inp Hsp Hva E a HA). Defined.
  Let AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS HA. exact (argH0_high2 APH Asan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau E M a HS HA). Defined.
  Let AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. reflexivity. Defined.
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf HS. exact (SINV0_frame APH Asan.M.init_pc sp rdraw brk0 mbase inp E M M' Hf HS). Defined.
  Let SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M Hag HS. exact (SINV0_agree APH Asan.M.init_pc sp rdraw brk0 mbase inp E E' M Hag HS). Defined.

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

    (* [comment removed for export] *)
    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound ASEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt ASEGS ASAN LIM HSn SINV argH HH fs ->
      check ASEGS IT ASAN nx LIM RZ (XNS ASEGS ASAN nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH fs E start R FULL model ->
        srealizes ASEGS (cfg_of ASEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      pose proof (check_sound ASEGS IT IT_ok ASAN nx Hnx LIM RZ HSn (XNS ASEGS ASAN nx LIM) XE0 XB0
                asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
                ltac:(eapply (AsanNodesMmB.node_sys_sound ASEGS ASAN nx LIM SINV argH fs); asan_side)
                ltac:(eapply (AsanNodesMmB.node_brk2_sound ASEGS ASAN nx LIM SINV argH fs); asan_side)
                ltac:(eapply (node_mmap2_sound_OBL ASEGS ASAN nx LIM SINV argH fs); asan_side)
                ltac:(eapply (node_mmapin_sound_OBL ASEGS ASAN nx LIM SINV argH fs); asan_side)
                ltac:(eapply (node_mprotect2_sound_OBL ASEGS ASAN nx LIM SINV argH fs); asan_side)
                (AsanNodesMmB.node_exit_sound ASEGS ASAN LIM SINV argH fs)
                ltac:(eapply (asan_node_x_sound_all Asan.M.init_pc sp rdraw brk0 mbase inp fs); asan_side)
                (node_join_sound ASEGS ASAN nx LIM SINV argH fs)
                ltac:(eapply (XNS_sound ASEGS ASAN nx LIM SINV argH fs); asan_side)
                (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH fs E start R FULL model ->
         srealizes ASEGS (cfg_of ASEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt ASEGS ASAN LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* a certificate's shape has only holes: its own boolean test, no shape computed here *)
  Local Ltac holes_r H := exact (holes_only_of _ (H RZ RZr)).
  (* a certificate as the check it states, its run unfolded: the goal names [check] itself, and unifying
     [run_X] with [check] may reduce the check *)
  Local Ltac cert_r C := let H := fresh "Hc" in pose proof C as H; cbv delta [run_0 run_A run_B run_C run_2] beta in H; exact H.

  (* [comment removed for export] *)
  Lemma S2_sound : holes_stmt ASEGS ASAN LIM (hlookup (HSL_C RZ)) SINV argH HH fs.
  Proof.
    apply (seg_holes (hlookup (HSL_C RZ)) 0%nat (ST_2 RZ) (one_key _ 0%nat (ST_C RZ) (keys_C RZ RZr))).
    apply (seg_sound (NX_2 RZ) (nx_2_ge RZ RZr) IT_2 IT_2_ok (hlookup (HSL_2 RZ)) FUEL BFUEL KC0 (PL_2 RZ) (ST_2 RZ) (SH_2 RZ));
      [| cert_r (cert_2 RZ RZr) | holes_r holes_2].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt ASEGS ASAN LIM (hlookup (HSL_B RZ)) SINV argH HH fs.
  Proof.
    apply (seg_holes (hlookup (HSL_B RZ)) 12%nat (ST_C RZ) (one_key _ 12%nat (ST_B RZ) (keys_B RZ RZr))).
    apply (seg_sound (NX_C RZ) (nx_C_ge RZ RZr) IT_C IT_C_ok (hlookup (HSL_C RZ)) FUEL BFUEL KC0 (PL_C RZ) (ST_C RZ) (SH_C RZ));
      [exact S2_sound | cert_r (cert_C RZ RZr) | holes_r holes_C].
  Qed.
  Lemma C_sound : holes_stmt ASEGS ASAN LIM (hlookup (HSL_A RZ)) SINV argH HH fs.
  Proof.
    apply (seg_holes (hlookup (HSL_A RZ)) 11%nat (ST_B RZ) (one_key _ 11%nat (ST_A RZ) (keys_A RZ RZr))).
    apply (seg_sound (NX_B RZ) (nx_B_ge RZ RZr) IT_B IT_B_ok (hlookup (HSL_B RZ)) FUEL BFUEL KC0 (PL_B RZ) (ST_B RZ) (SH_B RZ));
      [exact D_sound | cert_r (cert_B RZ RZr) | holes_r holes_B].
  Qed.
  Lemma B_sound : holes_stmt ASEGS ASAN LIM (hlookup (HSL_0 RZ)) SINV argH HH fs.
  Proof.
    apply (seg_holes (hlookup (HSL_0 RZ)) 10%nat (ST_A RZ) (one_key _ 10%nat (ST_0 RZ) (keys_0 RZ RZr))).
    apply (seg_sound (NX_A RZ) (nx_A_ge RZ RZr) IT_A IT_A_ok (hlookup (HSL_A RZ)) FUEL BFUEL KC0 (PL_A RZ) (ST_A RZ) (SH_A RZ));
      [exact C_sound | cert_r (cert_A RZ RZr) | holes_r holes_A].
  Qed.

  (* [comment removed for export] *)
  Theorem asan_boot_shape :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM inp)
              (sd HH t_nil E0a fs (SH_0 RZ)).
  Proof.
    pose proof (cert_0 RZ RZr) as C0. cbv delta [run_0 ST_0 NX_0] beta in C0.
    exact (asan_startup sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hlaunch Hrdr Hlau Hhw
             IT_0 IT_0_ok (hlookup (HSL_0 RZ)) (PL_0 RZ) (SH_0 RZ) KC0 BFUEL FUEL C0 HH HH_agree HH_nil B_sound).
  Qed.

  (* [comment removed for export] *)
  Theorem asan_boot :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM inp) (H E0a fs).
  Proof. eapply srz_conseq; [exact asan_boot_shape | apply sd_allH; holes_r holes_0]. Qed.
End Boot.
