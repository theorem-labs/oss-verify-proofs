(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's input, mmap base and entry draw; the CONFIG_RSEQ value; one start-up chain per CONFIG_RSEQ value over the certificates made again for it). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanNodesWJoin BothStartup.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require PlanRegen.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  StartupHSBoth StartupHS2Both BothStartupCert BothStartupCertB BothStartupCertC BothStartupCertD BothStartupCert2.

Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

(* The chain's concrete side conditions, each decided by the VM in a lemma of its own, so that
   the chain below is one application whose argument types are these lemmas' types as written. *)
Lemma bhA0 : holes_only bshA0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhB0 : holes_only bshB0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhC0 : holes_only bshC0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhD0 : holes_only bshD0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bh20 : holes_only bsh2_0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bnA0 : Nat.leb NX0 (nxt bSA0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma bnB0 : Nat.leb NX0 (nxt bSB0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma bnC0 : Nat.leb NX0 (nxt bSC0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma bnD0 : Nat.leb NX0 (nxt bSD0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhA1 : holes_only bshA1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhB1 : holes_only bshB1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhC1 : holes_only bshC1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhD1 : holes_only bshD1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bh21 : holes_only bsh2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bnA1 : Nat.leb NX0 (nxt bSA1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma bnB1 : Nat.leb NX0 (nxt bSB1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma bnC1 : Nat.leb NX0 (nxt bSC1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma bnD1 : Nat.leb NX0 (nxt bSD1) = true. Proof. vm_compute. reflexivity. Qed.

(* The start-up chain from the launch to the main phase's hand-off states: each segment is a
   recorded plan checked from a state of the previous segment's hand-off map, at the run's own
   CONFIG_RSEQ flag. *)
Section Boot.

  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis HL : launch_ok BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp.

  #[local] Notation SINV := (SINV0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation fs := (in_fs inp).

  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].

  Let AH := argH0_high_l BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp HL.
  Let AH2 := argH0_high2_l BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp HL.
  Let AA := argH0_agree sp rdraw inp.
  Let SF := SINV0_frame BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp.
  Let SA := SINV0_agree_g BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp.

  Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
  Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
  Proof. intros. unfold HH. apply H_agree. assumption. Qed.
  Lemma HH_nil : forall h E fs', HH h E fs' [].
  Proof. intros. unfold HH. apply H_nil. Qed.

  Lemma sd_allH : forall E fs' s, holes_only s = true -> t_eq (sd HH t_nil E fs' s) (H E fs').
  Proof.
    assert (ID : forall X Y Z : TSet, Z [] -> t_eq X Z -> t_eq Y Z -> t_eq (t_alt2 X Y) Z).
    { intros X Y Z HZ HX HY tr. unfold t_alt2. specialize (HX tr). specialize (HY tr). tauto. }
    intros E fs' s. induction s as [| |fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros Hs; try discriminate.
    - apply andb_prop in Hs as [Ha Hb]. apply ID; [apply H_nil | exact (IHa Ha) | exact (IHb Hb)].
    - apply andb_prop in Hs as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha) | exact (IHb Hb)].
    - unfold HH. apply t_eq_refl.
  Qed.

  Section Seg.
    Variable nx : nat.
    Hypothesis Hnx : (NX0 <= nx)%nat.
    Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
    Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
    Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
      fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
    Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
      fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).

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
                (AsanNodesMmB.node_sys_sound BSEGS BOTH nx LIM SINV argH fs both_res_len both_hull_ok both_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH fs)
                (both_node_x_sound_all AsanUbsan.M.init_pc sp rdraw brk0 mbase inp fs HL SINV (fun E M HH0 => HH0) SF nx Hnx SAn)
                (node_join_sound BSEGS BOTH nx LIM SINV argH fs)
                (XNS_sound BSEGS BOTH nx LIM SINV argH fs AAn SAn both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.
  End Seg.

  (* a segment certificate for one state of a hand-off map: some itab, variable floor and plan
     whose check from that state reaches only holes of the next map *)
  Definition seg_cert (HSout : nat -> option acs) (ch : acs) : Prop :=
    exists (IT : itab) (nx KC BFUEL FUEL : nat) (p : plan) (shp : shape),
      itab_sound BSEGS IT /\ (NX0 <= nx)%nat
      /\ check BSEGS IT BOTH nx LIM RZ (XNS BSEGS BOTH nx LIM) XE0 XB0 HSout KC BFUEL FUEL None ch p = COk shp
      /\ holes_only shp = true.

  Lemma chain_step : forall (HSin HSout : nat -> option acs),
    holes_stmt BSEGS BOTH LIM HSout SINV argH HH fs ->
    (forall h ch, HSin h = Some ch -> seg_cert HSout ch) ->
    holes_stmt BSEGS BOTH LIM HSin SINV argH HH fs.
  Proof.
    intros HSin HSout Hout Hcert h ch Hh E R FULL model HC. unfold HH.
    destruct (Hcert h ch Hh) as (IT & nx & KC & BFUEL & FUEL & p & shp & IT_ok & Hnx & CERT & Hshp).
    exact (seg_sound nx Hnx IT IT_ok HSout FUEL BFUEL KC p ch shp Hout CERT Hshp E R FULL model HC).
  Qed.

  (* the last map's states are the main phase's entry *)
  Lemma holes_of_main : forall (HS2 : nat -> option acs),
    holes_stmt BSEGS BOTH LIM HS2 SINV argH (fun _ => H) fs ->
    holes_stmt BSEGS BOTH LIM HS2 SINV argH HH fs.
  Proof. intros HS2 MAIN h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC). Qed.

  (* the first segment, from the launch's own start state *)
  Theorem boot_gen : forall (IT0 : itab) (IT0_ok : itab_sound BSEGS IT0) (HS1 : nat -> option acs)
                            (KC0 BFUEL FUEL : nat) (p : plan) (shp : shape),
    check BSEGS IT0 BOTH NX0 LIM RZ (XNS BSEGS BOTH NX0 LIM) XE0 XB0 HS1 KC0 BFUEL FUEL None (both_init RZ) p = COk shp ->
    holes_only shp = true ->
    holes_stmt BSEGS BOTH LIM HS1 SINV argH HH fs ->
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM inp) (H E0a fs).
  Proof.
    intros IT0 IT0_ok HS1 KC0 BFUEL FUEL p shp CERT Hshp HSOUND.
    rewrite (init_cfg_eq BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp HL).
    pose proof (init_cs_ok BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp HL) as HC.
    exact (seg_sound NX0 (le_n NX0) IT0 IT0_ok HS1 FUEL BFUEL KC0 p (both_init RZ) shp HSOUND CERT Hshp _ _ _ _ HC).
  Qed.

  (* one segment of the chain, generic in its data, so that nothing concrete is reduced here:
     a certificate at the run's CONFIG_RSEQ value [r] from the one state [s] of a one-state
     hand-off map *)
  Lemma chain_seg : forall (IT : itab) (r : Z) (nx : nat) (s : acs) (p : plan) (shp : shape)
                           (HSin HSout : nat -> option acs),
    itab_sound BSEGS IT -> RZ = r -> Nat.leb NX0 nx = true ->
    (forall h ch, HSin h = Some ch -> ch = s) ->
    check BSEGS IT BOTH nx LIM r (XNS BSEGS BOTH nx LIM) XE0 XB0 HSout 0%nat 400000%nat 3000%nat None s p = COk shp ->
    holes_only shp = true ->
    holes_stmt BSEGS BOTH LIM HSout SINV argH HH fs ->
    holes_stmt BSEGS BOTH LIM HSin SINV argH HH fs.
  Proof.
    intros IT r nx s p shp HSin HSout IT_ok ER Hnx Hone CERT Hshp Hout.
    subst r. apply (chain_step HSin HSout Hout).
    intros h ch Hh. rewrite (Hone h ch Hh). unfold seg_cert.
    exists IT, nx, 0%nat, 400000%nat, 3000%nat, p, shp.
    split; [exact IT_ok|]. split; [apply Nat.leb_le; exact Hnx|].
    split; [exact CERT | exact Hshp].
  Qed.

  (* the first segment, from the launch's start state at the run's CONFIG_RSEQ value [r] *)
  Lemma boot_first : forall (IT : itab) (r : Z) (p : plan) (shp : shape) (HS1 : nat -> option acs),
    itab_sound BSEGS IT -> RZ = r ->
    check BSEGS IT BOTH NX0 LIM r (XNS BSEGS BOTH NX0 LIM) XE0 XB0 HS1 0%nat 400000%nat 3000%nat None (both_init r) p = COk shp ->
    holes_only shp = true ->
    holes_stmt BSEGS BOTH LIM HS1 SINV argH HH fs ->
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM inp) (H E0a fs).
  Proof.
    intros IT r p shp HS1 IT_ok ER CERT Hshp HS. subst r.
    exact (boot_gen IT IT_ok HS1 0 400000 3000 p shp CERT Hshp HS).
  Qed.

  (* The chain at LPS 727298f3, one per CONFIG_RSEQ value: segments A, B, C, D and 2, each
     certified ([BothStartupCert*]) against the next segment's computed hand-off map
     ([StartupHSBoth], [StartupHS2Both]); the main phase's entry maps [bHS2_0], [bHS2_1] are the
     caller's. *)
  Theorem both_boot :
    (RZ = 0 -> holes_stmt BSEGS BOTH LIM bHS2_0 SINV argH (fun _ => H) fs) ->
    (RZ = 1 -> holes_stmt BSEGS BOTH LIM bHS2_1 SINV argH (fun _ => H) fs) ->
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM inp) (H E0a fs).
  Proof.
    intros M0 M1.
    assert (RZ01 : RZ = 0 \/ RZ = 1).
    { unfold rseq_z. destruct (kb_rseq (in_kernel inp)); [right|left]; reflexivity. }
    destruct RZ01 as [ERZ|ERZ].
    - exact (boot_first bIT 0 bplanA bshA0 bHSA0 bIT_ok ERZ bcertA0 bhA0
                 (chain_seg bIT 0 (nxt bSA0) bSA0 bplanB bshB0 bHSA0 bHSB0 bIT_ok ERZ bnA0
                 (PlanRegen.hs1_some 10 bSA0) bcertB0 bhB0
                 (chain_seg bIT 0 (nxt bSB0) bSB0 bplanC bshC0 bHSB0 bHSC0 bIT_ok ERZ bnB0
                 (PlanRegen.hs1_some 11 bSB0) bcertC0 bhC0
                 (chain_seg bIT 0 (nxt bSC0) bSC0 bplanD bshD0 bHSC0 bHSD0 bIT_ok ERZ bnC0
                 (PlanRegen.hs1_some 12 bSC0) bcertD0 bhD0
                 (chain_seg bIT2 0 (nxt bSD0) bSD0 bplan2 bsh2_0 bHSD0 bHS2_0 bIT2_ok ERZ bnD0
                 (PlanRegen.hs1_some 0 bSD0) bcert20 bh20
                 (holes_of_main bHS2_0 (M0 ERZ))))))).
    - exact (boot_first bIT 1 bplanA bshA1 bHSA1 bIT_ok ERZ bcertA1 bhA1
                 (chain_seg bIT 1 (nxt bSA1) bSA1 bplanB bshB1 bHSA1 bHSB1 bIT_ok ERZ bnA1
                 (PlanRegen.hs1_some 10 bSA1) bcertB1 bhB1
                 (chain_seg bIT 1 (nxt bSB1) bSB1 bplanC bshC1 bHSB1 bHSC1 bIT_ok ERZ bnB1
                 (PlanRegen.hs1_some 11 bSB1) bcertC1 bhC1
                 (chain_seg bIT 1 (nxt bSC1) bSC1 bplanD bshD1 bHSC1 bHSD1 bIT_ok ERZ bnC1
                 (PlanRegen.hs1_some 12 bSC1) bcertD1 bhD1
                 (chain_seg bIT2 1 (nxt bSD1) bSD1 bplan2 bsh2_1 bHSD1 bHS2_1 bIT2_ok ERZ bnD1
                 (PlanRegen.hs1_some 0 bSD1) bcert21 bh21
                 (holes_of_main bHS2_1 (M1 ERZ))))))).
  Qed.
End Boot.
