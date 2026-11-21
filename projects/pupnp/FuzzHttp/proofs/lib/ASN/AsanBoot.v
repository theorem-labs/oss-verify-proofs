(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's input, mmap base and entry draw; the CONFIG_RSEQ value; one start-up chain per CONFIG_RSEQ value over the certificates made again for it). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanNodesWJoin AsanStartup.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require PlanRegen.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  StartupHSAsan StartupHS2Asan AsanStartupCert AsanStartupCertB AsanStartupCertC AsanStartupCertD AsanStartupCert2.

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
Lemma ahA0 : holes_only ashA0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ahB0 : holes_only ashB0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ahC0 : holes_only ashC0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ahD0 : holes_only ashD0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ah20 : holes_only ash2_0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma anA0 : Nat.leb NX0 (nxt aSA0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma anB0 : Nat.leb NX0 (nxt aSB0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma anC0 : Nat.leb NX0 (nxt aSC0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma anD0 : Nat.leb NX0 (nxt aSD0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ahA1 : holes_only ashA1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ahB1 : holes_only ashB1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ahC1 : holes_only ashC1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ahD1 : holes_only ashD1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ah21 : holes_only ash2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma anA1 : Nat.leb NX0 (nxt aSA1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma anB1 : Nat.leb NX0 (nxt aSB1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma anC1 : Nat.leb NX0 (nxt aSC1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma anD1 : Nat.leb NX0 (nxt aSD1) = true. Proof. vm_compute. reflexivity. Qed.

(* The start-up chain from the launch to the main phase's hand-off states: each segment is a
   recorded plan checked from a state of the previous segment's hand-off map, at the run's own
   CONFIG_RSEQ flag. *)
Section Boot.

  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis HL : launch_ok ASEGS ASAN APH Asan.M.init_pc sp rdraw brk0 mbase inp.

  #[local] Notation SINV := (SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation fs := (in_fs inp).

  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].

  Let AH := argH0_high_l ASEGS ASAN APH Asan.M.init_pc sp rdraw brk0 mbase inp HL.
  Let AH2 := argH0_high2_l ASEGS ASAN APH Asan.M.init_pc sp rdraw brk0 mbase inp HL.
  Let AA := argH0_agree sp rdraw inp.
  Let SF := SINV0_frame APH Asan.M.init_pc sp rdraw brk0 mbase inp.
  Let SA := SINV0_agree_g APH Asan.M.init_pc sp rdraw brk0 mbase inp.

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
                (AsanNodesMmB.node_sys_sound ASEGS ASAN nx LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound ASEGS ASAN LIM SINV argH fs)
                (asan_node_x_sound_all Asan.M.init_pc sp rdraw brk0 mbase inp fs HL SINV (fun E M HH0 => HH0) SF nx Hnx SAn)
                (node_join_sound ASEGS ASAN nx LIM SINV argH fs)
                (XNS_sound ASEGS ASAN nx LIM SINV argH fs AAn SAn asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.
  End Seg.

  (* a segment certificate for one state of a hand-off map: some itab, variable floor and plan
     whose check from that state reaches only holes of the next map *)
  Definition seg_cert (HSout : nat -> option acs) (ch : acs) : Prop :=
    exists (IT : itab) (nx KC BFUEL FUEL : nat) (p : plan) (shp : shape),
      itab_sound ASEGS IT /\ (NX0 <= nx)%nat
      /\ check ASEGS IT ASAN nx LIM RZ (XNS ASEGS ASAN nx LIM) XE0 XB0 HSout KC BFUEL FUEL None ch p = COk shp
      /\ holes_only shp = true.

  Lemma chain_step : forall (HSin HSout : nat -> option acs),
    holes_stmt ASEGS ASAN LIM HSout SINV argH HH fs ->
    (forall h ch, HSin h = Some ch -> seg_cert HSout ch) ->
    holes_stmt ASEGS ASAN LIM HSin SINV argH HH fs.
  Proof.
    intros HSin HSout Hout Hcert h ch Hh E R FULL model HC. unfold HH.
    destruct (Hcert h ch Hh) as (IT & nx & KC & BFUEL & FUEL & p & shp & IT_ok & Hnx & CERT & Hshp).
    exact (seg_sound nx Hnx IT IT_ok HSout FUEL BFUEL KC p ch shp Hout CERT Hshp E R FULL model HC).
  Qed.

  (* the last map's states are the main phase's entry *)
  Lemma holes_of_main : forall (HS2 : nat -> option acs),
    holes_stmt ASEGS ASAN LIM HS2 SINV argH (fun _ => H) fs ->
    holes_stmt ASEGS ASAN LIM HS2 SINV argH HH fs.
  Proof. intros HS2 MAIN h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC). Qed.

  (* the first segment, from the launch's own start state *)
  Theorem boot_gen : forall (IT0 : itab) (IT0_ok : itab_sound ASEGS IT0) (HS1 : nat -> option acs)
                            (KC0 BFUEL FUEL : nat) (p : plan) (shp : shape),
    check ASEGS IT0 ASAN NX0 LIM RZ (XNS ASEGS ASAN NX0 LIM) XE0 XB0 HS1 KC0 BFUEL FUEL None (asan_init RZ) p = COk shp ->
    holes_only shp = true ->
    holes_stmt ASEGS ASAN LIM HS1 SINV argH HH fs ->
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM inp) (H E0a fs).
  Proof.
    intros IT0 IT0_ok HS1 KC0 BFUEL FUEL p shp CERT Hshp HSOUND.
    rewrite (init_cfg_eq ASEGS ASAN APH Asan.M.init_pc sp rdraw brk0 mbase inp HL).
    pose proof (init_cs_ok ASEGS ASAN APH Asan.M.init_pc sp rdraw brk0 mbase inp HL) as HC.
    exact (seg_sound NX0 (le_n NX0) IT0 IT0_ok HS1 FUEL BFUEL KC0 p (asan_init RZ) shp HSOUND CERT Hshp _ _ _ _ HC).
  Qed.

  (* one segment of the chain, generic in its data, so that nothing concrete is reduced here:
     a certificate at the run's CONFIG_RSEQ value [r] from the one state [s] of a one-state
     hand-off map *)
  Lemma chain_seg : forall (IT : itab) (r : Z) (nx : nat) (s : acs) (p : plan) (shp : shape)
                           (HSin HSout : nat -> option acs),
    itab_sound ASEGS IT -> RZ = r -> Nat.leb NX0 nx = true ->
    (forall h ch, HSin h = Some ch -> ch = s) ->
    check ASEGS IT ASAN nx LIM r (XNS ASEGS ASAN nx LIM) XE0 XB0 HSout 0%nat 400000%nat 3000%nat None s p = COk shp ->
    holes_only shp = true ->
    holes_stmt ASEGS ASAN LIM HSout SINV argH HH fs ->
    holes_stmt ASEGS ASAN LIM HSin SINV argH HH fs.
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
    itab_sound ASEGS IT -> RZ = r ->
    check ASEGS IT ASAN NX0 LIM r (XNS ASEGS ASAN NX0 LIM) XE0 XB0 HS1 0%nat 400000%nat 3000%nat None (asan_init r) p = COk shp ->
    holes_only shp = true ->
    holes_stmt ASEGS ASAN LIM HS1 SINV argH HH fs ->
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM inp) (H E0a fs).
  Proof.
    intros IT r p shp HS1 IT_ok ER CERT Hshp HS. subst r.
    exact (boot_gen IT IT_ok HS1 0 400000 3000 p shp CERT Hshp HS).
  Qed.

  (* The chain at LPS 727298f3, one per CONFIG_RSEQ value: segments A, B, C, D and 2, each
     certified ([AsanStartupCert*]) against the next segment's computed hand-off map
     ([StartupHSAsan], [StartupHS2Asan]); the main phase's entry maps [aHS2_0], [aHS2_1] are the
     caller's. *)
  Theorem asan_boot :
    (RZ = 0 -> holes_stmt ASEGS ASAN LIM aHS2_0 SINV argH (fun _ => H) fs) ->
    (RZ = 1 -> holes_stmt ASEGS ASAN LIM aHS2_1 SINV argH (fun _ => H) fs) ->
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM inp) (H E0a fs).
  Proof.
    intros M0 M1.
    assert (RZ01 : RZ = 0 \/ RZ = 1).
    { unfold rseq_z. destruct (kb_rseq (in_kernel inp)); [right|left]; reflexivity. }
    destruct RZ01 as [ERZ|ERZ].
    - exact (boot_first aIT 0 aplanA ashA0 aHSA0 aIT_ok ERZ acertA0 ahA0
                 (chain_seg aIT 0 (nxt aSA0) aSA0 aplanB ashB0 aHSA0 aHSB0 aIT_ok ERZ anA0
                 (PlanRegen.hs1_some 10 aSA0) acertB0 ahB0
                 (chain_seg aIT 0 (nxt aSB0) aSB0 aplanC ashC0 aHSB0 aHSC0 aIT_ok ERZ anB0
                 (PlanRegen.hs1_some 11 aSB0) acertC0 ahC0
                 (chain_seg aIT 0 (nxt aSC0) aSC0 aplanD ashD0 aHSC0 aHSD0 aIT_ok ERZ anC0
                 (PlanRegen.hs1_some 12 aSC0) acertD0 ahD0
                 (chain_seg aIT2 0 (nxt aSD0) aSD0 aplan2 ash2_0 aHSD0 aHS2_0 aIT2_ok ERZ anD0
                 (PlanRegen.hs1_some 0 aSD0) acert20 ah20
                 (holes_of_main aHS2_0 (M0 ERZ))))))).
    - exact (boot_first aIT 1 aplanA ashA1 aHSA1 aIT_ok ERZ acertA1 ahA1
                 (chain_seg aIT 1 (nxt aSA1) aSA1 aplanB ashB1 aHSA1 aHSB1 aIT_ok ERZ anA1
                 (PlanRegen.hs1_some 10 aSA1) acertB1 ahB1
                 (chain_seg aIT 1 (nxt aSB1) aSB1 aplanC ashC1 aHSB1 aHSC1 aIT_ok ERZ anB1
                 (PlanRegen.hs1_some 11 aSB1) acertC1 ahC1
                 (chain_seg aIT 1 (nxt aSC1) aSC1 aplanD ashD1 aHSC1 aHSD1 aIT_ok ERZ anC1
                 (PlanRegen.hs1_some 12 aSC1) acertD1 ahD1
                 (chain_seg aIT2 1 (nxt aSD1) aSD1 aplan2 ash2_1 aHSD1 aHS2_1 aIT2_ok ERZ anD1
                 (PlanRegen.hs1_some 0 aSD1) acert21 ah21
                 (holes_of_main aHS2_1 (M1 ERZ))))))).
  Qed.
End Boot.
