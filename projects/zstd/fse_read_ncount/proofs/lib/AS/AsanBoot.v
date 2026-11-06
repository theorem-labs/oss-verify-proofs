(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.zstd.fse_read_ncount.images Require Import Asan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import
PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit
AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanNodesWJoin AsanStartup
StartupPlanAsan StartupHSAsan
StartupPlan2Asan StartupHS2Asan AsanCertDefs.
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
Section Boot.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variables uid gid : word.
Variable hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nof sigm : word.
Variable abt : bool.
Variable urnd : InputStream.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
#[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
#[local] Notation E0a := (AsanInit.E0 APH sp rdraw brk0 argv envp uid hw).
Variable LIM : Z.
Hypothesis HLIM : source_alloc_limit <= LIM.
#[local] Notation CERT_A_T := (check ASEGS IT0 ASAN NX0 LIM (XNS ASEGS ASAN NX0 LIM) XE0 XB0 HS_asanA KC0 BFUEL FUEL None asan_init startup_plan = COk startup_shape).
#[local] Notation CERT_B_T := (check ASEGS ITB ASAN NXB LIM (XNS ASEGS ASAN NXB LIM) XE0 XB0 HS_asanB KC0 BFUEL FUEL None HS_asanA_10 startup_plan_segA = COk startup_shapeB).
#[local] Notation CERT_C_T := (check ASEGS ITC ASAN NXC LIM (XNS ASEGS ASAN NXC LIM) XE0 XB0 HS_asanC KC0 BFUEL FUEL None HS_asanB_11 startup_plan_segB = COk startup_shapeC).
#[local] Notation CERT_D_T := (check ASEGS ITD ASAN NXD LIM (XNS ASEGS ASAN NXD LIM) XE0 XB0 HS_asanD KC0 BFUEL FUEL None HS_asanC_12 startup_plan_segC = COk startup_shapeD).
#[local] Notation CERT_2_T := (check ASEGS IT2 ASAN NXS2 LIM (XNS ASEGS ASAN NXS2 LIM) XE0 XB0 HS_asan2 KC0 BFUEL FUEL None HS_asanD_0 startup2_plan = COk startup2_shape).
Variable H : env -> Fs.Fs -> TSet.
Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
Hypothesis H_nil : forall E fs', H E fs' [].
Hypothesis MAIN : holes_stmt ASEGS ASAN LIM HS_asan2 SINV argH (fun _ => H) fs.
Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
Let AH2 := argH0_high2 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
Let AA := argH0_agree APH sp rdraw argv envp uid hw.
Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.
Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
#[using="H_agree"] Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
Proof. intros. unfold HH. apply H_agree. assumption. Qed.
#[using="H_nil"] Lemma HH_nil : forall h E fs', HH h E fs' [].
Proof. intros. unfold HH. apply H_nil. Qed.
#[using="H_nil"] Lemma sd_allH : forall E fs' s, holes_only s = true -> t_eq (sd HH t_nil E fs' s) (H E fs').
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
#[using="Hnx"] Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).
#[using="Hsp Hva Hve Hfit H_agree H_nil AH AH2 AA SF SA Hnx AAn SAn"] Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound ASEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
(p : plan) (start : acs) (shp : shape),
holes_stmt ASEGS ASAN LIM HSn SINV argH HH fs ->
check ASEGS IT ASAN nx LIM (XNS ASEGS ASAN nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
holes_only shp = true ->
forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH fs E start R FULL model ->
srealizes ASEGS (cfg_of ASEGS R (pc start) FULL model) (H E (m_fs model)).
Proof.
intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
pose proof (check_sound ASEGS IT IT_ok ASAN nx Hnx LIM HSn (XNS ASEGS ASAN nx LIM) XE0 XB0
asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AAn SF SAn
HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
(AsanNodesMmB.node_sys_sound ASEGS ASAN nx LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AAn SF SAn)
(AsanNodesMmB.node_brk2_sound ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
(node_mmap2_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
(node_mmapin_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
(node_mprotect2_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
(AsanNodesMmB.node_exit_sound ASEGS ASAN LIM SINV argH fs)
(asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M HH0 => HH0) SF nx Hnx SAn LIM)
(node_join_sound ASEGS ASAN nx LIM SINV argH fs)
(XNS_sound ASEGS ASAN nx LIM SINV argH fs AAn SAn asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
HSOUND FUEL BFUEL None p start shp CERT
E R FULL model t_nil HC I eq_refl) as R0.
eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
Qed.
#[using="Type"] Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
(forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
(forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH fs E start R FULL model ->
srealizes ASEGS (cfg_of ASEGS R (pc start) FULL model) (H E (m_fs model))) ->
holes_stmt ASEGS ASAN LIM HSp SINV argH HH fs.
Proof.
intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
Qed.
End Seg.
#[using="Hsp Hva Hve Hfit H_agree H_nil MAIN AH AH2 AA SF SA"] Lemma S2_sound : CERT_2_T -> holes_stmt ASEGS ASAN LIM HS_asanD SINV argH HH fs.
Proof.
intros CERT_2.
apply (seg_holes HS_asanD 0%nat HS_asanD_0); [intros [|h] ch Hh; cbn in Hh; [injection Hh as <-; split; reflexivity | discriminate Hh]|].
apply (seg_sound NXS2 NXS2_ge IT2 IT2_ok HS_asan2 FUEL BFUEL KC0 startup2_plan HS_asanD_0 startup2_shape); [| exact CERT_2 | reflexivity].
intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
Qed.
#[using="Hsp Hva Hve Hfit H_agree H_nil MAIN AH AH2 AA SF SA"] Lemma D_sound : CERT_D_T -> CERT_2_T -> holes_stmt ASEGS ASAN LIM HS_asanC SINV argH HH fs.
Proof.
intros CERT_D CERT_2.
apply (seg_holes HS_asanC 12%nat HS_asanC_12).
{ intros h ch Hh. unfold HS_asanC in Hh. do 12 (destruct h as [|h]; [discriminate Hh|]).
destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
apply (seg_sound NXD NXD_ge ITD ITD_ok HS_asanD FUEL BFUEL KC0 startup_plan_segC HS_asanC_12 startup_shapeD); [exact (S2_sound CERT_2) | exact CERT_D | reflexivity].
Qed.
#[using="Hsp Hva Hve Hfit H_agree H_nil MAIN AH AH2 AA SF SA"] Lemma C_sound : CERT_C_T -> CERT_D_T -> CERT_2_T -> holes_stmt ASEGS ASAN LIM HS_asanB SINV argH HH fs.
Proof.
intros CERT_C CERT_D CERT_2.
apply (seg_holes HS_asanB 11%nat HS_asanB_11).
{ intros h ch Hh. unfold HS_asanB in Hh. do 11 (destruct h as [|h]; [discriminate Hh|]).
destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
apply (seg_sound NXC NXC_ge ITC ITC_ok HS_asanC FUEL BFUEL KC0 startup_plan_segB HS_asanB_11 startup_shapeC); [exact (D_sound CERT_D CERT_2) | exact CERT_C | reflexivity].
Qed.
#[using="Hsp Hva Hve Hfit H_agree H_nil MAIN AH AH2 AA SF SA"] Lemma B_sound : CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T -> holes_stmt ASEGS ASAN LIM HS_asanA SINV argH HH fs.
Proof.
intros CERT_B CERT_C CERT_D CERT_2.
apply (seg_holes HS_asanA 10%nat HS_asanA_10).
{ intros h ch Hh. unfold HS_asanA in Hh. do 10 (destruct h as [|h]; [discriminate Hh|]).
destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
apply (seg_sound NXB NXB_ge ITB ITB_ok HS_asanB FUEL BFUEL KC0 startup_plan_segA HS_asanA_10 startup_shapeB); [exact (C_sound CERT_C CERT_D CERT_2) | exact CERT_B | reflexivity].
Qed.
#[using="Hsp Hbrk Hva Hve Hfit Huid Hhw HLIM H_agree H_nil MAIN AH AH2 AA SF SA"] Theorem asan_boot_shape : CERT_A_T -> CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T ->
srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
(AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd))
(sd HH t_nil E0a fs startup_shape).
Proof.
intros CERT_A CERT_B CERT_C CERT_D CERT_2.
exact (asan_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw LIM HLIM
IT0 IT0_ok HS_asanA startup_plan startup_shape KC0 BFUEL FUEL CERT_A HH HH_agree HH_nil (B_sound CERT_B CERT_C CERT_D CERT_2)).
Qed.
#[using="Hsp Hbrk Hva Hve Hfit Huid Hhw HLIM H_agree H_nil MAIN AH AH2 AA SF SA"] Theorem asan_boot : CERT_A_T -> CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T ->
srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
(AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd))
(H E0a fs).
Proof. intros CERT_A CERT_B CERT_C CERT_D CERT_2. eapply srz_conseq; [exact (asan_boot_shape CERT_A CERT_B CERT_C CERT_D CERT_2) | apply sd_allH; reflexivity]. Qed.
End Boot.
