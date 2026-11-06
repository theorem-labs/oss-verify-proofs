(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct Asanoq0 AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Bothny9 AsanInit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb Bothy0u Bothmmq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothjqf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Starazj Bothjqf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Both6eh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Both6eh Starr0h Stargqr Bothg0u Both56i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanoq0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothy0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothjqf.Star1i1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starazj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothjqf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both6eh.Starfcw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both6eh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starr0h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Stargqr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothg0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both56i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition MAIN_PC_BOTH : Z := 0x867f8.

(* [comment removed for export] *)
Fixpoint only_holes (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SAlt2 a b => only_holes a && only_holes b
  | SCase _ _ a b => only_holes a && only_holes b
  | _ => false
  end%bool.

Lemma sd_const_holes : forall (T D : TSet) E fs s,
  T [] -> only_holes s = true -> t_eq (sd (fun _ _ _ => T) D E fs s) T.
Proof.
  intros T D E fs s HT. induction s as [| c | fd ps s IH | a IHa b IHb | e mid a IHa b IHb | h |]; intros H; cbn in H; try discriminate.
  - apply andb_prop in H as [Ha Hb]. cbn [sd]. intros tr. unfold t_alt2. split.
    + intros [X|X]; [apply (IHa Ha) | apply (IHb Hb)]; exact X.
    + intros X. left. apply (IHa Ha). exact X.
  - apply andb_prop in H as [Ha Hb]. cbn [sd]. destruct (Z.leb _ _); [exact (IHa Ha) | exact (IHb Hb)].
  - cbn [sd]. intros tr. tauto.
Qed.

Lemma startup_shape_both_only_holes : only_holes startup_shape_both = true.
Proof. reflexivity. Qed.

Lemma NX2b_ge : (NX0 <= NX2b)%nat.
Proof. unfold NX0, NX2b. lia. Qed.

(* [comment removed for export] *)
Lemma pc_HS_both_0 : pc HS_both_0 = 0x87618. Proof. reflexivity. Qed.
Lemma pc_HS_both_1 : pc HS_both_1 = 0x87618. Proof. reflexivity. Qed.
Lemma pc_HS_both2_1 : pc HS_both2_1 = MAIN_PC_BOTH. Proof. reflexivity. Qed.
Lemma pc_HS_both2_2 : pc HS_both2_2 = MAIN_PC_BOTH. Proof. reflexivity. Qed.
Lemma pc_HS_both2b_1 : pc HS_both2b_1 = MAIN_PC_BOTH. Proof. reflexivity. Qed.
Lemma pc_HS_both2b_2 : pc HS_both2b_2 = MAIN_PC_BOTH. Proof. reflexivity. Qed.

Section Main.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid nofile sigmask hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variable urandom : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 BPH sp rdraw brk0 argv envp uid hw).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation LIM := (@AsanInit.blim BL).
  (* [comment removed for export] *)
  Hypothesis CERT0 : check BSEGS IT0b BOTH NX0 LIM (XNb2 NX0) XE0 XB0 HS_both KC0b BFUELb FUELb None both_init startup_plan_both = COk startup_shape_both.
  Hypothesis CERT2 : check BSEGS IT2b BOTH NX2b LIM (XNb2 NX2b) XE0 XB0 HS_both2 KC2b BFUEL2b FUEL2b None HS_both_0 startup_plan_both2 = COk startup_shape_both2.
  Hypothesis CERT2B : check BSEGS IT2b BOTH NX2b LIM (XNb2 NX2b) XE0 XB0 HS_both2b KC2b BFUEL2b FUEL2b None HS_both_1 startup_plan_both2b = COk startup_shape_both2.

  (* [comment removed for export] *)
  Variable MAIN : TSet.
  Hypothesis MAIN_nil : MAIN [].
  Hypothesis MAIN1_sound : forall E R FULL model,
    cs_ok BSEGS BOTH LIM SINV argH fs E HS_both2_1 R FULL model -> srealizes BSEGS (cfg_of BSEGS R MAIN_PC_BOTH FULL model) MAIN.
  Hypothesis MAIN2_sound : forall E R FULL model,
    cs_ok BSEGS BOTH LIM SINV argH fs E HS_both2_2 R FULL model -> srealizes BSEGS (cfg_of BSEGS R MAIN_PC_BOTH FULL model) MAIN.
  Hypothesis MAIN3_sound : forall E R FULL model,
    cs_ok BSEGS BOTH LIM SINV argH fs E HS_both2b_1 R FULL model -> srealizes BSEGS (cfg_of BSEGS R MAIN_PC_BOTH FULL model) MAIN.
  Hypothesis MAIN4_sound : forall E R FULL model,
    cs_ok BSEGS BOTH LIM SINV argH fs E HS_both2b_2 R FULL model -> srealizes BSEGS (cfg_of BSEGS R MAIN_PC_BOTH FULL model) MAIN.

  (* [comment removed for export] *)
  Definition MAINH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := MAIN.
  Lemma MAINH_agree : forall n h E E' fs', env_agree n E E' -> MAINH h E fs' = MAINH h E' fs'.
  Proof. reflexivity. Qed.
  Lemma MAINH_nil : forall h E fs', MAINH h E fs' [].
  Proof. intros; exact MAIN_nil. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mainh_some_inj : forall (A : Type) (x y : A), Some x = Some y -> x = y.
  Proof. intros A x y H. exact (f_equal (fun o : option A => match o with Some v => v | None => x end) H). Qed.
  Lemma MAINH_sound2 : holes_stmt BSEGS BOTH LIM HS_both2 SINV argH MAINH fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    destruct h as [|[|[|h]]]; cbn [HS_both2] in Hh; try discriminate Hh; apply mainh_some_inj in Hh; subst ch.
    - rewrite pc_HS_both2_1. exact (MAIN1_sound E R FULL model HC).
    - rewrite pc_HS_both2_2. exact (MAIN2_sound E R FULL model HC).
  Qed.
  Lemma MAINH_sound2b : holes_stmt BSEGS BOTH LIM HS_both2b SINV argH MAINH fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    destruct h as [|[|[|h]]]; cbn [HS_both2b] in Hh; try discriminate Hh; apply mainh_some_inj in Hh; subst ch.
    - rewrite pc_HS_both2b_1. exact (MAIN3_sound E R FULL model HC).
    - rewrite pc_HS_both2b_2. exact (MAIN4_sound E R FULL model HC).
  Qed.

  Lemma sd_shape2 : forall E fs', t_eq (sd MAINH t_nil E fs' startup_shape_both2) MAIN.
  Proof. intros E fs'. cbn [sd startup_shape_both2 MAINH]. destruct (Z.leb _ _); apply t_eq_refl. Qed.

  Theorem seg2_sound : forall E R FULL model,
    cs_ok BSEGS BOTH LIM SINV argH fs E HS_both_0 R FULL model ->
    srealizes BSEGS (cfg_of BSEGS R 0x87618 FULL model) MAIN.
  Proof.
    intros E R FULL model HC.
    eapply srz_conseq; [| apply sd_shape2].
    rewrite <- pc_HS_both_0.
    exact (both_check_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NX2b NX2b_ge IT2b IT2b_ok HS_both2
             MAINH (MAINH_agree NX2b) MAINH_nil MAINH_sound2 KC2b BFUEL2b FUEL2b startup_plan_both2 HS_both_0 startup_shape_both2 CERT2
             E R FULL model HC).
  Qed.

  Theorem seg2b_sound : forall E R FULL model,
    cs_ok BSEGS BOTH LIM SINV argH fs E HS_both_1 R FULL model ->
    srealizes BSEGS (cfg_of BSEGS R 0x87618 FULL model) MAIN.
  Proof.
    intros E R FULL model HC.
    eapply srz_conseq; [| apply sd_shape2].
    rewrite <- pc_HS_both_1.
    exact (both_check_sound sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit NX2b NX2b_ge IT2b IT2b_ok HS_both2b
             MAINH (MAINH_agree NX2b) MAINH_nil MAINH_sound2b KC2b BFUEL2b FUEL2b startup_plan_both2b HS_both_1 startup_shape_both2 CERT2B
             E R FULL model HC).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma MAINH_sound1 : holes_stmt BSEGS BOTH LIM HS_both SINV argH MAINH fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    destruct h as [|[|h]]; cbn [HS_both] in Hh; try discriminate Hh; apply mainh_some_inj in Hh; subst ch.
    - rewrite pc_HS_both_0. exact (seg2_sound E R FULL model HC).
    - rewrite pc_HS_both_1. exact (seg2b_sound E R FULL model HC).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem both_startup_main : forall apc : N, Z.of_N apc = a_entry BOTH ->
    srealizes BSEGS (init_config BSEGS apc BPH sp brk0 mbase rdraw LIM (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom))
              MAIN.
  Proof.
    intros apc Hapc.
    eapply srz_conseq.
    - exact (both_startup sp rdraw brk0 mbase argv envp fs stdin uid gid nofile sigmask hw groups net urandom Hsp Hbrk Hva Hve Hfit Huid Hhw
               IT0b IT0b_ok HS_both MAINH (MAINH_agree NX0) MAINH_nil MAINH_sound1 KC0b BFUELb FUELb startup_plan_both startup_shape_both
               CERT0 apc Hapc).
    - apply (sd_const_holes MAIN t_nil E0a fs startup_shape_both MAIN_nil startup_shape_both_only_holes).
  Qed.

  Lemma both_entry_pc : Z.of_N AsanUbsan.M.init_pc = a_entry BOTH.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
End Main.
