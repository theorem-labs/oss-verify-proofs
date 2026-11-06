(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanCeil.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache.
From Stdlib Require Import Zify.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.  (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                                | Zify.zify; xlia zchecker ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition V_HW : nat := 9.
(* [comment removed for export] *)
Definition NX_HW : nat := 10.

(* [comment removed for export] *)
Definition STK_HW_TOP : Z := 2 ^ 47 + 8388608.
Definition STK_HW_HI : Z := 0x80801000.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stklen : expr := esub (ELit STK_HW_TOP) e_pd.
(* [comment removed for export] *)
Definition STK_HW_HI0 : Z := 0x80800000.       (* [comment removed for export] *)
Definition e_stklen0 : expr := esub (ELit STK_HW_TOP) e_sp0.

Definition init_vis_hw (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (eaddz e_pd STK_OFF, e_stklen); (eaddz e_sp0 STK_OFF, e_stklen0)].

(* [comment removed for export] *)
Definition init_kn_hw (A : atable) : list kentry := auxw 3 16 (EVar V_HW) ++ init_kn A.

Definition init_acs_hw (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs (init_kn_hw A) NX_HW) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis_hw A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost STK_HW_HI + vis_cost STK_HW_HI0) (escale 4096 (EVar V_BRK)) FdStd false.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kn_vars_lt_init_kn : forall A, AP.kn_vars_lt NX0 (init_kn A) = true.
Proof. intros A. cbv [init_kn init_kn_with app kn_vars_lt]. cbn. reflexivity. Qed.   (* [comment removed for export] *)

Lemma sr_vars_lt_init_regs : AP.sr_vars_lt NX0 init_regs = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kword_reenv : forall segs E E' M b k w v v',
  edenot E b = edenot E' b -> edenot E v = edenot E' v' ->
  kentry_ok segs E M (KWord (SA b k) w v) -> kentry_ok segs E' M (KWord (SA b k) w v').
Proof.
  intros segs E E' M b k w v v' Hb Hv H. cbn [kentry_ok] in *.
  unfold flat, estart, adenot in *. cbn [a_base a_off] in *. rewrite <- Hb, <- Hv. exact H.
Qed.

(* [comment removed for export] *)
Lemma auxw_reenv : forall segs E E' M i ty v v',
  env_agree NX0 E E' -> edenot E v = edenot E' v' ->
  know_ok segs E M (auxw i ty v) -> know_ok segs E' M (auxw i ty v').
Proof.
  intros segs E E' M i ty v v' Hag Hv HK. unfold auxw, know_ok in *.
  pose proof (Forall_inv HK) as HK1. pose proof (Forall_inv (Forall_inv_tail HK)) as HK3.
  assert (Hb : AP.expr_vars_lt NX0 (fst e_auxb) = true) by (vm_compute; reflexivity).
  pose proof (edenot_agree' NX0 E E' _ Hag Hb) as Eb.
  constructor; [|constructor; [|constructor]].
  - exact (kword_reenv segs E E' M _ _ 8 (ELit ty) (ELit ty) Eb eq_refl HK1).
  - exact (kword_reenv segs E E' M _ _ 8 v v' Eb Hv HK3).
Qed.

Section InitHW.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable nofile sigmask : word.   (* [comment removed for export] *)
  Variable urnd : InputStream.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  Let E0a := E0 ph sp rdraw brk0 argv envp uid hw.
  Let usp := bv_unsigned sp.

  (* [comment removed for export] *)
  Definition E0hw : env := Env (fun n => if Nat.eqb n V_HW then hw else ev E0a n) (eb E0a).

  Lemma E0hw_agree : env_agree NX0 E0a E0hw.
  Proof.
    split; [|reflexivity]. intros n Hn. unfold E0hw. cbn [ev].
    destruct (Nat.eqb n V_HW) eqn:E; [apply Nat.eqb_eq in E; unfold V_HW, NX0 in *; lia | reflexivity].
  Qed.

  Let model0a := model0 segs sp brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd.
  Let FULL0a := FULL0 ph sp rdraw argv envp uid hw.
  Let SINV := SINV0 ph sp rdraw brk0 argv envp uid hw.
  Let argH := argH0 ph sp rdraw argv envp uid hw.

  (* [comment removed for export] *)
  Lemma Mr0_indep : forall E E' cs cs', Mr A argH E cs model0a FULL0a = Mr A argH E' cs' model0a FULL0a.
  Proof.
    intros E E' cs cs'. apply functional_extensionality. intros a. unfold Mr, mrestrict, hid, vis.
    destruct (model0_facts segs sp brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd) as (_&_&_&_&Hm&_).
    fold model0a in Hm. rewrite Hm. cbn [in_ivs existsb andb]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Let upd := usp / 4096 * 4096.

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma u_pd0 : uE E0hw e_pd = upd.
  Proof.
    pose proof (usp_lo sp Hsp) as L. pose proof (u_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U.
    unfold uE in *. rewrite <- (edenot_agree' NX0 E0a E0hw e_pd E0hw_agree) by (vm_compute; reflexivity).
    fold (uE E0a e_pd). rewrite (e_pd_val E0a) by (unfold uE; fold E0a in U; rewrite U; fold usp; lia).
    unfold uE. fold E0a in U. rewrite U. reflexivity.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Lemma u_stklen : uE E0hw e_stklen = STK_HW_TOP - upd.
  Proof.
    pose proof (usp_lo sp Hsp). pose proof (usp_hi ph sp rdraw argv envp uid hw Hva Hve Hfit).
    pose proof u_pd0 as P. unfold e_stklen, esub, uE in *. rewrite mkAlu_denot, edenot_lit.
    rewrite u_sub64, u64_lit by (unfold STK_HW_TOP; lia). rewrite P. unfold upd, usp, STK_HW_TOP, two64 in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Z.mod_small; lia.
  Qed.

  Lemma u_stk0_hw : uE E0hw (eaddz e_pd STK_OFF) = upd - 8388608.
  Proof.
    pose proof (usp_lo sp Hsp). pose proof (usp_hi ph sp rdraw argv envp uid hw Hva Hve Hfit).
    pose proof u_pd0 as P. unfold eaddz, uE in *. rewrite mkAlu_denot, edenot_lit.
    rewrite u_add64, u_lit64. rewrite P. unfold upd, usp, STK_OFF, two64 in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Z.add_mod_idemp_r by lia. rewrite Z.mod_small; lia.
  Qed.

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma u_stklen0 : uE E0hw e_stklen0 = STK_HW_TOP - usp.
  Proof.
    pose proof (usp_lo sp Hsp). pose proof (usp_hi ph sp rdraw argv envp uid hw Hva Hve Hfit).
    unfold e_stklen0, esub, uE. rewrite mkAlu_denot, edenot_lit. cbn [edenot].
    rewrite <- (edenot_agree' NX0 E0a E0hw e_sp0 E0hw_agree) by (vm_compute; reflexivity).
    unfold E0a. rewrite (edenot_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
    rewrite u_sub64, u64_lit by (unfold STK_HW_TOP; lia). fold usp. unfold STK_HW_TOP, two64 in *.
    rewrite Z.mod_small; lia.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Lemma u_stk0_hw0 : uE E0hw (eaddz e_sp0 STK_OFF) = usp - 8388608.
  Proof.
    pose proof (u_stk0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U. unfold uE in *.
    rewrite <- (edenot_agree' NX0 E0a E0hw _ E0hw_agree) by (vm_compute; reflexivity). exact U.
  Qed.

  Lemma allowA_init_hw : allowA A E0hw (init_acs_hw A) =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (upd - 8388608), pageup (upd - 8388608 + (STK_HW_TOP - upd)));
     (pagedown (shadow_off A + (upd - 8388608) / 8), pageup (shadow_off A + (upd - 8388608 + (STK_HW_TOP - upd)) / 8));
     (pagedown (usp - 8388608), pageup (usp - 8388608 + (STK_HW_TOP - usp)));
     (pagedown (shadow_off A + (usp - 8388608) / 8), pageup (shadow_off A + (usp - 8388608 + (STK_HW_TOP - usp)) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, init_acs_hw, init_vis_hw. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_stk0_hw, !u_stklen, !u_stk0_hw0, !u_stklen0.
    unfold uE. rewrite !edenot_lit, !u64_lit by lia. reflexivity.
  Qed.

  Lemma abytes_init_hw : A_bytes (allowA A E0hw (init_acs_hw A)) <= vis_cost (img_hi A - img_lo A) + vis_cost STK_HW_HI + vis_cost STK_HW_HI0
                         /\ vis_cost (img_hi A - img_lo A) + vis_cost STK_HW_HI + vis_cost STK_HW_HI0 <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
    pose proof (usp_lo sp Hsp) as HL1. pose proof (usp_hi ph sp rdraw argv envp uid hw Hva Hve Hfit) as HL2. fold usp in HL1, HL2.
    rewrite allowA_init_hw. cbn [A_bytes fst snd]. unfold vis_cost, STK_HW_HI, STK_HW_HI0, STK_HW_TOP, LIMIT, target_alloc_limit.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    replace (upd - 8388608 + (2 ^ 47 + 8388608 - upd)) with (2 ^ 47) by lia.
    assert (UPD : usp - 4095 <= upd <= usp /\ upd mod 4096 = 0).
    { unfold upd. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (upd - 8388608) (2 ^ 47) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (upd - 8388608) / 8) (shadow_off A + 2 ^ 47 / 8) ltac:(lia)).
    replace (usp - 8388608 + (2 ^ 47 + 8388608 - usp)) with (2 ^ 47) by lia.
    pose proof (pageup_minus_pagedown (usp - 8388608) (2 ^ 47) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (usp - 8388608) / 8) (shadow_off A + 2 ^ 47 / 8) ltac:(lia)).
    split; lia.
  Qed.

  Lemma init_kn_hw_ok : know_ok segs E0hw (Mr A argH E0hw (init_acs_hw A) model0a FULL0a) (init_kn_hw A).
  Proof.
    rewrite (Mr0_indep E0hw E0a (init_acs_hw A) (init_acs_of A)). unfold init_kn_hw, know_ok. apply Forall_app. split.
    - apply (auxw_reenv segs E0a E0hw _ 3 16 (ELit (bv_unsigned hw)) (EVar V_HW) E0hw_agree).
      + rewrite edenot_lit. unfold E0hw. cbn [edenot ev]. rewrite Z_to_bv_bv_unsigned. reflexivity.
      + apply (auxw_ok segs A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd Hsp Hva Hve Hfit 3 16 (ELit (bv_unsigned hw)));
          [lia | rewrite auxv_words_eq; reflexivity | rewrite auxv_words_eq; cbn [nth Z.to_nat]; rewrite edenot_lit, Z_to_bv_bv_unsigned; reflexivity].
    - apply (know_ok_agree' segs NX0 E0a E0hw _ _ E0hw_agree (kn_vars_lt_init_kn A)).
      exact (init_kn_ok segs A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd IMG Hsp Hbrk Hva Hve Hfit Huid).
  Qed.

  Theorem init_cs_ok_hw : cs_ok segs A LIMIT SINV argH fs E0hw (init_acs_hw A) (R0 sp) FULL0a model0a.
  Proof.
    destruct (model0_facts segs sp brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd)
      as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    fold model0a in M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (brk_range segs A ph sp rdraw brk0 argv envp uid hw IMG Hbrk) as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init_hw as [AB1 AB2].
    constructor; cbn [init_acs_hw a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - apply (regs_ok_agree' NX0 E0a E0hw _ _ E0hw_agree sr_vars_lt_init_regs).
      exact (init_regs_ok segs A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd Hsp Hva Hve Hfit).
    - reflexivity.
    - exact init_kn_hw_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - constructor.
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      unfold model0a, model0. apply init_sp_ok_init_model. exact Hsp.
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
    - split; [| destruct Hsp as (_ & Hs2 & _); exact Hs2].
      pose proof (u_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U. unfold uE in *.
      rewrite <- (edenot_agree' NX0 E0a E0hw _ E0hw_agree) by (vm_compute; reflexivity). exact U.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      unfold E0hw. cbn [ev V_HW V_BRK Nat.eqb].
      destruct (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7.
      fold E0a in U7. rewrite U7. rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [| intros; reflexivity]. intros n Hn. unfold E0hw. cbn [ev].
      destruct (Nat.eqb n V_HW) eqn:E; [apply Nat.eqb_eq in E; unfold V_HW, NX0 in *; lia | reflexivity].
  Qed.
End InitHW.
