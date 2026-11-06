(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState SumConv SysOpen.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecTop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceEx IfaceS InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Code Init Start0 StartLib KxA StartMain StartArgBytes
  DrvTLXa DrvIfaceT DrvIfaceR DrvIfaceM DrvM_states DrvM DrvR DrvR_facts DrvR_dstates DrvFw MainJoin SpineA Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma hd_nth0 : forall l : list (list byte), hd [] l = nth 0 l [].
Proof. intros [|]; reflexivity. Qed.

Section TopA.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable inp : ProcInput.
Hypothesis Hent : valid_entry48 imgA (mkEntry sp brk mb draw) inp.
Hypothesis Hinp : valid_input_either inp.
Let lim : Z := target_alloc_limit.
Let argv : list (list byte) := in_argv inp.
Let FS0 : Fs := in_fs inp.
Let c0 : config := c0A sp brk mb draw lim inp.
Let m0 : Model := cfg_model c0.
Let SpecT : list event -> Prop := Spec inp.

Lemma Hlim : 2 ^ 25 <= lim.
Proof. unfold lim, target_alloc_limit. cbn. lia. Qed.

Lemma SpecT_eq : forall t, SpecT t <-> SpineA.SpecT argv FS0 t.
Proof. intros t. reflexivity. Qed.

Lemma argc_len : ARGC inp = 2 <-> length argv = 2%nat.
Proof. unfold ARGC, argv. lia. Qed.

Lemma argv1_nonul : length argv = 2%nat -> ~ In (Z_to_bv 8 0) (nth 1 argv []).
Proof.
  intros Hlen. destruct Hinp as (Hargv & _). destruct Hargv as (_ & _ & _ & Hall & _).
  unfold argv in *. destruct (in_argv inp) as [|a [|b l]]; cbn in Hlen; try lia.
  cbn. inversion Hall as [|x l' Ha Hl']; subst. inversion Hl' as [|y l'' Hb Hl'']; subst. exact Hb.
Qed.
(* [comment removed for export] *)
Lemma argv0_nonul : ~ In (Z_to_bv 8 0) (hd [] argv).
Proof.
  destruct Hinp as (Hargv & _). destruct Hargv as (_ & _ & _ & Hall & _).
  unfold argv in *. destruct (in_argv inp) as [|a l]; cbn; [tauto|]. inversion Hall as [|x l' Ha Hl']; subst. exact Ha.
Qed.
(* [comment removed for export] *)
Lemma argv1_plain : length argv = 2%nat -> path_has_slash (nth 1 argv []) = false /\ path_eqb (nth 1 argv []) dotdot_path = false.
Proof. intros Hlen. apply (valid_input_arg1_plain inp Hinp). unfold argv in Hlen. rewrite Hlen. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable AInv : AA -> valuation -> list word -> Model -> Prop.
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segsA AInv CST.
Hypothesis HCST : forall a, in_rangesZ CST a -> 0 <= a < IMG_HI.     (* [comment removed for export] *)
Hypothesis HXGL : forall a, in_rangesZ XGL a -> 0 <= a < IMG_HI.
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HLF : law_fds_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : forall z, in_rangesZ DrvTLXa.CST_drv z -> in_rangesZ CST z.
Hypothesis HLPP : DrvTLXa.law_pp_stmt AInv CST.   (* [comment removed for export] *)
Hypothesis HCSTdrv2 : forall z, in_rangesZ DrvIfaceR.CST_drv2 z -> in_rangesZ CST z.
Hypothesis AC : alloc_contractsA segsA AE_A AInv CST XGL.
Hypothesis ACX : alloc_contractsA_ex segsA AE_A AInv CST XGL.
(* [comment removed for export] *)
Hypothesis MS : malloc_contractA_strong segsA AE_A AInv CST XGL.
Hypothesis MSX : malloc_contractA_strong_ex segsA AE_A AInv CST XGL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis HFZ : forall Kc ok', Kc_ok Kc -> ok_frameKA segsA Kc ok' -> fuzz_one_sumT AInv CST XGL Kc ok'.
Hypothesis HFZX : forall Kc, Kc_ok Kc -> fuzz_one_sumE AInv CST XGL Kc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A0_facts (Mm : Model) (B : Z) (rhoM : valuation) (tpM : list word) (A0 : AA) : Prop :=
  (forall md, erase_mat md = erase_mat Mm -> paid md tpM <= B -> AInv A0 rhoM tpM md)
  /\ bv_unsigned (rw rhoM 24%positive) = ag_tp (aa_geom A0)
  /\ topG (aa_geom A0) = bv_unsigned (rw rhoM 30%positive)      (* [comment removed for export] *)
  /\ aa_frames A0 = []
  /\ (0 <= aa_V A0 <= 65536 /\ aa_Km A0 = 0 /\ aa_Kf A0 = 0)
  /\ classes_fresh A0
  /\ large_live A0 = 0    (* [comment removed for export] *)
  /\ small_live A0 = 0.   (* [comment removed for export] *)

Hypothesis HandM : forall w, ARGC inp = 2 -> QMain sp brk mb draw lim inp w ->
  exists (Mm : Model) (B : Z) (rhoM : valuation) (tpM : list word) (A0 : AA),
    SPA segsA (KxA Mm B) DrvIfaceM.S_M rhoM tpM w
    /\ DrvM.P0M (nth 1 argv []) rhoM
    /\ m_fds Mm = std_fds /\ m_fs Mm = FS0
    /\ A0_facts Mm B rhoM tpM A0.

Hypothesis HandU : forall w, ARGC inp <> 2 -> QMain sp brk mb draw lim inp w ->
  exists (Mm : Model) (B : Z) (rhoM : valuation) (tpM : list word) (A0 : AA),
    SPA segsA (KxA Mm B) DrvIfaceM.S_U rhoM tpM w
    /\ MainJoin.P0U (hd [] argv) rhoM
    /\ m_fds Mm = std_fds /\ m_fs Mm = FS0
    /\ A0_facts Mm B rhoM tpM A0.

Let okT : world -> Prop := ok_tgt segsA SpecT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tcons_nil : tcons SpecT [].
Proof using inp. destruct (Spec_nonempty inp) as [t Ht]. exists t. split; [exact Ht | apply is_prefix_nil]. Qed.

Lemma OKF : forall K, K_nil K -> ok_frame segsA okT K.
Proof using inp. intros K HK. apply ok_frame_tgt_K. intros tr md H. rewrite (HK _ _ H). apply tcons_nil. Qed.
Lemma OKP : forall K, K_nil K -> ok_pframe segsA okT K.
Proof using inp. intros K HK. apply ok_pframe_tgt_K. intros tr md H. rewrite (HK _ _ H). apply tcons_nil. Qed.
Lemma OKFA : forall J : jpredA, (forall rho tp tr md, J rho tp tr md -> tr = []) -> ok_frameA segsA okT J.
Proof using inp. intros J HJ. apply ok_frameA_tgt. intros rho tp tr md H. rewrite (HJ _ _ _ _ H). apply tcons_nil. Qed.
Lemma OKPA : forall J : jpredA, (forall rho tp tr md, J rho tp tr md -> tr = []) -> ok_pframeA segsA okT J.
Proof using inp. intros J HJ. apply ok_pframeA_tgt. intros rho tp tr md H. rewrite (HJ _ _ _ _ H). apply tcons_nil. Qed.
Lemma HOKJ : forall J : jpredA, (forall rho tp tr md, J rho tp tr md -> tcons (SpineA.SpecT argv FS0) tr) -> ok_frameA segsA okT J.
Proof using inp. intros J HJ. apply ok_frameA_tgt. exact HJ. Qed.
Lemma HOKP : forall J : jpredA, (forall rho tp tr md, J rho tp tr md -> tcons (SpineA.SpecT argv FS0) tr) -> ok_pframeA segsA okT J.
Proof using inp. intros J HJ. apply ok_pframeA_tgt. exact HJ. Qed.
Lemma Hokh : ok_halted okT (SpineA.SpecT argv FS0).
Proof using inp. apply ok_halted_tgt. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main_safe : triple segsA okT (QMain sp brk mb draw lim inp) (fun _ => False).
Proof.
  intros n Hg w HQ.
  destruct (Z.eq_dec (ARGC inp) 2) as [E|NE].
  - destruct (HandM w E HQ) as (Mm & B & rhoM & tpM & A0 & HS & HP0 & Hfds & Hfs & HA0).
    destruct HA0 as (HAI & Htp & Htop & Hfr & HV & Hfresh & Hnl & Hns).
    assert (Hargc : length argv = 2%nat) by (apply argc_len; exact E).
    destruct (argv1_plain Hargc) as [Hnsl Hndd].
    pose proof (MainJoin.main_join_M AInv CST XGL argv FS0 Mm B rhoM tpM A0 Hfds Hfs HAI Htp Htop Hfr HV Hfresh Hnl Hns w HP0 HS) as HS2.
    exact (SpineA.spine_safe_A AInv CST XGL ALA HCST HXGL HLV HLF HCSTok HCSTdrv HLPP HCSTdrv2 argv FS0 Hargc (argv1_nonul Hargc) Hndd Hnsl
             (MDfs FS0) (MDfs_vm FS0) (MDfs_fds FS0) (MDfs_fs FS0) rhoM okT HOKJ HOKP Hokh AC MS HFZ
             rhoM tpM n Hg w HS2).
  - destruct (HandU w NE HQ) as (Mm & B & rhoM & tpM & A0 & HS & HP0 & Hfds & Hfs & HA0).
    destruct HA0 as (HAI & Htp & Htop & Hfr & HV & Hfresh & Hnl & Hns).
    assert (Hne : length argv <> 2%nat) by (intros E; apply NE, argc_len, E).
    exact (MainJoin.usage_safe AInv CST XGL argv FS0 Mm B rhoM tpM A0 Hfds Hfs HAI Htp Htop Hfr HV Hfresh Hnl Hns ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2
             Hne argv0_nonul HP0 okT HOKJ HOKP Hokh n Hg w HS).
Qed.

Theorem top_sound_A : forall n, safe segsA okT n (w0 c0).
Proof.
  intros n.
  destruct (init_smatch_A sp brk mb draw lim inp Hent Hinp) as (rhoI & Hsm & HJ).
  apply (triple_init_safe c0 (Init := SymSoundR.SP segsA (Start0.K0 m0) S0_A rhoI)).
  { split; [exact Hsm | split; reflexivity]. }
  eapply triple_seq; [exact (start_main_A sp brk mb draw lim inp Hent Hinp Hlim rhoI HJ okT OKF OKP OKFA OKPA)|].
  exact main_safe.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main_exists : forall t, SpecT t -> etriple segsA (QMain sp brk mb draw lim inp) (fun w => w_tr w = t).
Proof.
  intros t Ht w HQ.
  destruct (Z.eq_dec (ARGC inp) 2) as [E|NE].
  - destruct (HandM w E HQ) as (Mm & B & rhoM & tpM & A0 & HS & HP0 & Hfds & Hfs & HA0).
    destruct HA0 as (HAI & Htp & Htop & Hfr & HV & Hfresh & Hnl & Hns).
    assert (Hargc : length argv = 2%nat) by (apply argc_len; exact E).
    destruct (argv1_plain Hargc) as [Hnsl Hndd].
    pose proof (MainJoin.main_join_M AInv CST XGL argv FS0 Mm B rhoM tpM A0 Hfds Hfs HAI Htp Htop Hfr HV Hfresh Hnl Hns w HP0 HS) as HS2.
    exact (SpineA.spine_ex_A AInv CST XGL ALA HCST HXGL HLV HLF HCSTok HCSTdrv HLPP HCSTdrv2 argv FS0 Hargc (argv1_nonul Hargc) Hndd Hnsl
             (MDfs FS0) (MDfs_vm FS0) (MDfs_fds FS0) (MDfs_fs FS0) rhoM ACX MSX HFZX
             t (proj1 (SpecT_eq t) Ht) rhoM tpM w HS2).
  - destruct (HandU w NE HQ) as (Mm & B & rhoM & tpM & A0 & HS & HP0 & Hfds & Hfs & HA0).
    destruct HA0 as (HAI & Htp & Htop & Hfr & HV & Hfresh & Hnl & Hns).
    assert (Hne : length argv <> 2%nat) by (intros E; apply NE, argc_len, E).
    pose proof Ht as Ht'. unfold SpecT, Spec in Ht'. rewrite (spec_traces_argc_ne2 _ _ Hne) in Ht'.
    destruct Ht' as [<-|[]].
    exact (MainJoin.usage_ex AInv CST XGL argv FS0 Mm B rhoM tpM A0 Hfds Hfs HAI Htp Htop Hfr HV Hfresh Hnl Hns ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2
             Hne argv0_nonul HP0 w HS).
Qed.

Theorem top_complete_A : COMPLETE segsA c0 SpecT.
Proof.
  apply etriple_complete. intros t Ht w ->.
  destruct (init_smatch_A sp brk mb draw lim inp Hent Hinp) as (rhoI & Hsm & HJ).
  assert (Hsp0 : SymSoundR.SP segsA (Start0.K0 m0) S0_A rhoI (w0 c0)) by (split; [exact Hsm | split; reflexivity]).
  destruct (start_main_ex_A sp brk mb draw lim inp Hent Hinp Hlim rhoI HJ okT OKFA OKPA (w0 c0) Hsp0) as (w1 & Hst1 & HQ1).
  destruct (main_exists t Ht w1 HQ1) as (w2 & Hst2 & Htr2).
  exists w2. split; [eapply wsteps_trans; eauto | exact Htr2].
Qed.

Theorem top_A :
  SOUND segsA c0 SpecT /\ COMPLETE segsA c0 SpecT /\ ~ reaches_error_a segsA c0.
Proof.
  split; [|split].
  - apply (safe_tgt_sound SpecT). exact top_sound_A.
  - exact top_complete_A.
  - apply (safe_tgt_noerror SpecT). exact top_sound_A.
Qed.

End TopA.
