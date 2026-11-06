(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxImg FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.

Module PDrvMain2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec StepTac MemSplit.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout RefMemcpyLib FileLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.FileLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefStartupDefs RefStartup PDrvData PDrvMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition RG_hi2 : list region :=
  [ RGz (laddc SP0 (-65536)) 65536 RW TEmpty;
    RGz (laddc SP0 8) 16 RW (put_bytes TEmpty 0 (bvs_of P0 8 ++ bvs_of P1 8));
    RGz (ladd P1 X1) 1 RW (put_bytes TEmpty 0 [BK 0]) ].
Definition RG_main2 : list region := RG_hi2 ++ RG_img.
Definition F_main2 : list fact :=
  [FRange SP0 0x7fff80000000 0x800000000000; FMod SP0 4 0; FRange ARGC 1 1024; FCond BC_NE ARGC (lconst 2) false;
   FRange P1 0x7fff80000000 0x800010000000; FRange X1 0 131071; FRange T 1 4194304].
Definition P_main2 : sst := SST 0x22638 R_main RG_main2 F_main2 200 RNone.
Lemma P_main2_wf : state_wf P_main2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bases_main2 : bases_wf (s_next P_main2) (s_rgs P_main2) = true. Proof. vm_compute. reflexivity. Qed.

Lemma rdn_stack_to_mem2 : forall segs (base : word) (img : list byte) (a : Z) n,
  bv_unsigned base <= a -> a - bv_unsigned base + Z.of_nat n <= Z.of_nat (length img) -> a + Z.of_nat n <= 2^64 ->
  rdn segs (stack_to_mem base img) (Z_to_bv 64 a) n = Some (firstn n (skipn (Z.to_nat (a - bv_unsigned base)) img)).
Proof.
  intros segs base img a n. revert a. induction n as [|n IH]; intros a H1 H2 H3; [reflexivity|].
  cbn [rdn]. pose proof (bv_unsigned_in_range _ base) as RB. unfold bv_modulus in RB.
  assert (Hs : stack_to_mem base img (Z_to_bv 64 a) = nth_error img (Z.to_nat (a - bv_unsigned base))).
  { unfold stack_to_mem. rewrite u_small64 by (unfold two64; lia).
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Hs. destruct (nth_error img (Z.to_nat (a - bv_unsigned base))) as [b|] eqn:Hb;
    [| apply nth_error_None in Hb; lia].
  rewrite zbv_add1. rewrite (IH (a + 1)) by lia.
  f_equal. replace (Z.to_nat (a + 1 - bv_unsigned base)) with (S (Z.to_nat (a - bv_unsigned base))) by lia.
  clear -Hb. revert Hb. generalize (Z.to_nat (a - bv_unsigned base)) as k. intros k Hb.
  revert k Hb. induction img as [|x img IHi]; intros [|k] Hb; cbn in *; try discriminate.
  - injection Hb as <-. destruct n; reflexivity.
  - apply IHi. exact Hb.
Qed.

Section Handoff2.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.
Hypothesis Hargc2 : length av = 2%nat.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation p1 := (cat_argv_ptr sp0 av ev 1).
Local Notation a1s := (nth 1 av []).

#[using="Hargc2"] Lemma E_P1 : E 4%positive = p1.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0). unfold E, E_main. cbn [Pos.eqb]. rewrite Hargc2. reflexivity. Qed.
#[using="Type"] Lemma E_X1 : E 8%positive = Z_to_bv 64 (Z.of_nat (length a1s)). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2"] Lemma p1_bounds : bv_unsigned sp0 + 192 <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length a1s) + 1 < 2^64 /\
  bv_unsigned p1 <= bv_unsigned sp0 + 2^28.
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  pose proof (sp0_lo sp0 Hsp) as L. pose proof (sp0_hi sp0 Hsp) as H.
  pose proof (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve L H 1 ltac:(lia)) as U.
  pose proof (argv_ptr_bounds_at sp0 av ev Hva Hve H 1 ltac:(lia)) as [_ B].
  pose proof (valid_argv_str_len av 0 Hva ltac:(lia)) as S0.
  rewrite U in B |- *. unfold cat_struct_size, auxv_size in *.
  destruct av as [|a0 [|a1 [|? ?]]]; cbn in Hargc2; try discriminate. cbn [firstn nth] in *. unfold total_arg_bytes_nat in *. cbn [fold_right] in *.
  pose proof (valid_argv_len _ Hva). destruct Hve as [Hev _]. cbn [length] in *.
  split; [|split]; lia.
Qed.

#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma u_P1X1 : bv_unsigned (lden E (ladd P1 X1)) = bv_unsigned p1 + Z.of_nat (length a1s).
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  pose proof p1_bounds as (B1 & B2 & B3). pose proof (sp0_lo sp0 Hsp).
  rewrite lden_ladd. unfold P1, X1. rewrite !lden_lvar, E_P1, E_X1.
  rewrite bv_add_unsigned, Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (Z.of_nat _)) by (unfold bv_modulus; lia).
  apply bv_wrap_small. unfold bv_modulus. pose proof (bv_unsigned_in_range _ p1). lia.
Qed.

(* [comment removed for export] *)
#[using="uid tid hw rdraw regs Hsp Hva Hve ME Hargc2"] Lemma rdn_argv1 : rdn PSEGS mem p1 (length a1s + 1) = Some (a1s ++ [Z_to_bv 8 0]).
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  pose proof p1_bounds as (B1 & B2 & B3). pose proof (sp0_lo sp0 Hsp) as L. pose proof (sp0_hi sp0 Hsp) as H.
  rewrite <- (Z_to_bv_bv_unsigned _ p1).
  rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite u_small64 by (unfold two64; lia); lia).
  change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
  rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by (rewrite u_small64 by (unfold two64; lia); lia).
  rewrite Z_to_bv_bv_unsigned.
  exact (read_argv_cstr_k RPH PSEGS sp0 av ev 1 uid hw rdraw ltac:(lia) (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve H)).
Qed.

#[using="uid tid hw rdraw regs Hsp Hva Hve ME Hargc2"] Lemma rdn_nul1 : rdn PSEGS mem (Z_to_bv 64 (bv_unsigned p1 + Z.of_nat (length a1s))) 1 = Some [Z_to_bv 8 0].
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  pose proof p1_bounds as (B1 & B2 & B3). pose proof (sp0_lo sp0 Hsp) as L. pose proof (sp0_hi sp0 Hsp) as H.
  rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite u_small64 by (unfold two64; lia); lia).
  change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
  rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by (rewrite u_small64 by (unfold two64; lia); lia).
  pose proof (read_argv_byte_k RPH PSEGS sp0 av ev 1 (length a1s) uid hw rdraw ltac:(lia) ltac:(lia)
                (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve H)) as R.
  rewrite word_add_nat in R. rewrite R. f_equal. f_equal.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

#[using="uid hw Hsp Hva Hve ME Hargc2"] Lemma rg2_ok2 : rg_ok PSEGS E mem (RGz (ladd P1 X1) 1 RW (put_bytes TEmpty 0 [BK 0])).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  pose proof p1_bounds as (B1 & B2 & B3). pose proof (sp0_lo sp0 Hsp) as L.
  change (RGz (ladd P1 X1) 1 RW (put_bytes TEmpty 0 [BK 0])) with (track (RGz (ladd P1 X1) 1 RW TEmpty) 0 [BK 0]).
  apply rg_track_rdn; [ | lia | rsz_simpl; cbn; lia | ].
  - apply rg_rw_empty_ok; rewrite ?u_P1X1; [lia | unfold two64; lia |].
    intros i Hi.
    pose proof (rdn_overlay PSEGS 0xa0000 mem (bv_unsigned p1 + Z.of_nat (length a1s)) 1 [Z_to_bv 8 0] PSEGS_top) as HO.
    rewrite HO; [| lia | unfold two64; lia | exact rdn_nul1 | exact Hi]. replace i with 0 by lia. discriminate.
  - cbn [RGz rg_base track RGz length]. rewrite u_P1X1, Z.add_0_r, rdn_nul1. reflexivity.
Qed.

#[using="uid hw Hsp Hva Hve ME Hargc2"] Lemma rgs_main2_ok : Forall (rg_ok PSEGS E mem) RG_main2.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  unfold RG_main2, RG_hi2, RG_img. cbn [app].
  repeat (apply Forall_cons;
    [ first [ exact (rg0_ok sp0 av ev uid tid hw rdraw regs mem Hsp ME) | exact (rg1_ok sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME)
            | exact rg2_ok2 | exact (rg6_ok sp0 av ev uid tid hw rdraw regs mem Hsp ME) | exact (rg7_ok sp0 av ev uid tid hw rdraw regs mem Hsp ME)
            | (apply (rg_ro_okZ sp0 av ev uid tid hw rdraw regs mem Hsp ME); [lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity])
            | (apply (rg_ri_empty_okZ sp0 av ev uid tid hw rdraw regs mem Hsp ME); [lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]) ] | ]).
  apply Forall_nil.
Qed.

#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma rgs_main2_disj : rgs_disj E RG_main2.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  pose proof (sp0_lo sp0 Hsp) as L. pose proof (sp0_hi sp0 Hsp) as H. pose proof p1_bounds as (B1 & B2 & B3).
  assert (HA0 : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  assert (HA1 : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  pose proof u_P1X1 as HA2.
  apply (rgs_disj_app_sep E RG_hi2 RG_img 0xa0000).
  - cbn [RG_hi2 rgs_disj].
    repeat match goal with
           | |- _ /\ _ => split
           | |- Forall _ (_ :: _) => apply Forall_cons
           | |- Forall _ [] => apply Forall_nil
           | |- True => exact I
           | |- rg_disj _ _ _ => unfold rg_disj; rsz_simpl; cbn [RGz rg_base rg_size]; rewrite ?HA0, ?HA1, ?HA2; lia
           end.
  - apply cdisj_sound; [vm_compute; reflexivity|].
    unfold RG_img. repeat (apply Forall_cons; [eexists; split; [reflexivity | rewrite w64_mod; unfold two64; lia] |]). apply Forall_nil.
  - unfold RG_hi2. repeat (apply Forall_cons; [cbn [RGz rg_base]; rewrite ?HA0, ?HA1, ?HA2; lia|]). apply Forall_nil.
  - unfold RG_img. repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size]; unfold lconst, lden, lz; cbn [l_c l_t tsum]; rewrite Z.add_0_r, w64_mod;
                                                  rewrite u_small64 by (unfold two64; lia); unfold two64; lia|]).
    apply Forall_nil.
Qed.

#[using="uid hw mem Hsp Hva Hve Htid ME Hargc2"] Lemma facts_main2 : Forall (fact_ok E) F_main2.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve Htid ME Hargc2 : LiaFast.U) => LiaFast.u0).
  pose proof (sp0_lo sp0 Hsp) as L. pose proof (sp0_hi sp0 Hsp) as H. pose proof (sp0_al sp0 Hsp) as Al. pose proof p1_bounds as (B1 & B2 & B3).
  pose proof (valid_argv_len av Hva). pose proof (valid_argv_nonempty av Hva).
  pose proof (u_argcN av Hva) as UA.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as SL.
  unfold F_main2. repeat apply Forall_cons; try apply Forall_nil; cbn [fact_ok]; unfold SP0, ARGC, P1, X1, T; rewrite ?lden_lvar.
  - change (E 1%positive) with sp0. lia.
  - change (E 1%positive) with sp0. exact Al.
  - change (E 2%positive) with (argcN av). lia.
  - cbn [branch_taken]. change (E 2%positive) with (argcN av).
    destruct (bv_eqb (argcN av) (lden E (lconst 2))) eqn:Heq; [reflexivity|]. exfalso.
    assert (Hx : argcN av = lden E (lconst 2)) by (apply bv_eq; rewrite UA, Hargc2; reflexivity).
    rewrite Hx in Heq. rewrite bv_eqb_refl in Heq. discriminate Heq.
  - rewrite E_P1. lia.
  - rewrite E_X1. rewrite u_small64 by (unfold two64; lia). lia.
  - change (E 6%positive) with tid. lia.
Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc2"] Theorem handoff2 : sden PSEGS E P_main2 (mkst (fx := fx0) regs (Z_to_bv 64 0x22638) mem (seg_rom PSEGS)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 : LiaFast.U) => LiaFast.u0).
  apply sden0_sden; [exact P_main2_wf|].
  refine (conj eq_refl (conj eq_refl (conj eq_refl (conj (E_regs sp0 av ev uid tid hw rdraw regs mem ME) (conj rgs_main2_ok
          (conj rgs_main2_disj (conj facts_main2 _))))))).
  vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma outside_main2_hi : forall x, bv_unsigned sp0 + 24 <= bv_unsigned x < 2^48 ->
  bv_unsigned x <> bv_unsigned p1 + Z.of_nat (length a1s) -> outside E (s_rgs P_main2) x.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros x Hx Hn. pose proof (sp0_lo sp0 Hsp). pose proof (sp0_hi sp0 Hsp).
  pose proof u_P1X1 as HA2.
  assert (HA0 : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  assert (HA1 : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  unfold outside. cbn [s_rgs P_main2 RG_main2 RG_hi2 RG_img app].
  repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size]; rewrite ?HA0, ?HA1, ?HA2, ?u_lconst by lia; lia|]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma exg_outside2 : forall lo n i, In (lo, n) EXG_RANGES -> 0 <= i < Z.of_nat n -> outside E (s_rgs P_main2) (Z_to_bv 64 (lo + i)).
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros lo n i Hin Hi. pose proof (sp0_lo sp0 Hsp). pose proof (sp0_hi sp0 Hsp). pose proof p1_bounds as (B1 & B2 & B3).
  pose proof u_P1X1 as HA2.
  assert (HA0 : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  assert (HA1 : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  unfold EXG_RANGES in Hin. unfold outside. cbn [s_rgs P_main2 RG_main2 RG_hi2 RG_img app].
  repeat (destruct Hin as [Hin|Hin];
    [injection Hin as <- <-; cbn in Hi; rewrite u_small64 by (unfold two64; lia);
     repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size]; rewrite ?HA0, ?HA1, ?HA2, ?u_lconst by lia; lia|]); apply Forall_nil |]).
  destruct Hin.
Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc2"] Lemma exit_glob_of_MF2 : forall m', (forall x, outside E (s_rgs P_main2) x -> m' x = mem x) -> exit_glob m'.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros m' Hmf. pose proof (sp0_lo sp0 Hsp) as L.
  assert (Hm : forall lo n, In (lo, n) EXG_RANGES -> rdn PSEGS m' (Z_to_bv 64 lo) n = rdn PSEGS (fun _ => None) (Z_to_bv 64 lo) n).
  { intros lo n Hin. pose proof exg_miss as HM. rewrite forallb_forall in HM. pose proof (HM _ Hin) as Hmo. cbv beta in Hmo.
    assert (Hb : 0 <= lo /\ lo + Z.of_nat n <= 0xa0000).
    { unfold EXG_RANGES in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn; lia|]). destruct Hin. }
    apply rdn_ext_rd1; [lia | unfold two64; lia |].
    intros i Hi. unfold rd1. rewrite (Hmf _ (exg_outside2 lo n i Hin Hi)).
    rewrite (mem_miss sp0 av ev uid tid hw rdraw regs mem Hsp ME lo n i) by (lia || exact Hmo). reflexivity. }
  pose proof exit_glob_pristine as P. unfold exit_glob in *.
  rewrite (Hm 0x95e38 4%nat), (Hm 0x60b18 8%nat), (Hm 0x65058 1%nat), (Hm 0x95e63 1%nat), (Hm 0x96290 8%nat), (Hm 0x96280 8%nat),
    (Hm 0x64ff8 8%nat), (Hm 0x64f08 8%nat) by (unfold EXG_RANGES; cbn; tauto). exact P.
Qed.

(* [comment removed for export] *)
#[using="uid hw rdraw Hsp Hva Hve Hargc2"] Lemma argv1_top : entry_stack_fits sp0 av ev -> bv_unsigned p1 + Z.of_nat (length a1s) + 1 <= TASK_SIZE.
Proof. LiaFast.lf_pins (fun (uid hw rdraw Hsp Hva Hve Hargc2 : LiaFast.U) => LiaFast.u0).
  intros Hf. pose proof (sp0_lo sp0 Hsp) as L. pose proof (sp0_hi sp0 Hsp) as H.
  destruct (bsb_byte_k RPH sp0 av ev 1 uid hw rdraw ltac:(lia)) as (pre & post & Hbsb & Hpre).
  pose proof (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve L H 1 ltac:(lia)) as U.
  pose proof (build_stack_bytes_within_span RPH sp0 av ev uid hw rdraw) as WS.
  unfold entry_stack_fits in Hf. unfold TASK_SIZE, sp_window_hi in *.
  assert (Hl : Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) >= Z.of_nat (length pre) + Z.of_nat (length a1s) + 1).
  { rewrite Hbsb, !length_app. cbn [length]. lia. }
  rewrite U, <- Hpre. lia.
Qed.
Definition K1 : nat := length a1s.

#[using="uid tid hw rdraw regs Hsp Hva Hve ME Hargc2"] Lemma argv1_window : exists buf,
  rdn PSEGS mem p1 (length buf) = Some buf /\
  firstn (S K1) buf = a1s ++ [Z_to_bv 8 0] /\
  (bv_unsigned p1 + Z.of_nat K1) / 8 * 8 + 8 <= bv_unsigned p1 + Z.of_nat (length buf) /\
  bv_unsigned p1 + Z.of_nat (length buf) <= 0x800010000000.
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  pose proof (sp0_lo sp0 Hsp) as L. pose proof (sp0_hi sp0 Hsp) as H. pose proof (sp0_al sp0 Hsp) as Al.
  pose proof p1_bounds as (B1 & B2 & B3).
  destruct (bsb_byte_k RPH sp0 av ev 1 uid hw rdraw ltac:(lia)) as (pre & post & Hbsb & Hpre).
  pose proof (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve L H 1 ltac:(lia)) as U.
  set (img := entry_stack_image RPH sp0 av ev uid hw rdraw).
  set (blk := build_stack_bytes RPH sp0 av ev uid hw rdraw) in *.
  assert (Himg : img = blk ++ entry_slack sp0 blk (ed_slack rdraw)) by reflexivity.
  assert (Hlimg : bv_unsigned sp0 + Z.of_nat (length img) = entry_page_top sp0 blk).
  { rewrite Himg, length_app, length_entry_slack. unfold entry_slack_len.
    pose proof (entry_page_top_ge sp0 blk) as G. unfold entry_block_top in *. lia. }
  assert (Hpt : entry_page_top sp0 blk mod 8 = 0).
  { unfold entry_page_top, page_round_up_Z, page_size. rewrite Z.mul_comm. rewrite <- Z.mul_mod_idemp_l by lia.
    change (4096 mod 8) with 0. reflexivity. }
  assert (Hlblk : bv_unsigned p1 + Z.of_nat K1 + 1 <= bv_unsigned sp0 + Z.of_nat (length blk)).
  { rewrite Hbsb, !length_app. rewrite U, Hpre. unfold K1. cbn [length]. lia. }
  pose proof (entry_page_top_ge sp0 blk) as G. unfold entry_block_top in G.
  pose proof (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve H) as NW.
  pose proof (bsb_bound RPH sp0 av ev uid hw rdraw Hva Hve) as BB. fold blk in BB, NW.
  assert (PT : entry_page_top sp0 blk <= entry_block_top sp0 blk + 4096).
  { unfold entry_page_top, page_round_up_Z, page_size. pose proof (Z.div_mod (entry_block_top sp0 blk + 4096 - 1) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound (entry_block_top sp0 blk + 4096 - 1) 4096 ltac:(lia)). lia. }
  unfold entry_block_top in PT.
  set (n := Z.to_nat ((bv_unsigned p1 + Z.of_nat K1) / 8 * 8 + 8 - bv_unsigned p1)).
  assert (Hn : Z.of_nat n = (bv_unsigned p1 + Z.of_nat K1) / 8 * 8 + 8 - bv_unsigned p1).
  { unfold n. rewrite Z2Nat.id; [reflexivity|]. pose proof (Z.mod_pos_bound (bv_unsigned p1 + Z.of_nat K1) 8 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned p1 + Z.of_nat K1) 8 ltac:(lia)). lia. }
  assert (Hwin : (bv_unsigned p1 + Z.of_nat K1) / 8 * 8 + 8 <= entry_page_top sp0 blk).
  { pose proof (Z.div_mod (bv_unsigned p1 + Z.of_nat K1) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned p1 + Z.of_nat K1) 8 ltac:(lia)).
    pose proof (Z.div_mod (entry_page_top sp0 blk) 8 ltac:(lia)). rewrite Hpt in *.
    assert ((bv_unsigned p1 + Z.of_nat K1) / 8 < entry_page_top sp0 blk / 8) by lia. lia. }
  exists (firstn n (skipn (Z.to_nat (bv_unsigned p1 - bv_unsigned sp0)) img)).
  assert (Hlen : length (firstn n (skipn (Z.to_nat (bv_unsigned p1 - bv_unsigned sp0)) img)) = n).
  { rewrite length_firstn, length_skipn. lia. }
  rewrite Hlen. refine (conj _ (conj _ (conj _ _))).
  - rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME); [ | lia | lia].
    change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
    rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by lia.
    pose proof (rdn_stack_to_mem2 PSEGS sp0 img (bv_unsigned p1) n) as R. rewrite Z_to_bv_bv_unsigned in R. apply R; lia.
  - rewrite firstn_firstn. rewrite Nat.min_l by lia.
    replace (Z.to_nat (bv_unsigned p1 - bv_unsigned sp0)) with (length pre) by (rewrite U, Hpre; lia).
    rewrite Himg, Hbsb, <- !app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O. cbn [app].
    rewrite firstn_app. unfold K1. replace (S (length a1s) - length a1s)%nat with 1%nat by lia.
    rewrite firstn_all2 by lia. reflexivity.
  - lia.
  - lia.
Qed.

#[using="sp0 av ev uid tid hw rdraw regs Hsp ME Hargc2"] Lemma rodata_clear_main2 : forall i, 0x12fa0 <= i < 0x12fc0 -> mem (Z_to_bv 64 i) = None.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros i Hi. replace i with (0x12fa0 + (i - 0x12fa0)) by lia.
  apply (mem_miss sp0 av ev uid tid hw rdraw regs mem Hsp ME 0x12fa0 32 (i - 0x12fa0)); [lia | lia | vm_compute; reflexivity | lia].
Qed.

#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma outside_main2_rodata : forall x, 0x12fa0 <= bv_unsigned x < 0x12fc0 -> outside E (s_rgs P_main2) x.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros x Hx. pose proof (sp0_lo sp0 Hsp). pose proof (sp0_hi sp0 Hsp).
  pose proof p1_bounds as (B1 & B2 & B3).
  pose proof u_P1X1 as HA2.
  assert (HA0 : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  assert (HA1 : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  unfold outside. cbn [s_rgs P_main2 RG_main2 RG_hi2 RG_img app].
  repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size]; rewrite ?HA0, ?HA1, ?HA2, ?u_lconst by lia; lia|]). apply Forall_nil.
Qed.
End Handoff2.
End PDrvMain2.

From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvCall2 PDrvExit PDrvSys PUsageCert.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PUsageCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

Definition INFO (L : sst) := (s_pc L, RET L, rget (s_regs L) (rk 2), rget (s_regs L) (rk 10), rget (s_regs L) (rk 11), rget (s_regs L) (rk 12), rget (s_regs L) (rk 13), rget (s_regs L) (rk 17)).

Definition LO := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 P_main2 [].
Set Default Proof Mode "Ltac2".
Lemma certO : fx_explore TBL_P IMG_P 4000 S1 P_main2 [] = LO. Proof. cert_refl_vm constr:(LO). Qed.
Set Default Proof Mode "Classic".
Definition L_O : sst := Eval vm_compute in nth 0 LO P_main2.
Lemma LO_one : LO = [L_O]. Proof. reflexivity. Qed.

Definition NXO : positive := Eval vm_compute in s_next L_O.
(* [comment removed for export] *)
Definition U_oe : sst := Eval vm_compute in add_fact (havoc_call L_O 0x5ee78 KEEPALL [] None) (FRange (lvar (NXO + 10)) 18446744073709547521 18446744073709551615).
Lemma U_oe_eq : add_fact (havoc_call L_O 0x5ee78 KEEPALL [] None) (FRange (lvar (NXO + 10)) 18446744073709547521 18446744073709551615) = U_oe.
Proof. vm_compute. reflexivity. Qed.
Lemma hok_oe : havoc_ok L_O [] None = true. Proof. vm_compute. reflexivity. Qed.
Lemma fwf_oe : fwf (s_next (havoc_call L_O (s_pc L_O + 4) KEEPALL [] None)) (FRange (lvar (NXO + 10)) 18446744073709547521 18446744073709551615) = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition U_ofd : sst := Eval vm_compute in havoc_call L_O 0x5ee78 KEEPALL [] (Some (lconst 3)).
Lemma U_ofd_eq : havoc_call L_O 0x5ee78 KEEPALL [] (Some (lconst 3)) = U_ofd. Proof. vm_compute. reflexivity. Qed.
Lemma hok_ofd : havoc_ok L_O [] (Some (lconst 3)) = true. Proof. vm_compute. reflexivity. Qed.
