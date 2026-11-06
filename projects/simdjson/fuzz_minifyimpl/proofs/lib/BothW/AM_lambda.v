(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ARep AMalloc_iface F_apoison F_annot F_annot_sg F_annot_grow APoisonR_iface I_asan_memmove I_asan_memset.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac AU_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit ShadowTac AM_kitA AM_kitB AM_kitC AM_model AM_iface AM_annotw AM_minify AM_strctor AM_valloc AM_vdealloc AM_vctor AM_resize AM_resize0 AM_construct AM_assign AM_clstable AM_lambda_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
Definition bxl (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxl P) in H end.
Local Ltac ub H := unfold bxl in H.
(* [comment removed for export] *)
Lemma land_ldiff_distrL x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x k), (Z.testbit a k), (Z.testbit b k); reflexivity. Qed.
Lemma land_alignL : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 -> Z.land x (Z.ldiff (Z.ones 64) (Z.ones k)) = x - x mod 2^k.
Proof.
  intros x k Hx Hk. rewrite land_ldiff_distrL. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2^k) ltac:(lia)). lia.
Qed.
Lemma land_m32L : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof. intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)). rewrite land_alignL by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition B00 : byte := Z_to_bv 8 0.
Definition BF1 : byte := Z_to_bv 8 18446744073709551601.   (* [comment removed for export] *)
Definition BF2 : byte := Z_to_bv 8 18446744073709551602.   (* [comment removed for export] *)
Definition BF3 : byte := Z_to_bv 8 18446744073709551603.   (* [comment removed for export] *)
Definition BF5 : byte := Z_to_bv 8 18446744073709551605.   (* [comment removed for export] *)
Definition BF8 : byte := Z_to_bv 8 18446744073709551608.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition lamsh1 : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF2; C1 BF2; C1 BF2; C1 BF8; C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3].

(* [comment removed for export] *)
Definition lamsh2 : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 BF2; C1 BF2; C1 BF2; C1 BF8; C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3].
(* [comment removed for export] *)
Definition lamsh3 : list cell :=
  [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 BF2; C1 BF2; C1 BF2; C1 B00; C1 B00; C1 B00; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3].

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma sh16_of_words : forall m A,
  rw_cells bsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells bsegs m A (repeat (C1 B00) 16).
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma sh2_read : forall m A (i : Z), 0 <= i < 2 ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  ov_read_bytes bsegs m (wa (A + i)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m A i Hi H.
  assert (C : i = 0 \/ i = 1) by lia.
  destruct C as [->| ->].
  - rewrite <- (Z.add_0_r A) at 1. rewrite Z.add_0_r. exact (rw_cells_read bsegs m A _ 0%nat (C1 (Z_to_bv 8 0)) H eq_refl).
  - exact (rw_cells_read bsegs m A _ 1%nat (C1 (Z_to_bv 8 0)) H eq_refl).
Qed.

(* [comment removed for export] *)
Lemma cb24_words : forall m A (bs : list byte), rw_cells bsegs m A [CB 24 bs] ->
  exists w0 w1 w2 : word, rw_cells bsegs m A [C8 w0; C8 w1; C8 w2].
Proof.
  intros m A bs H.
  assert (L : length bs = 24%nat) by (destruct H as [[WF _] _]; cbn in WF; tauto).
  exists (le_bytes_to_word (firstn 8 bs)), (le_bytes_to_word (firstn 8 (skipn 8 bs))), (le_bytes_to_word (skipn 16 bs)).
  eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite !le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
  rewrite !app_nil_r. rewrite <- (firstn_skipn 8 bs) at 4.
  replace (drop 16 bs) with (drop 8 (drop 8 bs)) by (rewrite skipn_skipn; reflexivity). f_equal. apply firstn_skipn.
Qed.

(* [comment removed for export] *)
Fixpoint insideb (W : list ivl) (x : Z) : bool :=
  match W with [] => false | (lo, hi) :: W' => (((lo <=? x) && (x <? hi)) || insideb W' x)%bool end.
Lemma insideb_false : forall W x, insideb W x = false <-> outside W x.
Proof.
  induction W as [|[lo' hi'] W IH]; intros x; [cbn; tauto|].
  cbn [insideb outside]. fold insideb. fold outside.
  rewrite Bool.orb_false_iff, Bool.andb_false_iff, <- IH, Z.leb_gt, Z.ltb_ge.
  split; intros [A B]; (split; [lia| exact B]).
Qed.
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo' hi'] W1 IH]; intros W2 x; [cbn; tauto|]. cbn [outside app]. fold outside. fold (W1 ++ W2). rewrite IH. tauto. Qed.
Lemma munch_split2 : forall W1 W2 (m m' : amem), munch (W1 ++ W2) m m' -> wmono bsegs m m' ->
  exists m1 : amem, munch W1 m m1 /\ wmono bsegs m m1 /\ munch W2 m1 m' /\ wmono bsegs m1 m'.
Proof.
  intros W1 W2 m m' MU WM. exists (fun x => if insideb W1 (bv_unsigned x) then m' x else m x).
  assert (WV : forall (m1 m2 : amem) x, m1 x = m2 x -> wview bsegs m1 x = wview bsegs m2 x) by (intros m1 m2 x E; unfold wview; rewrite E; reflexivity).
  split; [| split; [| split]].
  - intros x Hx. apply insideb_false in Hx. rewrite Hx. reflexivity.
  - intros x Hx. destruct (insideb W1 (bv_unsigned x)) eqn:E.
    + rewrite (WV (fun x0 => if insideb W1 (bv_unsigned x0) then m' x0 else m x0) m' x) by (rewrite E; reflexivity). apply WM. exact Hx.
    + rewrite (WV (fun x0 => if insideb W1 (bv_unsigned x0) then m' x0 else m x0) m x) by (rewrite E; reflexivity). exact Hx.
  - intros x Hx. destruct (insideb W1 (bv_unsigned x)) eqn:E; [reflexivity|]. apply insideb_false in E. apply MU. apply outside_app. split; assumption.
  - intros x Hx. destruct (insideb W1 (bv_unsigned x)) eqn:E.
    + rewrite (WV (fun x0 => if insideb W1 (bv_unsigned x0) then m' x0 else m x0) m' x) in Hx by (rewrite E; reflexivity). exact Hx.
    + rewrite (WV (fun x0 => if insideb W1 (bv_unsigned x0) then m' x0 else m x0) m x) in Hx by (rewrite E; reflexivity). apply WM. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma ajt_unpoisoned : forall m, client_x m -> unpoisoned m AJT (AJT + 768).
Proof.
  intros m (_ & X & _). unfold AJT, AJT_SH in *. split; [lia|]. split; [lia|].
  intros G _ H1 H2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
  unfold ASHOFF. replace (2147450880 + G) with (2147643532 + (G - 192652)) by lia. apply X. lia.
Qed.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition LFR (pre : list cell) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  C8 (Z_to_bv 64 0) :: pre ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Ltac pick_in := (left; reflexivity) + (right; pick_in).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac drop_disj := repeat match goal with K : _ \/ _ |- _ => clear K end.
Ltac keep_disj1 K := repeat match goal with K' : _ \/ _ |- _ => tryif constr_eq K' K then fail else clear K' end.
Ltac keep_disj2 K1 K2 := repeat match goal with K' : _ \/ _ |- _ => tryif constr_eq K' K1 then fail else (tryif constr_eq K' K2 then fail else clear K') end.
Ltac dlia :=
  first [ solve [drop_disj; lia]
        | match goal with K : _ \/ _ |- _ => solve [keep_disj1 K; lia] end
        | match goal with K1 : _ \/ _, K2 : _ \/ _ |- _ => solve [keep_disj2 K1 K2; lia] end
        | lia ].
Ltac xrw H MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport bsegs W mo mn A cs) in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul LFR lamsh1 lamsh2 lamsh3 app repeat Datatypes.length]; dlia] end end.
(* [comment removed for export] *)
Tactic Notation "xrwby" hyp(H) hyp(MU) hyp(WM) "by" tactic3(k) :=
  (lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport bsegs W mo mn A cs) in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul LFR lamsh1 lamsh2 lamsh3 app repeat Datatypes.length]; k] end end).
(* [comment removed for export] *)
Tactic Notation "xrwg" hyp(H) hyp(MU) hyp(WM) "by" tactic3(k) :=
  (lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport bsegs W mo mn A cs) in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; k] end end).
Ltac xst H MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with stk _ _ ?loq ?hiq =>
      apply (stk_transport_disjoint bsegs W mo mn loq hiq) in H; [| exact MU| exact WM| cbn [disjoint_from]; lia] end end.
Ltac ag_of_hpr H := lazymatch type of H with aheap_pres ?CI ?LB ?SP ?m ?m' => change (aheap_pres CI LB SP m m') with (magree bsegs (aclient_addr CI LB SP) m m') in H end.
Ltac xag H AG tac :=
  lazymatch type of AG with magree _ ?P ?mo ?mn =>
    lazymatch type of H with
    | rw_cells _ _ ?A ?cs => apply (rw_cells_magree bsegs P mo mn A cs AG) in H; [| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul LFR lamsh1 lamsh2 lamsh3 app repeat Datatypes.length]; intros ? ?; tac]
    | stk _ _ ?loq ?hiq => apply (stk_magree bsegs P mo mn loq hiq AG) in H; [| intros ? ?; tac]
    | wr_at _ _ ?A ?k => apply (wr_at_magree bsegs P mo mn A k AG) in H; [| intros ? ?; tac]
    end end.

(* [comment removed for export] *)
Lemma implMA_ret_bind : forall {A B} RNG (a : A) (f : A -> Monad.M APS B) s Q ms,
  implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
Proof. intros A B RNG a f s Q ms H. exact H. Qed.

(* [comment removed for export] *)

Section LAM.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop).
  Variable K : ALooseKit AI fflag rng_fs.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis ONTA : opnew_stmtA AI.
  Hypothesis OD : opdelete_stmtA AI.
  Hypothesis AI_kind : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
  Hypothesis AI_premap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> premap_cells m.
  Hypothesis SM1 : stack_malloc_1_stmt AI fflag rng_fs.

  Section Body.
    Variables (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem)
              (s : APS) (LB : list ablock) (lo R C D : Z) (payload : list Z) (r0 r1 r2 : word) (cls FA FN RLO2 RHI2 : Z) (tr : list Z) (ULO UHI : Z).
    Notation n := (zlength payload).
    Notation SPA := (bv_unsigned sp).
    Notation SPL := (bv_unsigned sp - 128).
    Hypothesis AH : AHEAP AI L RNG (aps_m s) LB m0.
    Hypothesis NOF1 : forall F1 n1, ~ In (mkABlock (ABFake 1) F1 n1) LB.
    Hypothesis LBK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b mod 8 = 0.
    Hypothesis MI : mem_inv bsegs m0.
    Hypothesis ST : stk bsegs m0 lo SPA.
    Hypothesis LOA : ATOP + 4096 <= lo.
    Hypothesis LOS : lo <= SPA - ALAMBDA_STACK.
    Hypothesis STOP : SPA + 16 < al_top L.
    Hypothesis SP32 : SPA mod 32 = 0.
    Hypothesis TP : tp = Z_to_bv 64 ATP.
    Hypothesis PAT : payload_atA LB D payload.
    Hypothesis PBY : bytes_at bsegs m0 D (map (Z_to_bv 8) payload).
    Hypothesis PRG : Forall (fun c => 0 <= c < 256) payload.
    Hypothesis D16 : D mod 16 = 0.
    Hypothesis NLT : n < 2^26.
    Hypothesis FIN : In (mkABlock (ABFake cls) FA FN) LB.
    Hypothesis FR1 : FA <= R.
    Hypothesis FR2 : R + 24 <= FA + FN.
    Hypothesis R8 : R mod 8 = 0.
    Hypothesis RBLK : ablk R (R + 24).
    Hypothesis RC0 : rw_cells bsegs m0 R [C8 r0; C8 r1; C8 r2].
    Hypothesis RSH0 : rw_cells bsegs m0 (shad R) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
    Hypothesis Q1 : FA <= RLO2. Hypothesis Q2 : RLO2 <= R. Hypothesis Q3 : R + 24 <= RHI2. Hypothesis Q4 : RHI2 <= FA + FN.
    Hypothesis Q5 : RLO2 mod 64 = 0. Hypothesis Q6 : RHI2 mod 64 = 0.
    Hypothesis WR2 : wr_at bsegs m0 (shad RLO2) (shad RHI2 - shad RLO2).
    Hypothesis RR2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).
    Hypothesis CSP : SPA <= C. Hypothesis C47 : C + 16 <= 2^47. Hypothesis C16 : C mod 16 = 0.
    Hypothesis CC0 : rw_cells bsegs m0 C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)].
    Hypothesis CSH0 : rw_cells bsegs m0 (shad C) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
    Hypothesis FBK0 : rw_cells bsegs m0 AFALLBACK [C8 (Z_to_bv 64 AFALLBACK_VT)].
    Hypothesis HI0 : harness_invA m0.
    Hypothesis HUN : In [AMALLOC_PC; AOPNEW_RET] (al_U L).
    Hypothesis HUD : In [AFREE_PC; 0xb3460] (al_U L).
    Hypothesis S0A : SPA + 16 <= bv_unsigned s0.
    Hypothesis UCH : uchain m0 (al_top L) AFREE_PC SPA (bv_unsigned s0) (Nat.pred UDEPTH) tr.
    Hypothesis HUS : In (AFREE_PC :: ALAM_STRDEL_RET :: bv_unsigned ra :: tr) (al_U L).
    Hypothesis TRL : (length tr <= 27)%nat.
    Hypothesis RA12 : 4096 <= bv_unsigned ra.
    Hypothesis RAPC : bv_unsigned ra <> AFREE_PC.
    Hypothesis RSTK : rng RNG lo (al_top L - lo).
    Hypothesis RI : rng_aimg RNG.
    Hypothesis RISH : rng_aimg_sh RNG.
    Hypothesis RFS : rng_fs L RNG.
    Hypothesis RV : rng RNG R 24.
    Hypothesis RVS : rng RNG (shad R) 3.
    Hypothesis RCL : rng RNG C 16.
    Hypothesis RCS : rng RNG (shad C) 2.
    Hypothesis AOK : aps_ok L s.
    (* [comment removed for export] *)
    Hypothesis BUSH : unpoisoned m0 ULO UHI. Hypothesis BU0 : ATOP <= ULO. Hypothesis BUL : ULO <= lo. Hypothesis BUH : SPA <= UHI. Hypothesis BU47 : UHI <= 2^47.
    Hypothesis BRUSH : rng RNG (shad ULO) (shad UHI - shad ULO).

    (* [comment removed for export] *)
    Lemma lam_geom : 0 <= SPA < 2^47 /\ SPL mod 32 = 0 /\ Z.land (SPA - 128) 18446744073709551584 = SPL /\ lo + 4224 <= SPL /\ 0 <= lo
                     /\ Z.shiftr (C + 8) 3 + ASHOFF = shad C + 1 /\ Z.shiftr C 3 + ASHOFF = shad C
                     /\ 0x7fff8000 + 512 <= shad C /\ shad C + 2 <= 0x10007fff8000.
    Proof.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _). unfold ALAMBDA_STACK in LOS. pose proof atop_range as ATR.
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      repeat split.
      - lia. - lia.
      - clear - SP32. Z.div_mod_to_equations. lia.
      - rewrite land_m32L by lia. clear - SP32 RSP LOS LOA ATR. Z.div_mod_to_equations. lia.
      - lia. - exact LO0.
      - unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - C16. Z.div_mod_to_equations. lia.
      - unfold shad, ASHOFF. lia.
      - unfold shad, ASHOFF. rewrite ?Z.shiftr_div_pow2 by lia. clear - CSP LOA LOS ATR. Z.div_mod_to_equations. lia.
      - unfold shad, ASHOFF. rewrite ?Z.shiftr_div_pow2 by lia. clear - C47. Z.div_mod_to_equations. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_pro : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
      stk bsegs m lo SPA -> mem_inv bsegs m ->
      rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)] -> rt_suar m ->
      evtF bsegs RNG (fun ms' => exists m' (y1 y2 : word) (j16 : list byte),
          ms' = MS (mkR (Z_to_bv 64 0xb1ccc) (Z_to_bv 64 SPL) gp tp t0 t1 t2 sp (Z_to_bv 64 SPL)
                       (Z_to_bv 64 128) y1 y2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 R) (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 C) s6 s7 s8 s9 (Z_to_bv 64 ASHOFF) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ASTKMALLOC1) fc None m' (seg_rom bsegs)
          /\ munch [(SPL, SPA)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
          /\ rw_cells bsegs m' SPL (LFR [CB 16 j16] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
          /\ stk bsegs m' lo SPL)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 R) (Z_to_bv 64 C) (Z_to_bv 64 AFALLBACK) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALAMBDA) fc None m (seg_rom bsegs)).
    Proof.
      intros until m. intros STm MIm GOT SHB GSU SUA. unfold rt_suar in SUA. unfold ALAMBDA, ASTKMALLOC1, AGOT_SUAR, ASUAR in *.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & _).
      pose proof (munch_refl [(SPL, SPA)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      carve_frame 128%nat STm.
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      do 13 zstep.                  (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      rewrite ELAND.
      zstep. zstep. zstep.          (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep. rewrite sx32_lit by lia.   (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; lia| clear Kz]).   (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      apply evtF_done. change (Z_to_bv 64 2147450880) with (Z_to_bv 64 ASHOFF).
      eexists _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact FR| exact STm].
    Qed.

    (* [comment removed for export] *)
    Lemma lam_hdr : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m (F1 : Z) (j16 : list byte) (h0 h1 h2 : word) (junk : list byte),
      stk bsegs m lo SPL -> mem_inv bsegs m ->
      rw_cells bsegs m SPL (LFR [CB 16 j16] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells bsegs m F1 [C8 h0; C8 h1; C8 h2; CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F1))] ->
      rw_cells bsegs m (shad F1) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
      F1 mod 128 = 0 -> ablk F1 (F1 + 128) -> F1 + 128 <= ATOP ->
      rw_cells bsegs m C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
      rw_cells bsegs m (shad C) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      rng RNG F1 128 -> rng RNG (shad F1) 16 ->
      evtF bsegs RNG (fun ms' => exists m' (y2 y3 y4 y5 : word),
          ms' = MS (mkR (Z_to_bv 64 0xb1da0) (Z_to_bv 64 SPL) gp tp t0 t1 t2 sp (Z_to_bv 64 SPL)
                       (Z_to_bv 64 R) (Z_to_bv 64 n) y2 y3 y4 y5 a6 a7
                       (Z_to_bv 64 F1) (Z_to_bv 64 R) (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 C) (Z_to_bv 64 (C + 8)) (Z_to_bv 64 (F1 + 32))
                       (Z_to_bv 64 (shad F1)) (Z_to_bv 64 F1) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (shad C + 1)) t3 t4 t5 t6)
                   F (Z_to_bv 64 AVCTOR) fc None m' (seg_rom bsegs)
          /\ munch [(SPL + 8, SPL + 16); (F1, F1 + 24); (shad F1, shad F1 + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
          /\ rw_cells bsegs m' SPL (LFR [C8 (Z_to_bv 64 F1); CB 8 (skipn 8 j16)] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
          /\ rw_cells bsegs m' F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F1))]
          /\ rw_cells bsegs m' (shad F1) lamsh1
          /\ rw_cells bsegs m' C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)]
          /\ rw_cells bsegs m' (shad C) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
          /\ stk bsegs m' lo SPL)
        (MS (mkR (Z_to_bv 64 0xb1ccc) (Z_to_bv 64 SPL) gp tp t0 t1 t2 sp (Z_to_bv 64 SPL)
                 (Z_to_bv 64 F1) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 R) (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 C) s6 s7 s8 s9 (Z_to_bv 64 ASHOFF) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xb1ccc) fc None m (seg_rom bsegs)).
    Proof.
      intros until junk. intros STm MIm LF FC FS F128 FBLK FTOP CC CS RF RFS1.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & SHC8 & SHC0 & SHCLO & SHCHI).
      pose proof (ablk_lin _ _ FBLK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1. pose proof atop_range as ATR.
      assert (SHF : 0x7fff8000 <= shad F1 /\ shad F1 + 16 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - FL1 FL3 ATR; Z.div_mod_to_equations; lia).
      assert (ESHF : Z.shiftr F1 3 + ASHOFF = shad F1) by (unfold shad; lia).
      assert (FNS : F1 + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= F1) by (unfold ablk, AIMG_HI, KLS in FBLK; clear - FBLK; lia).
      assert (SHFC : shad F1 + 16 <= shad C) by (rewrite !shad_div; clear - FTOP LOA LOS' CSP; Z.div_mod_to_equations; lia).
      assert (ACC : rng RNG (Z.shiftr (C + 8) 3 + ASHOFF) 1) by (rewrite SHC8; eapply rng_sub'; [exact RCS| lia]).
      pose proof (sh16_of_words _ _ FS) as FS16. clear FS. cbn [repeat] in FS16.
      pose proof (munch_refl [(SPL + 8, SPL + 16); (F1, F1 + 24); (shad F1, shad F1 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      unfold LFR in LF. cbn [app] in LF.
      zstep. zstep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [clear Kz| exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz FL1; lia]).   (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep.          (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep. zstep. zstep.          (* [comment removed for export] *)
      replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
      replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
      replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
      zstep. zstep. zstep.          (* [comment removed for export] *)
      zstep. zstep. zstep.          (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
      zstep.                        (* [comment removed for export] *)
      rewrite ESHF.
      zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with CSx : rw_cells bsegs mm (shad C) _ |- _ =>
        pose proof (sh2_read mm (shad C) 1 ltac:(lia) CSx) as HR1; rewrite <- SHC8 in HR1 end end.
      astep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      astep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      apply evtF_done. rewrite SHC8.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with LFx : rw_cells bsegs mm SPL _, FCx : rw_cells bsegs mm F1 _, FSx : rw_cells bsegs mm (shad F1) _,
                            CCx : rw_cells bsegs mm C _, CSx : rw_cells bsegs mm (shad C) _, STx : stk bsegs mm lo _ |- _ =>
        eexists mm, _, _, _, _; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|];
        split; [exact LFx|]; split; [exact FCx|]; split; [exact FSx|]; split; [exact CCx|]; split; [exact CSx| exact STx] end end.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_mid : forall RNGx (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m (F1 : Z) (w8 : cell) (junk : list byte) (beg e c : Z),
      stk bsegs m lo SPL -> mem_inv bsegs m ->
      rw_cells bsegs m F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F1))] ->
      rw_cells bsegs m (shad F1) lamsh1 ->
      F1 mod 128 = 0 -> ablk F1 (F1 + 128) -> F1 + 128 <= ATOP -> (R + 24 <= F1 \/ F1 + 128 <= R) ->
      rw_cells bsegs m C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
      rw_cells bsegs m (shad C) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      rw_cells bsegs m R [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c)] ->
      rw_cells bsegs m (shad R) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      rw_cells bsegs m AFALLBACK [C8 (Z_to_bv 64 AFALLBACK_VT)] ->
      client_img m -> client_sh m ->
      fp_le RNG RNGx -> rng RNGx F1 128 -> rng RNGx (shad F1) 16 ->
      evtF bsegs RNGx (fun ms' => exists m' (y5 y6 y7 : word) (j8 j80 : list byte),
          ms' = MS (mkR (Z_to_bv 64 0xb1e20) (Z_to_bv 64 SPL) gp tp t0 t1 t2 sp (Z_to_bv 64 SPL)
                       (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 beg) (Z_to_bv 64 (F1 + 32)) y5 y6 y7
                       (Z_to_bv 64 F1) (Z_to_bv 64 R) (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 C) (Z_to_bv 64 (C + 8)) (Z_to_bv 64 (F1 + 32))
                       (Z_to_bv 64 (shad F1)) (Z_to_bv 64 F1) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (shad C + 1)) t3 t4 t5 t6)
                   F (Z_to_bv 64 AMIN_FN) fc None m' (seg_rom bsegs)
          /\ munch [(shad F1 + 4, shad F1 + 5); (F1 + 32, F1 + 40)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
          /\ rw_cells bsegs m' F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8; C8 (Z_to_bv 64 0); CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))]
          /\ rw_cells bsegs m' (shad F1) lamsh2
          /\ stk bsegs m' lo SPL)
        (MS (mkR (Z_to_bv 64 0xb1da0) (Z_to_bv 64 SPL) gp tp t0 t1 t2 sp (Z_to_bv 64 SPL)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 F1) (Z_to_bv 64 R) (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 C) (Z_to_bv 64 (C + 8)) (Z_to_bv 64 (F1 + 32))
                 (Z_to_bv 64 (shad F1)) (Z_to_bv 64 F1) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (shad C + 1)) t3 t4 t5 t6)
            F (Z_to_bv 64 0xb1da0) fc None m (seg_rom bsegs)).
    Proof.
      intros until c. intros STm MIm FC FS F128 FBLK FTOP DJRF CC CS RC RS FBK IMG USH FLE RF RFS1.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & SHC8 & SHC0 & SHCLO & SHCHI).
      pose proof (ablk_lin _ _ FBLK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1. pose proof atop_range as ATR.
      pose proof (ablk_lin _ _ RBLK) as (RL1 & RL2 & RL3 & RL4). unfold AIMG_HI in RL1.
      assert (SHF : 2148345856 <= shad F1 /\ shad F1 + 16 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - FL1 FL3 ATR; Z.div_mod_to_equations; lia).
      assert (FNS : F1 + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= F1) by (unfold ablk, AIMG_HI, KLS in FBLK; clear - FBLK; lia).
      assert (RNS : R + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= R) by (unfold ablk, AIMG_HI, KLS in RBLK; clear - RBLK; lia).
      assert (SHR : 2148345856 <= shad R /\ shad R + 3 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - RL1 RL3 ATR; Z.div_mod_to_equations; lia).
      assert (SHRF : shad R + 3 <= shad F1 \/ shad F1 + 16 <= shad R) by (rewrite !shad_div; unfold ASHOFF; clear - DJRF R8 F128; Z.div_mod_to_equations; lia).
      assert (SHFC : shad F1 + 16 <= shad C) by (rewrite !shad_div; clear - FTOP LOA LOS' CSP; Z.div_mod_to_equations; lia).
      assert (ESHR : Z.shiftr R 3 + ASHOFF = shad R) by (unfold shad; lia).
      pose proof (rng_fp_le _ _ _ _ FLE RCS) as RCS'. pose proof (rng_fp_le _ _ _ _ FLE RVS) as RVS'. pose proof (rng_fp_le _ _ _ _ FLE RCL) as RCL'.
      pose proof (rng_fp_le _ _ _ _ FLE RV) as RV'. pose proof (rng_fp_le _ _ _ _ FLE RI) as RI'. pose proof (rng_fp_le _ _ _ _ FLE RISH) as RISH'.
      (* [comment removed for export] *)
      pose proof (client_sh_cell _ AFALLBACK USH ltac:(unfold client_sh_addrs, AFALLBACK; pick_in)) as XF. change (Z.shiftr AFALLBACK 3 + 2147450880) with 2148327312 in XF.
      pose proof (client_sh_cell _ AVTAB_MIN USH ltac:(unfold client_sh_addrs, AVTAB_MIN; pick_in)) as XV. change (Z.shiftr AVTAB_MIN 3 + 2147450880) with 2147638278 in XV.
      destruct IMG as (_ & _ & _ & VMIN & _).
      assert (ACC0 : rng RNGx (Z.shiftr C 3 + ASHOFF) 1) by (rewrite SHC0; eapply rng_sub'; [exact RCS'| lia]).
      assert (ACCR : rng RNGx (Z.shiftr R 3 + ASHOFF) 1) by (rewrite ESHR; eapply rng_sub'; [exact RVS'| lia]).
      pose proof (munch_refl [(shad F1 + 4, shad F1 + 5); (F1 + 32, F1 + 40)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      unfold lamsh1 in FS. unfold ASHOFF in *. unfold AFALLBACK, AFALLBACK_VT, AVTAB_MIN, AMIN_FN in *.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54)] 96 junk [C8 (Z_to_bv 64 (fflag L 1 F1))] [8;8;80]%nat) in FC; [| reflexivity].
      cbn [mk_CB_cells app] in FC.
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia| clear K]).   (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep; try (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K; ubalign K; lia| clear K]).   (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with CSx : rw_cells bsegs mm (shad C) _, RSx : rw_cells bsegs mm (shad R) [C1 _; C1 _; C1 _] |- _ =>
        pose proof (sh2_read mm (shad C) 0 ltac:(lia) CSx) as HR0; rewrite Z.add_0_r, <- SHC0 in HR0;
        pose proof (sh3_read mm (shad R) 0 ltac:(lia) RSx) as HRR; rewrite Z.add_0_r, <- ESHR in HRR end end.
      astep. astep.                 (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      astep. astep.                 (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      astep. astep.                 (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      astep. astep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      astep. astep.                 (* [comment removed for export] *)
      zstep. zstep. zstep.          (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      apply evtF_done.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with FCx : rw_cells bsegs mm F1 _, FSx : rw_cells bsegs mm (shad F1) _, STx : stk bsegs mm lo _ |- _ =>
        eexists mm, _, _, _, _, _; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|];
        split; [exact FCx|]; split; [exact FSx| exact STx] end end.
    Qed.

    (* [comment removed for export] *)
    Notation LREGS ra0 a0v a1v a2v a3v a4v a5v a6v a7v s5v t0 t1 t2 t3 t4 t5 t6 F1 :=
      (mkR ra0 (Z_to_bv 64 SPL) gp tp t0 t1 t2 sp (Z_to_bv 64 SPL) a0v a1v a2v a3v a4v a5v a6v a7v
            (Z_to_bv 64 F1) (Z_to_bv 64 R) (Z_to_bv 64 AFALLBACK) s5v (Z_to_bv 64 (C + 8)) (Z_to_bv 64 (F1 + 32))
            (Z_to_bv 64 (shad F1)) (Z_to_bv 64 F1) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (shad C + 1)) t3 t4 t5 t6) (only parsing).

    (* [comment removed for export] *)
    Lemma lam_sok : forall RNGx (ra0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) m (F1 pos : Z),
      mem_inv bsegs m ->
      rw_cells bsegs m C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
      rw_cells bsegs m (shad C) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      rw_cells bsegs m (F1 + 32) [C8 (Z_to_bv 64 pos)] -> 0 <= pos <= n -> 0 <= F1 -> F1 + 128 <= ATOP ->
      fp_le RNG RNGx -> rng RNGx F1 128 ->
      evtF bsegs RNGx (fun ms' =>
          ms' = MS (LREGS (Z_to_bv 64 0xb1eac) (Z_to_bv 64 R) (Z_to_bv 64 pos) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 C) t0 t1 t2 t3 t4 t5 t6 F1)
                   F (Z_to_bv 64 AVRESIZE) fc None m (seg_rom bsegs))
        (MS (LREGS ra0 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 C) t0 t1 t2 t3 t4 t5 t6 F1)
            F (Z_to_bv 64 0xb1e20) fc None m (seg_rom bsegs)).
    Proof.
      intros until pos. intros MIm CC CS RSW POS F0 FTOP FLE RF.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & SHC8 & SHC0 & SHCLO & SHCHI). pose proof atop_range as ATR.
      pose proof (rng_fp_le _ _ _ _ FLE RCS) as RCS'. pose proof (rng_fp_le _ _ _ _ FLE RCL) as RCL'.
      zstep.                        (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; lia| clear Kz]).   (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [clear Kz| exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; lia]).   (* [comment removed for export] *)
      astep. astep.                 (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz POS NLT; lia| clear Kz]).   (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      apply evtF_done. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_err1 : forall RNGx (ra0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) m (F1 : Z),
      mem_inv bsegs m -> stk bsegs m lo SPL ->
      rw_cells bsegs m (shad F1) lamsh2 ->
      F1 mod 128 = 0 -> ablk F1 (F1 + 128) -> F1 + 128 <= ATOP ->
      client_img m -> client_sh m ->
      fp_le RNG RNGx -> rng RNGx (shad F1) 16 ->
      evtF bsegs RNGx (fun ms' => exists m' y2 y3,
          ms' = MS (LREGS (Z_to_bv 64 0xb1e78) (Z_to_bv 64 (F1 + 64)) (Z_to_bv 64 AERRMSG) y2 y3 a4 a5 a6 a7 (Z_to_bv 64 (F1 + 64)) t0 t1 t2 t3 t4 t5 t6 F1)
                   F (Z_to_bv 64 ASTRCTOR) fc None m' (seg_rom bsegs)
          /\ munch [(shad F1 + 8, shad F1 + 11)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
          /\ rw_cells bsegs m' (shad F1) lamsh3 /\ stk bsegs m' lo SPL)
        (MS (LREGS ra0 (Z_to_bv 64 15) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 C) t0 t1 t2 t3 t4 t5 t6 F1)
            F (Z_to_bv 64 0xb1e20) fc None m (seg_rom bsegs)).
    Proof.
      intros until F1. intros MIm STm FS F128 FBLK FTOP IMG USH FLE RFS1.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & SHC8 & SHC0 & SHCLO & SHCHI). pose proof atop_range as ATR.
      pose proof (ablk_lin _ _ FBLK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
      assert (SHF : 2148345856 <= shad F1 /\ shad F1 + 16 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - FL1 FL3 ATR; Z.div_mod_to_equations; lia).
      pose proof (rng_fp_le _ _ _ _ FLE RI) as RI'. pose proof (rng_fp_le _ _ _ _ FLE RISH) as RISH'.
      destruct IMG as (_ & _ & _ & _ & GERRC & MSG & _). unfold AGOT_ERRC, AERRC in GERRC, MSG. change (0x16dd60 + 248) with 1498712 in MSG.
      pose proof (client_sh_cell _ 0x16de58 USH ltac:(unfold client_sh_addrs; pick_in)) as XE. change (Z.shiftr 0x16de58 3 + 2147450880) with 2147638219 in XE.
      pose proof (munch_refl [(shad F1 + 8, shad F1 + 11)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      unfold lamsh2 in FS. unfold lamsh3. unfold ASHOFF in *.
      zstep.                        (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; lia| clear Kz]).   (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; lia| clear Kz]).   (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep. zstep. zstep.          (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; ubguard Kz; lia| clear Kz]).   (* [comment removed for export] *)
      zstep. zstep. zstep.          (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      astep. astep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      apply evtF_done.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with FSx : rw_cells bsegs mm (shad F1) _, STx : stk bsegs mm lo _ |- _ =>
        eexists mm, _, _; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact FSx| exact STx] end end.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_err2 : forall RNGx (ra0 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) m (F1 P : Z),
      mem_inv bsegs m ->
      rw_cells bsegs m (F1 + 64) [C8 (Z_to_bv 64 57); C8 (Z_to_bv 64 54); C8 (Z_to_bv 64 P)] -> 0 < P (* [comment removed for export] *) -> P + 56 <= ATOP -> 0 <= F1 -> F1 + 128 <= ATOP ->
      fp_le RNG RNGx -> rng RNGx F1 128 ->
      evtF bsegs RNGx (fun ms' => exists y4,
          ms' = MS (LREGS (Z_to_bv 64 0xb1ed8) (Z_to_bv 64 R) (Z_to_bv 64 P) (Z_to_bv 64 (P + 54)) (Z_to_bv 64 54) y4 a5 a6 a7 (Z_to_bv 64 (F1 + 64)) t0 t1 t2 t3 t4 t5 t6 F1)
                   F (Z_to_bv 64 AVASSIGN) fc None m (seg_rom bsegs))
        (MS (LREGS ra0 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F1 + 64)) t0 t1 t2 t3 t4 t5 t6 F1)
            F (Z_to_bv 64 0xb1e78) fc None m (seg_rom bsegs)).
    Proof.
      intros until P. intros MIm TC P0 PTOP F0 FTOP FLE RF.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & _). pose proof atop_range as ATR.
      (* [comment removed for export] *)
      assert (TB : rw_cells bsegs m (F1 + 64) [C1 (Z_to_bv 8 57); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 54); C8 (Z_to_bv 64 P)])
        by (eapply rw_cells_recast; [exact TC| cbn; repeat split; exact I| reflexivity| reflexivity]).
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [clear Kz| exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; lia]).   (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz P0 PTOP ATR; lia| clear Kz]).   (* [comment removed for export] *)
      zstep. zstep. zstep.          (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz P0 PTOP ATR; ubguard Kz; lia| clear Kz]).   (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      apply evtF_done. replace (54 + P) with (P + 54) by lia. eexists _. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_err3 : forall RNGx (ra0 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) m (F1 P : Z),
      mem_inv bsegs m ->
      rw_cells bsegs m (F1 + 64) [C8 (Z_to_bv 64 57); C8 (Z_to_bv 64 54); C8 (Z_to_bv 64 P)] -> 0 <= P -> P + 56 <= ATOP -> 0 <= F1 -> F1 + 128 <= ATOP ->
      fp_le RNG RNGx -> rng RNGx F1 128 ->
      evtF bsegs RNGx (fun ms' => exists y2 y3,
          ms' = MS (LREGS (Z_to_bv 64 ALAM_STRDEL_RET) (Z_to_bv 64 P) (Z_to_bv 64 56) y2 y3 a4 a5 a6 a7 (Z_to_bv 64 (F1 + 64)) t0 t1 t2 t3 t4 t5 t6 F1)
                   F (Z_to_bv 64 AOPDEL_SZ) fc None m (seg_rom bsegs))
        (MS (LREGS ra0 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F1 + 64)) t0 t1 t2 t3 t4 t5 t6 F1)
            F (Z_to_bv 64 0xb1ed8) fc None m (seg_rom bsegs)).
    Proof.
      intros until P. intros MIm TC P0 PTOP F0 FTOP FLE RF.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & _). pose proof atop_range as ATR.
      assert (TB : rw_cells bsegs m (F1 + 64) [C1 (Z_to_bv 8 57); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 54); C8 (Z_to_bv 64 P)])
        by (eapply rw_cells_recast; [exact TC| cbn; repeat split; exact I| reflexivity| reflexivity]).
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz; lia| clear Kz]).   (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      apply evtF_done. eexists _, _. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_err4 : forall RNGx (ra0 a0 a1 a2 a3 a4 a5 a6 a7 s5v t0 t1 t2 t3 t4 t5 t6 : word) m (F1 : Z),
      mem_inv bsegs m -> stk bsegs m lo SPL ->
      rw_cells bsegs m (shad F1) lamsh3 ->
      F1 mod 128 = 0 -> ablk F1 (F1 + 128) -> F1 + 128 <= ATOP ->
      fp_le RNG RNGx -> rng RNGx (shad F1) 16 ->
      evtF bsegs RNGx (fun ms' => exists m',
          ms' = MS (LREGS ra0 (Z_to_bv 64 18446744073709551608) a1 a2 a3 a4 a5 a6 a7 s5v t0 t1 t2 t3 t4 t5 t6 F1)
                   F (Z_to_bv 64 0xb1f04) fc None m' (seg_rom bsegs)
          /\ munch [(shad F1 + 8, shad F1 + 11)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
          /\ rw_cells bsegs m' (shad F1) lamsh2 /\ stk bsegs m' lo SPL)
        (MS (LREGS ra0 a0 a1 a2 a3 a4 a5 a6 a7 s5v t0 t1 t2 t3 t4 t5 t6 F1)
            F (Z_to_bv 64 ALAM_STRDEL_RET) fc None m (seg_rom bsegs)).
    Proof.
      intros until F1. intros MIm STm FS F128 FBLK FTOP FLE RFS1.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & _). pose proof atop_range as ATR.
      pose proof (ablk_lin _ _ FBLK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
      assert (SHF : 2148345856 <= shad F1 /\ shad F1 + 16 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - FL1 FL3 ATR; Z.div_mod_to_equations; lia).
      pose proof (munch_refl [(shad F1 + 8, shad F1 + 11)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      unfold lamsh3 in FS. unfold lamsh2, ALAM_STRDEL_RET.
      zstep.                        (* [comment removed for export] *)
      replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
      zstep. zstep. zstep.          (* [comment removed for export] *)
      apply evtF_done.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with FSx : rw_cells bsegs mm (shad F1) _, STx : stk bsegs mm lo _ |- _ =>
        eexists mm; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact FSx| exact STx] end end.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_ret : forall RNGx (ra0 a0 a1 a2 a3 a4 a5 a6 a7 s5v t0 t1 t2 t3 t4 t5 t6 : word) m (F1 FLG : Z) (w8 : word) (j8 : list byte) (h1 : word),
      mem_inv bsegs m -> stk bsegs m lo SPL ->
      rw_cells bsegs m SPL (LFR [C8 w8; CB 8 j8] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells bsegs m F1 [C8 h1] -> rw_cells bsegs m (F1 + 120) [C8 (Z_to_bv 64 FLG)] ->
      rw_cells bsegs m (shad F1) lamsh2 ->
      rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
      F1 mod 128 = 0 -> ablk F1 (F1 + 128) -> F1 + 128 <= ATOP ->
      ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= F1 \/ F1 + 128 <= FLG) ->
      fp_le RNG RNGx -> rng RNGx F1 128 -> rng RNGx (shad F1) 16 -> rng RNGx FLG 1 ->
      evtF bsegs RNGx (fun ms' => exists mp m' (y0 : word),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 y0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom bsegs)
          /\ munch [(shad F1, shad F1 + 16); (F1, F1 + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
          /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
          /\ stk bsegs m' lo SPA /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
        (MS (LREGS ra0 a0 a1 a2 a3 a4 a5 a6 a7 s5v t0 t1 t2 t3 t4 t5 t6 F1)
            F (Z_to_bv 64 0xb1f04) fc None m (seg_rom bsegs)).
    Proof.
      intros until h1. intros MIm STm LF FC FCF FS FLC F128 FBLK FTOP GBLK GTOP GF FLE RF RFS1 RG.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & _). pose proof atop_range as ATR.
      pose proof (ablk_lin _ _ FBLK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
      pose proof (ablk_lin _ _ GBLK) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1.
      assert (FNS : F1 + 128 <= KLS \/ 0x10007fff8000 <= F1) by (apply ablk_disj_band; exact FBLK). unfold KLS in FNS.
      assert (GNS : FLG + 1 <= KLS \/ 0x10007fff8000 <= FLG) by (apply ablk_disj_band; exact GBLK). unfold KLS in GNS.
      assert (SHF : 2148345856 <= shad F1 /\ shad F1 + 16 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - FL1 FL3 ATR; Z.div_mod_to_equations; lia).
      pose proof (rng_fp_le _ _ _ _ FLE RSTK) as RSTK'.
      pose proof (munch_refl [(shad F1, shad F1 + 16); (F1, F1 + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      unfold lamsh2 in FS. unfold LFR in LF. cbn [app] in LF.
      zstep.                        (* [comment removed for export] *)
      replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
      zstep.                        (* [comment removed for export] *)
      zstep. zstep.                 (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep; (let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz; [exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz FL1; lia| clear Kz]).   (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
      do 16 zstep.                  (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with MIx : mem_inv bsegs mm |- _ =>
        pose proof MU as MUP; pose proof WM as WMP; pose proof MIx as MIP; box MUP; box WMP; box MIP; clear MU WM;
        pose proof (munch_refl [(FLG, FLG + 1)] mm) as MU; pose proof (wmono_refl bsegs mm) as WM end end.
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) by lia.
      do 13 zstep.                  (* [comment removed for export] *)
      zstep.                        (* [comment removed for export] *)
      lazymatch goal with LFx : rw_cells bsegs _ (bv_unsigned sp - 128) _, STx : stk bsegs _ lo _ |- _ => release_frame LFx STx (bv_unsigned sp) end.
      zstep.                        (* [comment removed for export] *)
      apply evtF_done. replace (bv_unsigned sp - 128 + 128) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
        lazymatch goal with FLx : rw_cells bsegs mm FLG _, STx : stk bsegs mm lo _, MIx : mem_inv bsegs mm |- _ =>
        lazymatch type of MUP with bxl (munch _ m ?mp) =>
        eexists mp, mm, _; split; [reflexivity|]; unfold bxl in MUP, WMP, MIP;
        split; [exact MUP|]; split; [exact WMP|]; split; [exact MIP|]; split; [exact MU|]; split; [exact WM|]; split; [exact MIx|]; split; [exact STx| exact FLx] end end end.
    Qed.

    (* [comment removed for export] *)
    Definition lam_px (a : Z) : Prop := aclient_addr CI LB SPA a /\ ~ (R <= a < R + 24).
    Lemma lam_px_client : forall LB' sp' a, lam_px a -> (forall b, In b LB -> In b LB') -> sp' <= SPA -> aclient_addr CI LB' sp' a.
    Proof. intros LB' sp' a [Ha _] INCL LE. eapply aclient_addr_mono_sp; [eapply aclient_addr_mono_lb; [exact Ha| exact INCL]| exact LE]. Qed.

    (* [comment removed for export] *)
    Lemma lam_outside : forall RNGx st LBF mx F1 a,
      AHEAP AI L RNGx st LBF mx -> In (mkABlock (ABFake 1) F1 128) LBF -> (forall b, In b LB -> In b LBF) -> ablk F1 (F1 + 128) -> F1 mod 8 = 0 ->
      aclient_addr CI LB SPA a ->
      (a < lo \/ SPA <= a) /\ ~ (F1 <= a < F1 + 128) /\ ~ (shad F1 <= a < shad F1 + 16).
    Proof.
      intros RNGx st LBF mx F1 a AHx HF INCL FH F8 Ha. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
      pose proof lam_geom as (RSP & _ & _ & LOS' & LO0 & _). pose proof atop_range as ATR.
      pose proof (fun b Hb => AI_block_bounds AI _ _ _ _ _ b AHx Hb) as BB. cbv beta in BB.
      pose proof (BB _ HF) as BF. cbn [ab_addr ab_size] in BF.
      assert (FNS : F1 + 128 <= KLS \/ 0x10007fff8000 <= F1) by (apply ablk_disj_band; exact FH).
      unfold AIMG_HI, KHIGH, KLS in *. rewrite !shad_div. unfold ASHOFF.
      destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
      - clear - X BF LOS' LOA ATR FNS. Z.div_mod_to_equations. lia.
      - pose proof (AI_aci_img AI iv Hiv). pose proof (AI_aci_lo AI iv Hiv). unfold AIMG_HI in *. clear - H H0 Hr BF LOS' LOA ATR FH1 FNS. Z.div_mod_to_equations. lia.
      - pose proof (BB _ (INCL _ Hb)) as Bb.
        assert (NE : b <> mkABlock (ABFake 1) F1 128) by (intros ->; exact (NOF1 _ _ Hb)).
        pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx (INCL _ Hb) HF NE) as DJ. cbn [ab_addr ab_size] in DJ.
        unfold in_block in Hr. unfold AIMG_HI in Bb.
        assert (BNS : ab_addr b + ab_size b <= 2147446784 \/ 17594333495296 <= ab_addr b)
          by (pose proof (proj1 (LBK _ Hb)) as R1; apply ablk_disj_band in R1; unfold KLS in R1; exact R1).
        clear - Hr DJ Bb BNS BF LOS' LOA ATR FH2 FH3 FNS. Z.div_mod_to_equations. lia.
      - assert (A47 : 0 <= a' < 2^47 /\ (ATOP <= a' \/ a' < AIMG_HI \/ (exists c FA' fn, In (mkABlock (ABFake c) FA' fn) LB /\ FA' <= a' < FA' + fn))).
        { unfold AIMG_HI. destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]].
          - split; [clear - X ATR; lia| left; clear - X; lia].
          - pose proof (AI_aci_img AI iv Hiv) as IM1. pose proof (AI_aci_lo AI iv Hiv) as IM2. unfold AIMG_HI, in_ranges in *. split; [clear - IM1 IM2 Hr; lia| right; left; clear - IM1 IM2 Hr; lia].
          - pose proof (BB _ (INCL _ Hb')) as Bb. cbn [ab_addr ab_size] in Bb. split; [clear - Bb Hr ATR; lia|]. right; right. exists c, FA', fn. split; [exact Hb'| exact Hr]. }
        unfold AIMG_HI in A47. destruct A47 as [A47 CASES]. rewrite !shad_div. unfold ASHOFF. split; [| split].
        + clear - A47 BF LOS' LOA ATR. Z.div_mod_to_equations. lia.
        + clear - A47 FNS FH2 FH3. Z.div_mod_to_equations. lia.
        + destruct CASES as [X|[X|(c & FA' & fn & Hb' & Hr)]].
          * clear - X A47 FH3. Z.div_mod_to_equations. lia.
          * clear - X A47 FH1. Z.div_mod_to_equations. lia.
          * assert (NE : mkABlock (ABFake c) FA' fn <> mkABlock (ABFake 1) F1 128) by (intros E; apply (NOF1 F1 128); rewrite <- E; exact Hb').
            pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx (INCL _ Hb') HF NE) as DJ. cbn [ab_addr ab_size] in DJ.
            clear - DJ Hr A47 F8. Z.div_mod_to_equations. lia.
    Qed.
    (* [comment removed for export] *)
    Lemma lam_outsideL : forall RNGx st LBF mx F1 a,
      forall Lx, AHL AI fflag rng_fs K Lx RNGx st LBF mx -> In (mkABlock (ABFake 1) F1 128) LBF -> (forall b, In b LB -> In b LBF) -> ablk F1 (F1 + 128) -> F1 mod 8 = 0 ->
      aclient_addr CI LB SPA a ->
      (a < lo \/ SPA <= a) /\ ~ (F1 <= a < F1 + 128) /\ ~ (shad F1 <= a < shad F1 + 16).
    Proof.
      intros RNGx st LBF mx F1 a Lx AHx HF INCL FH F8 Ha. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
      pose proof lam_geom as (RSP & _ & _ & LOS' & LO0 & _). pose proof atop_range as ATR.
      pose proof (fun b Hb => lk_block_bounds _ _ _ K _ _ _ _ _ b AHx Hb) as BB. cbv beta in BB.
      pose proof (BB _ HF) as BF. cbn [ab_addr ab_size] in BF.
      assert (FNS : F1 + 128 <= KLS \/ 0x10007fff8000 <= F1) by (apply ablk_disj_band; exact FH).
      unfold AIMG_HI, KHIGH, KLS in *. rewrite !shad_div. unfold ASHOFF.
      destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
      - clear - X BF LOS' LOA ATR FNS. Z.div_mod_to_equations. lia.
      - pose proof (AI_aci_img AI iv Hiv). pose proof (AI_aci_lo AI iv Hiv). unfold AIMG_HI in *. clear - H H0 Hr BF LOS' LOA ATR FH1 FNS. Z.div_mod_to_equations. lia.
      - pose proof (BB _ (INCL _ Hb)) as Bb.
        assert (NE : b <> mkABlock (ABFake 1) F1 128) by (intros ->; exact (NOF1 _ _ Hb)).
        pose proof (lk_blocks_disjoint _ _ _ K _ _ _ _ _ _ _ AHx (INCL _ Hb) HF NE) as DJ. cbn [ab_addr ab_size] in DJ.
        unfold in_block in Hr. unfold AIMG_HI in Bb.
        assert (BNS : ab_addr b + ab_size b <= 2147446784 \/ 17594333495296 <= ab_addr b)
          by (pose proof (proj1 (LBK _ Hb)) as R1; apply ablk_disj_band in R1; unfold KLS in R1; exact R1).
        clear - Hr DJ Bb BNS BF LOS' LOA ATR FH2 FH3 FNS. Z.div_mod_to_equations. lia.
      - assert (A47 : 0 <= a' < 2^47 /\ (ATOP <= a' \/ a' < AIMG_HI \/ (exists c FA' fn, In (mkABlock (ABFake c) FA' fn) LB /\ FA' <= a' < FA' + fn))).
        { unfold AIMG_HI. destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]].
          - split; [clear - X ATR; lia| left; clear - X; lia].
          - pose proof (AI_aci_img AI iv Hiv) as IM1. pose proof (AI_aci_lo AI iv Hiv) as IM2. unfold AIMG_HI, in_ranges in *. split; [clear - IM1 IM2 Hr; lia| right; left; clear - IM1 IM2 Hr; lia].
          - pose proof (BB _ (INCL _ Hb')) as Bb. cbn [ab_addr ab_size] in Bb. split; [clear - Bb Hr ATR; lia|]. right; right. exists c, FA', fn. split; [exact Hb'| exact Hr]. }
        unfold AIMG_HI in A47. destruct A47 as [A47 CASES]. rewrite !shad_div. unfold ASHOFF. split; [| split].
        + clear - A47 BF LOS' LOA ATR. Z.div_mod_to_equations. lia.
        + clear - A47 FNS FH2 FH3. Z.div_mod_to_equations. lia.
        + destruct CASES as [X|[X|(c & FA' & fn & Hb' & Hr)]].
          * clear - X A47 FH3. Z.div_mod_to_equations. lia.
          * clear - X A47 FH1. Z.div_mod_to_equations. lia.
          * assert (NE : mkABlock (ABFake c) FA' fn <> mkABlock (ABFake 1) F1 128) by (intros E; apply (NOF1 F1 128); rewrite <- E; exact Hb').
            pose proof (lk_blocks_disjoint _ _ _ K _ _ _ _ _ _ _ AHx (INCL _ Hb') HF NE) as DJ. cbn [ab_addr ab_size] in DJ.
            clear - DJ Hr A47 F8. Z.div_mod_to_equations. lia.
    Qed.

    (* [comment removed for export] *)
    Local Ltac in_cr := apply IMG_CI; unfold client_ranges; pick_in.
    Local Ltac relro_cellL R A v := eapply rw_cells_recast; [apply (rw_cells_image0 bsegs _ A (le8 (Z_to_bv 64 v)));
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
        | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].

    (* [comment removed for export] *)
    Lemma lam_px_band : forall a, KLS + 4096 <= a < 0x10007fff8000 -> ~ (R <= a < R + 24).
    Proof.
      intros a Ha. pose proof (ablk_disj_band _ _ RBLK) as RNS. unfold KLS in *. clear - Ha RNS. lia.
    Qed.
    Lemma lam_px_img : forall a iv, In iv client_ranges -> fst iv <= a < snd iv -> lam_px a.
    Proof.
      intros a iv Hiv Ha. pose proof (AI_aci_img AI iv (IMG_CI iv Hiv)) as IM. pose proof (ablk_lin _ _ RBLK) as (RL1 & _).
      split; [right; left; exists iv; split; [apply IMG_CI; exact Hiv| lia]| clear - IM Ha RL1; lia].
    Qed.
    Lemma lam_px_stack : forall a, SPA <= a < 2^47 -> lam_px a.
    Proof.
      intros a Ha. pose proof (ablk_lin _ _ RBLK) as (_ & _ & RL3 & _). pose proof lam_geom as (_ & _ & _ & LOS' & _).
      split; [left; exact Ha| clear - Ha RL3 LOA LOS'; lia].
    Qed.
    (* [comment removed for export] *)
    Lemma lam_px_shadow : forall X k a, X mod 8 = 0 -> 0 <= X -> X + 8 * k <= 2^47 ->
      ((ATOP <= X) \/ (exists iv, In iv client_ranges /\ fst iv <= X /\ X + 8 * k - 7 <= snd iv) \/ (exists c FA' fn, In (mkABlock (ABFake c) FA' fn) LB /\ FA' <= X /\ X + 8 * k - 7 <= FA' + fn)) ->
      shad X <= a < shad X + k -> lam_px a.
    Proof.
      intros X k a X8 X0 XK HX Ha. pose proof atop_range as ATR.
      assert (EA : a = shad (X + 8 * (a - shad X)) /\ X <= X + 8 * (a - shad X) < X + 8 * k)
        by (rewrite !shad_div in *; unfold ASHOFF in *; clear - X8 X0 Ha; Z.div_mod_to_equations; lia).
      destruct EA as [EA RA]. split.
      - right; right; right. exists (X + 8 * (a - shad X)). split; [| exact EA].
        destruct HX as [H|[(iv & Hiv & H1 & H2)|(c & FA' & fn & Hb & H1 & H2)]].
        + left. clear - H RA XK. lia.
        + right; left. exists iv. split; [apply IMG_CI; exact Hiv| clear - H1 H2 RA; lia].
        + right; right. exists c, FA', fn. split; [exact Hb| clear - H1 H2 RA; lia].
      - apply lam_px_band. rewrite shad_div in Ha. unfold ASHOFF, KLS in *. clear - Ha X0 XK. Z.div_mod_to_equations. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_px_gran : forall A cap a,
      (forall b, In b LB -> A + cap <= ab_addr b \/ ab_addr b + ab_size b <= A) ->
      A mod 8 = 0 -> AIMG_HI <= A -> A + cap <= ATOP -> 0 <= cap ->
      lam_px a -> ~ (shad A <= a < shad A + granules cap).
    Proof.
      intros A cap a DJ A8 ALO AHI C0 [Ha _] X. rewrite granules_div in X by exact C0.
      pose proof lam_geom as (RSP & _ & _ & LOS' & LO0 & _). pose proof atop_range as ATR. pose proof ATOP_al16 as AT16. unfold AIMG_HI in ALO.
      rewrite !shad_div in X. unfold ASHOFF in X.
      destruct Ha as [Y|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & Ea)]]].
      - clear - X Y AHI ATR LOA LOS' C0. Z.div_mod_to_equations. lia.
      - pose proof (AI_aci_img AI iv Hiv) as IM. unfold AIMG_HI in IM. clear - X Hr IM ALO C0. Z.div_mod_to_equations. lia.
      - pose proof (proj1 (LBK _ Hb)) as BK. apply ablk_disj_band in BK. unfold KLS, in_block in *.
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb) as BB. unfold AIMG_HI in BB.
        clear - X Hr BK BB ALO AHI ATR C0. Z.div_mod_to_equations. lia.
      - subst a. rewrite shad_div in X. unfold ASHOFF in X.
        destruct Ha' as [Y|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]].
        + clear - X Y A8 AHI AT16 C0. Z.div_mod_to_equations. lia.
        + pose proof (AI_aci_img AI iv Hiv) as IM. unfold AIMG_HI in IM. clear - X Hr IM ALO A8 C0. Z.div_mod_to_equations. lia.
        + pose proof (DJ _ Hb') as DB. pose proof (proj2 (LBK _ Hb')) as F8'. cbn [ab_addr ab_size] in DB, F8'.
          clear - X Hr DB F8' A8 C0. Z.div_mod_to_equations. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma lam_ush : forall mk, magree bsegs lam_px m0 mk -> unpoisoned mk ULO UHI.
    Proof.
      intros mk AG. pose proof atop_range as ATR. pose proof ATOP_al16 as AT16. pose proof lam_geom as (RSP & _).
      eapply unpoisoned_agree; [exact BUSH|]. intros sh Hs. rewrite !shad_div in Hs. unfold ASHOFF in Hs.
      apply (fun H1 H2 => proj1 (AG sh H1 H2)).
      - clear - Hs BU0 BU47 BUH RSP ATR. Z.div_mod_to_equations. lia.
      - eapply (lam_px_shadow ATOP ((2^47 - ATOP) / 8));
          [clear - AT16; Z.div_mod_to_equations; lia| clear - ATR; lia| clear - ATR AT16; Z.div_mod_to_equations; lia| left; clear; lia|].
        rewrite shad_div. unfold ASHOFF. clear - Hs BU0 BU47 BUH RSP ATR AT16. Z.div_mod_to_equations. lia.
    Qed.

    Lemma lam_refresh : forall mk, magree bsegs lam_px m0 mk -> (forall i, ARELRO_LO <= i < ARELRO_HI -> mk (wa i) = None) -> mem_inv bsegs mk ->
      rw_cells bsegs mk C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)]
      /\ rw_cells bsegs mk (shad C) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      /\ rw_cells bsegs mk (shad R) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      /\ rw_cells bsegs mk AFALLBACK [C8 (Z_to_bv 64 AFALLBACK_VT)]
      /\ client_img mk /\ client_sh mk
      /\ uchain mk (al_top L) AFREE_PC SPA (bv_unsigned s0) (Nat.pred UDEPTH) tr
      /\ wr_at bsegs mk (shad RLO2) (shad RHI2 - shad RLO2).
    Proof.
      intros mk AG RR MIk. pose proof lam_geom as (RSP & _ & _ & LOS' & LO0 & _). pose proof atop_range as ATR.
      pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH FIN) as FB. cbn [ab_addr ab_size] in FB. unfold AIMG_HI in FB.
      destruct HI0 as [IMG0 USH0].
      split. { eapply rw_cells_magree; [exact AG| exact CC0|]. cbn. intros a Ha. apply lam_px_stack. clear - Ha CSP C47. lia. }
      split. { eapply rw_cells_magree; [exact AG| exact CSH0|]. cbn. intros a Ha. eapply (lam_px_shadow C 2); [clear - C16; Z.div_mod_to_equations; lia| lia| lia| left; clear - CSP LOS' LOA; lia| exact Ha]. }
      split. { eapply rw_cells_magree; [exact AG| exact RSH0|]. cbn. intros a Ha. eapply (lam_px_shadow R 3); [exact R8| lia| lia| right; right; exists cls, FA, FN; split; [exact FIN| lia]| exact Ha]. }
      split. { eapply rw_cells_magree; [exact AG| exact FBK0|]. cbn. intros a Ha. eapply (lam_px_img a (0x6afc80, 0x6afcac)); [unfold client_ranges; pick_in| unfold AFALLBACK in Ha; cbn; lia]. }
      split. { destruct IMG0 as (_ & V1 & V2 & V3 & _ & M1 & X). unfold client_img, AVTAB_SRS, AVTAB_VU8, AVTAB_MIN in *.
        unfold ARELRO_LO, ARELRO_HI in RR.
        split; [unfold AGOT_SUAR, ASUAR; relro_cellL RR 0x173d30 0x17d480|].
        split; [eapply rw_cells_magree; [exact AG| exact V1|]; cbn; intros a Ha; eapply (lam_px_img a (0x16e010, 0x16e050)); [unfold client_ranges; pick_in| cbn; lia]|].
        split; [eapply rw_cells_magree; [exact AG| exact V2|]; cbn; intros a Ha; eapply (lam_px_img a (0x16e010, 0x16e050)); [unfold client_ranges; pick_in| cbn; lia]|].
        split; [eapply rw_cells_magree; [exact AG| exact V3|]; cbn; intros a Ha; eapply (lam_px_img a (0x16e010, 0x16e050)); [unfold client_ranges; pick_in| cbn; lia]|].
        split; [unfold AGOT_ERRC, AERRC; relro_cellL RR 0x174958 0x16dd60|].
        split; [eapply rw_cells_magree; [exact AG| exact M1|]; cbn; intros a Ha; eapply (lam_px_img a (0x16de50, 0x16de60)); [unfold client_ranges; pick_in| unfold AERRC in Ha; cbn; lia]|].
        eapply client_x_magree; [exact X| exact AG|]. unfold client_x_addr, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN. intros a [Ha|[Ha|[Ha|Ha]]].
        - eapply (lam_px_shadow 0x24480 16); [reflexivity| lia| lia| right; left; exists (0x24480, 0x24500); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x178460 96); [reflexivity| lia| lia| right; left; exists (0x178460, 0x178760); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_img a (0x178460, 0x178760)); [unfold client_ranges; pick_in| cbn; lia].   (* [comment removed for export] *)
        - eapply (lam_px_img a (0x175b28, 0x175b30)); [unfold client_ranges; pick_in| cbn; lia]. }
      split. { eapply client_sh_magree; [exact USH0| exact AG|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX.
        destruct HX as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].
        - eapply (lam_px_shadow 0x16e010 8); [reflexivity| lia| lia| right; left; exists (0x16e010, 0x16e050); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x16e010 8); [reflexivity| lia| lia| right; left; exists (0x16e010, 0x16e050); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x6afb00 8); [reflexivity| lia| lia| right; left; exists (0x6afb00, 0x6afb40); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x6afb00 8); [reflexivity| lia| lia| right; left; exists (0x6afb00, 0x6afb40); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x6afb00 8); [reflexivity| lia| lia| right; left; exists (0x6afb00, 0x6afb40); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x6afc60 1); [reflexivity| lia| lia| right; left; exists (0x6afc60, 0x6afc68); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x6afc80 5); [reflexivity| lia| lia| right; left; exists (0x6afc80, 0x6afcac); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x6afc80 6); [reflexivity| lia| lia| right; left; exists (0x6afc80, 0x6afcac); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x16e010 8); [reflexivity| lia| lia| right; left; exists (0x16e010, 0x16e050); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia].
        - eapply (lam_px_shadow 0x16de50 2); [reflexivity| lia| lia| right; left; exists (0x16de50, 0x16de60); split; [unfold client_ranges; pick_in| cbn; lia]| rewrite !shad_div; unfold ASHOFF; lia]. }
      split. { eapply uchain_frame; [exact UCH|]. intros a Ha. apply AG; [clear - Ha S0A RSP LY3; lia| apply lam_px_stack; clear - Ha S0A LY3; lia]. }
      eapply wr_at_magree; [exact AG| exact WR2|]. intros a Ha.
      eapply (lam_px_shadow RLO2 ((RHI2 - RLO2) / 8)); [clear - Q5; Z.div_mod_to_equations; lia| lia| clear - Q4 Q5 Q6 FB ATR; Z.div_mod_to_equations; lia
        | right; right; exists cls, FA, FN; split; [exact FIN| clear - Q1 Q4 Q5 Q6; Z.div_mod_to_equations; lia]| rewrite !shad_div in *; unfold ASHOFF in *; clear - Ha Q5 Q6; Z.div_mod_to_equations; lia].
    Qed.

    Notation POST := (lambda_post AI fflag rng_fs K L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB R C D payload lo m0).
    (* [comment removed for export] *)
    Definition bl (b : option AsanCtrl.aptr) (A : Z) : list ablock := match b with Some p => [HB p A n] | None => [] end.

    (* [comment removed for export] *)
    Definition lay (b : option AsanCtrl.aptr) (A cap k : Z) : alayout :=
      match b with Some p => lk_setb AI fflag rng_fs K L p A cap (Some (vpat cap k)) | None => L end.
    Definition blc (b : option AsanCtrl.aptr) (A cap : Z) : list ablock := match b with Some p => [HB p A cap] | None => [] end.
    Lemma lay_fflag : forall b A cap k c F0, fflag (lay b A cap k) c F0 = fflag L c F0.
    Proof. intros [p|] A cap k c F0; [apply (lk_fflag _ _ _ K)| reflexivity]. Qed.
    Lemma lay_top : forall b A cap k, al_top (lay b A cap k) = al_top L.
    Proof. intros [p|] A cap k; [apply (lk_top _ _ _ K)| reflexivity]. Qed.
    Lemma lay_U : forall b A cap k, al_U (lay b A cap k) = al_U L.
    Proof. intros [p|] A cap k; [apply (lk_U _ _ _ K)| reflexivity]. Qed.
    Lemma lay_aps_ok : forall b A cap k sx, aps_ok (lay b A cap k) sx <-> aps_ok L sx.
    Proof. intros [p|] A cap k sx; [apply (lk_aps_ok _ _ _ K)| reflexivity]. Qed.

    (* [comment removed for export] *)
    Lemma lam_close : forall (RNGv : footprint) (sv : APS) (mv : amem) (F1 : Z) (w8 : word) (j8 : list byte) (h1 : word)
        (b : option AsanCtrl.aptr) (A k cap : Z) (ra0 a0 a1 a2 a3 a4 a5 a6 a7 s5v t0 t1 t2 t3 t4 t5 t6 : word),
      fp_le RNG RNGv -> aps_rest sv = aps_rest s -> aps_cl sv = aps_cl s ->
      AHL AI fflag rng_fs K (lay b A cap k) RNGv (aps_m sv) (blc b A cap ++ mkABlock (ABFake 1) F1 128 :: LB) mv -> lk_tight AI fflag rng_fs K L ->
      magree bsegs lam_px m0 mv -> mem_inv bsegs mv -> stk bsegs mv lo SPL ->
      rw_cells bsegs mv SPL (LFR [C8 w8; CB 8 j8] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells bsegs mv F1 [C8 h1] -> rw_cells bsegs mv (F1 + 120) [C8 (Z_to_bv 64 (fflag L 1 F1))] ->
      rw_cells bsegs mv (shad F1) lamsh2 ->
      F1 mod 128 = 0 -> ablk F1 (F1 + 128) -> F1 + 128 <= ATOP -> (R + 24 <= F1 \/ F1 + 128 <= R) ->
      rng RNGv F1 128 -> rng RNGv (shad F1) 16 ->
      rw_cells bsegs mv R [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + k)); C8 (Z_to_bv 64 (A + cap))] -> 0 <= k <= cap ->
      match b with
      | None => A = 0 /\ cap = 0
      | Some p => 0 < cap <= AREQMAX /\ ablock_range A cap /\ rng RNGv A cap /\ rng RNGv (shad A) (granules cap)
                  /\ rw_cells bsegs mv (shad A) [CB (Z.to_nat (granules cap)) (vpat cap k)]
      end ->
      evtF bsegs RNGv (POST b sv RNGv)
        (MS (LREGS ra0 a0 a1 a2 a3 a4 a5 a6 a7 s5v t0 t1 t2 t3 t4 t5 t6 F1) F (Z_to_bv 64 0xb1f04) fc None mv (seg_rom bsegs)).
    Proof.
      intros until t6. intros FLEv ARSv CLv AHv TIGHT AGv MIv STv LFv FCv FCFv FSv F128 FBLK FTOP DJRF RFv RFSv RCv KC BLK.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & _). pose proof atop_range as ATR.
      pose proof (ablk_lin _ _ RBLK) as (RL1 & RL2 & RL3 & RL4). unfold AIMG_HI in RL1.
      assert (RNS : R + 24 <= KLS \/ 0x10007fff8000 <= R) by (apply ablk_disj_band; exact RBLK). unfold KLS in RNS.
      pose proof (ablk_lin _ _ FBLK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
      assert (F8 : F1 mod 8 = 0) by (clear - F128; Z.div_mod_to_equations; lia).
      assert (FNS : F1 + 128 <= KLS \/ 0x10007fff8000 <= F1) by (apply ablk_disj_band; exact FBLK). unfold KLS in FNS.
      assert (SHF : 2148345856 <= shad F1 /\ shad F1 + 16 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - FL1 FL3 ATR; Z.div_mod_to_equations; lia).
      assert (INF : In (mkABlock (ABFake 1) F1 128) (blc b A cap ++ mkABlock (ABFake 1) F1 128 :: LB)) by (apply in_or_app; right; left; reflexivity).
      assert (INCL : forall b0, In b0 LB -> In b0 (blc b A cap ++ mkABlock (ABFake 1) F1 128 :: LB)) by (intros b0 Hb; apply in_or_app; right; right; exact Hb).
      (* [comment removed for export] *)
      destruct (lk_fake_flag _ _ _ K _ _ _ _ _ _ _ _ AHv INF) as (FLC & RG & GBLK & GTOP & GDJ & GCI). rewrite !lay_fflag in FLC, RG, GBLK, GTOP, GDJ, GCI.
      set (FLG := fflag L 1 F1) in *.
      pose proof (GDJ _ INF) as GF. cbn [ab_addr ab_size] in GF.
      pose proof (GDJ _ (INCL _ FIN)) as GR. cbn [ab_addr ab_size] in GR.
      pose proof (ablk_lin _ _ GBLK) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1.
      assert (GNS : FLG + 1 <= KLS \/ 0x10007fff8000 <= FLG) by (apply ablk_disj_band; exact GBLK). unfold KLS in GNS.
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (lam_ret RNGv ra0 a0 a1 a2 a3 a4 a5 a6 a7 s5v t0 t1 t2 t3 t4 t5 t6 mv F1 FLG w8 j8 h1);
          first [exact MIv| exact STv| exact LFv| exact FCv| exact FCFv| exact FSv| exact FLC| exact F128| exact FBLK| exact FTOP| exact GBLK| exact GTOP| exact GF| exact FLEv| exact RFv| exact RFSv| exact RG]. }
      cbv beta. intros ms7 (mp & m7 & y0 & -> & MUP & WMP & MIP & MU7 & WM7 & MI7 & ST7 & FLC7).
      (* [comment removed for export] *)
      assert (AHp : AHL AI fflag rng_fs K (lay b A cap k) RNGv (aps_m sv) (mkABlock (ABFake 1) F1 128 :: blc b A cap ++ LB) mp).
      { eapply (lk_perm _ _ _ K); [apply Permutation.Permutation_sym; apply Permutation.Permutation_middle|].
        eapply (lk_frame _ _ _ K); [exact AHv| exact MUP| exact WMP|].
        constructor; [| constructor; [| constructor]]; cbn [fst snd].
        - right; right. right; right. exists 1, F1, 128. split; [exact INF|]. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia.
        - eapply aclient_range_fake; [exact INF| lia| lia]. }
      pose proof (lk_fake_release _ _ _ K _ _ _ _ _ _ _ _ AHp) as AHr. rewrite lay_fflag in AHr. fold FLG in AHr.
      rewrite <- (mem_eq_single mp m7 FLG (Z_to_bv 8 0) ltac:(lia) ltac:(lia) MU7 (byte_of_c1 _ _ _ FLC7 ltac:(lia))) in AHr. clear AHp.
      (* [comment removed for export] *)
      assert (AG7 : magree bsegs lam_px m0 m7).
      { eapply magree_trans; [exact AGv|]. eapply magree_trans.
        - eapply magree_mono; [eapply magree_of_munch; [exact MUP| exact WMP]|]. intros a [Ha _]. cbn [outside].
          destruct (lam_outsideL _ _ _ _ F1 a _ AHv INF INCL FBLK F8 Ha) as (O1 & O2 & O3). clear - O2 O3. lia.
        - eapply magree_mono; [eapply magree_of_munch; [exact MU7| exact WM7]|]. intros a [Ha HR]. cbn [outside]. split; [| exact I].
          destruct Ha as [X|[(iv & Hiv & Hr)|[(b0 & Hb & Hr)|(a' & Ha' & ->)]]].
          + clear - X GTOP LOA LOS'. lia.
          + intros [X1 X2]. apply GCI. exists iv. split; [exact Hiv| clear - Hr X1 X2; lia].
          + pose proof (GDJ _ (INCL _ Hb)) as Y. unfold in_block in Hr. clear - Y Hr. lia.
          + rewrite shad_div. unfold ASHOFF. assert (0 <= a' < 2^47).
            { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [clear - X ATR; lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
              pose proof (lk_block_bounds _ _ _ K _ _ _ _ _ _ AHv (INCL _ Hb')) as Bb. cbn [ab_addr ab_size] in Bb. unfold AIMG_HI in Bb. clear - Bb Hr ATR. lia. }
            clear - H GNS. Z.div_mod_to_equations. lia. }
      destruct (lam_refresh m7 AG7 (lk_relro _ _ _ K _ _ _ _ _ AHr) MI7) as (CC7 & CS7 & RSH7 & _ & IMG7 & USH7 & _).
      (* [comment removed for export] *)
      pose proof RCv as RCp. xrw RCp MUP WMP. pose proof RCp as RC7. xrw RC7 MU7 WM7. clear RCp.
      (* [comment removed for export] *)
      apply evtF_done. unfold lambda_post. split; [exact FLEv|].
      do 15 eexists. exists m7, A, k, cap. split; [reflexivity|].
      split; [exact MI7|]. split; [exact ST7|]. split; [exact ARSv|]. split; [exact CLv|].
      split. { intros a Ha Hc Hx. apply AG7; [exact Ha| split; [exact Hc| exact Hx]]. }
      split; [split; [exact IMG7| exact USH7]|].
      split; [exact CC7|]. split; [exact CS7|]. split; [exact RC7|]. split; [exact RSH7|]. split; [exact KC|].
      destruct b as [p|].
      - destruct BLK as (CAP & BR & RA & RSA & OUTv). cbn [blc app] in AHr.
        pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
        assert (ANS : A + cap <= KLS \/ 0x10007fff8000 <= A) by (apply ablk_disj_band; exact BR1). unfold KLS in ANS.
        assert (A8 : A mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
        assert (GA : exists G, granules cap = G /\ 0 <= G /\ 8 * G <= cap + 7) by (exists (granules cap); rewrite granules_div by lia; clear - CAP; Z.div_mod_to_equations; lia).
        destruct GA as (G & EG & G0 & G8). rewrite EG in OUTv |- *.
        assert (SHA : 2148345856 <= shad A /\ shad A + G <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - BL1 BR3 ATR G8 CAP; Z.div_mod_to_equations; lia).
        pose proof AHv as AHv'. cbn [blc app] in AHv'.
        assert (IN1 : In (HB p A cap) (HB p A cap :: mkABlock (ABFake 1) F1 128 :: LB)) by (left; reflexivity).
        assert (IN2 : In (mkABlock (ABFake 1) F1 128) (HB p A cap :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; left; reflexivity).
        pose proof (lk_blocks_disjoint _ _ _ K _ _ _ _ _ _ _ AHv' IN1 IN2 ltac:(discriminate)) as DAF. cbn [ab_addr ab_size] in DAF.
        assert (SHAF : shad A + G <= shad F1 \/ shad F1 + 16 <= shad A) by (rewrite !shad_div; clear - DAF A8 F8 G8 CAP; Z.div_mod_to_equations; lia).
        pose proof (GDJ _ ltac:(apply in_or_app; left; left; reflexivity)) as GA'. cbn [ab_addr ab_size] in GA'.
        assert (OUTp : rw_cells bsegs mp (shad A) [CB (Z.to_nat G) (vpat cap k)])
          by (eapply rw_cells_transport; [exact OUTv| exact MUP| exact WMP| cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - SHAF SHA FNS; lia]).
        assert (OUT7 : rw_cells bsegs m7 (shad A) [CB (Z.to_nat G) (vpat cap k)])
          by (eapply rw_cells_transport; [exact OUTp| exact MU7| exact WM7| cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - GNS SHA; lia]).
        split; [exact CAP|]. split; [exact BR|]. split; [exact AHr|]. split; [exact OUT7|]. split; [exact RA| rewrite <- EG; exact RSA].
      - destruct BLK as [EA EC]. split; [exact EA|]. split; [exact EC|]. cbn [blc app] in AHr. exact (lk_to_AI _ _ _ K _ _ _ _ _ AHr TIGHT).
    Qed.

    (* [comment removed for export] *)
    Lemma lam_tail : forall (RNGv : footprint) (sv : APS) (mv : amem) (F1 : Z) (j8 : list byte) (junk : list byte) (b : option AsanCtrl.aptr) (A : Z)
        (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      fp_le RNG RNGv ->
      AHEAP AI L RNGv (aps_m sv) (bl b A ++ mkABlock (ABFake 1) F1 128 :: LB) mv ->
      aps_rest sv = aps_rest s -> aps_cl sv = aps_cl s ->
      magree bsegs lam_px m0 mv ->
      mem_inv bsegs mv -> stk bsegs mv lo SPL ->
      rw_cells bsegs mv SPL (LFR [C8 (Z_to_bv 64 F1); CB 8 j8] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
      rw_cells bsegs mv F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F1))] ->
      rw_cells bsegs mv (shad F1) lamsh1 ->
      F1 mod 128 = 0 -> ablk F1 (F1 + 128) -> F1 + 128 <= ATOP -> (R + 24 <= F1 \/ F1 + 128 <= R) ->
      rng RNGv F1 128 -> rng RNGv (shad F1) 16 ->
      rw_cells bsegs mv R [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 (A + n))] ->
      match b with
      | None => A = 0 /\ n = 0
      | Some p => ablock_range A n /\ 0 < n /\ rng RNGv A n /\ rng RNGv (shad A) (shlen (n + 7))
                  /\ rw_cells bsegs mv A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
      end ->
      implMA RNGv (if unclosed payload then t <- opnewA ERRSTR_BYTES ;; b' <- assignA n b ;; opdeleteA t ;;; mret b' else mret b) sv POST
        (MS (mkR (Z_to_bv 64 0xb1da0) (Z_to_bv 64 SPL) gp tp t0 t1 t2 sp (Z_to_bv 64 SPL)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 F1) (Z_to_bv 64 R) (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 C) (Z_to_bv 64 (C + 8)) (Z_to_bv 64 (F1 + 32))
                 (Z_to_bv 64 (shad F1)) (Z_to_bv 64 F1) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (shad C + 1)) t3 t4 t5 t6)
            F (Z_to_bv 64 0xb1da0) fc None mv (seg_rom bsegs)).
    Proof.
      intros until t6. intros FLEv AHv ARSv CLv AGv MIv STv LFv FCv FSv F128 FBLK FTOP DJRF RFv RFSv RCv BLK.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & SHC8 & SHC0 & SHCLO & SHCHI). pose proof atop_range as ATR.
      assert (USPL : bv_unsigned (Z_to_bv 64 SPL) = SPL) by (apply unsigned_lit; clear - RSP LOS' LO0; lia).
      assert (URET : bv_unsigned (Z_to_bv 64 ALAM_STRDEL_RET) = ALAM_STRDEL_RET) by (apply unsigned_lit; unfold ALAM_STRDEL_RET; clear; lia).
      pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
      pose proof (ablk_lin _ _ RBLK) as (RL1 & RL2 & RL3 & RL4). unfold AIMG_HI in RL1.
      assert (RNS : R + 24 <= KLS \/ 0x10007fff8000 <= R) by (apply ablk_disj_band; exact RBLK). unfold KLS in RNS.
      pose proof (ablk_lin _ _ FBLK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
      assert (F8 : F1 mod 8 = 0) by (clear - F128; Z.div_mod_to_equations; lia).
      assert (FNS : F1 + 128 <= KLS \/ 0x10007fff8000 <= F1) by (apply ablk_disj_band; exact FBLK). unfold KLS in FNS.
      assert (SHF : 2148345856 <= shad F1 /\ shad F1 + 16 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - FL1 FL3 ATR; Z.div_mod_to_equations; lia).
      assert (INF : In (mkABlock (ABFake 1) F1 128) (bl b A ++ mkABlock (ABFake 1) F1 128 :: LB)) by (apply in_or_app; right; left; reflexivity).
      assert (INCL : forall b0, In b0 LB -> In b0 (bl b A ++ mkABlock (ABFake 1) F1 128 :: LB)) by (intros b0 Hb; apply in_or_app; right; right; exact Hb).
      pose proof (rng_fp_le _ _ _ _ FLEv RSTK) as RSTKv. pose proof (rng_fp_le _ _ _ _ FLEv RI) as RIv. pose proof (rng_fp_le _ _ _ _ FLEv RISH) as RISHv.
      pose proof (rng_fp_le _ _ _ _ FLEv RV) as RVv. pose proof (rng_fp_le _ _ _ _ FLEv RVS) as RVSv. pose proof (rng_fp_le _ _ _ _ FLEv RCL) as RCLv. pose proof (rng_fp_le _ _ _ _ FLEv RCS) as RCSv.
      destruct (lam_refresh mv AGv (AI_relro AI _ _ _ _ _ AHv) MIv) as (CCv & CSv & RSHv & FBKv & IMGv & USHv & UCHv & _).
      (* [comment removed for export] *)
      assert (AF : 0 <= A /\ A + n <= ATOP /\ A mod 8 = 0 /\ (A + n <= 2147446784 \/ 17594333495296 <= A) /\ (A + n <= F1 \/ F1 + 128 <= A) /\ (A + n <= R \/ R + 24 <= A)).
      { destruct b as [p|].
        - destruct BLK as ((BR1 & BR2 & BR3 & BR4) & NP & _). pose proof (ablk_disj_band _ _ BR1) as X. unfold KLS in X.
          pose proof AHv as AHv'. cbn [bl app] in AHv'.
          assert (IN1 : In (mkABlock (ABFake 1) F1 128) (mkABlock (ABFake 1) F1 128 :: LB)) by (left; reflexivity).
          assert (IN2 : In (mkABlock (ABFake cls) FA FN) (mkABlock (ABFake 1) F1 128 :: LB)) by (right; exact FIN).
          pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AHv' IN1) as D1. cbn [ab_addr ab_size] in D1.
          pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AHv' IN2) as D2. cbn [ab_addr ab_size] in D2. clear AHv' IN1 IN2.
          pose proof (ablk_lin _ _ BR1) as (B1 & B2 & B3 & B4).
          repeat split; [clear - B2; lia| exact BR3| clear - BR4; Z.div_mod_to_equations; lia| exact X| clear - D1; lia| clear - D2 FR1 FR2; lia].
        - destruct BLK as [-> N0]. rewrite N0. clear - FL1 RL1 ATR. repeat split; lia. }
      destruct AF as (A0 & ATOPA & A8 & ANS & DJAF & DJAR).
      apply implMA_from_evtF.
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (lam_mid RNGv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mv F1 (CB 8 j8) junk A (A + n) (A + n));
          first [exact STv| exact MIv| exact FCv| exact FSv| exact F128| exact FBLK| exact FTOP| exact DJRF| exact CCv| exact CSv| exact RCv| exact RSHv| exact FBKv| exact IMGv| exact USHv| exact FLEv| exact RFv| exact RFSv]. }
      cbv beta. intros ms5 (m5 & y5 & y6 & y7 & j8' & j80 & -> & MU5 & WM5 & MI5 & FC5 & FS5 & ST5).
      assert (AH5 : AHEAP AI L RNGv (aps_m sv) (bl b A ++ mkABlock (ABFake 1) F1 128 :: LB) m5).
      { eapply (AI_frame AI); [exact AHv| exact MU5| exact WM5|].
        constructor; [| constructor; [| constructor]]; cbn [fst snd].
        - right; right. right; right. exists 1, F1, 128. split; [exact INF|]. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia.
        - eapply aclient_range_fake; [exact INF| lia| lia]. }
      assert (AG5 : magree bsegs lam_px m0 m5).
      { eapply magree_trans; [exact AGv|]. eapply magree_mono; [eapply magree_of_munch; [exact MU5| exact WM5]|]. intros a [Ha _]. cbn [outside].
        destruct (lam_outside _ _ _ _ F1 a AHv INF INCL FBLK F8 Ha) as (O1 & O2 & O3). clear - O2 O3. lia. }
      pose proof LFv as LF5. xrwby LF5 MU5 WM5 by (clear - SHF ATR LOA LOS' FTOP; lia). pose proof RCv as RC5. xrwby RC5 MU5 WM5 by (clear - SHF RNS DJRF; lia).
      clear CCv CSv RSHv FBKv IMGv USHv UCHv.
      destruct (lam_refresh m5 AG5 (AI_relro AI _ _ _ _ _ AH5) MI5) as (CC5 & CS5 & RSH5 & FBK5 & IMG5 & USH5 & UCH5 & _).
      (* [comment removed for export] *)
      assert (PF : bytes_at bsegs m5 D (map (Z_to_bv 8) payload) /\ unpoisoned m5 D (D + n) /\ rng RNGv D n /\ rng RNGv (shad D) (nshad n)
                   /\ 0 <= D /\ D + n <= lo /\ (A + n <= D \/ D + n <= A)).
      { destruct PAT as [(pD & HINp & NP)|(PL0 & ->)].
        - destruct (AI_block AI _ _ _ _ _ _ _ _ AH5 (INCL _ HINp)) as (_ & (PB1 & PB2 & PB3 & PB4) & RD & RSD & _).
          pose proof (ablk_lin _ _ PB1) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
          pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HINp FIN ltac:(discriminate)) as DJP. cbn [ab_addr ab_size] in DJP.
          split. { eapply bytes_at_magree; [exact AG5| exact PBY|]. rewrite map_length. intros a Ha. unfold zlength in *.
                   split; [right; right; left; exists (HB pD D n); split; [exact HINp| cbn; unfold zlength; lia]| clear - Ha DJP FR1 FR2; lia]. }
          split. { destruct (blk_window_facts AI _ _ _ _ _ _ _ _ D n AH5 (INCL _ HINp) ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & U & _). exact U. }
          split; [exact RD|]. split; [unfold nshad; unfold shlen in RSD; exact RSD|]. split; [exact PL2|]. split; [clear - PB3 LOA; lia|].
          destruct b as [p|]; [| destruct BLK as [-> N0]; rewrite N0; clear - PL2; lia].
          pose proof AHv as AHv'. cbn [bl app] in AHv'.
          assert (IN3 : In (HB pD D n) (mkABlock (ABFake 1) F1 128 :: LB)) by (right; exact HINp).
          pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AHv' IN3) as D3. cbn [ab_addr ab_size] in D3. clear - D3. lia.
        - assert (N0 : n = 0) by (rewrite PL0; reflexivity). rewrite N0, PL0. unfold AEMPTY. cbn [map].
          split; [split; [lia| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]|].
          split; [apply unpoisoned_nil; lia|].
          split; [eapply rng_sub'; [exact RIv| clear; lia]|].
          split; [eapply rng_sub'; [exact RISHv| clear; split; apply Z.leb_le; vm_compute; reflexivity]|].
          split; [lia|]. split; [clear - LOA ATR; lia| clear - A0 N0; lia]. }
      destruct PF as (PBY5 & UNPD & RD & RSD & DLO & DLE & TD).
      assert (TF : unpoisoned m5 A (A + n) /\ wr_at bsegs m5 A n).
      { destruct b as [p|].
        - pose proof AH5 as AH5'. cbn [bl app] in AH5'.
          destruct (blk_window_facts AI _ _ _ _ _ _ _ _ A n AH5' ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & U & _).
          destruct (AI_block AI _ _ _ _ _ _ _ _ AH5' ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & W & _). split; [exact U| exact W].
        - destruct BLK as [-> N0]. rewrite N0. split; [apply unpoisoned_nil; lia| split; [lia| split; [lia| intros; lia]]]. }
      destruct TF as [UNPT WT].
      (* [comment removed for export] *)
      assert (RSC : (exists r0, rw_cells bsegs m5 (F1 + 32) [C8 r0]) /\ rw_cells bsegs m5 (Z.shiftr (F1 + 32) 3 + 2147450880) [C1 (Z_to_bv 8 0)]).
      { split.
        - exists (Z_to_bv 64 0). pose proof FC5 as X.
          change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 0); CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))])
            with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'] ++ [C8 (Z_to_bv 64 0)] ++ [CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))]) in X.
          apply rw_cells_app_split in X as [_ X]. apply rw_cells_app_split in X as [X _]. cbn [cells_size csize Nat.add] in X.
          replace (F1 + Z.of_nat 32) with (F1 + 32) in X by lia. exact X.
        - pose proof FS5 as X. unfold lamsh2 in X.
          change ([C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 BF2; C1 BF2; C1 BF2; C1 BF8; C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3])
            with ([C1 BF1; C1 BF1; C1 BF1; C1 BF1] ++ [C1 B00] ++ [C1 BF2; C1 BF2; C1 BF2; C1 BF8; C1 BF8; C1 BF8; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3]) in X.
          apply rw_cells_app_split in X as [_ X]. apply rw_cells_app_split in X as [X _]. cbn [cells_size csize Nat.add] in X.
          replace (shad F1 + Z.of_nat 4) with (Z.shiftr (F1 + 32) 3 + 2147450880) in X by (rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; clear - F8; Z.div_mod_to_equations; lia).
          exact X. }
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH5) as (GOT5 & _ & _ & SHB5 & _).
      assert (RRS : rng RNGv (F1 + 32) 8) by (eapply rng_sub'; [exact RFv| clear; lia]).
      assert (RRSS : rng RNGv (Z.shiftr (F1 + 32) 3 + 2147450880) 1)
        by (eapply rng_sub'; [exact RFSv| rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; clear - F8; Z.div_mod_to_equations; lia]).
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ ?msq =>
        assert (MCALL : evtF bsegs RNGv (mf_post (Z_to_bv 64 0xb1e20) (Z_to_bv 64 SPL) gp tp sp (Z_to_bv 64 SPL) (Z_to_bv 64 F1) (Z_to_bv 64 R) (Z_to_bv 64 AFALLBACK) (Z_to_bv 64 C)
                                            (Z_to_bv 64 (C + 8)) (Z_to_bv 64 (F1 + 32)) (Z_to_bv 64 (shad F1)) (Z_to_bv 64 F1) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (shad C + 1)) F fc m5 A (F1 + 32) payload lo) msq) end.
      { destruct b as [p|].
        - (* [comment removed for export] *)
          destruct BLK as (BR & NP & RA & RSA & _).
          pose proof (proj1 (ablk_lin _ _ (proj1 BR))) as BL1. unfold AIMG_HI in BL1.
          assert (DPOS : 0 < D).
          { destruct PAT as [(pD & HINp & _)|(PL0 & _)].
            - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HINp) as PB. cbn [ab_addr ab_size] in PB. unfold AIMG_HI in PB. clear - PB. lia.
            - exfalso. rewrite PL0 in NP. unfold zlength in NP. cbn [length] in NP. clear - NP. lia. }
          pose proof (client_img_x _ IMG5) as (_ & _ & JT5 & _).
          pose proof minify_proofA as MF. unfold minify_stmtA, MINIFY_STACK in MF.
          eapply (MF RNGv) with (lo := lo) (D := D) (DST := A) (RS := F1 + 32) (pl := payload); clear MF;
            try reflexivity; rewrite ?USPL, ?URET;
            first [ exact PBY5 | exact PRG | exact JT5 | exact UNPD | exact UNPT | exact RD | exact RSD | exact RSC | exact ST5 | exact MI5 | exact GOT5 | exact SHB5 | exact RIv | exact RISHv | exact WT | exact TD
                  | exact RA | exact RRS | exact RRSS | exact DPOS
                  | (eapply rng_sub'; [exact RFSv| rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; clear - F8; Z.div_mod_to_equations; lia])
                  | (unfold nshad; unfold shlen in RSA; exact RSA)
                  | (apply ajt_unpoisoned; apply client_img_x; exact IMG5)
                  | exact A8 | exact NLT | exact DLE
                  | (clear - D16; Z.div_mod_to_equations; lia)
                  | (clear - F8; Z.div_mod_to_equations; lia)
                  | (unfold KHIGH; clear - LOA ATR; lia)
                  | (eapply rng_sub'; [exact RSTKv| clear - LOS' LO0 STOP LY3 RSP; lia])
                  | (clear - ATOPA LOA; lia)
                  | (unfold KLOW, KHIGH; clear - ANS; lia)
                  | (clear - DJAF; lia)
                  | (left; unfold AJT; clear - BL1; lia)
                  | (clear - BL1; lia)
                  | (unfold KEND; clear - ATOPA ATR A0 NLT; lia)
                  | (unfold KEND; clear - DLE LOA ATR LOS' RSP; lia)
                  | (clear - FL2; lia)
                  | (unfold KEND; clear - FL3 ATR; lia)
                  | (clear - FL3 LOA; lia)
                  ].
        - (* [comment removed for export] *)
          destruct BLK as [EA N0]. destruct RSC as [[rw0 RSW0] RSS0].
          assert (PL0 : payload = []) by (destruct payload; [reflexivity| unfold zlength in N0; cbn [length] in N0; lia]).
          rewrite PL0, EA.
          eapply (minify_nilA RNGv) with (lo := lo) (RS := F1 + 32) (D := 0); try reflexivity; rewrite ?USPL, ?URET;
            first [ exact GOT5 | exact SHB5 | exact RIv | exact RRS | exact RRSS | exact RSW0 | exact RSS0 | exact ST5 | exact MI5
                  | (unfold KHIGH; clear - LOA ATR; lia)
                  | (eapply rng_sub'; [exact RSTKv| clear - LOS' LO0 STOP LY3 RSP; lia])
                  | (clear - F8; Z.div_mod_to_equations; lia)
                  | (unfold KLS, KHIGH; clear - FNS; lia)
                  | (rewrite PL0; reflexivity)
                  | (clear - LOS'; lia) | (clear - STOP LY3; lia) | (clear - FL2; lia) | (clear - FL3 LOA; lia)
                  ]. }
      eapply evtF_cut; [exact MCALL|]. clear MCALL. cbv beta. unfold mf_post. intros ms6 PO6.
      destruct PO6 as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & z5 & z6 & z7 & x3 & x4 & x5 & x6 & m6 & pos & -> & POS & RSW & MU6 & WM6 & MI6 & ST6).
      rewrite ?USPL, ?URET in MU6, ST6. retlit.
      (* [comment removed for export] *)
      assert (AH6 : AHEAP AI L RNGv (aps_m sv) (bl b A ++ mkABlock (ABFake 1) F1 128 :: LB) m6).
      { destruct b as [p|].
        - eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|].
          constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd bl app].
          + apply aclient_range_stack; clear - RSP LOA LOS'; lia.
          + right; left. exists (HB p A n). split; [left; reflexivity| cbn; lia].
          + eapply aclient_range_fake; [exact INF| lia| lia].
        - destruct BLK as [EA N0].
          assert (MU6' : munch [(SPL - 32, SPL); (F1 + 32, F1 + 32 + 8)] m5 m6)
            by (eapply munch_weaken; [| exact MU6]; unfold sub_fp; cbn [outside]; rewrite EA, N0; intros; lia).
          eapply (AI_frame AI); [exact AH5| exact MU6'| exact WM6|].
          constructor; [| constructor; [| constructor]]; cbn [fst snd bl app].
          + apply aclient_range_stack; clear - RSP LOA LOS'; lia.
          + eapply aclient_range_fake; [exact INF| lia| lia]. }
      assert (AG6 : magree bsegs lam_px m0 m6).
      { eapply magree_trans; [exact AG5|]. eapply magree_mono; [eapply magree_of_munch; [exact MU6| exact WM6]|]. intros a [Ha HR]. cbn [outside].
        destruct (lam_outside _ _ _ _ F1 a AH5 INF INCL FBLK F8 Ha) as (O1 & O2 & O3).
        assert (OA : ~ (A <= a < A + n)).
        { destruct b as [p|]; [| destruct BLK as [-> N0]; rewrite N0; clear; lia].
          pose proof AH5 as AH5'. cbn [bl app] in AH5'.
          assert (INCLF : forall b0, In b0 LB -> In b0 (mkABlock (ABFake 1) F1 128 :: LB)) by (intros b0 Hb; right; exact Hb).
          pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ SPA a AH5' ltac:(clear - LOA LOS'; lia) ltac:(eapply aclient_addr_mono_lb; [exact Ha| exact INCLF])) as Y. clear - Y. lia. }
        clear - O1 O2 OA LOS'. lia. }
      pose proof LF5 as LF6. xrwby LF6 MU6 WM6 by (clear - ATOPA LOA LOS' FTOP; lia). pose proof RC5 as RC6. xrwby RC6 MU6 WM6 by (clear - RL3 LOA LOS' DJAR DJRF; lia). pose proof FS5 as FS6. xrwby FS6 MU6 WM6 by (clear - SHF ATR LOA LOS' ANS FNS; lia).
      (* [comment removed for export] *)
      assert (FC6 : rw_cells bsegs m6 F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))]).
      { pose proof FC5 as X.
        change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 0); CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))])
          with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'] ++ [C8 (Z_to_bv 64 0)] ++ [CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))]) in X.
        apply rw_cells_app_split in X as [X1 X]. apply rw_cells_app_split in X as [_ X3]. cbn [cells_size csize Nat.add] in X1, X3.
        xrwby X1 MU6 WM6 by (clear - FTOP LOA LOS' DJAF; lia). xrwby X3 MU6 WM6 by (clear - FTOP LOA LOS' DJAF; lia).
        change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))])
          with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'] ++ [C8 (Z_to_bv 64 pos)] ++ [CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))]).
        apply rw_cells_app_join; [exact X1|]. cbn [cells_size csize Nat.add]. apply rw_cells_app_join; [replace (F1 + Z.of_nat 32) with (F1 + 32) by lia; exact RSW|].
        cbn [cells_size csize Nat.add]. replace (F1 + Z.of_nat 32 + Z.of_nat 8) with (F1 + Z.of_nat 32 + Z.of_nat 8) by lia. exact X3. }
      clear CC5 CS5 RSH5 FBK5 IMG5 USH5 UCH5 LF5 RC5 FS5 FC5.
      destruct (lam_refresh m6 AG6 (AI_relro AI _ _ _ _ _ AH6) MI6) as (CC6 & CS6 & RSH6 & FBK6 & IMG6 & USH6 & UCH6 & _).
      destruct (unclosed payload) eqn:UC.
      { (* [comment removed for export] *)
        destruct b as [p|]; [| destruct BLK as [_ N0]; exfalso;
          assert (PL0 : payload = []) by (destruct payload; [reflexivity| unfold zlength in N0; cbn [length] in N0; lia]); rewrite PL0 in UC; discriminate].
        destruct BLK as (BR & NP & RA & RSA & _). pose proof BR as (BR1 & BR2 & BR3 & BR4).
        pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
        (* [comment removed for export] *)
        eapply evtF_cut.
        { eapply (lam_err1 RNGv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 F1); first [exact MI6| exact ST6| exact FS6| exact F128| exact FBLK| exact FTOP| exact IMG6| exact USH6| exact FLEv| exact RFSv]. }
        cbv beta. intros ms7 (m7 & y8 & y9 & -> & MU7 & WM7 & MI7 & FS7 & ST7).
        pose proof AH6 as AH6'. cbn [bl app] in AH6'.
        assert (IN1 : In (HB p A n) (HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)) by (left; reflexivity).
        assert (IN2 : In (mkABlock (ABFake 1) F1 128) (HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; left; reflexivity).
        assert (AH7 : AHEAP AI L RNGv (aps_m sv) (HB p A n :: mkABlock (ABFake 1) F1 128 :: LB) m7).
        { eapply (AI_frame AI); [exact AH6'| exact MU7| exact WM7|]. constructor; [| constructor]. cbn [fst snd].
          right; right. right; right. exists 1, F1, 128. split; [exact IN2|]. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
        assert (AG7 : magree bsegs lam_px m0 m7).
        { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU7| exact WM7]|]. intros a [Ha _]. cbn [outside].
          destruct (lam_outside _ _ _ _ F1 a AH6 INF INCL FBLK F8 Ha) as (_ & _ & O3). clear - O3. lia. }
        pose proof LF6 as LF7. xrwby LF7 MU7 WM7 by (clear - SHF ATR LOA LOS'; lia). pose proof RC6 as RC7. xrwby RC7 MU7 WM7 by (clear - SHF RNS; lia). pose proof FC6 as FC7. xrwby FC7 MU7 WM7 by (clear - SHF FNS; lia).
        clear CC6 CS6 RSH6 FBK6 USH6 UCH6.
        destruct (lam_refresh m7 AG7 (AI_relro AI _ _ _ _ _ AH7) MI7) as (_ & _ & _ & _ & IMG7 & _ & _ & _).
        (* [comment removed for export] *)
        assert (TC7 : exists (w0 w1 w2 : word) (ja jb : list byte),
                  rw_cells bsegs m7 F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja]
                  /\ rw_cells bsegs m7 (F1 + 64) [C8 w0; C8 w1; C8 w2]
                  /\ rw_cells bsegs m7 (F1 + 88) [CB 32 jb; C8 (Z_to_bv 64 (fflag L 1 F1))]).
        { pose proof FC7 as X.
          apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos)] 80 j80 [C8 (Z_to_bv 64 (fflag L 1 F1))] [24;24;32]%nat) in X; [| reflexivity].
          cbn [mk_CB_cells app] in X.
          change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 (firstn 24 j80); CB 24 (firstn 24 (skipn 24 j80)); CB 32 (firstn 32 (skipn 24 (skipn 24 j80))); C8 (Z_to_bv 64 (fflag L 1 F1))])
            with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 (firstn 24 j80)] ++ [CB 24 (firstn 24 (skipn 24 j80))] ++ [CB 32 (firstn 32 (skipn 24 (skipn 24 j80))); C8 (Z_to_bv 64 (fflag L 1 F1))]) in X.
          apply rw_cells_app_split in X as [X1 X]. apply rw_cells_app_split in X as [X2 X3]. cbn [cells_size csize Nat.add] in X2, X3.
          replace (F1 + Z.of_nat 64) with (F1 + 64) in X2 by lia. replace (F1 + Z.of_nat 64 + Z.of_nat 24) with (F1 + 88) in X3 by lia.
          destruct (cb24_words _ _ _ X2) as (w0 & w1 & w2 & TW). exists w0, w1, w2, (firstn 24 j80), (firstn 32 (skipn 24 (skipn 24 j80))). split; [exact X1| split; [exact TW| exact X3]]. }
        destruct TC7 as (tw0 & tw1 & tw2 & ja & jb & FCh7 & TC7 & FCt7). clear FC7.
        assert (TSH7 : rw_cells bsegs m7 (shad (F1 + 64)) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
        { pose proof FS7 as X. unfold lamsh3 in X.
          change ([C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 BF2; C1 BF2; C1 BF2; C1 B00; C1 B00; C1 B00; C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3])
            with ([C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B00; C1 BF2; C1 BF2; C1 BF2] ++ [C1 B00; C1 B00; C1 B00] ++ [C1 BF3; C1 BF3; C1 BF3; C1 BF3; C1 BF3]) in X.
          apply rw_cells_app_split in X as [_ X]. apply rw_cells_app_split in X as [X _]. cbn [cells_size csize Nat.add] in X.
          replace (shad F1 + Z.of_nat 8) with (shad (F1 + 64)) in X by (rewrite !shad_div; clear - F8; Z.div_mod_to_equations; lia). exact X. }
        apply evtF_done.
        (* [comment removed for export] *)
        eapply implMA_bind.
        { eapply implMA_cl; [apply cl_stable_opnew|].
          eapply (astrctor_proof AI ONTA IMG_CI) with (lo := lo) (L := L) (LB := HB p A n :: mkABlock (ABFake 1) F1 128 :: LB) (T := F1 + 64) (cls := 1) (FA := F1) (FN := 128);
            try reflexivity; rewrite ?USPL, ?URET;
            first [ exact AH7 | exact MI7 | exact ST7 | exact LOA | exact TP | exact IN2 | exact TC7 | exact TSH7 | exact HUN | exact RSTKv | exact RIv | exact RISHv
                  | (apply client_img_x; exact IMG7)
                  | (destruct (client_img_x _ IMG7) as (_ & _ & X); exact X)
                  | (unfold ASTRCTOR_STACK, OPNEW_STACK_A, AMALLOC_STACK; clear - LOS'; lia)
                  | (clear - STOP; lia)
                  | (clear - SPL32; Z.div_mod_to_equations; lia)
                  | (clear - F128; Z.div_mod_to_equations; lia)
                  | (eapply ablk_sub; [exact FBLK| lia| lia])
                  | (eapply rng_sub'; [exact RFv| clear; lia])
                  | (eapply rng_sub'; [exact RFSv| rewrite !shad_div; clear - F8; Z.div_mod_to_equations; lia])
                  | (eapply aps_ok_rest; [exact ARSv| exact AOK])
                  ]. }
        cbv beta. intros t ss RNGs ms8 [PO8 CL8].
        destruct PO8 as (FLE8 & u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & m8 & P & jb56 & -> & MI8 & ST8 & ARS8 & PBR & HPX8 & AH8 & TC8 & TSH8 & STRB8 & RPv & RPS).
        rewrite ?USPL, ?URET in ST8, HPX8. retlit.
        pose proof (fp_le_trans _ _ _ FLEv FLE8) as FLE8'.
        pose proof (rng_fp_le _ _ _ _ FLE8 RFv) as RF8. pose proof (rng_fp_le _ _ _ _ FLE8 RFSv) as RFS8. pose proof (rng_fp_le _ _ _ _ FLE8 RSTKv) as RSTK8.
        pose proof (rng_fp_le _ _ _ _ FLE8 RIv) as RI8. pose proof (rng_fp_le _ _ _ _ FLE8 RVv) as RV8. pose proof (rng_fp_le _ _ _ _ FLE8 RVSv) as RVS8.
        pose proof (rng_fp_le _ _ _ _ FLE8 RA) as RA8. pose proof (rng_fp_le _ _ _ _ FLE8 RSA) as RSA8.
        pose proof PBR as (PB1 & PB2 & PB3 & PB4). pose proof (ablk_lin _ _ PB1) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
        assert (PNS : P + 56 <= KLS \/ 0x10007fff8000 <= P) by (apply ablk_disj_band; exact PB1). unfold KLS in PNS.
        assert (IN3 : In (mkABlock (ABFake 1) F1 128) (HB t P 56 :: HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; right; left; reflexivity).
        assert (IN4 : In (HB p A n) (HB t P 56 :: HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; left; reflexivity).
        assert (IN5 : In (HB t P 56) (HB t P 56 :: HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)) by (left; reflexivity).
        pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH8 IN2) as DJPF. cbn [ab_addr ab_size] in DJPF.
        pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH8 IN1) as DJPA. cbn [ab_addr ab_size] in DJPA.
        pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH8 ltac:(right; right; exact FIN)) as DJPR. cbn [ab_addr ab_size] in DJPR.
        assert (INCLF : forall b0, In b0 LB -> In b0 (HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)) by (intros b0 Hb; right; right; exact Hb).
        assert (AG8 : magree bsegs lam_px m0 m8).
        { eapply magree_trans; [exact AG7|]. intros a Ha Hp. apply HPX8; [exact Ha| eapply lam_px_client; [exact Hp| exact INCLF| clear - LOS'; lia]|].
          destruct (lam_outside _ _ _ _ F1 a AH6 INF INCL FBLK F8 (proj1 Hp)) as (_ & O2 & _). clear - O2. lia. }
        assert (LF8 : rw_cells bsegs m8 SPL (LFR [C8 (Z_to_bv 64 F1); CB 8 j8] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
          by (eapply (aheap_pres_x_rw_cells CI); [exact HPX8| exact LF7| apply aclient_range_stack; cbn; clear - RSP; lia| cbn; clear - FTOP LOA LOS'; lia]).
        assert (RC8 : rw_cells bsegs m8 R [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 (A + n))])
          by (eapply (aheap_pres_x_rw_cells CI); [exact HPX8| exact RC7| eapply aclient_range_fake; [right; right; exact FIN| exact FR1| cbn; clear - FR2; lia]| cbn; clear - DJRF; lia]).
        assert (FCh8 : rw_cells bsegs m8 F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja])
          by (eapply (aheap_pres_x_rw_cells CI); [exact HPX8| exact FCh7| eapply aclient_range_fake; [exact IN2| lia| cbn; lia]| cbn; lia]).
        assert (FCt8 : rw_cells bsegs m8 (F1 + 88) [CB 32 jb; C8 (Z_to_bv 64 (fflag L 1 F1))])
          by (eapply (aheap_pres_x_rw_cells CI); [exact HPX8| exact FCt7| eapply aclient_range_fake; [exact IN2| lia| cbn; lia]| cbn; lia]).
        assert (FS8 : rw_cells bsegs m8 (shad F1) lamsh3).
        { eapply (aheap_pres_x_rw_cells CI); [exact HPX8| exact FS7| | cbn; clear - SHF FNS; lia].
          right; right. right; right. exists 1, F1, 128. split; [exact IN2|]. cbn. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
        clear IMG7 LF7 RC7 FCh7 FCt7 FS7 TC7 TSH7.
        destruct (lam_refresh m8 AG8 (AI_relro AI _ _ _ _ _ AH8) MI8) as (CC8 & CS8 & RSH8 & FBK8 & IMG8 & USH8 & UCH8 & WRH8).
        assert (STR8 : rw_cells bsegs m8 P [CB 54 errmsg]).
        { pose proof STRB8 as X. change [CB 54 errmsg; C1 (Z_to_bv 8 0); C1 jb56] with ([CB 54 errmsg] ++ [C1 (Z_to_bv 8 0); C1 jb56]) in X. apply rw_cells_app_split in X as [X _]. exact X. }
        (* [comment removed for export] *)
        pose proof (client_rt_of_aheap AI _ _ _ _ _ AH8) as (GOT8 & RIC8 & REAL8 & SHB8 & _ & INI8 & LAY8).
        destruct (AI_block AI _ _ _ _ _ _ _ _ AH8 IN4) as (CAP & _ & _ & _ & BSH8 & WA8 & _).
        pose proof (cells_of_ablock_shadow m8 A n ltac:(clear - NP; lia) ltac:(exact A0) ltac:(clear - ATOPA ATR; lia) BSH8) as FULL8.
        assert (AOKv : aps_ok L sv) by (eapply aps_ok_rest; [exact ARSv| exact AOK]).   (* [comment removed for export] *)
        destruct (Z_lt_le_dec n 54) as [NLT54|NGE54].
        - (* [comment removed for export] *)
          rewrite (assignA_realloc n (Some p)) by (unfold ERRMSG_LEN; clear - NLT54; lia).
          apply implMA_from_evtF.
          (* [comment removed for export] *)
          eapply evtF_cut.
          { eapply (lam_err2 RNGs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 F1 P); first [exact MI8| exact TC8| exact PL2| exact PB3| exact FL2| exact FTOP| exact FLE8'| exact RF8| (clear - PL1; lia)]. }
          cbv beta. intros ms9 (y10 & ->). apply evtF_done.
          (* [comment removed for export] *)
          eapply implMA_bind.
          { eapply implMA_cl; [apply cl_stable_bind; [apply cl_stable_odelete| intros []; apply cl_stable_bind; [apply cl_stable_opnew| intros ?; apply cl_stable_ret]]|].
            eapply (avassign_realloc_proof AI OD ONTA AI_kind AI_premap) with (lo := lo) (L := L) (LB := HB t P 56 :: HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)
                   (V := R) (beg := A) (n := n) (P := P) (pv := p) (ps := t) (cls := cls) (FA := FA) (FN := FN) (RLO2 := RLO2) (RHI2 := RHI2) (ULO := ULO) (UHI := UHI);
              try reflexivity; rewrite ?USPL, ?URET;
              first [ exact AH8 | exact IN4 | exact IN5 | exact MI8 | exact ST8 | exact LOA | exact TP | exact FR1 | exact FR2 | exact R8 | exact RBLK | exact RC8 | exact RSH8
                    | exact Q1 | exact Q2 | exact Q3 | exact Q4 | exact Q5 | exact Q6 | exact WRH8 | exact STR8 | exact HUD | exact HUN | exact RSTK8 | exact RI8 | exact RV8 | exact RVS8
                    | exact (lam_ush m8 AG8) | exact BU0 | exact BUL | exact BU47 | (eapply rng_fp_le; [exact FLE8'| exact BRUSH])      (* [comment removed for export] *)
                    | (clear - BUH; lia)
                    | (right; right; right; exact FIN)
                    | (eapply rng_fp_le; [exact FLE8'| exact RR2])
                    | (clear - NP NLT54; lia)
                    | (unfold AVASSIGN_STACK, AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK; clear - LOS'; lia)
                    | (clear - STOP; lia)
                    | (clear - SPL32; Z.div_mod_to_equations; lia)
                    | (eapply aps_ok_rest; [exact ARS8| exact AOKv]) ]. }
          cbv beta. intros b' sa RNGa ms10 [POa CLa].
          destruct POa as (FLEa & v0 & v1 & v2 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & v3 & v4 & v5 & v6 & m9 & A' & p' & -> & -> & MI9 & ST9 & ARS9 & BR' & HPX9 & AH9 & RC9 & RSH9 & BLK9 & OUT9 & SRC9 & RA9 & RSA9).
          rewrite ?USPL, ?URET in ST9, HPX9. retlit.
          rewrite (lb_remove_secondA p A n) in HPX9, AH9 by (exact (AI_hb_ids AI _ _ _ _ _ AH8)).
          pose proof (fp_le_trans _ _ _ FLE8' FLEa) as FLEa'.
          pose proof BR' as (NB1 & NB2 & NB3 & NB4). pose proof (ablk_lin _ _ NB1) as (NL1 & NL2 & NL3 & NL4). unfold AIMG_HI in NL1.
          assert (A8' : A' mod 8 = 0) by (clear - NB4; Z.div_mod_to_equations; lia).
          assert (SHA' : 2148345856 <= shad A' /\ shad A' + 7 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - NL1 NL3 ATR; Z.div_mod_to_equations; lia).
          assert (IN6 : In (mkABlock (ABFake 1) F1 128) (HB p' A' 54 :: HB t P 56 :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; right; left; reflexivity).
          assert (IN7 : In (HB t P 56) (HB p' A' 54 :: HB t P 56 :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; left; reflexivity).
          assert (IN8 : In (HB p' A' 54) (HB p' A' 54 :: HB t P 56 :: mkABlock (ABFake 1) F1 128 :: LB)) by (left; reflexivity).
          pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH9 ltac:(right; left; reflexivity)) as DJNF. cbn [ab_addr ab_size] in DJNF.
          pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH9 ltac:(right; right; exact FIN)) as DJNR. cbn [ab_addr ab_size] in DJNR.
          assert (SHAF' : shad A' + 7 <= shad F1 \/ shad F1 + 16 <= shad A') by (rewrite !shad_div; clear - DJNF A8' F8; Z.div_mod_to_equations; lia).
          assert (INCLT : forall b0, In b0 LB -> In b0 (HB t P 56 :: mkABlock (ABFake 1) F1 128 :: LB)) by (intros b0 Hb; right; right; exact Hb).
          assert (AG9 : magree bsegs lam_px m0 m9).
          { eapply magree_trans; [exact AG8|]. intros a Ha Hp. apply HPX9; [exact Ha| eapply lam_px_client; [exact Hp| exact INCLT| clear - LOS'; lia]| exact (proj2 Hp)]. }
          assert (IN3x : In (mkABlock (ABFake 1) F1 128) (HB t P 56 :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; left; reflexivity).   (* [comment removed for export] *)
          assert (LF9 : rw_cells bsegs m9 SPL (LFR [C8 (Z_to_bv 64 F1); CB 8 j8] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
            by (eapply (aheap_pres_x_rw_cells CI); [exact HPX9| exact LF8| apply aclient_range_stack; cbn; clear - RSP; lia| cbn; clear - RL3 LOA LOS'; lia]).
          assert (TC9 : rw_cells bsegs m9 (F1 + 64) [C8 (Z_to_bv 64 57); C8 (Z_to_bv 64 54); C8 (Z_to_bv 64 P)])
            by (eapply (aheap_pres_x_rw_cells CI); [exact HPX9| exact TC8| eapply aclient_range_fake; [exact IN3x| lia| cbn; lia]| cbn; clear - DJRF; lia]).
          assert (FCh9 : rw_cells bsegs m9 F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja])
            by (eapply (aheap_pres_x_rw_cells CI); [exact HPX9| exact FCh8| eapply aclient_range_fake; [exact IN3x| lia| cbn; lia]| cbn; clear - DJRF; lia]).
          assert (FCt9 : rw_cells bsegs m9 (F1 + 88) [CB 32 jb; C8 (Z_to_bv 64 (fflag L 1 F1))])
            by (eapply (aheap_pres_x_rw_cells CI); [exact HPX9| exact FCt8| eapply aclient_range_fake; [exact IN3x| lia| cbn; lia]| cbn; clear - DJRF; lia]).
          assert (FS9 : rw_cells bsegs m9 (shad F1) lamsh3).
          { eapply (aheap_pres_x_rw_cells CI); [exact HPX9| exact FS8| | cbn; clear - SHF RNS; lia].
            right; right. right; right. exists 1, F1, 128. split; [exact IN3x|]. cbn. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
          clear CC8 CS8 RSH8 FBK8 IMG8 USH8 UCH8 WRH8 LF8 TC8 FCh8 FCt8 FS8.
          destruct (lam_refresh m9 AG9 (AI_relro AI _ _ _ _ _ AH9) MI9) as (CC9 & CS9 & _ & FBK9 & IMG9 & USH9 & UCH9 & _).
          apply implMA_from_evtF.
          (* [comment removed for export] *)
          eapply evtF_cut.
          { eapply (lam_err3 RNGa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 F1 P); first [exact MI9| exact TC9| exact PL2| exact PB3| exact FL2| exact FTOP| exact FLEa'| eapply rng_fp_le; [exact FLEa| exact RF8]]. }
          cbv beta. intros ms11 (y2' & y3' & ->).
          assert (BFR : bytes_at bsegs m9 (SPA - 16) (le8 s0) /\ bytes_at bsegs m9 (SPA - 8) (le8 ra)).
          { pose proof LF9 as X. unfold LFR in X. cbn [app] in X.
            change ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F1); CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
              with ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F1); CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0] ++ [C8 ra]) in X.
            apply rw_cells_app_split in X as [_ X]. apply rw_cells_app_split in X as [X1 X2]. cbn [cells_size csize Nat.add] in X1, X2.
            pose proof (rw_cells_bytes_at _ _ _ _ X1) as B1. pose proof (rw_cells_bytes_at _ _ _ _ X2) as B2. cbn [cells_bytes cbytes app] in B1, B2. rewrite app_nil_r in B1, B2.
            replace (SPL + Z.of_nat 112) with (SPA - 16) in B1 by lia. replace (SPL + Z.of_nat 112 + Z.of_nat 8) with (SPA - 8) in B2 by lia. split; [exact B1| exact B2]. }
          destruct BFR as [BFP BRA].
          assert (UC9 : uchain m9 (al_top L) AFREE_PC SPL SPA UDEPTH (bv_unsigned ra :: tr)).
          { replace (bv_unsigned ra :: tr) with ((if bv_unsigned ra =? AFREE_PC then [] else [bv_unsigned ra]) ++ tr) by (rewrite (proj2 (Z.eqb_neq _ _) RAPC); reflexivity).
            pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RRA, RS0. cbn in RRA, RS0.
            eapply uc_step; [clear - RSP; lia| clear - STOP; lia| clear - SP32; Z.div_mod_to_equations; lia| unfold UDEPTH; clear; lia
                           | rewrite Z_to_bv_bv_unsigned; exact BFP| rewrite Z_to_bv_bv_unsigned; exact BRA| clear - RA12 RRA; lia| clear - RS0; lia|].
            rewrite (proj2 (Z.eqb_neq _ _) RAPC). exact UCH9. }
          apply evtF_done.
          (* [comment removed for export] *)
          destruct (lk_of_AI _ _ _ K _ _ _ _ _ AH9) as [AL9 TIGHT].
          eapply implMA_bind.
          { eapply implMA_cl; [apply cl_stable_opdelete|]. unfold opdeleteA.
            eapply (lk_opdel_sz _ _ _ K) with (lo := lo) (A := P) (n := 56) (tr := bv_unsigned ra :: tr); try reflexivity; rewrite ?USPL, ?URET;
              first [ exact AL9 | exact IN7 | exact MI9 | exact ST9 | exact LOA | exact TP | exact UC9 | exact HUS
                    | (eapply rng_fp_le; [exact FLEa| exact RSTK8])
                    | (unfold AFREE_STACK; clear - LOS'; lia) | (clear - STOP; lia) | (clear - RSP; lia)
                    | (unfold ALAM_STRDEL_RET; clear; lia) | (unfold ALAM_STRDEL_RET, AFREE_PC; clear; lia)
                    | (cbn [length]; clear - TRL; lia) | (clear - SPL32; Z.div_mod_to_equations; lia)
                    | (eapply aps_ok_rest; [rewrite ARS9; exact ARS8| exact AOKv]) ]. }
          cbv beta. intros [] sd RNGd ms12 [[ARSd POd] CLd].
          destruct POd as (FLEd & v0' & v1' & v2' & q0' & q1' & q2' & q3' & q4' & q5' & q6' & q7' & v3' & v4' & v5' & v6' & m10 & -> & MI10 & ST10 & HPR10 & AL10).
          rewrite ?USPL, ?URET in ST10, HPR10.
          replace (ret_pc (Z_to_bv 64 ALAM_STRDEL_RET)) with (Z_to_bv 64 ALAM_STRDEL_RET : word) by (symmetry; apply ret_pc_even; [unfold ALAM_STRDEL_RET; clear; lia| reflexivity]).   (* [comment removed for export] *)
          rewrite (lb_remove_secondA t P 56) in HPR10, AL10 by (exact (lk_hb_ids _ _ _ K _ _ _ _ _ AL9)).
          pose proof (fp_le_trans _ _ _ FLEa' FLEd) as FLEd'.
          assert (INCLN : forall b0, In b0 LB -> In b0 (HB p' A' 54 :: mkABlock (ABFake 1) F1 128 :: LB)) by (intros b0 Hb; right; right; exact Hb).
          assert (AG10 : magree bsegs lam_px m0 m10).
          { eapply magree_trans; [exact AG9|]. ag_of_hpr HPR10. eapply magree_mono; [exact HPR10|]. intros a Ha. eapply lam_px_client; [exact Ha| exact INCLN| clear - LOS'; lia]. }
          assert (IN9 : In (mkABlock (ABFake 1) F1 128) (HB p' A' 54 :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; left; reflexivity).
          assert (LF10 : rw_cells bsegs m10 SPL (LFR [C8 (Z_to_bv 64 F1); CB 8 j8] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
            by (eapply aheap_pres_rw_cells; [exact HPR10| exact LF9| apply aclient_range_stack; cbn; clear - RSP; lia]).
          assert (RC10 : rw_cells bsegs m10 R [C8 (Z_to_bv 64 A'); C8 (Z_to_bv 64 (A' + 54)); C8 (Z_to_bv 64 (A' + 54))])
            by (eapply aheap_pres_rw_cells; [exact HPR10| exact RC9| eapply aclient_range_fake; [right; right; exact FIN| exact FR1| cbn; clear - FR2; lia]]).
          assert (FCh10 : rw_cells bsegs m10 F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja])
            by (eapply aheap_pres_rw_cells; [exact HPR10| exact FCh9| eapply aclient_range_fake; [exact IN9| lia| cbn; lia]]).
          assert (FCt10 : rw_cells bsegs m10 (F1 + 88) [CB 32 jb; C8 (Z_to_bv 64 (fflag L 1 F1))])
            by (eapply aheap_pres_rw_cells; [exact HPR10| exact FCt9| eapply aclient_range_fake; [exact IN9| lia| cbn; lia]]).
          assert (FS10 : rw_cells bsegs m10 (shad F1) lamsh3).
          { eapply aheap_pres_rw_cells; [exact HPR10| exact FS9|].
            right; right. right; right. exists 1, F1, 128. split; [exact IN9|]. cbn. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
          (* [comment removed for export] *)
          pose proof (lk_to_AI _ _ _ K _ _ _ _ _ AL10 TIGHT) as AH10.
          destruct (AI_block AI _ _ _ _ _ _ _ _ AH10 ltac:(left; reflexivity)) as (CAP' & _ & _ & _ & BSH10 & _).
          pose proof (cells_of_ablock_shadow m10 A' 54 ltac:(lia) ltac:(exact NL2) ltac:(clear - NL3 ATR; lia) BSH10) as OUT10. change (Z.to_nat (granules 54)) with 7%nat in OUT10.
          clear LF9 TC9 FCh9 FCt9 FS9 CC9 CS9 FBK9 IMG9 USH9 UCH9.
          (* [comment removed for export] *)
          apply implMA_ret.
          eapply evtF_cut.
          { eapply (lam_err4 RNGd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 F1); first [exact MI10| exact ST10| exact FS10| exact F128| exact FBLK| exact FTOP| exact FLEd'| eapply rng_fp_le; [exact FLEd| eapply rng_fp_le; [exact FLEa| exact RFS8]]]. }
          cbv beta. intros ms13 (m11 & -> & MU11 & WM11 & MI11 & FS11 & ST11).
          assert (AL11 : AHL AI fflag rng_fs K (lay (Some p') A' 54 54) RNGd (aps_m sd) (blc (Some p') A' 54 ++ mkABlock (ABFake 1) F1 128 :: LB) m11).
          { cbn [lay blc app].
            assert (AL11a : AHL AI fflag rng_fs K L RNGd (aps_m sd) (HB p' A' 54 :: mkABlock (ABFake 1) F1 128 :: LB) m11).
            { eapply (lk_frame _ _ _ K); [exact AL10| exact MU11| exact WM11|]. constructor; [| constructor]. cbn [fst snd].
              right; right. right; right. exists 1, F1, 128. split; [exact IN9|]. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
            assert (OUT11 : rw_cells bsegs m11 (shad A') [CB 7 (vpat 54 54)]).
            { rewrite vpat_tight. eapply rw_cells_transport; [exact OUT10| exact MU11| exact WM11| cbn [disjoint_from cells_size csize]; clear - SHAF'; lia]. }
            eapply (lk_set_some _ _ _ K) with (slo := SPL) (shi := SPL) (glo := shad A') (ghi := shad A');
              [exact AL11a| left; reflexivity| apply munch_refl| apply wmono_refl| clear - LOA LOS'; lia| clear - RSP; lia| lia| change (granules 54) with 7; lia| exact OUT11]. }
          assert (AG11 : magree bsegs lam_px m0 m11).
          { eapply magree_trans; [exact AG10|]. eapply magree_mono; [eapply magree_of_munch; [exact MU11| exact WM11]|]. intros a [Ha _]. cbn [outside].
            destruct (lam_outside _ _ _ _ F1 a AH6 INF INCL FBLK F8 Ha) as (_ & _ & O3). clear - O3. lia. }
          (* [comment removed for export] *)
          pose proof LF10 as LF11. apply (rw_cells_transport bsegs [(shad F1 + 8, shad F1 + 11)] m10 m11) in LF11; [| exact MU11| exact WM11| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul LFR lamsh1 lamsh2 lamsh3 app repeat Datatypes.length]; clear - SHF LOS' LOA; lia].
          pose proof RC10 as RC11. apply (rw_cells_transport bsegs [(shad F1 + 8, shad F1 + 11)] m10 m11) in RC11; [| exact MU11| exact WM11| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul LFR lamsh1 lamsh2 lamsh3 app repeat Datatypes.length]; clear - SHF RNS; lia].
          pose proof FCh10 as FCh11. apply (rw_cells_transport bsegs [(shad F1 + 8, shad F1 + 11)] m10 m11) in FCh11; [| exact MU11| exact WM11| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul LFR lamsh1 lamsh2 lamsh3 app repeat Datatypes.length]; unfold KLS in FNS; clear - SHF FNS; lia].
          pose proof FCt10 as FCt11. apply (rw_cells_transport bsegs [(shad F1 + 8, shad F1 + 11)] m10 m11) in FCt11; [| exact MU11| exact WM11| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul LFR lamsh1 lamsh2 lamsh3 app repeat Datatypes.length]; unfold KLS in FNS; clear - SHF FNS; lia].
          assert (OUT11 : rw_cells bsegs m11 (shad A') [CB 7 (vpat 54 54)]).
          { rewrite vpat_tight. eapply rw_cells_transport; [exact OUT10| exact MU11| exact WM11| cbn [disjoint_from cells_size csize]; clear - SHAF'; lia]. }
          assert (FCa : rw_cells bsegs m11 F1 [C8 (Z_to_bv 64 0x41b58ab3)] /\ rw_cells bsegs m11 (F1 + 120) [C8 (Z_to_bv 64 (fflag L 1 F1))]).
          { split.
            - pose proof FCh11 as X. change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja]) with ([C8 (Z_to_bv 64 0x41b58ab3)] ++ [C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja]) in X.
              apply rw_cells_app_split in X as [X _]. exact X.
            - pose proof FCt11 as X. change ([CB 32 jb; C8 (Z_to_bv 64 (fflag L 1 F1))]) with ([CB 32 jb] ++ [C8 (Z_to_bv 64 (fflag L 1 F1))]) in X.
              apply rw_cells_app_split in X as [_ X]. cbn [cells_size csize Nat.add] in X. replace (F1 + 88 + Z.of_nat 32) with (F1 + 120) in X by lia. exact X. }
          destruct FCa as [FCa FCf].
          eapply (lam_close RNGd sd m11 F1 (Z_to_bv 64 F1) j8 (Z_to_bv 64 0x41b58ab3) (Some p') A' 54 54);
            first [ exact FLEd' | exact AL11 | exact TIGHT | exact AG11 | exact MI11 | exact ST11 | exact LF11 | exact FCa | exact FCf | exact FS11 | exact F128 | exact FBLK | exact FTOP | exact DJRF | exact RC11
                  | (rewrite ARSd, ARS9, ARS8; exact ARSv) | (rewrite CLd, CLa, CL8; exact CLv)
                  | (eapply rng_fp_le; [exact FLEd| eapply rng_fp_le; [exact FLEa| first [exact RF8| exact RFS8]]])
                  | (clear; lia)
                  | (split; [clear - CAP'; lia| split; [exact BR'| split; [eapply rng_fp_le; [exact FLEd| exact RA9]| split; [eapply rng_fp_le; [exact FLEd| exact RSA9]| exact OUT11]]]]) ].
        - (* [comment removed for export] *)
          rewrite (assignA_inplace n (Some p)) by (unfold ERRMSG_LEN; clear - NGE54; lia). apply implMA_ret_bind. cbv beta.
          apply implMA_from_evtF.
          (* [comment removed for export] *)
          eapply evtF_cut.
          { eapply (lam_err2 RNGs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 F1 P); first [exact MI8| exact TC8| exact PL2| exact PB3| exact FL2| exact FTOP| exact FLE8'| exact RF8| (clear - PL1; lia)]. }
          cbv beta. intros ms9 (y10 & ->).
          (* [comment removed for export] *)
          eapply evtF_cut.
          { eapply (avassign_inplace RNGs) with (lo := lo) (V := R) (beg := A) (n := n) (P := P); try reflexivity; rewrite ?USPL, ?URET;
              first [ exact MI8 | exact ST8 | exact LOA | exact GOT8 | exact RIC8 | exact SHB8 | exact INI8 | exact LAY8 | exact RC8 | exact RSH8 | exact R8 | exact RBLK | (clear - DJAR; lia) | exact BR | exact FULL8 | exact WA8
                    | exact PBR | exact RI8 | exact RV8 | exact RVS8 | exact RSA8
                    | (clear - DJPA; lia)
                    | (apply (poison_cells_of_aheap AI _ _ _ _ _ AH8))
                    | (apply (annot_cells_of_aheap AI _ _ _ _ _ AH8); apply (hrt_cells_of_aheap AI _ _ _ _ _ AH8))
                    | (unfold AVASSIGN_STACK, AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK; clear - LOS'; lia)
                    | (clear - STOP LY3; lia)
                    | (split; [clear - NGE54; lia| exact (proj2 CAP)])
                    | (exact (blk_window_facts AI _ _ _ _ _ _ _ _ A 54 AH8 IN4 ltac:(lia) ltac:(clear - NGE54; lia) ltac:(lia)))
                    | (destruct STR8 as [[_ SB] _]; cbn [cells_bytes cbytes app] in SB; rewrite app_nil_r in SB; exact SB)
                    | (exact (blk_window_facts AI _ _ _ _ _ _ _ _ P 54 AH8 IN5 ltac:(lia) ltac:(lia) ltac:(lia)))
                    | (clear - DJPR FR1 FR2; lia)
                    | (eapply rng_sub'; [exact RSTK8| clear - LOS' LO0 STOP LY3 RSP; lia])
                    ]. }
          cbv beta. unfold avassign_inplace_post. intros ms10 PO10.
          destruct PO10 as (v0 & v1 & v2 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & v3 & v4 & v5 & v6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & RC9 & RSH9 & OUT9 & BLK9 & SRC9 & (mq & MUa & WMa & MUb & WMb)).
          rewrite ?USPL, ?URET in MU9, ST9, MUa, MUb. retlit.
          assert (GA : exists G, granules n = G /\ 7 <= G /\ 8 * G <= n + 7) by (exists (granules n); rewrite granules_div by lia; clear - NGE54; Z.div_mod_to_equations; lia).
          destruct GA as (G & EG & G7 & G8). rewrite EG in MU9, OUT9, MUb.
          assert (SHA : 2148345856 <= shad A /\ shad A + G <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - BL1 ATOPA ATR G8 NP; Z.div_mod_to_equations; lia).
          assert (SHAF : shad A + G <= shad F1 \/ shad F1 + 16 <= shad A) by (rewrite !shad_div; clear - DJAF A8 F8 G8 NP; Z.div_mod_to_equations; lia).
          assert (DJA : forall b0, In b0 LB -> A + n <= ab_addr b0 \/ ab_addr b0 + ab_size b0 <= A).
          { intros b0 Hb. assert (INb : In b0 (mkABlock (ABFake 1) F1 128 :: LB)) by (right; exact Hb). exact (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH6' INb). }
          (* [comment removed for export] *)
          destruct (lk_of_AI _ _ _ K _ _ _ _ _ AH8) as [AL8 TIGHT].
          assert (AL9 : AHL AI fflag rng_fs K (lk_setb AI fflag rng_fs K L p A n (Some (vpat n 54))) RNGs (aps_m ss) (HB t P 56 :: HB p A n :: mkABlock (ABFake 1) F1 128 :: LB) m9).
          { eapply (lk_set_some _ _ _ K) with (slo := lo) (shi := SPL) (glo := shad A + 6) (ghi := shad A + G);
              [| exact IN4| exact MUb| exact WMb| exact LOA| clear - RSP; lia| clear; lia| rewrite EG; clear; lia| rewrite EG; exact OUT9].
            eapply (lk_frame _ _ _ K); [exact AL8| exact MUa| exact WMa|].
            constructor; [apply aclient_range_stack; cbn; clear - RSP LOA LOS'; lia| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
            - eapply aclient_range_fake; [right; right; right; exact FIN| clear - FR1; lia| clear - FR2; lia].
            - right; left. exists (HB p A n). split; [exact IN4| cbn; clear - NGE54; lia]. }
          assert (AG9 : magree bsegs lam_px m0 m9).
          { eapply magree_trans; [exact AG8|]. eapply magree_mono; [eapply magree_of_munch; [exact MU9| exact WM9]|]. intros a Ha. cbn [outside].
            pose proof Ha as [Hc HR]. destruct (lam_outside _ _ _ _ F1 a AH6 INF INCL FBLK F8 Hc) as (O1 & _).
            pose proof (lam_px_gran A n a DJA A8 ltac:(exact (proj1 (ablk_lin _ _ BR1))) ATOPA ltac:(clear - NP; lia) Ha) as OG. rewrite EG in OG.
            pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ SPA a AH6' ltac:(clear - LOA LOS'; lia) ltac:(eapply aclient_addr_mono_lb; [exact Hc| intros b0 Hb; right; exact Hb])) as OA.
            clear - O1 HR OG OA LOS' NGE54. lia. }
          pose proof LF8 as LF9. xrwby LF9 MU9 WM9 by (clear - ATR LOA LOS' RL3 BL3 NGE54 SHA; lia).
          pose proof TC8 as TC9. xrwby TC9 MU9 WM9 by (clear - ATR LOA LOS' FTOP DJRF DJAF NGE54 FNS SHA; lia).
          pose proof FCh8 as FCh9. xrwby FCh9 MU9 WM9 by (clear - ATR LOA LOS' FTOP DJRF DJAF NGE54 FNS SHA; lia).
          pose proof FCt8 as FCt9. xrwby FCt9 MU9 WM9 by (clear - ATR LOA LOS' FTOP DJRF DJAF NGE54 FNS SHA; lia).
          pose proof FS8 as FS9. xrwby FS9 MU9 WM9 by (clear - ATR LOA SHF RNS ANS NGE54 SHAF; lia).
          clear CC8 CS8 RSH8 FBK8 IMG8 USH8 UCH8 WRH8.
          destruct (lam_refresh m9 AG9 (lk_relro _ _ _ K _ _ _ _ _ AL9) MI9) as (CC9 & CS9 & RSH9' & FBK9 & IMG9 & USH9 & UCH9 & _).
          (* [comment removed for export] *)
          eapply evtF_cut.
          { eapply (lam_err3 RNGs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 F1 P); first [exact MI9| exact TC9| exact PL2| exact PB3| exact FL2| exact FTOP| exact FLE8'| exact RF8]. }
          cbv beta. intros ms11 (y2' & y3' & ->).
          (* [comment removed for export] *)
          assert (BFR : bytes_at bsegs m9 (SPA - 16) (le8 s0) /\ bytes_at bsegs m9 (SPA - 8) (le8 ra)).
          { pose proof LF9 as X. unfold LFR in X. cbn [app] in X.
            change ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F1); CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
              with ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F1); CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0] ++ [C8 ra]) in X.
            apply rw_cells_app_split in X as [_ X]. apply rw_cells_app_split in X as [X1 X2]. cbn [cells_size csize Nat.add] in X1, X2.
            pose proof (rw_cells_bytes_at _ _ _ _ X1) as B1. pose proof (rw_cells_bytes_at _ _ _ _ X2) as B2. cbn [cells_bytes cbytes app] in B1, B2. rewrite app_nil_r in B1, B2.
            replace (SPL + Z.of_nat 112) with (SPA - 16) in B1 by lia. replace (SPL + Z.of_nat 112 + Z.of_nat 8) with (SPA - 8) in B2 by lia. split; [exact B1| exact B2]. }
          destruct BFR as [BFP BRA].
          assert (UC9 : uchain m9 (al_top L) AFREE_PC SPL SPA UDEPTH (bv_unsigned ra :: tr)).
          { replace (bv_unsigned ra :: tr) with ((if bv_unsigned ra =? AFREE_PC then [] else [bv_unsigned ra]) ++ tr) by (rewrite (proj2 (Z.eqb_neq _ _) RAPC); reflexivity).
            pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RRA, RS0. cbn in RRA, RS0.
            eapply uc_step; [clear - RSP; lia| clear - STOP; lia| clear - SP32; Z.div_mod_to_equations; lia| unfold UDEPTH; clear; lia
                           | rewrite Z_to_bv_bv_unsigned; exact BFP| rewrite Z_to_bv_bv_unsigned; exact BRA| clear - RA12 RRA; lia| clear - RS0; lia|].
            rewrite (proj2 (Z.eqb_neq _ _) RAPC). exact UCH9. }
          apply evtF_done.
          (* [comment removed for export] *)
          eapply implMA_bind.
          { eapply implMA_cl; [apply cl_stable_opdelete|]. unfold opdeleteA.
            eapply (lk_opdel_sz _ _ _ K) with (L := lk_setb AI fflag rng_fs K L p A n (Some (vpat n 54))) (lo := lo) (A := P) (n := 56) (tr := bv_unsigned ra :: tr);
              try reflexivity; rewrite ?USPL, ?URET; rewrite ?(lk_top _ _ _ K), ?(lk_U _ _ _ K);
              first [ exact AL9 | exact IN5 | exact MI9 | exact ST9 | exact LOA | exact TP | exact UC9 | exact HUS | exact RSTK8
                    | (unfold AFREE_STACK; clear - LOS'; lia) | (clear - STOP; lia) | (clear - RSP; lia)
                    | (unfold ALAM_STRDEL_RET; clear; lia) | (unfold ALAM_STRDEL_RET, AFREE_PC; clear; lia)
                    | (cbn [length]; clear - TRL; lia) | (clear - SPL32; Z.div_mod_to_equations; lia)
                    | (apply (proj2 (lk_aps_ok _ _ _ K _ _ _ _ _ _)); eapply aps_ok_rest; [exact ARS8| exact AOKv]) ]. }
          cbv beta. intros [] sd RNGd ms12 [[ARSd POd] CLd].
          destruct POd as (FLEd & v0' & v1' & v2' & q0' & q1' & q2' & q3' & q4' & q5' & q6' & q7' & v3' & v4' & v5' & v6' & m10 & -> & MI10 & ST10 & HPR10 & AL10).
          rewrite ?USPL, ?URET in ST10, HPR10.
          replace (ret_pc (Z_to_bv 64 ALAM_STRDEL_RET)) with (Z_to_bv 64 ALAM_STRDEL_RET) by (symmetry; apply ret_pc_even; [unfold ALAM_STRDEL_RET; clear; lia| reflexivity]).
          rewrite (lb_remove_headA t P 56) in HPR10, AL10 by (exact (lk_hb_ids _ _ _ K _ _ _ _ _ AL9)).
          pose proof (fp_le_trans _ _ _ FLE8' FLEd) as FLEd'.
          assert (AG10 : magree bsegs lam_px m0 m10).
          { eapply magree_trans; [exact AG9|]. ag_of_hpr HPR10. eapply magree_mono; [exact HPR10|]. intros a Ha. eapply lam_px_client; [exact Ha| exact INCLF| clear - LOS'; lia]. }
          assert (LF10 : rw_cells bsegs m10 SPL (LFR [C8 (Z_to_bv 64 F1); CB 8 j8] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
            by (eapply aheap_pres_rw_cells; [exact HPR10| exact LF9| apply aclient_range_stack; cbn; clear - RSP; lia]).
          assert (RC10 : rw_cells bsegs m10 R [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 54)); C8 (Z_to_bv 64 (A + n))])
            by (eapply aheap_pres_rw_cells; [exact HPR10| exact RC9| eapply aclient_range_fake; [right; right; exact FIN| exact FR1| cbn; clear - FR2; lia]]).
          assert (FCh10 : rw_cells bsegs m10 F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja])
            by (eapply aheap_pres_rw_cells; [exact HPR10| exact FCh9| eapply aclient_range_fake; [exact IN2| lia| cbn; lia]]).
          assert (FCt10 : rw_cells bsegs m10 (F1 + 88) [CB 32 jb; C8 (Z_to_bv 64 (fflag L 1 F1))])
            by (eapply aheap_pres_rw_cells; [exact HPR10| exact FCt9| eapply aclient_range_fake; [exact IN2| lia| cbn; lia]]).
          assert (FS10 : rw_cells bsegs m10 (shad F1) lamsh3).
          { eapply aheap_pres_rw_cells; [exact HPR10| exact FS9|].
            right; right. right; right. exists 1, F1, 128. split; [exact IN2|]. cbn. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
          pose proof (lk_cell_some _ _ _ K _ _ _ _ _ _ _ _ _ AL10 IN1 ltac:(apply length_vpat; clear - NGE54; lia)) as OUT10. rewrite EG in OUT10.
          clear LF9 TC9 FCh9 FCt9 FS9 CC9 CS9 RSH9' FBK9 IMG9 USH9 UCH9.
          (* [comment removed for export] *)
          apply implMA_ret.
          eapply evtF_cut.
          { eapply (lam_err4 RNGd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m10 F1); first [exact MI10| exact ST10| exact FS10| exact F128| exact FBLK| exact FTOP| exact FLEd'| eapply rng_fp_le; [exact FLEd| exact RFS8]]. }
          cbv beta. intros ms13 (m11 & -> & MU11 & WM11 & MI11 & FS11 & ST11).
          assert (AL11 : AHL AI fflag rng_fs K (lay (Some p) A n 54) RNGd (aps_m sd) (blc (Some p) A n ++ mkABlock (ABFake 1) F1 128 :: LB) m11).
          { cbn [lay blc app]. eapply (lk_frame _ _ _ K); [exact AL10| exact MU11| exact WM11|]. constructor; [| constructor]. cbn [fst snd].
            right; right. right; right. exists 1, F1, 128. split; [exact IN2|]. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
          assert (AG11 : magree bsegs lam_px m0 m11).
          { eapply magree_trans; [exact AG10|]. eapply magree_mono; [eapply magree_of_munch; [exact MU11| exact WM11]|]. intros a [Ha _]. cbn [outside].
            destruct (lam_outside _ _ _ _ F1 a AH6 INF INCL FBLK F8 Ha) as (_ & _ & O3). clear - O3. lia. }
          pose proof LF10 as LF11. xrwby LF11 MU11 WM11 by (clear - ATR LOA LOS' SHF; lia). pose proof RC10 as RC11. xrwby RC11 MU11 WM11 by (clear - RNS SHF; lia).
          pose proof FCh10 as FCh11. xrwby FCh11 MU11 WM11 by (clear - FNS SHF; lia). pose proof FCt10 as FCt11. xrwby FCt11 MU11 WM11 by (clear - FNS SHF; lia).
          assert (OUT11 : rw_cells bsegs m11 (shad A) [CB (Z.to_nat G) (vpat n 54)])
            by (eapply rw_cells_transport; [exact OUT10| exact MU11| exact WM11| cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - SHAF; lia]).
          assert (FCa : rw_cells bsegs m11 F1 [C8 (Z_to_bv 64 0x41b58ab3)] /\ rw_cells bsegs m11 (F1 + 120) [C8 (Z_to_bv 64 (fflag L 1 F1))]).
          { split.
            - pose proof FCh11 as X. change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja]) with ([C8 (Z_to_bv 64 0x41b58ab3)] ++ [C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 24 ja]) in X.
              apply rw_cells_app_split in X as [X _]. exact X.
            - pose proof FCt11 as X. change ([CB 32 jb; C8 (Z_to_bv 64 (fflag L 1 F1))]) with ([CB 32 jb] ++ [C8 (Z_to_bv 64 (fflag L 1 F1))]) in X.
              apply rw_cells_app_split in X as [_ X]. cbn [cells_size csize Nat.add] in X. replace (F1 + 88 + Z.of_nat 32) with (F1 + 120) in X by lia. exact X. }
          destruct FCa as [FCa FCf].
          eapply (lam_close RNGd sd m11 F1 (Z_to_bv 64 F1) j8 (Z_to_bv 64 0x41b58ab3) (Some p) A 54 n);
            first [ exact FLEd' | exact AL11 | exact TIGHT | exact AG11 | exact MI11 | exact ST11 | exact LF11 | exact FCa | exact FCf | exact FS11 | exact F128 | exact FBLK | exact FTOP | exact DJRF | exact RC11
                  | (rewrite ARSd, ARS8; exact ARSv) | (rewrite CLd, CL8; exact CLv)
                  | (eapply rng_fp_le; [exact FLEd| first [exact RF8| exact RFS8]])
                  | (clear - NGE54; lia)
                  | (rewrite EG; split; [split; [clear - NP; lia| exact (proj2 CAP)]| split; [exact BR| split; [eapply rng_fp_le; [exact FLEd| exact RA8]| split; [eapply rng_fp_le; [exact FLEd| unfold granules; rewrite <- EG; exact RSA8]| exact OUT11]]]]) ]. }
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (lam_sok RNGv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 F1 pos); first [exact MI6| exact CC6| exact CS6| exact RSW| exact POS| exact FL2| exact FTOP| exact FLEv| exact RFv]. }
      cbv beta. intros ms7 ->.
      destruct (lk_of_AI _ _ _ K _ _ _ _ _ AH6) as [AL6 TIGHT].
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH6) as (GOT6 & _ & _ & SHB6 & _).
      (* [comment removed for export] *)
      assert (FCa : rw_cells bsegs m6 F1 [C8 (Z_to_bv 64 0x41b58ab3)] /\ rw_cells bsegs m6 (F1 + 120) [C8 (Z_to_bv 64 (fflag L 1 F1))]).
      { pose proof FC6 as X.
        change ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 80 j80; C8 (Z_to_bv 64 (fflag L 1 F1))])
          with ([C8 (Z_to_bv 64 0x41b58ab3)] ++ [C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 8 j8'; C8 (Z_to_bv 64 pos); CB 80 j80] ++ [C8 (Z_to_bv 64 (fflag L 1 F1))]) in X.
        apply rw_cells_app_split in X as [X1 X]. apply rw_cells_app_split in X as [_ X3]. cbn [cells_size csize Nat.add] in X3.
        replace (F1 + Z.of_nat 8 + Z.of_nat 112) with (F1 + 120) in X3 by lia. split; [exact X1| exact X3]. }
      destruct FCa as [FCa FCf].
      destruct b as [p|].
      - (* [comment removed for export] *)
        destruct BLK as (BR & NP & RA & RSA & _). pose proof BR as (BR1 & BR2 & BR3 & BR4).
        pose proof AH6 as AH6'. cbn [bl app] in AH6'.
        assert (IN1 : In (HB p A n) (HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)) by (left; reflexivity).
        destruct (AI_block AI _ _ _ _ _ _ _ _ AH6' IN1) as (CAP & _ & _ & _ & BSH & _).
        pose proof (cells_of_ablock_shadow m6 A n ltac:(clear - NP; lia) ltac:(exact A0) ltac:(clear - ATOPA ATR; lia) BSH) as FULL6.
        pose proof (poison_cells_of_aheap AI _ _ _ _ _ AH6') as PC6. pose proof (annot_cells_of_aheap AI _ _ _ _ _ AH6' (hrt_cells_of_aheap AI _ _ _ _ _ AH6')) as AC6.
        pose proof (ablk_rup8 _ _ BR1 A8 ltac:(clear - NP; lia)) as BRU. pose proof (ablk_lin _ _ BRU) as (_ & _ & BU3 & BU4).
        assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NP; Z.div_mod_to_equations; lia).
        assert (DJ8 : R + 24 <= A \/ A + rup8 n <= R) by (unfold rup8, rdn8; clear - DJAR FR1 FR2 R8 A8 NP; Z.div_mod_to_equations; lia).
        pose proof (granules_rup8 n ltac:(clear - NP; lia)) as EGR.
        destruct (Z.eq_dec pos n) as [PE|PNE].
        + (* [comment removed for export] *)
          eapply evtF_cut.
          { eapply (aresize_eq RNGv) with (lo := lo) (V := R) (beg := A) (n := n); try reflexivity; rewrite ?USPL, ?URET;
              first [ exact MI6 | exact ST6 | exact GOT6 | exact SHB6 | exact RC6 | exact RSH6 | exact R8 | exact RBLK | exact BRU | exact RIv | exact RVv | exact RVSv
                    | (rewrite PE; reflexivity)
                    | (clear - LOA; lia) | (clear - LOS'; lia) | (clear - STOP LY3; lia) | (clear - NP; lia) | (clear - NLT; lia)
                    | (eapply rng_sub'; [exact RSTKv| clear - LOS' LO0 STOP LY3 RSP; lia])
                    ]. }
          cbv beta. unfold aresize_nop_post. intros ms8 PO8.
          destruct PO8 as (v0 & v1 & v2 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & v3 & v4 & v5 & v6 & m8 & -> & MU8 & WM8 & MI8 & ST8).
          rewrite ?USPL, ?URET in MU8, ST8. retlit.
          zstep.                    (* [comment removed for export] *)
          apply evtF_done. apply implMA_ret.
          assert (AL8 : AHL AI fflag rng_fs K (lay (Some p) A n n) RNGv (aps_m sv) (blc (Some p) A n ++ mkABlock (ABFake 1) F1 128 :: LB) m8).
          { cbn [lay blc app]. pose proof FULL6 as FULL8. xrwg FULL8 MU8 WM8 by (rewrite Nat.add_0_r, Z2Nat.id by (rewrite granules_div by (clear - NP; lia); clear - NP; Z.div_mod_to_equations; lia); rewrite shad_div, granules_div by (clear - NP; lia); unfold ASHOFF; clear - A0 ATOPA ATR LOA LOS' NP; Z.div_mod_to_equations; lia). rewrite <- vpat_tight in FULL8.
            eapply (lk_set_some _ _ _ K) with (slo := SPL) (shi := SPL) (glo := shad A) (ghi := shad A); [| exact IN1| apply munch_refl| apply wmono_refl| clear - LOA LOS'; lia| clear - RSP; lia| clear; lia| rewrite granules_div by (clear - NP; lia); clear - NP; Z.div_mod_to_equations; lia| exact FULL8].
            eapply (lk_frame _ _ _ K); [exact AL6| exact MU8| exact WM8|]. constructor; [apply aclient_range_stack; cbn; clear - RSP LOA LOS'; lia| constructor]. }
          assert (AG8 : magree bsegs lam_px m0 m8).
          { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU8| exact WM8]|]. intros a [Ha _]. cbn [outside].
            destruct (lam_outside _ _ _ _ F1 a AH6 INF INCL FBLK F8 Ha) as (O1 & _). clear - O1 LOS'. lia. }
          pose proof LF6 as LF8. xrwby LF8 MU8 WM8 by (clear; lia). pose proof FCa as FC8. xrwby FC8 MU8 WM8 by (clear - FTOP ATR LOA LOS'; lia). pose proof FCf as FCf8. xrwby FCf8 MU8 WM8 by (clear - FTOP ATR LOA LOS'; lia).
          pose proof FS6 as FS8. xrwby FS8 MU8 WM8 by (clear - SHF ATR LOA LOS'; lia). pose proof RC6 as RC8. xrwby RC8 MU8 WM8 by (clear - RL3 ATR LOA LOS'; lia). pose proof FULL6 as OUT8. xrwg OUT8 MU8 WM8 by (rewrite Nat.add_0_r, Z2Nat.id by (rewrite granules_div by (clear - NP; lia); clear - NP; Z.div_mod_to_equations; lia); rewrite shad_div, granules_div by (clear - NP; lia); unfold ASHOFF; clear - A0 ATOPA ATR LOA LOS' NP; Z.div_mod_to_equations; lia).
          rewrite <- vpat_tight in OUT8.
          eapply (lam_close RNGv sv m8 F1 (Z_to_bv 64 F1) j8 (Z_to_bv 64 0x41b58ab3) (Some p) A n n);
            first [ exact FLEv | exact ARSv | exact CLv | exact AL8 | exact TIGHT | exact AG8 | exact MI8 | exact ST8 | exact LF8 | exact FC8 | exact FCf8 | exact FS8 | exact F128 | exact FBLK | exact FTOP | exact DJRF | exact RFv | exact RFSv | exact RC8
                  | (clear - NP; lia)
                  | (split; [clear - CAP; lia| split; [exact BR| split; [exact RA| split; [first [exact RSA| unfold granules; exact RSA| rewrite <- EGR; unfold rup8; exact RSA] | exact OUT8]]]]) ].
        + (* [comment removed for export] *)
          eapply evtF_cut.
          { eapply (aresize_lt RNGv) with (lo := lo) (V := R) (beg := A) (n := n) (k := pos); try reflexivity; rewrite ?USPL, ?URET;
              first [ exact MI6 | exact ST6 | exact PC6 | exact AC6 | exact GOT6 | exact SHB6 | exact RC6 | exact RSH6 | exact R8 | exact RBLK | exact DJ8 | exact A8 | exact BRU | exact RIv | exact RVv | exact RVSv
                    | (rewrite EGR; exact FULL6) | (rewrite EGR; unfold granules; exact RSA)
                    | (unfold ANNOTW_STACK; clear - LOS'; lia) | (clear - LOA; lia) | (clear - STOP LY3; lia) | (clear - POS; lia) | (clear - PNE POS; lia) | (clear - NLT; lia) | (clear - BU4; lia)
                    | (eapply rng_sub'; [exact RSTKv| clear - LOS' LO0 STOP LY3 RSP; lia])
                    ]. }
          cbv beta. unfold aresize_post. intros ms8 PO8.
          destruct PO8 as (v0 & v1 & v2 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & v3 & v4 & v5 & v6 & m8 & -> & MU8 & WM8 & MI8 & ST8 & RC8 & RSH8 & OUT8).
          rewrite ?USPL, ?URET in MU8, ST8. retlit. rewrite EGR in MU8, OUT8. unfold ANNOTW_STACK in MU8.
          zstep.                    (* [comment removed for export] *)
          apply evtF_done. apply implMA_ret.
          assert (GA : exists G gk, granules n = G /\ pos / 8 = gk /\ 0 <= gk <= G /\ 8 * G <= n + 7) by (exists (granules n), (pos / 8); rewrite granules_div by lia; clear - NP POS PNE; Z.div_mod_to_equations; lia).
          destruct GA as (G & gk & EG & EGK & GK & G8). rewrite EG, EGK in MU8. rewrite EG in OUT8.
          assert (SHA : 2148345856 <= shad A /\ shad A + G <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; pose proof (ablk_lin _ _ BR1) as (BL1 & _); unfold AIMG_HI in BL1; clear - BL1 ATOPA ATR G8 NP; Z.div_mod_to_equations; lia).
          assert (SHAF : shad A + G <= shad F1 \/ shad F1 + 16 <= shad A) by (rewrite !shad_div; clear - DJAF A8 F8 G8 NP; Z.div_mod_to_equations; lia).
          (* [comment removed for export] *)
          destruct (munch_split2 [(SPL - 2736, SPL); (R + 8, R + 16)] [(shad A + gk, shad A + G)] m6 m8 MU8 WM8) as (mq & MUa & WMa & MUb & WMb).
          assert (AL8 : AHL AI fflag rng_fs K (lay (Some p) A n pos) RNGv (aps_m sv) (blc (Some p) A n ++ mkABlock (ABFake 1) F1 128 :: LB) m8).
          { cbn [lay blc app].
            eapply (lk_set_some _ _ _ K) with (slo := SPL) (shi := SPL) (glo := shad A + gk) (ghi := shad A + G);
              [| exact IN1| eapply munch_weaken; [| exact MUb]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; tauto| exact WMb| clear - LOA LOS'; lia| clear - RSP; lia| clear - GK; lia| rewrite EG; clear - GK; lia| rewrite EG; exact OUT8].
            eapply (lk_frame _ _ _ K); [exact AL6| exact MUa| exact WMa|].
            constructor; [apply aclient_range_stack; cbn; clear - RSP LOA LOS'; lia| constructor; [| constructor]]. cbn [fst snd].
            eapply aclient_range_fake; [right; right; exact FIN| clear - FR1; lia| clear - FR2; lia]. }
          assert (DJA : forall b0, In b0 LB -> A + n <= ab_addr b0 \/ ab_addr b0 + ab_size b0 <= A).
          { intros b0 Hb. assert (INb : In b0 (mkABlock (ABFake 1) F1 128 :: LB)) by (right; exact Hb). exact (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH6' INb). }
          assert (AG8 : magree bsegs lam_px m0 m8).
          { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU8| exact WM8]|]. intros a Ha. cbn [outside].
            pose proof Ha as [Hc HR]. destruct (lam_outside _ _ _ _ F1 a AH6 INF INCL FBLK F8 Hc) as (O1 & _).
            pose proof (lam_px_gran A n a DJA A8 ltac:(pose proof (ablk_lin _ _ BR1) as (BL1 & _); exact BL1) ATOPA ltac:(clear - NP; lia) Ha) as OG. rewrite EG in OG.
            clear - O1 HR OG LOS' GK. lia. }
          pose proof LF6 as LF8. xrwby LF8 MU8 WM8 by (clear - RL3 ATR LOA LOS' SHA GK; lia). pose proof FCa as FC8. xrwby FC8 MU8 WM8 by (clear - FTOP ATR LOA LOS' DJRF FNS SHA GK; lia).
          pose proof FCf as FCf8. xrwby FCf8 MU8 WM8 by (clear - FTOP ATR LOA LOS' DJRF FNS SHA GK; lia). pose proof FS6 as FS8. xrwby FS8 MU8 WM8 by (clear - SHF ATR LOA LOS' RNS SHAF GK; lia).
          eapply (lam_close RNGv sv m8 F1 (Z_to_bv 64 F1) j8 (Z_to_bv 64 0x41b58ab3) (Some p) A pos n);
            first [ exact FLEv | exact ARSv | exact CLv | exact AL8 | exact TIGHT | exact AG8 | exact MI8 | exact ST8 | exact LF8 | exact FC8 | exact FCf8 | exact FS8 | exact F128 | exact FBLK | exact FTOP | exact DJRF | exact RFv | exact RFSv | exact RC8
                  | (clear - POS; lia)
                  | (split; [clear - CAP; lia| split; [exact BR| split; [exact RA| split; [exact RSA| rewrite EG; exact OUT8]]]]) ].
      - (* [comment removed for export] *)
        destruct BLK as [EA N0].
        assert (P0 : pos = 0) by (clear - POS N0; lia).
        eapply evtF_cut.
        { eapply (aresize_null0 RNGv) with (lo := lo) (V := R); try reflexivity; rewrite ?USPL, ?URET;
            first [ exact MI6 | exact ST6 | exact GOT6 | exact SHB6 | exact RSH6 | exact R8 | exact RBLK | exact RIv | exact RVv | exact RVSv
                  | (rewrite P0; reflexivity)
                  | (pose proof RC6 as X; rewrite EA, N0 in X; exact X)
                  | (clear - LOA; lia) | (clear - LOS'; lia) | (clear - STOP LY3; lia)
                  | (eapply rng_sub'; [exact RSTKv| clear - LOS' LO0 STOP LY3 RSP; lia])
                  ]. }
        cbv beta. unfold aresize_nop_post. intros ms8 PO8.
        destruct PO8 as (v0 & v1 & v2 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & v3 & v4 & v5 & v6 & m8 & -> & MU8 & WM8 & MI8 & ST8).
        rewrite ?USPL, ?URET in MU8, ST8. retlit.
        zstep.                      (* [comment removed for export] *)
        apply evtF_done. apply implMA_ret.
        assert (AL8 : AHL AI fflag rng_fs K (lay None A n pos) RNGv (aps_m sv) (blc None A n ++ mkABlock (ABFake 1) F1 128 :: LB) m8).
        { cbn [lay blc app]. cbn [bl app] in AL6. eapply (lk_frame _ _ _ K); [exact AL6| exact MU8| exact WM8|]. constructor; [apply aclient_range_stack; cbn; clear - RSP LOA LOS'; lia| constructor]. }
        assert (AG8 : magree bsegs lam_px m0 m8).
        { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU8| exact WM8]|]. intros a [Ha _]. cbn [outside].
          destruct (lam_outside _ _ _ _ F1 a AH6 INF INCL FBLK F8 Ha) as (O1 & _). clear - O1 LOS'. lia. }
        pose proof LF6 as LF8. xrwby LF8 MU8 WM8 by (clear; lia). pose proof FCa as FC8. xrwby FC8 MU8 WM8 by (clear - FTOP ATR LOA LOS'; lia). pose proof FCf as FCf8. xrwby FCf8 MU8 WM8 by (clear - FTOP ATR LOA LOS'; lia).
        pose proof FS6 as FS8. xrwby FS8 MU8 WM8 by (clear - SHF ATR LOA LOS'; lia). pose proof RC6 as RC8. xrwby RC8 MU8 WM8 by (clear - RL3 ATR LOA LOS'; lia).
        eapply (lam_close RNGv sv m8 F1 (Z_to_bv 64 F1) j8 (Z_to_bv 64 0x41b58ab3) None A pos n);
          first [ exact FLEv | exact ARSv | exact CLv | exact AL8 | exact TIGHT | exact AG8 | exact MI8 | exact ST8 | exact LF8 | exact FC8 | exact FCf8 | exact FS8 | exact F128 | exact FBLK | exact FTOP | exact DJRF | exact RFv | exact RFSv
                | (replace (A + pos) with (A + n) by (clear - P0 N0; lia); exact RC8)
                | (clear - POS; lia)
                | (split; [exact EA| exact N0]) ].
    Qed.

    (* [comment removed for export] *)

    Lemma lam_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      implMA RNG (lamA payload) s POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 R) (Z_to_bv 64 C) (Z_to_bv 64 AFALLBACK) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALAMBDA) fc None m0 (seg_rom bsegs)).
    Proof.
      intros.
      pose proof lam_geom as (RSP & SPL32 & ELAND & LOS' & LO0 & SHC8 & SHC0 & SHCLO & SHCHI). pose proof atop_range as ATR.
      assert (USPL : bv_unsigned (Z_to_bv 64 SPL) = SPL) by (apply unsigned_lit; clear - RSP LOS' LO0; lia).
      assert (URET : bv_unsigned (Z_to_bv 64 ALAM_STRDEL_RET) = ALAM_STRDEL_RET) by (apply unsigned_lit; unfold ALAM_STRDEL_RET; clear; lia).
      pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT0 & RIC0 & REAL0 & SHB0 & SUA0 & INI0 & LAY0).
      destruct HI0 as [IMG0 USH0]. pose proof IMG0 as (GSU0 & _).
      pose proof (ablk_lin _ _ RBLK) as (RL1 & RL2 & RL3 & RL4). unfold AIMG_HI in RL1.
      assert (RNS : R + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= R) by (apply ablk_disj_band in RBLK; unfold KLS in RBLK; exact RBLK).
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH FIN) as FB. cbn [ab_addr ab_size] in FB. unfold AIMG_HI in FB.
      rewrite lamA_unfold.
      apply implMA_from_evtF.
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (lam_pro t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0); first [exact ST| exact MI| exact GOT0| exact SHB0| exact GSU0| exact SUA0]. }
      cbv beta. intros ms1 (m1 & y1 & y2 & j16 & -> & MU1 & WM1 & MI1 & LF1 & ST1).
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
      { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [apply aclient_range_stack; cbn; clear - LOA LOS' RSP; lia| constructor]. }
      assert (AG1 : magree bsegs lam_px m0 m1).
      { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a [Ha _]. cbn [outside].
        destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
        - clear - X. lia.
        - pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. clear - H Hr LOA LOS' ATR. lia.
        - pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb). unfold in_block in Hr. clear - H Hr LOA LOS' ATR. lia.
        - rewrite shad_div. unfold ASHOFF. assert (0 <= a' < 2^47).
          { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
            pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb'). cbn [ab_addr ab_size] in H. unfold AIMG_HI in H. lia. }
          clear - H LOA LOS' ATR. Z.div_mod_to_equations. lia. }
      pose proof RC0 as RC1. xrw RC1 MU1 WM1.
      clear MU1 WM1.
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply SM1; first [exact AH1| exact NOF1| exact MI1| exact LOA| exact TP| exact RSTK| exact RI| exact RFS| rewrite unsigned_lit by lia; first [exact ST1| unfold SM1_STACK; clear - LOS'; lia| clear - STOP; lia]]. }
      cbv beta. intros ms2 PO. destruct PO as (F1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & h0 & h1 & h2 & junk & -> & MI2 & ST2 & HPR2 & AH2 & F128 & FBLK & FTOP & FC2 & FS2 & RF1 & RFS1).
      rewrite ?USPL, ?URET in ST2, HPR2. retlit.
      pose proof (ablk_lin _ _ FBLK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
      assert (F8 : F1 mod 8 = 0) by (clear - F128; Z.div_mod_to_equations; lia).
      assert (FNS : F1 + 128 <= KLS \/ 0x10007fff8000 <= F1) by (apply ablk_disj_band; exact FBLK).
      assert (INF : In (mkABlock (ABFake 1) F1 128) (mkABlock (ABFake 1) F1 128 :: LB)) by (left; reflexivity).
      assert (INCL2 : forall b, In b LB -> In b (mkABlock (ABFake 1) F1 128 :: LB)) by (intros b Hb; right; exact Hb).
      assert (AG2 : magree bsegs lam_px m0 m2).
      { eapply magree_trans; [exact AG1|]. ag_of_hpr HPR2. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply lam_px_client; [exact Ha| intros b Hb; exact Hb| clear; lia]. }
      assert (LF2 : rw_cells bsegs m2 SPL (LFR [CB 16 j16] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
        by (eapply aheap_pres_rw_cells; [exact HPR2| exact LF1| apply aclient_range_stack; cbn; clear - RSP; lia]).
      assert (RC2 : rw_cells bsegs m2 R [C8 r0; C8 r1; C8 r2])
        by (eapply aheap_pres_rw_cells; [exact HPR2| exact RC1| eapply aclient_range_fake; [exact FIN| exact FR1| cbn; clear - FR2; lia]]).
      clear LF1 ST1 MI1 AH1 AG1 HPR2 RC1.
      destruct (lam_refresh m2 AG2 (AI_relro AI _ _ _ _ _ AH2) MI2) as (CC2 & CS2 & RSH2 & FBK2 & IMG2 & USH2 & UCH2 & WRH2).
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (lam_hdr u0 u1 u2 _ _ _ _ _ _ _ u3 u4 u5 u6 m2 F1 j16 h0 h1 h2 junk);
          first [exact ST2| exact MI2| exact LF2| exact FC2| exact FS2| exact F128| exact FBLK| exact FTOP| exact CC2| exact CS2| exact RF1| exact RFS1]. }
      cbv beta. intros ms3 (m3 & y3 & y4 & y5 & y6 & -> & MU3 & WM3 & MI3 & LF3 & FC3 & FS3 & CC3 & CS3 & ST3).
      assert (AH3 : AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 1) F1 128 :: LB) m3).
      { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
        constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
        - apply aclient_range_stack; clear - RSP LOA LOS'; lia.
        - eapply aclient_range_fake; [exact INF| lia| lia].
        - right; right. right; right. exists 1, F1, 128. split; [exact INF|]. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
      assert (AG3 : magree bsegs lam_px m0 m3).
      { eapply magree_trans; [exact AG2|]. eapply magree_mono; [eapply magree_of_munch; [exact MU3| exact WM3]|]. intros a [Ha _]. cbn [outside].
        destruct (lam_outside _ _ _ _ F1 a AH2 INF INCL2 FBLK F8 Ha) as (O1 & O2 & O3). clear - O1 O2 O3 LOS'. lia. }
      (* [comment removed for export] *)
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 (INCL2 _ FIN) INF ltac:(intros E; apply (NOF1 F1 128); rewrite <- E; exact FIN)) as DJRF. cbn [ab_addr ab_size] in DJRF.
      assert (DJRF' : R + 24 <= F1 \/ F1 + 128 <= R) by (clear - DJRF FR1 FR2; lia). clear DJRF. rename DJRF' into DJRF.
      assert (SHF : 2148345856 <= shad F1 /\ shad F1 + 16 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - FL1 FL3 ATR; Z.div_mod_to_equations; lia).
      pose proof RC2 as RC3. xrw RC3 MU3 WM3.
      destruct (lam_refresh m3 AG3 (AI_relro AI _ _ _ _ _ AH3) MI3) as (_ & _ & RSH3 & FBK3 & IMG3 & USH3 & UCH3 & WRH3).
      clear MU3 WM3 AG2 CC2 CS2 RSH2 FBK2 IMG2 USH2 UCH2 WRH2 RC2 LF2 FC2 FS2 ST2 MI2.
      (* [comment removed for export] *)
      apply evtF_done. change (Z.of_nat (length payload)) with n.
      destruct (Z.eq_dec n 0) as [N0|NP].
      { (* [comment removed for export] *)
        replace (vctorA n) with (vctorA 0) by (rewrite N0; reflexivity). rewrite vctorA_zero. apply implMA_ret_bind. cbv beta.
        apply implMA_from_evtF. eapply evtF_cut.
        { eapply (avctor_zero AI) with (lo := lo) (L := L) (LB := mkABlock (ABFake 1) F1 128 :: LB) (V := R) (cls := cls) (FA := FA) (FN := FN) (RLO2 := RLO2) (RHI2 := RHI2);
            try reflexivity; rewrite ?USPL, ?URET;
            first [ exact AH3 | exact MI3 | exact ST3 | exact LOA | exact FR1 | exact FR2 | exact R8 | exact RBLK | exact RC3 | exact RSH3 | exact Q1 | exact Q2 | exact Q3 | exact Q4 | exact Q5 | exact Q6
                  | exact WRH3 | exact RR2 | exact RSTK | exact RI | exact RV | exact RVS
                  | (right; exact FIN)
                  | (unfold AVCTOR_STACK, AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK; clear - LOS'; lia)
                  | (clear - STOP; lia)
                  | (clear - SPL32; Z.div_mod_to_equations; lia)
                  | (rewrite N0; reflexivity)
                  ]. }
        cbv beta. intros ms4 PO4.
        destruct PO4 as (w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & RC4 & RSH4).
        rewrite ?USPL, ?URET in ST4, MU4. retlit.
        assert (AH4 : AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 1) F1 128 :: LB) m4).
        { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|].
          constructor; [apply aclient_range_stack; cbn; clear - RSP LOA LOS'; lia| constructor; [| constructor]].
          cbn [fst snd]. eapply aclient_range_fake; [exact (INCL2 _ FIN)| exact FR1| clear - FR2; lia]. }
        assert (AG4 : magree bsegs lam_px m0 m4).
        { eapply magree_trans; [exact AG3|]. eapply magree_mono; [eapply magree_of_munch; [exact MU4| exact WM4]|]. intros a [Ha HR]. cbn [outside].
          destruct (lam_outside _ _ _ _ F1 a AH2 INF INCL2 FBLK F8 Ha) as (O1 & _). clear - O1 HR LOS'. lia. }
        pose proof LF3 as LF4. xrw LF4 MU4 WM4. pose proof FC3 as FC4. xrw FC4 MU4 WM4. pose proof FS3 as FS4. xrw FS4 MU4 WM4.
        apply evtF_done.
        eapply (lam_tail RNG s m4 F1 (skipn 8 j16) junk None 0);
          first [ exact AG4 | exact MI4 | exact ST4 | exact LF4 | exact FC4 | exact FS4 | exact F128 | exact FBLK | exact FTOP | exact DJRF | exact RF1 | exact RFS1
                | exact (fp_le_refl _) | reflexivity
                | (cbn [bl app]; exact AH4)
                | (rewrite N0; exact RC4)
                | (cbn; split; [reflexivity| exact N0]) ]. }
      (* [comment removed for export] *)
      assert (NPOS : 0 < n) by (unfold zlength in *; clear - NP; lia).
      rewrite (vctorA_pos n NPOS). apply implMA_bind_assoc.
      eapply implMA_bind.
      { eapply implMA_cl; [apply cl_stable_opnew|].
        eapply (avctor_proof AI ONTA AI_kind AI_premap) with (lo := lo) (L := L) (LB := mkABlock (ABFake 1) F1 128 :: LB) (V := R) (n := n) (cls := cls) (FA := FA) (FN := FN) (RLO2 := RLO2) (RHI2 := RHI2) (ULO := ULO) (UHI := UHI);
          try reflexivity; rewrite ?USPL, ?URET;
          first [ exact AH3 | exact MI3 | exact ST3 | exact LOA | exact TP | exact FR1 | exact FR2 | exact R8 | exact RBLK | exact RC3 | exact RSH3 | exact Q1 | exact Q2 | exact Q3 | exact Q4 | exact Q5 | exact Q6
                | exact WRH3 | exact RR2 | exact HUN | exact RSTK | exact RI | exact RV | exact RVS | exact AOK
                | exact (lam_ush m3 AG3) | exact BU0 | exact BUL | exact BU47 | exact BRUSH      (* [comment removed for export] *)
                | (clear - BUH; lia)
                | (right; exact FIN)
                | (unfold AVCTOR_STACK, AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK; clear - LOS'; lia)
                | (clear - STOP; lia)
                | (clear - SPL32; Z.div_mod_to_equations; lia)
                | (clear - NPOS NLT; lia)
                ]. }
      cbv beta. intros p sv RNG4 ms4 [PO4 CL4].
      destruct PO4 as (FLE4 & w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m4 & A & -> & MI4 & ST4 & ARS4 & BR & HPX4 & AH4 & RC4 & RSH4 & BLK4 & RA4 & RSA4).
      rewrite ?USPL, ?URET in ST4, HPX4. retlit.
      apply implMA_ret_bind. cbv beta.
      assert (INF4 : In (mkABlock (ABFake 1) F1 128) (HB p A n :: mkABlock (ABFake 1) F1 128 :: LB)) by (right; left; reflexivity).
      pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH4 INF) as DJAF. cbn [ab_addr ab_size] in DJAF.
      pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH4 (INCL2 _ FIN)) as DJAR. cbn [ab_addr ab_size] in DJAR.
      pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_disj_band _ _ BR1) as ANS. unfold KLS in ANS.
      assert (AG4 : magree bsegs lam_px m0 m4).
      { eapply magree_trans; [exact AG3|]. intros a Ha Hp. apply HPX4; [exact Ha| eapply lam_px_client; [exact Hp| exact INCL2| clear - LOS'; lia]| exact (proj2 Hp)]. }
      assert (LF4 : rw_cells bsegs m4 SPL (LFR [C8 (Z_to_bv 64 F1); CB 8 (skipn 8 j16)] ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
        by (eapply (aheap_pres_x_rw_cells CI); [exact HPX4| exact LF3| apply aclient_range_stack; cbn; clear - RSP; lia| cbn; clear - RL3 LOA LOS'; lia]).
      assert (FC4 : rw_cells bsegs m4 F1 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13d91); C8 (Z_to_bv 64 0xb1c54); CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F1))])
        by (eapply (aheap_pres_x_rw_cells CI); [exact HPX4| exact FC3| eapply aclient_range_fake; [exact INF| lia| cbn; lia]| cbn; clear - DJRF; lia]).
      assert (FS4 : rw_cells bsegs m4 (shad F1) lamsh1).
      { eapply (aheap_pres_x_rw_cells CI); [exact HPX4| exact FS3| | cbn; clear - SHF RNS; lia].
        right; right. right; right. exists 1, F1, 128. split; [exact INF|]. cbn. rewrite shad_div. unfold ASHOFF. clear - F8 FL2; Z.div_mod_to_equations; lia. }
      eapply (lam_tail RNG4 sv m4 F1 (skipn 8 j16) junk (Some p) A);
        first [ exact FLE4 | exact AH4 | exact ARS4 | exact CL4 | exact AG4 | exact MI4 | exact ST4 | exact LF4 | exact FC4 | exact FS4 | exact F128 | exact FBLK | exact FTOP | exact DJRF | exact RC4
              | (eapply rng_fp_le; [exact FLE4| first [exact RF1| exact RFS1]])
              | (cbn [bl]; split; [exact BR| split; [exact NPOS| split; [exact RA4| split; [exact RSA4| exact BLK4]]]]) ].
    Qed.
  End Body.

  Theorem lambda_proof : lambda_stmt AI fflag rng_fs K.
  Proof.
    unfold lambda_stmt. intros.
    subst. eapply lam_main; first [eassumption| reflexivity].
  Qed.
End LAM.
End CANSEC1.
