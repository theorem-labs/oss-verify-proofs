(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefMemcpyLib DriverCfg ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode FxRunPost ArgLoops.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXD.ArgLoops.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition frz_pt (E : valu) (M : smodel) (w : Z) : Prop :=
  exists p, In p (sm_frz M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p).
(* [comment removed for export] *)
Definition wend (B L : Z) : Z := 8 * ((B + L) / 8 + 1).
Definition cstr_ok (E : valu) (M : smodel) (m0 : word -> option byte) (b l : lin) : Prop :=
  let B := uE E b in let L := uE E l in
  wend B L <= 0x800000000000 /\
  (forall w, B <= w < wend B L -> frz_pt E M w /\ m0 (Z_to_bv 64 w) <> None) /\
  (forall k, 0 <= k < L -> exists bb, m0 (Z_to_bv 64 (B + k)) = Some bb /\ bv_unsigned bb <> 0) /\
  m0 (Z_to_bv 64 (B + L)) = Some (Z_to_bv 8 0).
Definition HAS (E : valu) (M : smodel) (a : list (lin * lin)) (m0 : word -> option byte) : Prop :=
  Forall (fun p => cstr_ok E M m0 (fst p) (snd p)) a.
Definition awfS (n : positive) (a : list (lin * lin)) : bool := forallb (fun p => (lwf n (fst p) && lwf n (snd p))%bool) a.
Definition anilS (a : list (lin * lin)) : bool := match a with [] => true | _ => false end.
Fixpoint aeqbS (a b : list (lin * lin)) : bool :=
  match a, b with
  | [], [] => true
  | (x, y) :: a', (x', y') :: b' => (lin_eqb x x' && lin_eqb y y' && aeqbS a' b')%bool
  | _, _ => false
  end.

Lemma awfS_mono : forall n n' a, (n <= n')%positive -> awfS n a = true -> awfS n' a = true.
Proof.
  intros n n' a Hle H. unfold awfS in *. rewrite forallb_forall in *. intros p Hp. specialize (H p Hp).
  apply andb_prop in H as [H1 H2]. rewrite (lwf_mono _ _ _ Hle H1), (lwf_mono _ _ _ Hle H2). reflexivity.
Qed.
Lemma aeqbS_eq : forall a b, aeqbS a b = true -> a = b.
Proof.
  induction a as [|[x y] a IH]; intros [|[x' y'] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1, H2. subst. f_equal. exact (IH b H3).
Qed.
Lemma HAS_nil : forall E M a m0, anilS a = true -> HAS E M a m0.
Proof. intros E M a m0 H. destruct a; [constructor | discriminate]. Qed.

Lemma uE_agree : forall n E E' l, lwf n l = true -> agree n E E' -> uE E' l = uE E l.
Proof. intros n E E' l Hw Ha. unfold uE. rewrite (lden_agree_wf n E E' l Hw Ha). reflexivity. Qed.

Lemma HAS_agree : forall n E E' M a m0, sm_wf n M = true -> awfS n a = true -> agree n E E' -> HAS E M a m0 -> HAS E' M a m0.
Proof.
  intros n E E' M a m0 Hwf Hwa Ha Hh. unfold HAS in *. rewrite Forall_forall in *. intros p Hp.
  unfold awfS in Hwa. rewrite forallb_forall in Hwa. destruct (andb_prop _ _ (Hwa p Hp)) as [Hw1 Hw2].
  destruct (Hh p Hp) as (C1 & C2 & C3 & C4). unfold cstr_ok.
  rewrite (uE_agree n E E' _ Hw1 Ha), (uE_agree n E E' _ Hw2 Ha).
  split; [exact C1|]. split; [|split; [exact C3 | exact C4]].
  intros w Hw. destruct (C2 w Hw) as [(q & Hq & Hqw) Hm]. split; [|exact Hm].
  exists q. split; [exact Hq|]. pose proof (sm_wf_frz _ M Hwf) as Hwz. rewrite Forall_forall in Hwz. destruct (Hwz q Hq) as [W1 W2].
  rewrite (uE_agree n E E' _ W1 Ha), (uE_agree n E E' _ W2 Ha). exact Hqw.
Qed.

(* [comment removed for export] *)
Definition isl_ok (segs : list Segment) (x : Z) : Prop :=
  (0 <= x /\ x + 28 < 2 ^ 64) /\
  qins segs x 0 (OpImm ALU_ADD 11 0 0) /\ qins segs x 1 (Op ALU_ADD 12 10 11) /\ qins segs x 2 (Load SZ1 false 12 12 0) /\
  qins segs x 3 (OpImm ALU_ADD 11 11 1) /\ qins segs x 4 (Branch BC_NE 12 0 8180) /\ qins segs x 5 (OpImm ALU_ADD 10 11 4095) /\
  qins segs x 6 (Jalr 0 1 0).
Definition rsv_none (S : sst) : bool := match s_resv S with RNone => true | _ => false end.
Definition isl_chk (x : Z) (j : nat) (S : sst) (a : list (lin * lin)) : bool :=
  match nth_error a j, rg_is S 1 with
  | Some (b, l), Some r => (Z.eqb (s_pc S) x && lin_eqb (rget (s_regs S) (rkey (xr 10))) b && Z.eqb (r mod 2) 0 &&
                             rsv_none S && lwf (s_next S) l)%bool
  | _, _ => false
  end.
Definition isl_post (j : nat) (S : sst) (a : list (lin * lin)) : sst :=
  match nth_error a j, rg_is S 1 with
  | Some (b, l), Some r => run_post S r [(xr 10, l); (xr 11, laddc l 1); (xr 12, lconst 0)] []
  | _, _ => S
  end.

Lemma xr_lit : forall k : Z, 0 <= k < 32 -> xr k = Z_to_bv 5 k. Proof. reflexivity. Qed.
Lemma u64_of : forall (w : word), Z_to_bv 64 (bv_unsigned w) = w. Proof. intros w. apply Z_to_bv_bv_unsigned. Qed.
Lemma rdn1_of : forall segs (m : word -> option byte) a bb, m a = Some bb -> rdn segs m a 1 = Some [bb].
Proof. intros segs m a bb H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma fx_isteps_of_msteps : forall segs ms ms', CatSim.msteps segs ms ms' -> FxStep.isteps segs ms ms'.
Proof.
  intros segs ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH]; [apply ist_refl | eapply ist_step; eassumption].
Qed.

(* [comment removed for export] *)
Record nsite : Type := NS { ns_pc : Z; ns_rd : reg; ns_rs : reg }.
Definition nsite_ok (segs : list Segment) (q : nsite) : Prop :=
  ns_rd q <> 0%bv /\ 0 <= ns_pc q /\ ns_pc q + 4 < 2 ^ 64 /\ qins segs (ns_pc q) 0 (Load SZ1 false (ns_rd q) (ns_rs q) (Z_to_bv 12 0)).
Definition nul_chk (q : nsite) (j : nat) (S : sst) (a : list (lin * lin)) : bool :=
  match nth_error a j with
  | Some (b, l) => (Z.eqb (s_pc S) (ns_pc q) && rsv_none S && lin_eqb (rget (s_regs S) (rkey (ns_rs q))) (ladd b l))%bool
  | None => false
  end.
Definition nul_post (q : nsite) (S : sst) : sst := run_post S (ns_pc q + 4) [(ns_rd q, lconst 0)] [].

Section Nul.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_nul : forall q j S M a E ms model T,
  nsite_ok segs q -> nul_chk q j S a = true -> DEN segs LIMIT model0 mem0 E S M ms model -> HAS E M a mem0 ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (nul_post q S) M ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros [x rd rs] j S M a E ms model T Hq Hck Hd Hh Hk.
  destruct Hq as (Hrd & Hx0 & Hx4 & J0). cbn [ns_pc ns_rd ns_rs] in *.
  destruct J0 as (w0 & F0 & E0 & D0). unfold qpc in F0. replace (x + 4 * 0) with x in F0 by lia.
  unfold nul_chk in Hck. cbn [ns_pc ns_rd ns_rs] in Hck.
  destruct (nth_error a j) as [[b l]|] eqn:Hj; [|discriminate].
  apply andb_prop in Hck as [Hck Hadr]. apply andb_prop in Hck as [Hpc0 Hrvn]. apply Z.eqb_eq in Hpc0. apply lin_eqb_eq in Hadr.
  assert (Hrv : s_resv S = RNone) by (unfold rsv_none in Hrvn; destruct (s_resv S); [reflexivity|discriminate|discriminate]).
  unfold HAS in Hh. rewrite Forall_forall in Hh. destruct (Hh (b, l) (nth_error_In _ _ Hj)) as (C1 & C2 & C3 & C4). cbv zeta in *.
  cbn [fst snd] in C1, C2, C3, C4.
  set (B := uE E b) in *. set (L := uE E l) in *.
  pose proof (uE_range E b) as RB. pose proof (uE_range E l) as RL. fold B L in RB, RL.
  assert (Hwe : B + L < wend B L) by (unfold wend; pose proof (Z.div_mod (B + L) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (B + L) 8 ltac:(lia)); lia).
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  (* [comment removed for export] *)
  assert (Hadw : v_addi (getr (ms_regs ms) rs) (bv_signed (Z_to_bv 12 0)) = Z_to_bv 64 (B + L)).
  { rewrite (HR rs), Hadr. change (bv_signed (Z_to_bv 12 0)) with 0. unfold v_addi. rewrite Z.add_0_r.
    rewrite lden_ladd. rewrite bv_add_unsigned. unfold B, L, uE. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_mod by (unfold bv_modulus; lia). reflexivity. }
  assert (Hm : ms_mem (restrict H ms) (Z_to_bv 64 (B + L)) = mem0 (Z_to_bv 64 (B + L)))
    by (apply (frz_restrict segs LIMIT model0 mem0 E S M ms model _ Hd); exact (proj1 (C2 (B + L) ltac:(lia)))).
  assert (Hrd1 : rdn segs (mrestrict H (ms_mem ms)) (v_addi (getr (ms_regs ms) rs) (bv_signed (Z_to_bv 12 0))) 1%nat = Some [Z_to_bv 8 0]).
  { rewrite Hadw. apply rdn1_of. change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms)). rewrite Hm. exact C4. }
  assert (Hst : RiscvSemantics.step segs (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 x) (mrestrict H (ms_mem ms)) (ms_rom ms)) =
                MachineOk (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (regupd (ms_regs ms) rd (Z_to_bv 64 0)) (Z_to_bv 64 (x + 4)) (mrestrict H (ms_mem ms)) (ms_rom ms))).
  { rewrite (step_lbu segs (ms_regs ms) (Z_to_bv 64 x) (mrestrict H (ms_mem ms)) (ms_rom ms) w0 rd rs (Z_to_bv 12 0) (Z_to_bv 8 0) F0 E0 D0 Hrd1).
    rewrite (PropExec.bv_eqb_neq rd 0%bv Hrd). unfold v_addi. rewrite u_small by (unfold two64; lia). reflexivity. }
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 x) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. subst pcv. reflexivity. }
  apply (den_run_post segs cfg LIMIT model0 mem0 Hwx E S M ms model T (regupd (ms_regs ms) rd (Z_to_bv 64 0)) (x + 4) [(rd, lconst 0)] [] Hd Hrv).
  - fold H. rewrite Hmsr. eapply ist_step; [reflexivity | exact Hst | apply ist_refl].
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [exact Hrd|]. split; [apply lwf_lconst|].
    rewrite getr_same by exact Hrd. rewrite lden_lconst. reflexivity.
  - apply Forall_nil.
  - intros rr Es _. cbn [existsb fst] in Es. rewrite orb_false_r in Es.
    rewrite getr_other; [reflexivity|]. intros Hc. subst rr. rewrite bv_eqb_refl in Es. discriminate.
  - exact Hk.
Qed.
End Nul.

Section Nodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_isl : forall x j S M a E ms model T,
  isl_ok segs x -> isl_chk x j S a = true -> DEN segs LIMIT model0 mem0 E S M ms model -> HAS E M a mem0 ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (isl_post j S a) M ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros x j S M a E ms model T Hq Hck Hd Hh Hk.
  unfold isl_chk in Hck. unfold isl_post in Hk.
  destruct (nth_error a j) as [[b l]|] eqn:Hj; [|discriminate]. destruct (rg_is S 1) as [r|] eqn:R1; [|discriminate].
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  rename Hck into Hpc0. apply Z.eqb_eq in Hpc0.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx
         end.
  match goal with Hx : rsv_none S = true |- _ => rename Hx into Hrvn end.
  match goal with Hx : rget (s_regs S) (rkey (xr 10)) = b |- _ => rename Hx into Hb10 end.
  match goal with Hx : lwf (s_next S) l = true |- _ => rename Hx into Hwl end.
  assert (Hrv : s_resv S = RNone) by (unfold rsv_none in Hrvn; destruct (s_resv S); [reflexivity|discriminate|discriminate]).
  destruct Hq as ((Hx0 & Hx28) & J0 & J1 & J2 & J3 & J4 & J5 & J6).
  destruct J0 as (w0 & F0 & E0 & D0). destruct J1 as (w1 & F1 & E1 & D1). destruct J2 as (w2 & F2 & E2 & D2).
  destruct J3 as (w3 & F3 & E3 & D3). destruct J4 as (w4 & F4 & E4 & D4). destruct J5 as (w5 & F5 & E5 & D5).
  destruct J6 as (w6 & F6 & E6 & D6).
  unfold qpc in F0, F1, F2, F3, F4, F5, F6.
  replace (x + 4 * 0) with x in F0 by lia. replace (x + 4 * 1) with (x + 4) in F1 by lia. replace (x + 4 * 2) with (x + 8) in F2 by lia.
  replace (x + 4 * 3) with (x + 12) in F3 by lia. replace (x + 4 * 4) with (x + 16) in F4 by lia.
  replace (x + 4 * 5) with (x + 20) in F5 by lia. replace (x + 4 * 6) with (x + 24) in F6 by lia.
  unfold HAS in Hh. rewrite Forall_forall in Hh. destruct (Hh (b, l) (nth_error_In _ _ Hj)) as (C1 & C2 & C3 & C4). cbv zeta in *.
  cbn [fst snd] in C1, C2, C3, C4.
  set (B := uE E b) in *. set (L := uE E l) in *.
  pose proof (uE_range E b) as RB. pose proof (uE_range E l) as RL. fold B L in RB, RL.
  assert (Hwe : B + L < wend B L) by (unfold wend; pose proof (Z.div_mod (B + L) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (B + L) 8 ltac:(lia)); lia).
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  (* [comment removed for export] *)
  set (byte := fun k : nat => match mem0 (Z_to_bv 64 (B + Z.of_nat k)) with Some bb => bb | None => Z_to_bv 8 0 end).
  set (Ln := Z.to_nat L).
  assert (Hfz : forall k : nat, (k <= Ln)%nat -> ms_mem (restrict H ms) (Z_to_bv 64 (B + Z.of_nat k)) = mem0 (Z_to_bv 64 (B + Z.of_nat k))).
  { intros k Hkk. apply (frz_restrict segs LIMIT model0 mem0 E S M ms model _ Hd). apply (proj1 (C2 (B + Z.of_nat k) ltac:(unfold Ln in Hkk; lia))). }
  assert (Rd : forall k, (k <= Ln)%nat -> rdn segs (mrestrict H (ms_mem ms)) (Z_to_bv 64 (B + Z.of_nat k)) 1 = Some [byte k]).
  { intros k Hkk. apply rdn1_of. change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms)). rewrite (Hfz k Hkk). unfold byte.
    destruct (mem0 (Z_to_bv 64 (B + Z.of_nat k))) as [bb|] eqn:Hm; [reflexivity|]. exfalso.
    exact (proj2 (C2 (B + Z.of_nat k) ltac:(unfold Ln in Hkk; lia)) Hm). }
  assert (Bnz : forall k, (k < Ln)%nat -> bv_unsigned (byte k) <> 0).
  { intros k Hkk. destruct (C3 (Z.of_nat k) ltac:(unfold Ln in Hkk; lia)) as (bb & Hm & Hnz). unfold byte. rewrite Hm. exact Hnz. }
  assert (Bz : bv_unsigned (byte Ln) = 0).
  { unfold byte. replace (B + Z.of_nat Ln) with (B + L) by (unfold Ln; lia). rewrite C4. reflexivity. }
  (* [comment removed for export] *)
  assert (H10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 B).
  { replace (10%bv : reg) with (xr 10) by (apply bv_eq; reflexivity). rewrite (HR (xr 10)), Hb10. unfold B, uE. symmetry. apply u64_of. }
  destruct (is_const_sound E _ r R1) as [Hr1 Hr64].
  assert (Hra : getr (ms_regs ms) 1%bv = Z_to_bv 64 r) by (replace (1%bv : reg) with (xr 1) by (apply bv_eq; reflexivity); rewrite (HR (xr 1)); exact Hr1).
  assert (Hret : ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite u_small by exact Hr64; assumption).
  destruct (@istrlen_run (mkFP (ms_fregs ms) (ms_fcsr ms)) segs x w0 w1 w2 w3 w4 w5 w6 (conj Hx0 Hx28) F0 F1 F2 F3 F4 F5 F6
              E0 E1 E2 E3 E4 E5 E6 D0 D1 D2 D3 D4 D5 D6 (mrestrict H (ms_mem ms)) (ms_rom ms) B Ln byte
              ltac:(unfold Ln; lia) Rd Bnz Bz (ms_regs ms) (Z_to_bv 64 r) H10 Hret Hra) as (regs' & Hms & P10 & P11 & P12 & Pag).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 x) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. subst pcv. reflexivity. }
  apply (den_run_post segs cfg LIMIT model0 mem0 Hwx E S M ms model T regs' r [(xr 10, l); (xr 11, laddc l 1); (xr 12, lconst 0)] [] Hd Hrv).
  - fold H. rewrite Hmsr. apply fx_isteps_of_msteps. exact Hms.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
      (split; [intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]).
    + split; [exact Hwl|]. replace (xr 10) with (10%bv : reg) by (apply bv_eq; reflexivity). rewrite P10. unfold Ln. rewrite Z2Nat.id by lia. unfold L, uE. apply u64_of.
    + split; [exact (lwf_laddc _ _ 1 Hwl)|]. replace (xr 11) with (11%bv : reg) by (apply bv_eq; reflexivity). rewrite P11. unfold Ln. rewrite Z2Nat.id by lia. rewrite lden_laddc. reflexivity.
    + split; [apply lwf_lconst|]. replace (xr 12) with (12%bv : reg) by (apply bv_eq; reflexivity). rewrite P12. rewrite lden_lconst. reflexivity.
  - constructor.
  - intros rr Es _. cbn [existsb fst] in Es. rewrite !orb_false_iff in Es. destruct Es as (N10 & N11 & N12 & _).
    apply Pag. intros [Hc|[Hc|Hc]]; subst rr.
    + replace (10%bv : reg) with (xr 10) in N10 by (apply bv_eq; reflexivity). rewrite bv_eqb_refl in N10. discriminate.
    + replace (11%bv : reg) with (xr 11) in N11 by (apply bv_eq; reflexivity). rewrite bv_eqb_refl in N11. discriminate.
    + replace (12%bv : reg) with (xr 12) in N12 by (apply bv_eq; reflexivity). rewrite bv_eqb_refl in N12. discriminate.
  - exact Hk.
Qed.
End Nodes.
