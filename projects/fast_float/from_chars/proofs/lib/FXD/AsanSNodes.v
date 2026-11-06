(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefMemcpyLib ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode FxRunPost FxSNodes AsanMBase AsanMchrRef.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanMBase OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanMchrRef.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation ASEGSN := Asan.M.loaded_segments.

Lemma rdn_of_pts : forall segs (m : word -> option byte) n (a : Z) (f : nat -> byte), 0 <= a -> a + Z.of_nat n <= two64 ->
  (forall k, (k < n)%nat -> m (Z_to_bv 64 (a + Z.of_nat k)) = Some (f k)) ->
  rdn segs m (Z_to_bv 64 a) n = Some (List.map f (seq 0 n)).
Proof.
  intros segs m n. induction n as [|n IH]; intros a f Ha Hn Hm; [reflexivity|].
  cbn [rdn]. pose proof (Hm O ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0. rewrite H0.
  assert (Hadd : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite Hadd. rewrite (IH (a + 1) (fun k => f (Datatypes.S k)) ltac:(lia) ltac:(lia)).
  - cbn [seq List.map]. rewrite <- seq_shift, map_map. reflexivity.
  - intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (Datatypes.S k)) by lia. apply Hm. lia.
Qed.

Definition MCH_PC : Z := 0xd2b88.
Definition MCH_HAVS : list reg := List.map xr [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].
(* [comment removed for export] *)
Definition ro_cover (R : region) : bool :=
  match rg_kind R, is_const (rg_base R), is_const (rg_size R) with
  | RO, Some c0, Some c1 => (Z.leb c0 0x103a8 && Z.leb 0x103d0 (c0 + c1))%bool
  | _, _, _ => false
  end.
Definition mch_chk (j : nat) (S : sst) (a : list (lin * lin)) : bool :=
  match nth_error a j, rg_is S 1, rg_is S 11, rg_is S 12 with
  | Some (b, l), Some r, Some 0, Some n =>
      (Z.eqb (s_pc S) MCH_PC && lin_eqb (rget (s_regs S) (rkey (xr 10))) b && Z.eqb (r mod 2) 0 && rsv_none S &&
       lwf (s_next S) b && lwf (s_next S) l && Z.leb (snd (irange (s_facts S) l) + 8) n && existsb ro_cover (s_rgs S))%bool
  | _, _, _, _ => false
  end.
Definition mch_post (j : nat) (S : sst) (a : list (lin * lin)) : sst :=
  match nth_error a j, rg_is S 1 with
  | Some (b, l), Some r => run_post S r [(xr 10, ladd b l)] MCH_HAVS
  | _, _ => S
  end.

Section Node.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.

#[using="Hwx"] Theorem den_mch : forall j S M a E ms model T,
  mch_chk j S a = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model -> HAS E M a mem0 ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (mch_post j S a) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros j S M a E ms model T Hck Hd Hh Hk.
  unfold mch_chk in Hck. unfold mch_post in Hk.
  destruct (nth_error a j) as [[b l]|] eqn:Hj; [|discriminate]. destruct (rg_is S 1) as [r|] eqn:R1; [|discriminate].
  destruct (rg_is S 11) as [[|p11|p11]|] eqn:R11; try discriminate. destruct (rg_is S 12) as [n|] eqn:R12; [|discriminate].
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  rename Hck into Hpc0. apply Z.eqb_eq in Hpc0.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx
         end.
  match goal with Hx : rsv_none S = true |- _ => rename Hx into Hrvn end.
  match goal with Hx : rget (s_regs S) (rkey (xr 10)) = b |- _ => rename Hx into Hb10 end.
  match goal with Hx : lwf (s_next S) b = true |- _ => rename Hx into Hwb end.
  match goal with Hx : lwf (s_next S) l = true |- _ => rename Hx into Hwl end.
  match goal with Hx : existsb ro_cover (s_rgs S) = true |- _ => rename Hx into Hro end.
  match goal with Hx : snd (irange (s_facts S) l) + 8 <= n |- _ => rename Hx into Hln end.
  assert (Hrv : s_resv S = RNone) by (unfold rsv_none in Hrvn; destruct (s_resv S); [reflexivity|discriminate|discriminate]).
  unfold HAS in Hh. rewrite Forall_forall in Hh. destruct (Hh (b, l) (nth_error_In _ _ Hj)) as (C1 & C2 & C3 & C4). cbv zeta in *.
  cbn [fst snd] in C1, C2, C3, C4.
  set (B := uE E b) in *. set (L := uE E l) in *.
  pose proof (uE_range E b) as RB. pose proof (uE_range E l) as RL. fold B L in RB, RL.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  pose proof (irange_sound E (s_facts S) l HF) as Rl. fold L in Rl.
  destruct (irange (s_facts S) l) as [llo lhi] eqn:Hil. cbn [fst snd] in Hln, Rl. change (bv_unsigned (lden E l)) with L in Rl.
  destruct (is_const_sound E _ n R12) as [Hn12 Hn64].
  assert (Hwe : B + L < wend B L) by (unfold wend; pose proof (Z.div_mod (B + L) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (B + L) 8 ltac:(lia)); lia).
  (* [comment removed for export] *)
  set (Wn := Z.to_nat (wend B L - B)).
  set (byte := fun k : nat => match mem0 (Z_to_bv 64 (B + Z.of_nat k)) with Some bb => bb | None => Z_to_bv 8 0 end).
  set (buf := List.map byte (seq 0 Wn)).
  assert (Hlb : length buf = Wn) by (unfold buf; rewrite length_map, length_seq; reflexivity).
  assert (Hbuf : rdn ASEGSN (mrestrict H (ms_mem ms)) (Z_to_bv 64 B) Wn = Some buf).
  { apply rdn_of_pts; [lia | unfold Wn, two64; rewrite Z2Nat.id by lia; lia|]. intros k Hkk.
    assert (Hkw : B <= B + Z.of_nat k < wend B L) by (unfold Wn in Hkk; lia).
    change (mrestrict H (ms_mem ms)) with (ms_mem (restrict H ms)).
    assert (Hfk : ms_mem (restrict H ms) (Z_to_bv 64 (B + Z.of_nat k)) = mem0 (Z_to_bv 64 (B + Z.of_nat k)))
      by (apply (frz_restrict ASEGSN LIMIT model0 mem0 E S M ms model _ Hd); exact (proj1 (C2 (B + Z.of_nat k) Hkw))).
    rewrite Hfk. unfold byte.
    destruct (mem0 (Z_to_bv 64 (B + Z.of_nat k))) as [bb|] eqn:Hm; [reflexivity|]. exfalso. exact (proj2 (C2 (B + Z.of_nat k) Hkw) Hm). }
  assert (Hnth : forall k, (k < Wn)%nat -> nth k buf (Z_to_bv 8 0) = byte k).
  { intros k Hkk. unfold buf. rewrite (nth_indep _ _ (byte O)) by (rewrite length_map, length_seq; exact Hkk).
    rewrite map_nth, seq_nth by exact Hkk. reflexivity. }
  (* [comment removed for export] *)
  assert (Hrc : rodata_clear (mrestrict H (ms_mem ms))).
  { apply existsb_exists in Hro as (R & HRin & HRc). unfold ro_cover in HRc.
    destruct (rg_kind R) eqn:HkR; try discriminate. destruct (is_const (rg_base R)) as [c0|] eqn:Hc0; [|discriminate].
    destruct (is_const (rg_size R)) as [c1|] eqn:Hc1; [|discriminate]. apply andb_prop in HRc as [X1 X2]. apply Z.leb_le in X1, X2.
    intros i Hi. rewrite Forall_forall in HG. destruct (HG R HRin) as (_ & _ & Hpts & _).
    destruct (is_const_sound E _ c0 Hc0) as [Hb0 Hb64]. destruct (is_const_sound E _ c1 Hc1) as [Hs0 Hs64].
    assert (Hrs : rsz E R = c1) by (unfold rsz; rewrite Hs0; apply u_small; exact Hs64).
    specialize (Hpts (i - c0) ltac:(rewrite Hrs; lia)). rewrite HkR in Hpts. destruct Hpts as [Hnone _].
    rewrite Hb0, u_small in Hnone by exact Hb64. replace (c0 + (i - c0)) with i in Hnone by lia. exact Hnone. }
  assert (HmH : mchrH (mrestrict H (ms_mem ms)) (Z_to_bv 64 B) buf L n).
  { constructor.
    - rewrite Hlb. exact Hbuf.
    - rewrite u_small by (unfold two64; lia). rewrite Hlb. unfold Wn. rewrite Z2Nat.id by lia. unfold wend in *. lia.
    - rewrite u_small by (unfold two64; lia). rewrite Hlb. unfold Wn. rewrite Z2Nat.id by lia. unfold two64 in *. lia.
    - lia.
    - rewrite (Hnth (Z.to_nat L) ltac:(unfold Wn; lia)). unfold byte. rewrite Z2Nat.id by lia. rewrite C4. reflexivity.
    - intros k Hkk. rewrite (Hnth k ltac:(unfold Wn; lia)). destruct (C3 (Z.of_nat k) ltac:(lia)) as (bb & Hm & Hnz).
      unfold byte. rewrite Hm. exact Hnz.
    - lia.
    - unfold two64 in Hn64. lia.
    - exact Hrc. }
  (* [comment removed for export] *)
  assert (H10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 B).
  { replace (10%bv : reg) with (xr 10) by (apply bv_eq; reflexivity). rewrite (HR (xr 10)), Hb10. unfold B, uE. symmetry. apply u64_of. }
  destruct (is_const_sound E _ r R1) as [Hr1 Hr64].
  assert (Hra : getr (ms_regs ms) 1%bv = Z_to_bv 64 r) by (replace (1%bv : reg) with (xr 1) by (apply bv_eq; reflexivity); rewrite (HR (xr 1)); exact Hr1).
  assert (H11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 0).
  { replace (11%bv : reg) with (xr 11) by (apply bv_eq; reflexivity). rewrite (HR (xr 11)). exact (proj1 (is_const_sound E _ 0 R11)). }
  assert (H12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 n) by (replace (12%bv : reg) with (xr 12) by (apply bv_eq; reflexivity); rewrite (HR (xr 12)); exact Hn12).
  assert (Hret : ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite u_small by exact Hr64; assumption).
  destruct (@ref_memchr0 (mkFP (ms_fregs ms) (ms_fcsr ms)) (mrestrict H (ms_mem ms)) (Z_to_bv 64 B) buf L n (ms_rom ms) (ms_regs ms)
              (Z_to_bv 64 r) HmH Hret Hra H10 H11 H12) as (regs' & Hms & Hkc & P10).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (0xd2b88 : word) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. unfold MCH_PC in Hpc. subst pcv.
    unfold restrict, mkst. cbn. f_equal. apply bv_eq. reflexivity. }
  apply (den_run_post ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs' r [(xr 10, ladd b l)] MCH_HAVS Hd Hrv).
  - fold H. rewrite Hmsr. apply fx_isteps_of_msteps. exact Hms.
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    split; [intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|].
    split; [exact (lwf_ladd _ _ _ Hwb Hwl)|].
    replace (xr 10) with (10%bv : reg) by (apply bv_eq; reflexivity). rewrite P10. rewrite u_small by (unfold two64; lia).
    rewrite lden_ladd. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. fold (uE E b) (uE E l). fold B L. reflexivity.
  - unfold MCH_HAVS. repeat constructor; intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate.
  - intros rr Es Eh.
    assert (Hex : exists k, 0 <= k < 32 /\ rr = Z_to_bv 5 k).
    { exists (bv_unsigned rr). split; [pose proof (bv_unsigned_in_range _ rr) as X; change (bv_modulus 5) with 32 in X; lia|].
      symmetry; apply Z_to_bv_bv_unsigned. }
    destruct Hex as (k & Hk32 & ->).
    assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
    all: first
      [ (vm_compute in Es; discriminate Es) | (vm_compute in Eh; discriminate Eh)
      | (replace (Z_to_bv 5 0) with (0%bv : reg) by (apply bv_eq; reflexivity); rewrite !getr_zero; reflexivity)
      | (apply Hkc; cbn [callee_saved]; repeat (first [left; apply bv_eq; reflexivity | right])) ].
  - exact Hk.
Qed.
End Node.
