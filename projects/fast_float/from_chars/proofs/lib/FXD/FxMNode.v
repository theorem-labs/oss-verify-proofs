(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition msite_ok (segs : list Segment) (pcw : Z) : Prop :=
  qins segs pcw 0 (Load SZ8 true (xr 17) (xr 10) (Z_to_bv 12 0)) /\ qins segs pcw 1 (Op ALU_XOR (xr 17) (xr 17) (xr 15)) /\
  qins segs pcw 2 (Op ALU_SUB (xr 5) (xr 13) (xr 17)) /\ qins segs pcw 3 (Op ALU_OR (xr 17) (xr 5) (xr 17)) /\
  qins segs pcw 4 (Op ALU_AND (xr 17) (xr 17) (xr 14)) /\ qins segs pcw 5 (Branch BC_NE (xr 17) (xr 14) (Z_to_bv 13 52)) /\
  qins segs pcw 18 (OpImm ALU_ADD (xr 13) (xr 12) (Z_to_bv 12 0)) /\ qins segs pcw 19 (Load SZ1 false (xr 12) (xr 10) (Z_to_bv 12 0)) /\
  qins segs pcw 20 (Branch BC_NE (xr 12) (xr 11) (Z_to_bv 13 8164)) /\ qins segs pcw 13 (OpImm ALU_ADD (xr 13) (xr 13) (Z_to_bv 12 4095)) /\
  qins segs pcw 14 (OpImm ALU_ADD (xr 10) (xr 10) (Z_to_bv 12 1)) /\ qins segs pcw 15 (Branch BC_NE (xr 13) (xr 0) (Z_to_bv 13 8176)) /\
  qins segs pcw 11 (Load SZ1 false (xr 12) (xr 10) (Z_to_bv 12 0)) /\ qins segs pcw 12 (Branch BC_EQ (xr 12) (xr 11) (Z_to_bv 13 20)) /\
  qins segs pcw 17 (Jalr (xr 0) (xr 1) (Z_to_bv 12 0)).

Definition rg_is (S : sst) (k : Z) : option Z := is_const (rget (s_regs S) (rkey (xr k))).

Definition mc_chk (img : tree Z) (pcw : Z) (S : sst) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let s := rget (s_regs S) (rkey (xr 10)) in let n := rget (s_regs S) (rkey (xr 12)) in
  match rg_is S 11, rg_is S 13, rg_is S 14, rg_is S 15, rg_is S 1, s_resv S,
        load_at img fs rgs s SZ8 false, load_at img fs rgs s SZ1 false, load_at img fs rgs (laddc s 1) SZ1 false with
  | Some 0, Some c, Some h, Some 0, Some r, RNone, Some _, Some (Some l0), Some (Some l1) =>
      match is_const l0, is_const l1 with
      | Some b0, Some 0 =>
          (Z.eqb (s_pc S) pcw && Z.eqb c MC_C && Z.eqb h MC_H && Z.eqb (r mod 2) 0 && Z.ltb 0 b0 && Z.ltb b0 256 &&
           Z.leb 2 (fst (irange fs n)) && Z.ltb (snd (irange fs s) + 8) two64 && lwf (s_next S) s && lwf (s_next S) n)%bool
      | _, _ => false
      end
  | _, _, _, _, _, _, _, _, _ => false
  end.

Definition mc_post (S : sst) : sst :=
  let s := rget (s_regs S) (rkey (xr 10)) in let n := rget (s_regs S) (rkey (xr 12)) in
  let r := match rg_is S 1 with Some r => r | None => 0 end in
  SST r (rset (rset (rset (rset (rset (s_regs S) (rkey (xr 10)) (laddc s 1)) (rkey (xr 12)) (lconst 0)) (rkey (xr 13)) (laddc n (-1)))
                    (rkey (xr 17)) (lvar (s_next S))) (rkey (xr 5)) (lvar (Pos.succ (s_next S))))
      (s_rgs S) (s_facts S) (Pos.succ (Pos.succ (s_next S))) (s_resv S).

Lemma rdn_first2 : forall segs m (a : word) bs, rdn segs m a 8 = Some bs ->
  exists b0 b1 rest, bs = b0 :: b1 :: rest /\ rdn segs m a 1 = Some [b0] /\ rdn segs m (v_addi a 1) 1 = Some [b1].
Proof.
  intros segs m a bs H.
  assert (Hs : forall k a', rdn segs m a' (Datatypes.S k) = match (match m a' with Some b => Some b | None => seg_rom segs a' end) with
                                                         | Some b => match rdn segs m (a' + 1)%bv k with Some r => Some (b :: r) | None => None end
                                                         | None => None end) by reflexivity.
  rewrite Hs in H.
  destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [x0|] eqn:E0; [|discriminate].
  destruct (rdn segs m (a + 1)%bv 7) as [r1|] eqn:Er1; [|discriminate]. injection H as <-.
  rewrite Hs in Er1.
  destruct (match m (a + 1)%bv with Some b => Some b | None => seg_rom segs (a + 1)%bv end) as [x1|] eqn:E1; [|discriminate].
  destruct (rdn segs m (a + 1 + 1)%bv 6) as [r|] eqn:Er; [|discriminate]. injection Er1 as <-.
  exists x0, x1, r. split; [reflexivity|]. split.
  - rewrite Hs, E0. reflexivity.
  - assert (Ha : v_addi a 1 = (a + 1)%bv).
    { unfold v_addi. apply bv_eq. rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity. }
    rewrite Ha, Hs, E1. reflexivity.
Qed.

Ltac neqr := first [ assumption | apply not_eq_sym; assumption |
                     let Hc := fresh "Hc" in intro Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate ].

Section Node.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Himg : img_ok segs img.

#[using="Hwx Himg"] Theorem den_mc : forall pcw S M E ms model T,
  msite_ok segs pcw -> mc_chk img pcw S = true -> DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (mc_post S) M ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Himg : LiaFast.U) => LiaFast.u0).
  intros pcw S M E ms model T Hq Hck Hd Hk.
  destruct Hq as (J0 & J1 & J2 & J3 & J4 & J5 & J18 & J19 & J20 & J13 & J14 & J15 & J11 & J12 & J17).
  unfold mc_chk in Hck.
  set (fs := s_facts S) in *. set (s := rget (s_regs S) (rkey (xr 10))) in *. set (n := rget (s_regs S) (rkey (xr 12))) in *.
  destruct (rg_is S 11) as [[|p11|p11]|] eqn:R11; try discriminate.
  destruct (rg_is S 13) as [c|] eqn:R13; [|discriminate]. destruct (rg_is S 14) as [h|] eqn:R14; [|discriminate].
  destruct (rg_is S 15) as [[|p15|p15]|] eqn:R15; try discriminate. destruct (rg_is S 1) as [r|] eqn:R1; [|discriminate].
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (load_at img fs (s_rgs S) s SZ8 false) as [ow|] eqn:Hlw; [|discriminate].
  destruct (load_at img fs (s_rgs S) s SZ1 false) as [[l0|]|] eqn:Hl0; try discriminate.
  destruct (load_at img fs (s_rgs S) (laddc s 1) SZ1 false) as [[l1|]|] eqn:Hl1; try discriminate.
  destruct (is_const l0) as [b0v|] eqn:Hb0c; [|discriminate]. destruct (is_const l1) as [[|p1|p1]|] eqn:Hb1c; try discriminate.
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  rename Hck into Hpc0. apply Z.eqb_eq in Hpc0.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx
         end.
  subst c h.
  match goal with Hx : lwf (s_next S) s = true |- _ => rename Hx into Hws end.
  match goal with Hx : lwf (s_next S) n = true |- _ => rename Hx into Hwn end.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  assert (Hreg : forall k z, rg_is S k = Some z -> getr (ms_regs ms) (xr k) = Z_to_bv 64 z).
  { intros k z Hz. rewrite (HR (xr k)). unfold rg_is in Hz. exact (proj1 (is_const_sound E _ z Hz)). }
  set (sw := lden E s). set (nw := lden E n).
  assert (H10 : getr (ms_regs ms) (xr 10) = sw) by exact (HR (xr 10)).
  assert (H12 : getr (ms_regs ms) (xr 12) = nw) by exact (HR (xr 12)).
  pose proof (irange_sound E fs n HF) as Rn. fold nw in Rn.
  pose proof (irange_sound E fs s HF) as Rs. fold sw in Rs.
  (* [comment removed for export] *)
  destruct (load_at_sound segs E img fs (s_rgs S) s SZ8 false ow (ms_mem (restrict H ms)) Himg HG HF Hlw) as (bsw & Hrw & _).
  rewrite ov_rdn in Hrw. cbn [nbytes] in Hrw. fold sw in Hrw.
  destruct (rdn_first2 segs _ sw bsw Hrw) as (x0 & x1 & rest & -> & Hx0 & Hx1).
  destruct (load_at_sound segs E img fs (s_rgs S) s SZ1 false _ (ms_mem (restrict H ms)) Himg HG HF Hl0) as (bs0 & Hr0 & Hv0).
  destruct (load_at_sound segs E img fs (s_rgs S) (laddc s 1) SZ1 false _ (ms_mem (restrict H ms)) Himg HG HF Hl1) as (bs1 & Hr1 & Hv1).
  specialize (Hv0 _ eq_refl). specialize (Hv1 _ eq_refl). rewrite ov_rdn in Hr0, Hr1. cbn [nbytes] in Hr0, Hr1. fold sw in Hr0.
  assert (Hs1 : lden E (laddc s 1) = v_addi sw 1) by (rewrite lden_laddc; reflexivity).
  rewrite Hs1 in Hr1. rewrite Hx0 in Hr0. rewrite Hx1 in Hr1. injection Hr0 as <-. injection Hr1 as <-.
  destruct (is_const_sound E l0 b0v Hb0c) as [HE0 _]. destruct (is_const_sound E l1 0 Hb1c) as [HE1 _].
  rewrite HE0, ld1_byte in Hv0. rewrite HE1, ld1_byte in Hv1.
  assert (Hb0 : bv_unsigned x0 <> 0).
  { apply (f_equal bv_unsigned) in Hv0. rewrite !Z_to_bv_unsigned in Hv0. pose proof (bv_unsigned_in_range _ x0) as R0. change (bv_modulus 8) with 256 in R0.
    unfold bv_wrap in Hv0. change (bv_modulus 64) with (2 ^ 64) in Hv0. rewrite !Z.mod_small in Hv0 by lia. lia. }
  assert (Hb1 : bv_unsigned x1 = 0).
  { apply (f_equal bv_unsigned) in Hv1. rewrite !Z_to_bv_unsigned in Hv1. pose proof (bv_unsigned_in_range _ x1) as R0. change (bv_modulus 8) with 256 in R0.
    unfold bv_wrap in Hv1. change (bv_modulus 64) with (2 ^ 64) in Hv1. rewrite !Z.mod_small in Hv1 by lia. lia. }
  (* [comment removed for export] *)
  destruct (is_const_sound E _ r R1) as [_ Hr64].
  assert (Hra : getr (ms_regs ms) (xr 1) = Z_to_bv 64 r) by exact (Hreg 1 r R1).
  pose proof (Hreg 11 0 R11) as H11. pose proof (Hreg 13 MC_C R13) as H13. pose proof (Hreg 14 MC_H R14) as H14. pose proof (Hreg 15 0 R15) as H15.
  destruct (@mc_isteps (mkFP (ms_fregs ms) (ms_fcsr ms)) segs pcw J0 J1 J2 J3 J4 J5 J18 J19 J20 J13 J14 J15 J11 J12 J17
              (ms_regs ms) (mrestrict H (ms_mem ms)) (ms_rom ms) sw nw (Z_to_bv 64 r) x0 x1 rest H10 H11 H12 H13 H14 H15 Hra
              ltac:(lia) ltac:(rewrite u_small by exact Hr64; assumption) ltac:(unfold two64 in *; lia) Hrw Hb0 Hb1 Hx1 Hx0)
    as (regs' & Hst & R10' & R12' & R13' & Rothers).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (qpc pcw 0) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. subst pcv.
    unfold restrict, mkst, qpc. cbn [ms_regs ms_fregs ms_fcsr ms_mem ms_rom fp_regs fp_csr ms_pc_val ms_svc_pending ms_resv].
    replace (pcw + 4 * 0) with pcw by lia. reflexivity. }
  set (x1' := s_next S). set (x2' := Pos.succ (s_next S)).
  set (E1 := upd (upd E x1' (getr regs' (xr 17))) x2' (getr regs' (xr 5))).
  assert (Ha1 : agree (s_next S) E E1).
  { intros y Hy. unfold E1, upd. destruct (Pos.eqb_spec y x2'); [unfold x2' in *; lia|]. destruct (Pos.eqb_spec y x1'); [unfold x1' in *; lia|]. reflexivity. }
  assert (HE1a : E1 x1' = getr regs' (xr 17)) by (unfold E1, upd; destruct (Pos.eqb_spec x1' x2'); [unfold x1', x2' in *; lia|]; rewrite Pos.eqb_refl; reflexivity).
  assert (HE1b : E1 x2' = getr regs' (xr 5)) by (unfold E1, upd; rewrite Pos.eqb_refl; reflexivity).
  set (S1 := bump S (Pos.succ x2')).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump, x2'; cbn [s_next]; lia).
  assert (Hy1 : (x1' < s_next S1)%positive) by (unfold S1, bump, x1', x2'; cbn [s_next]; lia).
  assert (Hy2 : (x2' < s_next S1)%positive) by (unfold S1, bump, x2'; cbn [s_next]; lia).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model) by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | unfold x2'; lia]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  assert (Hpost : sden segs E1 (mc_post S) (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 r) (mrestrict H (ms_mem ms)) (ms_rom ms))).
  { pose proof (sden_regs segs E1 S1 (restrict H ms) (s_regs (mc_post S)) regs' r ltac:(rewrite <- HH1; exact (dn_sden _ _ _ _ _ _ _ _ _ HdS1))) as X.
    cbn [restrict ms_fregs ms_fcsr ms_resv ms_mem ms_rom] in X. rewrite Hrsv in X.
    unfold mc_post at 1. rewrite R1. unfold mkst. cbn [fp_regs fp_csr]. apply X.
    intros E' Ha' HR'.
    assert (HsE' : lden E' s = sw) by (unfold sw; apply (lden_agree_wf (s_next S) E E' s Hws); exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' Hnx Ha'))).
    assert (HnE' : lden E' n = nw) by (unfold nw; apply (lden_agree_wf (s_next S) E E' n Hwn); exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' Hnx Ha'))).
    assert (HE'1 : E' x1' = getr regs' (xr 17)) by (rewrite <- HE1a; symmetry; apply Ha'; exact Hy1).
    assert (HE'2 : E' x2' = getr regs' (xr 5)) by (rewrite <- HE1b; symmetry; apply Ha'; exact Hy2).
    set (r5 := regupd (regupd (regupd (regupd (regupd (ms_regs ms) (xr 10) (v_addi sw 1)) (xr 12) (Z_to_bv 64 0)) (xr 13) (v_addi nw (-1)))
                       (xr 17) (getr regs' (xr 17))) (xr 5) (getr regs' (xr 5))).
    assert (R0 : forall E0 R regs (rd : reg) l v, rd <> 0%bv -> regs_ok E0 R regs -> lden E0 l = v ->
                   regs_ok E0 (rset R (rkey rd) l) (regupd regs rd v)).
    { intros E0 R regs rd l v Hne HR0 Hv. pose proof (regs_ok_upd E0 R regs rd l v HR0 Hv) as X0.
      rewrite (PropExec.bv_eqb_neq rd 0%bv Hne) in X0. exact X0. }
    assert (HR5 : regs_ok E' (s_regs (mc_post S)) r5).
    { unfold mc_post. cbn [s_regs]. fold s n. unfold r5.
      apply R0; [neqr| |]; [apply R0; [neqr| |]; [apply R0; [neqr| |]; [apply R0; [neqr| |]; [apply R0; [neqr| |]|]|]|]|].
      - exact HR'.
      - rewrite lden_laddc, HsE'. reflexivity.
      - rewrite lden_lconst. reflexivity.
      - rewrite lden_laddc, HnE'. reflexivity.
      - rewrite lden_lvar. exact HE'1.
      - rewrite lden_lvar. exact HE'2. }
    intros rr. rewrite <- (HR5 rr). unfold r5.
    destruct (decide (rr = xr 5)) as [->|N5]; [rewrite getr_same by neqr; reflexivity|]. rewrite getr_other by exact N5.
    destruct (decide (rr = xr 17)) as [->|N17]; [rewrite getr_same by neqr; reflexivity|]. rewrite getr_other by exact N17.
    destruct (decide (rr = xr 13)) as [->|N13]; [rewrite getr_same by neqr; exact R13'|]. rewrite getr_other by exact N13.
    destruct (decide (rr = xr 12)) as [->|N12]; [rewrite getr_same by neqr; exact R12'|]. rewrite getr_other by exact N12.
    destruct (decide (rr = xr 10)) as [->|N10]; [rewrite getr_same by neqr; exact R10'|]. rewrite getr_other by exact N10.
    exact (Rothers rr N10 N12 N13 N17 N5). }
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E1 S1 M ms model T (mc_post S)
           (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 r) (mrestrict H (ms_mem ms)) (ms_rom ms)) E1 HdS1).
  - rewrite HH1, Hmsr. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - unfold mc_post, S1, bump, x2'. cbn [s_next]. apply Pos.le_refl.
  - intros y _. rewrite HH1. reflexivity.
  - reflexivity.
  - intros E2 ms2 model2 HD2 Ha2. apply (Hk E2 ms2 model2); [|exact HD2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.
End Node.
