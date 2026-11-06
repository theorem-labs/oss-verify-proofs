(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require XformFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition law_flag_stmt (AInv : AA -> valuation -> list word -> Model -> Prop) : Prop :=
  forall A rho tp md fs, AInv A rho tp md -> In fs (aa_frames A) ->
    rm rho (Z_to_bv 64 (frame_flag (aa_geom A) fs)) = Some (Z_to_bv 8 1).
Definition law_fshadow_stmt (AInv : AA -> valuation -> list word -> Model -> Prop) : Prop :=
  forall A rho tp md f s z, AInv A rho tp md -> In (f, s) (aa_frames A) -> Sh f <= z < Sh (f + s) ->
    rm rho (Z_to_bv 64 z) <> None.

Definition shobj (g : positive) (k1 k2 : Z) (cells : list cell) (d : odefault) : sobj :=
  mkObj (SVar g) (SLit (SHADOW_OFF + k1)) (SLit (SHADOW_OFF + k2)) cells d.

Lemma Sh_val : forall a, Sh a = SHADOW_OFF + a / 8.
Proof. intros a. unfold Sh. lia. Qed.

Lemma word_in_aligned_range : forall y lo n j,
  lo mod 8 = 0 -> n mod 8 = 0 -> 0 <= j < 8 ->
  lo <= y / 8 * 8 + j < lo + n -> lo <= y < lo + n.
Proof.
  intros y lo n j Hlo Hn Hj H.
  pose proof (Z.div_mod y 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as E2. pose proof (Z.div_mod n 8 ltac:(lia)) as E3.
  nia.
Qed.

Lemma Sh_range_iff : forall p sz x, p mod 8 = 0 -> sz mod 8 = 0 ->
  Sh p <= Sh x < Sh p + sz / 8 <-> p <= x < p + sz.
Proof.
  intros p sz x Hp Hs. unfold Sh.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)). nia.
Qed.

Ltac cm_stack H := first [exact H | match goal with E : aa_geom _ = aa_geom _ |- _ => first [rewrite E; exact H | rewrite <- E; exact H] end].
Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.
Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.
Variable E : aentry.
Variable AInv : AA -> valuation -> list word -> Model -> Prop.
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : forall a, in_rangesZ CST a -> 0 <= a < IMG_HI.
Ltac hcst H := match type of H with _ /\ _ => let H' := fresh in destruct H as [H H']; apply HCST in H | _ => apply HCST in H end.
Hypothesis HXGL : forall a, in_rangesZ XGL a -> 0 <= a < IMG_HI.
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.

Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : list (Z * Z * Z).
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.
Hypothesis HNP : NP_okA NP.

Let JAi := JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA.
Let JA := JA AInv CST XGL NP Kc rho0 P0f FB FF BX PA.

Lemma own_frame_facts : forall Ai rho tp md fr fe,
  AInv Ai rho tp md -> TPA rho0 Ai -> frinA FF Ai rho fr -> In fe fr ->
  let p := fst (frv rho fe) in let sz := snd (frv rho fe) in let fl := uval rho (snd fe) in
  In (p, sz) (aa_frames Ai) /\ fl = frame_flag (aa_geom Ai) (p, sz)
  /\ p mod 64 = 0 /\ sz mod 64 = 0 /\ 64 <= sz
  /\ ((IMG_HI <= p /\ ltac:(let v := eval cbv in IMG_HI in exact v) <= p)
      /\ (p + sz <= SHADOW_OFF \/ HIGH_SHADOW_END <= p) /\ (p + sz <= 2147450880 \/ 17594333495296 <= p))
  /\ (p + sz <= T0 rho0 /\ T0 rho0 <= 140737479966720)
  /\ ((IMG_HI <= fl /\ ltac:(let v := eval cbv in IMG_HI in exact v) <= fl)
      /\ (fl + 1 <= SHADOW_OFF \/ HIGH_SHADOW_END <= fl) /\ (fl + 1 <= 2147450880 \/ 17594333495296 <= fl))
  /\ (fl + 1 <= T0 rho0 /\ T0 rho0 <= 140737479966720)
  /\ (forall b n, In (b, n) (aa_live Ai) -> b + n <= fl \/ fl + 1 <= b - 16)
  /\ (forall f' s', In (f', s') (aa_frames Ai) -> f' + s' <= fl \/ fl + 1 <= f').
Proof using ALA HCST.
  intros Ai rho tp md fr fe HM HT (HFR0 & _ & _) Hin p sz fl.
  pose proof (proj1 (Forall_forall _ _) HFR0 fe Hin) as (E1 & E2 & E3).
  assert (Ep : frv rho fe = (p, sz)) by (subst p sz; destruct (frv rho fe); reflexivity). rewrite Ep in E1, E2, E3.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (_ & _ & HFr).
  destruct (HFr p sz E1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). rewrite (TPA_top rho0 Ai HT) in F4, F5, F7.
  subst fl. rewrite E2. pose proof (topG_range (aa_geom Ai)) as TG. rewrite (TPA_top rho0 Ai HT) in TG.
  repeat split; auto; try apply F4; try apply F6; lia.
Qed.

Lemma frames_sep : forall Ai rho tp md f1 s1 f2 s2,
  AInv Ai rho tp md -> In (f1, s1) (aa_frames Ai) -> In (f2, s2) (aa_frames Ai) -> (f1, s1) <> (f2, s2) ->
  f1 + s1 <= f2 \/ f2 + s2 <= f1.
Proof using ALA.
  intros Ai rho tp md f1 s1 f2 s2 HM H1 H2 Hne.
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (HPD & _ & _).
  apply In_nth_error in H1 as [i Hi]. apply In_nth_error in H2 as [j Hj].
  assert (Hij : i <> j) by (intros ->; rewrite Hi in Hj; injection Hj; intros; subst; apply Hne; reflexivity).
  set (L := aa_live Ai) in *.
  assert (Hi' : nth_error (L ++ aa_frames Ai) (length L + i) = Some (f1, s1)) by (rewrite nth_error_app2 by lia; rewrite Nat.add_comm, Nat.add_sub; exact Hi).
  assert (Hj' : nth_error (L ++ aa_frames Ai) (length L + j) = Some (f2, s2)) by (rewrite nth_error_app2 by lia; rewrite Nat.add_comm, Nat.add_sub; exact Hj).
  destruct (Nat.lt_ge_cases (length L + i) (length L + j)) as [Hlt|Hge].
  - exact (HPD _ _ _ _ _ _ Hlt Hi' Hj').
  - assert (Hlt : (length L + j < length L + i)%nat) by lia. pose proof (HPD _ _ _ _ _ _ Hlt Hj' Hi') as P. lia.
Qed.

Lemma block_frame_sep : forall Ai rho tp md b n f s,
  AInv Ai rho tp md -> In (b, n) (aa_live Ai) -> In (f, s) (aa_frames Ai) -> b + n <= f \/ f + s <= b.
Proof using ALA.
  intros Ai rho tp md b n f s HM H1 H2.
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (HPD & _ & _).
  apply In_nth_error in H1 as [i Hi]. apply In_nth_error in H2 as [j Hj].
  set (L := aa_live Ai) in *.
  assert (Hil : (i < length L)%nat) by (apply (proj1 (nth_error_Some L i)); rewrite Hi; discriminate).
  assert (Hi' : nth_error (L ++ aa_frames Ai) i = Some (b, n)) by (rewrite nth_error_app1 by exact Hil; exact Hi).
  assert (Hj' : nth_error (L ++ aa_frames Ai) (length L + j) = Some (f, s)) by (rewrite nth_error_app2 by lia; rewrite Nat.add_comm, Nat.add_sub; exact Hj).
  apply (HPD i (length L + j)%nat b n f s); [lia | exact Hi' | exact Hj'].
Qed.

Lemma own_frame_sep : forall Ai rho tp md tv fr i fe y,
  AInv Ai rho tp md -> TPA rho0 Ai -> fbinA FB Ai -> ffinA FF Ai -> tvinA FB Ai rho tv -> frinA FF Ai rho fr ->
  nth_error fr i = Some fe ->
  pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (remove_nth i fr)) y \/ in_rangesZ XGL y ->
  ~ (fst (frv rho fe) <= y < fst (frv rho fe) + snd (frv rho fe)).
Proof using ALA HCST HXGL.
  intros Ai rho tp md tv fr i fe y HM HT HB HFF HN HFR Hnth Hy Hin.
  pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & _).
  pose proof HFR as (HFR0 & HCEN & HND).
  destruct Hy as [[Hs|[Hc|[(b & n & Hbn & Hr)|(f & s & fl & Hf & Hr)]]]|Hx].
  -   lia.
  - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  -
    assert (HL : In (b, n) (aa_live Ai)).
    { assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
      exact (fbinA_FBx FB Ai rho tv [] HB HNx _ Hbn). }
    destruct (block_frame_sep Ai rho tp md b n _ _ HM HL E1); lia.
  -
    apply In_FFx in Hf as [Hf|(x & Hx & Ex)].
    + pose proof (proj1 (Forall_forall _ _) HFR0 fe Hfe) as (_ & _ & X3).
      pose proof (X3 _ Hf) as NE. cbn [fst] in NE.
      destruct (HFF _ _ _ Hf) as [Hf1 _].
      destruct (frames_sep Ai rho tp md f s _ _ HM Hf1 E1 ltac:(intros EE; injection EE; intros; apply NE; congruence)); lia.
    + injection Ex as Ef Es Efl.
      assert (NE : frv rho x <> frv rho fe).
      { intros EQ. apply In_nth_error in Hx as [k Hk].
        destruct (remove_nth_split fr i fe Hnth) as [SP1 SP2]. rewrite SP2 in Hk.
        rewrite SP1, map_app in HND. cbn [map] in HND.
        apply (NoDup_remove_2 _ _ _ HND). rewrite <- EQ, <- map_app. apply in_map. eapply nth_error_In. exact Hk. }
      pose proof (proj1 (Forall_forall _ _) HFR0 x (In_remove_nth _ _ _ Hx)) as (X1 & _ & _).
      assert (Efx : frv rho x = (f, s)) by (unfold frv; rewrite <- Ef, <- Es; reflexivity). rewrite Efx in X1, NE.
      destruct (frames_sep Ai rho tp md f s _ _ HM X1 E1 ltac:(intros EE; apply NE; rewrite EE; destruct (frv rho fe); reflexivity)); lia.
  - apply HXGL in Hx. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Definition frame_factsA (g pR : positive) (sz : Z) : list sprop :=
  FE g (SVar pR) ++ [SPUle (SVar pR) (SLit (140737479966720 - sz)); SPUle (SVar pR) (SLit (2 ^ 47)); SPUle (SAlu ALU_ADD (SVar pR) (SLit sz)) (SVar V_TOP)].
Definition frame_open_stateA (A : axst) (objs : list sobj) (X' : list (sv * sv)) (pR : positive) (sz : Z) : axst :=
  let S := ax_S A in let g := ss_next S in
  mkAX (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
             (objs ++ [shobj g 0 (sz / 8) [] DZero]) (frame_factsA g pR sz ++ ss_facts S) (Pos.succ g) (ss_lenient S))
       X' (ax_base A).

Lemma fs_frame_size_bounds' : forall c, 0 <= c <= 6 -> 64 <= fs_frame_size c <= 4096.
Proof using . intros c Hc. apply fs_frame_size_bounds. exact Hc. Qed.

Lemma enc1 : forall z, 0 <= z < 256 -> enc_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof using .
  intros z Hz. rewrite <- (enc_bytes_1_byte (Z_to_bv 8 z)). f_equal. f_equal. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma cell1_byte : forall rho ms o off v,
  rom_ok segs ms -> obj_holds segs rho ms o -> In (mkCell (SLit off) 1 (SLit v)) (ob_cells o) ->
  - 2 ^ 62 <= off < 2 ^ 62 -> 0 <= v < 256 ->
  let a := bv_unsigned (eval rho (ob_base o)) + off in
  IMG_HI <= a < 2 ^ 64 ->
  ms_mem ms (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof using HTOP.
  intros rho ms o off v Hrom Ho Hin Hoff Hv a Ha.
  pose proof (obj_read_cell segs rho ms o _ off 1 Ho Hin ltac:(cbn; lia)) as R. cbn [SymState.c_off SymState.c_width SymState.c_val] in R.
  rewrite soff_lit_small in R by lia. specialize (R ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite Z.sub_diag, Z.mul_0_r, Z.shiftr_0_r in R. cbn [eval] in R. rewrite (u64_lit v) in R by lia.
  change (Z.to_nat 1) with 1%nat in R. rewrite (enc1 v Hv) in R. cbn [rd_bytes] in R.
  unfold oaddr in R. fold a in R.
  destruct (rd ms (Z_to_bv 64 a)) as [b8|] eqn:Hrd; [|discriminate]. injection R as ->.
  rewrite <- Hrd. symmetry. apply (rd_high segs HTOP); [exact Hrom|]. unfold IMG_HI in *. rewrite (u64_lit a) by lia. lia.
Qed.

Lemma JA_frame_open : forall tv fr bd am i pR c pF (A : axst) objs X1 X2 rho tp w,
  let n := ss_next (ax_S A) in let sz := fs_frame_size c in
  nth_error fr i = Some (SVar pR, c, SVar pF) -> 0 <= c <= 6 ->
  ax_base A = SLit SHADOW_OFF ->
  ss_objs (ax_S A) = objs ++ [flagbyte_obj (SVar pF) [mkCell (SLit 0) 1 (SLit 1)]] ->
  ax_X A = X1 ++ (SVar pR, SLit sz) :: X2 ->
  swf (ax_S (frame_open_stateA A objs (X1 ++ X2) pR sz)) = true ->
  (NP <=? n)%positive = true -> nd_below n (NDA tv fr bd am) = true ->
  (forall Ai rho1 tp1 md1, Forall (holds rho) (ss_facts (ax_S A)) -> P0f rho0 -> agree_vals NP rho0 rho -> AInv Ai rho1 tp1 md1 -> TPA rho0 Ai -> T_ok rho (topG (aa_geom Ai)) ->
      fbinA FB Ai -> ffinA FF Ai -> tvinA FB Ai rho tv -> tvd rho tv -> tvz rho tv -> frinA FF Ai rho fr ->
      xrs_okL CST XGL rho0 FB FF rho tv (remove_nth i fr) (X1 ++ X2)) ->
  SPA segs (JA (NDA tv fr bd am)) A rho tp w ->
  exists rho', agree_below n rho rho' /\ SPA segs (JA (NDA tv fr bd am)) (frame_open_stateA A objs (X1 ++ X2) pR sz) rho' tp w.
Proof using ALA HCST HXGL HBX HKc HTOP LFLAG HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF A objs X1 X2 rho tp w n sz Hnth Hc6 Hbase Ho HX Hwf Hnp Hnb HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  pose proof (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT) HB HFF HN HD HZ HFR) as HXL.
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9. fold sz in E1, E2, F2, F3, F5.
  set (p := uval rho (SVar pR)) in *. set (fl := uval rho (SVar pF)) in *.
  unfold aceil in F5, F7. pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am] in Hbt, Hbf, Hbb, Hba.
  pose proof (proj1 (forallb_forall _ _) Hbf fe Hfe) as Hfeb. cbn [fe fst snd sv_below] in Hfeb. apply andb_prop in Hfeb as [HpRn HpFn].
  apply Pos.ltb_lt in HpRn. apply Pos.ltb_lt in HpFn.
  pose proof Hsm as (HsmS & HMI & HwfA & Hsh & Hhz).
  pose proof HsmS as (Hswf & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & (Hall & Hpd & Hfr) & _).
  cbn [virt fst snd cfg_ms cfg_model] in Hall, Hrom.

  assert (MSfl : ms_mem (vms md tp ms) (Z_to_bv 64 fl) = Some (Z_to_bv 8 1)).
  { rewrite Ho in Hall. apply Forall_app in Hall as [_ Hfb]. apply Forall_inv in Hfb.
    pose proof (cell1_byte rho (vms md tp ms) _ 0 1 Hrom Hfb ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as C.
    cbn [ob_base flagbyte_obj] in C. fold (uval rho (SVar pF)) in C. fold fl in C. rewrite Z.add_0_r in C.
    apply C. unfold IMG_HI, HIGH_SHADOW_END in *. lia. }
  assert (RMfl : rm rho (Z_to_bv 64 fl) = Some (Z_to_bv 8 1)).
  { rewrite E2. eapply LFLAG; [exact HM | exact E1]. }

  set (R := [flagbyte_obj (SVar pF) [mkCell (SLit 0) 1 (SLit 1)]]).
  set (rho1 := rho_absorb rho R (vms md tp ms)).
  assert (AG1 : forall m, agree_below m rho rho1).
  { intros m. split; [intros; reflexivity|]. split; [intros; reflexivity|]. intros a. unfold rho1, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho R a) as [Hin|Hnin]; [|reflexivity].
    destruct Hin as (o & [<-|[]] & Hr). unfold obj_range, obj_lo_of, obj_hi_of, flagbyte_obj in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
    rewrite !soff_lit_small in Hr by lia. fold (uval rho (SVar pF)) in Hr. fold fl in Hr.
    assert (Ea : a = Z_to_bv 64 fl) by (rewrite <- (Z_to_bv_bv_unsigned 64 a); f_equal; lia). rewrite Ea, MSfl, RMfl. reflexivity. }
  assert (SP1 : SPA segs (JAi (NDA tv fr bd am) Ai kc) (ax_setS A (set_objs (ax_S A) objs)) rho1 tp (tr, mkCfg ms md)).
  { apply (SPA_unobj segs (JAi (NDA tv fr bd am) Ai kc) rho A objs R tp tr ms md Ho (conj Hsm HJ)).
    intros HJ'. eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | apply AG1 | apply mat_equiv_refl | exact HJ']. }

  pose proof (SPA_x_sub segs _ rho1 (ax_setS A (set_objs (ax_S A) objs)) (X1 ++ X2) tp _
                ltac:(cbn [ax_X ax_setS]; rewrite HX; intros r Hr; apply in_app_or in Hr as [Hr|Hr]; apply in_or_app; [left; exact Hr | right; right; exact Hr]) SP1) as SP2.
  set (A2 := ax_setX (ax_setS A (set_objs (ax_S A) objs)) (X1 ++ X2)) in SP2.

  set (rho' := rho_set_rw rho1 n (Z_to_bv 64 (p / 8))).
  assert (AG2 : agree_below n rho1 rho') by (apply agree_below_set_rw; lia).
  assert (AG : agree_below n rho rho') by (eapply agree_below_trans; [apply AG1 | exact AG2]).
  exists rho'. split; [exact AG|].
  assert (Hrm : forall a, rm rho' a = rm rho a) by (intros a; destruct AG as (_ & _ & C); symmetry; apply C).
  assert (Un : bv_unsigned (rw rho' n) = p / 8).
  { unfold rho', rho_set_rw. cbn [rw]. rewrite Pos.eqb_refl. apply u64_lit. unfold HIGH_SHADOW_END in F4. lia. }
  assert (UpR : uval rho' (SVar pR) = p) by (unfold uval; rewrite <- (eval_agree n rho rho' (SVar pR) AG ltac:(cbn; apply Pos.ltb_lt; exact HpRn)); reflexivity).
  assert (SP3 : SPA segs (JAi (NDA tv fr bd am) Ai kc) A2 rho' tp (tr, mkCfg ms md)).
  { eapply SPA_agree; [subst A2; cbn [ax_S ax_setX ax_setS set_objs ss_next]; exact AG2 | | exact SP2].
    intros HJ'. eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact AG2 | apply mat_equiv_refl | exact HJ']. }

  assert (XR : xr_ok rho (ss_objs (ax_S A)) SHADOW_OFF (SVar pR, SLit sz)).
  { unfold shadow_ok in Hsh. rewrite Hbase in Hsh. cbn [eval] in Hsh. rewrite lit_unsigned in Hsh. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hsh.
    rewrite HX in Hsh. apply Forall_app in Hsh as [_ Hsh]. apply Forall_inv in Hsh. exact Hsh. }
  unfold xr_ok in XR. cbn [fst snd] in XR. fold (uval rho (SVar pR)) in XR. fold p in XR.
  assert (UL : bv_unsigned (eval rho (SLit sz)) = sz) by (cbn [eval]; apply u64_lit; lia). rewrite UL in XR.
  destruct XR as (XR1 & XR2 & XR3).
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (PS8 : (p + sz) mod 8 = 0) by (rewrite Z.add_mod, P8, S8 by lia; reflexivity).
  assert (SP8 : Sh p mod 8 = 0).
  { unfold Sh, SHADOW_OFF. clear -F1 F4. pose proof (Z.div_mod p 64 ltac:(lia)). pose proof (Z.div_mod (p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p / 8) 8 ltac:(lia)).
    rewrite Z.add_mod by lia. replace (2147450880 mod 8) with 0 by reflexivity. rewrite Z.add_0_r, Z.mod_mod by lia. nia. }
  assert (SS8 : (sz / 8) mod 8 = 0).
  { clear -F2 Hszb. pose proof (Z.div_mod sz 64 ltac:(lia)). pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz / 8) 8 ltac:(lia)). nia. }
  assert (ZERO : forall z, Sh p <= z < Sh p + sz / 8 ->
            rm rho (Z_to_bv 64 z) = Some (Z_to_bv 8 0) /\ outside_all rho (ss_objs (ax_S A)) (Z_to_bv 64 z)).
  { intros z Hz. set (x := p + 8 * (z - Sh p)).
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Ms.
    assert (Hx : p <= x < p + sz) by (unfold Sh in Hz; subst x; rewrite P8 in Dp; rewrite S8 in Ds; unfold Sh; lia).
    assert (Ex8 : x / 8 = z - Sh p + p / 8).
    { subst x. unfold Sh in Hz |- *. rewrite P8, Z.add_0_r in Dp. rewrite Dp at 1. rewrite <- Z.mul_add_distr_l, Z.mul_comm, Z.div_mul by lia. lia. }
    assert (Ez : shadow_addr SHADOW_OFF x = Z_to_bv 64 z) by (unfold shadow_addr; f_equal; rewrite Ex8; unfold Sh; lia).
    destruct (XR3 x Hx) as (_ & Hout & _ & (v & Hv & Hv0)). rewrite Ez in Hout, Hv. split; [|exact Hout].
    rewrite Hv. f_equal. assert (Hv00 : bv_unsigned v = 0) by (destruct Hv0 as [Hv0|[Hv0 _]]; [exact Hv0 | rewrite Hv0, PS8; reflexivity]).
    rewrite <- (Z_to_bv_bv_unsigned 8 v). rewrite Hv00. reflexivity. }

  pose proof (swf_objs _ Hswf) as HOWF. rewrite Ho, forallb_app in HOWF. apply andb_prop in HOWF as [HOWF _].
  assert (Hwf1 : swf (mkSS (ss_pc (ax_S A2)) (ss_regs (ax_S A2)) (ss_fregs (ax_S A2)) (ss_fcsr (ax_S A2)) (ss_resv (ax_S A2))
                          (ss_objs (ax_S A2) ++ [mkObj (SVar n) (SLit (SHADOW_OFF + 0)) (SLit (SHADOW_OFF + sz / 8)) [] DZero])
                          (ss_facts (ax_S A2)) (Pos.succ n) (ss_lenient (ax_S A2))) = true).
  { subst A2. cbn [ax_S ax_setX ax_setS set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_lenient].
    unfold frame_open_stateA in Hwf. cbn [ax_S] in Hwf. fold n in Hwf. eapply swf_facts_suffix. exact Hwf. }
  pose proof (SPA_carve_zero segs (JAi (NDA tv fr bd am) Ai kc) rho' A2 tp tr ms md (SVar n) (SHADOW_OFF + 0) (SHADOW_OFF + sz / 8) (Pos.succ n) SP3 Hwf1) as SP4.
  cbn [eval] in SP4. rewrite Un in SP4.
  assert (HXA2 : ax_X A2 = X1 ++ X2) by reflexivity. assert (HBA2 : ax_base A2 = SLit SHADOW_OFF) by (subst A2; cbn [ax_base ax_setX ax_setS]; exact Hbase).
  assert (HOA2 : ss_objs (ax_S A2) = objs) by reflexivity.
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END in F4; lia).
  assert (Hn2 : (ss_next (ax_S A2) <= Pos.succ n)%positive) by (subst A2; cbn [ax_S ax_setX ax_setS set_objs ss_next]; lia).
  specialize (SP4 Hn2 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
                  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
  assert (DISJ : Forall (fun o' => ranges_disjoint (obj_range rho' o') (p / 8 + (SHADOW_OFF + 0), p / 8 + (SHADOW_OFF + sz / 8))) (ss_objs (ax_S A2))).
  { rewrite HOA2. apply Forall_forall. intros o Ho'.
    rewrite (obj_range_agree_vals n rho rho' o (agree_below_vals _ _ _ AG) (proj1 (forallb_forall _ _) HOWF o Ho')).
    destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
    destruct (ZERO a ltac:(unfold Sh; lia)) as [_ Hout]. rewrite Ho in Hout. apply Forall_app in Hout as [Hout _].
    pose proof (proj1 (Forall_forall _ _) Hout o Ho') as Hc. cbn beta in Hc. rewrite Eo in Hc. cbn [fst snd] in Hc.
    rewrite u64_lit in Hc by (unfold Sh, SHADOW_OFF, HIGH_SHADOW_END in *; lia). exact (Hc Ha1). }
  specialize (SP4 DISJ ltac:(intros a Ha; rewrite Hrm; apply (proj1 (ZERO a ltac:(unfold Sh; lia))))).
  assert (XCL : forall rr y j, In rr (ax_X A2) ->
            bv_unsigned (eval rho' (fst rr)) <= y < bv_unsigned (eval rho' (fst rr)) + bv_unsigned (eval rho' (snd rr)) -> 0 <= j < 8 ->
            ~ (p / 8 + (SHADOW_OFF + 0) <= (bv_unsigned (eval rho' (ax_base A2)) + y / 8) / 8 * 8 + j < p / 8 + (SHADOW_OFF + sz / 8))).
  { intros rr y j Hr Hy Hj Hin. rewrite HBA2 in Hin. cbn [eval] in Hin. rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
    rewrite HXA2 in Hr.
    assert (HrA : In rr (ax_X A)) by (rewrite HX; apply in_app_or in Hr as [Hr|Hr]; apply in_or_app; [left; exact Hr | right; right; exact Hr]).
    unfold axwf in HwfA. apply andb_prop in HwfA as [HXb _]. pose proof (proj1 (forallb_forall _ _) HXb rr HrA) as Yb.
    unfold xr_below in Yb. apply andb_prop in Yb as [Yb1 Yb2]. fold n in Yb1, Yb2.
    rewrite <- (eval_agree n rho rho' _ AG Yb1), <- (eval_agree n rho rho' _ AG Yb2) in Hy.
    pose proof (word_in_aligned_range (SHADOW_OFF + y / 8) (Sh p) (sz / 8) j SP8 SS8 Hj ltac:(unfold Sh in *; lia)) as W.
    replace (SHADOW_OFF + y / 8) with (Sh y) in W by (unfold Sh; lia). apply (proj1 (Sh_range_iff p sz y P8 S8)) in W.
    exact (own_frame_sep Ai rho tp md tv fr i fe y HM HT HB HFF HN HFR Hnth (HXL rr y Hr Hy) W). }
  specialize (SP4 XCL).

  set (S' := mkSS (ss_pc (ax_S A2)) (ss_regs (ax_S A2)) (ss_fregs (ax_S A2)) (ss_fcsr (ax_S A2)) (ss_resv (ax_S A2))
                   (ss_objs (ax_S A2) ++ [mkObj (SVar n) (SLit (SHADOW_OFF + 0)) (SLit (SHADOW_OFF + sz / 8)) [] DZero])
                   (ss_facts (ax_S A2)) (Pos.succ n) (ss_lenient (ax_S A2))) in *.
  assert (FB' : forallb (sprop_below (ss_next (ax_S (ax_setS A2 S')))) (frame_factsA n pR sz ++ ss_facts (ax_S A)) = true).
  { cbn [ax_S ax_setS]. subst S'. cbn [ss_next]. unfold frame_open_stateA in Hwf. cbn [ax_S] in Hwf. fold n in Hwf.
    pose proof (swf_facts _ Hwf) as WFF. cbn [ss_facts ss_next] in WFF. exact WFF. }
  assert (Ug8 : bv_unsigned (eval rho' (g8 n)) = p).
  { unfold g8. rewrite U_sll_lit. cbn [eval]. rewrite Un. change (2 ^ (3 mod 64)) with 8. rewrite <- M64v_eq.
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. rewrite P8, Z.add_0_r in Dp. rewrite Z.mul_comm, <- Dp. apply Z.mod_small. unfold HIGH_SHADOW_END in *. lia. }
  assert (EpR : bv_unsigned (eval rho' (SVar pR)) = p) by exact UpR.
  assert (FH : Forall (holds rho') (ss_facts (ax_S (ax_setS A2 S'))) -> Forall (holds rho') (frame_factsA n pR sz ++ ss_facts (ax_S A))).
  { intros HF'. apply Forall_app. split; [| cbn [ax_S ax_setS] in HF'; subst S'; cbn [ss_facts] in HF'; exact HF'].
    unfold frame_factsA, FE. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [holds].
    - apply bv_eq. rewrite Ug8, EpR. reflexivity.
    - cbn [eval]. rewrite Un, u64_lit by lia. unfold HIGH_SHADOW_END in *. lia.
    - rewrite Ug8, EpR. lia.
    - rewrite Ug8, EpR. lia.
    - rewrite EpR. cbn [eval]. unfold aceil. rewrite u64_lit by lia. lia.
    - rewrite EpR. cbn [eval]. rewrite u64_lit by lia. lia.
    - pose proof EpR as EpR'. cbn [eval] in EpR' |- *. rewrite add_val, EpR'. rewrite u64_lit by lia.
      rewrite <- (proj1 AG V_TOP ltac:(unfold NP_okA in HNP; lia)).
      pose proof (proj1 (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT)) as ET. unfold Contract.V_TOP in ET. unfold Iface.V_TOP. rewrite ET.
      rewrite (TPA_top rho0 Ai HT). rewrite Z.mod_small by lia. lia. }
  pose proof (SPA_refacts segs _ rho' (ax_setS A2 S') (frame_factsA n pR sz ++ ss_facts (ax_S A)) tp _ SP4 FB' FH) as SP5.

  assert (EQS : ax_with_facts (ax_setS A2 S') (frame_factsA n pR sz ++ ss_facts (ax_S A)) = frame_open_stateA A objs (X1 ++ X2) pR sz).
  { subst S' A2. destruct A as [S X b]. destruct S. reflexivity. }
  rewrite EQS in SP5. destruct SP5 as [Hsm5 HJ5]. split; [exact Hsm5|]. exists Ai, kc. exact HJ5.
Qed.

Fixpoint shbyte (cells : list cell) (d : odefault) (off : Z) : option Z :=
  match cells with
  | [] => match d with DZero => Some 0 | _ => None end
  | mkCell (SLit o) w (SLit v) :: rest =>
      if negb ((- 2 ^ 62 <=? o) && (o <? 2 ^ 62)) then None
      else if (o <=? off) && (off <? o + w)
      then (if (w <=? 8) && (0 <=? v) && (v <? 2 ^ 64) then Some ((Z.shiftr v (8 * (off - o))) mod 256) else None)
      else shbyte rest d off
  | _ :: _ => None
  end.

Lemma shbyte_cases : forall cells d off b, shbyte cells d off = Some b ->
  (exists o w v, In (mkCell (SLit o) w (SLit v)) cells /\ o <= off < o + w /\ w <= 8 /\ - 2 ^ 62 <= o < 2 ^ 62 /\ 0 <= v < 2 ^ 64
                 /\ b = (Z.shiftr v (8 * (off - o))) mod 256)
  \/ (d = DZero /\ b = 0 /\ forall c, In c cells -> exists o w v, c = mkCell (SLit o) w (SLit v) /\ - 2 ^ 62 <= o < 2 ^ 62 /\ ~ (o <= off < o + w)).
Proof using .
  induction cells as [|c rest IH]; intros d off b H; cbn [shbyte] in H.
  - right. destruct d; try discriminate. injection H as <-. split; [reflexivity|]. split; [reflexivity|]. intros c0 [].
  - destruct c as [co cw cv]. destruct co as [o| | | | | | |]; try discriminate. destruct cv as [v| | | | | | |]; try discriminate.
    destruct ((- 2 ^ 62 <=? o) && (o <? 2 ^ 62)) eqn:E0; cbn [negb] in H; [|discriminate].
    destruct ((o <=? off) && (off <? o + cw)) eqn:E1.
    + destruct ((cw <=? 8) && (0 <=? v) && (v <? 2 ^ 64)) eqn:E2; [|discriminate]. injection H as <-.
      left. exists o, cw, v. split; [left; reflexivity|]. lia.
    + destruct (IH d off b H) as [(o' & w' & v' & Hin & R)|(Hd & Hb & Hall)].
      * left. exists o', w', v'. split; [right; exact Hin | exact R].
      * right. split; [exact Hd|]. split; [exact Hb|]. intros c0 [<-|Hc0]; [|exact (Hall c0 Hc0)].
        exists o, cw, v. split; [reflexivity | lia].
Qed.

Lemma Z_to_bv8_mod64 : forall x, Z_to_bv 8 (x mod 2 ^ 64) = Z_to_bv 8 (x mod 256).
Proof using .
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 56). reflexivity.
Qed.

Lemma shbyte_sound : forall rho ms o off b,
  rom_ok segs ms -> obj_holds segs rho ms o ->
  shbyte (ob_cells o) (ob_dflt o) off = Some b ->
  obj_lo_of rho o <= off < obj_hi_of rho o ->
  let a := bv_unsigned (eval rho (ob_base o)) + off in
  IMG_HI <= a < 2 ^ 64 ->
  ms_mem ms (Z_to_bv 64 a) = Some (Z_to_bv 8 b).
Proof using HTOP.
  intros rho ms o off b Hrom Ho Hsh Hoff a Ha.
  assert (RD : forall x, rd ms (Z_to_bv 64 a) = Some x -> ms_mem ms (Z_to_bv 64 a) = Some x).
  { intros x Hx. rewrite <- Hx. symmetry. apply (rd_high segs HTOP); [exact Hrom|]. unfold IMG_HI in *. rewrite (u64_lit a) by lia. lia. }
  apply RD.
  destruct (shbyte_cases _ _ _ _ Hsh) as [(co & w & v & Hin & Hcov & Hw & Hob & Hv & ->)|(Hd & -> & Hall)].
  - pose proof (obj_read_cell segs rho ms o _ off 1 Ho Hin ltac:(cbn; lia)) as R. cbn [SymState.c_off SymState.c_width SymState.c_val] in R.
    rewrite soff_lit_small in R by lia. specialize (R ltac:(lia) ltac:(lia) ltac:(lia)). cbn [eval] in R. rewrite (u64_lit v) in R by lia.
    change (Z.to_nat 1) with 1%nat in R. unfold enc_bytes in R. cbn [Z_to_le_bytes] in R.
    rewrite Z_to_bv_unsigned in R. unfold bv_wrap in R. change (bv_modulus 64) with (2 ^ 64) in R. rewrite Z_to_bv8_mod64 in R.
    cbn [rd_bytes] in R. unfold oaddr in R. fold a in R.
    destruct (rd ms (Z_to_bv 64 a)) as [b8|]; [|discriminate]. injection R as ->. reflexivity.
  - pose proof Ho as (Hb & Hw & Hcells & Hdf & Hdl).
    assert (NC : ~ covered rho (ob_cells o) off).
    { intros HC. unfold covered in HC. apply Exists_exists in HC as (c & Hc & HIc). destruct (Hall c Hc) as (co & w & v & -> & Hob & Hn).
      unfold in_cell in HIc. cbn [SymState.c_off SymState.c_width] in HIc. rewrite soff_lit_small in HIc by lia. exact (Hn HIc). }
    specialize (Hdf off Hoff NC). rewrite Hd in Hdf. cbn [dflt_holds] in Hdf. exact Hdf.
Qed.

Lemma own_frame_sepF : forall Ai rho tp md (tv : list (sv * sv)) fr i fe y,
  AInv Ai rho tp md -> TPA rho0 Ai -> fbinA FB Ai -> ffinA FF Ai -> frinA FF Ai rho fr ->
  nth_error fr i = Some fe ->
  pclFA CST rho0 FB FF y \/ in_rangesZ XGL y ->
  ~ (fst (frv rho fe) <= y < fst (frv rho fe) + snd (frv rho fe)).
Proof using ALA HCST HXGL.
  intros Ai rho tp md tv fr i fe y HM HT HB HFF HFR Hnth Hy Hin.
  pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & _).
  pose proof HFR as (HFR0 & HCEN & HND).
  destruct Hy as [[Hs|[Hc|[(b & n & Hbn & Hr)|(f & s & fl & Hf & Hr)]]]|Hx].
  - lia.
  - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  - destruct (block_frame_sep Ai rho tp md b n _ _ HM (HB _ Hbn) E1); lia.
  - pose proof (proj1 (Forall_forall _ _) HFR0 fe Hfe) as (_ & _ & X3). pose proof (X3 _ Hf) as NE. cbn [fst] in NE.
    destruct (HFF _ _ _ Hf) as [Hf1 Hfl]. destruct Hr as [Hr| ->].
    + destruct (frames_sep Ai rho tp md f s _ _ HM Hf1 E1 ltac:(intros EE; injection EE; intros; apply NE; congruence)); lia.
    + destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (_ & _ & HFr).
      destruct (HFr f s Hf1) as (_ & _ & _ & _ & _ & _ & _ & _ & G9). rewrite <- Hfl in G9.
      destruct (G9 _ _ E1); lia.
  - apply HXGL in Hx. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Lemma Sh_last : forall p sz, p mod 8 = 0 -> sz mod 8 = 0 -> 8 <= sz -> Sh (p + sz - 1) = Sh p + sz / 8 - 1.
Proof.
  intros p sz Hp Hs H8. unfold Sh.
  pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)).
  replace (p + sz - 1) with ((p / 8 + sz / 8 - 1) * 8 + 7) by lia.
  rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
Qed.

Lemma JAi_shadow_write : forall nd Ai kc rho rho' tp tr md i fe lo hi,
  JAi nd Ai kc rho tp tr md ->
  nth_error (nd_fr nd) i = Some fe ->
  let p := fst (frv rho fe) in let sz := snd (frv rho fe) in
  Sh p <= lo -> hi <= Sh p + sz / 8 ->
  (forall v, rw rho' v = rw rho v) -> (forall l, rl rho' l = rl rho l) ->
  (forall a, ~ (lo <= bv_unsigned a < hi) -> rm rho' a = rm rho a) ->
  (forall a, lo <= bv_unsigned a < hi -> rm rho' a <> None) ->
  JAi nd Ai kc rho' tp tr md.
Proof using ALA HCST HXGL HKc HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros nd Ai kc rho rho' tp tr md i fe lo hi HJ Hnth p sz Hlo Hhi HRW HRL OUT PRES.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts Ai rho tp md (nd_fr nd) fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  fold p sz in E1, E2, F1, F2, F3, F4, F5, F9. unfold aceil in F5.
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 F3; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (EV : forall e, eval rho' e = eval rho e).
  { intros e. symmetry. apply (eval_agree_vars (fun _ => true)); [intros v _; symmetry; apply HRW | intros l; symmetry; apply HRL | apply sv_vars_all_true]. }

  assert (RNG : forall z, lo <= z < hi -> Sh p <= z < Sh p + sz / 8) by (intros z Hz; lia).
  assert (SHAD : forall z, lo <= z < hi -> is_shadowZ z).
  { intros z Hz. pose proof (Sh_is_shadow p ltac:(unfold HIGH_SHADOW_END in F4; lia)) as S1.
    pose proof (Sh_is_shadow (p + sz - 1) ltac:(unfold HIGH_SHADOW_END in F4; lia)) as S2. rewrite Sh_last in S2 by lia.
    unfold is_shadowZ in *. lia. }
  assert (OUTapp : forall a, ~ is_shadowZ (bv_unsigned a) -> rm rho' a = rm rho a).
  { intros a Ha. apply OUT. intros Hr. exact (Ha (SHAD _ Hr)). }
  split; [destruct Hav as [A1 A2]; split; [intros v Hv; rewrite HRW; exact (A1 v Hv) | intros l; rewrite HRL; exact (A2 l)]|].
  split; [exact Hk|].
  split.
  {
    eapply (law_frame _ _ _ ALA); [exact HM| |].
    - intros a _ Hns. apply OUT. intros Hr. apply Hns. exists p, sz. split; [exact E1|]. rewrite Sh_last by lia. lia.
    - intros a _ Hd. destruct (Z_le_dec lo (bv_unsigned a)), (Z_lt_dec (bv_unsigned a) hi); try (rewrite OUT by lia; exact Hd). apply PRES. lia. }
  split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split.
  { split; [|split]; [eapply tvinA_map; [| | exact HN] | eapply tvd_map; [| | exact HD] | eapply tvz_map; [| | exact HZ]];
      try (apply map_ext; intros t; unfold tvv; rewrite !EV; reflexivity);
      intros k t t' Ht Ht'; rewrite Ht in Ht'; injection Ht' as <-; unfold tnz; rewrite EV; tauto. }
  split.
  { destruct HFR as [HFR0 HCEN]. split.
    + unfold frinA0 in HFR0 |- *. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HFR0 x Hx) as Y.
      unfold frv, uval in Y |- *. rewrite !EV. exact Y.
    + eapply frinA_rest_map; [reflexivity | | exact HCEN]. apply map_ext. intros x. unfold frv, uval. rewrite !EV. reflexivity. }
  split.
  {
    destruct HK0 as [K1 K2]. split.
    + intros a Ha Hp. rewrite OUT; [exact (K1 a Ha Hp)|]. rewrite u64_of_sum by exact Ha. intros Hr.
      destruct Hp as [Hp|[(x & Hx & Hpx & ->) _]].
      *
        exact (client_not_shadow segs AInv CST ALA HCST Ai a rho tp md HM (pclFA_client CST rho0 FB FF Ai a HB HFF HT Hp) (SHAD a Hr)).
      * assert (W : p <= x < p + sz) by (apply (proj1 (Sh_range_iff p sz x P8 S8)); apply RNG; exact Hr).
        exact (own_frame_sepF Ai rho tp md (nd_tv nd) (nd_fr nd) i fe x HM HT HB HFF HFR Hnth Hpx W).
    + intros a j Ha Hp Hj Hd. destruct (Z_le_dec lo (bv_unsigned (word_byte a j))), (Z_lt_dec (bv_unsigned (word_byte a j)) hi);
        try (rewrite OUT by lia; exact (K2 a j Ha Hp Hj Hd)). apply PRES. lia. }
  split; [exact HP0|].

  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  assert (XT : XAz FB (am_eval rho (nd_am nd)) Ai (rm rho') (tvals rho (nd_tv nd)) kc
               /\ apotz (am_eval rho (nd_am nd)) (rm rho') = apotz (am_eval rho (nd_am nd)) (rm rho)).
  { eapply (XAz_transport FB FB _ Ai Ai (rm rho) (rm rho')); [exact HXA | intros; auto | | | intros bn H1 _ H3 H4; auto].
    - intros b n z Hin _ _ Hz. destruct (HBl b n Hin) as (G1 & G2 & G3 & G4 & G5). unfold HIGH_SHADOW_END in G5.
      apply OUTapp. rewrite u64_of_sum by lia. unfold is_shadowZ, HIGH_SHADOW_END. lia.
    - intros b n a Hin _ _ Ha. destruct (HBl b n Hin) as (G1 & G2 & G3 & G4 & G5). unfold HIGH_SHADOW_END in G5.
      split.
      + intros _. rewrite shadow_addr_Sh. apply OUT. rewrite u64_of_sum by (unfold Sh, SHADOW_OFF, HIGH_SHADOW_END in *; lia). intros Hr.
        assert (W : p <= a < p + sz) by (apply (proj1 (Sh_range_iff p sz a P8 S8)); apply RNG; exact Hr).
        destruct (block_frame_sep Ai rho tp md b n p sz HM Hin E1); lia.
      + intros j Hj Hd. destruct (Z_le_dec lo (bv_unsigned (word_byte (SHADOW_OFF + a / 8) j))), (Z_lt_dec (bv_unsigned (word_byte (SHADOW_OFF + a / 8) j)) hi);
          try (rewrite OUT by lia; exact Hd). apply PRES. lia. }
  destruct XT as [XT1 XT2].
  refine (conj _ (conj _ (conj HPA (conj HCKi (capN_ext _ _ rho rho' _ EV HCNi))))).
  { unfold XA. rewrite (am_eval_exteq (nd_am nd) rho rho' ltac:(intros e _; apply EV)).
    unfold tvals. rewrite (map_ext (tvv rho') (tvv rho)) by (intros t; unfold tvv; rewrite !EV; reflexivity). exact XT1. }
  { unfold apot. rewrite (am_eval_exteq (nd_am nd) rho rho' ltac:(intros e _; apply EV)). rewrite XT2. fold (apot (nd_am nd) rho).
    destruct (bsum_eval_ext (nd_bd nd) rho' rho EV) as [B1 B2]. unfold BUD in HBU |- *. rewrite B1, B2.
    destruct HBU as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). repeat (split; [assumption|]). split; [|split; assumption].
    eapply bd_nn_eval_ext; [| exact Q7]. intros e. symmetry. apply EV. }
Qed.

Fixpoint zrange (a : Z) (n : nat) : list Z := match n with O => [] | S k => a :: zrange (a + 1) k end.
Lemma In_zrange : forall n a q, In q (zrange a n) <-> a <= q < a + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros a q; cbn [zrange].
  - split; [intros [] | lia].
  - rewrite Nat2Z.inj_succ. split.
    + intros [<-|H]; [lia|]. apply IH in H. lia.
    + intros H. destruct (Z.eq_dec a q) as [->|Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.

Definition granules (off len : Z) : list Z := zrange (off / 8) (Z.to_nat ((off + len + 7) / 8 - off / 8)).
Lemma In_granules : forall off len q, 0 <= off -> 1 <= len -> off / 8 <= q < (off + len + 7) / 8 -> In q (granules off len).
Proof.
  intros off len q Ho Hl Hq. unfold granules. apply In_zrange. rewrite Z2Nat.id; [lia|].
  pose proof (Z.div_le_mono off (off + len + 7) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Definition expected_sh (off len q : Z) : Z := if q <? (off + len) / 8 then 0 else (off + len) mod 8.
Definition local_ok (cells : list cell) (d : odefault) (k1 k2 : Z) (ol : Z * Z) : bool :=
  let (off, len) := ol in
  (0 <=? off) && (off mod 8 =? 0) && (1 <=? len) && (k1 <=? off / 8) && ((off + len + 7) / 8 <=? k2) &&
  forallb (fun q => match shbyte cells d (SHADOW_OFF + q) with Some b => b =? expected_sh off len q | None => false end) (granules off len).

Definition xlocal (pR : positive) (ol : Z * Z) : sv * sv := (SAlu ALU_ADD (SVar pR) (SLit (fst ol)), SLit (snd ol)).
Definition shadow_release_stateA (A : axst) (objs : list sobj) (pR : positive) (L : list (Z * Z)) : axst :=
  mkAX (set_objs (ax_S A) objs) (map (xlocal pR) L ++ ax_X A) (ax_base A).

Lemma JA_shadow_release : forall tv fr bd am i pR c pF g k1 k2 cells d (A : axst) objs L rho tp tr ms md,
  let sz := fs_frame_size c in let sh := shobj g k1 k2 cells d in
  nth_error fr i = Some (SVar pR, c, SVar pF) -> 0 <= c <= 6 ->
  ax_base A = SLit SHADOW_OFF ->
  ss_objs (ax_S A) = objs ++ [sh] -> 0 <= k1 -> k1 <= k2 <= sz / 8 -> dflt_writable d = true ->
  has_facts [SPEq (g8 g) (SVar pR); SPUle (SVar g) (SLit (2 ^ 61 - 1))] (ss_facts (ax_S A)) = true ->
  forallb (local_ok cells d k1 k2) L = true ->
  nd_below (ss_next (ax_S A)) (NDA tv fr bd am) = true ->
  (forall Ai rho1 tp1 md1, Forall (holds rho) (ss_facts (ax_S A)) -> P0f rho0 -> agree_vals NP rho0 rho -> AInv Ai rho1 tp1 md1 -> TPA rho0 Ai -> T_ok rho (topG (aa_geom Ai)) ->
      fbinA FB Ai -> ffinA FF Ai -> tvinA FB Ai rho tv -> tvd rho tv -> tvz rho tv -> frinA FF Ai rho fr ->
      TobjJAR.robjs_okF CST rho0 FB FF rho tv fr objs) ->
  SPA segs (JA (NDA tv fr bd am)) A rho tp (tr, mkCfg ms md) ->
  SPA segs (JA (NDA tv fr bd am)) (shadow_release_stateA A objs pR L) (rho_absorb rho [sh] (vms md tp ms)) tp (tr, mkCfg ms md).
Proof using ALA HCST HXGL HBX HKc HTOP LFSH HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF g k1 k2 cells d A objs L rho tp tr ms md sz sh Hnth Hc6 Hbase Ho Hk1 Hk2 Hdw Hfe2 HL Hnb HSITE [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  pose proof (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT) HB HFF HN HD HZ HFR) as HROK.
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9. fold sz in E1, E2, F2, F3, F5.
  set (p := uval rho (SVar pR)) in *.
  unfold aceil in F5, F7. pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (SP8 : Sh p mod 8 = 0).
  { unfold Sh, SHADOW_OFF. clear -F1 F4. pose proof (Z.div_mod p 64 ltac:(lia)). pose proof (Z.div_mod (p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p / 8) 8 ltac:(lia)).
    rewrite Z.add_mod by lia. replace (2147450880 mod 8) with 0 by reflexivity. rewrite Z.add_0_r, Z.mod_mod by lia. nia. }
  assert (SS8 : (sz / 8) mod 8 = 0).
  { clear -F2 Hszb. pose proof (Z.div_mod sz 64 ltac:(lia)). pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz / 8) 8 ltac:(lia)). nia. }
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END in F4; lia).

  pose proof (has_facts_sound rho _ _ HF Hfe2) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia. change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  pose proof Hsm as (HsmS & HMI & HwfA & Hsh & Hhz).
  pose proof HsmS as (Hswf & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & (Hall & Hpd & Hfr) & _).
  cbn [virt fst snd cfg_ms cfg_model] in Hall, Hrom.
  assert (Hrng : obj_range rho sh = (Sh p + k1, Sh p + k2)).
  { unfold obj_range, obj_lo_of, obj_hi_of, sh, shobj. cbn [ob_base ob_lo ob_hi eval]. rewrite Ug. unfold Sh, SHADOW_OFF in *. rewrite !soff_lit_small by lia. f_equal; lia. }
  set (rho' := rho_absorb rho [sh] (vms md tp ms)).
  assert (OUT : forall a, ~ (Sh p + k1 <= bv_unsigned a < Sh p + k2) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply GlueM.rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr. exact (Ha Hr). }
  assert (INa : forall a, Sh p + k1 <= bv_unsigned a < Sh p + k2 -> rm rho' a = ms_mem (vms md tp ms) a).
  { intros a Ha. unfold rho'. apply GlueM.rm_absorb_in. exists sh. split; [left; reflexivity|]. rewrite Hrng. exact Ha. }
  destruct (released_bytesA segs HTOP rho A objs [sh] sh tp tr ms md Ho ltac:(left; reflexivity) Hsm Hdw
              ltac:(rewrite Hrng; cbn [fst]; unfold Sh, SHADOW_OFF, IMG_HI in *; lia) ltac:(rewrite Hrng; cbn [snd]; unfold Sh, SHADOW_OFF in *; lia)) as [BY _].
  rewrite Hrng in BY. cbn [fst snd] in BY. fold rho' in BY.

  assert (SP1 : SPA segs (JAi (NDA tv fr bd am) Ai kc) (ax_setS A (set_objs (ax_S A) objs)) rho' tp (tr, mkCfg ms md)).
  { apply (SPA_unobj segs (JAi (NDA tv fr bd am) Ai kc) rho A objs [sh] tp tr ms md Ho (conj Hsm HJ)).
    intros HJ'. apply (JAi_shadow_write (NDA tv fr bd am) Ai kc rho rho' tp tr md i fe (Sh p + k1) (Sh p + k2) HJ' Hnth);
      cbn [nd_fr frv fst snd fe]; fold (uval rho (SVar pR)); fold p; fold sz; try lia; try (intros; reflexivity).
    - exact OUT.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply BY. exact Ha. }

  assert (EVr : forall e, eval rho' e = eval rho e) by (intros e; unfold rho'; apply eval_absorb).
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  assert (NOSH : forall o a, In o objs -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> ~ is_shadowZ a).
  { intros o a Hoin Hr Hs. destruct (HROK o a Hoin Hr) as [Hc|Hi].
    - exact (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None a rho tp md HM (pclMA_cmaddrA CST rho0 _ _ Ai a FBX FFX HT Hc) Hs).
    - unfold is_shadowZ, SHADOW_OFF, IMG_HI in *. lia. }
  pose proof (swf_objs _ Hswf) as HOWF. rewrite Ho, forallb_app in HOWF. apply andb_prop in HOWF as [HOWF _].
  assert (OUTS : forall z, is_shadowZ z -> 0 <= z < 2 ^ 64 -> outside_all rho' objs (Z_to_bv 64 z)).
  { intros z Hz Hz64. unfold outside_all. apply Forall_forall. intros o Hoin. cbn beta.
    rewrite (obj_range_agree_vals (ss_next (ax_S A)) rho rho' o ltac:(split; intros; reflexivity) (proj1 (forallb_forall _ _) HOWF o Hoin)).
    rewrite u64_lit by lia. intros Hr. exact (NOSH o z Hoin Hr Hz). }
  assert (FSH : forall z, Sh p <= z < Sh p + sz / 8 -> rm rho' (Z_to_bv 64 z) <> None).
  { intros z Hz. destruct (Z_le_dec (Sh p + k1) z), (Z_lt_dec z (Sh p + k2)); try (apply BY; lia);
      rewrite OUT by (rewrite u64_lit by (unfold Sh, SHADOW_OFF in *; lia); lia);
      apply (LFSH Ai rho tp md p sz z HM E1); rewrite Sh_val in *; unfold Sh; pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia. }
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am] in Hbf.
  pose proof (proj1 (forallb_forall _ _) Hbf fe Hfe) as Hfeb. cbn [fe fst snd sv_below] in Hfeb. apply andb_prop in Hfeb as [HpRn _]. apply Pos.ltb_lt in HpRn.
  assert (UpR : bv_unsigned (rw rho pR) = p) by reflexivity.
  assert (PUB : forall L', forallb (local_ok cells d k1 k2) L' = true -> forall X0,
            SPA segs (JAi (NDA tv fr bd am) Ai kc) (mkAX (set_objs (ax_S A) objs) X0 (ax_base A)) rho' tp (tr, mkCfg ms md) ->
            SPA segs (JAi (NDA tv fr bd am) Ai kc) (mkAX (set_objs (ax_S A) objs) (map (xlocal pR) L' ++ X0) (ax_base A)) rho' tp (tr, mkCfg ms md)).
  { induction L' as [|[off len] L' IH]; intros HL' X0 SP; [exact SP|].
    cbn [forallb] in HL'. apply andb_prop in HL' as [Hl HL']. specialize (IH HL' X0 SP). cbn [map app].
    apply (SPA_x_publish segs _ rho' (mkAX (set_objs (ax_S A) objs) (map (xlocal pR) L' ++ X0) (ax_base A)) (xlocal pR (off, len)) tp _); [| | exact IH].
    - unfold xr_below, xlocal. cbn [fst snd ax_S set_objs ss_next sv_below]. rewrite !andb_true_r. apply Pos.ltb_lt. exact HpRn.
    - unfold local_ok in Hl. apply andb_prop in Hl as [Hl HQ]. apply andb_prop in Hl as [Hl Hl5]. apply andb_prop in Hl as [Hl Hl4].
      apply andb_prop in Hl as [Hl Hl3]. apply andb_prop in Hl as [Hl1 Hl2].
      apply Z.leb_le in Hl1. apply Z.eqb_eq in Hl2. apply Z.leb_le in Hl3. apply Z.leb_le in Hl4. apply Z.leb_le in Hl5.
      assert (Hlen : off + len <= sz).
      { pose proof (Z.div_mod (off + len + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (off + len + 7) 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)). nia. }
      cbn [ax_base ax_S set_objs ss_objs]. rewrite Hbase. cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
      unfold xr_ok, xlocal. cbn [fst snd]. rewrite !EVr. rewrite U_add. cbn [eval]. rewrite UpR, !u64_lit by lia. rewrite <- M64v_eq, (Z.mod_small (p + off) (2 ^ 64)) by lia.
      split; [rewrite Z.add_mod, P8, Hl2 by lia; reflexivity|]. split; [lia|].
      intros a Ha. set (q := (a - p) / 8).
      pose proof (Z.div_mod (a - p) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (a - p) 8 ltac:(lia)) as Mq. pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
      assert (Ha8 : a / 8 = p / 8 + q) by (subst q; rewrite P8 in Dp; clear - Dq Mq Dp; nia).
      assert (Hq : off / 8 <= q < (off + len + 7) / 8).
      { subst q. split; [apply Z.div_le_mono; clear - Ha; lia|]. apply Z.div_lt_upper_bound; [clear - Ha; lia|]. pose proof (Z.mul_div_le (off + len + 7) 8 ltac:(lia)) as MDL.
        pose proof (Z.div_mod (off + len + 7) 8 ltac:(lia)) as DL8. pose proof (Z.mod_pos_bound (off + len + 7) 8 ltac:(lia)) as ML8. first [clear - Ha MDL DL8 ML8; lia | nia]. }
      assert (HSa : is_shadowZ (Sh a)) by (apply Sh_is_shadow; lia).
      assert (Hza : Sh p <= Sh a < Sh p + sz / 8) by (apply (proj2 (Sh_range_iff p sz a P8 S8)); lia).
      pose proof HSa as SS. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS.
      split; [unfold Sh, SHADOW_OFF in Hza, SS |- *; lia|].
      split; [rewrite shadow_addr_Sh; apply OUTS; [exact HSa | lia]|].
      split.
      + intros j Hj. pose proof (word_byte_of_shadow (Sh a) j HSa Hj) as WS.
        destruct (word_byte_range (Sh a) j ltac:(lia) Hj) as (W1 & W2 & W3).
        replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
        split; [rewrite <- (Z_to_bv_bv_unsigned 64 (word_byte (Sh a) j)), W2; apply OUTS; [rewrite <- W2; exact WS | lia]|].
        rewrite <- (Z_to_bv_bv_unsigned 64 (word_byte (Sh a) j)), W2. apply FSH.
        pose proof (word_in_aligned_range (Sh a) (Sh p) (sz / 8) j SP8 SS8 Hj) as WW.

        pose proof (Z.div_mod (Sh a) 8 ltac:(lia)) as DA8. pose proof (Z.mod_pos_bound (Sh a) 8 ltac:(lia)) as MA8.
        pose proof (Z.div_mod (Sh p) 8 ltac:(lia)) as DP8. pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)) as DS8.
        first [ clear - DA8 MA8 DP8 DS8 WW W1 W2 W3 Hza Hj SP8 SS8; lia | clear - DA8 MA8 DP8 DS8 WW W1 W2 W3 Hza Hj SP8 SS8; nia | nia ].
      +
        pose proof (proj1 (forallb_forall _ _) HQ q (In_granules off len q Hl1 Hl3 Hq)) as HQq. cbn beta in HQq.
        destruct (shbyte cells d (SHADOW_OFF + q)) as [b|] eqn:Hsb; [|discriminate]. apply Z.eqb_eq in HQq.
        rewrite Ho in Hall. apply Forall_app in Hall as [_ Hshh]. apply Forall_inv in Hshh.
        pose proof (shbyte_sound rho (vms md tp ms) sh (SHADOW_OFF + q) b Hrom Hshh Hsb) as SB.
        unfold obj_lo_of, obj_hi_of, sh, shobj in SB. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt eval] in SB. rewrite Ug in SB.
        unfold SHADOW_OFF in SB. rewrite !soff_lit_small in SB by lia.
        specialize (SB ltac:(lia) ltac:(unfold IMG_HI, Sh, SHADOW_OFF in *; lia)).
        replace (p / 8 + (2147450880 + q)) with (Sh a) in SB by (unfold Sh, SHADOW_OFF; lia).
        assert (HSq : Sh a = Sh p + q) by (unfold Sh; lia).
        exists (Z_to_bv 8 b). split; [rewrite shadow_addr_Sh, INa by (rewrite u64_lit by lia; lia); exact SB|].
        rewrite Z_to_bv_unsigned. unfold expected_sh in HQq.
        assert (Hb8 : 0 <= (off + len) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
        destruct (q <? (off + len) / 8) eqn:Eq; [apply Z.ltb_lt in Eq | apply Z.ltb_ge in Eq]; subst b.
        * left. reflexivity.
        * right. rewrite bv_wrap_small by (change (bv_modulus 8) with 256; lia).
          assert (Eqq : q = (off + len) / 8).
          { subst q. apply Z.le_antisymm; [|exact Eq]. apply Z.div_le_mono; [lia|]. lia. }
          split.
          -- replace (p + off + len) with ((off + len) + p) by lia. rewrite (Z.add_mod (off + len) p 8), P8, Z.add_0_r, Z.mod_mod by lia. reflexivity.
          -- rewrite Ha8, Eqq. rewrite P8, Z.add_0_r in Dp. rewrite Dp at 2. rewrite <- Z.add_assoc, Z.mul_comm, Z.div_add_l by lia. reflexivity. }
  specialize (PUB L HL (ax_X A)).
  assert (EQA : mkAX (set_objs (ax_S A) objs) (ax_X A) (ax_base A) = ax_setS A (set_objs (ax_S A) objs)) by reflexivity.
  rewrite EQA in PUB. specialize (PUB SP1). destruct PUB as [Hsm5 HJ5].
  split; [exact Hsm5|]. exists Ai, kc. exact HJ5.
Qed.

Definition wclear (k1 k2 off len : Z) : bool :=
  forallb (fun q => (q / 8 * 8 + 8 <=? k1) || (k2 <=? q / 8 * 8)) (granules off len).

Definition shadow_reopen_stateA (A : axst) (X' : list (sv * sv)) (g : positive) (k1 k2 : Z) : axst :=
  let S := ax_S A in
  mkAX (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [shobj g k1 k2 [] DUnknown])
             (ss_facts S) (ss_next S) (ss_lenient S)) X' (ax_base A).

Lemma JA_shadow_reopen : forall tv fr bd am i pR c pF g k1 k2 (A : axst) X' rho tp w,
  let sz := fs_frame_size c in
  nth_error fr i = Some (SVar pR, c, SVar pF) -> 0 <= c <= 6 ->
  ax_base A = SLit SHADOW_OFF ->
  0 <= k1 -> k1 <= k2 <= sz / 8 ->
  has_facts [SPEq (g8 g) (SVar pR); SPUle (SVar g) (SLit (2 ^ 61 - 1))] (ss_facts (ax_S A)) = true ->
  (forall r, In r X' -> In r (ax_X A)) ->
  swf (ax_S (shadow_reopen_stateA A X' g k1 k2)) = true ->
  (forall Ai rho1 tp1 md1, Forall (holds rho) (ss_facts (ax_S A)) -> P0f rho0 -> agree_vals NP rho0 rho -> AInv Ai rho1 tp1 md1 -> TPA rho0 Ai -> T_ok rho (topG (aa_geom Ai)) ->
      fbinA FB Ai -> ffinA FF Ai -> tvinA FB Ai rho tv -> tvd rho tv -> tvz rho tv -> frinA FF Ai rho fr ->
      TobjJAR.robjs_okF CST rho0 FB FF rho tv fr (ss_objs (ax_S A))
      /\ (forall r y, In r X' -> uval rho (fst r) <= y < uval rho (fst r) + uval rho (snd r) ->
            (pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (remove_nth i fr)) y \/ in_rangesZ XGL y)
            \/ (exists off len, r = xlocal pR (off, len) /\ 0 <= off /\ 1 <= len /\ off + len <= sz /\ wclear k1 k2 off len = true))) ->
  SPA segs (JA (NDA tv fr bd am)) A rho tp w ->
  SPA segs (JA (NDA tv fr bd am)) (shadow_reopen_stateA A X' g k1 k2) rho tp w.
Proof using ALA HCST HXGL HBX HKc HTOP LFSH HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF g k1 k2 A X' rho tp w sz Hnth Hc6 Hbase Hk1 Hk2 Hfe2 HX' Hwf HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT) HB HFF HN HD HZ HFR) as [HROK HXW].
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9. fold sz in E1, E2, F2, F3, F5.
  set (p := uval rho (SVar pR)) in *.
  unfold aceil in F5, F7. pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (SP8 : Sh p mod 8 = 0).
  { unfold Sh, SHADOW_OFF. clear -F1 F4. pose proof (Z.div_mod p 64 ltac:(lia)). pose proof (Z.div_mod (p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p / 8) 8 ltac:(lia)).
    rewrite Z.add_mod by lia. replace (2147450880 mod 8) with 0 by reflexivity. rewrite Z.add_0_r, Z.mod_mod by lia. nia. }
  assert (SS8 : (sz / 8) mod 8 = 0).
  { clear -F2 Hszb. pose proof (Z.div_mod sz 64 ltac:(lia)). pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz / 8) 8 ltac:(lia)). nia. }
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END in F4; lia).
  pose proof (has_facts_sound rho _ _ HF Hfe2) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia.
    change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  assert (NOSH : forall o a, In o (ss_objs (ax_S A)) -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> ~ is_shadowZ a).
  { intros o a Hoin Hr Hs. destruct (HROK o a Hoin Hr) as [Hc|Hi].
    - exact (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None a rho tp md HM (pclMA_cmaddrA CST rho0 _ _ Ai a FBX FFX HT Hc) Hs).
    - unfold is_shadowZ, SHADOW_OFF, IMG_HI in *. lia. }
  assert (SHAD : forall z, Sh p + k1 <= z < Sh p + k2 -> is_shadowZ z).
  { intros z Hz. pose proof (Sh_is_shadow p ltac:(lia)) as S1. pose proof (Sh_is_shadow (p + sz - 1) ltac:(lia)) as S2. rewrite Sh_last in S2 by lia.
    unfold is_shadowZ in *. lia. }

  pose proof (SPA_x_sub segs _ rho A X' tp _ HX' (conj Hsm HJ)) as SP1.
  set (A1 := ax_setX A X') in SP1.

  pose proof (SPA_carve_obj segs (JAi (NDA tv fr bd am) Ai kc) rho A1 tp (tr, mkCfg ms md) (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) [] (ss_next (ax_S A)) SP1) as SP2.
  cbn [eval] in SP2. rewrite Ug in SP2.
  assert (Hwf1 : swf (mkSS (ss_pc (ax_S A1)) (ss_regs (ax_S A1)) (ss_fregs (ax_S A1)) (ss_fcsr (ax_S A1)) (ss_resv (ax_S A1))
                          (ss_objs (ax_S A1) ++ [carved (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) []]) (ss_facts (ax_S A1)) (ss_next (ax_S A)) (ss_lenient (ax_S A1))) = true).
  { subst A1. cbn [ax_S ax_setX]. unfold shadow_reopen_stateA in Hwf. cbn [ax_S] in Hwf. exact Hwf. }
  specialize (SP2 Hwf1 ltac:(subst A1; cbn [ax_S ax_setX]; lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia)
                  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia) ltac:(constructor)).
  assert (DISJ : Forall (fun o' => ranges_disjoint (obj_range rho o') (p / 8 + (SHADOW_OFF + k1), p / 8 + (SHADOW_OFF + k2))) (ss_objs (ax_S A1))).
  { subst A1. cbn [ax_S ax_setX]. apply Forall_forall. intros o Ho'.
    destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
    apply (NOSH o a Ho'); [rewrite Eo; exact Ha1|]. apply SHAD. unfold Sh. lia. }
  specialize (SP2 DISJ).
  assert (VIEW : forall off, SHADOW_OFF + k1 <= off < SHADOW_OFF + k2 ->
             wok_of segs (rm rho) (Z_to_bv 64 (p / 8 + off)) = true /\ exists x, rd_of segs (rm rho) (Z_to_bv 64 (p / 8 + off)) = Some x).
  { intros off Hoff.
    assert (Hz : Sh p <= p / 8 + off < Sh (p + sz)).
    { unfold Sh in *. pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)). rewrite P8 in *. rewrite S8 in *.
      replace (p + sz) with ((p / 8 + sz / 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    pose proof (LFSH Ai rho tp md p sz (p / 8 + off) HM E1 Hz) as D.
    unfold wok_of, rd_of. destruct (rm rho (Z_to_bv 64 (p / 8 + off))) as [x|]; [split; [reflexivity | exists x; reflexivity] | exfalso; exact (D eq_refl)]. }
  specialize (SP2 VIEW ltac:(constructor)).
  assert (XCL : xwords_clear rho A1 (p / 8 + (SHADOW_OFF + k1)) (p / 8 + (SHADOW_OFF + k2))).
  { intros rr y j Hr Hy Hj Hin. subst A1. cbn [ax_X ax_base ax_setX] in Hr, Hin. rewrite Hbase in Hin. cbn [eval] in Hin.
    rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
    destruct (HXW rr y Hr Hy) as [Hout|(off & len & -> & Ho0 & Hl1 & Hol & Hwc)].
    -
      pose proof (word_in_aligned_range (SHADOW_OFF + y / 8) (Sh p) (sz / 8) j SP8 SS8 Hj ltac:(unfold Sh in *; lia)) as W.
      replace (SHADOW_OFF + y / 8) with (Sh y) in W by (unfold Sh; lia). apply (proj1 (Sh_range_iff p sz y P8 S8)) in W.
      exact (own_frame_sep Ai rho tp md tv fr i fe y HM HT HB HFF HN HFR Hnth Hout W).
    -
      unfold xlocal in Hy. cbn [fst snd] in Hy. unfold uval in Hy. rewrite U_add in Hy. cbn [eval] in Hy. change (bv_unsigned (rw rho pR)) with p in Hy.
      rewrite !u64_lit in Hy by lia. rewrite <- M64v_eq, (Z.mod_small (p + off) (2 ^ 64)) in Hy by lia.
      set (q := (y - p) / 8).
      pose proof (Z.div_mod (y - p) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (y - p) 8 ltac:(lia)) as Mq. pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
      assert (Hy8 : y / 8 = p / 8 + q) by (subst q; rewrite P8 in Dp; clear - Dq Mq Dp; nia).
      assert (Hq : off / 8 <= q < (off + len + 7) / 8).
      { subst q. split; [apply Z.div_le_mono; clear - Hy; lia|]. apply Z.div_lt_upper_bound; [clear - Hy; lia|].
        pose proof (Z.div_mod (off + len + 7) 8 ltac:(lia)) as DL8. pose proof (Z.mod_pos_bound (off + len + 7) 8 ltac:(lia)) as ML8. first [clear - Hy DL8 ML8; lia | nia]. }
      pose proof (proj1 (forallb_forall _ _) Hwc q (In_granules off len q Ho0 Hl1 Hq)) as WQ. cbn beta in WQ.
      apply orb_prop in WQ. rewrite Hy8 in Hin. unfold Sh in Hin.

      pose proof (Z.div_mod q 8 ltac:(lia)) as Dq8. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Mq8.
      assert (WB : (SHADOW_OFF + (p / 8 + q)) / 8 * 8 = SHADOW_OFF + p / 8 + q / 8 * 8).
      { unfold Sh in SP8. pose proof (Z.div_mod (p / 8 + SHADOW_OFF) 8 ltac:(lia)) as DS. rewrite SP8 in DS.
        replace (SHADOW_OFF + (p / 8 + q)) with ((( p / 8 + SHADOW_OFF) / 8 + q / 8) * 8 + q mod 8) by (clear - DS Dq8 Mq8; lia).
        rewrite Z.div_add_l by (clear - Mq8; lia). rewrite (Z.div_small (q mod 8) 8) by (clear - Mq8; lia). clear - DS Dq8 Mq8; lia. }
      rewrite WB in Hin. destruct WQ as [WQ|WQ]; [apply Z.leb_le in WQ | apply Z.leb_le in WQ]; first [ clear - Hin WQ Hj Hq Dq8 Mq8; lia | lia ]. }
  specialize (SP2 XCL).
  assert (EQS : ax_setS A1 (mkSS (ss_pc (ax_S A1)) (ss_regs (ax_S A1)) (ss_fregs (ax_S A1)) (ss_fcsr (ax_S A1)) (ss_resv (ax_S A1))
                          (ss_objs (ax_S A1) ++ [carved (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) []]) (ss_facts (ax_S A1)) (ss_next (ax_S A)) (ss_lenient (ax_S A1)))
                = shadow_reopen_stateA A X' g k1 k2).
  { subst A1. destruct A as [S X b]. destruct S. reflexivity. }
  rewrite EQS in SP2. destruct SP2 as [Hsm5 HJ5]. split; [exact Hsm5|]. exists Ai, kc. exact HJ5.
Qed.

Definition flag_carve_stateA (A : axst) (pF : positive) : axst :=
  let S := ax_S A in
  mkAX (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [flagbyte_obj (SVar pF) []])
             (ss_facts S) (ss_next S) (ss_lenient S)) (ax_X A) (ax_base A).

Lemma JA_flag_carve : forall tv fr bd am i pR c pF (A : axst) rho tp w,
  nth_error fr i = Some (SVar pR, c, SVar pF) -> 0 <= c <= 6 ->
  ax_base A = SLit SHADOW_OFF ->
  swf (ax_S (flag_carve_stateA A pF)) = true ->
  (forall Ai rho1 tp1 md1, Forall (holds rho) (ss_facts (ax_S A)) -> P0f rho0 -> agree_vals NP rho0 rho -> AInv Ai rho1 tp1 md1 -> TPA rho0 Ai -> T_ok rho (topG (aa_geom Ai)) ->
      fbinA FB Ai -> ffinA FF Ai -> tvinA FB Ai rho tv -> tvd rho tv -> tvz rho tv -> frinA FF Ai rho fr ->
      (forall o a, In o (ss_objs (ax_S A)) -> fst (obj_range rho o) <= a < snd (obj_range rho o) ->
          pclMA CST rho0 (FBx FB rho tv) (FFx FF rho fr) a \/ (0 <= a < IMG_HI \/ is_shadowZ a))
      /\ TobjJAR.xrs_ok47 rho (ax_X A)) ->
  SPA segs (JA (NDA tv fr bd am)) A rho tp w ->
  SPA segs (JA (NDA tv fr bd am)) (flag_carve_stateA A pF) rho tp w.
Proof using ALA HCST HXGL HBX HKc HTOP LFLAG HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF A rho tp w Hnth Hc6 Hbase Hwf HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT) HB HFF HN HD HZ HFR) as [HROK HX47].
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9.
  set (p := uval rho (SVar pR)) in *. set (fl := uval rho (SVar pF)) in *. set (sz := fs_frame_size c) in *.
  unfold aceil in F5, F7.
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  pose proof (SPA_carve_plain segs (JAi (NDA tv fr bd am) Ai kc) rho A tp (tr, mkCfg ms md) (SVar pF) (SLit 1) (ss_next (ax_S A)) (conj Hsm HJ)) as SP.
  cbn zeta in SP. cbn [eval] in SP. change (bv_unsigned (rw rho pF)) with fl in SP. rewrite (u64_lit 1) in SP by lia.
  specialize (SP ltac:(unfold flag_carve_stateA in Hwf; exact Hwf) ltac:(lia) ltac:(lia) ltac:(unfold HIGH_SHADOW_END in F6; lia)).
  assert (DISJ : Forall (fun o' => ranges_disjoint (obj_range rho o') (fl, fl + 1)) (ss_objs (ax_S A))).
  { apply Forall_forall. intros o Ho'. destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
    assert (Ea : a = fl) by lia. subst a.
    destruct (HROK o fl Ho' ltac:(rewrite Eo; exact Ha1)) as [[Hs|[Hc|[(b & n & Hbn & Hr)|(f & s0 & fl' & Hf & Hr)]]]|Hlow].
    - unfold aceil in Hs. lia.
    - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
    - destruct (F8 b n (FBX _ Hbn)); lia.
    - destruct (FFX _ _ _ Hf) as [Hf1 _]. destruct (F9 f s0 Hf1); lia.
    - unfold is_shadowZ in Hlow. lia. }
  specialize (SP DISJ ltac:(intros z Hz; replace z with fl by lia; exists (Z_to_bv 8 1); rewrite E2; exact (LFLAG Ai rho tp md _ HM E1))).
  assert (XCL : xwords_clear rho A fl (fl + 1)).
  { intros rr y j Hr Hy Hj Hin. rewrite Hbase in Hin. cbn [eval] in Hin. rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
    pose proof (HX47 rr y Hr Hy) as Hy47.
    pose proof (word_byte_of_shadow (Sh y) j (Sh_is_shadow y Hy47) Hj) as WS.
    destruct (word_byte_range (Sh y) j ltac:(pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia) Hj) as (_ & EWB & _).
    rewrite EWB in WS. unfold Sh in WS. replace (y / 8 + SHADOW_OFF) with (SHADOW_OFF + y / 8) in WS by lia. unfold is_shadowZ in WS. lia. }
  specialize (SP XCL).
  assert (EQS : ax_setS A (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                               (ss_objs (ax_S A) ++ [plain_obj (SVar pF) (SLit 1)]) (ss_facts (ax_S A)) (ss_next (ax_S A)) (ss_lenient (ax_S A)))
                = flag_carve_stateA A pF).
  { destruct A as [S X b]. destruct S. reflexivity. }
  rewrite EQS in SP. destruct SP as [Hsm5 HJ5]. split; [exact Hsm5|]. exists Ai, kc. exact HJ5.
Qed.

Ltac split_lazy_andb H :=
  first [ apply lazy_andb_prop in H;
          let H1 := fresh "HQ" in let H2 := fresh "HQ" in
          destruct H as [H1 H2]; split_lazy_andb H1; split_lazy_andb H2
        | idtac ].

Definition release_objs_ok (pR pF g : positive) (c : Z) (R : list sobj) : bool :=
  let sz := fs_frame_size c in
  match R with
  | [of; ofl; osh; ofb] =>
      sv_eqb (ob_base of) (SVar pR) &&& sv_eqb (ob_lo of) (SLit 0) &&& sv_eqb (ob_hi of) (SLit (sz - 8)) &&& dflt_writable (ob_dflt of)
      &&& sv_eqb (ob_base ofl) (SVar pR) &&& sv_eqb (ob_lo ofl) (SLit (sz - 8)) &&& sv_eqb (ob_hi ofl) (SLit sz) &&& dflt_writable (ob_dflt ofl)
      &&& sv_eqb (ob_base osh) (SVar g) &&& sv_eqb (ob_lo osh) (SLit (SHADOW_OFF + 0)) &&& sv_eqb (ob_hi osh) (SLit (SHADOW_OFF + sz / 8)) &&& dflt_writable (ob_dflt osh)
      &&& sv_eqb (ob_base ofb) (SVar pF) &&& sv_eqb (ob_lo ofb) (SLit 0) &&& sv_eqb (ob_hi ofb) (SLit 1)
      &&& match ob_cells ofb with [c0] => sv_eqb (SymState.c_off c0) (SLit 0) &&& (SymState.c_width c0 =? 1) &&& sv_eqb (SymState.c_val c0) (SLit 0) | _ => false end
  | _ => false
  end.

Lemma obj_range_lit : forall rho o base lo hi, ob_base o = base -> ob_lo o = SLit lo -> ob_hi o = SLit hi ->
  - 2 ^ 63 <= lo < 2 ^ 63 -> - 2 ^ 63 <= hi < 2 ^ 63 ->
  obj_range rho o = (bv_unsigned (eval rho base) + lo, bv_unsigned (eval rho base) + hi).
Proof using .
  intros rho o base lo hi Hb Hl Hh Hlo Hhi. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. rewrite !soff_lit_small by lia. reflexivity.
Qed.

Lemma JA_release_inline : forall tv fr bd am i pR c pF g (A : axst) objs R rho tp tr ms md,
  nth_error fr i = Some (SVar pR, c, SVar pF) -> 0 <= c <= 6 ->
  ss_objs (ax_S A) = objs ++ R -> release_objs_ok pR pF g c R = true ->
  has_facts [SPEq (g8 g) (SVar pR); SPUle (SVar g) (SLit (2 ^ 61 - 1))] (ss_facts (ax_S A)) = true ->
  nd_below (ss_next (ax_S A)) (NDA tv fr bd am) = true ->
  (forall A1 A2, PA A1 -> PA A2) ->
  SPA segs (JA (NDA tv fr bd am)) A rho tp (tr, mkCfg ms md) ->
  SPA segs (JA (NDA tv (remove_nth i fr) bd am)) (drop_lastA A objs) (rho_absorb rho R (vms md tp ms)) tp (tr, mkCfg ms md).
Proof using ALA HCST HXGL HBX HKc HTOP LFLAG LFSH HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF g A objs R rho tp tr ms md Hnth Hc6 Ho HR Hfe2 Hnb HPAK [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9.
  set (p := uval rho (SVar pR)) in *. set (fl := uval rho (SVar pF)) in *. set (sz := fs_frame_size c) in *.
  unfold aceil in F5, F7. pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END in F4; lia).
  pose proof (has_facts_sound rho _ _ HF Hfe2) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia.
    change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  pose proof Hsm as (HsmS & HMI & HwfA & Hsh & Hhz).
  pose proof HsmS as (Hswf & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & (Hall & Hpd & Hfr) & _).
  cbn [virt fst snd cfg_ms cfg_model] in Hall, Hrom.

  unfold release_objs_ok in HR. destruct R as [|of [|ofl [|osh [|ofb [|]]]]]; try discriminate. fold sz in HR.
  split_lazy_andb HR.
  repeat match goal with H : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in H end.
  match goal with H : match ob_cells ofb with _ => _ end = true |- _ => rename H into Hcells end.
  assert (Rf : obj_range rho of = (p, p + (sz - 8))).
  { rewrite (obj_range_lit rho of (SVar pR) 0 (sz - 8)); try assumption; try lia. cbn [eval]. change (bv_unsigned (rw rho pR)) with p. f_equal. lia. }
  assert (Rfl : obj_range rho ofl = (p + (sz - 8), p + sz)).
  { rewrite (obj_range_lit rho ofl (SVar pR) (sz - 8) sz); try assumption; try lia. cbn [eval]. change (bv_unsigned (rw rho pR)) with p. reflexivity. }
  assert (Rsh : obj_range rho osh = (Sh p, Sh p + sz / 8)).
  { rewrite (obj_range_lit rho osh (SVar g) (SHADOW_OFF + 0) (SHADOW_OFF + sz / 8)); try assumption; try (unfold SHADOW_OFF; lia). cbn [eval]. rewrite Ug. unfold Sh, SHADOW_OFF. f_equal; lia. }
  assert (Rfb : obj_range rho ofb = (fl, fl + 1)).
  { rewrite (obj_range_lit rho ofb (SVar pF) 0 1); try assumption; try lia. cbn [eval]. change (bv_unsigned (rw rho pF)) with fl. f_equal. lia. }
  set (R := [of; ofl; osh; ofb]) in *.
  set (rho' := rho_absorb rho R (vms md tp ms)).
  assert (EVr : forall e, eval rho' e = eval rho e) by (intros e; unfold rho'; apply eval_absorb).
  assert (CHG : forall a, rm rho' a <> rm rho a ->
            let z := bv_unsigned a in (p <= z < p + sz) \/ (Sh p <= z < Sh p + sz / 8) \/ z = fl).
  { intros a Hne z. destruct (in_ranges_dec rho R a) as [Hin|Hnin].
    - destruct Hin as (o & Hoin & Hr). subst z. destruct Hoin as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?Rf, ?Rfl, ?Rsh, ?Rfb in Hr; cbn [fst snd] in Hr; lia.
    - exfalso. apply Hne. unfold rho'. apply GlueM.rm_absorb_out. exact Hnin. }
  assert (OUT : forall a, let z := bv_unsigned a in ~ (p <= z < p + sz) -> ~ (Sh p <= z < Sh p + sz / 8) -> z <> fl -> rm rho' a = rm rho a).
  { intros a z H1 H2 H3.
    destruct (rm rho' a) as [x|] eqn:Ea; destruct (rm rho a) as [y|] eqn:Eb.
    all: try reflexivity.
    all: try (exfalso; destruct (CHG a ltac:(rewrite Ea, Eb; congruence)) as [C|[C|C]]; subst z; [exact (H1 C) | exact (H2 C) | exact (H3 C)]).
    destruct (bv_eq_dec 8 x y) as [->|NE]; [reflexivity|]. exfalso. destruct (CHG a ltac:(rewrite Ea, Eb; congruence)) as [C|[C|C]]; subst z; [exact (H1 C) | exact (H2 C) | exact (H3 C)]. }

  assert (BYo : forall o, In o R -> dflt_writable (ob_dflt o) = true -> IMG_HI <= fst (obj_range rho o) \/ o = osh -> snd (obj_range rho o) <= 2 ^ 63 ->
            forall z, fst (obj_range rho o) <= z < snd (obj_range rho o) -> rm rho' (Z_to_bv 64 z) <> None).
  { intros o HoR Hdw Hlo Hhi.
    destruct (released_bytesA segs HTOP rho A objs R o tp tr ms md Ho HoR Hsm Hdw ltac:(destruct Hlo as [Hlo| ->]; [unfold IMG_HI, HIGH_SHADOW_END in *; lia | rewrite Rsh; cbn [fst]; unfold Sh, SHADOW_OFF, IMG_HI; lia]) Hhi) as [BY _].
    exact BY. }
  assert (BYf : forall z, p <= z < p + (sz - 8) -> rm rho' (Z_to_bv 64 z) <> None).
  { intros z Hz. apply (BYo of ltac:(left; reflexivity) ltac:(assumption) ltac:(left; rewrite Rf; cbn [fst]; lia) ltac:(rewrite Rf; cbn [snd]; lia)). rewrite Rf. exact Hz. }
  assert (BYfl : forall z, p + (sz - 8) <= z < p + sz -> rm rho' (Z_to_bv 64 z) <> None).
  { intros z Hz. apply (BYo ofl ltac:(right; left; reflexivity) ltac:(assumption) ltac:(left; rewrite Rfl; cbn [fst]; lia) ltac:(rewrite Rfl; cbn [snd]; lia)). rewrite Rfl. exact Hz. }
  assert (BYsh : forall z, Sh p <= z < Sh p + sz / 8 -> rm rho' (Z_to_bv 64 z) <> None).
  { intros z Hz. apply (BYo osh ltac:(right; right; left; reflexivity) ltac:(assumption) ltac:(right; reflexivity) ltac:(rewrite Rsh; cbn [snd]; unfold Sh, SHADOW_OFF; lia)). rewrite Rsh. exact Hz. }
  assert (FL0 : rm rho' (Z_to_bv 64 fl) = Some (Z_to_bv 8 0)).
  { assert (Hin : in_ranges rho R (Z_to_bv 64 fl)).
    { exists ofb. split; [do 3 right; left; reflexivity|]. rewrite Rfb. cbn [fst snd]. rewrite u64_lit by (unfold HIGH_SHADOW_END in F6; lia). lia. }
    unfold rho'. rewrite (GlueM.rm_absorb_in rho R _ _ Hin).
    rewrite Ho in Hall. apply Forall_app in Hall as [_ HallR].
    pose proof (proj1 (Forall_forall _ _) HallR ofb ltac:(do 3 right; left; reflexivity)) as Hofb.
    pose proof (cell1_byte rho (vms md tp ms) ofb 0 0 Hrom Hofb) as C.
    destruct (ob_cells ofb) as [|[co cw cv] [|]]; try discriminate. cbn [SymState.c_off SymState.c_width SymState.c_val] in Hcells.
    split_lazy_andb Hcells.
    repeat match goal with H : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in H end.
    match goal with H : (cw =? 1) = true |- _ => apply Z.eqb_eq in H end. subst co cw cv.
    specialize (C ltac:(left; reflexivity) ltac:(lia) ltac:(lia)). cbn zeta in C.
    replace (ob_base ofb) with (SVar pF) in C by (symmetry; assumption). cbn [eval] in C. change (bv_unsigned (rw rho pF)) with fl in C. rewrite Z.add_0_r in C.
    apply C. unfold IMG_HI, HIGH_SHADOW_END in *. lia. }

  destruct (law_fake_frame_release _ _ _ ALA Ai rho rho' tp md p sz HM E1) as (A' & l1 & l2 & HM' & HLi & HF' & HL' & HV' & HKm' & HKf' & HG').
  { intros z Hz Hnf Hnfl Hnsh. apply OUT; rewrite u64_lit by exact Hz; [exact Hnf | | rewrite E2; exact Hnfl].
    intros Hr. apply Hnsh. unfold Sh in Hr |- *. pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)).
    replace (p + sz) with ((p / 8 + sz / 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  { rewrite <- E2 || idtac. fold fl. rewrite <- E2 in |- * || idtac. replace (frame_flag (aa_geom Ai) (p, sz)) with fl by exact E2. exact FL0. }
  { intros z Hz. destruct (Z_lt_dec z (p + (sz - 8))); [apply BYf; lia | apply BYfl; lia]. }
  { intros z Hz. apply BYsh. unfold Sh in Hz |- *. pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)).
    replace (p + sz) with ((p / 8 + sz / 8) * 8) in Hz by lia. rewrite Z.div_mul in Hz by lia. lia. }

  pose proof HFR as (HFR0 & HCEN & HND).
  destruct (remove_nth_split fr i fe Hnth) as [SP1 SP2].
  assert (Efe : frv rho fe = (p, sz)) by reflexivity.
  assert (OTHER : forall x, In x (remove_nth i fr) -> frv rho x <> frv rho fe).
  { intros x Hx Ex. rewrite SP1 in HND. rewrite map_app in HND. cbn [map] in HND.
    apply (NoDup_remove_2 _ _ _ HND). rewrite <- map_app, <- Ex. apply in_map. rewrite <- SP2. exact Hx. }
  pose proof (proj1 (Forall_forall _ _) HFR0 fe Hfe) as (_ & _ & E3). rewrite Efe in E3. cbn [fst] in E3.
  assert (FFin : forall f s0 fl0, In (f, s0, fl0) FF -> In (f, s0) (aa_frames A')).
  { intros f s0 fl0 Hin. destruct (HFF _ _ _ Hin) as [HinA _].
    rewrite HLi in HinA. apply in_mid_cases in HinA as [Ex|HinA]; [|rewrite HF'; exact HinA].
    exfalso. apply (E3 _ Hin). cbn [fst]. injection Ex as -> ->. reflexivity. }
  assert (FR0 : frinA0 FF A' rho (remove_nth i fr)).
  { unfold frinA0. apply Forall_forall. intros x Hx.
    pose proof (proj1 (Forall_forall _ _) HFR0 x (In_remove_nth _ _ _ Hx)) as (X1 & X2 & X3).
    rewrite HG'. split; [|split; [exact X2 | exact X3]].
    rewrite HLi in X1. apply in_mid_cases in X1 as [Ex|X1]; [exfalso; apply (OTHER x Hx); rewrite Ex, Efe; reflexivity | rewrite HF'; exact X1]. }
  assert (ND : List.NoDup (aa_frames Ai)) by (eapply (frames_nodup segs AInv CST ALA); exact HM).

  split; [exact (smatchA_unobj segs rho A objs R tp tr ms md Ho Hsm)|].
  exists A', kc.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM'|]. split; [unfold TPA in HT |- *; rewrite HG'; exact HT|].
  split; [intros b Hb; rewrite HL'; exact (HB b Hb)|].
  split; [intros f s0 fl0 Hin; split; [exact (FFin _ _ _ Hin) | rewrite HG'; exact (proj2 (HFF _ _ _ Hin))]|].
  cbn [nd_tv nd_fr nd_bd nd_am].
  assert (HN' : tvinA FB A' rho tv).
  { unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (Y0 & Y1 & Y2).
    split; [exact Y0|]. split; [rewrite HL'; exact Y1 | exact Y2]. }
  split.
  { split; [|split]; [eapply tvinA_map; [| | exact HN'] | eapply tvd_map; [| | exact HD] | eapply tvz_map; [| | exact HZ]];
      try (apply map_ext; intros t; unfold tvv; rewrite !EVr; reflexivity);
      intros k t t' Ht Ht'; rewrite Ht in Ht'; injection Ht' as <-; unfold tnz; rewrite EVr; tauto. }
  split.
  {
    split; [|split].
    - unfold frinA0 in FR0 |- *. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) FR0 x Hx) as Y.
      unfold frv, uval in Y |- *. rewrite !EVr. exact Y.
    - intros y Hy. rewrite HF' in Hy.
      assert (HyA : In y (aa_frames Ai)) by (rewrite HLi; apply in_app_mid; exact Hy).
      destruct (HCEN y HyA) as [H|H]; [left; exact H | right].
      rewrite SP1, map_app in H. cbn [map] in H. rewrite SP2, map_app.
      rewrite (map_ext (frv rho') (frv rho)) by (intros x; unfold frv, uval; rewrite !EVr; reflexivity).
      rewrite (map_ext (frv rho') (frv rho)) in |- * by (intros x; unfold frv, uval; rewrite !EVr; reflexivity) || idtac.
      apply in_mid_cases in H as [Ex|H]; [|rewrite <- map_app; rewrite map_app; exact H].
      exfalso. rewrite HLi in ND. apply (NoDup_remove_2 _ _ _ ND). rewrite <- Efe, <- Ex. exact Hy.
    - rewrite (map_ext (frv rho') (frv rho)) by (intros x; unfold frv, uval; rewrite !EVr; reflexivity).
      rewrite SP1 in HND. rewrite map_app in HND. cbn [map] in HND. rewrite SP2, map_app. exact (NoDup_remove_1 _ _ _ HND). }
  split.
  {
    destruct HK0 as [K1 K2]. split.
    - intros a Ha Hp. rewrite <- (K1 a Ha Hp).
      destruct Hp as [Hp|[(x & Hx & Hpx & ->) _]].
      +
        assert (NF : ~ (p <= a < p + sz)).
        { exact (own_frame_sepF Ai rho tp md tv fr i fe a HM HT HB HFF HFR Hnth (or_introl Hpx || or_introl Hp) ) || exact (own_frame_sepF Ai rho tp md tv fr i fe a HM HT HB HFF HFR Hnth (or_introl Hp)). }
        assert (NS : ~ (Sh p <= a < Sh p + sz / 8)).
        { intros Hr. pose proof (Sh_is_shadow p ltac:(lia)) as S1. pose proof (Sh_is_shadow (p + sz - 1) ltac:(lia)) as S2. rewrite Sh_last in S2 by lia.

          apply (client_not_shadow segs AInv CST ALA HCST Ai a rho tp md HM (pclFA_client CST rho0 FB FF Ai a HB HFF HT Hp)).
          unfold is_shadowZ in S1, S2 |- *. lia. }
        destruct (Z.eq_dec a fl) as [->|Hne]; [|apply OUT; rewrite u64_lit by exact Ha; assumption].

        destruct Hp as [Hs|[Hc|[(b & n & Hbn & Hr)|(f & s0 & fl0 & Hf & Hr)]]].
        * exfalso. unfold aceil in Hs. lia.
        * exfalso. hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
        * exfalso. destruct (F8 b n (HB _ Hbn)); lia.
        * destruct (HFF _ _ _ Hf) as [Hf1 Hfl]. destruct Hr as [Hr|Efl].
          -- exfalso. destruct (F9 f s0 Hf1); lia.
          -- rewrite Efl, Hfl. rewrite (LFLAG Ai rho tp md (f, s0) HM Hf1).
             rewrite <- HG'. exact (LFLAG A' rho' tp md (f, s0) HM' (FFin _ _ _ Hf)).
      +
        assert (Hx47 : 0 <= x < 2 ^ 47).
        { destruct Hpx as [Hpx|Hg]; [exact (pclFA_range segs AInv CST ALA HCST rho0 FB FF Ai rho tp md x HM HB HFF HT Hpx) | apply HXGL in Hg; unfold IMG_HI, LOW_SHADOW_BEG in Hg; lia]. }
        pose proof (Sh_is_shadow x Hx47) as SS. unfold is_shadowZ in SS.
        apply OUT; rewrite u64_lit by exact Ha.
        * unfold HIGH_SHADOW_END in *. lia.
        * intros Hr. apply (proj1 (Sh_range_iff p sz x P8 S8)) in Hr. exact (own_frame_sepF Ai rho tp md tv fr i fe x HM HT HB HFF HFR Hnth Hpx Hr).
        * unfold HIGH_SHADOW_END in *. lia.
    - intros a j Ha Hp Hj Hd0. pose proof (K2 a j Ha Hp Hj Hd0) as Hd. destruct (rm rho' (word_byte a j)) eqn:Ew; [discriminate|]. exfalso.
      destruct (CHG (word_byte a j) ltac:(intros EQ; apply Hd; rewrite <- EQ; exact Ew)) as [C|[C|C]].
      +         destruct (Z_lt_dec (bv_unsigned (word_byte a j)) (p + (sz - 8))).
        * apply (BYf (bv_unsigned (word_byte a j))); [lia|]. rewrite Z_to_bv_bv_unsigned. exact Ew.
        * apply (BYfl (bv_unsigned (word_byte a j))); [lia|]. rewrite Z_to_bv_bv_unsigned. exact Ew.
      + apply (BYsh (bv_unsigned (word_byte a j))); [exact C|]. rewrite Z_to_bv_bv_unsigned. exact Ew.
      + pose proof FL0 as FL. rewrite <- C, Z_to_bv_bv_unsigned in FL. rewrite Ew in FL. discriminate. }
  split; [exact HP0|].

  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  assert (XT : XAz FB (am_eval rho am) A' (rm rho') (tvals rho tv) kc /\ apotz (am_eval rho am) (rm rho') = apotz (am_eval rho am) (rm rho)).
  { eapply (XAz_transport FB FB _ Ai A' (rm rho) (rm rho')); [exact HXA | | | |].
    - intros b n Hin Hnfb Hut. rewrite HL'. auto.
    - intros b n z Hin _ _ Hz. destruct (HBl b n Hin) as (G1 & G2 & G3 & G4 & G5). unfold HIGH_SHADOW_END in G5.
      apply OUT; rewrite u64_of_sum by lia.
      + intros Hr. destruct (block_frame_sep Ai rho tp md b n p sz HM Hin E1); lia.
      + intros Hr. pose proof (Sh_is_shadow p ltac:(lia)) as S1. pose proof (Sh_is_shadow (p + sz - 1) ltac:(lia)) as S2. rewrite Sh_last in S2 by lia.
        unfold is_shadowZ, HIGH_SHADOW_END in *. lia.
      + intros ->. destruct (F8 b n Hin); lia.
    - intros b n a Hin _ _ Ha. destruct (HBl b n Hin) as (G1 & G2 & G3 & G4 & G5). unfold HIGH_SHADOW_END in G5.
      pose proof (Sh_is_shadow a ltac:(lia)) as SS. unfold is_shadowZ in SS.
      split.
      + intros _. rewrite shadow_addr_Sh. apply OUT; rewrite u64_of_sum by (unfold SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
        * unfold HIGH_SHADOW_END in *. lia.
        * intros Hr. apply (proj1 (Sh_range_iff p sz a P8 S8)) in Hr. destruct (block_frame_sep Ai rho tp md b n p sz HM Hin E1); lia.
        * unfold HIGH_SHADOW_END in *. lia.
      + intros j Hj Hd. destruct (rm rho' (word_byte (SHADOW_OFF + a / 8) j)) eqn:Ew; [discriminate|]. exfalso.
        destruct (CHG (word_byte (SHADOW_OFF + a / 8) j) ltac:(intros EQ; apply Hd; rewrite <- EQ; exact Ew)) as [C|[C|C]].
        * destruct (Z_lt_dec (bv_unsigned (word_byte (SHADOW_OFF + a / 8) j)) (p + (sz - 8))).
          -- apply (BYf (bv_unsigned (word_byte (SHADOW_OFF + a / 8) j))); [lia|]. rewrite Z_to_bv_bv_unsigned. exact Ew.
          -- apply (BYfl (bv_unsigned (word_byte (SHADOW_OFF + a / 8) j))); [lia|]. rewrite Z_to_bv_bv_unsigned. exact Ew.
        * apply (BYsh (bv_unsigned (word_byte (SHADOW_OFF + a / 8) j))); [exact C|]. rewrite Z_to_bv_bv_unsigned. exact Ew.
        * pose proof FL0 as FL. rewrite <- C, Z_to_bv_bv_unsigned in FL. rewrite Ew in FL. discriminate.
    -
      intros bn H1 _ H3 H4. rewrite HL' in H1. auto. }
  destruct XT as [XT1 XT2].
  refine (conj _ (conj _ (conj (HPAK Ai A' HPA) (conj ltac:(eapply capK_same; [exact HCKi | exact HL' | rewrite HV'; lia]) _)))).
  { unfold XA. rewrite (am_eval_exteq am rho rho' ltac:(intros e _; apply EVr)).
    unfold tvals. rewrite (map_ext (tvv rho') (tvv rho)) by (intros t; unfold tvv; rewrite !EVr; reflexivity). exact XT1. }
  { unfold apot. rewrite (am_eval_exteq am rho rho' ltac:(intros e _; apply EVr)). rewrite XT2. fold (apot am rho).
    rewrite HV', HKm', HKf'.
    destruct (bsum_eval_ext bd rho' rho EVr) as [B1 B2]. unfold BUD in HBU |- *. rewrite B1, B2.
    destruct HBU as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). repeat (split; [assumption|]). split; [|split; assumption].
    eapply bd_nn_eval_ext; [| exact Q7]. intros e. symmetry. apply EVr. }
  {
    unfold capN in *. cbn [nd_tv]. rewrite (small_live_same Ai A' HL'), (cntS_ext rho rho' _ EVr). exact HCNi. }
Qed.

Lemma SPA_x_len0 : forall (J : jpredA) (A : axst) pR k rho tp w,
  existsb (sprop_eqb (SPAlign pR k)) (ss_facts (ax_S A)) = true -> 3 <= k ->
  (pR <? ss_next (ax_S A))%positive = true ->
  SPA segs J A rho tp w -> SPA segs J (ax_setX A ((SVar pR, SLit 0) :: ax_X A)) rho tp w.
Proof using .
  intros J A pR k rho tp w Hf Hk Hb HS. apply SPA_x_publish; [| | exact HS].
  - unfold xr_below. cbn [fst snd sv_below]. rewrite Hb. reflexivity.
  - pose proof (holds_mem rho _ _ (smatchA_facts segs _ _ _ _ (proj1 HS)) Hf) as HA. cbn [holds] in HA. destruct HA as [_ HA].
    unfold xr_ok. cbn [fst snd eval]. rewrite (u64_lit 0) by lia. split; [|split; [pose proof (bv_urange (rw rho pR)) as R0; change (bv_modulus 64) with (2 ^ 64) in R0; lia | intros a Ha; lia]].
    apply Z.mod_divide in HA; [|lia]. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact HA].
    exists (2 ^ (k - 3)). replace k with ((k - 3) + 3) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma In_remove_nth_ne {T} : forall (l : list T) i j x, nth_error l j = Some x -> i <> j -> In x (remove_nth i l).
Proof using .
  induction l as [|y l IH]; intros [|i] [|j] x H Hne; cbn in H |- *; try discriminate.
  - exfalso. apply Hne. reflexivity.
  - eapply nth_error_In. exact H.
  - injection H as ->. left. reflexivity.
  - right. eapply IH; [exact H | lia].
Qed.

Fixpoint robj_ownframe (fr : list (sv * Z * sv)) (j : nat) (skip : option nat) (o : sobj) : bool :=
  match fr with
  | [] => false
  | x :: rest =>
      (negb (match skip with Some i => Nat.eqb i j | None => false end)
       &&& (sv_eqb (ob_base o) (fst (fst x))
       &&& match ob_lo o, ob_hi o with
           | SLit lo, SLit hi => (0 <=? lo) &&& ((lo <=? hi) &&& ((hi <=? fs_frame_size (snd (fst x))) &&& ((0 <=? snd (fst x)) &&& (snd (fst x) <=? 6))))
           | _, _ => false end))
      ||| robj_ownframe rest (S j) skip o
  end.

Definition robj_image (o : sobj) : bool :=
  match ob_base o, ob_lo o, ob_hi o with
  | SLit 0, SLit lo, SLit hi => (0 <=? lo) &&& ((lo <=? hi) &&& (hi <=? IMG_HI))
  | _, _, _ => false
  end.

Definition robjs_checkF_ref (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool :=
  forallb (fun o => robj_stackA facts o ||| (robj_tracked tv None o ||| (robj_ownframe fr 0 skip o ||| (robj_image o ||| extra o)))) R.

Definition robjs_checkF_dg (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool :=
  let pf := DigFastA.mk_pf_f facts in
  forallb (fun o => robj_tracked tv None o ||| (robj_ownframe fr 0 skip o ||| (robj_image o ||| (extra o ||| robj_stackA_p pf o)))) R.
Lemma robjs_checkF_dg_eq : forall facts tv fr skip extra R, robjs_checkF_dg facts tv fr skip extra R = robjs_checkF_ref facts tv fr skip extra R.
Proof using .
  clear. intros facts tv fr skip extra R. unfold robjs_checkF_dg, robjs_checkF_ref. cbv zeta. rewrite DigFastA.mk_pf_f_eq.
  induction R as [|o r IH]; cbn [forallb]; [reflexivity|]. rewrite IH, robj_stackA_p_eq.
  destruct (robj_stackA facts o), (robj_tracked tv None o), (robj_ownframe fr 0 skip o), (robj_image o), (extra o); reflexivity.
Qed.
Definition robjs_checkF (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool :=
  if forallb_lazy (fun o => robj_tracked tv None o ||| (robj_ownframe fr 0 skip o ||| (robj_image o ||| extra o))) R then true else robjs_checkF_dg facts tv fr skip extra R.
Lemma robjs_checkF_ref_eq : forall facts tv fr skip extra R, robjs_checkF facts tv fr skip extra R = robjs_checkF_ref facts tv fr skip extra R.
Proof using .
  clear. intros facts tv fr skip extra R. unfold robjs_checkF. rewrite <- robjs_checkF_dg_eq.
  destruct (forallb_lazy (fun o => robj_tracked tv None o ||| (robj_ownframe fr 0 skip o ||| (robj_image o ||| extra o))) R) eqn:Z; [|reflexivity].
  symmetry. rewrite robjs_checkF_dg_eq. unfold robjs_checkF_ref. revert Z. apply forallb_lazy_weaken_rl. intros o Hs.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; try reflexivity; try discriminate Hs; try exact Hs.
Qed.

Lemma robj_ownframe_sound : forall fr j0 skip o, robj_ownframe fr j0 skip o = true ->
  exists j x lo hi, nth_error fr j = Some x /\ skip <> Some (j0 + j)%nat /\ ob_base o = fst (fst x) /\ ob_lo o = SLit lo /\ ob_hi o = SLit hi
                    /\ 0 <= lo /\ lo <= hi /\ hi <= fs_frame_size (snd (fst x)) /\ 0 <= snd (fst x) <= 6.
Proof using .
  induction fr as [|y rest IH]; intros j0 skip o H; cbn [robj_ownframe] in H; [discriminate|].
  apply lazy_orb_prop in H as [Hc|H].
  - apply lazy_andb_prop in Hc as [Hs Hc]. apply lazy_andb_prop in Hc as [Hb Hc]. apply sv_eqb_sound in Hb.
    destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
    apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H2 Hc]. apply lazy_andb_prop in Hc as [H3 Hc]. apply lazy_andb_prop in Hc as [H4 H5].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
    exists 0%nat, y, lo, hi. rewrite Nat.add_0_r. split; [reflexivity|].
    split; [destruct skip as [i|]; [intros EQ; injection EQ as ->; rewrite Nat.eqb_refl in Hs; discriminate | discriminate]|].
    repeat split; auto.
  - destruct (IH (S j0) skip o H) as (j & x & lo & hi & Hj & Hsk & R). exists (S j), x, lo, hi. split; [exact Hj|]. split; [|exact R].
    replace (j0 + S j)%nat with (S j0 + j)%nat by lia. exact Hsk.
Qed.

Lemma robjs_checkF_sound : forall Ai rho facts tv fr skip extra R rho1 tp1 md1,
  AInv Ai rho1 tp1 md1 -> Forall (holds rho) facts -> T_ok rho (T0 rho0) -> tvinA FB Ai rho tv -> tvd rho tv -> tvz rho tv -> frinA FF Ai rho fr ->
  robjs_checkF facts tv fr skip extra R = true ->
  let frs := match skip with Some i => remove_nth i fr | None => fr end in
  (forall o a, In o R -> extra o = true -> fst (obj_range rho o) <= a < snd (obj_range rho o) ->
      pclMA CST rho0 (FBx FB rho tv) (FFx FF rho frs) a \/ 0 <= a < IMG_HI) ->
  forall o a, In o R -> fst (obj_range rho o) <= a < snd (obj_range rho o) ->
    pclMA CST rho0 (FBx FB rho tv) (FFx FF rho frs) a \/ 0 <= a < IMG_HI.
Proof using ALA.
  intros Ai rho facts tv fr skip extra R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hchk frs Hextra o a Ho Hr.
  rewrite robjs_checkF_ref_eq in Hchk. unfold robjs_checkF_ref in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [left; left; exact (robj_stackA_sound facts rho _ o a HF HT0 Hc Hr)|].
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { destruct (robj_tracked_sound tv None o Hc) as (j & t & Hj & _ & Hb & Hl & Hh).
    destruct (tracked_range rho o t a Hb Hl Hh Hr) as [Ha Hpos]. pose proof (nth_error_In _ _ Hj) as Hin.
    assert (Hnz : tnz rho t) by (intros Hz0; pose proof (proj1 (Forall_forall _ _) HZ t Hin (fun H => H Hz0)); lia).
    left. right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split; [|exact Ha].
    apply In_FBx. right. exists t. rewrite <- surjective_pairing. auto. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { destruct (robj_ownframe_sound fr 0 skip o Hc) as (j & x & lo & hi & Hj & Hsk & Hb & Hl & Hh & H1 & H2 & H3 & Hc6). rewrite Nat.add_0_l in Hsk.
    pose proof (nth_error_In _ _ Hj) as Hinx.
    pose proof (proj1 (Forall_forall _ _) (proj1 HFR) x Hinx) as (X1 & _ & _).
    destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & _ & HFrl).
    destruct (HFrl _ _ X1) as (_ & _ & _ & F4 & F5 & _). top_rng F5.
    assert (Hin' : In x frs).
    { subst frs. destruct skip as [i|]; [|exact Hinx]. eapply In_remove_nth_ne; [exact Hj | intros ->; apply Hsk; reflexivity]. }
    left. right; right; right. exists (fst (frv rho x)), (snd (frv rho x)), (uval rho (snd x)). split.
    - apply In_FFx. right. exists x. split; [exact Hin' | reflexivity].
    - unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr.
      pose proof (fs_frame_size_bounds (snd (fst x))) as B.
      unfold frv in *. cbn [fst snd] in *. unfold uval in *. unfold IMG_HI, HIGH_SHADOW_END in *.
      pose proof (fs_frame_size_bounds' (snd (fst x)) Hc6) as Bsz.
      rewrite !soff_lit_small in Hr by lia. cbn [fst snd] in Hr. lia. }
  apply lazy_orb_prop in Hc as [Hc|Hc]; [|exact (Hextra o a Ho Hc Hr)].
  right. unfold robj_image in Hc. destruct (ob_base o) as [b0| | | | | | |] eqn:Eb; try discriminate. destruct b0; try discriminate.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
  apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H2 H3]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Eb, El, Eh in Hr. cbn [eval fst snd] in Hr. unfold IMG_HI in *.
  rewrite (u64_lit 0), !soff_lit_small in Hr by lia. lia.
Qed.

Definition xr_ownlocal1 (x : sv * Z * sv) (r : sv * sv) : bool :=
  match r with
  | (SAlu ALU_ADD b (SLit off), SLit len) =>
      sv_eqb b (fst (fst x)) &&& ((0 <=? off) &&& ((0 <=? len) &&& ((off + len <=? fs_frame_size (snd (fst x))) &&& ((0 <=? snd (fst x)) &&& (snd (fst x) <=? 6)))))
  | _ => false
  end.

Definition xr_len0 (r : sv * sv) : bool := match snd r with SLit len => len =? 0 | _ => false end.
Definition xr_ownlocal (fr : list (sv * Z * sv)) (skip : option nat) (r : sv * sv) : bool :=
  existsb (fun jx : nat * (sv * Z * sv) => let (j, x) := jx in
     negb (match skip with Some i => Nat.eqb i j | None => false end) &&& xr_ownlocal1 x r)
    (combine (seq 0 (length fr)) fr).

Lemma In_combine_seq {T} : forall (l : list T) k j x, In (j, x) (combine (seq k (length l)) l) -> nth_error l (j - k) = Some x /\ (k <= j)%nat.
Proof using .
  induction l as [|y l IH]; intros k j x H; cbn in H; [destruct H|]. destruct H as [EQ|H].
  - injection EQ as -> ->. rewrite Nat.sub_diag. split; [reflexivity | lia].
  - destruct (IH (S k) j x H) as [A B]. split; [|lia]. destruct (j - k)%nat as [|m] eqn:Em; [lia|]. cbn. replace (j - S k)%nat with m in A by lia. exact A.
Qed.

Definition xrs_checkL_ref (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (skip : option nat) (objs : list sobj)
           (extra : sv * sv -> bool) (X : list (sv * sv)) : bool :=
  forallb (fun r => extra r ||| (xr_len0 r ||| (xr_lit_in XGL r ||| (xr_tracked tv None r
                     ||| (existsb (xr_in_stack_obj facts r) (mkObj (fst r) (SLit 0) (snd r) [] DUnknown :: objs)
                     ||| xr_ownlocal fr skip r))))) X.

Definition xrs_checkL_dg (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (skip : option nat) (objs : list sobj)
           (extra : sv * sv -> bool) (X : list (sv * sv)) : bool :=
  let pf := DigFastA.mk_pf_f facts in
  forallb (fun r => extra r ||| (xr_len0 r ||| (xr_lit_in XGL r ||| (xr_tracked tv None r ||| (xr_ownlocal fr skip r
                     ||| existsb_lazy (xr_in_stack_obj_p pf r) (mkObj (fst r) (SLit 0) (snd r) [] DUnknown :: objs)))))) X.
Lemma xrs_checkL_dg_eq : forall facts tv fr skip objs extra X, xrs_checkL_dg facts tv fr skip objs extra X = xrs_checkL_ref facts tv fr skip objs extra X.
Proof using .
  clear. intros facts tv fr skip objs extra X. unfold xrs_checkL_dg, xrs_checkL_ref. cbv zeta. rewrite DigFastA.mk_pf_f_eq.
  induction X as [|r t IH]; cbn [forallb]; [reflexivity|]. rewrite IH, existsb_lazy_eq.
  rewrite (EntailFast.existsb_ext_in (xr_in_stack_obj_p (mk_pf facts) r) (xr_in_stack_obj facts r) _ (fun o _ => xr_in_stack_obj_p_eq facts r o)).
  destruct (extra r), (xr_len0 r), (xr_lit_in XGL r), (xr_tracked tv None r),
    (existsb (xr_in_stack_obj facts r) (mkObj (fst r) (SLit 0) (snd r) [] DUnknown :: objs)), (xr_ownlocal fr skip r); reflexivity.
Qed.
Definition xrs_checkL (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (skip : option nat) (objs : list sobj)
           (extra : sv * sv -> bool) (X : list (sv * sv)) : bool :=
  if forallb_lazy (fun r => extra r ||| (xr_len0 r ||| (xr_lit_in XGL r ||| (xr_tracked tv None r ||| xr_ownlocal fr skip r)))) X then true else xrs_checkL_dg facts tv fr skip objs extra X.
Lemma xrs_checkL_ref_eq : forall facts tv fr skip objs extra X, xrs_checkL facts tv fr skip objs extra X = xrs_checkL_ref facts tv fr skip objs extra X.
Proof using .
  clear. intros facts tv fr skip objs extra X. unfold xrs_checkL. rewrite <- xrs_checkL_dg_eq.
  destruct (forallb_lazy (fun r => extra r ||| (xr_len0 r ||| (xr_lit_in XGL r ||| (xr_tracked tv None r ||| xr_ownlocal fr skip r)))) X) eqn:Z; [|reflexivity].
  symmetry. rewrite xrs_checkL_dg_eq. unfold xrs_checkL_ref. revert Z. apply forallb_lazy_weaken_rl. intros r Hs.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; try reflexivity; try discriminate Hs; try exact Hs.
Qed.

Lemma xr_ownlocal_sound : forall fr skip r rho a, xr_ownlocal fr skip r = true ->
  uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
  exists j x, nth_error fr j = Some x /\ skip <> Some j /\ 0 <= snd (fst x) <= 6
              /\ (fst (frv rho x) <= a < fst (frv rho x) + snd (frv rho x) \/ 2 ^ 64 - 4096 <= fst (frv rho x)).
Proof using .
  intros fr skip r rho a H Ha. unfold xr_ownlocal in H. apply existsb_exists in H as ([j x] & Hin & Hc).
  apply In_combine_seq in Hin as [Hj _]. rewrite Nat.sub_0_r in Hj.
  apply lazy_andb_prop in Hc as [Hs Hc].
  exists j, x. split; [exact Hj|]. split; [destruct skip as [i|]; [intros EQ; injection EQ as ->; rewrite Nat.eqb_refl in Hs; discriminate | discriminate]|].
  - unfold xr_ownlocal1 in Hc. destruct r as [b l]. cbn [fst snd] in Ha.
    destruct b as [v|z|op b1 b2| | | | |]; try discriminate. destruct op; try discriminate. destruct b2 as [off| | | | | | |]; try discriminate.
    destruct l as [len| | | | | | |]; try discriminate.
    apply lazy_andb_prop in Hc as [Hb Hc]. apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H2 Hc].
    apply lazy_andb_prop in Hc as [H3 Hc]. apply lazy_andb_prop in Hc as [H4 H5].
    apply sv_eqb_sound in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
    subst b1. split; [lia|]. pose proof (fs_frame_size_bounds' (snd (fst x)) ltac:(lia)) as Bsz.
    unfold uval in Ha. rewrite U_add in Ha. cbn [eval] in Ha. rewrite !u64_lit in Ha by lia.
    unfold frv. cbn [fst snd]. unfold uval. set (f := bv_unsigned (eval rho (fst (fst x)))) in *.
    pose proof (bv_urange (eval rho (fst (fst x)))) as Rf. change (bv_modulus 64) with (2 ^ 64) in Rf. fold f in Rf.
    destruct (Z_lt_dec (f + off) (2 ^ 64)) as [L|L].
    + left. rewrite <- M64v_eq, Z.mod_small in Ha by lia. lia.
    + right. lia.
Qed.

Lemma xrs_checkL_sound : forall Ai rho facts tv fr skip objs extra X rho1 tp1 md1,
  AInv Ai rho1 tp1 md1 -> Forall (holds rho) facts -> T_ok rho (T0 rho0) -> tvinA FB Ai rho tv -> tvd rho tv -> tvz rho tv -> frinA FF Ai rho fr ->
  xrs_checkL facts tv fr skip objs extra X = true ->
  let frs := match skip with Some i => remove_nth i fr | None => fr end in
  (forall r a, In r X -> extra r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
      pclMA CST rho0 (FBx FB rho tv) (FFx FF rho frs) a \/ in_rangesZ XGL a) ->
  xrs_okL CST XGL rho0 FB FF rho tv frs X.
Proof using ALA.
  intros Ai rho facts tv fr skip objs extra X rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hchk frs Hextra r a Hr Ha.
  rewrite xrs_checkL_ref_eq in Hchk. unfold xrs_checkL_ref in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (Hextra r a Hr Hc Ha)|].
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { exfalso. unfold xr_len0 in Hc. destruct r as [rb rl]. cbn [fst snd] in Hc, Ha. destruct rl as [len| | | | | | |]; try discriminate. apply Z.eqb_eq in Hc. subst len.
    unfold uval in Ha. cbn [eval] in Ha. rewrite (u64_lit 0) in Ha by lia. lia. }
  apply lazy_orb_prop in Hc as [Hc|Hc]; [right; exact (xr_lit_in_sound XGL rho r a Hc Ha)|].
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { left. unfold xr_tracked in Hc.
    destruct (robj_tracked_sound tv None _ Hc) as (j & t & Hj & _ & Hb & _ & Hh). cbn [ob_base ob_hi] in Hb, Hh.
    pose proof (nth_error_In _ _ Hj) as Hin.
    assert (Er : tvv rho t = (uval rho (fst r), uval rho (snd r))) by (unfold tvv, uval; rewrite Hb, Hh; reflexivity).
    destruct (Z.eq_dec (uval rho (fst r)) 0) as [Hz0|Hnz0].
    { exfalso. pose proof (proj1 (Forall_forall _ _) HZ t Hin) as Z0. cbv beta in Z0. rewrite Er in Z0. cbn [snd] in Z0.
      unfold tnz in Z0. rewrite <- Hb in Z0. unfold uval in *. specialize (Z0 ltac:(lia)). lia. }
    assert (Hnz : tnz rho t) by (unfold tnz; rewrite <- Hb; unfold uval in Hnz0; exact Hnz0).
    right; right; left. exists (uval rho (fst r)), (uval rho (snd r)). split; [|exact Ha].
    apply In_FBx. right. exists t. rewrite Er. auto. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { apply existsb_exists in Hc as (o & Ho & Hc). left. left. eapply xr_in_stack_obj_sound; eauto. }
  destruct (xr_ownlocal_sound fr skip r rho a Hc Ha) as (j & x & Hj & Hsk & Hc6 & Hax).
  pose proof (nth_error_In _ _ Hj) as Hinx.
  pose proof (proj1 (Forall_forall _ _) (proj1 HFR) x Hinx) as (X1 & _ & _).
  destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & _ & HFrl).
  destruct (HFrl _ _ X1) as (_ & _ & _ & F4 & F5 & _). top_rng F5.
  destruct Hax as [Hax|Hax]; [|exfalso; unfold frv in F5, Hax; cbn [fst snd] in F5, Hax; pose proof (fs_frame_size_bounds' _ Hc6); lia].
  left. right; right; right. exists (fst (frv rho x)), (snd (frv rho x)), (uval rho (snd x)). split; [|exact Hax].
  apply In_FFx. right. exists x. split; [|reflexivity].
  subst frs. destruct skip as [i|]; [|exact Hinx]. eapply In_remove_nth_ne; [exact Hj | intros ->; apply Hsk; reflexivity].
Qed.

End Sum.
End WithSegs.
