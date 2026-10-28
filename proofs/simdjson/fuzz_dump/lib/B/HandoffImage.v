(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import SrzEqv HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanPlanImagesB.
From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hi_fx : PropExec.FPState := PropExec.fx0.

Definition USP_OFF : Z := 48.

Definition hs_regs_ok (ch : acs) : bool :=
  (expr_eqb (reg ch 1) (ELit MAIN_RA) && expr_eqb (reg ch 4) (ELit TP_A) && expr_eqb (reg ch 10) (EVar V_ARGC)
   && expr_eqb (reg ch 11) (eaddz e_sp0 8) && expr_eqb (reg ch 2) (eaddz e_sp0 (- USP_OFF))
   && Z.leb 4 (ealign (kn ch) e_sp0))%bool.

Section Regs.
Variables (SEGS : list Segment) (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok SEGS A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Hypothesis HR : hs_regs_ok ch = true.

#[local] Notation sp0 := (bv_unsigned (vm_init_sp (m_vmmaps model))).

Lemma hi_sp0 : sp0 = uE E e_sp0 /\ sp_window_lo <= sp0 <= sp_window_hi.
Proof. eapply APS.cs_isp. exact HC. Unshelve. all: try exact (fun _ => None); try exact (fun _ _ _ => None). Qed.

Lemma hi_reg : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg ch n).
Proof. intros n Hn. eapply APS.reg_sound; [exact HC | exact Hn]. Unshelve. all: try exact (fun _ => None); try exact (fun _ _ _ => None). Qed.

Lemma hi_regs :
  getr R (Z_to_bv 5 1) = Z_to_bv 64 MAIN_RA /\ getr R (Z_to_bv 5 4) = Z_to_bv 64 TP_A
  /\ getr R (Z_to_bv 5 10) = ev E V_ARGC
  /\ getr R (Z_to_bv 5 11) = Z_to_bv 64 (sp0 + 8) /\ getr R (Z_to_bv 5 2) = Z_to_bv 64 (sp0 - USP_OFF).
Proof.
  unfold hs_regs_ok in HR.
  repeat match type of HR with (_ && _)%bool = true => apply andb_prop in HR as [HR ?X] end.
  match goal with H1 : expr_eqb (reg ch 1) _ = true, H4 : expr_eqb (reg ch 4) _ = true, H10 : expr_eqb (reg ch 10) _ = true,
                  H11 : expr_eqb (reg ch 11) _ = true, H2 : expr_eqb (reg ch 2) _ = true |- _ =>
    apply expr_eqb_eq in H1; apply expr_eqb_eq in H4; apply expr_eqb_eq in H10; apply expr_eqb_eq in H11; apply expr_eqb_eq in H2;
    rename H1 into E1; rename H4 into E4; rename H10 into E10; rename H11 into E11; rename H2 into E2 end.
  destruct hi_sp0 as [Hsp [Hlo Hhi]]. unfold sp_window_lo, sp_window_hi in *.
  pose proof (hi_reg 1 ltac:(lia)) as G1. pose proof (hi_reg 4 ltac:(lia)) as G4. pose proof (hi_reg 10 ltac:(lia)) as G10.
  pose proof (hi_reg 11 ltac:(lia)) as G11. pose proof (hi_reg 2 ltac:(lia)) as G2.
  rewrite E1 in G1. rewrite E4 in G4. rewrite E10 in G10. rewrite E11 in G11. rewrite E2 in G2.
  change (Z.of_nat 1) with 1 in G1. change (Z.of_nat 4) with 4 in G4. change (Z.of_nat 10) with 10 in G10.
  change (Z.of_nat 11) with 11 in G11. change (Z.of_nat 2) with 2 in G2.
  split; [rewrite G1; apply edenot_lit|]. split; [rewrite G4; apply edenot_lit|]. split; [rewrite G10; reflexivity|].
  split.
  - rewrite G11. unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64, u_lit64. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus, two64. cbn [Z.of_N]. fold (uE E e_sp0). rewrite <- Hsp. rewrite Zplus_mod_idemp_r. reflexivity.
  - rewrite G2. unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64, u_lit64. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus, two64. cbn [Z.of_N]. fold (uE E e_sp0). rewrite <- Hsp. rewrite Zplus_mod_idemp_r.
    replace (sp0 + - USP_OFF) with (sp0 - USP_OFF) by lia. reflexivity.
Qed.

Lemma hi_usp : (sp0 - USP_OFF) mod 16 = 0 /\ sp0 - USP_OFF < sp0 + 8 /\ sp0 - STACK_WIN + 0x100000 <= sp0 - USP_OFF
               /\ sp0 - USP_OFF <= sp0 /\ 0x7fff80000000 <= sp0.
Proof.
  destruct hi_sp0 as [Hsp [Hlo Hhi]]. unfold sp_window_lo, sp_window_hi in *.
  unfold hs_regs_ok in HR. apply andb_prop in HR as [_ Hal]. apply Z.leb_le in Hal.
  pose proof (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (ealign_sound SEGS E _ (kn ch) e_sp0 HK) as [EA ED].
  assert (D4 : (2 ^ 4 | 2 ^ ealign (kn ch) e_sp0)) by (exists (2 ^ (ealign (kn ch) e_sp0 - 4)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  destruct (Z.divide_trans _ _ _ D4 ED) as [q Hq]. fold (uE E e_sp0) in Hq. rewrite <- Hsp in Hq.
  unfold USP_OFF, STACK_WIN. change (2 ^ 4) with 16 in Hq.
  split; [rewrite Hq; replace (q * 16 - 48) with ((q - 3) * 16) by lia; apply Z.mod_mul; lia|]. lia.
Qed.

End Regs.

Fixpoint kimg_at (k : list kentry) (cur : Z) : option Z :=
  match k with
  | [] => None
  | KImg lo hi :: r => if (Z.leb lo cur && Z.ltb cur hi)%bool then Some hi else kimg_at r cur
  | _ :: r => kimg_at r cur
  end.

Fixpoint kimg_cover (k : list kentry) (cur hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb hi cur then true else
           match kimg_at k cur with Some h => kimg_cover k h hi f | None => false end
  end.

Lemma kimg_at_sound : forall k cur h, kimg_at k cur = Some h -> exists lo, In (KImg lo h) k /\ lo <= cur < h.
Proof.
  induction k as [|K r IH]; intros cur h H; [discriminate|].
  destruct K; cbn [kimg_at] in H; try (destruct (IH _ _ H) as (lo0 & Hin & Hr); exists lo0; split; [right; exact Hin| exact Hr]).
  destruct ((lo <=? cur) && (cur <? hi))%bool eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    exists lo. split; [left; reflexivity| lia].
  - destruct (IH _ _ H) as (lo' & Hin & Hr). exists lo'. split; [right; exact Hin| exact Hr].
Qed.

Lemma kimg_cover_sound : forall f k cur hi, kimg_cover k cur hi f = true ->
  forall i, cur <= i < hi -> exists lo h, In (KImg lo h) k /\ lo <= i < h.
Proof.
  induction f as [|f IH]; intros k cur hi H i Hi; cbn [kimg_cover] in H; [discriminate|].
  destruct (Z.leb_spec0 hi cur); [lia|].
  destruct (kimg_at k cur) as [h|] eqn:Hk; [|discriminate].
  destruct (kimg_at_sound _ _ _ Hk) as (lo & Hin & Hr).
  destruct (Z.ltb_spec0 i h).
  - exists lo, h. split; [exact Hin| lia].
  - exact (IH k h hi H i ltac:(lia)).
Qed.

Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).

Lemma find_segment_in : forall segs a n s, find_segment segs a n = Some s -> In s segs /\ seg_lo s <= a /\ a + n <= seg_hi s.
Proof.
  induction segs as [|s0 r IH]; intros a n s H; cbn [find_segment] in H; [discriminate|].
  destruct ((Z.of_N (seg_base s0) <=? a) && (a + n <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. unfold seg_lo, seg_hi. lia.
  - destruct (IH _ _ _ H) as (Hin & Hr). split; [right; exact Hin| exact Hr].
Qed.

Definition hs_ro_ok (SEGS : list Segment) (ch : acs) : bool :=
  forallb (fun s => seg_writable s || kimg_cover (kn ch) (seg_lo s) (seg_hi s) (S (length (kn ch)))) SEGS.

Section MemInv.
Variables (SEGS : list Segment) (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok SEGS A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.
Hypothesis HRO : hs_ro_ok SEGS ch = true.

Theorem hi_mem_inv : mem_inv SEGS (mH FULL model A').
Proof.
  pose proof HULL_ok as (H0 & H1 & H2 & H3). unfold KHI in H3.
  apply mem_inv_intro.
  - intros a Hs. unfold seg_addr in Hs. destruct (find_segment SEGS (bv_unsigned a) 1) eqn:F; [|discriminate].
    destruct (APS.in_hull A (bv_unsigned a)) eqn:Hin.
    + unfold APS.in_hull in Hin. apply andb_prop in Hin as [_ Hin]. apply Z.ltb_lt in Hin. unfold UTOP. lia.
    + rewrite (SEGS_in_hull a Hin) in F. discriminate.
  - intros a b Hm. unfold mH, mrestrict in Hm. destruct (HID A' model a) eqn:Hh; [discriminate|].
    assert (Hlt : bv_unsigned a < 2 ^ 47).
    { unfold HID in Hh. apply orb_false_iff in Hh as [_ Hh]. apply Z.leb_gt in Hh. exact Hh. }
    split; [|unfold UTOP; lia].
    unfold ro_addr. destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:F; [|reflexivity].
    destruct (seg_writable seg) eqn:W; [reflexivity|]. exfalso.
    destruct (find_segment_in _ _ _ _ F) as (Hin & Hr1 & Hr2).
    unfold hs_ro_ok in HRO. rewrite forallb_forall in HRO. specialize (HRO seg Hin). rewrite W in HRO. cbn [orb] in HRO.
    destruct (kimg_cover_sound _ _ _ _ HRO (bv_unsigned a) ltac:(lia)) as (lo & h & Hk & Hr).
    pose proof (hk_kimg SEGS A nx0 LIMIT SINV argH FS0 E ch R FULL model HC lo h Hk (bv_unsigned a) Hr) as HN.
    rewrite (Z_to_bv_bv_unsigned a) in HN.
    destruct (APS.in_hull A (bv_unsigned a)) eqn:Hin2; [| rewrite (SEGS_in_hull a Hin2) in F; discriminate].
    destruct (hk_hull SEGS A nx0 LIMIT SINV argH FS0 HULL_ok argH_high E ch R FULL model HC A' HA' a Hin2) as [E1 E2].
    rewrite E2, Hm in HN. discriminate.
Qed.

End MemInv.

Fixpoint kwr_at (k : list kentry) (b : expr) (cur : Z) : option Z :=
  match k with
  | [] => None
  | KWr (SA b' o) (ELit n) :: r =>
      if (expr_eqb b' b && Z.leb 0 n && Z.ltb n (2 ^ 64) && Z.leb o cur && Z.ltb cur (o + n))%bool then Some (o + n)
      else kwr_at r b cur
  | _ :: r => kwr_at r b cur
  end.

Fixpoint kwr_cover (k : list kentry) (b : expr) (cur hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb hi cur then true else
           match kwr_at k b cur with Some h => kwr_cover k b h hi f | None => false end
  end.

Lemma kwr_at_sound : forall k b cur h, kwr_at k b cur = Some h ->
  exists o n, In (KWr (SA b o) (ELit n)) k /\ 0 <= n < 2 ^ 64 /\ o <= cur < h /\ h = o + n.
Proof.
  induction k as [|K r IH]; intros b cur h H; [discriminate|].
  assert (Hr : kwr_at r b cur = Some h ->
               exists o n, In (KWr (SA b o) (ELit n)) (K :: r) /\ 0 <= n < 2 ^ 64 /\ o <= cur < h /\ h = o + n).
  { intros H'. destruct (IH _ _ _ H') as (o & n & Hin & Hn & Hc & Hh). exists o, n. split; [right; exact Hin| auto]. }
  destruct K; cbn [kwr_at] in H; try exact (Hr H).
  destruct a as [b' o]. destruct n as [z| | | | | | |]; cbn [kwr_at] in H; try exact (Hr H).
  destruct (expr_eqb b' b && (0 <=? z) && (z <? 2 ^ 64) && (o <=? cur) && (cur <? o + z))%bool eqn:E; [|exact (Hr H)].
  injection H as <-.
  repeat match type of E with (_ && _)%bool = true => apply andb_prop in E as [E ?X] end.
  match goal with H1 : (0 <=? z) = true, H2 : (z <? 2 ^ 64) = true, H3 : (o <=? cur) = true, H4 : (cur <? o + z) = true |- _ =>
    apply Z.leb_le in H1; apply Z.ltb_lt in H2; apply Z.leb_le in H3; apply Z.ltb_lt in H4 end.
  apply expr_eqb_eq in E. subst b'.
  exists o, z. split; [left; reflexivity| lia].
Qed.

Lemma kwr_cover_sound : forall f k b cur hi, kwr_cover k b cur hi f = true ->
  forall i, cur <= i < hi -> exists o n, In (KWr (SA b o) (ELit n)) k /\ 0 <= n < 2 ^ 64 /\ o <= i < o + n.
Proof.
  induction f as [|f IH]; intros k b cur hi H i Hi; cbn [kwr_cover] in H; [discriminate|].
  destruct (Z.leb_spec0 hi cur); [lia|].
  destruct (kwr_at k b cur) as [h|] eqn:Hk; [|discriminate].
  destruct (kwr_at_sound _ _ _ _ Hk) as (o & nn & Hin & Hn & Hr & ->).
  destruct (Z.ltb_spec0 i (o + nn)).
  - exists o, nn. split; [exact Hin| lia].
  - exact (IH k b (o + nn) hi H i ltac:(lia)).
Qed.

Definition hs_stk_ok (ch : acs) : bool := kwr_cover (kn ch) e_sp0 (-8388608) (- USP_OFF) (S (length (kn ch))).

Lemma rdn1_mrd : forall segs m a b, L_rdn segs m a 1 = Some [b] -> mrd segs m a = Some b.
Proof.
  intros segs m a b H. rewrite rdn_unfold in H. cbv beta iota in H.
  destruct (mrd segs m a) as [b'|]; [|discriminate]. cbn in H. injection H as <-. reflexivity.
Qed.

Section Stack.
Variables (SEGS : list Segment) (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok SEGS A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation MR := (APS.Mr A argH E ch model FULL).
#[local] Notation sp0 := (bv_unsigned (vm_init_sp (m_vmmaps model))).

Lemma hi_wr_byte : forall b o n i, In (KWr (SA b o) (ELit n)) (kn ch) -> 0 <= n < 2 ^ 64 -> o <= i < o + n ->
  wview SEGS MR (Z_to_bv 64 (uE E b + i)) <> None /\ 0 <= uE E b + i < 2 ^ 64.
Proof.
  intros b o n i Hin Hn Hi.
  destruct (hk_kentry SEGS A nx0 LIMIT SINV argH FS0 E ch R FULL model HC _ Hin) as [Hfl Hst].
  rewrite (APS.elenZ_lit E n Hn) in Hfl, Hst.
  specialize (Hst (i - o) 1%nat ltac:(lia) ltac:(lia)).
  unfold flat, estart in Hfl. cbn [a_base a_off] in Hfl.
  unfold estart in Hst. cbn [a_base a_off] in Hst.
  replace (bv_unsigned (edenot E b) + o + (i - o)) with (uE E b + i) in Hst by (unfold uE; lia).
  assert (Hr : 0 <= uE E b + i < 2 ^ 64) by (unfold uE; lia).
  split; [|exact Hr].
  pose proof (store_ok_wview SEGS _ _ 1 0 Hst ltac:(lia)) as W.
  rewrite Z_to_bv_unsigned, bv_wrap_small in W by (unfold bv_modulus; cbn; lia).
  change (Z.of_nat 0) with 0 in W. rewrite Z.add_0_r in W. exact W.
Qed.

Theorem hi_stk : hs_stk_ok ch = true -> stk SEGS (mH FULL model A') (sp0 - 8388608) (sp0 - USP_OFF).
Proof.
  intros H. destruct (APS.cs_isp SEGS A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) as [Hsp [Hlo Hhi]].
  pose proof HULL_ok as (H0 & H1 & H2 & H3). unfold KHI in H3. unfold sp_window_lo, sp_window_hi in *. unfold USP_OFF.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (kwr_cover_sound _ _ _ _ _ H (a - sp0) ltac:(unfold USP_OFF; lia)) as (o & n & Hin & Hn & Hi).
  destruct (hi_wr_byte e_sp0 o n (a - sp0) Hin Hn Hi) as [W Hr].
  unfold APS.uE in Hsp. unfold AX2S.uE in W, Hr. rewrite <- Hsp in W, Hr. replace (sp0 + (a - sp0)) with a in W by lia.
  assert (Hnh : APS.in_hull A (bv_unsigned (wa a)) = false).
  { unfold APS.in_hull. rewrite wa_unsigned by lia. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
  pose proof (SEGS_in_hull _ Hnh) as F.
  unfold wview in W. fold (wa a) in W. rewrite F in W.
  destruct (MR (wa a)) as [bb|] eqn:Hm; [|exfalso; apply W; reflexivity].
  rewrite <- (hk_mr_some SEGS A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA' (wa a)) in Hm;
    [| rewrite Hm; discriminate | rewrite wa_unsigned by lia; lia].
  unfold wview, mrd. rewrite Hm. split; [discriminate| exists bb; reflexivity].
Qed.

Definition klit_keep (lo hi : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA (ELit 0) a) w _ => (Z.ltb a hi && Z.ltb lo (a + Z.of_nat w))%bool
  | KZero (SA (ELit 0) a) (ELit n) => (Z.ltb a hi && Z.ltb lo (a + n))%bool
  | KFill (SA (ELit 0) a) (ELit n) _ => (Z.ltb a hi && Z.ltb lo (a + n))%bool
  | KImg l h => (Z.ltb l hi && Z.ltb lo h)%bool
  | _ => false
  end.
Definition klit_cut (lo hi : Z) (k : list kentry) : list kentry := List.filter (klit_keep lo hi) k.

Lemma know_ok_filter : forall segs E0 M0 (f : kentry -> bool) k, know_ok segs E0 M0 k -> know_ok segs E0 M0 (List.filter f k).
Proof.
  intros segs E0 M0 f k H. unfold know_ok in *. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _].
  exact (proj1 (Forall_forall _ _) H x Hx).
Qed.

Theorem hi_lit_k : forall k a n zs, know_ok SEGS E MR k -> AP.hs_table SEGS k a n = Some zs -> 0 <= a -> 0 <= n -> a + n <= 2 ^ 47 ->
  bytes_at SEGS (mH FULL model A') a (map (Z_to_bv 8) zs).
Proof.
  intros k a n zs HK H Ha Hn Hlt.
  destruct (APSX.hs_table_sound SEGS E MR k a n zs HK H Ha Hn ltac:(lia)) as (Hlen & _ & Hrd).
  apply (hk_bytes_at SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA');
    [rewrite length_map, Hlen; lia|].
  split; [lia|]. split; [rewrite length_map, Hlen; lia|].
  intros i Hi. rewrite length_map, Hlen in Hi.
  specialize (Hrd (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in Hrd.
  rewrite rdn_AS_Lib in Hrd. apply rdn1_mrd in Hrd. unfold wa. rewrite Hrd.
  rewrite nth_error_map, (nth_error_nth' zs 0) by lia. reflexivity.
Qed.

Theorem hi_lit : forall a n zs, AP.hs_table SEGS (kn ch) a n = Some zs -> 0 <= a -> 0 <= n -> a + n <= 2 ^ 47 ->
  bytes_at SEGS (mH FULL model A') a (map (Z_to_bv 8) zs).
Proof. intros a n zs. apply hi_lit_k. exact (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Theorem hi_lit_cut : forall lo hi a n zs, AP.hs_table SEGS (klit_cut lo hi (kn ch)) a n = Some zs -> 0 <= a -> 0 <= n -> a + n <= 2 ^ 47 ->
  bytes_at SEGS (mH FULL model A') a (map (Z_to_bv 8) zs).
Proof. intros lo hi a n zs. apply hi_lit_k. apply know_ok_filter. exact (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

End Stack.

Definition seg_rw_byte (SEGS : list Segment) (z : Z) : bool :=
  match find_segment SEGS z 1 with
  | Some s => (seg_writable s && seg_readable s &&
               match segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s))) with Some _ => true | None => false end)%bool
  | None => false
  end.

Fixpoint seg_rw_go (SEGS : list Segment) (a : Z) (fuel : nat) : bool :=
  match fuel with O => true | S f => (seg_rw_byte SEGS a && seg_rw_go SEGS (a + 1) f)%bool end.
Definition seg_rw_ok (SEGS : list Segment) (a n : Z) : bool :=
  (Z.leb 0 a && Z.leb 0 n && Z.leb (a + n) (2 ^ 64) && seg_rw_go SEGS a (Z.to_nat n))%bool.

Lemma seg_rw_go_sound : forall SEGS f a, seg_rw_go SEGS a f = true -> forall i, 0 <= i < Z.of_nat f -> seg_rw_byte SEGS (a + i) = true.
Proof.
  induction f as [|f IH]; intros a H i Hi; [lia|]. cbn [seg_rw_go] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r; exact H1|].
  replace (a + i) with ((a + 1) + (i - 1)) by lia. apply (IH _ H2). lia.
Qed.

Lemma seg_rw_byte_sound : forall SEGS m z, 0 <= z < 2 ^ 64 -> seg_rw_byte SEGS z = true ->
  wview SEGS m (wa z) <> None /\ exists b, mrd SEGS m (wa z) = Some b.
Proof.
  intros SEGS m z Hz H. unfold seg_rw_byte in H.
  destruct (find_segment SEGS z 1) as [s|] eqn:F; [|discriminate].
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [Hw Hr].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s)))) as [bb|] eqn:Hby; [|discriminate].
  assert (Hu : bv_unsigned (wa z) = z) by (apply wa_unsigned; exact Hz).
  unfold wview, mrd. destruct (m (wa z)) as [b0|].
  - split; [discriminate| exists b0; reflexivity].
  - match goal with |- context [find_segment SEGS ?x 1] => assert (Ex : x = z) by exact Hu; rewrite Ex end.
    rewrite F, Hw, Hby. split; [discriminate|].
    exists bb. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Common.PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1.
    match goal with |- context [find_segment SEGS ?x 1] => assert (Ex2 : x = z) by exact Hu; rewrite Ex2 end.
    rewrite F, Hr. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Hby. reflexivity.
Qed.

Lemma seg_rw_ok_sound : forall SEGS a n, seg_rw_ok SEGS a n = true -> forall m, wr_at SEGS m a n /\ stk SEGS m a (a + n).
Proof.
  intros SEGS a n H m. unfold seg_rw_ok in H.
  apply andb_prop in H as [H Hall]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  assert (G : forall i, 0 <= i < n -> wview SEGS m (wa (a + i)) <> None /\ exists b, mrd SEGS m (wa (a + i)) = Some b).
  { intros i Hi. apply seg_rw_byte_sound; [lia|]. apply (seg_rw_go_sound _ _ _ Hall). lia. }
  split.
  - split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (G i Hi)).
  - split; [lia|]. split; [lia|]. intros x Hx. replace x with (a + (x - a)) by lia. apply G. lia.
Qed.

Lemma stk_bytes : forall SEGS m a n, stk SEGS m a (a + Z.of_nat n) -> exists bs, length bs = n /\ bytes_at SEGS m a bs.
Proof.
  intros SEGS m a n (H1 & H2 & H).
  exists (map (fun i => match mrd SEGS m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  rewrite length_map, length_seq. split; [reflexivity|].
  split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; lia). rewrite seq_nth by lia. cbn [option_map Nat.add].
  destruct (H (a + Z.of_nat i) ltac:(lia)) as [_ [b Hb]]. rewrite Hb. reflexivity.
Qed.

Lemma cells_c8_of : forall SEGS m a bs, length bs = 8%nat -> bytes_at SEGS m a bs -> exists v, cells_at SEGS m a [C8 v].
Proof.
  intros SEGS m a bs Hl Hb. exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [cbn; tauto|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8.
  pose proof (bytes_le_to_Z_bound bs) as Bd. rewrite Hl in Bd.
  rewrite <- store_bytes_8'. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  rewrite <- Hl at 1. rewrite APS.Z_to_le_bytes_to_Z. exact Hb.
Qed.

Lemma cells_c4_of : forall SEGS m a bs, length bs = 4%nat -> bytes_at SEGS m a bs -> exists v, cells_at SEGS m a [C4 v].
Proof.
  intros SEGS m a bs Hl Hb. exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [cbn; tauto|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4.
  pose proof (bytes_le_to_Z_bound bs) as Bd. rewrite Hl in Bd.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  rewrite <- Hl at 1. rewrite APS.Z_to_le_bytes_to_Z. exact Hb.
Qed.

Lemma cells_c1_of : forall SEGS m a bs, length bs = 1%nat -> bytes_at SEGS m a bs -> exists v, cells_at SEGS m a [C1 v].
Proof.
  intros SEGS m a bs Hl Hb. destruct bs as [|b [|]]; try (cbn in Hl; lia).
  exists b. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. exact Hb.
Qed.

Lemma seg_rw_guard : seg_rw_ok bsegs SSP_GUARD 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_errno : seg_rw_ok bsegs ERRNO_A 4 = true. Proof. vm_compute. reflexivity. Qed.

Lemma hi_seg_rw_byte_win : forall z, 0x168000 <= z < 0x6cd000 -> seg_rw_byte bsegs z = true.
Proof.
  intros z Hz. assert (Hu : bv_unsigned (wa z) = z) by (apply wa_unsigned; lia).
  pose proof (asan_rw_window (fun _ => None) (wa z) ltac:(rewrite Hu; lia)) as W.
  unfold wview in W. change ASEGS with bsegs in W. rewrite Hu in W. cbv beta iota in W. unfold seg_rw_byte.
  destruct (find_segment bsegs z 1) as [s|] eqn:F; [|exfalso; apply W; reflexivity].
  destruct (seg_writable s) eqn:Ew; [|exfalso; apply W; reflexivity].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (z - Z.of_N (seg_base s)))) eqn:Eb; [|exfalso; apply W; reflexivity].
  assert (Er : seg_readable s = true).
  { apply find_segment_some_spec in F as (Hin & _). change bsegs with ASEGS in Hin. rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_readable seg_writable seg_perms string_has Ascii.eqb AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Ew |- *; first [reflexivity | discriminate]. }
  rewrite Er. reflexivity.
Qed.
Lemma hi_seg_rw_go_win : forall f a, 0x168000 <= a -> a + Z.of_nat f <= 0x6cd000 -> seg_rw_go bsegs a f = true.
Proof.
  induction f as [|f IH]; intros a H1 H2; cbn [seg_rw_go]; [reflexivity|].
  rewrite (hi_seg_rw_byte_win a ltac:(lia)), (IH (a + 1) ltac:(lia) ltac:(lia)). reflexivity.
Qed.
Lemma seg_rw_stage : seg_rw_ok bsegs g_read_stage 65536 = true.
Proof.
  unfold seg_rw_ok, g_read_stage. rewrite (hi_seg_rw_go_win (Z.to_nat 65536) 6920080 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)).
  reflexivity.
Qed.
Lemma seg_rw_latch : seg_rw_ok bsegs TR_INIT 1 = true. Proof. vm_compute. reflexivity. Qed.

Theorem hi_clx_statics : forall m : word -> option byte,
  (exists g, ro_cells bsegs m SSP_GUARD [C8 g]) /\ (exists v, rw_cells bsegs m ERRNO_A [C4 v])
  /\ stk bsegs m g_read_stage (g_read_stage + 65536) /\ (exists v, rw_cells bsegs m TR_INIT [C1 v]).
Proof.
  intros m.
  destruct (seg_rw_ok_sound _ _ _ seg_rw_guard m) as [_ Sg].
  destruct (seg_rw_ok_sound _ _ _ seg_rw_errno m) as [We Se].
  destruct (seg_rw_ok_sound _ _ _ seg_rw_stage m) as [_ Ss].
  destruct (seg_rw_ok_sound _ _ _ seg_rw_latch m) as [Wl Sl].
  split; [|split; [|split]].
  - destruct (stk_bytes bsegs m SSP_GUARD 8 Sg) as (bs & Hl & Hb). exact (cells_c8_of _ _ _ _ Hl Hb).
  - destruct (stk_bytes bsegs m ERRNO_A 4 Se) as (bs & Hl & Hb). destruct (cells_c4_of _ _ _ _ Hl Hb) as [v Hv].
    exists v. split; [exact Hv| exact We].
  - exact Ss.
  - destruct (stk_bytes bsegs m TR_INIT 1 Sl) as (bs & Hl & Hb). destruct (cells_c1_of _ _ _ _ Hl Hb) as [v Hv].
    exists v. split; [exact Hv| exact Wl].
Qed.

Fixpoint kw_find (k : list kentry) (b : expr) (off : Z) (w : nat) : option expr :=
  match k with
  | [] => None
  | KWord (SA b' o') w' v :: r => if (expr_eqb b' b && Z.eqb o' off && Nat.eqb w' w)%bool then Some v else kw_find r b off w
  | _ :: r => kw_find r b off w
  end.

Lemma kw_find_in : forall k b off w v, kw_find k b off w = Some v -> In (KWord (SA b off) w v) k.
Proof.
  induction k as [|K r IH]; intros b off w v H; [discriminate|].
  destruct K as [[b' o'] w' v'| | | | | | | | |]; cbn [kw_find] in H; try (right; exact (IH _ _ _ _ H)).
  destruct (expr_eqb b' b && Z.eqb o' off && Nat.eqb w' w)%bool eqn:E; [|right; exact (IH _ _ _ _ H)].
  injection H as <-. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply expr_eqb_eq in E1. apply Z.eqb_eq in E2. apply Nat.eqb_eq in E3. subst. left. reflexivity.
Qed.
