(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocG_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r7af8c_7b250_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatPoisonRun_b BatPoison2G_b Ba0RegionPoisoned_b BatAnnotate_b BatAnnotateU_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
#[local] Abbreviation SB := BatPoison_b.SB.
Ltac lit_cell H :=
  unfold cell in H;
  match type of H with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
    match goal with |- rdn _ _ ?w _ = _ => replace w with (Z_to_bv 64 a : word) by (apply bv_eq; reflexivity); exact H end end.

(* [comment removed for export] *)
Definition annU_plo (u u' : Z) : Z := if u <? u' then u / 8 else (u' + 7) / 8.
Definition annU_phi (u u' : Z) : Z := if u <? u' then u' / 8 else (u + 7) / 8.
Definition annU_pv (u u' : Z) : Z := if u <? u' then 0 else 252.
(* [comment removed for export] *)
Definition annU_lo (u u' : Z) : Z := Z.min u u' / 8.
Definition annU_hi (u u' : Z) : Z := if u =? u' then Z.min u u' / 8 else (Z.max u u' + 7) / 8.
Definition annval (u' j : Z) : Z := if j <? u' / 8 then 0 else if (j =? u' / 8) && negb (u' mod 8 =? 0) then u' mod 8 else 252.

(* [comment removed for export] *)
Definition annU_place (b c : Z) : Prop := b + c <= 0x7fff7000 \/ 0x10007fff8000 <= b.

Lemma annU_div8_facts u : 0 <= u -> u / 8 <= (u + 7) / 8 <= u / 8 + 1 /\ 0 <= u / 8 /\ (u mod 8 = 0 -> (u + 7) / 8 = u / 8) /\ (u mod 8 <> 0 -> (u + 7) / 8 = u / 8 + 1)
  /\ 8 * (u / 8) = RD u /\ 8 * ((u + 7) / 8) = RU u.
Proof.
  intros Hu. pose proof (RD_range u Hu) as (A1 & A2 & A3). pose proof (RU_range u Hu) as (B1 & B2).
  pose proof (RD_eq u) as E1. pose proof (RD_eq (u + 7)) as E2. unfold RU in *.
  pose proof (Z.div_pos u 8 Hu ltac:(lia)) as P.
  assert (C1 : u mod 8 = 0 -> (u + 7) / 8 = u / 8) by (intros H; pose proof (RU_RD_full u H) as X; unfold RU in X; lia).
  assert (C2 : u mod 8 <> 0 -> (u + 7) / 8 = u / 8 + 1) by (intros H; pose proof (RU_RD_partial u Hu H) as X; unfold RU in X; lia).
  destruct (Z.eq_dec (u mod 8) 0) as [E|E]; [pose proof (C1 E)|pose proof (C2 E)]; repeat split; first [assumption | lia].
Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_annU_A : forall regs (M rom : word -> option byte) (b c u u' v : Z),
  getr regs 9 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 (b + u') -> getr regs 19 = Z_to_bv 64 (b + u) -> getr regs 20 = Z_to_bv 64 (b + c) ->
  0 <= b -> b + c < 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> u <> u' -> b mod 8 = 0 ->
  cellA M 0x1374c0 8 0x13fc38 -> cellA M 0x13fc38 8 SB ->
  (c mod 8 <> 0 -> cellA M (SB + (b + c) / 8) 1 v /\ (v = 252 \/ 1 <= v <= c mod 8)) ->
  exists regs', msteps ASEGS (mkst regs (0x7bb94 : word) M rom) (mkst regs' (0x7bbbc : word) M rom)
    /\ getr regs' 10 = Z_to_bv 64 (b + u) /\ getr regs' 11 = Z_to_bv 64 (b + u) /\ getr regs' 19 = Z_to_bv 64 0
    /\ getr regs' 20 = Z_to_bv 64 (b + u) /\ getr regs' 21 = Z_to_bv 64 (b + u')
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 19%bv -> r <> 20%bv -> r <> 21%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b c u u' v H9 H18 H19 H20 Hb Hbc Hu Hu' Ne Hb8 CG CS CV.
  assert (CHK : exists r1, msteps ASEGS (mkst regs (0x7bb94 : word) M rom) (mkst r1 (0x7bba0 : word) M rom)
            /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 21%bv -> getr r1 r = getr regs r)).
  { destruct (Z.eq_dec (c mod 8) 0) as [E|E].
    - destruct (art_annU_chk0 regs M rom b c u u' H18 H19 H20 Hb Hbc Hu Hu' Ne Hb8 E) as (r1 & RUN & K). exists r1. split; [exact RUN|].
      intros r N10 _ _ _. exact (K r N10).
    - destruct (CV E) as (CV' & Hv). exact (art_annU_chkU regs M rom b c u u' v H18 H19 H20 Hb Hbc Hu Hu' Ne Hb8 E CG CS CV' Hv). }
  destruct CHK as (r1 & RUN1 & K1).
  assert (R9 : getr r1 9 = Z_to_bv 64 b) by (rewrite K1 by (intros X; discriminate X); exact H9).
  assert (R18 : getr r1 18 = Z_to_bv 64 (b + u')) by (rewrite K1 by (intros X; discriminate X); exact H18).
  assert (R19 : getr r1 19 = Z_to_bv 64 (b + u)) by (rewrite K1 by (intros X; discriminate X); exact H19).
  destruct (art_annU_mid r1 M rom b u u' R9 R18 R19 ltac:(lia) Hb8) as (r2 & RUN2 & A10 & A11 & A19 & A20 & A21 & K2).
  exists r2. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
  split; [exact A10|]. split; [exact A11|]. split; [exact A19|]. split; [exact A20|]. split; [exact A21|].
  intros r N10 N11 N12 N19 N20 N21. rewrite (K2 r N10 N11 N19 N20 N21). exact (K1 r N10 N11 N12 N21).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_annU_B : forall regs (M rom : word -> option byte) (sp b c u u' : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 (b + u) -> getr regs 11 = Z_to_bv 64 (b + u) -> getr regs 20 = Z_to_bv 64 (b + u) ->
  getr regs 21 = Z_to_bv 64 (b + u') ->
  4096 <= b -> b + c + 8 <= 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> u <> u' -> b mod 8 = 0 -> annU_place b c ->
  0x10007fff8000 + 64 <= sp -> sp < 2 ^ 63 -> wrA M (sp - 64) 64 -> art_layout M ->
  wrA M (SB + b / 8 + annU_plo u u') (annU_phi u u' - annU_plo u u') ->
  exists regs' M', msteps ASEGS (mkst regs (0x7bbbc : word) M rom) (mkst regs' (0x7bcc4 : word) M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 9 = Z_to_bv 64 (b + RD u') /\ getr regs' 18 = Z_to_bv 64 (b + RU u') /\ getr regs' 21 = Z_to_bv 64 (b + u')
    /\ getr regs' 8 = getr regs 8
    /\ (forall r : reg, art_ann_kept r -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (sp - 64 <= U x < sp) -> ~ (SB + b / 8 + annU_plo u u' <= U x < SB + b / 8 + annU_phi u u') -> M' x = M x)
    /\ (forall j, annU_plo u u' <= j < annU_phi u u' -> M' (Z_to_bv 64 (SB + b / 8 + j)) = Some (Z_to_bv 8 (annU_pv u u'))).
Proof.
  intros regs M rom sp b c u u' H2 H10 H11 H20 H21 Hb Hbc Hu Hu' Ne Hb8 PL Hsp Hsp' W L Wsh.
  pose proof (annU_div8_facts u ltac:(lia)) as (Du1 & Du2 & Du3 & Du4 & Du5 & Du6).
  pose proof (annU_div8_facts u' ltac:(lia)) as (Dv1 & Dv2 & Dv3 & Dv4 & Dv5 & Dv6).
  pose proof (RD_range u ltac:(lia)) as (R1 & R2 & R3). pose proof (RD_range u' ltac:(lia)) as (Q1 & Q2 & Q3).
  pose proof (RU_range u ltac:(lia)) as (P3 & P4). pose proof (RU_range u' ltac:(lia)) as (P1 & P2).
  assert (Hbd : b = 8 * (b / 8)) by (pose proof (Z.div_mod b 8 ltac:(lia)); lia).
  assert (RG : forall r : reg, 0 <= U (getr regs r) < 2 ^ 64) by (intros r; apply bv_unsigned_in_range).
  unfold BatPoison_b.SB in *.
  destruct (Z_lt_le_dec u u') as [Lt|Ge].
  - (* [comment removed for export] *)
    assert (Eplo : annU_plo u u' = u / 8) by (unfold annU_plo; rewrite (proj2 (Z.ltb_lt u u') Lt); reflexivity).
    assert (Ephi : annU_phi u u' = u' / 8) by (unfold annU_phi; rewrite (proj2 (Z.ltb_lt u u') Lt); reflexivity).
    assert (Epv : annU_pv u u' = 0) by (unfold annU_pv; rewrite (proj2 (Z.ltb_lt u u') Lt); reflexivity).
    rewrite Eplo, Ephi, Epv in *.
    destruct (Z_lt_le_dec (RD u) (RD u')) as [Pz|Dz].
    + destruct (art_annU_grow_p regs M rom b c u u' H10 H11 H20 H21 ltac:(lia) ltac:(lia) Hu Hu' Hb8 Lt Pz) as (r1 & RUN1 & A1 & A10 & A11 & A12 & A9 & A18 & K1).
      assert (A2 : getr r1 2 = Z_to_bv 64 sp) by (rewrite K1 by (intros X; discriminate X); exact H2).
      assert (PLC : art_poison_lo_okG (b + RD u) (RD u' - RD u) \/ art_poison_hi_okG (b + RD u) (RD u' - RD u)).
      { clear - PL Hb Hbc Hu Hu' R1 R3 Q1 Q3 Pz Du5 Dv5. destruct PL as [Lo|Hi]; [left; unfold art_poison_lo_okG, BatPoison_b.SB|right; unfold art_poison_hi_okG, kHighMemBeg, kHighMemEnd]; lia. }
      assert (Ep8 : (b + RD u) / 8 = b / 8 + u / 8) by (rewrite Hbd at 1; rewrite <- Du5, <- Z.mul_add_distr_l, Z.mul_comm, Z.div_mul by lia; reflexivity).
      assert (En8 : (RD u' - RD u) / 8 = u' / 8 - u / 8) by (rewrite <- Du5, <- Dv5, <- Z.mul_sub_distr_l, Z.mul_comm, Z.div_mul by lia; reflexivity).
      destruct (art_poison_runG r1 M rom (Z_to_bv 64 0x7bcc4) sp (b + RD u) (RD u' - RD u) 0 A1 art_ann_ret_7b8ac A2 A10 A11 A12 ltac:(lia) ltac:(lia) W
                 ltac:(unfold apart; lia) ltac:(unfold apart; lia) L PLC ltac:(rewrite Z.add_mod, Hb8, R2 by lia; reflexivity) ltac:(rewrite Zminus_mod, R2, Q2 by lia; reflexivity)
                 ltac:(lia) ltac:(lia) ltac:(intros _; rewrite En8; lia) ltac:(rewrite Ep8, En8; unfold BatPoison_b.SB; rewrite Z.add_assoc; exact Wsh))
        as (r2 & RUN2 & B10 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & BK).
      rewrite Ep8, En8 in RUN2. unfold BatPoison_b.SB in RUN2, B10.
      eexists r2, _. split; [eapply msteps_trans; [exact RUN1|]; replace (0x7bcc4%bv : word) with (Z_to_bv 64 0x7bcc4 : word) by (apply bv_eq; vm_compute; reflexivity); exact RUN2|].
      split; [exact B2|]. split; [rewrite B9; exact A9|]. split; [rewrite B18; exact A18|]. split; [rewrite B21, K1 by (intros X; discriminate X); exact H21|].
      split; [rewrite B8; apply K1; intros X; discriminate X|].
      split. { intros r Hr. rewrite (BK r (art_ann_kept_poison r Hr)). apply K1; unfold art_ann_kept in Hr; clear - Hr;
               destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; intros X; discriminate X. }
      split. { eapply mem_grows_trans; [apply art_pf_grows|apply Wf_grows]. }
      split. { intros x Hx Hy. rewrite Wf_outside by (try rewrite Z2Nat.id by lia; lia). unfold art_poison_frame. rewrite !Wn_outside by (cbn; lia). reflexivity. }
      intros j Hj. replace (2147450880 + b / 8 + j) with (2147450880 + (b / 8 + u / 8) + (j - u / 8)) by lia. apply Wf_inside; [lia|rewrite Z2Nat.id by lia; lia|rewrite Z2Nat.id by lia; lia].
    + assert (Ed : RD u = RD u') by (pose proof (RD_mono u u' ltac:(lia)); lia).
      destruct (art_annU_grow_d regs M rom b c u u' H10 H11 H20 H21 ltac:(lia) ltac:(lia) Hu Hu' Hb8 Lt Ed) as (r1 & RUN1 & A9 & A18 & K1).
      exists r1, M. split; [exact RUN1|].
      split; [rewrite K1 by (intros X; discriminate X); exact H2|]. split; [exact A9|]. split; [exact A18|]. split; [rewrite K1 by (intros X; discriminate X); exact H21|].
      split; [apply K1; intros X; discriminate X|].
      split. { intros r Hr. apply K1; unfold art_ann_kept in Hr; clear - Hr; destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; intros X; discriminate X. }
      split; [apply mem_grows_refl|]. split; [intros; reflexivity|].
      intros j Hj. exfalso. clear - Hj Ed Du5 Dv5. lia.
  - (* [comment removed for export] *)
    assert (Gt : u' < u) by lia.
    assert (Eplo : annU_plo u u' = (u' + 7) / 8) by (unfold annU_plo; rewrite (proj2 (Z.ltb_ge u u') Ge); reflexivity).
    assert (Ephi : annU_phi u u' = (u + 7) / 8) by (unfold annU_phi; rewrite (proj2 (Z.ltb_ge u u') Ge); reflexivity).
    assert (Epv : annU_pv u u' = 252) by (unfold annU_pv; rewrite (proj2 (Z.ltb_ge u u') Ge); reflexivity).
    rewrite Eplo, Ephi, Epv in *.
    destruct (Z_lt_le_dec (RU u') (RU u)) as [Pz|Dz].
    + destruct (art_annU_shr_p regs M rom b c u u' H10 H11 H20 H21 ltac:(lia) ltac:(lia) Hu Hu' Hb8 Gt Pz) as (r1 & RUN1 & A1 & A10 & A11 & A12 & A9 & A18 & K1).
      assert (A2 : getr r1 2 = Z_to_bv 64 sp) by (rewrite K1 by (intros X; discriminate X); exact H2).
      assert (PLC : art_poison_lo_okG (b + RU u') (RU u - RU u') \/ art_poison_hi_okG (b + RU u') (RU u - RU u')).
      { clear - PL Hb Hbc Hu Hu' P1 P3 Pz Du6 Dv6. destruct PL as [Lo|Hi]; [left; unfold art_poison_lo_okG, BatPoison_b.SB|right; unfold art_poison_hi_okG, kHighMemBeg, kHighMemEnd]; lia. }
      assert (Ep8 : (b + RU u') / 8 = b / 8 + (u' + 7) / 8) by (rewrite Hbd at 1; rewrite <- Dv6, <- Z.mul_add_distr_l, Z.mul_comm, Z.div_mul by lia; reflexivity).
      assert (En8 : (RU u - RU u') / 8 = (u + 7) / 8 - (u' + 7) / 8) by (rewrite <- Du6, <- Dv6, <- Z.mul_sub_distr_l, Z.mul_comm, Z.div_mul by lia; reflexivity).
      destruct (art_poison_runG r1 M rom (Z_to_bv 64 0x7bcc4) sp (b + RU u') (RU u - RU u') 252 A1 art_ann_ret_7b8ac A2 A10 A11 A12 ltac:(lia) ltac:(lia) W
                 ltac:(unfold apart; lia) ltac:(unfold apart; lia) L PLC ltac:(rewrite Z.add_mod, Hb8, P2 by lia; reflexivity) ltac:(rewrite Zminus_mod, P2, P4 by lia; reflexivity)
                 ltac:(lia) ltac:(lia) ltac:(intros X; discriminate X) ltac:(rewrite Ep8, En8; unfold BatPoison_b.SB; rewrite Z.add_assoc; exact Wsh))
        as (r2 & RUN2 & B10 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & BK).
      rewrite Ep8, En8 in RUN2. unfold BatPoison_b.SB in RUN2, B10.
      eexists r2, _. split; [eapply msteps_trans; [exact RUN1|]; replace (0x7bcc4%bv : word) with (Z_to_bv 64 0x7bcc4 : word) by (apply bv_eq; vm_compute; reflexivity); exact RUN2|].
      split; [exact B2|]. split; [rewrite B9; exact A9|]. split; [rewrite B18; exact A18|]. split; [rewrite B21, K1 by (intros X; discriminate X); exact H21|].
      split; [rewrite B8; apply K1; intros X; discriminate X|].
      split. { intros r Hr. rewrite (BK r (art_ann_kept_poison r Hr)). apply K1; unfold art_ann_kept in Hr; clear - Hr;
               destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; intros X; discriminate X. }
      split. { eapply mem_grows_trans; [apply art_pf_grows|apply Wf_grows]. }
      split. { intros x Hx Hy. rewrite Wf_outside by (try rewrite Z2Nat.id by lia; lia). unfold art_poison_frame. rewrite !Wn_outside by (cbn; lia). reflexivity. }
      intros j Hj. replace (2147450880 + b / 8 + j) with (2147450880 + (b / 8 + (u' + 7) / 8) + (j - (u' + 7) / 8)) by lia. apply Wf_inside; [lia|rewrite Z2Nat.id by lia; lia|rewrite Z2Nat.id by lia; lia].
    + destruct (art_annU_shr_d regs M rom b c u u' H10 H11 H20 H21 ltac:(lia) ltac:(lia) Hu Hu' Hb8 Gt Dz) as (r1 & RUN1 & A9 & A18 & K1).
      assert (Ed : RU u = RU u') by (pose proof (RD_mono (u' + 7) (u + 7) ltac:(lia)) as X; unfold RU in *; lia).
      exists r1, M. split; [exact RUN1|].
      split; [rewrite K1 by (intros X; discriminate X); exact H2|]. split; [exact A9|]. split; [exact A18|]. split; [rewrite K1 by (intros X; discriminate X); exact H21|].
      split; [apply K1; intros X; discriminate X|].
      split. { intros r Hr. apply K1; unfold art_ann_kept in Hr; clear - Hr; destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; intros X; discriminate X. }
      split; [apply mem_grows_refl|]. split; [intros; reflexivity|].
      intros j Hj. exfalso. clear - Hj Ed Du6 Dv6. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_annU_C : forall regs (M rom : word -> option byte) (b c u' : Z),
  getr regs 9 = Z_to_bv 64 (b + RD u') -> getr regs 18 = Z_to_bv 64 (b + RU u') -> getr regs 21 = Z_to_bv 64 (b + u') ->
  4096 <= b -> b + c + 8 <= 2 ^ 47 -> 0 <= u' <= c -> b mod 8 = 0 -> annU_place b c ->
  art_layout M -> (u' mod 8 <> 0 -> wrA M (SB + b / 8 + u' / 8) 1) ->
  exists regs' M', msteps ASEGS (mkst regs (0x7bcc4 : word) M rom) (mkst regs' (0x7bce4 : word) M' rom)
    /\ getr regs' 2 = getr regs 2
    /\ (forall r : reg, In r callee_saved -> r <> 1%bv -> r <> 18%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (u' mod 8 <> 0 /\ U x = SB + b / 8 + u' / 8) -> M' x = M x)
    /\ (u' mod 8 <> 0 -> M' (Z_to_bv 64 (SB + b / 8 + u' / 8)) = Some (Z_to_bv 8 (u' mod 8))).
Proof.
  intros regs M rom b c u' H9 H18 H21 Hb Hbc Hu' Hb8 PL L W.
  pose proof (annU_div8_facts u' ltac:(lia)) as (Dv1 & Dv2 & Dv3 & Dv4 & Dv5 & Dv6). pose proof (RD_range u' ltac:(lia)) as (Q1 & Q2 & Q3).
  assert (Hbd : b = 8 * (b / 8)) by (pose proof (Z.div_mod b 8 ltac:(lia)); lia).
  assert (Ep8 : (b + RD u') / 8 = b / 8 + u' / 8) by (rewrite Hbd at 1; rewrite <- Dv5, <- Z.mul_add_distr_l, Z.mul_comm, Z.div_mul by lia; reflexivity).
  unfold BatPoison_b.SB in *.
  destruct (Z.eq_dec (u' mod 8) 0) as [E|E].
  - exists regs, M. split; [exact (art_annU_tail_a regs M rom b u' H9 H18 E)|].
    split; [reflexivity|]. split; [intros; reflexivity|]. split; [apply mem_grows_refl|]. split; [intros; reflexivity|]. intros X. exfalso. exact (X E).
  - assert (GL : rt_layout_globs M).
    { destruct L as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs.
      repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
    assert (HA : in_app (b + RD u')) by (clear - PL Hb Hbc Hu' Q1 Q3; unfold in_app, LOWEND, HIGHBEG, HIGHEND; destruct PL as [Lo|Hi]; [left|right]; lia).
    destruct (art_annU_tail_u regs M rom b c u' H9 H18 H21 ltac:(lia) ltac:(lia) Hu' Hb8 E GL HA ltac:(unfold BatPoison_b.SB; rewrite Ep8, Z.add_assoc; exact (W E))) as (r1 & RUN1 & A2 & K1).
    rewrite Ep8 in RUN1. unfold BatPoison_b.SB in RUN1. rewrite Z.add_assoc in RUN1.
    eexists r1, _. split; [exact RUN1|].
    split; [exact A2|]. split; [exact K1|]. split; [apply Wn_grows|].
    split. { intros x Hx. rewrite Wn_outside; [reflexivity|lia|cbn; lia|cbn; lia]. }
    intros _. pose proof (Z.mod_pos_bound u' 8 ltac:(lia)).
    replace (2147450880 + b / 8 + u' / 8) with (2147450880 + b / 8 + u' / 8 + 0) at 2 by lia.
    pose proof (Wf_inside M (2147450880 + b / 8 + u' / 8) 1 (u' mod 8) 0 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as X. unfold Wf in X. cbn [repeat] in X.
    unfold Wn. rewrite art_bytes1 by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma annU_window_facts u u' : 0 <= u -> 0 <= u' -> u <> u' ->
  annU_lo u u' <= annU_plo u u' /\ annU_phi u u' <= annU_hi u u' /\ annU_plo u u' <= annU_phi u u'
  /\ (u' mod 8 <> 0 -> annU_lo u u' <= u' / 8 < annU_hi u u')
  /\ (forall j, annU_lo u u' <= j < annU_hi u u' -> ~ (u' mod 8 <> 0 /\ j = u' / 8) -> annU_plo u u' <= j < annU_phi u u' /\ annval u' j = annU_pv u u').
Proof.
  intros Hu Hu' Ne.
  pose proof (annU_div8_facts u Hu) as (Du1 & Du2 & Du3 & Du4 & Du5 & Du6). pose proof (annU_div8_facts u' Hu') as (Dv1 & Dv2 & Dv3 & Dv4 & Dv5 & Dv6).
  pose proof (RD_range u Hu) as (R1 & R2 & R3). pose proof (RD_range u' Hu') as (Q1 & Q2 & Q3).
  unfold annU_lo, annU_hi, annU_plo, annU_phi, annU_pv, annval. rewrite (proj2 (Z.eqb_neq u u') Ne).
  destruct (Z_lt_le_dec u u') as [Lt|Ge].
  - rewrite (proj2 (Z.ltb_lt u u') Lt). rewrite Z.min_l, Z.max_r by lia.
    assert (M1 : u / 8 <= u' / 8) by (apply Z.div_le_mono; lia). assert (M2 : (u + 7) / 8 <= (u' + 7) / 8) by (apply Z.div_le_mono; lia).
    destruct (Z.eq_dec (u' mod 8) 0) as [E|E]; [pose proof (Dv3 E) as X|pose proof (Dv4 E) as X].
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [intros C; exfalso; exact (C E)|].
      intros j Hj Nj. split; [lia|]. rewrite (proj2 (Z.ltb_lt j (u' / 8))) by lia. reflexivity.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [intros _; lia|].
      intros j Hj Nj. assert (j <> u' / 8) by (intros C; apply Nj; split; [exact E|exact C]). split; [lia|]. rewrite (proj2 (Z.ltb_lt j (u' / 8))) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge u u') Ge). rewrite Z.min_r, Z.max_l by lia.
    assert (M1 : u' / 8 <= u / 8) by (apply Z.div_le_mono; lia). assert (M2 : (u' + 7) / 8 <= (u + 7) / 8) by (apply Z.div_le_mono; lia).
    destruct (Z.eq_dec (u' mod 8) 0) as [E|E]; [pose proof (Dv3 E) as X|pose proof (Dv4 E) as X].
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [intros C; exfalso; exact (C E)|].
      intros j Hj Nj. split; [lia|]. rewrite (proj2 (Z.ltb_ge j (u' / 8))) by lia. rewrite E. cbn [Z.eqb negb andb]. rewrite Bool.andb_false_r. reflexivity.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [intros _; lia|].
      intros j Hj Nj. assert (j <> u' / 8) by (intros C; apply Nj; split; [exact E|exact C]). split; [lia|].
      rewrite (proj2 (Z.ltb_ge j (u' / 8))) by lia. rewrite (proj2 (Z.eqb_neq j (u' / 8))) by lia. reflexivity.
Qed.

#[using="Type"] Theorem art_annotateU_run : forall regs (M rom : word -> option byte) (raw : word) (sp0 b c u u' v : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp0 -> getr regs 10 = Z_to_bv 64 b -> getr regs 11 = Z_to_bv 64 (b + c) ->
  getr regs 12 = Z_to_bv 64 (b + u) -> getr regs 13 = Z_to_bv 64 (b + u') ->
  4096 <= b -> b mod 8 = 0 -> 0 <= u <= c -> 0 <= u' <= c -> b + c + 8 <= 2 ^ 47 -> c < 2 ^ 40 -> annU_place b c ->
  0x10007fff8000 + 2192 <= sp0 -> sp0 < 2 ^ 63 -> wrA M (sp0 - 2192) 2192 ->
  art_layout M -> cellA M (0x13d438 + 96) 1 1 -> cellA M 0x137510 8 0x1cf6d8 -> cellA M 0x1cf6d8 4 0 ->
  (c mod 8 <> 0 -> cellA M (SB + (b + c) / 8) 1 v /\ (v = 252 \/ 1 <= v <= c mod 8)) ->
  wrA M (SB + b / 8 + annU_lo u u') (annU_hi u u' - annU_lo u u') ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x7ba7c : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp0
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_ann_kept r -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (sp0 - 2192 <= U x < sp0) -> ~ (SB + b / 8 + annU_lo u u' <= U x < SB + b / 8 + annU_hi u u') -> M' x = M x)
    /\ (forall j, annU_lo u u' <= j < annU_hi u u' -> M' (Z_to_bv 64 (SB + b / 8 + j)) = Some (Z_to_bv 8 (annval u' j))).
Proof.
  intros regs M rom raw sp0 b c u u' v H1 Hret H2 H10 H11 H12 H13 Hb Hb8 Hu Hu' Hbc Hc40 PL Hsp Hsp' W L CF CV CV0 CSH Wsh.
  pose proof L as L'. destruct L' as (CG1 & CG2 & _ & _ & _ & _ & _ & _ & CG & _).
  assert (Dsh : 0 <= b / 8 /\ b / 8 + (c + 7) / 8 < 2 ^ 44 + 1).
  { split; [apply Z.div_pos; lia|]. pose proof (annU_div8_facts c ltac:(lia)) as (_ & _ & _ & _ & _ & X6). pose proof (RU_range c ltac:(lia)) as (Y1 & _).
    pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8 in Db. clear - Hb Hbc X6 Y1 Db. lia. }
  assert (Dbc : 0 <= (b + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (WIN : 0 <= annU_lo u u' /\ annU_hi u u' <= (c + 7) / 8).
  { unfold annU_lo, annU_hi. split; [apply Z.div_pos; lia|]. destruct (u =? u'); apply Z.div_le_mono; lia. }
  destruct (art_ann_pre regs M rom raw sp0 b c u u' H1 H2 H10 H11 H12 H13 ltac:(lia) ltac:(lia) Hu Hu' Hc40 ltac:(lia) Hsp' W CG CF CV CV0)
    as (r1 & RUN1 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & PK).
  set (M2 := art_poison_frame M sp0 (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) in *.
  assert (GR2 : mem_grows M M2) by (apply art_pf_grows).
  assert (FR2 : forall x : word, ~ (sp0 - 56 <= U x < sp0) -> M2 x = M x).
  { intros x Hx. unfold M2, art_poison_frame. rewrite !Wn_outside by (cbn; lia). reflexivity. }
  assert (C8 : cellA M2 (sp0 - 8) 8 (U raw)) by (unfold M2, art_poison_frame; zcell).
  assert (C16 : cellA M2 (sp0 - 16) 8 (U (getr regs 8))) by (unfold M2, art_poison_frame; zcell).
  assert (C24 : cellA M2 (sp0 - 24) 8 (U (getr regs 9))) by (unfold M2, art_poison_frame; zcell).
  assert (C32 : cellA M2 (sp0 - 32) 8 (U (getr regs 18))) by (unfold M2, art_poison_frame; zcell).
  assert (C40 : cellA M2 (sp0 - 40) 8 (U (getr regs 19))) by (unfold M2, art_poison_frame; zcell).
  assert (C48 : cellA M2 (sp0 - 48) 8 (U (getr regs 20))) by (unfold M2, art_poison_frame; zcell).
  assert (C56 : cellA M2 (sp0 - 56) 8 (U (getr regs 21))) by (unfold M2, art_poison_frame; zcell).
  assert (RG : forall r : reg, 0 <= U (getr regs r) < 2 ^ 64) by (intros r; apply bv_unsigned_in_range).
  assert (L2 : art_layout M2) by (apply (art_layout_agree3 M M2); [intros x Hx; apply FR2; clear - Hx Hsp; lia|exact L]).
  unfold BatPoison_b.SB in *.
  destruct (Z.eq_dec u u') as [Eq|Ne].
  - (* [comment removed for export] *)
    subst u'.
    assert (E19 : getr r1 19 = getr r1 18) by (rewrite P18, P19; reflexivity).
    destruct (art_ann_epi r1 M2 rom raw sp0 _ _ _ _ _ _ P2 ltac:(lia) Hsp' Hret (RG 8%bv) (RG 9%bv) (RG 18%bv) (RG 19%bv) (RG 20%bv) (RG 21%bv) C8 C16 C24 C32 C40 C48 C56)
      as (r3 & RUN3 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK).
    exists r3, M2. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact (art_ann_eq0 r1 M2 rom E19)|exact RUN3]|].
    rewrite !Z_to_bv_bv_unsigned in Q8, Q9, Q18, Q19, Q20, Q21.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|].
    split; [intros r Hr; rewrite (QK r Hr); exact (PK r Hr)|]. split; [exact GR2|].
    split; [intros x Hx _; apply FR2; clear - Hx; lia|]. intros j Hj. exfalso. unfold annU_lo, annU_hi in Hj. rewrite Z.eqb_refl in Hj. clear - Hj. lia.
  - pose proof (annU_window_facts u u' ltac:(lia) ltac:(lia) Ne) as (F1 & F2 & F3 & F4 & F5).
    (* [comment removed for export] *)
    assert (CSH2 : c mod 8 <> 0 -> cellA M2 (2147450880 + (b + c) / 8) 1 v /\ (v = 252 \/ 1 <= v <= c mod 8)).
    { intros Hc8. destruct (CSH Hc8) as (X & Y). split; [|exact Y]. apply (cell_agree M M2); [intros x Hx; apply FR2; cbn in Hx; clear - Hx Hsp Dbc; lia|clear -Dbc; lia|cbn; clear -Dbc; lia|exact X]. }
    assert (CG12 : cellA M2 0x1374c0 8 0x13fc38) by (destruct L2 as (X & _); exact X).
    assert (CG22 : cellA M2 0x13fc38 8 2147450880) by (destruct L2 as (_ & X & _); exact X).
    destruct (art_annU_A r1 M2 rom b c u u' v P9 P18 P19 P20 ltac:(lia) ltac:(lia) Hu Hu' Ne Hb8 CG12 CG22 CSH2) as (r2 & RUN2 & A10 & A11 & A19 & A20 & A21 & AK).
    assert (A2 : getr r2 2 = Z_to_bv 64 (sp0 - 2128)) by (rewrite AK by (intros X; discriminate X); exact P2).
    (* [comment removed for export] *)
    assert (W2 : wrA M2 (sp0 - 2128 - 64) 64) by (unfold M2, art_poison_frame; repeat apply wr_Wn; eapply wr_sub; [exact W|lia|lia]).
    assert (Wsh2 : wrA M2 (2147450880 + b / 8 + annU_plo u u') (annU_phi u u' - annU_plo u u')).
    { unfold M2, art_poison_frame; repeat apply wr_Wn. intros d k Hd Hk. replace (2147450880 + b / 8 + annU_plo u u' + d) with (2147450880 + b / 8 + annU_lo u u' + (annU_plo u u' - annU_lo u u' + d)) by lia. apply Wsh; clear - Hd Hk F1 F2 F3; lia. }
    destruct (art_annU_B r2 M2 rom (sp0 - 2128) b c u u' A2 A10 A11 A20 A21 Hb Hbc Hu Hu' Ne Hb8 PL ltac:(lia) ltac:(lia) W2 L2 Wsh2)
      as (r3 & M3 & RUN3 & B2 & B9 & B18 & B21 & B8 & BK & GR3 & FR3 & NEW3). unfold BatPoison_b.SB in FR3, NEW3.
    (* [comment removed for export] *)
    assert (L3 : art_layout M3) by (apply (art_layout_agree3 M2 M3); [intros x Hx; apply FR3; clear - Hx Hsp Dsh WIN F1; lia|exact L2]).
    assert (Wsh3 : u' mod 8 <> 0 -> wrA M3 (2147450880 + b / 8 + u' / 8) 1).
    { intros E. eapply wr_grows; [exact GR3|]. eapply wr_grows; [exact GR2|]. intros d k Hd Hk.
      replace (2147450880 + b / 8 + u' / 8 + d) with (2147450880 + b / 8 + annU_lo u u' + (u' / 8 - annU_lo u u' + d)) by lia. apply Wsh; clear - Hd Hk F4 E; lia. }
    destruct (art_annU_C r3 M3 rom b c u' B9 B18 B21 Hb Hbc Hu' Hb8 PL L3 Wsh3) as (r4 & M4 & RUN4 & D2 & DK & GR4 & FR4 & NEW4). unfold BatPoison_b.SB in FR4, NEW4.
    (* [comment removed for export] *)
    pose proof (Z.div_pos u' 8 ltac:(lia) ltac:(lia)) as Du'. assert (Du8 : u' / 8 <= (c + 7) / 8) by (apply Z.div_le_mono; lia).
    assert (TR : forall a v8, sp0 - 56 <= a -> a + 8 <= sp0 -> cellA M2 a 8%nat v8 -> cellA M4 a 8%nat v8).
    { intros a v8 Ha Ha' C. apply (cell_agree M3 M4); [intros x Hx; apply FR4; cbn in Hx; clear - Hx Ha Ha' Hsp Dsh Du' Du8; lia|clear - Ha Hsp; lia|cbn; clear - Ha' Hsp'; lia|].
      apply (cell_agree M2 M3); [intros x Hx; apply FR3; cbn in Hx; clear - Hx Ha Ha' Hsp Dsh WIN F1 F2 F3; lia|clear - Ha Hsp; lia|cbn; clear - Ha' Hsp'; lia|exact C]. }
    rewrite B2 in D2.
    destruct (art_ann_epi r4 M4 rom raw sp0 _ _ _ _ _ _ D2 ltac:(lia) Hsp' Hret (RG 8%bv) (RG 9%bv) (RG 18%bv) (RG 19%bv) (RG 20%bv) (RG 21%bv)
                (TR (sp0 - 8) _ ltac:(lia) ltac:(lia) C8) (TR (sp0 - 16) _ ltac:(lia) ltac:(lia) C16) (TR (sp0 - 24) _ ltac:(lia) ltac:(lia) C24) (TR (sp0 - 32) _ ltac:(lia) ltac:(lia) C32)
                (TR (sp0 - 40) _ ltac:(lia) ltac:(lia) C40) (TR (sp0 - 48) _ ltac:(lia) ltac:(lia) C48) (TR (sp0 - 56) _ ltac:(lia) ltac:(lia) C56))
      as (r5 & RUN5 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK).
    exists r5, M4. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|exact RUN5]. }
    rewrite !Z_to_bv_bv_unsigned in Q8, Q9, Q18, Q19, Q20, Q21.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|].
    split. { intros r Hr. rewrite (QK r Hr). pose proof Hr as Hr'. unfold art_ann_kept in Hr.
             rewrite DK; [| clear - Hr; cbv [callee_saved In]; destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; tauto
                        | clear - Hr; destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; intros X; discriminate X
                        | clear - Hr; destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; intros X; discriminate X ].
             rewrite (BK r Hr'). rewrite AK by (clear - Hr; destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; intros X; discriminate X). exact (PK r Hr'). }
    split. { eapply mem_grows_trans; [exact GR2|]. eapply mem_grows_trans; [exact GR3|exact GR4]. }
    split. { intros x Hx Hy. rewrite FR4 by (clear - Hy F4; lia). rewrite FR3 by (clear - Hx Hy F1 F2; lia). apply FR2. clear - Hx; lia. }
    intros j Hj. destruct (Z.eq_dec (u' mod 8) 0) as [E|E].
    + destruct (F5 j Hj ltac:(clear - E; lia)) as (Pj & Ev). rewrite Ev, <- (NEW3 j Pj). apply FR4. clear - E; lia.
    + destruct (Z.eq_dec j (u' / 8)) as [Ej|Nj].
      * subst j. rewrite (NEW4 E). unfold annval. rewrite Z.ltb_irrefl, Z.eqb_refl, (proj2 (Z.eqb_neq (u' mod 8) 0) E). reflexivity.
      * destruct (F5 j Hj ltac:(clear - Nj; lia)) as (Pj & Ev). rewrite Ev, <- (NEW3 j Pj). apply FR4. rewrite art_u_lit by (clear - Dsh WIN Hj; lia). clear - Nj; lia.
Qed.

End FPX.
