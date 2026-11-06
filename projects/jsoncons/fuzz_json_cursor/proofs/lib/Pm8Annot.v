(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
Require OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.GcFlush06.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib RefMemcpyLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac ArtRunsMem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8ArtPoison Pm8ArtPoisonRun Pm8ArtPoison2 Pm8RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8AnnotTab.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Definition ann_frame (M : word -> option byte) (s ra v8 v9 v18 v19 v20 v21 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (s - 8) ra) (s - 16) v8) (s - 24) v9) (s - 32) v18) (s - 40) v19) (s - 48) v20) (s - 56) v21.

Lemma ann_andi_m8 : forall x, 0 <= x < 2 ^ 64 -> v_andi (Z_to_bv 64 x) (-8) = Z_to_bv 64 (x / 8 * 8).
Proof. intros x Hx. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia. reflexivity. Qed.
Lemma ann_andi_7 : forall x, 0 <= x < 2 ^ 64 -> v_andi (Z_to_bv 64 x) 7 = Z_to_bv 64 (x mod 8).
Proof. intros x Hx. rewrite art_zb_andi by lia. rewrite land7_mod8. reflexivity. Qed.
Lemma ann_c_lts_zb : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> c_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold c_lts, bv_lts. rewrite !signed64_small by lia. reflexivity. Qed.
Lemma ann_c_lts_fc : forall x, 0 <= x < 2 ^ 63 -> c_lts (Z_to_bv 64 x) (v_lb (Z_to_bv 8 252)) = false.
Proof. intros x Hx. unfold c_lts, bv_lts. rewrite signed64_small by lia. replace (bv_signed (v_lb (Z_to_bv 8 252))) with (-4) by vmc_refl. apply Z.ltb_ge. lia. Qed.

Lemma ann_layout_agree : forall (M M' : word -> option byte), art_layout M -> (forall x : word, U x < 0x6b3000 -> M' x = M x) -> art_layout M'.
Proof.
  intros M M' L AG. unfold art_layout in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply (art_cell_agree ASEGS M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | eassumption]).
Qed.

Section WALK.
  Variables (M0 rom : word -> option byte) (raw : word) (s b e o m : Z).
  Hypothesis Hs : 0x10007fff8000 <= s - 2192 /\ s < 2 ^ 47.
  Hypothesis W : wrA M0 (s - 2192) 2192.
  Hypothesis Hb : 4096 <= b /\ b mod 8 = 0 /\ b <= o <= e /\ b <= m <= e /\ e < 2 ^ 47 /\ e - b <= 2 ^ 18.
  Hypothesis LAY : art_layout M0.
  Hypothesis CDCO : cellA M0 0x15a218 1 1.
  Hypothesis CVP : cellA M0 0x153188 8 0x1ec458.
  Hypothesis CV : cellA M0 0x1ec458 4 0.

  Lemma ann_L1a : forall regs, getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s ->
    getr regs 10 = Z_to_bv 64 b -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 o -> getr regs 13 = Z_to_bv 64 m ->
    exists regs', msteps ASEGS (mkst regs (0x82c5c : word) M0 rom)
        (mkst regs' (0x82d74 : word) (ann_frame M0 s (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 2128) /\ getr regs' 9 = Z_to_bv 64 b /\ getr regs' 18 = Z_to_bv 64 m /\ getr regs' 19 = Z_to_bv 64 o /\ getr regs' 20 = Z_to_bv 64 e
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
  Proof.
    intros regs H1 H2 H10 H11 H12 H13. destruct LAY as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & _).
    eexists. split.
    - zstep Fx_82c0c Dx_82c0c.
      zsd Fx_82c10 Dx_82c10 (s - 8) (U raw) ltac:(rewok W).
      zsd Fx_82c14 Dx_82c14 (s - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd Fx_82c18 Dx_82c18 (s - 24) (U (getr regs 9)) ltac:(rewok W).
      zsd Fx_82c1c Dx_82c1c (s - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd Fx_82c20 Dx_82c20 (s - 40) (U (getr regs 19)) ltac:(rewok W).
      zsd Fx_82c24 Dx_82c24 (s - 48) (U (getr regs 20)) ltac:(rewok W).
      zsd Fx_82c28 Dx_82c28 (s - 56) (U (getr regs 21)) ltac:(rewok W).
      fold (ann_frame M0 s (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))).
      set (MF := ann_frame M0 s (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))).
      zstep Fx_82c2c Dx_82c2c. zstep Fx_82c30 Dx_82c30. zstep Fx_82c34 Dx_82c34. zstep Fx_82c38 Dx_82c38.
      assert (L9f : cellA MF 0x153130 8 0x15a1b8) by (unfold MF, ann_frame; recell L9).
      assert (CDCOf : cellA MF 0x15a218 1 1) by (unfold MF, ann_frame; recell CDCO).
      assert (CVPf : cellA MF 0x153188 8 0x1ec458) by (unfold MF, ann_frame; recell CVP).
      assert (CVf : cellA MF 0x1ec458 4 0) by (unfold MF, ann_frame; recell CV).
      zld Fx_82c3c Dx_82c3c 0x153130 L9f.
      zlbu Fx_82c40 Dx_82c40 0x15a218 CDCOf.
      zbft Fx_82c44 Dx_82c44.
      zstep Fx_82c48 Dx_82c48. zstep Fx_82c4c Dx_82c4c. zstep Fx_82c50 Dx_82c50. zstep Fx_82c54 Dx_82c54.
      zld Fx_82c58 Dx_82c58 0x153188 CVPf.
      zlw Fx_82c5c Dx_82c5c 0x1ec458 CVf.
      zstep Fx_82c60 Dx_82c60.
      zbft Fx_82c64 Dx_82c64.
      zbtk Fx_82c68 Dx_82c68.
      zbft Fx_82d04 Dx_82d04. zbft Fx_82d08 Dx_82d08. zbft Fx_82d0c Dx_82d0c.
      zstep Fx_82d10 Dx_82d10. zstep Fx_82d14 Dx_82d14. zstep Fx_82d18 Dx_82d18. zstep Fx_82d1c Dx_82d1c.
      zbft Fx_82d20 Dx_82d20.
      apply mst_refl.
    - split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|].
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [gres; reflexivity|]). destruct Hr.
  Qed.

  Lemma ann_L1b : forall (M : word -> option byte) regs, cellA M 0x153138 8 0x15c9b8 -> cellA M 0x15c9b8 8 0x7fff8000 ->
    (e mod 8 <> 0 -> exists sv, cellA M (0x7fff8000 + e / 8) 1 sv /\ (sv = 252 \/ (1 <= sv <= 7 /\ sv <= e mod 8))) ->
    o <> m -> getr regs 9 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 m -> getr regs 19 = Z_to_bv 64 o -> getr regs 20 = Z_to_bv 64 e ->
    exists regs', msteps ASEGS (mkst regs (0x82d74 : word) M rom) (mkst regs' (0x82d80 : word) M rom)
      /\ getr regs' 9 = Z_to_bv 64 b /\ getr regs' 18 = Z_to_bv 64 m /\ getr regs' 19 = Z_to_bv 64 o
      /\ (forall r : reg, In r [1; 2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
  Proof.
    intros M regs C1 C2 HEND Hne H9 H18 H19 H20.
    pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Re. pose proof (Z.div_mod e 8 ltac:(lia)) as De.
    assert (FIN : forall rg : bvmap 5 word, getr rg 9 = getr regs 9 -> getr rg 18 = getr regs 18 -> getr rg 19 = getr regs 19 ->
              (forall r : reg, In r [1; 2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r) ->
              getr rg 9 = Z_to_bv 64 b /\ getr rg 18 = Z_to_bv 64 m /\ getr rg 19 = Z_to_bv 64 o /\ (forall r : reg, In r [1; 2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r)).
    { intros rg E9 E18 E19 EK. rewrite E9, E18, E19. repeat (split; [assumption|]). exact EK. }
    destruct (Z.eq_dec (e mod 8) 0) as [E0|N0].
    -
      eexists. split.
      + zbft Fx_82d24 Dx_82d24. zstep Fx_82d28 Dx_82d28. rewrite ann_andi_7 by lia. rewrite E0.
        zbft Fx_82d2c Dx_82d2c. apply mst_refl.
      + apply FIN; [gres; reflexivity|gres; reflexivity|gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [gres; reflexivity|]). destruct Hr.
    - destruct (HEND N0) as (sv & CSV & HSV).

      assert (RD : forall rg : bvmap 5 word, getr rg 10 = Z_to_bv 64 (e mod 8) -> getr rg 20 = Z_to_bv 64 e ->
                exists rg', msteps ASEGS (mkst rg (0x82df0 : word) M rom) (mkst rg' (0x82d80 : word) M rom)
                  /\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> getr rg' r = getr rg r)).
      { intros rg G10 G20. destruct HSV as [-> | (K1 & K2)].
        - eexists. split.
          + zstep Fx_82da0 Dx_82da0. zld Fx_82da4 Dx_82da4 0x153138 C1. zld Fx_82da8 Dx_82da8 0x15c9b8 C2.
            zstep Fx_82dac Dx_82dac. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
            zstep Fx_82db0 Dx_82db0.
            chain_step; [reflexivity | eapply step_lb; [exact Fx_82db4 | reflexivity | exact Dx_82db4 | zaddr (0x7fff8000 + e / 8); eapply cell_rdn1; [ | exact CSV]; lia ] | step_simpl; vnorm].
            stepb_ft Fx_82db8 Dx_82db8 ltac:(vm_compute; reflexivity).
            stepb_tk Fx_82dbc Dx_82dbc ltac:(rwH; apply ann_c_lts_fc; lia).
            apply mst_refl.
          + intros r N11 N12. repeat (rewrite getr_other by (assumption || (symmetry; assumption))). reflexivity.
        - eexists. split.
          + zstep Fx_82da0 Dx_82da0. zld Fx_82da4 Dx_82da4 0x153138 C1. zld Fx_82da8 Dx_82da8 0x15c9b8 C2.
            zstep Fx_82dac Dx_82dac. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
            zstep Fx_82db0 Dx_82db0.
            zlb Fx_82db4 Dx_82db4 (0x7fff8000 + e / 8) CSV.
            zbft Fx_82db8 Dx_82db8.
            stepb_tk Fx_82dbc Dx_82dbc ltac:(rwH; rewrite ann_c_lts_zb by lia; apply Z.ltb_ge; lia).
            apply mst_refl.
          + intros r N11 N12. repeat (rewrite getr_other by (assumption || (symmetry; assumption))). reflexivity. }
      assert (KEEPF : forall rg : bvmap 5 word, (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 21%bv -> getr rg r = getr regs r) ->
                getr rg 9 = Z_to_bv 64 b /\ getr rg 18 = Z_to_bv 64 m /\ getr rg 19 = Z_to_bv 64 o /\ (forall r : reg, In r [1; 2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r)).
      { intros rg KP. apply FIN; [apply KP; intros X; discriminate X|apply KP; intros X; discriminate X|apply KP; intros X; discriminate X|].
        intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [apply KP; intros X; discriminate X|]). destruct Hr. }
      assert (E8lo : 0 <= e / 8 * 8 <= e) by lia.
      destruct (Z_lt_ge_dec m o) as [Lmo|Gmo].
      + destruct (Z_le_gt_dec o (e / 8 * 8)) as [Fit|Over].
        * eexists. split.
          -- zbft Fx_82d24 Dx_82d24. zstep Fx_82d28 Dx_82d28. rewrite ann_andi_7 by lia. zbtk Fx_82d2c Dx_82d2c. zstep Fx_82d8c Dx_82d8c. rewrite ann_andi_m8 by lia. zstep Fx_82d90 Dx_82d90.
             zbtk Fx_82d94 Dx_82d94. zbtk Fx_82d9c Dx_82d9c. apply mst_refl.
          -- apply KEEPF. intros r N10 N11 N12 N21. repeat (rewrite getr_other by (assumption || (symmetry; assumption))). reflexivity.
        * assert (PRE : exists rg, msteps ASEGS (mkst regs (0x82d74 : word) M rom) (mkst rg (0x82df0 : word) M rom) /\ getr rg 10 = Z_to_bv 64 (e mod 8) /\ getr rg 20 = Z_to_bv 64 e
                          /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 21%bv -> getr rg r = getr regs r)).
          { eexists. split.
            - zbft Fx_82d24 Dx_82d24. zstep Fx_82d28 Dx_82d28. rewrite ann_andi_7 by lia. zbtk Fx_82d2c Dx_82d2c. zstep Fx_82d8c Dx_82d8c. rewrite ann_andi_m8 by lia. zstep Fx_82d90 Dx_82d90.
              zbtk Fx_82d94 Dx_82d94. zbft Fx_82d9c Dx_82d9c. apply mst_refl.
            - split; [gres; reflexivity|]. split; [gres; rwH; reflexivity|]. intros r N10 N11 N12 N21. repeat (rewrite getr_other by (assumption || (symmetry; assumption))). reflexivity. }
          destruct PRE as (rgA & RUNA & A10 & A20 & KA). destruct (RD rgA A10 A20) as (rgB & RUNB & KB).
          exists rgB. split; [eapply msteps_trans; [exact RUNA|exact RUNB]|]. apply KEEPF. intros r N10 N11 N12 N21. rewrite (KB r N11 N12). exact (KA r N10 N11 N12 N21).
      + destruct (Z_le_gt_dec m (e / 8 * 8)) as [Fit|Over].
        * eexists. split.
          -- zbft Fx_82d24 Dx_82d24. zstep Fx_82d28 Dx_82d28. rewrite ann_andi_7 by lia. zbtk Fx_82d2c Dx_82d2c. zstep Fx_82d8c Dx_82d8c. rewrite ann_andi_m8 by lia. zstep Fx_82d90 Dx_82d90.
             zbft Fx_82d94 Dx_82d94. zstep Fx_82d98 Dx_82d98. zbtk Fx_82d9c Dx_82d9c. apply mst_refl.
          -- apply KEEPF. intros r N10 N11 N12 N21. repeat (rewrite getr_other by (assumption || (symmetry; assumption))). reflexivity.
        * assert (PRE : exists rg, msteps ASEGS (mkst regs (0x82d74 : word) M rom) (mkst rg (0x82df0 : word) M rom) /\ getr rg 10 = Z_to_bv 64 (e mod 8) /\ getr rg 20 = Z_to_bv 64 e
                          /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 21%bv -> getr rg r = getr regs r)).
          { eexists. split.
            - zbft Fx_82d24 Dx_82d24. zstep Fx_82d28 Dx_82d28. rewrite ann_andi_7 by lia. zbtk Fx_82d2c Dx_82d2c. zstep Fx_82d8c Dx_82d8c. rewrite ann_andi_m8 by lia. zstep Fx_82d90 Dx_82d90.
              zbft Fx_82d94 Dx_82d94. zstep Fx_82d98 Dx_82d98. zbft Fx_82d9c Dx_82d9c. apply mst_refl.
            - split; [gres; reflexivity|]. split; [gres; rwH; reflexivity|]. intros r N10 N11 N12 N21. repeat (rewrite getr_other by (assumption || (symmetry; assumption))). reflexivity. }
          destruct PRE as (rgA & RUNA & A10 & A20 & KA). destruct (RD rgA A10 A20) as (rgB & RUNB & KB).
          exists rgB. split; [eapply msteps_trans; [exact RUNA|exact RUNB]|]. apply KEEPF. intros r N10 N11 N12 N21. rewrite (KB r N11 N12). exact (KA r N10 N11 N12 N21).
  Qed.

  Definition ann_lo : Z := if o <? m then o / 8 else (m + 7) / 8.
  Definition ann_hi : Z := if o <? m then m / 8 else (o + 7) / 8.
  Definition ann_v : Z := if o <? m then 0 else 252.

  Hypothesis Happ : (8 <= b /\ e <= 0x7fff8000) \/ (kHighMemBeg <= b /\ e <= kHighMemEnd + 1).

  Lemma ann_poison : forall (M : word -> option byte) regs p n' v, art_layout M -> wrA M (s - 2192) 64 -> wrA M (0x7fff8000 + b / 8) ((e - b + 7) / 8) ->
    getr regs 2 = Z_to_bv 64 (s - 2128) -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n' -> getr regs 12 = Z_to_bv 64 v ->
    b <= p -> p mod 8 = 0 -> n' mod 8 = 0 -> 8 <= n' -> p + n' <= (e + 7) / 8 * 8 -> (v = 0 \/ v = 252) ->
    exists regs' M', msteps ASEGS (mkst regs (0x82ea0 : word) M rom) (mkst regs' (0x82ea4 : word) M' rom)
      /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
      /\ mem_grows M M'
      /\ (forall x : word, ~ (s - 2192 <= U x < s - 2128) -> ~ (0x7fff8000 + p / 8 <= U x < 0x7fff8000 + (p + n') / 8) -> M' x = M x)
      /\ (forall j, p / 8 <= j < (p + n') / 8 -> M' (Z_to_bv 64 (0x7fff8000 + j)) = Some (Z_to_bv 8 v)).
  Proof.
    intros M regs p n' v LM WM WSH H2 H10 H11 H12 Hp Hp8 Hn8 Hn Hpe Hv.
    pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Re.
    pose proof (Z.div_mod (e + 7) 8 ltac:(lia)) as De7. pose proof (Z.mod_pos_bound (e + 7) 8 ltac:(lia)) as Re7.
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. rewrite Hp8, Z.add_0_r in Dp. pose proof (Z.div_mod n' 8 ltac:(lia)) as Dn. rewrite Hn8, Z.add_0_r in Dn.
    destruct Hb as (B0 & B8 & _ & _ & E47 & EB). pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite B8, Z.add_0_r in Db.
    pose proof (Z.div_mod (e - b + 7) 8 ltac:(lia)) as Deb. pose proof (Z.mod_pos_bound (e - b + 7) 8 ltac:(lia)) as Reb.
    assert (EPN : (p + n') / 8 = p / 8 + n' / 8) by (rewrite Dp at 1; rewrite Dn at 1; replace (8 * (p / 8) + 8 * (n' / 8)) with ((p / 8 + n' / 8) * 8) by ring; apply Z.div_mul; lia).
    assert (SEG : exists rg, msteps ASEGS (mkst regs (0x82ea0 : word) M rom) (mkst rg (0x81d18 : word) M rom) /\ getr rg 1 = (0x82ea4%bv : word)
                    /\ (forall r : reg, r <> 1%bv -> getr rg r = getr regs r)).
    { eexists. split; [stepn Fx_82e50 Dx_82e50; apply mst_refl|]. split; [gres; first [reflexivity | apply bv_eq; reflexivity]|].
      intros r N1. repeat (rewrite getr_other by (assumption || (symmetry; assumption))). reflexivity. }
    destruct SEG as (rgA & RUNA & A1 & KA).
    destruct (art_poison_run rgA M rom (0x82ea4%bv : word) (s - 2128) p n' v A1 ltac:(unfold ret_ok; bveq)
                ltac:(rewrite (KA 2%bv) by (intros X; discriminate X); exact H2) ltac:(rewrite (KA 10%bv) by (intros X; discriminate X); exact H10)
                ltac:(rewrite (KA 11%bv) by (intros X; discriminate X); exact H11) ltac:(rewrite (KA 12%bv) by (intros X; discriminate X); exact H12)
                ltac:(lia) ltac:(lia) ltac:(replace (s - 2128 - 64) with (s - 2192) by ring; exact WM)
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) LM
                ltac:(unfold art_poison_lo_ok, art_poison_hi_ok, Pm8ArtPoison.SB, kHighMemBeg, kHighMemEnd in *; clear - Happ Hp Hn Hpe De7 Re7 De Re; lia)
                Hp8 Hn8 ltac:(lia) ltac:(lia) ltac:(intros _; clear - Hp Hn Hpe EB De7 Re7 Dn; lia)
                ltac:(unfold Pm8ArtPoison.SB; apply (wr_sub _ _ _ _ _ _ WSH); clear - Hp Hpe Dp Dn Db De7 Re7 EPN Deb Reb; lia))
      as (rgB & RUNB & _ & B1 & B2 & B8' & B9 & B18 & B19 & B20 & B21 & KB).
    match type of RUNB with msteps _ _ (mkst _ _ ?X _) => set (M' := X) in * end.
    exists rgB, M'. split; [eapply msteps_trans; [exact RUNA|exact RUNB]|].
    split. { intros r Hr. cbn [In] in Hr.
             assert (KK : forall r0 : reg, art_poison_kept r0 -> r0 <> 1%bv -> getr rgB r0 = getr regs r0) by (intros r0 K0 N0; rewrite (KB r0 K0); exact (KA r0 N0)).
             destruct Hr as [<- | Hr]; [rewrite B2, H2; reflexivity|].
             destruct Hr as [<- | Hr]; [apply KK; [unfold art_poison_kept; repeat split; intros X; discriminate X|intros X; discriminate X]|].
             destruct Hr as [<- | Hr]; [apply KK; [unfold art_poison_kept; repeat split; intros X; discriminate X|intros X; discriminate X]|].
             destruct Hr as [<- | Hr]; [rewrite B8'; apply KA; intros X; discriminate X|]. destruct Hr as [<- | Hr]; [rewrite B9; apply KA; intros X; discriminate X|].
             destruct Hr as [<- | Hr]; [rewrite B18; apply KA; intros X; discriminate X|]. destruct Hr as [<- | Hr]; [rewrite B19; apply KA; intros X; discriminate X|].
             destruct Hr as [<- | Hr]; [rewrite B20; apply KA; intros X; discriminate X|]. destruct Hr as [<- | Hr]; [rewrite B21; apply KA; intros X; discriminate X|].
             repeat (destruct Hr as [<- | Hr]; [apply KK; [unfold art_poison_kept; repeat split; intros X; discriminate X|intros X; discriminate X]|]). destruct Hr. }
    assert (NN : Z.of_nat (Z.to_nat (n' / 8)) = n' / 8) by (apply Z2Nat.id; lia).
    split. { unfold M', art_poison_frame. eapply mem_grows_trans; [|apply Wf_grows]. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
    split. { intros x X1 X2. unfold M', art_poison_frame, Pm8ArtPoison.SB. rewrite Wf_outside by (rewrite ?NN; clear - Hp B0 Hpe E47 De7 Re7 X2 EPN Dp Dn; lia).
             rewrite !Wn_outside by (cbn [Z.of_nat Pos.to_nat]; clear - Hs X1; lia). reflexivity. }
    intros j Hj. unfold M', Pm8ArtPoison.SB. replace (2147450880 + j) with (2147450880 + p / 8 + (j - p / 8)) by ring.
    apply Wf_inside; [clear - Hp B0; lia|rewrite NN; clear - Hp B0 Hpe E47 De7 Re7 EPN Dp Dn; lia|rewrite NN; clear - Hj EPN; lia].
  Qed.

  #[local] Ltac keepr := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [gres; reflexivity|]); destruct Hr.

  Lemma ann_L2 : forall (M : word -> option byte) regs, art_layout M -> wrA M (s - 2192) 64 -> wrA M (0x7fff8000 + b / 8) ((e - b + 7) / 8) -> o <> m ->
    getr regs 2 = Z_to_bv 64 (s - 2128) -> getr regs 9 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 m -> getr regs 19 = Z_to_bv 64 o ->
    exists regs' M', msteps ASEGS (mkst regs (0x82d80 : word) M rom) (mkst regs' (0x82ea4 : word) M' rom)
      /\ getr regs' 9 = Z_to_bv 64 (m / 8 * 8) /\ getr regs' 18 = Z_to_bv 64 ((m + 7) / 8 * 8) /\ getr regs' 21 = Z_to_bv 64 m
      /\ (forall r : reg, In r [2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
      /\ mem_grows M M'
      /\ (forall x : word, ~ (s - 2192 <= U x < s - 2128) -> ~ (0x7fff8000 + ann_lo <= U x < 0x7fff8000 + ann_hi) -> M' x = M x)
      /\ (forall j, ann_lo <= j < ann_hi -> M' (Z_to_bv 64 (0x7fff8000 + j)) = Some (Z_to_bv 8 ann_v)).
  Proof.
    intros M regs LM WM WSH Hne H2 H9 H18 H19. destruct Hb as (B0 & B8 & (Bo1 & Bo2) & (Bm1 & Bm2) & E47 & EB).

    pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite B8, Z.add_0_r in Db.
    assert (RBo : b <= o / 8 * 8 <= o) by (pose proof (Z.div_mod o 8 ltac:(lia)); pose proof (Z.mod_pos_bound o 8 ltac:(lia)); lia).
    assert (RBm : b <= m / 8 * 8 <= m) by (pose proof (Z.div_mod m 8 ltac:(lia)); pose proof (Z.mod_pos_bound m 8 ltac:(lia)); lia).
    assert (RBo7 : o <= (o + 7) / 8 * 8 <= (e + 7) / 8 * 8)
      by (pose proof (Z.div_mod (o + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (o + 7) 8 ltac:(lia)); pose proof (Z.div_mod (e + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (e + 7) 8 ltac:(lia)); lia).
    assert (RBm7 : m <= (m + 7) / 8 * 8 <= (e + 7) / 8 * 8)
      by (pose proof (Z.div_mod (m + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (m + 7) 8 ltac:(lia)); pose proof (Z.div_mod (e + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (e + 7) 8 ltac:(lia)); lia).
    assert (RBe : (e + 7) / 8 * 8 <= e + 7) by (pose proof (Z.div_mod (e + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (e + 7) 8 ltac:(lia)); lia).
    assert (RBn1 : o / 8 * 8 >= m / 8 * 8 -> o / 8 >= m / 8) by lia.
    assert (RBn2 : (m + 7) / 8 * 8 >= (o + 7) / 8 * 8 -> (m + 7) / 8 >= (o + 7) / 8) by lia.
    clear Db.
    destruct (Z_lt_ge_dec o m) as [Lom|Gom].
    -
      assert (ELO : ann_lo = o / 8) by (unfold ann_lo; rewrite (proj2 (Z.ltb_lt o m) Lom); reflexivity).
      assert (EHI : ann_hi = m / 8) by (unfold ann_hi; rewrite (proj2 (Z.ltb_lt o m) Lom); reflexivity).
      assert (EV : ann_v = 0) by (unfold ann_v; rewrite (proj2 (Z.ltb_lt o m) Lom); reflexivity).
      destruct (Z_lt_ge_dec (o / 8 * 8) (m / 8 * 8)) as [P|NP].
      + assert (PRE : exists rg, msteps ASEGS (mkst regs (0x82d80 : word) M rom) (mkst rg (0x82ea0 : word) M rom)
                        /\ getr rg 2 = Z_to_bv 64 (s - 2128) /\ getr rg 10 = Z_to_bv 64 (o / 8 * 8) /\ getr rg 11 = Z_to_bv 64 (m / 8 * 8 - o / 8 * 8) /\ getr rg 12 = Z_to_bv 64 0
                        /\ getr rg 9 = Z_to_bv 64 (m / 8 * 8) /\ getr rg 18 = Z_to_bv 64 ((m + 7) / 8 * 8) /\ getr rg 21 = Z_to_bv 64 m
                        /\ (forall r : reg, In r [2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r)).
        { eexists. split.
          - zstep Fx_82d30 Dx_82d30. zstep Fx_82d34 Dx_82d34. zstep Fx_82d38 Dx_82d38. zstep Fx_82d3c Dx_82d3c. rewrite ann_andi_7 by lia. rewrite B8.
            zbft Fx_82d40 Dx_82d40. zstep Fx_82d44 Dx_82d44. zstep Fx_82d48 Dx_82d48. zbtk Fx_82d4c Dx_82d4c.
            zstep Fx_82e1c Dx_82e1c. rewrite ann_andi_m8 by lia. zbft Fx_82e20 Dx_82e20.
            zstep Fx_82e24 Dx_82e24. zstep Fx_82e28 Dx_82e28. rewrite ann_andi_m8 by lia. zstep Fx_82e2c Dx_82e2c. zstep Fx_82e30 Dx_82e30. rewrite ann_andi_m8 by lia.
            zbtk Fx_82e34 Dx_82e34.
            zstep Fx_82d68 Dx_82d68. zstep Fx_82d6c Dx_82d6c. zstep Fx_82d70 Dx_82d70.
            apply mst_refl.
          - split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. keepr. }
        destruct PRE as (rgA & RUNA & A2 & A10 & A11 & A12 & A9 & A18 & A21 & KA).
        destruct (ann_poison M rgA (o / 8 * 8) (m / 8 * 8 - o / 8 * 8) 0 LM WM WSH A2 A10 A11 A12 ltac:(lia)
                    ltac:(apply Z_mod_mult) ltac:(replace (m / 8 * 8 - o / 8 * 8) with ((m / 8 - o / 8) * 8) by ring; apply Z_mod_mult) ltac:(lia) ltac:(lia) ltac:(left; reflexivity))
          as (rgB & M' & RUNB & KB & GRB & FRB & FLB).
        assert (Q1 : o / 8 * 8 / 8 = o / 8) by (apply Z.div_mul; lia).
        assert (Q2 : (o / 8 * 8 + (m / 8 * 8 - o / 8 * 8)) / 8 = m / 8) by (replace (o / 8 * 8 + (m / 8 * 8 - o / 8 * 8)) with (m / 8 * 8) by ring; apply Z.div_mul; lia).
        rewrite Q1, Q2 in FRB, FLB.
        exists rgB, M'. split; [eapply msteps_trans; [exact RUNA|exact RUNB]|].
        split; [rewrite (KB 9%bv) by (cbn [In]; tauto); exact A9|]. split; [rewrite (KB 18%bv) by (cbn [In]; tauto); exact A18|]. split; [rewrite (KB 21%bv) by (cbn [In]; tauto); exact A21|].
        split. { intros r Hr. rewrite (KB r) by (cbn [In] in Hr |- *; tauto). exact (KA r Hr). }
        split; [exact GRB|]. rewrite ELO, EHI, EV. split; [exact FRB|exact FLB].
      + assert (SEG : exists rg, msteps ASEGS (mkst regs (0x82d80 : word) M rom) (mkst rg (0x82ea4 : word) M rom)
                        /\ getr rg 9 = Z_to_bv 64 (m / 8 * 8) /\ getr rg 18 = Z_to_bv 64 ((m + 7) / 8 * 8) /\ getr rg 21 = Z_to_bv 64 m
                        /\ (forall r : reg, In r [2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r)).
        { eexists. split.
          - zstep Fx_82d30 Dx_82d30. zstep Fx_82d34 Dx_82d34. zstep Fx_82d38 Dx_82d38. zstep Fx_82d3c Dx_82d3c. rewrite ann_andi_7 by lia. rewrite B8.
            zbft Fx_82d40 Dx_82d40. zstep Fx_82d44 Dx_82d44. zstep Fx_82d48 Dx_82d48. zbtk Fx_82d4c Dx_82d4c.
            zstep Fx_82e1c Dx_82e1c. rewrite ann_andi_m8 by lia. zbft Fx_82e20 Dx_82e20.
            zstep Fx_82e24 Dx_82e24. zstep Fx_82e28 Dx_82e28. rewrite ann_andi_m8 by lia. zstep Fx_82e2c Dx_82e2c. zstep Fx_82e30 Dx_82e30. rewrite ann_andi_m8 by lia.
            zbft Fx_82e34 Dx_82e34.
            zstep Fx_82e38 Dx_82e38. zstep Fx_82e3c Dx_82e3c. rewrite ann_andi_m8 by lia. zbtk Fx_82e40 Dx_82e40.
            apply mst_refl.
          - split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. keepr. }
        destruct SEG as (rg & RUN & F9 & F18 & F21 & KR). exists rg, M. split; [exact RUN|]. split; [exact F9|]. split; [exact F18|]. split; [exact F21|]. split; [exact KR|].
        split; [apply mem_grows_refl|]. split; [intros x _ _; reflexivity|]. intros j Hj. exfalso. rewrite ELO, EHI in Hj. clear - Hj NP RBn1 RBn2. lia.
    -
      assert (Lmo : m < o) by lia.
      assert (ELO : ann_lo = (m + 7) / 8) by (unfold ann_lo; rewrite (proj2 (Z.ltb_ge o m) ltac:(lia)); reflexivity).
      assert (EHI : ann_hi = (o + 7) / 8) by (unfold ann_hi; rewrite (proj2 (Z.ltb_ge o m) ltac:(lia)); reflexivity).
      assert (EV : ann_v = 252) by (unfold ann_v; rewrite (proj2 (Z.ltb_ge o m) ltac:(lia)); reflexivity).
      destruct (Z_lt_ge_dec ((m + 7) / 8 * 8) ((o + 7) / 8 * 8)) as [P|NP].
      + assert (PRE : exists rg, msteps ASEGS (mkst regs (0x82d80 : word) M rom) (mkst rg (0x82ea0 : word) M rom)
                        /\ getr rg 2 = Z_to_bv 64 (s - 2128) /\ getr rg 10 = Z_to_bv 64 ((m + 7) / 8 * 8) /\ getr rg 11 = Z_to_bv 64 ((o + 7) / 8 * 8 - (m + 7) / 8 * 8) /\ getr rg 12 = Z_to_bv 64 252
                        /\ getr rg 9 = Z_to_bv 64 (m / 8 * 8) /\ getr rg 18 = Z_to_bv 64 ((m + 7) / 8 * 8) /\ getr rg 21 = Z_to_bv 64 m
                        /\ (forall r : reg, In r [2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r)).
        { eexists. split.
          - zstep Fx_82d30 Dx_82d30. zstep Fx_82d34 Dx_82d34. zstep Fx_82d38 Dx_82d38. zstep Fx_82d3c Dx_82d3c. rewrite ann_andi_7 by lia. rewrite B8.
            zbft Fx_82d40 Dx_82d40. zstep Fx_82d44 Dx_82d44. zstep Fx_82d48 Dx_82d48. zbft Fx_82d4c Dx_82d4c.
            zstep Fx_82d50 Dx_82d50. rewrite ann_andi_m8 by lia. zbft Fx_82d54 Dx_82d54.
            zstep Fx_82d58 Dx_82d58. rewrite ann_andi_m8 by lia. zstep Fx_82d5c Dx_82d5c. zstep Fx_82d60 Dx_82d60. rewrite ann_andi_m8 by lia.
            zbtk Fx_82d64 Dx_82d64.
            zstep Fx_82e38 Dx_82e38. zstep Fx_82e3c Dx_82e3c. rewrite ann_andi_m8 by lia.
            zbft Fx_82e40 Dx_82e40.
            zstep Fx_82e44 Dx_82e44. zstep Fx_82e48 Dx_82e48. zstep Fx_82e4c Dx_82e4c.
            apply mst_refl.
          - split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. keepr. }
        destruct PRE as (rgA & RUNA & A2 & A10 & A11 & A12 & A9 & A18 & A21 & KA).
        destruct (ann_poison M rgA ((m + 7) / 8 * 8) ((o + 7) / 8 * 8 - (m + 7) / 8 * 8) 252 LM WM WSH A2 A10 A11 A12 ltac:(lia)
                    ltac:(apply Z_mod_mult) ltac:(replace ((o + 7) / 8 * 8 - (m + 7) / 8 * 8) with (((o + 7) / 8 - (m + 7) / 8) * 8) by ring; apply Z_mod_mult) ltac:(lia) ltac:(lia) ltac:(right; reflexivity))
          as (rgB & M' & RUNB & KB & GRB & FRB & FLB).
        assert (Q1 : (m + 7) / 8 * 8 / 8 = (m + 7) / 8) by (apply Z.div_mul; lia).
        assert (Q2 : ((m + 7) / 8 * 8 + ((o + 7) / 8 * 8 - (m + 7) / 8 * 8)) / 8 = (o + 7) / 8) by (replace ((m + 7) / 8 * 8 + ((o + 7) / 8 * 8 - (m + 7) / 8 * 8)) with ((o + 7) / 8 * 8) by ring; apply Z.div_mul; lia).
        rewrite Q1, Q2 in FRB, FLB.
        exists rgB, M'. split; [eapply msteps_trans; [exact RUNA|exact RUNB]|].
        split; [rewrite (KB 9%bv) by (cbn [In]; tauto); exact A9|]. split; [rewrite (KB 18%bv) by (cbn [In]; tauto); exact A18|]. split; [rewrite (KB 21%bv) by (cbn [In]; tauto); exact A21|].
        split. { intros r Hr. rewrite (KB r) by (cbn [In] in Hr |- *; tauto). exact (KA r Hr). }
        split; [exact GRB|]. rewrite ELO, EHI, EV. split; [exact FRB|exact FLB].
      + assert (SEG : exists rg, msteps ASEGS (mkst regs (0x82d80 : word) M rom) (mkst rg (0x82ea4 : word) M rom)
                        /\ getr rg 9 = Z_to_bv 64 (m / 8 * 8) /\ getr rg 18 = Z_to_bv 64 ((m + 7) / 8 * 8) /\ getr rg 21 = Z_to_bv 64 m
                        /\ (forall r : reg, In r [2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r)).
        { eexists. split.
          - zstep Fx_82d30 Dx_82d30. zstep Fx_82d34 Dx_82d34. zstep Fx_82d38 Dx_82d38. zstep Fx_82d3c Dx_82d3c. rewrite ann_andi_7 by lia. rewrite B8.
            zbft Fx_82d40 Dx_82d40. zstep Fx_82d44 Dx_82d44. zstep Fx_82d48 Dx_82d48. zbft Fx_82d4c Dx_82d4c.
            zstep Fx_82d50 Dx_82d50. rewrite ann_andi_m8 by lia. zbft Fx_82d54 Dx_82d54.
            zstep Fx_82d58 Dx_82d58. rewrite ann_andi_m8 by lia. zstep Fx_82d5c Dx_82d5c. zstep Fx_82d60 Dx_82d60. rewrite ann_andi_m8 by lia.
            zbtk Fx_82d64 Dx_82d64.
            zstep Fx_82e38 Dx_82e38. zstep Fx_82e3c Dx_82e3c. rewrite ann_andi_m8 by lia.
            zbtk Fx_82e40 Dx_82e40.
            apply mst_refl.
          - split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. keepr. }
        destruct SEG as (rg & RUN & F9 & F18 & F21 & KR). exists rg, M. split; [exact RUN|]. split; [exact F9|]. split; [exact F18|]. split; [exact F21|]. split; [exact KR|].
        split; [apply mem_grows_refl|]. split; [intros x _ _; reflexivity|]. intros j Hj. exfalso. rewrite ELO, EHI in Hj. clear - Hj NP RBn1 RBn2. lia.
  Qed.

  Lemma ann_L3 : forall (M : word -> option byte) regs, art_layout M -> wrA M (0x7fff8000 + b / 8) ((e - b + 7) / 8) ->
    getr regs 9 = Z_to_bv 64 (m / 8 * 8) -> getr regs 18 = Z_to_bv 64 ((m + 7) / 8 * 8) -> getr regs 21 = Z_to_bv 64 m ->
    exists regs', msteps ASEGS (mkst regs (0x82ea4 : word) M rom) (mkst regs' (0x82ec4 : word) (if Z.eq_dec (m mod 8) 0 then M else Wn 1 M (0x7fff8000 + m / 8) (m mod 8)) rom)
      /\ (forall r : reg, In r [2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
  Proof.
    intros M regs LM WSH H9 H18 H21. destruct Hb as (B0 & B8 & (Bo1 & Bo2) & (Bm1 & Bm2) & E47 & EB).
    pose proof (Z.div_mod m 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as Rm.
    pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite B8, Z.add_0_r in Db.
    assert (RB0 : m mod 8 = 0 -> (m + 7) / 8 * 8 = m / 8 * 8) by (pose proof (Z.div_mod (m + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (m + 7) 8 ltac:(lia)); lia).
    assert (RB8 : m mod 8 <> 0 -> (m + 7) / 8 * 8 - m / 8 * 8 = 8) by (pose proof (Z.div_mod (m + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (m + 7) 8 ltac:(lia)); lia).
    assert (RBm : b <= m / 8 * 8 <= m) by lia.
    assert (RBlt : m mod 8 <> 0 -> m / 8 * 8 < m) by lia.
    assert (RBs : m mod 8 <> 0 -> b / 8 <= m / 8 /\ m / 8 + 1 <= b / 8 + (e - b + 7) / 8)
      by (pose proof (Z.div_mod (e - b + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (e - b + 7) 8 ltac:(lia)); lia).
    clear Dm Db.
    destruct (Z.eq_dec (m mod 8) 0) as [E0|N0].
    - eexists. split; [zbtk Fx_82e54 Dx_82e54; apply mst_refl|]. keepr.
    - assert (PRE : exists rg, msteps ASEGS (mkst regs (0x82ea4 : word) M rom) (mkst rg (0x82214 : word) M rom)
                      /\ getr rg 1 = (0x82ec0%bv : word) /\ getr rg 10 = Z_to_bv 64 (m / 8 * 8) /\ getr rg 18 = Z_to_bv 64 (m mod 8)
                      /\ (forall r : reg, In r [2; 3; 4; 8; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r)).
      { eexists. split.
        - zbft Fx_82e54 Dx_82e54. zstep Fx_82e58 Dx_82e58. zstep Fx_82e5c Dx_82e5c. zbft Fx_82e60 Dx_82e60.
          zstep Fx_82e64 Dx_82e64. rewrite ann_andi_7 by lia. zstep Fx_82e68 Dx_82e68. stepn Fx_82e6c Dx_82e6c.
          apply mst_refl.
        - split; [gres; first [reflexivity | apply bv_eq; reflexivity]|]. split; [gres; rwH; zval|]. split; [gres; rwH; zval|]. keepr. }
      destruct PRE as (rgA & RUNA & A1 & A10 & A18 & KA).
      assert (GLOB : rt_layout_globs M).
      { destruct LM as (A1' & A2' & A3' & A4' & A5' & A6' & A7' & A8' & _). unfold rt_layout_globs, cell, Pm8ArtPoison.SB, Pm8RegionPoisoned.SB, kHighMemEnd, HIGHEND in *.
        repeat split; match goal with |- rdn _ _ ?w _ = _ => match goal with H : rdn _ _ (Z_to_bv 64 ?a) _ = _ |- _ => replace w with (Z_to_bv 64 a : word) by (apply bv_eq; reflexivity); exact H end end. }
      destruct (memtoshadow_run rgA M rom (0x82ec0%bv : word) (m / 8 * 8) GLOB
                  ltac:(unfold in_app, LOWEND, HIGHBEG, HIGHEND; unfold kHighMemBeg, kHighMemEnd in Happ; clear - Happ Bm1 Bm2 RBm RBlt N0 B0; lia) A10 A1 ltac:(unfold ret_ok; bveq))
        as (rgB & RUNB & B10 & KB).
      assert (Q : m / 8 * 8 / 8 = m / 8) by (apply Z.div_mul; lia). rewrite Q in B10. unfold Pm8RegionPoisoned.SB in B10.
      assert (B18 : getr rgB 18 = Z_to_bv 64 (m mod 8)) by (rewrite (KB 18%bv) by (unfold callee_saved; cbn [In]; tauto); exact A18).
      assert (FIN : exists rg, msteps ASEGS (mkst rgB (0x82ec0%bv : word) M rom) (mkst rg (0x82ec4 : word) (Wn 1 M (0x7fff8000 + m / 8) (m mod 8)) rom)
                      /\ (forall r : reg, getr rg r = getr rgB r)).
      { eexists. split.
        - zsb Fx_82e70 Dx_82e70 (0x7fff8000 + m / 8) (m mod 8) ltac:(eapply (wr_wok _ _ _ _ WSH); cbn [Z.of_nat Pos.to_nat]; clear - RBs N0; lia).
          apply mst_refl.
        - intros r. reflexivity. }
      destruct FIN as (rgC & RUNC & KC).
      exists rgC. split; [eapply msteps_trans; [exact RUNA|]; eapply msteps_trans; [exact RUNB|exact RUNC]|].
      intros r Hr. rewrite KC. rewrite <- (KA r Hr). apply KB. cbn [In] in Hr. unfold callee_saved. cbn [In]. tauto.
  Qed.

  Lemma ann_epi : forall (M : word -> option byte) regs (v1 v8 v9 v18 v19 v20 v21 : Z), getr regs 2 = Z_to_bv 64 (s - 2128) -> ret_ok (Z_to_bv 64 v1) ->
    cellA M (s - 8) 8 v1 -> cellA M (s - 16) 8 v8 -> cellA M (s - 24) 8 v9 -> cellA M (s - 32) 8 v18 -> cellA M (s - 40) 8 v19 -> cellA M (s - 48) 8 v20 -> cellA M (s - 56) 8 v21 ->
    exists regs', msteps ASEGS (mkst regs (0x82ec4 : word) M rom) (mkst regs' (Z_to_bv 64 v1) M rom)
      /\ getr regs' 1 = Z_to_bv 64 v1 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = Z_to_bv 64 v8 /\ getr regs' 9 = Z_to_bv 64 v9 /\ getr regs' 18 = Z_to_bv 64 v18
      /\ getr regs' 19 = Z_to_bv 64 v19 /\ getr regs' 20 = Z_to_bv 64 v20 /\ getr regs' 21 = Z_to_bv 64 v21
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
  Proof.
    intros M regs v1 v8 v9 v18 v19 v20 v21 H2 Hret C1 C8 C9 C18 C19 C20 C21.
    eexists. split.
    - zstep Fx_82e74 Dx_82e74.
      zld Fx_82e78 Dx_82e78 (s - 8) C1. zld Fx_82e7c Dx_82e7c (s - 16) C8. zld Fx_82e80 Dx_82e80 (s - 24) C9. zld Fx_82e84 Dx_82e84 (s - 32) C18.
      zld Fx_82e88 Dx_82e88 (s - 40) C19. zld Fx_82e8c Dx_82e8c (s - 48) C20. zld Fx_82e90 Dx_82e90 (s - 56) C21.
      zstep Fx_82e94 Dx_82e94.
      stepret Fx_82e98 Dx_82e98 (Z_to_bv 64 v1) ltac:(reflexivity).
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; rwH; zval|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
      split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. keepr.
  Qed.

  Hypothesis Hret : ret_ok raw.
  Hypothesis WSH : wrA M0 (0x7fff8000 + b / 8) ((e - b + 7) / 8).
  Hypothesis HEND : e mod 8 <> 0 -> exists sv, cellA M0 (0x7fff8000 + e / 8) 1 sv /\ (sv = 252 \/ (1 <= sv <= 7 /\ sv <= e mod 8)).

  Theorem ann_run : forall regs, getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s ->
    getr regs 10 = Z_to_bv 64 b -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 o -> getr regs 13 = Z_to_bv 64 m ->
    exists regs' M1, msteps ASEGS (mkst regs (0x82c5c : word) M0 rom) (mkst regs' raw M1 rom)
      /\ keeps_cs regs regs' /\ mem_grows M0 M1
      /\ (forall x : word, ~ (s - 2192 <= U x < s) -> ~ (o <> m /\ 0x7fff8000 + ann_lo <= U x < 0x7fff8000 + ann_hi) -> ~ (o <> m /\ m mod 8 <> 0 /\ U x = 0x7fff8000 + m / 8) -> M1 x = M0 x)
      /\ (o <> m -> forall j, ann_lo <= j < ann_hi -> M1 (Z_to_bv 64 (0x7fff8000 + j)) = Some (Z_to_bv 8 ann_v))
      /\ (o <> m -> m mod 8 <> 0 -> M1 (Z_to_bv 64 (0x7fff8000 + m / 8)) = Some (Z_to_bv 8 (m mod 8))).
  Proof.
    intros regs H1 H2 H10 H11 H12 H13.
    destruct (ann_L1a regs H1 H2 H10 H11 H12 H13) as (rg1 & RUN1 & A2 & A9 & A18 & A19 & A20 & K1).
    set (MF := ann_frame M0 s (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) in *.
    pose proof Hb as (B0 & B8 & (Bo1 & Bo2) & (Bm1 & Bm2) & E47 & EB).
    pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite B8, Z.add_0_r in Db.
    pose proof (Z.div_mod (e + 7) 8 ltac:(lia)) as De7. pose proof (Z.mod_pos_bound (e + 7) 8 ltac:(lia)) as Re7.
    assert (GRF : mem_grows M0 MF) by (unfold MF, ann_frame; repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl).
    assert (FRF : forall x : word, ~ (s - 2192 <= U x < s) -> MF x = M0 x).
    { intros x X. unfold MF, ann_frame. rewrite !Wn_outside by (cbn [Z.of_nat Pos.to_nat]; clear - Hs X; lia). reflexivity. }
    assert (CF1 : cellA MF (s - 8) 8 (U raw)) by (unfold MF, ann_frame; zcell).
    assert (CF8 : cellA MF (s - 16) 8 (U (getr regs 8))) by (unfold MF, ann_frame; zcell).
    assert (CF9 : cellA MF (s - 24) 8 (U (getr regs 9))) by (unfold MF, ann_frame; zcell).
    assert (CF18 : cellA MF (s - 32) 8 (U (getr regs 18))) by (unfold MF, ann_frame; zcell).
    assert (CF19 : cellA MF (s - 40) 8 (U (getr regs 19))) by (unfold MF, ann_frame; zcell).
    assert (CF20 : cellA MF (s - 48) 8 (U (getr regs 20))) by (unfold MF, ann_frame; zcell).
    assert (CF21 : cellA MF (s - 56) 8 (U (getr regs 21))) by (unfold MF, ann_frame; zcell).
    assert (RETU : ret_ok (Z_to_bv 64 (U raw))) by (rewrite Z_to_bv_bv_unsigned; exact Hret).

    assert (FINR : forall rgE : bvmap 5 word, getr rgE 1 = Z_to_bv 64 (U raw) -> getr rgE 2 = Z_to_bv 64 s -> getr rgE 8 = Z_to_bv 64 (U (getr regs 8)) -> getr rgE 9 = Z_to_bv 64 (U (getr regs 9)) ->
               getr rgE 18 = Z_to_bv 64 (U (getr regs 18)) -> getr rgE 19 = Z_to_bv 64 (U (getr regs 19)) -> getr rgE 20 = Z_to_bv 64 (U (getr regs 20)) -> getr rgE 21 = Z_to_bv 64 (U (getr regs 21)) ->
               (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr rgE r = getr regs r) -> keeps_cs regs rgE).
    { intros rgE E1 E2 E8 E9 E18 E19 E20 E21 EK r Hr. unfold callee_saved in Hr. cbn [In] in Hr. rewrite Z_to_bv_bv_unsigned in *.
      destruct Hr as [<- | Hr]; [rewrite E1; symmetry; exact H1|]. destruct Hr as [<- | Hr]; [rewrite E2; symmetry; exact H2|].
      destruct Hr as [<- | Hr]; [apply EK; cbn [In]; repeat first [left; reflexivity | right]|]. destruct Hr as [<- | Hr]; [apply EK; cbn [In]; repeat first [left; reflexivity | right]|].
      destruct Hr as [<- | Hr]; [exact E8|]. destruct Hr as [<- | Hr]; [exact E9|]. destruct Hr as [<- | Hr]; [exact E18|]. destruct Hr as [<- | Hr]; [exact E19|].
      destruct Hr as [<- | Hr]; [exact E20|]. destruct Hr as [<- | Hr]; [exact E21|].
      repeat (destruct Hr as [<- | Hr]; [apply EK; cbn [In]; repeat first [left; reflexivity | right]|]). destruct Hr. }
    destruct (Z.eq_dec o m) as [Eom|Nom].
    -
      assert (SEG : exists rg, msteps ASEGS (mkst rg1 (0x82d74 : word) MF rom) (mkst rg (0x82ec4 : word) MF rom) /\ (forall r : reg, getr rg r = getr rg1 r)).
      { eexists. split; [zbtk Fx_82d24 Dx_82d24; apply mst_refl|]. intros r. reflexivity. }
      destruct SEG as (rg2 & RUN2 & K2).
      destruct (ann_epi MF rg2 (U raw) _ _ _ _ _ _ ltac:(rewrite K2; exact A2) RETU CF1 CF8 CF9 CF18 CF19 CF20 CF21) as (rgE & RUNE & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & KE).
      exists rgE, MF. split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. rewrite Z_to_bv_bv_unsigned in RUNE. exact RUNE. }
      split. { apply FINR; try assumption. intros r Hr. rewrite (KE r Hr), K2. exact (K1 r Hr). }
      split; [exact GRF|]. split; [intros x X _ _; exact (FRF x X)|]. split; intros X; contradiction.
    -
      destruct LAY as (L1 & L2 & _).
      assert (LAYF : art_layout MF) by (apply (ann_layout_agree M0 MF LAY); intros x Hx; apply FRF; clear - Hx Hs; lia).
      assert (HENDF : e mod 8 <> 0 -> exists sv, cellA MF (0x7fff8000 + e / 8) 1 sv /\ (sv = 252 \/ (1 <= sv <= 7 /\ sv <= e mod 8))).
      { intros N0. destruct (HEND N0) as (sv & C & V). exists sv. split; [|exact V].
        apply (art_cell_agree ASEGS M0 MF); [|clear - E47 B0 Bo1 Bo2; assert (0 <= e / 8) by (apply Z.div_pos; lia); lia| |exact C].
        - intros x Hx. apply FRF. cbn in Hx. assert (e / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). clear - Hx Hs H. lia.
        - cbn. assert (e / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
      destruct LAYF as (LF1 & LF2 & LFR). unfold Pm8ArtPoison.SB in LF2.
      destruct (ann_L1b MF rg1 LF1 LF2 HENDF Nom A9 A18 A19 A20) as (rg2 & RUN2 & C9 & C18 & C19 & K2).
      assert (LAYF : art_layout MF) by (apply (ann_layout_agree M0 MF LAY); intros x Hx; apply FRF; clear - Hx Hs; lia).
      destruct (ann_L2 MF rg2 LAYF ltac:(unfold MF, ann_frame; zwr) ltac:(unfold MF, ann_frame; zwr) Nom ltac:(rewrite (K2 2%bv) by (cbn [In]; repeat first [left; reflexivity | right]); exact A2) C9 C18 C19)
        as (rg3 & M2 & RUN3 & D9 & D18 & D21 & K3 & GR2 & FR2 & FL2).
      assert (LOHI : b / 8 <= ann_lo /\ ann_hi <= (e + 7) / 8).
      { assert (Q1 : b / 8 <= o / 8 /\ b / 8 <= m / 8) by (split; apply Z.div_le_mono; lia).
        assert (Q2 : m / 8 <= (e + 7) / 8 /\ (o + 7) / 8 <= (e + 7) / 8 /\ (m + 7) / 8 <= (e + 7) / 8) by (repeat split; apply Z.div_le_mono; lia).
        assert (Q3 : m / 8 <= (m + 7) / 8) by (apply Z.div_le_mono; lia).
        unfold ann_lo, ann_hi. destruct (o <? m); clear - Q1 Q2 Q3; lia. }
      assert (SHB : 0x7fff8000 + (e + 7) / 8 <= 0x10007fff8000) by (clear - E47 De7 Re7; lia).
      assert (LAY2 : art_layout M2).
      { apply (ann_layout_agree MF M2 LAYF). intros x Hx. apply FR2; [clear - Hx Hs; lia|]. clear - Hx LOHI B0 Db. lia. }
      destruct (ann_L3 M2 rg3 LAY2 ltac:(apply (wr_grows _ _ _ _ _ GR2); unfold MF, ann_frame; zwr) D9 D18 D21) as (rg4 & RUN4 & K4).
      set (M3 := if Z.eq_dec (m mod 8) 0 then M2 else Wn 1 M2 (0x7fff8000 + m / 8) (m mod 8)) in *.
      assert (MDIV : b / 8 <= m / 8 < (e + 7) / 8 \/ m mod 8 = 0).
      { pose proof (Z.div_mod m 8 ltac:(lia)). pose proof (Z.mod_pos_bound m 8 ltac:(lia)). destruct (Z.eq_dec (m mod 8) 0); [right; assumption|left; lia]. }
      assert (FR3 : forall x : word, ~ (m mod 8 <> 0 /\ U x = 0x7fff8000 + m / 8) -> M3 x = M2 x).
      { intros x X. unfold M3. destruct (Z.eq_dec (m mod 8) 0) as [E0|N0]; [reflexivity|]. apply Wn_outside; [clear - MDIV N0 B0 Db; lia|cbn; clear - MDIV N0 SHB; lia|cbn; clear - X N0; lia]. }
      assert (GR3 : mem_grows M2 M3) by (unfold M3; destruct (Z.eq_dec (m mod 8) 0); [apply mem_grows_refl|apply Wn_grows]).
      assert (STK : forall x : word, s - 56 <= U x < s -> M3 x = MF x).
      { intros x Hx. rewrite FR3 by (clear - Hx Hs MDIV SHB; lia). apply FR2; [clear - Hx; lia|clear - Hx Hs LOHI SHB; lia]. }
      assert (CT : forall a v, s - 56 <= a -> a + 8 <= s -> cellA MF a 8 v -> cellA M3 a 8 v).
      { intros a v Ha Ha' C. apply (art_cell_agree ASEGS MF M3); [|clear - Ha Hs; lia|cbn; clear - Ha' Hs; lia|exact C]. intros x Hx. apply STK. cbn in Hx. clear - Hx Ha Ha'. lia. }
      destruct (ann_epi M3 rg4 (U raw) _ _ _ _ _ _ ltac:(rewrite (K4 2%bv) by (cbn [In]; repeat first [left; reflexivity | right]); rewrite (K3 2%bv) by (cbn [In]; repeat first [left; reflexivity | right]); rewrite (K2 2%bv) by (cbn [In]; repeat first [left; reflexivity | right]); exact A2) RETU
                  (CT (s - 8) _ ltac:(lia) ltac:(lia) CF1) (CT (s - 16) _ ltac:(lia) ltac:(lia) CF8) (CT (s - 24) _ ltac:(lia) ltac:(lia) CF9) (CT (s - 32) _ ltac:(lia) ltac:(lia) CF18)
                  (CT (s - 40) _ ltac:(lia) ltac:(lia) CF19) (CT (s - 48) _ ltac:(lia) ltac:(lia) CF20) (CT (s - 56) _ ltac:(lia) ltac:(lia) CF21))
        as (rgE & RUNE & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & KE).
      exists rgE, M3. split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. rewrite Z_to_bv_bv_unsigned in RUNE. exact RUNE. }
      split. { apply FINR; try assumption. intros r Hr. cbn [In] in Hr.
               repeat (destruct Hr as [<- | Hr]; [rewrite KE by (cbn [In]; repeat first [left; reflexivity | right]); rewrite K4 by (cbn [In]; repeat first [left; reflexivity | right]); rewrite K3 by (cbn [In]; repeat first [left; reflexivity | right]); rewrite K2 by (cbn [In]; repeat first [left; reflexivity | right]); apply K1; cbn [In]; repeat first [left; reflexivity | right]|]). destruct Hr. }
      split; [eapply mem_grows_trans; [exact GRF|]; eapply mem_grows_trans; [exact GR2|exact GR3]|].
      split. { intros x X1 X2 X3. rewrite FR3 by (intros (P & Q); apply X3; repeat split; assumption). rewrite FR2; [apply FRF; exact X1|clear - X1; lia|intros R; apply X2; split; [exact Nom|exact R]]. }
      split. { intros _ j Hj. rewrite FR3; [exact (FL2 j Hj)|]. rewrite art_u_lit by (clear - Hj LOHI SHB B0 Db; lia). intros (N0 & Q).
               assert (Q4 : m / 8 < (m + 7) / 8) by (pose proof (Z.div_mod m 8 ltac:(lia)); pose proof (Z.mod_pos_bound m 8 ltac:(lia)); pose proof (Z.div_mod (m + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (m + 7) 8 ltac:(lia)); lia).
               unfold ann_lo, ann_hi in Hj. destruct (o <? m); clear - Hj Q Q4; lia. }
      intros _ N0. unfold M3. destruct (Z.eq_dec (m mod 8) 0) as [E0|_]; [contradiction|].
      assert (RM : 0 <= m mod 8 < 8) by (apply Z.mod_pos_bound; lia).
      unfold Wn. rewrite (art_bytes1 (m mod 8)) by (clear - RM; lia). change [Z_to_bv 8 (m mod 8)] with (repeat (Z_to_bv 8 (m mod 8)) 1). fold (Wf M2 (0x7fff8000 + m / 8) 1 (m mod 8)).
      replace (Z_to_bv 64 (0x7fff8000 + m / 8)) with (Z_to_bv 64 (0x7fff8000 + m / 8 + 0)) by (f_equal; ring).
      apply Wf_inside; [clear - MDIV N0 B0 Db; lia|cbn; clear - MDIV N0 SHB; lia|cbn; lia].
  Qed.
End WALK.
End FPX.
