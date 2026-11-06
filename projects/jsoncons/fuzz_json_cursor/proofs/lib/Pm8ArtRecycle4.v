(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm8ArtLeaf Pm8ArtAllocG Pm8ArtPoison ArtRuns ArtRunsMem Pm8ArtFp Pm8ArtFree1 Pm8ArtPopulate1 Pm8ArtCellEx Pm8ArtRecycle3.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5b000_5c000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac zcl4 := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ =>
  let v := eval vm_compute in (bv_unsigned x) in replace x with (Z_to_bv 64 v : word) by (apply bv_eq; vm_compute; reflexivity) end.

Lemma art_zb_divuw : forall x y, 0 <= x < 2 ^ 64 -> 0 < y < 2 ^ 32 -> (x mod 2 ^ 32) / y < 2 ^ 31 ->
  v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 ((x mod 2 ^ 32) / y).
Proof.
  intros x y Hx Hy Hq. unfold v_divuw. rewrite !art_u_lit by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  assert (0 <= x mod 2 ^ 32 / y) by (apply Z.div_pos; [apply Z.mod_pos_bound|]; lia).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_land_31 : forall c, 0 <= c < 32 -> Z.land c 31 = c.
Proof. intros c Hc. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Definition art_cas30w_ok (b1 : Z) : bool :=
  bv_eqb (v_xor (Z_to_bv 64 (3 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (3 + 256 * b1)) (Z_to_bv 64 0)) (Z_to_bv 64 255))) (Z_to_bv 64 (256 * b1)).
Lemma art_cas30w_all : forallb art_cas30w_ok (AsanTab.zrange 0 256) = true.
Proof. vmc_refl. Qed.
Lemma art_cas30w : forall b1, 0 <= b1 < 256 ->
  v_xor (Z_to_bv 64 (3 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (3 + 256 * b1)) (Z_to_bv 64 0)) (Z_to_bv 64 255)) = Z_to_bv 64 (256 * b1).
Proof.
  intros b1 Hb. pose proof art_cas30w_all as H. rewrite forallb_forall in H.
  specialize (H b1 ltac:(unfold AsanTab.zrange; apply AsanTab.in_ziota; rewrite Z2Nat.id by lia; lia)). unfold art_cas30w_ok, bv_eqb in H.
  apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Ltac zlhu4 F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].
Lemma art_zb_or4 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_cbr_pa1 : forall regs (M rom : word -> option byte) (raw : word) (sp cb m spb c off : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 cb -> getr regs 11 = Z_to_bv 64 m ->
  0x6b3000 + 48 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 48) 48 -> 0 <= cb < 2 ^ 64 ->
  0x6b3000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 1 <= c <= 30 -> 0 <= off < 2 ^ 32 -> m = spb + c * 2 ^ 32 + off ->
  cellA M (1413976 + 32) 8 spb ->
  exists regs', msteps ASEGS (mkst regs (0x5b76c : word) M rom) (mkst regs' (0x5b81c : word) (art_f48 M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 8 = Z_to_bv 64 cb /\ getr regs' 9 = Z_to_bv 64 m /\ getr regs' 19 = Z_to_bv 64 1413976
    /\ getr regs' 20 = Z_to_bv 64 (2 ^ 37) /\ getr regs' 10 = Z_to_bv 64 spb /\ getr regs' 11 = Z_to_bv 64 (spb + 2 ^ 37) /\ getr regs' 12 = Z_to_bv 64 c
    /\ getr regs' 13 = Z_to_bv 64 c /\ getr regs' 14 = Z_to_bv 64 (m - spb) /\ getr regs' 15 = Z_to_bv 64 (AsanTab.class_size c)
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp cb m spb c off H1 H2 H10 H11 Hsp Hsp' W Hcb Hspb Hspb' Hc Hoff Em Cspb.
  assert (Ediv : (m - spb) / 2 ^ 32 = c).
  { symmetry. apply (Z.div_unique_pos (m - spb) (2 ^ 32) c off); lia. }
  destruct (Z_le_gt_dec c 16) as [Lc|Gc].
  - eexists. split.
    { zstep F_5b71c D_5b71c.
      zsd F_5b720 D_5b720 (sp - 8) (U raw) ltac:(rewok W). zsd F_5b724 D_5b724 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_5b728 D_5b728 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5b72c D_5b72c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_5b730 D_5b730 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5b734 D_5b734 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zstep F_5b738 D_5b738. zstep F_5b73c D_5b73c.
      stepn F_5b740 D_5b740. stepn F_5b744 D_5b744. zcl4.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1413976 + 32) 8 spb) by zcell end.
      zld F_5b748 D_5b748 (1413976 + 32) Cspb'.
      zstep F_5b74c D_5b74c. zstep F_5b750 D_5b750.
      zbft F_5b754 D_5b754.
      zstep F_5b758 D_5b758.
      zbft F_5b75c D_5b75c.
      zstep F_5b760 D_5b760.
      stepn F_5b764 D_5b764. rwH. rewrite (art_zb_srli (m - spb) 32) by lia. rewrite Ediv.
      stepn F_5b768 D_5b768. rwH. rewrite (art_zb_andi c 31) by lia. rewrite (art_land_31 c) by lia.
      zstep F_5b76c D_5b76c.
      zbft F_5b770 D_5b770.
      zstep F_5b774 D_5b774.
      zbft F_5b778 D_5b778.
      zbft F_5b77c D_5b77c.
      zstep F_5b780 D_5b780.
      stepn F_5b784 D_5b784.
      unfold art_f48. apply mst_refl. }
    rewrite (art_class_size_small c ltac:(lia)).
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; f_equal; lia|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zstep F_5b71c D_5b71c.
      zsd F_5b720 D_5b720 (sp - 8) (U raw) ltac:(rewok W). zsd F_5b724 D_5b724 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_5b728 D_5b728 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5b72c D_5b72c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_5b730 D_5b730 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5b734 D_5b734 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zstep F_5b738 D_5b738. zstep F_5b73c D_5b73c.
      stepn F_5b740 D_5b740. stepn F_5b744 D_5b744. zcl4.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1413976 + 32) 8 spb) by zcell end.
      zld F_5b748 D_5b748 (1413976 + 32) Cspb'.
      zstep F_5b74c D_5b74c. zstep F_5b750 D_5b750.
      zbft F_5b754 D_5b754.
      zstep F_5b758 D_5b758.
      zbft F_5b75c D_5b75c.
      zstep F_5b760 D_5b760.
      stepn F_5b764 D_5b764. rwH. rewrite (art_zb_srli (m - spb) 32) by lia. rewrite Ediv.
      stepn F_5b768 D_5b768. rwH. rewrite (art_zb_andi c 31) by lia. rewrite (art_land_31 c) by lia.
      zstep F_5b76c D_5b76c.
      zbft F_5b770 D_5b770.
      zstep F_5b774 D_5b774.
      zbtk F_5b778 D_5b778.
      zstep F_5b7a8 D_5b7a8. zstep F_5b7ac D_5b7ac. zstep F_5b7b0 D_5b7b0. zstep F_5b7b4 D_5b7b4. zstep F_5b7b8 D_5b7b8. zstep F_5b7bc D_5b7bc.
      zstep F_5b7c0 D_5b7c0. zstep F_5b7c4 D_5b7c4. zstep F_5b7c8 D_5b7c8.
      fold (art_pop_szw c). rewrite (art_pop_szw_ok c ltac:(lia)).
      unfold art_f48. apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_cbr_pa2 : forall regs (M rom : word -> option byte) (m spb ris c off i mu : Z),
  let sz := AsanTab.class_size c in
  getr regs 10 = Z_to_bv 64 spb -> getr regs 11 = Z_to_bv 64 (spb + 2 ^ 37) -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 c ->
  getr regs 14 = Z_to_bv 64 (m - spb) -> getr regs 15 = Z_to_bv 64 sz -> getr regs 19 = Z_to_bv 64 1413976 ->
  0x6b3000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> ris = spb + 2 ^ 37 -> 1 <= c <= 30 -> 0 <= off < 2 ^ 32 -> m = spb + c * 2 ^ 32 + off ->
  0 <= i -> sz * i <= off < sz * (i + 1) -> sz * i + sz <= mu -> mu <= 3758096384 ->
  cellA M (1413976 + 48) 8 ris -> cellA M (ris + 128 * c + 48) 8 mu ->
  exists regs', msteps ASEGS (mkst regs (0x5b81c : word) M rom) (mkst regs' (0x5b860 : word) M rom)
    /\ getr regs' 18 = Z_to_bv 64 (spb + c * 2 ^ 32 + sz * i)
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom m spb ris c off i mu sz H10 H11 H12 H13 H14 H15 H19 Hspb Hspb' Eris Hc Hoff Em Hi Hoi Hmu Hmu' Cris Cmu.
  pose proof (art_class_size_facts c Hc) as (Hsz & _). fold sz in Hsz.
  assert (Emod : (m - spb) mod 2 ^ 32 = off).
  { symmetry. apply (Z.mod_unique_pos (m - spb) (2 ^ 32) c off); lia. }
  assert (Eq : off / sz = i).
  { symmetry. apply (Z.div_unique_pos off sz i (off - sz * i)); lia. }
  assert (Hi' : i < 2 ^ 27). { assert (sz * i < 2 ^ 32) by lia. nia. }
  eexists. split.
  { stepn F_5b7cc D_5b7cc. rwH. rewrite (art_zb_divuw (m - spb) sz) by (rewrite ?Emod, ?Eq; lia). rewrite Emod, Eq.
    zstep F_5b7d0 D_5b7d0.
    zld F_5b7d4 D_5b7d4 (1413976 + 48) Cris.
    zstep F_5b7d8 D_5b7d8. zstep F_5b7dc D_5b7dc. zstep F_5b7e0 D_5b7e0. zstep F_5b7e4 D_5b7e4.
    zld F_5b7e8 D_5b7e8 (ris + 128 * c + 48) Cmu.
    stepn F_5b7ec D_5b7ec. rwH. rewrite (art_zb_srli_exact _ 32 i) by lia.
    zstep F_5b7f0 D_5b7f0. zstep F_5b7f4 D_5b7f4. zstep F_5b7f8 D_5b7f8. zstep F_5b7fc D_5b7fc. zstep F_5b800 D_5b800.
    stepn F_5b804 D_5b804. rwH. rewrite (art_zb_and 18446744073709551615 (c * 2 ^ 32 + spb + sz * i)) by lia. rewrite art_land_full_l by lia.
    zbft F_5b808 D_5b808.
    zbft F_5b80c D_5b80c.
    apply mst_refl. }
  split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_cbr_magic : forall regs (M rom : word -> option byte) (m ab : Z),
  getr regs 9 = Z_to_bv 64 m -> getr regs 18 = Z_to_bv 64 ab ->
  0x6b3000 <= ab -> ab + 8 < 2 ^ 47 -> 0 <= m < 2 ^ 64 -> ab mod 8 = 0 ->
  cellA M 0x10378 8 0xcc6e96b9cc6e96b9 ->
  (ab <> m -> cellA M ab 8 0xcc6e96b9cc6e96b9 /\ wrA M ab 8) ->
  exists regs', msteps ASEGS (mkst regs (0x5b860 : word) M rom) (mkst regs' (0x5b87c : word) (if ab =? m then M else Wn 8 M ab 0) rom)
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom m ab H9 H18 Hab Hab' Hm Hab8 Cmag Hne.
  destruct (Z.eqb_spec ab m) as [E|NE].
  - eexists. split.
    { zbtk F_5b810 D_5b810. apply mst_refl. }
    intros r Hr. reflexivity.
  - destruct (Hne NE) as [Cab Wab].
    eexists. split.
    { zbft F_5b810 D_5b810.
      stepn F_5b814 D_5b814. zcl4.
      zld F_5b818 D_5b818 0x10378 Cmag.
      chain_step; [reflexivity
        | eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ab) _ (Z_to_bv 64 0xcc6e96b9cc6e96b9));
          [exact F_5b81c | reflexivity | exact D_5b81c | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hab8
          | exact Cab | apply bytes_le_to_Z_8 ]
        | ]. wpc.
      chain_step; [reflexivity
        | eapply art_step_branch_ft_r; [exact F_5b820 | reflexivity | exact D_5b820 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
        | ]. wpc.
      chain_step; [reflexivity
        | eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ab));
          [exact F_5b824 | reflexivity | exact D_5b824 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hab8 | gres; rwH; reflexivity
          | eapply (wr_wok _ _ _ _ Wab); lia ]
        | ]. wpc.
      change (wbytes ?M0 (Z_to_bv 64 ab) (word_to_le_bytes 8 (Z_to_bv 64 0))) with (Wn 8 M0 ab 0).
      zbft F_5b828 D_5b828.
      apply mst_refl. }
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_cbr_cas30 : forall regs (M rom : word -> option byte) (m b1 : Z),
  getr regs 9 = Z_to_bv 64 m -> 16 <= m -> m + 16 < 2 ^ 47 -> m mod 16 = 0 -> 0 <= b1 < 256 ->
  cellA M m 4 (3 + 256 * b1) -> wrA M m 4 ->
  exists regs', msteps ASEGS (mkst regs (0x5b87c : word) M rom) (mkst regs' (0x5b8b4 : word) (Wn 4 M m (256 * b1)) rom)
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom m b1 H9 Hm Hm' Hm16 Hb1 Chw Whw.
  assert (Hm4 : m mod 4 = 0). { pose proof (Z.div_mod m 16 ltac:(lia)) as E. rewrite Hm16 in E. rewrite E. replace (16 * (m / 16) + 0) with ((4 * (m / 16)) * 4) by lia. apply Z_mod_mult. }
  eexists. split.
  { stepn F_5b82c D_5b82c. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612. rewrite art_land_m4 by lia.
    replace (m / 4 * 4) with m by (pose proof (Z.div_mod m 4 ltac:(lia)); lia).
    stepn F_5b830 D_5b830. rwH. rewrite art_zb_slli by lia.
    zstep F_5b834 D_5b834. zstep F_5b838 D_5b838.
    stepn F_5b83c D_5b83c. rwH. rewrite art_sllw_0 by lia.
    stepn F_5b840 D_5b840. rwH. rewrite art_sllw_0 by lia.
    chain_step; [reflexivity
      | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m) _ (Z_to_bv 64 (3 + 256 * b1)));
        [exact F_5b844 | reflexivity | exact D_5b844 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4
        | exact Chw | apply art_bytes4; lia ]
      | ]. wpc. rewrite art_v_lw_small by lia.
    chain_step; [reflexivity | eapply art_step_and_r; [exact F_5b848 | reflexivity | exact D_5b848 | reflexivity] | ]. wpc.
    gres. rewrite (art_zb_and (3 + 256 * b1) 255) by lia.
    replace (Z.land (3 + 256 * b1) 255) with 3.
    2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. replace (3 + 256 * b1) with (3 + b1 * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
    chain_step; [reflexivity
      | eapply art_step_branch_ft_r; [exact F_5b84c | reflexivity | exact D_5b84c | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
      | ]. wpc.
    chain_step; [reflexivity | eapply art_step_xor_r; [exact F_5b850 | reflexivity | exact D_5b850 | reflexivity] | ]. wpc.
    chain_step; [reflexivity | eapply art_step_and_r; [exact F_5b854 | reflexivity | exact D_5b854 | reflexivity] | ]. wpc.
    chain_step; [reflexivity | eapply art_step_xor_r; [exact F_5b858 | reflexivity | exact D_5b858 | reflexivity] | ]. wpc.
    gres.
    rewrite art_cas30w by lia.
    match goal with |- msteps _ (mkstr _ _ ?X _ _) _ => assert (Whw' : wokA X m 4) by (eapply (wr_wok _ _ _ _ Whw); lia) end.
    chain_step; [reflexivity
      | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m));
        [exact F_5b85c | reflexivity | exact D_5b85c | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4 | gres; rwH; reflexivity
        | exact Whw' ]
      | ]. wpc.
    change (wbytes ?M0 (Z_to_bv 64 m) (word_to_le_bytes 4 (Z_to_bv 64 (256 * b1)))) with (Wn 4 M0 m (256 * b1)).
    zbft F_5b860 D_5b860.
    apply mst_refl. }
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_cbr_pd : forall regs (M rom : word -> option byte) (m n : Z),
  getr regs 9 = Z_to_bv 64 m -> 16 <= m -> m + 16 < 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
  cellA M (m + 2) 2 0 -> cellA M (m + 4) 4 n ->
  exists regs', msteps ASEGS (mkst regs (0x5b8b4 : word) M rom) (mkst regs' (0x81d18 : word) M rom)
    /\ getr regs' 1 = (0x5b8d8 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (m + 16) /\ getr regs' 11 = Z_to_bv 64 ((n + 7) / 8 * 8) /\ getr regs' 12 = Z_to_bv 64 250
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom m n H9 Hm Hm' Hn Chi Cn.
  eexists. split.
  { zlhu4 F_5b864 D_5b864 (m + 2) Chi.
    zlwu F_5b868 D_5b868 (m + 4) Cn.
    zstep F_5b86c D_5b86c. zstep F_5b870 D_5b870.
    stepn F_5b874 D_5b874. rwH. rewrite (art_zb_or4 0 n) by lia. rewrite Z.lor_0_l.
    zstep F_5b878 D_5b878.
    stepn F_5b87c D_5b87c. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
    zstep F_5b880 D_5b880.
    stepn F_5b884 D_5b884.
    apply mst_refl. }
  split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Definition art_cbr_stats_mem (M : word -> option byte) (sp1 t n f1 f2 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp1 - 8) 0x5b8dc) (sp1 - 24) 0x89c9c) (t + 2800 + 40) (f1 + 1)) (t + 2800 + 48) (n + f2).

Lemma art_cbr_stats : forall regs (M rom : word -> option byte) (sp1 HI tp key tsd ctx t m n f1 f2 : Z),
  getr regs 2 = Z_to_bv 64 sp1 -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 m ->
  0x6b3000 <= HI -> HI <= sp1 - 32 -> sp1 < 2 ^ 64 -> wrA M (sp1 - 32) 32 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> wrA M t 4096 ->
  16 <= m -> m + 16 <= HI -> 0 <= n < 2 ^ 32 -> 0 <= f1 < 2 ^ 64 -> 0 <= f2 < 2 ^ 64 ->
  cellA M (m + 2) 2 0 -> cellA M (m + 4) 4 n -> cellA M (t + 2800 + 40) 8 f1 -> cellA M (t + 2800 + 48) 8 f2 ->
  exists regs', msteps ASEGS (mkst regs (0x5b8d8 : word) M rom) (mkst regs' (0x5b904 : word) (art_cbr_stats_mem M sp1 t n f1 f2) rom)
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp1 HI tp key tsd ctx t m n f1 f2 H2 H4 H9 HHI Hsp Hsp' W TSD Ht Ht' Htp Htsd Hctx Wt Hm Hm' Hn Hf1 Hf2 Chi Cn C40 C48.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  eexists. split.
  { stepn F_5b888 D_5b888.
    zcall (art_thread_stats_fn _ _ _ (0x5b8dc : word) sp1 tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chi' : cellA X (m + 2) 2 0) by zcell; assert (Cn' : cellA X (m + 4) 4 n) by zcell;
      assert (C40' : cellA X (t + 2800 + 40) 8 f1) by zcell; assert (C48' : cellA X (t + 2800 + 48) 8 f2) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
    zlhu4 F_5b88c D_5b88c (m + 2) Chi'.
    zlwu F_5b890 D_5b890 (m + 4) Cn'.
    zld F_5b894 D_5b894 (t + 2800 + 48) C48'.
    zld F_5b898 D_5b898 (t + 2800 + 40) C40'.
    zstep F_5b89c D_5b89c.
    stepn F_5b8a0 D_5b8a0. rwH. rewrite (art_zb_or4 0 n) by lia. rewrite Z.lor_0_l.
    zstep F_5b8a4 D_5b8a4. zstep F_5b8a8 D_5b8a8.
    zsd F_5b8ac D_5b8ac (t + 2800 + 40) (f1 + 1) ltac:(zwok').
    zsd F_5b8b0 D_5b8b0 (t + 2800 + 48) (n + f2) ltac:(zwok').
    unfold art_cbr_stats_mem. apply mst_refl. }
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; exact H2]|]). destruct Hr.
Qed.

Lemma art_cbr_tailp : forall regs (M rom : word -> option byte) (raw : word) (sp cb cache spb c szi g8 g9 g18 g19 g20 : Z),
  let ab := spb + c * 2 ^ 32 + szi in
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 cb -> getr regs 18 = Z_to_bv 64 ab -> getr regs 19 = Z_to_bv 64 1413976 -> getr regs 20 = Z_to_bv 64 (2 ^ 37) ->
  48 <= sp -> sp < 2 ^ 64 -> 0x6b3000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 1 <= c <= 30 -> 0 <= szi < 2 ^ 32 -> 0 <= cb -> cb + 8 < 2 ^ 64 ->
  cellA M (1413976 + 32) 8 spb -> cellA M cb 8 cache ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x5b904 : word) M rom) (mkst regs' (0x5bb70 : word) M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 cache /\ getr regs' 11 = Z_to_bv 64 1413976
    /\ getr regs' 12 = Z_to_bv 64 c /\ getr regs' 13 = Z_to_bv 64 ab
    /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp cb cache spb c szi g8 g9 g18 g19 g20 ab H2 H8 H18 H19 H20 Hsp Hsp' Hspb Hspb' Hc Hszi Hcb Hcb' Cspb Ccb F1 F8 F9 F18 F19 F20.
  assert (Hab : ab = spb + c * 2 ^ 32 + szi) by reflexivity. clearbody ab.
  assert (Ec : (ab - spb) * 2 ^ 27 / 2 ^ 59 = c).
  { symmetry. apply (Z.div_unique_pos ((ab - spb) * 2 ^ 27) (2 ^ 59) c (szi * 2 ^ 27)); lia. }
  eexists. split.
  { zbft F_5b8b4 D_5b8b4.
    zld F_5b8b8 D_5b8b8 (1413976 + 32) Cspb.
    zbft F_5b8bc D_5b8bc.
    zstep F_5b8c0 D_5b8c0.
    zbft F_5b8c4 D_5b8c4.
    zld F_5b8c8 D_5b8c8 cb Ccb.
    zstep F_5b8cc D_5b8cc.
    zstep F_5b8d0 D_5b8d0.
    stepn F_5b8d4 D_5b8d4. rwH. rewrite (art_zb_srli ((ab - spb) * 2 ^ 27) 59) by lia. rewrite Ec.
    stepn F_5b8d8 D_5b8d8. stepn F_5b8dc D_5b8dc. zcl4.
    zstep F_5b8e0 D_5b8e0.
    zld F_5b8e4 D_5b8e4 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_5b8e8 D_5b8e8 (sp - 16) F8. zld F_5b8ec D_5b8ec (sp - 24) F9. zld F_5b8f0 D_5b8f0 (sp - 32) F18. zld F_5b8f4 D_5b8f4 (sp - 40) F19. zld F_5b8f8 D_5b8f8 (sp - 48) F20.
    zstep F_5b8fc D_5b8fc.
    stepn F_5b900 D_5b900.
    apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_cbr_tails : forall regs (M rom : word -> option byte) (raw : word) (sp spb hb g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 18 = Z_to_bv 64 hb -> getr regs 19 = Z_to_bv 64 1413976 -> getr regs 20 = Z_to_bv 64 (2 ^ 37) ->
  48 <= sp -> sp < 2 ^ 64 -> 0x6b3000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 < hb < 2 ^ 64 -> (hb < spb \/ spb + 2 ^ 37 <= hb) ->
  cellA M (1413976 + 32) 8 spb ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x5b904 : word) M rom) (mkst regs' (0x5bd38 : word) M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0x159398 /\ getr regs' 11 = Z_to_bv 64 0x159608 /\ getr regs' 12 = Z_to_bv 64 hb
    /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp spb hb g8 g9 g18 g19 g20 H2 H18 H19 H20 Hsp Hsp' Hspb Hspb' Hhb Hsec Cspb F1 F8 F9 F18 F19 F20.
  destruct (Z_lt_le_dec hb spb) as [Lo|Hi].
  - eexists. split.
    { zbft F_5b8b4 D_5b8b4.
      zld F_5b8b8 D_5b8b8 (1413976 + 32) Cspb.
      zbtk F_5b8bc D_5b8bc.
      zstep F_5b924 D_5b924. zstep F_5b928 D_5b928. zstep F_5b92c D_5b92c.
      zld F_5b930 D_5b930 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
      zld F_5b934 D_5b934 (sp - 16) F8. zld F_5b938 D_5b938 (sp - 24) F9. zld F_5b93c D_5b93c (sp - 32) F18. zld F_5b940 D_5b940 (sp - 40) F19. zld F_5b944 D_5b944 (sp - 48) F20.
      zstep F_5b948 D_5b948.
      stepn F_5b94c D_5b94c.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zbft F_5b8b4 D_5b8b4.
      zld F_5b8b8 D_5b8b8 (1413976 + 32) Cspb.
      zbft F_5b8bc D_5b8bc.
      zstep F_5b8c0 D_5b8c0.
      zbtk F_5b8c4 D_5b8c4.
      zstep F_5b924 D_5b924. zstep F_5b928 D_5b928. zstep F_5b92c D_5b92c.
      zld F_5b930 D_5b930 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
      zld F_5b934 D_5b934 (sp - 16) F8. zld F_5b938 D_5b938 (sp - 24) F9. zld F_5b93c D_5b93c (sp - 32) F18. zld F_5b940 D_5b940 (sp - 40) F19. zld F_5b944 D_5b944 (sp - 48) F20.
      zstep F_5b948 D_5b948.
      stepn F_5b94c D_5b94c.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_cbr_sa : forall regs (M rom : word -> option byte) (raw : word) (sp cb m spb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 cb -> getr regs 11 = Z_to_bv 64 m ->
  0x6b3000 + 48 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 48) 48 -> 0 <= cb < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  0x6b3000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> (m < spb \/ spb + 2 ^ 37 <= m) ->
  cellA M (1413976 + 32) 8 spb ->
  exists regs', msteps ASEGS (mkst regs (0x5b76c : word) M rom) (mkst regs' (0x5b9f0 : word) (art_f48 M sp raw regs) rom)
    /\ getr regs' 1 = (0x5b7e4 : bv 64)%bv /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 8 = Z_to_bv 64 cb /\ getr regs' 9 = Z_to_bv 64 m
    /\ getr regs' 19 = Z_to_bv 64 1413976 /\ getr regs' 20 = Z_to_bv 64 (2 ^ 37) /\ getr regs' 10 = Z_to_bv 64 0x159398 /\ getr regs' 11 = Z_to_bv 64 m
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp cb m spb H1 H2 H10 H11 Hsp Hsp' W Hcb Hm Hspb Hspb' Hsec Cspb.
  destruct (Z_lt_le_dec m spb) as [Lo|Hi].
  - eexists. split.
    { zstep F_5b71c D_5b71c.
      zsd F_5b720 D_5b720 (sp - 8) (U raw) ltac:(rewok W). zsd F_5b724 D_5b724 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_5b728 D_5b728 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5b72c D_5b72c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_5b730 D_5b730 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5b734 D_5b734 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zstep F_5b738 D_5b738. zstep F_5b73c D_5b73c.
      stepn F_5b740 D_5b740. stepn F_5b744 D_5b744. zcl4.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1413976 + 32) 8 spb) by zcell end.
      zld F_5b748 D_5b748 (1413976 + 32) Cspb'.
      zstep F_5b74c D_5b74c. zstep F_5b750 D_5b750.
      zbtk F_5b754 D_5b754.
      zstep F_5b788 D_5b788. zstep F_5b78c D_5b78c.
      stepn F_5b790 D_5b790.
      unfold art_f48. apply mst_refl. }
    split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zstep F_5b71c D_5b71c.
      zsd F_5b720 D_5b720 (sp - 8) (U raw) ltac:(rewok W). zsd F_5b724 D_5b724 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_5b728 D_5b728 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5b72c D_5b72c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_5b730 D_5b730 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5b734 D_5b734 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zstep F_5b738 D_5b738. zstep F_5b73c D_5b73c.
      stepn F_5b740 D_5b740. stepn F_5b744 D_5b744. zcl4.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1413976 + 32) 8 spb) by zcell end.
      zld F_5b748 D_5b748 (1413976 + 32) Cspb'.
      zstep F_5b74c D_5b74c. zstep F_5b750 D_5b750.
      zbft F_5b754 D_5b754.
      zstep F_5b758 D_5b758.
      zbtk F_5b75c D_5b75c.
      zstep F_5b788 D_5b788. zstep F_5b78c D_5b78c.
      stepn F_5b790 D_5b790.
      unfold art_f48. apply mst_refl. }
    split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_cbr_sb : forall regs (M rom : word -> option byte) (spb hb : Z),
  getr regs 10 = Z_to_bv 64 hb -> getr regs 19 = Z_to_bv 64 1413976 -> getr regs 20 = Z_to_bv 64 (2 ^ 37) ->
  0x6b3000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= hb < 2 ^ 64 -> (hb < spb \/ spb + 2 ^ 37 <= hb) ->
  cellA M (1413976 + 32) 8 spb ->
  exists regs', msteps ASEGS (mkst regs (0x5b7e4 : word) M rom) (mkst regs' (0x5b8d8 : word) M rom)
    /\ getr regs' 18 = Z_to_bv 64 hb
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom spb hb H10 H19 H20 Hspb Hspb' Hhb Hsec Cspb.
  destruct (Z_lt_le_dec hb spb) as [Lo|Hi].
  - eexists. split.
    { zstep F_5b794 D_5b794.
      zld F_5b798 D_5b798 (1413976 + 32) Cspb.
      zstep F_5b79c D_5b79c.
      zbft F_5b7a0 D_5b7a0.
      stepn F_5b7a4 D_5b7a4.
      apply mst_refl. }
    split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zstep F_5b794 D_5b794.
      zld F_5b798 D_5b798 (1413976 + 32) Cspb.
      zstep F_5b79c D_5b79c.
      zbtk F_5b7a0 D_5b7a0.
      zbtk F_5b80c D_5b80c.
      apply mst_refl. }
    split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.

Lemma art_cbr_stats_mem_facts : forall M sp1 t n f1 f2, 32 <= sp1 -> sp1 < 2 ^ 64 -> 0 <= t -> t + 4096 < 2 ^ 64 ->
  mem_grows M (art_cbr_stats_mem M sp1 t n f1 f2) /\ art_agree [(sp1 - 32, 32); (t + 2800 + 40, 16)] M (art_cbr_stats_mem M sp1 t n f1 f2).
Proof. intros M sp1 t n f1 f2 H1 H2 H3 H4. unfold art_cbr_stats_mem. split; [zgrows|]. eapply art_agree_sub; [zagree|]. zsub. Qed.

Lemma art_poison_mem_facts : forall M sp ra s0 s1 s2 s3 s4 s5 a k v, 64 <= sp -> sp < 2 ^ 64 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  let M' := Wf (art_poison_frame M sp ra s0 s1 s2 s3 s4 s5) a k v in
  mem_grows M M' /\ art_agree [(sp - 64, 64); (a, Z.of_nat k)] M M'.
Proof.
  intros M sp ra s0 s1 s2 s3 s4 s5 a k v H1 H2 H3 H4 M'. unfold M', art_poison_frame. split; [zgrows|].
  eapply art_agree_sub; [eapply art_agree_trans; [|apply art_agree_Wf; [exact H3|exact H4]]; zagree|]. zsub.
Qed.
