(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac EatAllocG EatDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r7fbdc_7fe80 Ea0_code_r802bc_80400.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module MM2.
Definition w64 (x : Z) : Z := x mod 2 ^ 64.

Definition mm2_h0 (k1 k2 size : Z) : Z := w64 (Z.lxor (w64 (size * k1)) k2).

Definition mm2_step (mC h w : Z) : Z :=
  let u1 := w64 (w * mC) in let u2 := w64 (Z.lxor (u1 / 2 ^ 47) u1) in let u3 := w64 (u2 * mC) in let u4 := w64 (Z.lxor u3 h) in w64 (u4 * mC).

Definition mm2_fin (mC hN : Z) : Z :=
  let u1 := w64 (0 * mC) in let u2 := w64 (Z.lxor (u1 / 2 ^ 47) u1) in let u3 := w64 (u2 * mC) in let u4 := w64 (Z.lxor u3 hN) in let u5 := w64 (u4 * mC) in
  let u6 := w64 (Z.lxor (u5 / 2 ^ 47) u5) in let u7 := w64 (u6 * mC) in w64 (Z.lxor (u7 / 2 ^ 47) u7).
Definition mm2g (mC k1 k2 : Z) (ws : list Z) : Z := mm2_fin mC (fold_left (mm2_step mC) ws (mm2_h0 k1 k2 (Z.of_nat (length ws)))).

Definition MC : Z := 0xc6a4a7935bd1e995.
Definition K1 : Z := 0x35253c9ade8f4ca8.
Definition K2 : Z := 0x9747b28c9747b28c.
Definition mm2 (ws : list Z) : Z := mm2g MC K1 K2 ws.

Lemma w64_range : forall x, 0 <= w64 x < 2 ^ 64.
Proof. intros. unfold w64. apply Z.mod_pos_bound. lia. Qed.
Lemma mm2_fin_range : forall mC hN, 0 <= mm2_fin mC hN < 2 ^ 64.
Proof. intros. unfold mm2_fin. apply w64_range. Qed.
Lemma mm2_range : forall ws, 0 <= mm2 ws < 2 ^ 64.
Proof. intros. apply mm2_fin_range. Qed.

Lemma skipn_nth_cons : forall (ws : list Z) (i : nat), (i < length ws)%nat -> skipn i ws = nth i ws 0 :: skipn (S i) ws.
Proof.
  induction ws as [|a ws IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hi. lia.
Qed.
Lemma mm2_fold_step : forall mC ws i h, 0 <= i < Z.of_nat (length ws) ->
  fold_left (mm2_step mC) (skipn (Z.to_nat i) ws) h = fold_left (mm2_step mC) (skipn (Z.to_nat (i + 1)) ws) (mm2_step mC h (nth (Z.to_nat i) ws 0)).
Proof.
  intros mC ws i h Hi. rewrite (skipn_nth_cons ws (Z.to_nat i)) by lia. cbn [fold_left].
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.
Lemma mm2_fold_end : forall mC ws i h, Z.of_nat (length ws) <= i -> fold_left (mm2_step mC) (skipn (Z.to_nat i) ws) h = h.
Proof. intros mC ws i h Hi. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma zb_fn : forall e, exists u, 0 <= u < 2 ^ 64 /\ Z_to_bv 64 e = Z_to_bv 64 u /\ u = w64 e.
Proof.
  intros e. exists (e mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|]. split; [|reflexivity].
  apply art_zb_eq. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End MM2.
Export MM2.

Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma dp_cell8_inj : forall (M : word -> option byte) a v w, cellA M a 8 v -> cellA M a 8 w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
  intros M a v w C1 C2 Hv Hw. unfold cell in *. rewrite C1 in C2.
  apply (f_equal (fun o : option (list byte) => match o with Some l => bytes_le_to_Z l | None => 0 end)) in C2.
  rewrite !SeqExec.bytes_le_to_Z_8 in C2. rewrite !art_u_lit in C2 by lia. exact C2.
Qed.
Lemma dp_cell4_inj : forall (M : word -> option byte) a v w, cellA M a 4 v -> cellA M a 4 w -> 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> v = w.
Proof.
  intros M a v w C1 C2 Hv Hw. unfold cell in *. rewrite C1 in C2.
  apply (f_equal (fun o : option (list byte) => match o with Some l => bytes_le_to_Z l | None => 0 end)) in C2.
  rewrite !art_bytes4 in C2 by lia. rewrite !art_u_lit in C2 by lia. exact C2.
Qed.

Inductive dp_chain (M : word -> option byte) (l2 h : Z) : Z -> Prop :=
| dpc_here : forall id, 1 <= id -> cellA M (l2 + 16 * id) 8 h -> dp_chain M l2 h id
| dpc_next : forall id lk, 1 <= id -> cellA M (l2 + 16 * id + 8) 4 lk -> 0 <= lk < id -> dp_chain M l2 h lk -> dp_chain M l2 h id.

Lemma dp_chain_pos : forall M l2 h id, dp_chain M l2 h id -> 1 <= id.
Proof. intros M l2 h id H. destruct H; assumption. Qed.

Lemma dp_chain_agree : forall (M M' : word -> option byte) l2 h id N, dp_chain M l2 h id -> id <= N -> 0 <= l2 -> l2 + 16 * N + 16 < 2 ^ 64 ->
  (forall x : word, l2 + 16 <= U x < l2 + 16 * N + 16 -> M' x = M x) -> dp_chain M' l2 h id.
Proof.
  intros M M' l2 h id N H. induction H as [id Hid C | id lk Hid C Hlk H IH]; intros HN Hl2 Hl2' AG.
  - apply dpc_here; [exact Hid|]. apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; Lia.lia | Lia.lia | cbn; Lia.lia | exact C].
  - apply (dpc_next M' l2 h id lk); [exact Hid | | exact Hlk | apply IH; [Lia.lia | exact Hl2 | exact Hl2' | exact AG]].
    apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; Lia.lia | Lia.lia | cbn; Lia.lia | exact C].
Qed.

Section FPX. Context {fx : PropExec.FPState}.

Lemma dp_pro_fn : forall regs (M rom : word -> option byte) (raw : word) (s trp size mC k1 k2 : Z),
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 trp -> getr regs 11 = Z_to_bv 64 size -> getr regs 1 = raw ->
  0x698000 <= s - 224 -> s < 2 ^ 64 -> 4096 <= trp -> trp + 8 * size < 2 ^ 64 -> 1 <= size <= 30 ->
  0 <= mC < 2 ^ 64 -> 0 <= k1 < 2 ^ 64 -> 0 <= k2 < 2 ^ 64 ->
  cellA M 0x102e8 8 mC -> cellA M 0x10320 8 k1 -> cellA M 0x10420 8 k2 -> wrA M (s - 224) 224 ->
  exists regs' h0,
    msteps ASEGS (mkst regs (0x9a948 : word) M rom) (mkst regs' (0x9a9f8 : word) (dp_frame M s trp size raw regs) rom)
    /\ getr regs' 11 = Z_to_bv 64 trp /\ getr regs' 14 = Z_to_bv 64 (trp + 8 * size) /\ getr regs' 10 = Z_to_bv 64 mC /\ getr regs' 12 = Z_to_bv 64 h0
    /\ 0 <= h0 < 2 ^ 64 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 DEP /\ getr regs' 2 = Z_to_bv 64 (s - 112)
    /\ (forall r : reg, r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> ~ (10 <= U r <= 16) -> getr regs' r = getr regs r)
    /\ h0 = mm2_h0 k1 k2 size.
Proof.
  intros regs M rom raw s trp size mC k1 k2 H2 H10 H11 H1 Hs Hs' Ht Ht' Hsz HmC Hk1 Hk2 CmC Ck1 Ck2 W.
  destruct (zb_fn (size * k1)) as (u1 & R1 & E1 & Qu1).
  destruct (zb_fn (Z.lxor u1 k2)) as (h0 & R0 & E0 & Qh0).
  unfold dp_frame, DEP.
  eexists _, h0. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - zstep F_9a8f8 D_9a8f8.
    stepn F_9a8fc D_9a8fc.
    stepn F_9a900 D_9a900.
    zstep F_9a904 D_9a904.
    zstep F_9a908 D_9a908.
    zstep F_9a90c D_9a90c.
    zstep F_9a910 D_9a910.
    stepn F_9a914 D_9a914.
    zstep F_9a918 D_9a918.
    zsd F_9a91c D_9a91c (s - 8) (U raw) ltac:(rewok W).
    zsd F_9a920 D_9a920 (s - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_9a924 D_9a924 (s - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_9a928 D_9a928 (s - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_9a92c D_9a92c (s - 40) (U (getr regs 19)) ltac:(rewok W).
    zsd F_9a930 D_9a930 (s - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_9a934 D_9a934 (s - 56) (U (getr regs 21)) ltac:(rewok W).
    zsd F_9a938 D_9a938 (s - 64) (U (getr regs 22)) ltac:(rewok W).
    zsd F_9a93c D_9a93c (s - 72) (U (getr regs 23)) ltac:(rewok W).
    zsd F_9a940 D_9a940 (s - 80) (U (getr regs 24)) ltac:(rewok W).
    zsd F_9a944 D_9a944 (s - 88) (U (getr regs 25)) ltac:(rewok W).
    zstep F_9a948 D_9a948.
    zstep F_9a94c D_9a94c.
    zsd F_9a950 D_9a950 (s - 104) trp ltac:(rewok W).
    zsd F_9a954 D_9a954 (s - 96) size ltac:(rewok W).
    zbtk F_9a958 D_9a958.
    stepn F_9a960 D_9a960. rwH. unfold v_addiw. rewrite art_u_lit by lia.
    replace (bv_swrap 32 (size + 0)) with size by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).
    zstep F_9a964 D_9a964.
    zbft F_9a968 D_9a968.
    zbft F_9a96c D_9a96c.
    stepn F_9a970 D_9a970. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small size (2 ^ 32)) by lia.
    stepn F_9a974 D_9a974.
    stepn F_9a978 D_9a978.
    stepn F_9a97c D_9a97c.
    stepn F_9a980 D_9a980.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (C1 : cellA X 0x10320 8 k1) by zcell; assert (C2 : cellA X 0x10420 8 k2) by zcell; assert (C0 : cellA X 0x102e8 8 mC) by zcell end.
    zld F_9a984 D_9a984 0x10320 C1.
    stepn F_9a988 D_9a988. rwH.
    match goal with |- context [v_and (Z_to_bv 64 size) ?L] =>
      replace (v_and (Z_to_bv 64 size) L) with (Z_to_bv 64 size : word)
        by (symmetry; replace L with (Z_to_bv 64 (Z.ones 32) : word) by (apply bv_eq; vm_compute; reflexivity);
            rewrite art_zb_and by (change (Z.ones 32) with 4294967295; lia); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia) end.
    stepn F_9a98c D_9a98c.
    zld F_9a990 D_9a990 0x10420 C2.
    zld F_9a994 D_9a994 0x102e8 C0.
    zstep F_9a998 D_9a998. rewrite E1.
    zstep F_9a99c D_9a99c.
    stepn F_9a9a0 D_9a9a0. rwH. rewrite art_zb_xor by lia. rewrite E0.
    zstep F_9a9a4 D_9a9a4.
    replace (trp + size * 2 ^ 3) with (trp + 8 * size) by lia.
    apply mst_refl.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - exact R0.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - split; [|rewrite Qh0, Qu1; reflexivity]. intros r N2 N8 N9 NR.
    destruct (decide (r = 10%bv)) as [->|N10]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 11%bv)) as [->|N11]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 12%bv)) as [->|N12]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 13%bv)) as [->|N13]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 14%bv)) as [->|N14]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 15%bv)) as [->|N15]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 16%bv)) as [->|N16]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    kept_solve.
Qed.

Lemma dp_hash_fn : forall (q : nat) regs (M rom : word -> option byte) (trp size mC i h : Z) (ws : list Z),
  (forall j, 0 <= j < size -> cellA M (trp + 8 * j) 8 (nth (Z.to_nat j) ws 0)) -> (forall j, 0 <= j < size -> 0 <= nth (Z.to_nat j) ws 0 < 2 ^ 64) ->
  size = Z.of_nat (length ws) ->
  0 <= trp -> trp + 8 * size < 2 ^ 64 -> 0 <= mC < 2 ^ 64 -> 0 <= h < 2 ^ 64 -> 0 <= i -> i + Z.of_nat q + 1 = size ->
  getr regs 11 = Z_to_bv 64 (trp + 8 * i) -> getr regs 14 = Z_to_bv 64 (trp + 8 * size) -> getr regs 10 = Z_to_bv 64 mC -> getr regs 12 = Z_to_bv 64 h ->
  exists regs' h',
    msteps ASEGS (mkst regs (0x9a9f8 : word) M rom) (mkst regs' (0x9aa1c : word) M rom)
    /\ getr regs' 11 = Z_to_bv 64 (trp + 8 * size) /\ getr regs' 12 = Z_to_bv 64 h' /\ 0 <= h' < 2 ^ 64
    /\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> getr regs' r = getr regs r)
    /\ h' = fold_left (mm2_step mC) (skipn (Z.to_nat i) ws) h.
Proof.
  induction q as [|q IH]; intros regs M rom trp size mC i h ws RC WR Esz Ht1 Ht2 HmC Hh Hi Hq H11 H14 H10 H12.
  - pose proof (RC i ltac:(lia)) as Rb. pose proof (WR i ltac:(lia)) as Bb.
    destruct (zb_fn (nth (Z.to_nat i) ws 0 * mC)) as (u1 & R1 & E1 & Qu1).
    pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)).
    destruct (zb_fn (Z.lxor (u1 / 2 ^ 47) u1)) as (u2 & R2 & E2 & Qu2).
    destruct (zb_fn (u2 * mC)) as (u3 & R3 & E3 & Qu3).
    destruct (zb_fn (Z.lxor u3 h)) as (u4 & R4 & E4 & Qu4).
    destruct (zb_fn (u4 * mC)) as (u5 & R5 & E5 & Qu5).
    eexists _, _. split; [|split; [|split; [|split]]].
    + zld F_9a9a8 D_9a9a8 (trp + 8 * i) Rb.
      zstep F_9a9ac D_9a9ac.
      zstep F_9a9b0 D_9a9b0. rewrite E1.
      stepn F_9a9b4 D_9a9b4. rwH. rewrite art_zb_srli by lia.
      stepn F_9a9b8 D_9a9b8. rwH. rewrite art_zb_xor by lia. rewrite E2.
      zstep F_9a9bc D_9a9bc. rewrite E3.
      stepn F_9a9c0 D_9a9c0. rwH. rewrite art_zb_xor by lia. rewrite E4.
      zstep F_9a9c4 D_9a9c4. rewrite E5.
      zbft F_9a9c8 D_9a9c8.
      apply mst_refl.
    + kept_solve.
    + kept_solve.
    + lia.
    + split; [intros r N11 N12 N15 N16; kept_solve|].
      rewrite (mm2_fold_step mC ws i h) by (clear - Hi Hq Esz; Lia.lia). rewrite (mm2_fold_end mC ws (i + 1)) by (clear - Hi Hq Esz; Lia.lia). rewrite Qu5, Qu4, Qu3, Qu2, Qu1; reflexivity.
  - pose proof (RC i ltac:(lia)) as Rb. pose proof (WR i ltac:(lia)) as Bb.
    destruct (zb_fn (nth (Z.to_nat i) ws 0 * mC)) as (u1 & R1 & E1 & Qu1).
    pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)).
    destruct (zb_fn (Z.lxor (u1 / 2 ^ 47) u1)) as (u2 & R2 & E2 & Qu2).
    destruct (zb_fn (u2 * mC)) as (u3 & R3 & E3 & Qu3).
    destruct (zb_fn (Z.lxor u3 h)) as (u4 & R4 & E4 & Qu4).
    destruct (zb_fn (u4 * mC)) as (u5 & R5 & E5 & Qu5).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x9a9f8 : word) M rom) (mkst r1 (0x9a9f8 : word) M rom)
              /\ (getr r1 11 = Z_to_bv 64 (trp + 8 * (i + 1)) /\ getr r1 14 = Z_to_bv 64 (trp + 8 * size) /\ getr r1 10 = Z_to_bv 64 mC
                  /\ getr r1 12 = Z_to_bv 64 u5
                  /\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> getr r1 r = getr regs r))).
    { eexists. split.
      - zld F_9a9a8 D_9a9a8 (trp + 8 * i) Rb.
        zstep F_9a9ac D_9a9ac.
        zstep F_9a9b0 D_9a9b0. rewrite E1.
        stepn F_9a9b4 D_9a9b4. rwH. rewrite art_zb_srli by lia.
        stepn F_9a9b8 D_9a9b8. rwH. rewrite art_zb_xor by lia. rewrite E2.
        zstep F_9a9bc D_9a9bc. rewrite E3.
        stepn F_9a9c0 D_9a9c0. rwH. rewrite art_zb_xor by lia. rewrite E4.
        zstep F_9a9c4 D_9a9c4. rewrite E5.
        zbtk F_9a9c8 D_9a9c8.
        apply mst_refl.
      - split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. intros r N11 N12 N15 N16. kept_solve. }
    destruct S1 as (r1 & RUN1 & Q11 & Q14 & Q10 & Q12 & K1).
    destruct (IH r1 M rom trp size mC (i + 1) u5 ws RC WR Esz Ht1 Ht2 HmC R5 ltac:(lia) ltac:(lia) Q11 Q14 Q10 Q12) as (r2 & h2 & RUN2 & P11 & P12 & Rh2 & K2 & F2).
    exists r2, h2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [exact P11|]. split; [exact P12|]. split; [exact Rh2|].
    split; [intros r N11 N12 N15 N16; rewrite (K2 r N11 N12 N15 N16); apply K1; assumption|].
    rewrite F2. rewrite (mm2_fold_step mC ws i h) by (clear - Hi Hq Esz; Lia.lia). f_equal. rewrite Qu5, Qu4, Qu3, Qu2, Qu1; reflexivity.
Qed.

Lemma dp_mid_fn : forall regs (M rom : word -> option byte) (hN mC N : Z),
  getr regs 12 = Z_to_bv 64 hN -> getr regs 13 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 mC -> getr regs 9 = Z_to_bv 64 DEP ->
  0 <= hN < 2 ^ 64 -> 0 <= mC < 2 ^ 64 -> 0 <= N < 2 ^ 16 ->
  (forall b, 0 <= b < 2 ^ 20 -> exists v, cellA M (DEP + 4 * b) 4 v /\ 0 <= v <= N) ->
  exists regs' h b v,
    msteps ASEGS (mkst regs (0x9aa1c : word) M rom) (mkst regs' (0x9aa88 : word) M rom)
    /\ 0 <= h < 2 ^ 64 /\ 0 <= b < 2 ^ 20 /\ cellA M (DEP + 4 * b) 4 v /\ 0 <= v <= N
    /\ getr regs' 19 = Z_to_bv 64 h /\ getr regs' 18 = Z_to_bv 64 (DEP + 4 * b) /\ getr regs' 11 = Z_to_bv 64 v /\ getr regs' 25 = Z_to_bv 64 v
    /\ getr regs' 24 = Z_to_bv 64 MAP1 /\ getr regs' 20 = Z_to_bv 64 (DEP + 4194312) /\ getr regs' 22 = Z_to_bv 64 65535 /\ getr regs' 23 = Z_to_bv 64 2147483647
    /\ getr regs' 9 = Z_to_bv 64 DEP
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> ~ (18 <= U r <= 20) -> ~ (22 <= U r <= 25) -> getr regs' r = getr regs r)
    /\ h = mm2_fin mC hN /\ b = h mod 2 ^ 20.
Proof.
  intros regs M rom hN mC N H12 H13 H10 H9 HhN HmC HN BK.
  destruct (zb_fn (0 * mC)) as (u1 & R1 & E1 & Qu1).
  pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)) as D1. pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D1'.
  destruct (zb_fn (Z.lxor (u1 / 2 ^ 47) u1)) as (u2 & R2 & E2 & Qu2).
  destruct (zb_fn (u2 * mC)) as (u3 & R3 & E3 & Qu3).
  destruct (zb_fn (Z.lxor u3 hN)) as (u4 & R4 & E4 & Qu4).
  destruct (zb_fn (u4 * mC)) as (u5 & R5 & E5 & Qu5).
  pose proof (Z.div_pos u5 (2 ^ 47) ltac:(lia) ltac:(lia)) as D5. pose proof (Z.div_lt_upper_bound u5 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D5'.
  destruct (zb_fn (Z.lxor (u5 / 2 ^ 47) u5)) as (u6 & R6 & E6 & Qu6).
  destruct (zb_fn (u6 * mC)) as (u7 & R7 & E7 & Qu7).
  pose proof (Z.div_pos u7 (2 ^ 47) ltac:(lia) ltac:(lia)) as D7. pose proof (Z.div_lt_upper_bound u7 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D7'.
  destruct (zb_fn (Z.lxor (u7 / 2 ^ 47) u7)) as (h & Rh & Eh & Qh).
  set (b := h mod 2 ^ 20). pose proof (Z.mod_pos_bound h (2 ^ 20) ltac:(lia)) as Rb.
  destruct (BK b ltac:(lia)) as (v & Cv & Rv).
  unfold DEP, MAP1 in *.
  eexists _, h, b, v. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]].
  - stepn F_9a9cc D_9a9cc.
    stepn F_9a9d0 D_9a9d0.
    zstep F_9a9d4 D_9a9d4. rewrite E1.
    stepn F_9a9d8 D_9a9d8.
    stepn F_9a9dc D_9a9dc.
    stepn F_9a9e0 D_9a9e0.
    stepn F_9a9e4 D_9a9e4. rwH. rewrite art_zb_srli by lia.
    stepn F_9a9e8 D_9a9e8. rwH. rewrite art_zb_xor by lia. rewrite E2.
    zstep F_9a9ec D_9a9ec. rewrite E3.
    stepn F_9a9f0 D_9a9f0. rwH. rewrite art_zb_xor by lia. rewrite E4.
    zstep F_9a9f4 D_9a9f4. rewrite E5.
    stepn F_9a9f8 D_9a9f8. rwH. rewrite art_zb_srli by lia.
    stepn F_9a9fc D_9a9fc. rwH. rewrite art_zb_xor by lia. rewrite E6.
    zstep F_9aa00 D_9aa00. rewrite E7.
    stepn F_9aa04 D_9aa04. rwH. rewrite art_zb_srli by lia.
    stepn F_9aa08 D_9aa08. rwH. rewrite art_zb_xor by lia. rewrite Eh.
    zstep F_9aa0c D_9aa0c.
    replace (Z_to_bv 64 (h * 2 ^ 44) : word) with (Z_to_bv 64 (b * 2 ^ 44) : word)
      by (apply art_zb_eq; rewrite (mod_mul_pow44 h) by lia; subst b; rewrite Z.mod_small; [reflexivity | nia]).
    stepn F_9aa10 D_9aa10. rwH. rewrite (art_zb_srli_exact (b * 2 ^ 44) 42 (4 * b)) by lia.
    zstep F_9aa14 D_9aa14.
    zlw F_9aa18 D_9aa18 (2242776 + 4 * b) Cv.
    stepn F_9aa1c D_9aa1c.
    zstep F_9aa20 D_9aa20.
    stepfence F_9aa24 D_9aa24.
    stepn F_9aa28 D_9aa28. rwH.
    match goal with |- context [v_and (Z_to_bv 64 v) ?L] =>
      replace (v_and (Z_to_bv 64 v) L) with (Z_to_bv 64 v : word)
        by (symmetry; replace L with (Z_to_bv 64 (Z.ones 31) : word) by (apply bv_eq; vm_compute; reflexivity);
            rewrite art_zb_and by (change (Z.ones 31) with 2147483647; lia); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia) end.
    stepn F_9aa2c D_9aa2c.
    zstep F_9aa30 D_9aa30.
    zstep F_9aa34 D_9aa34.
    apply mst_refl.
  - exact Rh.
  - lia.
  - exact Cv.
  - exact Rv.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - split; [|split; [rewrite Qh, Qu7, Qu6, Qu5, Qu4, Qu3, Qu2, Qu1; reflexivity | reflexivity]]. intros r N10 N11 N12 N13 N14 NA NB.
    destruct (decide (r = 18%bv)) as [->|N18]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 19%bv)) as [->|N19]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 20%bv)) as [->|N20]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 22%bv)) as [->|N22]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 23%bv)) as [->|N23]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 24%bv)) as [->|N24]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 25%bv)) as [->|N25]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
    kept_solve.
Qed.

Lemma dp_find_fn : forall (m : nat) regs (M rom : word -> option byte) (l2 N h cur : Z),
  (Z.to_nat cur <= m)%nat ->
  cellA M MAP1 8 l2 -> 4096 <= l2 -> l2 + 2 ^ 20 < 2 ^ 64 -> l2 mod 16 = 0 -> 0 <= N < 2 ^ 16 -> dp_nodes M l2 N ->
  0 <= cur <= N -> 0 <= h < 2 ^ 64 ->
  getr regs 11 = Z_to_bv 64 cur -> getr regs 19 = Z_to_bv 64 h -> getr regs 24 = Z_to_bv 64 MAP1 -> getr regs 22 = Z_to_bv 64 65535 ->
  exists regs',
    ((msteps ASEGS (mkst regs (0x9aa88 : word) M rom) (mkst regs' (0x9aae0 : word) M rom) /\ getr regs' 11 = Z_to_bv 64 0 /\ ~ dp_chain M l2 h cur)
     \/ (msteps ASEGS (mkst regs (0x9aa88 : word) M rom) (mkst regs' (0x9ab8c : word) M rom) /\ (exists id, 1 <= id <= N /\ getr regs' 10 = Z_to_bv 64 id) /\ dp_chain M l2 h cur))
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r).
Proof.
  induction m as [|m IH]; intros regs M rom l2 N h cur Hm CM Hl2 Hl2' Hl16 HN ND Hcur Hh H11 H19 H24 H22.
  - assert (cur = 0) by lia. subst cur.
    eexists. split; [left; split|].
    + zbtk F_9aa38 D_9aa38. apply mst_refl.
    + split; [exact H11 | intros X; apply dp_chain_pos in X; clear - X; Lia.lia].
    + intros; reflexivity.
  - destruct (Z.eq_dec cur 0) as [->|NZ].
    { eexists. split; [left; split|].
      + zbtk F_9aa38 D_9aa38. apply mst_refl.
      + split; [exact H11 | intros X; apply dp_chain_pos in X; clear - X; Lia.lia].
      + intros; reflexivity. }
    destruct (ND cur ltac:(lia)) as (hv & lk & Rhv & Chv & Clk & Rlk).
    unfold MAP1 in *.

    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x9aa88 : word) M rom) (mkst r1 (0x9aac0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 cur /\ getr r1 11 = Z_to_bv 64 lk /\ getr r1 12 = Z_to_bv 64 hv /\ getr r1 19 = Z_to_bv 64 h
                  /\ getr r1 24 = Z_to_bv 64 6437096 /\ getr r1 22 = Z_to_bv 64 65535
                  /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr r1 r = getr regs r))).
    { eexists. split.
      - zbft F_9aa38 D_9aa38.
        zstep F_9aa3c D_9aa3c.
        stepn F_9aa40 D_9aa40. rwH. rewrite art_srliw_small by lia.
        zstep F_9aa44 D_9aa44.
        zstep F_9aa48 D_9aa48.
        zld F_9aa4c D_9aa4c 6437096 CM.
        zbft F_9aa50 D_9aa50.
        zstep F_9aa54 D_9aa54.
        stepn F_9aa58 D_9aa58. rwH. rewrite (art_zb_srli_exact (cur * 2 ^ 32) 32 cur) by lia.
        stepn F_9aa5c D_9aa5c. rwH. rewrite art_zb_and by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
        rewrite (Z.mod_small cur (2 ^ 16)) by lia.
        zstep F_9aa60 D_9aa60.
        zstep F_9aa64 D_9aa64.
        zld F_9aa68 D_9aa68 (l2 + 16 * cur) Chv.
        zlw F_9aa6c D_9aa6c (l2 + 16 * cur + 8) Clk.
        apply mst_refl.
      - repeat (split; [kept_solve|]). intros r N10 N11 N12. kept_solve. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q19 & Q24 & Q22 & K1).
    destruct (Z.eq_dec h hv) as [EQ|NE].
    +
      eexists. split; [right; split|].
      * eapply msteps_trans; [exact RUN1|].
        zbft F_9aa70 D_9aa70.
        stepn F_9aa74 D_9aa74.
        apply mst_refl.
      * split; [exists cur; split; [lia|]; kept_solve | apply dpc_here; [lia | rewrite EQ; exact Chv]].
      * intros r N10 N11 N12. kept_solve || (gres; apply K1; assumption).
    +
      assert (S2 : exists r2, msteps ASEGS (mkst r1 (0x9aac0 : word) M rom) (mkst r2 (0x9aa88 : word) M rom)
                /\ (getr r2 11 = Z_to_bv 64 lk /\ getr r2 19 = Z_to_bv 64 h /\ getr r2 24 = Z_to_bv 64 6437096 /\ getr r2 22 = Z_to_bv 64 65535
                    /\ (forall r : reg, getr r2 r = getr r1 r))).
      { eexists. split.
        - zbtk F_9aa70 D_9aa70. apply mst_refl.
        - repeat (split; [kept_solve|]). intros; reflexivity. }
      destruct S2 as (r2 & RUN2 & P11 & P19 & P24 & P22 & K2).
      destruct (IH r2 M rom l2 N h lk ltac:(lia) CM Hl2 Hl2' Hl16 HN ND ltac:(lia) Hh P11 P19 P24 P22) as (r3 & ALT & K3).
      exists r3. split.
      * destruct ALT as [(RUN3 & A & NC)|(RUN3 & A & YC)]; [left|right];
          (split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|]); (split; [exact A|]).
        -- intros X. inversion X as [id' Hid' C' | id' lk' Hid' C' Hlk' X']; subst id'.
           ++ apply NE. exact (dp_cell8_inj M _ _ _ C' Chv Hh Rhv).
           ++ apply NC. replace lk with lk'; [exact X' | exact (dp_cell4_inj M _ _ _ C' Clk ltac:(clear - Hlk' Hcur HN; Lia.lia) ltac:(clear - Rlk Hcur HN; Lia.lia))].
        -- exact (dpc_next M l2 h cur lk ltac:(clear - NZ Hcur; Lia.lia) Clk Rlk YC).
      * intros r N10 N11 N12. rewrite (K3 r N10 N11 N12), (K2 r). apply K1; assumption.
Qed.

End FPX.
