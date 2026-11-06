(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_a1000_a2000  .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition DEP : Z := 0x23e898.
Definition NID : Z := 0x63e898.
Definition MAP1 : Z := 0x63e8a8.
Definition STO : Z := 0x22e888.

Lemma lxor_range64 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= Z.lxor x y < 2 ^ 64.
Proof.
  intros x y Hx Hy. split. apply Z.lxor_nonneg; lia.
  destruct (Z.eq_dec (Z.lxor x y) 0) as [E|NZ]; [rewrite E; lia|].
  assert (Hl : Z.log2 (Z.lxor x y) < 64).
  { eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt.
    - destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  apply Z.log2_lt_pow2 in Hl; [exact Hl|]. pose proof (Z.lxor_nonneg x y). lia.
Qed.
Lemma art_zb_xor : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_xor (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lxor x y).
Proof. intros x y Hx Hy. unfold v_xor. rewrite !art_u_lit by lia. reflexivity. Qed.
Lemma art_zb_or : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

Lemma zb_fresh : forall e, exists u, 0 <= u < 2 ^ 64 /\ Z_to_bv 64 e = Z_to_bv 64 u.
Proof.
  intros e. exists (e mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|].
  apply art_zb_eq. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Ltac zfresh u :=
  lazymatch goal with |- msteps _ (mkst (regupd _ _ (Z_to_bv 64 ?e)) _ _ _) _ =>
    let R := fresh "R" u in let E := fresh "E" u in
    destruct (zb_fresh e) as [u [R E]]; rewrite E; clear E
  end.

Lemma rdn_grows : forall segs k (M M' : word -> option byte) (a : word) bs,
  mem_grows M M' -> rdn segs M a k = Some bs -> exists bs', rdn segs M' a k = Some bs'.
Proof.
  intros segs k. induction k as [|k IH]; intros M M' a bs G R; [exists []%list; reflexivity|].
  cbn [rdn] in R |- *.
  destruct (M a) as [b|] eqn:Ma.
  - assert (M'a : M' a <> None) by (apply G; congruence). destruct (M' a) as [b'|]; [|congruence].
    destruct (rdn segs M (a + 1) k) as [rest|] eqn:Rk; [|discriminate].
    destruct (IH M M' (a + 1)%bv rest G Rk) as [rest' ->]. eexists; reflexivity.
  - destruct (seg_rom segs a) as [b|]; [|discriminate].
    destruct (rdn segs M (a + 1) k) as [rest|] eqn:Rk; [|discriminate].
    destruct (IH M M' (a + 1)%bv rest G Rk) as [rest' ->].
    destruct (M' a); eexists; reflexivity.
Qed.

Definition rcell (M : word -> option byte) (a : Z) : Prop := exists bs, rdn ASEGS M (Z_to_bv 64 a) 8%nat = Some bs.
Lemma rcell_grows : forall M M' a, mem_grows M M' -> rcell M a -> rcell M' a.
Proof. intros M M' a G (bs & R). destruct (rdn_grows _ _ _ _ _ _ G R) as [bs' R']. exists bs'. exact R'. Qed.
Lemma art_bytes8_range : forall M (a : word) bs, rdn ASEGS M a 8%nat = Some bs -> 0 <= bytes_le_to_Z bs < 2 ^ 64.
Proof.
  intros M a bs H. pose proof (rdn_length _ _ _ _ _ H) as L. pose proof (bytes_le_to_Z_bound bs) as B.
  pose proof (bytes_le_to_Z_nonneg bs). rewrite L in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B. lia.
Qed.

Ltac zldr F D a R :=
  chain_step; [reflexivity
    | eapply step_ld with (v := Z_to_bv 64 (bytes_le_to_Z _)); [exact F | reflexivity | exact D | zaddr a; exact R | rewrite art_u_lit; [reflexivity | eapply art_bytes8_range; exact R] ]
    | step_simpl; vnorm].

Lemma art_signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma art_c_lts_zb : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> c_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold c_lts, bv_lts. rewrite !art_signed_small by lia. reflexivity. Qed.
Lemma art_srliw_small : forall x k, 0 <= x < 2 ^ k -> 0 <= k <= 31 -> v_srliw (Z_to_bv 64 x) k = Z_to_bv 64 0.
Proof.
  intros x k Hx Hk. unfold v_srliw. rewrite art_u_lit by (assert (2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia); lia).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  assert (2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Ltac zconds := rwH; rewrite ?art_c_eq_zb, ?art_c_ltu_zb, ?art_c_lts_zb by lia;
  first [ apply Z.eqb_neq; lia | apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia ].

Section FPX. Context {fx : PropExec.FPState}.

Lemma dp_hash_loop : forall (q : nat) regs (M rom : word -> option byte) (trp size mC i h : Z),
  (forall j, 0 <= j < size -> rcell M (trp + 8 * j)) ->
  0 <= trp -> trp + 8 * size < 2 ^ 64 -> 0 <= mC < 2 ^ 64 -> 0 <= h < 2 ^ 64 -> 0 <= i -> i + Z.of_nat q + 1 = size ->
  getr regs 11 = Z_to_bv 64 (trp + 8 * i) -> getr regs 14 = Z_to_bv 64 (trp + 8 * size) -> getr regs 10 = Z_to_bv 64 mC -> getr regs 12 = Z_to_bv 64 h ->
  exists regs' h',
    msteps ASEGS (mkst regs (0xa1254 : word) M rom) (mkst regs' (0xa1278 : word) M rom)
    /\ getr regs' 11 = Z_to_bv 64 (trp + 8 * size) /\ getr regs' 12 = Z_to_bv 64 h' /\ 0 <= h' < 2 ^ 64
    /\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> getr regs' r = getr regs r).
Proof.
  induction q as [|q IH]; intros regs M rom trp size mC i h RC Ht1 Ht2 HmC Hh Hi Hq H11 H14 H10 H12.
  - destruct (RC i ltac:(lia)) as (bs & Rb). pose proof (art_bytes8_range _ _ _ Rb) as Bb.
    destruct (zb_fresh (bytes_le_to_Z bs * mC)) as [u1 [R1 E1]].
    pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)).
    destruct (zb_fresh (Z.lxor (u1 / 2 ^ 47) u1)) as [u2 [R2 E2]].
    destruct (zb_fresh (u2 * mC)) as [u3 [R3 E3]].
    destruct (zb_fresh (Z.lxor u3 h)) as [u4 [R4 E4]].
    destruct (zb_fresh (u4 * mC)) as [u5 [R5 E5]].
    eexists _, _. split; [|split; [|split; [|split]]].
    + zldr F_a1204 D_a1204 (trp + 8 * i) Rb.
      zstep F_a1208 D_a1208.
      zstep F_a120c D_a120c. rewrite E1.
      stepn F_a1210 D_a1210. rwH. rewrite art_zb_srli by lia.
      stepn F_a1214 D_a1214. rwH. rewrite art_zb_xor by lia. rewrite E2.
      zstep F_a1218 D_a1218. rewrite E3.
      stepn F_a121c D_a121c. rwH. rewrite art_zb_xor by lia. rewrite E4.
      zstep F_a1220 D_a1220. rewrite E5.
      zbft F_a1224 D_a1224.
      apply mst_refl.
    + kept_solve.
    + kept_solve.
    + lia.
    + intros r N11 N12 N15 N16. kept_solve.
  - destruct (RC i ltac:(lia)) as (bs & Rb). pose proof (art_bytes8_range _ _ _ Rb) as Bb.
    destruct (zb_fresh (bytes_le_to_Z bs * mC)) as [u1 [R1 E1]].
    pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)).
    destruct (zb_fresh (Z.lxor (u1 / 2 ^ 47) u1)) as [u2 [R2 E2]].
    destruct (zb_fresh (u2 * mC)) as [u3 [R3 E3]].
    destruct (zb_fresh (Z.lxor u3 h)) as [u4 [R4 E4]].
    destruct (zb_fresh (u4 * mC)) as [u5 [R5 E5]].
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0xa1254 : word) M rom) (mkst r1 (0xa1254 : word) M rom)
              /\ (getr r1 11 = Z_to_bv 64 (trp + 8 * (i + 1)) /\ getr r1 14 = Z_to_bv 64 (trp + 8 * size) /\ getr r1 10 = Z_to_bv 64 mC
                  /\ getr r1 12 = Z_to_bv 64 u5
                  /\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> getr r1 r = getr regs r))).
    { eexists. split.
      - zldr F_a1204 D_a1204 (trp + 8 * i) Rb.
        zstep F_a1208 D_a1208.
        zstep F_a120c D_a120c. rewrite E1.
        stepn F_a1210 D_a1210. rwH. rewrite art_zb_srli by lia.
        stepn F_a1214 D_a1214. rwH. rewrite art_zb_xor by lia. rewrite E2.
        zstep F_a1218 D_a1218. rewrite E3.
        stepn F_a121c D_a121c. rwH. rewrite art_zb_xor by lia. rewrite E4.
        zstep F_a1220 D_a1220. rewrite E5.
        zbtk F_a1224 D_a1224.
        apply mst_refl.
      - split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. intros r N11 N12 N15 N16. kept_solve. }
    destruct S1 as (r1 & RUN1 & Q11 & Q14 & Q10 & Q12 & K1).
    destruct (IH r1 M rom trp size mC (i + 1) u5 RC Ht1 Ht2 HmC R5 ltac:(lia) ltac:(lia) Q11 Q14 Q10 Q12) as (r2 & h2 & RUN2 & P11 & P12 & Rh2 & K2).
    exists r2, h2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [exact P11|]. split; [exact P12|]. split; [exact Rh2|].
    intros r N11 N12 N15 N16. rewrite (K2 r N11 N12 N15 N16). apply K1; assumption.
Qed.

Definition dp_nodes (M : word -> option byte) (l2 N : Z) : Prop :=
  forall id, 1 <= id <= N -> exists hv lk, 0 <= hv < 2 ^ 64 /\ cellA M (l2 + 16 * id) 8 hv /\ cellA M (l2 + 16 * id + 8) 4 lk /\ 0 <= lk < id.

Lemma dp_find_loop : forall (m : nat) regs (M rom : word -> option byte) (l2 N h cur : Z),
  (Z.to_nat cur <= m)%nat ->
  cellA M MAP1 8 l2 -> 4096 <= l2 -> l2 + 2 ^ 20 < 2 ^ 64 -> l2 mod 16 = 0 -> 0 <= N < 2 ^ 16 -> dp_nodes M l2 N ->
  0 <= cur <= N -> 0 <= h < 2 ^ 64 ->
  getr regs 11 = Z_to_bv 64 cur -> getr regs 19 = Z_to_bv 64 h -> getr regs 24 = Z_to_bv 64 MAP1 -> getr regs 22 = Z_to_bv 64 65535 ->
  exists regs',
    ((msteps ASEGS (mkst regs (0xa12e4 : word) M rom) (mkst regs' (0xa133c : word) M rom) /\ getr regs' 11 = Z_to_bv 64 0)
     \/ (msteps ASEGS (mkst regs (0xa12e4 : word) M rom) (mkst regs' (0xa13e8 : word) M rom) /\ exists id, 1 <= id <= N /\ getr regs' 10 = Z_to_bv 64 id))
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r).
Proof.
  induction m as [|m IH]; intros regs M rom l2 N h cur Hm CM Hl2 Hl2' Hl16 HN ND Hcur Hh H11 H19 H24 H22.
  - assert (cur = 0) by lia. subst cur.
    eexists. split; [left; split|].
    + zbtk F_a1294 D_a1294. apply mst_refl.
    + exact H11.
    + intros; reflexivity.
  - destruct (Z.eq_dec cur 0) as [->|NZ].
    { eexists. split; [left; split|].
      + zbtk F_a1294 D_a1294. apply mst_refl.
      + exact H11.
      + intros; reflexivity. }
    destruct (ND cur ltac:(lia)) as (hv & lk & Rhv & Chv & Clk & Rlk).
    unfold MAP1 in *.

    assert (S1 : exists r1, msteps ASEGS (mkst regs (0xa12e4 : word) M rom) (mkst r1 (0xa131c : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 cur /\ getr r1 11 = Z_to_bv 64 lk /\ getr r1 12 = Z_to_bv 64 hv /\ getr r1 19 = Z_to_bv 64 h
                  /\ getr r1 24 = Z_to_bv 64 6547624 /\ getr r1 22 = Z_to_bv 64 65535
                  /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr r1 r = getr regs r))).
    { eexists. split.
      - zbft F_a1294 D_a1294.
        zstep F_a1298 D_a1298.
        stepn F_a129c D_a129c. rwH. rewrite art_srliw_small by lia.
        zstep F_a12a0 D_a12a0.
        zstep F_a12a4 D_a12a4.
        zld F_a12a8 D_a12a8 6547624 CM.
        zbft F_a12ac D_a12ac.
        zstep F_a12b0 D_a12b0.
        stepn F_a12b4 D_a12b4. rwH. rewrite (art_zb_srli_exact (cur * 2 ^ 32) 32 cur) by lia.
        stepn F_a12b8 D_a12b8. rwH. rewrite art_zb_and by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
        rewrite (Z.mod_small cur (2 ^ 16)) by lia.
        zstep F_a12bc D_a12bc.
        zstep F_a12c0 D_a12c0.
        zld F_a12c4 D_a12c4 (l2 + 16 * cur) Chv.
        zlw F_a12c8 D_a12c8 (l2 + 16 * cur + 8) Clk.
        apply mst_refl.
      - repeat (split; [kept_solve|]). intros r N10 N11 N12. kept_solve. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q19 & Q24 & Q22 & K1).
    destruct (Z.eq_dec h hv) as [EQ|NE].
    +
      eexists. split; [right; split|].
      * eapply msteps_trans; [exact RUN1|].
        zbft F_a12cc D_a12cc.
        stepn F_a12d0 D_a12d0.
        apply mst_refl.
      * exists cur. split; [lia|]. kept_solve.
      * intros r N10 N11 N12. kept_solve || (gres; apply K1; assumption).
    +
      assert (S2 : exists r2, msteps ASEGS (mkst r1 (0xa131c : word) M rom) (mkst r2 (0xa12e4 : word) M rom)
                /\ (getr r2 11 = Z_to_bv 64 lk /\ getr r2 19 = Z_to_bv 64 h /\ getr r2 24 = Z_to_bv 64 6547624 /\ getr r2 22 = Z_to_bv 64 65535
                    /\ (forall r : reg, getr r2 r = getr r1 r))).
      { eexists. split.
        - zbtk F_a12cc D_a12cc. apply mst_refl.
        - repeat (split; [kept_solve|]). intros; reflexivity. }
      destruct S2 as (r2 & RUN2 & P11 & P19 & P24 & P22 & K2).
      destruct (IH r2 M rom l2 N h lk ltac:(lia) CM Hl2 Hl2' Hl16 HN ND ltac:(lia) Hh P11 P19 P24 P22) as (r3 & ALT & K3).
      exists r3. split.
      * destruct ALT as [[RUN3 A]|[RUN3 A]]; [left|right]; split; try exact A;
          (eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3).
      * intros r N10 N11 N12. rewrite (K3 r N10 N11 N12), (K2 r). apply K1; assumption.
Qed.

Definition dp_lock_mem (M : word -> option byte) (s adr v : Z) (raw : word) (x8 x9 x18 x19 : word) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (s - 8) (U raw)) (s - 16) (U x8)) (s - 24) (U x9)) (s - 32) (U x18)) (s - 40) (U x19))
     adr (Z.lor v 18446744071562067968).
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

Lemma dp_lock_run : forall regs (M rom : word -> option byte) (raw : word) (s adr v : Z),
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 adr -> getr regs 1 = raw -> ret_ok raw ->
  4096 <= s - 48 -> s < 2 ^ 64 -> 4096 <= adr -> adr + 4 < 2 ^ 64 -> adr mod 4 = 0 -> 0 <= v < 2 ^ 31 ->
  cellA M adr 4 v -> wrA M adr 4 -> wrA M (s - 48) 48 -> apart adr 4 (s - 48) 48 ->
  exists regs',
    msteps ASEGS (mkst regs (0xa1938 : word) M rom) (mkst regs' raw (dp_lock_mem M s adr v raw (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 10 = Z_to_bv 64 v /\ getr regs' 2 = Z_to_bv 64 s
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw s adr v H2 H10 H1 Hret Hs Hs' Ha Ha' Ha4 Hv Cv Wv Wf AP.
  unfold dp_lock_mem.
  eexists. split; [|split; [|split]].
  - zstep F_a18e8 D_a18e8.
    zsd F_a18ec D_a18ec (s - 8) (U raw) ltac:(rewok Wf).
    zsd F_a18f0 D_a18f0 (s - 16) (U (getr regs 8)) ltac:(rewok Wf).
    zsd F_a18f4 D_a18f4 (s - 24) (U (getr regs 9)) ltac:(rewok Wf).
    zsd F_a18f8 D_a18f8 (s - 32) (U (getr regs 18)) ltac:(rewok Wf).
    zsd F_a18fc D_a18fc (s - 40) (U (getr regs 19)) ltac:(rewok Wf).
    zstep F_a1900 D_a1900.
    zstep F_a1904 D_a1904.
    stepn F_a1908 D_a1908.
    zstep F_a190c D_a190c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cv' : cellA X adr 4 v) by recell Cv; assert (Wv' : wok Asan.M.loaded_segments X adr 4) by (rewok Wv) end.
    zlw F_a1910 D_a1910 adr Cv'.
    stepb_tk F_a1914 D_a1914 ltac:(zconds).
    stepn F_a1928 D_a1928. rwH.
    match goal with |- context [v_or (Z_to_bv 64 v) ?L] =>
      replace (v_or (Z_to_bv 64 v) L) with (Z_to_bv 64 (Z.lor v 18446744071562067968) : word)
        by (symmetry; replace L with (Z_to_bv 64 18446744071562067968 : word) by (apply bv_eq; vm_compute; reflexivity); apply art_zb_or; lia) end.

    chain_step; [reflexivity
      | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 adr) _ (Z_to_bv 64 v));
        [exact F_a192c | reflexivity | exact D_a192c | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Ha4
        | exact Cv' | apply art_bytes4; lia ]
      | ]. wpc. rewrite art_v_lw_small by lia.

    chain_step; [reflexivity
      | eapply art_step_branch_ft_r; [exact F_a1930 | reflexivity | exact D_a1930 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
      | ]. wpc.

    chain_step; [reflexivity
      | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 adr));
        [exact F_a1934 | reflexivity | exact D_a1934 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Ha4 | gres; rwH; reflexivity
        | exact Wv' ]
      | ]. wpc.
    change (wbytes ?M0 (Z_to_bv 64 adr) (word_to_le_bytes 4 (Z_to_bv 64 (Z.lor v 18446744071562067968)))) with (Wn 4 M0 adr (Z.lor v 18446744071562067968)).
    zbft F_a1938 D_a1938.
    stepb_tk F_a193c D_a193c ltac:(zconds).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (L1 : cellA X (s - 8) 8 (U raw)) by zcell;
      assert (L2 : cellA X (s - 16) 8 (U (getr regs 8))) by zcell;
      assert (L3 : cellA X (s - 24) 8 (U (getr regs 9))) by zcell;
      assert (L4 : cellA X (s - 32) 8 (U (getr regs 18))) by zcell;
      assert (L5 : cellA X (s - 40) 8 (U (getr regs 19))) by zcell end.
    zld F_a195c D_a195c (s - 8) L1. rewrite Z_to_bv_bv_unsigned.
    zld F_a1960 D_a1960 (s - 16) L2. rewrite Z_to_bv_bv_unsigned.
    zld F_a1964 D_a1964 (s - 24) L3. rewrite Z_to_bv_bv_unsigned.
    zld F_a1968 D_a1968 (s - 32) L4. rewrite Z_to_bv_bv_unsigned.
    zld F_a196c D_a196c (s - 40) L5. rewrite Z_to_bv_bv_unsigned.
    zstep F_a1970 D_a1970.
    stepret F_a1974 D_a1974 raw ltac:(rwH; reflexivity).
    replace (s - 48 + 48) with s by lia. apply mst_refl.
  - kept_solve.
  - kept_solve.
  - intros r N10 N11 N12 N13 N14. kept_solve.
Qed.

Definition dp_frame (M : word -> option byte) (s trp szt : Z) (raw : word) (rg : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19)))
    (s - 48) (U (getr rg 20))) (s - 56) (U (getr rg 21))) (s - 64) (U (getr rg 22))) (s - 72) (U (getr rg 23))) (s - 80) (U (getr rg 24)))
    (s - 88) (U (getr rg 25))) (s - 104) trp) (s - 96) szt.

Lemma mod_mul_pow44 : forall h, 0 <= h -> (h * 2 ^ 44) mod 2 ^ 64 = (h mod 2 ^ 20) * 2 ^ 44.
Proof. intros h Hh. change (2 ^ 64) with (2 ^ 20 * 2 ^ 44). rewrite Z.mul_mod_distr_r by lia. reflexivity. Qed.

Lemma dp_pro_run : forall regs (M rom : word -> option byte) (raw : word) (s trp size mC k1 k2 : Z),
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 trp -> getr regs 11 = Z_to_bv 64 size -> getr regs 1 = raw ->
  0x6b3000 <= s - 224 -> s < 2 ^ 64 -> 4096 <= trp -> trp + 8 * size < 2 ^ 64 -> 1 <= size <= 30 ->
  0 <= mC < 2 ^ 64 -> 0 <= k1 < 2 ^ 64 -> 0 <= k2 < 2 ^ 64 ->
  cellA M 0x102e8 8 mC -> cellA M 0x10328 8 k1 -> cellA M 0x10438 8 k2 -> wrA M (s - 224) 224 ->
  exists regs' h0,
    msteps ASEGS (mkst regs (0xa11a4 : word) M rom) (mkst regs' (0xa1254 : word) (dp_frame M s trp size raw regs) rom)
    /\ getr regs' 11 = Z_to_bv 64 trp /\ getr regs' 14 = Z_to_bv 64 (trp + 8 * size) /\ getr regs' 10 = Z_to_bv 64 mC /\ getr regs' 12 = Z_to_bv 64 h0
    /\ 0 <= h0 < 2 ^ 64 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 DEP /\ getr regs' 2 = Z_to_bv 64 (s - 112)
    /\ (forall r : reg, r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> ~ (10 <= U r <= 16) -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw s trp size mC k1 k2 H2 H10 H11 H1 Hs Hs' Ht Ht' Hsz HmC Hk1 Hk2 CmC Ck1 Ck2 W.
  destruct (zb_fresh (size * k1)) as [u1 [R1 E1]].
  destruct (zb_fresh (Z.lxor u1 k2)) as [h0 [R0 E0]].
  unfold dp_frame, DEP.
  eexists _, h0. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - zstep F_a1154 D_a1154.
    stepn F_a1158 D_a1158.
    stepn F_a115c D_a115c.
    zstep F_a1160 D_a1160.
    zstep F_a1164 D_a1164.
    zstep F_a1168 D_a1168.
    zstep F_a116c D_a116c.
    stepn F_a1170 D_a1170.
    zstep F_a1174 D_a1174.
    zsd F_a1178 D_a1178 (s - 8) (U raw) ltac:(rewok W).
    zsd F_a117c D_a117c (s - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_a1180 D_a1180 (s - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_a1184 D_a1184 (s - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_a1188 D_a1188 (s - 40) (U (getr regs 19)) ltac:(rewok W).
    zsd F_a118c D_a118c (s - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_a1190 D_a1190 (s - 56) (U (getr regs 21)) ltac:(rewok W).
    zsd F_a1194 D_a1194 (s - 64) (U (getr regs 22)) ltac:(rewok W).
    zsd F_a1198 D_a1198 (s - 72) (U (getr regs 23)) ltac:(rewok W).
    zsd F_a119c D_a119c (s - 80) (U (getr regs 24)) ltac:(rewok W).
    zsd F_a11a0 D_a11a0 (s - 88) (U (getr regs 25)) ltac:(rewok W).
    zstep F_a11a4 D_a11a4.
    zstep F_a11a8 D_a11a8.
    zsd F_a11ac D_a11ac (s - 104) trp ltac:(rewok W).
    zsd F_a11b0 D_a11b0 (s - 96) size ltac:(rewok W).
    zbtk F_a11b4 D_a11b4.
    stepn F_a11bc D_a11bc. rwH. unfold v_addiw. rewrite art_u_lit by lia.
    replace (bv_swrap 32 (size + 0)) with size by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).
    zstep F_a11c0 D_a11c0.
    zbft F_a11c4 D_a11c4.
    zbft F_a11c8 D_a11c8.
    stepn F_a11cc D_a11cc. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small size (2 ^ 32)) by lia.
    stepn F_a11d0 D_a11d0.
    stepn F_a11d4 D_a11d4.
    stepn F_a11d8 D_a11d8.
    stepn F_a11dc D_a11dc.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (C1 : cellA X 0x10328 8 k1) by zcell; assert (C2 : cellA X 0x10438 8 k2) by zcell; assert (C0 : cellA X 0x102e8 8 mC) by zcell end.
    zld F_a11e0 D_a11e0 0x10328 C1.
    stepn F_a11e4 D_a11e4. rwH.
    match goal with |- context [v_and (Z_to_bv 64 size) ?L] =>
      replace (v_and (Z_to_bv 64 size) L) with (Z_to_bv 64 size : word)
        by (symmetry; replace L with (Z_to_bv 64 (Z.ones 32) : word) by (apply bv_eq; vm_compute; reflexivity);
            rewrite art_zb_and by (change (Z.ones 32) with 4294967295; lia); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia) end.
    stepn F_a11e8 D_a11e8.
    zld F_a11ec D_a11ec 0x10438 C2.
    zld F_a11f0 D_a11f0 0x102e8 C0.
    zstep F_a11f4 D_a11f4. rewrite E1.
    zstep F_a11f8 D_a11f8.
    stepn F_a11fc D_a11fc. rwH. rewrite art_zb_xor by lia. rewrite E0.
    zstep F_a1200 D_a1200.
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
  - intros r N2 N8 N9 NR.
    destruct (decide (r = 10%bv)) as [->|N10]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 11%bv)) as [->|N11]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 12%bv)) as [->|N12]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 13%bv)) as [->|N13]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 14%bv)) as [->|N14]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 15%bv)) as [->|N15]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 16%bv)) as [->|N16]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    kept_solve.
Qed.

Lemma dp_mid_run : forall regs (M rom : word -> option byte) (hN mC N : Z),
  getr regs 12 = Z_to_bv 64 hN -> getr regs 13 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 mC -> getr regs 9 = Z_to_bv 64 DEP ->
  0 <= hN < 2 ^ 64 -> 0 <= mC < 2 ^ 64 -> 0 <= N < 2 ^ 16 ->
  (forall b, 0 <= b < 2 ^ 20 -> exists v, cellA M (DEP + 4 * b) 4 v /\ 0 <= v <= N) ->
  exists regs' h b v,
    msteps ASEGS (mkst regs (0xa1278 : word) M rom) (mkst regs' (0xa12e4 : word) M rom)
    /\ 0 <= h < 2 ^ 64 /\ 0 <= b < 2 ^ 20 /\ cellA M (DEP + 4 * b) 4 v /\ 0 <= v <= N
    /\ getr regs' 19 = Z_to_bv 64 h /\ getr regs' 18 = Z_to_bv 64 (DEP + 4 * b) /\ getr regs' 11 = Z_to_bv 64 v /\ getr regs' 25 = Z_to_bv 64 v
    /\ getr regs' 24 = Z_to_bv 64 MAP1 /\ getr regs' 20 = Z_to_bv 64 (DEP + 4194312) /\ getr regs' 22 = Z_to_bv 64 65535 /\ getr regs' 23 = Z_to_bv 64 2147483647
    /\ getr regs' 9 = Z_to_bv 64 DEP
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> ~ (18 <= U r <= 20) -> ~ (22 <= U r <= 25) -> getr regs' r = getr regs r).
Proof.
  intros regs M rom hN mC N H12 H13 H10 H9 HhN HmC HN BK.
  destruct (zb_fresh (0 * mC)) as [u1 [R1 E1]].
  pose proof (Z.div_pos u1 (2 ^ 47) ltac:(lia) ltac:(lia)) as D1. pose proof (Z.div_lt_upper_bound u1 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D1'.
  destruct (zb_fresh (Z.lxor (u1 / 2 ^ 47) u1)) as [u2 [R2 E2]].
  destruct (zb_fresh (u2 * mC)) as [u3 [R3 E3]].
  destruct (zb_fresh (Z.lxor u3 hN)) as [u4 [R4 E4]].
  destruct (zb_fresh (u4 * mC)) as [u5 [R5 E5]].
  pose proof (Z.div_pos u5 (2 ^ 47) ltac:(lia) ltac:(lia)) as D5. pose proof (Z.div_lt_upper_bound u5 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D5'.
  destruct (zb_fresh (Z.lxor (u5 / 2 ^ 47) u5)) as [u6 [R6 E6]].
  destruct (zb_fresh (u6 * mC)) as [u7 [R7 E7]].
  pose proof (Z.div_pos u7 (2 ^ 47) ltac:(lia) ltac:(lia)) as D7. pose proof (Z.div_lt_upper_bound u7 (2 ^ 47) (2 ^ 17) ltac:(lia) ltac:(lia)) as D7'.
  destruct (zb_fresh (Z.lxor (u7 / 2 ^ 47) u7)) as [h [Rh Eh]].
  set (b := h mod 2 ^ 20). pose proof (Z.mod_pos_bound h (2 ^ 20) ltac:(lia)) as Rb.
  destruct (BK b ltac:(lia)) as (v & Cv & Rv).
  unfold DEP, MAP1 in *.
  eexists _, h, b, v. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]].
  - stepn F_a1228 D_a1228.
    stepn F_a122c D_a122c.
    zstep F_a1230 D_a1230. rewrite E1.
    stepn F_a1234 D_a1234.
    stepn F_a1238 D_a1238.
    stepn F_a123c D_a123c.
    stepn F_a1240 D_a1240. rwH. rewrite art_zb_srli by lia.
    stepn F_a1244 D_a1244. rwH. rewrite art_zb_xor by lia. rewrite E2.
    zstep F_a1248 D_a1248. rewrite E3.
    stepn F_a124c D_a124c. rwH. rewrite art_zb_xor by lia. rewrite E4.
    zstep F_a1250 D_a1250. rewrite E5.
    stepn F_a1254 D_a1254. rwH. rewrite art_zb_srli by lia.
    stepn F_a1258 D_a1258. rwH. rewrite art_zb_xor by lia. rewrite E6.
    zstep F_a125c D_a125c. rewrite E7.
    stepn F_a1260 D_a1260. rwH. rewrite art_zb_srli by lia.
    stepn F_a1264 D_a1264. rwH. rewrite art_zb_xor by lia. rewrite Eh.
    zstep F_a1268 D_a1268.
    replace (Z_to_bv 64 (h * 2 ^ 44) : word) with (Z_to_bv 64 (b * 2 ^ 44) : word)
      by (apply art_zb_eq; rewrite (mod_mul_pow44 h) by lia; subst b; rewrite Z.mod_small; [reflexivity | nia]).
    stepn F_a126c D_a126c. rwH. rewrite (art_zb_srli_exact (b * 2 ^ 44) 42 (4 * b)) by lia.
    zstep F_a1270 D_a1270.
    zlw F_a1274 D_a1274 (2353304 + 4 * b) Cv.
    stepn F_a1278 D_a1278.
    zstep F_a127c D_a127c.
    stepfence F_a1280 D_a1280.
    stepn F_a1284 D_a1284. rwH.
    match goal with |- context [v_and (Z_to_bv 64 v) ?L] =>
      replace (v_and (Z_to_bv 64 v) L) with (Z_to_bv 64 v : word)
        by (symmetry; replace L with (Z_to_bv 64 (Z.ones 31) : word) by (apply bv_eq; vm_compute; reflexivity);
            rewrite art_zb_and by (change (Z.ones 31) with 2147483647; lia); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia) end.
    stepn F_a1288 D_a1288.
    zstep F_a128c D_a128c.
    zstep F_a1290 D_a1290.
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
  - intros r N10 N11 N12 N13 N14 NA NB.
    destruct (decide (r = 18%bv)) as [->|N18]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 19%bv)) as [->|N19]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 20%bv)) as [->|N20]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 22%bv)) as [->|N22]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 23%bv)) as [->|N23]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 24%bv)) as [->|N24]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 25%bv)) as [->|N25]; [exfalso; apply NB; clear; vm_compute; split; discriminate|].
    kept_solve.
Qed.

Lemma dp_epi_run : forall (regs0 regs : bvmap 5 word) (X rom : word -> option byte) (raw : word) (s : Z),
  getr regs 2 = Z_to_bv 64 (s - 112) -> ret_ok raw -> 4096 <= s - 112 -> s < 2 ^ 64 ->
  cellA X (s - 8) 8 (U raw) -> cellA X (s - 16) 8 (U (getr regs0 8)) -> cellA X (s - 24) 8 (U (getr regs0 9)) ->
  cellA X (s - 32) 8 (U (getr regs0 18)) -> cellA X (s - 40) 8 (U (getr regs0 19)) -> cellA X (s - 48) 8 (U (getr regs0 20)) ->
  cellA X (s - 56) 8 (U (getr regs0 21)) -> cellA X (s - 64) 8 (U (getr regs0 22)) -> cellA X (s - 72) 8 (U (getr regs0 23)) ->
  cellA X (s - 80) 8 (U (getr regs0 24)) -> cellA X (s - 88) 8 (U (getr regs0 25)) ->
  exists regs',
    msteps ASEGS (mkst regs (0xa13e8 : word) X rom) (mkst regs' raw X rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = raw
    /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18 /\ getr regs' 19 = getr regs0 19
    /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21 /\ getr regs' 22 = getr regs0 22 /\ getr regs' 23 = getr regs0 23
    /\ getr regs' 24 = getr regs0 24 /\ getr regs' 25 = getr regs0 25
    /\ (forall r : reg, r <> 1%bv -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> ~ (18 <= U r <= 25) -> getr regs' r = getr regs r).
Proof.
  intros regs0 regs X rom raw s H2 Hret Hs Hs' L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11.
  eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]].
  - zld F_a1398 D_a1398 (s - 8) L1. rewrite Z_to_bv_bv_unsigned.
    zld F_a139c D_a139c (s - 16) L2. rewrite Z_to_bv_bv_unsigned.
    zld F_a13a0 D_a13a0 (s - 24) L3. rewrite Z_to_bv_bv_unsigned.
    zld F_a13a4 D_a13a4 (s - 32) L4. rewrite Z_to_bv_bv_unsigned.
    zld F_a13a8 D_a13a8 (s - 40) L5. rewrite Z_to_bv_bv_unsigned.
    zld F_a13ac D_a13ac (s - 48) L6. rewrite Z_to_bv_bv_unsigned.
    zld F_a13b0 D_a13b0 (s - 56) L7. rewrite Z_to_bv_bv_unsigned.
    zld F_a13b4 D_a13b4 (s - 64) L8. rewrite Z_to_bv_bv_unsigned.
    zld F_a13b8 D_a13b8 (s - 72) L9. rewrite Z_to_bv_bv_unsigned.
    zld F_a13bc D_a13bc (s - 80) L10. rewrite Z_to_bv_bv_unsigned.
    zld F_a13c0 D_a13c0 (s - 88) L11. rewrite Z_to_bv_bv_unsigned.
    zstep F_a13c4 D_a13c4.
    stepret F_a13c8 D_a13c8 raw ltac:(rwH; reflexivity).
    replace (s - 112 + 112) with s by lia. apply mst_refl.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r N1 N2 N8 N9 NA.
    destruct (decide (r = 18%bv)) as [->|N18]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 19%bv)) as [->|N19]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 20%bv)) as [->|N20]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 21%bv)) as [->|N21]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 22%bv)) as [->|N22]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 23%bv)) as [->|N23]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 24%bv)) as [->|N24]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 25%bv)) as [->|N25]; [exfalso; apply NA; clear; vm_compute; split; discriminate|].
    kept_solve.
Qed.
End FPX.
