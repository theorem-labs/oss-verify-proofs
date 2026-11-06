(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_80128_803cc Bo0_code_80808_8094c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition DEP : Z := 0x1c0618.       (* [comment removed for export] *)
Definition NID : Z := 0x5c0618.       (* [comment removed for export] *)
Definition MAP1 : Z := 0x5c0628.      (* [comment removed for export] *)
Definition STO : Z := 0x1b0608.       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Lemma zb_fresh : forall e, exists u, 0 <= u < 2 ^ 64 /\ Z_to_bv 64 e = Z_to_bv 64 u.
Proof.
  intros e. exists (e mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|].
  apply art_zb_eq. rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac zfresh u :=
  lazymatch goal with |- msteps _ (mkst (regupd _ _ (Z_to_bv 64 ?e)) _ _ _) _ =>
    let R := fresh "R" u in let E := fresh "E" u in
    destruct (zb_fresh e) as [u [R E]]; rewrite E; clear E
  end.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition rcell (M : word -> option byte) (a : Z) : Prop := exists bs, rdn ASEGS M (Z_to_bv 64 a) 8%nat = Some bs.
Lemma rcell_grows : forall M M' a, mem_grows M M' -> rcell M a -> rcell M' a.
Proof. intros M M' a G (bs & R). destruct (rdn_grows _ _ _ _ _ _ G R) as [bs' R']. exists bs'. exact R'. Qed.
Lemma art_bytes8_range : forall M (a : word) bs, rdn ASEGS M a 8%nat = Some bs -> 0 <= bytes_le_to_Z bs < 2 ^ 64.
Proof.
  intros M a bs H. pose proof (rdn_length _ _ _ _ _ H) as L. pose proof (bytes_le_to_Z_bound bs) as B.
  pose proof (bytes_le_to_Z_nonneg bs). rewrite L in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B. lia.
Qed.
(* [comment removed for export] *)
Ltac zldr F D a R :=
  chain_step; [reflexivity
    | eapply step_ld with (v := Z_to_bv 64 (bytes_le_to_Z _)); [exact F | reflexivity | exact D | zaddr a; exact R | rewrite art_u_lit; [reflexivity | eapply art_bytes8_range; exact R] ]
    | step_simpl; vnorm].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac zconds := rwH; rewrite ?art_c_eq_zb, ?art_c_ltu_zb, ?art_c_lts_zb by lia;
  first [ apply Z.eqb_neq; lia | apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia ].

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dp_hash_loop : forall (q : nat) regs (M rom : word -> option byte) (trp size mC i h : Z),
  (forall j, 0 <= j < size -> rcell M (trp + 8 * j)) ->
  0 <= trp -> trp + 8 * size < 2 ^ 64 -> 0 <= mC < 2 ^ 64 -> 0 <= h < 2 ^ 64 -> 0 <= i -> i + Z.of_nat q + 1 = size ->
  getr regs 11 = Z_to_bv 64 (trp + 8 * i) -> getr regs 14 = Z_to_bv 64 (trp + 8 * size) -> getr regs 10 = Z_to_bv 64 mC -> getr regs 12 = Z_to_bv 64 h ->
  exists regs' h',
    msteps ASEGS (mkst regs (0x801d8 : word) M rom) (mkst regs' (0x801fc : word) M rom)
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
    + zldr F_801d8 D_801d8 (trp + 8 * i) Rb.                                    (* [comment removed for export] *)
      zstep F_801dc D_801dc.                                                     (* [comment removed for export] *)
      zstep F_801e0 D_801e0. rewrite E1.                                         (* [comment removed for export] *)
      stepn F_801e4 D_801e4. rwH. rewrite art_zb_srli by lia.                    (* [comment removed for export] *)
      stepn F_801e8 D_801e8. rwH. rewrite art_zb_xor by lia. rewrite E2.         (* [comment removed for export] *)
      zstep F_801ec D_801ec. rewrite E3.                                         (* [comment removed for export] *)
      stepn F_801f0 D_801f0. rwH. rewrite art_zb_xor by lia. rewrite E4.         (* [comment removed for export] *)
      zstep F_801f4 D_801f4. rewrite E5.                                         (* [comment removed for export] *)
      zbft F_801f8 D_801f8.                                                      (* [comment removed for export] *)
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
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x801d8 : word) M rom) (mkst r1 (0x801d8 : word) M rom)
              /\ (getr r1 11 = Z_to_bv 64 (trp + 8 * (i + 1)) /\ getr r1 14 = Z_to_bv 64 (trp + 8 * size) /\ getr r1 10 = Z_to_bv 64 mC
                  /\ getr r1 12 = Z_to_bv 64 u5
                  /\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> getr r1 r = getr regs r))).
    { eexists. split.
      - zldr F_801d8 D_801d8 (trp + 8 * i) Rb.                                  (* [comment removed for export] *)
        zstep F_801dc D_801dc.                                                   (* [comment removed for export] *)
        zstep F_801e0 D_801e0. rewrite E1.                                       (* [comment removed for export] *)
        stepn F_801e4 D_801e4. rwH. rewrite art_zb_srli by lia.                  (* [comment removed for export] *)
        stepn F_801e8 D_801e8. rwH. rewrite art_zb_xor by lia. rewrite E2.       (* [comment removed for export] *)
        zstep F_801ec D_801ec. rewrite E3.                                       (* [comment removed for export] *)
        stepn F_801f0 D_801f0. rwH. rewrite art_zb_xor by lia. rewrite E4.       (* [comment removed for export] *)
        zstep F_801f4 D_801f4. rewrite E5.                                       (* [comment removed for export] *)
        zbtk F_801f8 D_801f8.                                                    (* [comment removed for export] *)
        apply mst_refl.
      - split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. intros r N11 N12 N15 N16. kept_solve. }
    destruct S1 as (r1 & RUN1 & Q11 & Q14 & Q10 & Q12 & K1).
    destruct (IH r1 M rom trp size mC (i + 1) u5 RC Ht1 Ht2 HmC R5 ltac:(lia) ltac:(lia) Q11 Q14 Q10 Q12) as (r2 & h2 & RUN2 & P11 & P12 & Rh2 & K2).
    exists r2, h2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [exact P11|]. split; [exact P12|]. split; [exact Rh2|].
    intros r N11 N12 N15 N16. rewrite (K2 r N11 N12 N15 N16). apply K1; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dp_nodes (M : word -> option byte) (l2 N : Z) : Prop :=
  forall id, 1 <= id <= N -> exists hv lk, 0 <= hv < 2 ^ 64 /\ cellA M (l2 + 16 * id) 8 hv /\ cellA M (l2 + 16 * id + 8) 4 lk /\ 0 <= lk < id.

Lemma dp_find_loop : forall (m : nat) regs (M rom : word -> option byte) (l2 N h cur : Z),
  (Z.to_nat cur <= m)%nat ->
  cellA M MAP1 8 l2 -> 4096 <= l2 -> l2 + 2 ^ 20 < 2 ^ 64 -> l2 mod 16 = 0 -> 0 <= N < 2 ^ 16 -> dp_nodes M l2 N ->
  0 <= cur <= N -> 0 <= h < 2 ^ 64 ->
  getr regs 11 = Z_to_bv 64 cur -> getr regs 19 = Z_to_bv 64 h -> getr regs 24 = Z_to_bv 64 MAP1 -> getr regs 22 = Z_to_bv 64 65535 ->
  exists regs',
    ((msteps ASEGS (mkst regs (0x80268 : word) M rom) (mkst regs' (0x802c0 : word) M rom) /\ getr regs' 11 = Z_to_bv 64 0)
     \/ (msteps ASEGS (mkst regs (0x80268 : word) M rom) (mkst regs' (0x8036c : word) M rom) /\ exists id, 1 <= id <= N /\ getr regs' 10 = Z_to_bv 64 id))
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r).
Proof.
  induction m as [|m IH]; intros regs M rom l2 N h cur Hm CM Hl2 Hl2' Hl16 HN ND Hcur Hh H11 H19 H24 H22.
  - assert (cur = 0) by lia. subst cur.
    eexists. split; [left; split|].
    + zbtk F_80268 D_80268. apply mst_refl.
    + exact H11.
    + intros; reflexivity.
  - destruct (Z.eq_dec cur 0) as [->|NZ].
    { eexists. split; [left; split|].
      + zbtk F_80268 D_80268. apply mst_refl.
      + exact H11.
      + intros; reflexivity. }
    destruct (ND cur ltac:(lia)) as (hv & lk & Rhv & Chv & Clk & Rlk).
    unfold MAP1 in *.
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x80268 : word) M rom) (mkst r1 (0x802a0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 cur /\ getr r1 11 = Z_to_bv 64 lk /\ getr r1 12 = Z_to_bv 64 hv /\ getr r1 19 = Z_to_bv 64 h
                  /\ getr r1 24 = Z_to_bv 64 6030888 /\ getr r1 22 = Z_to_bv 64 65535
                  /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr r1 r = getr regs r))).
    { eexists. split.
      - zbft F_80268 D_80268.                                                    (* [comment removed for export] *)
        zstep F_8026c D_8026c.                                                   (* [comment removed for export] *)
        stepn F_80270 D_80270. rwH. rewrite art_srliw_small by lia.              (* [comment removed for export] *)
        zstep F_80274 D_80274.                                                   (* [comment removed for export] *)
        zstep F_80278 D_80278.                                                   (* [comment removed for export] *)
        zld F_8027c D_8027c 6030888 CM.                                          (* [comment removed for export] *)
        zbft F_80280 D_80280.                                                    (* [comment removed for export] *)
        zstep F_80284 D_80284.                                                   (* [comment removed for export] *)
        stepn F_80288 D_80288. rwH. rewrite (art_zb_srli_exact (cur * 2 ^ 32) 32 cur) by lia.   (* [comment removed for export] *)
        stepn F_8028c D_8028c. rwH. rewrite art_zb_and by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
        rewrite (Z.mod_small cur (2 ^ 16)) by lia.                              (* [comment removed for export] *)
        zstep F_80290 D_80290.                                                   (* [comment removed for export] *)
        zstep F_80294 D_80294.                                                   (* [comment removed for export] *)
        zld F_80298 D_80298 (l2 + 16 * cur) Chv.                                 (* [comment removed for export] *)
        zlw F_8029c D_8029c (l2 + 16 * cur + 8) Clk.                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat (split; [kept_solve|]). intros r N10 N11 N12. kept_solve. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q19 & Q24 & Q22 & K1).
    destruct (Z.eq_dec h hv) as [EQ|NE].
    + (* [comment removed for export] *)
      eexists. split; [right; split|].
      * eapply msteps_trans; [exact RUN1|].
        zbft F_802a0 D_802a0.                                                    (* [comment removed for export] *)
        stepn F_802a4 D_802a4.                                                   (* [comment removed for export] *)
        apply mst_refl.
      * exists cur. split; [lia|]. kept_solve.
      * intros r N10 N11 N12. kept_solve || (gres; apply K1; assumption).
    + (* [comment removed for export] *)
      assert (S2 : exists r2, msteps ASEGS (mkst r1 (0x802a0 : word) M rom) (mkst r2 (0x80268 : word) M rom)
                /\ (getr r2 11 = Z_to_bv 64 lk /\ getr r2 19 = Z_to_bv 64 h /\ getr r2 24 = Z_to_bv 64 6030888 /\ getr r2 22 = Z_to_bv 64 65535
                    /\ (forall r : reg, getr r2 r = getr r1 r))).
      { eexists. split.
        - zbtk F_802a0 D_802a0. apply mst_refl.
        - repeat (split; [kept_solve|]). intros; reflexivity. }
      destruct S2 as (r2 & RUN2 & P11 & P19 & P24 & P22 & K2).
      destruct (IH r2 M rom l2 N h lk ltac:(lia) CM Hl2 Hl2' Hl16 HN ND ltac:(lia) Hh P11 P19 P24 P22) as (r3 & ALT & K3).
      exists r3. split.
      * destruct ALT as [[RUN3 A]|[RUN3 A]]; [left|right]; split; try exact A;
          (eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3).
      * intros r N10 N11 N12. rewrite (K3 r N10 N11 N12), (K2 r). apply K1; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dp_lock_mem (M : word -> option byte) (s adr v : Z) (raw : word) (x8 x9 x18 x19 : word) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (s - 8) (U raw)) (s - 16) (U x8)) (s - 24) (U x9)) (s - 32) (U x18)) (s - 40) (U x19))
     adr (Z.lor v 18446744071562067968).
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

Lemma dp_lock_run : forall regs (M rom : word -> option byte) (raw : word) (s adr v : Z),
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 adr -> getr regs 1 = raw -> ret_ok raw ->
  4096 <= s - 48 -> s < 2 ^ 64 -> 4096 <= adr -> adr + 4 < 2 ^ 64 -> adr mod 4 = 0 -> 0 <= v < 2 ^ 31 ->
  cellA M adr 4 v -> wrA M adr 4 -> wrA M (s - 48) 48 -> apart adr 4 (s - 48) 48 ->
  exists regs',
    msteps ASEGS (mkst regs (0x808bc : word) M rom) (mkst regs' raw (dp_lock_mem M s adr v raw (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 10 = Z_to_bv 64 v /\ getr regs' 2 = Z_to_bv 64 s
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw s adr v H2 H10 H1 Hret Hs Hs' Ha Ha' Ha4 Hv Cv Wv Wf AP.
  unfold dp_lock_mem.
  eexists. split; [|split; [|split]].
  - zstep F_808bc D_808bc.                                                       (* [comment removed for export] *)
    zsd F_808c0 D_808c0 (s - 8) (U raw) ltac:(rewok Wf).                           (* [comment removed for export] *)
    zsd F_808c4 D_808c4 (s - 16) (U (getr regs 8)) ltac:(rewok Wf).                 (* [comment removed for export] *)
    zsd F_808c8 D_808c8 (s - 24) (U (getr regs 9)) ltac:(rewok Wf).                 (* [comment removed for export] *)
    zsd F_808cc D_808cc (s - 32) (U (getr regs 18)) ltac:(rewok Wf).                (* [comment removed for export] *)
    zsd F_808d0 D_808d0 (s - 40) (U (getr regs 19)) ltac:(rewok Wf).                (* [comment removed for export] *)
    zstep F_808d4 D_808d4.                                                       (* [comment removed for export] *)
    zstep F_808d8 D_808d8.                                                       (* [comment removed for export] *)
    stepn F_808dc D_808dc.                                                       (* [comment removed for export] *)
    zstep F_808e0 D_808e0.                                                       (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cv' : cellA X adr 4 v) by recell Cv; assert (Wv' : wok AsanUbsan.M.loaded_segments X adr 4) by (rewok Wv) end.
    zlw F_808e4 D_808e4 adr Cv'.                                                 (* [comment removed for export] *)
    stepb_tk F_808e8 D_808e8 ltac:(zconds).                                      (* [comment removed for export] *)
    stepn F_808fc D_808fc. rwH.                                                  (* [comment removed for export] *)
    match goal with |- context [v_or (Z_to_bv 64 v) ?L] =>
      replace (v_or (Z_to_bv 64 v) L) with (Z_to_bv 64 (Z.lor v 18446744071562067968) : word)
        by (symmetry; replace L with (Z_to_bv 64 18446744071562067968 : word) by (apply bv_eq; vm_compute; reflexivity); apply art_zb_or; lia) end.
    (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 adr) _ (Z_to_bv 64 v));
        [exact F_80900 | reflexivity | exact D_80900 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Ha4
        | exact Cv' | apply art_bytes4; lia ]
      | ]. wpc. rewrite art_v_lw_small by lia.
    (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply art_step_branch_ft_r; [exact F_80904 | reflexivity | exact D_80904 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
      | ]. wpc.
    (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 adr));
        [exact F_80908 | reflexivity | exact D_80908 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Ha4 | gres; rwH; reflexivity
        | exact Wv' ]
      | ]. wpc.
    change (wbytes ?M0 (Z_to_bv 64 adr) (word_to_le_bytes 4 (Z_to_bv 64 (Z.lor v 18446744071562067968)))) with (Wn 4 M0 adr (Z.lor v 18446744071562067968)).
    zbft F_8090c D_8090c.                                                        (* [comment removed for export] *)
    stepb_tk F_80910 D_80910 ltac:(zconds).                                      (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (L1 : cellA X (s - 8) 8 (U raw)) by zcell;
      assert (L2 : cellA X (s - 16) 8 (U (getr regs 8))) by zcell;
      assert (L3 : cellA X (s - 24) 8 (U (getr regs 9))) by zcell;
      assert (L4 : cellA X (s - 32) 8 (U (getr regs 18))) by zcell;
      assert (L5 : cellA X (s - 40) 8 (U (getr regs 19))) by zcell end.
    zld F_80930 D_80930 (s - 8) L1. rewrite Z_to_bv_bv_unsigned.                 (* [comment removed for export] *)
    zld F_80934 D_80934 (s - 16) L2. rewrite Z_to_bv_bv_unsigned.                (* [comment removed for export] *)
    zld F_80938 D_80938 (s - 24) L3. rewrite Z_to_bv_bv_unsigned.                (* [comment removed for export] *)
    zld F_8093c D_8093c (s - 32) L4. rewrite Z_to_bv_bv_unsigned.                (* [comment removed for export] *)
    zld F_80940 D_80940 (s - 40) L5. rewrite Z_to_bv_bv_unsigned.                (* [comment removed for export] *)
    zstep F_80944 D_80944.                                                       (* [comment removed for export] *)
    stepret F_80948 D_80948 raw ltac:(rwH; reflexivity).
    replace (s - 48 + 48) with s by lia. apply mst_refl.
  - kept_solve.
  - kept_solve.
  - intros r N10 N11 N12 N13 N14. kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dp_frame (M : word -> option byte) (s trp szt : Z) (raw : word) (rg : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19)))
    (s - 48) (U (getr rg 20))) (s - 56) (U (getr rg 21))) (s - 64) (U (getr rg 22))) (s - 72) (U (getr rg 23))) (s - 80) (U (getr rg 24)))
    (s - 88) (U (getr rg 25))) (s - 104) trp) (s - 96) szt.

Lemma mod_mul_pow44 : forall h, 0 <= h -> (h * 2 ^ 44) mod 2 ^ 64 = (h mod 2 ^ 20) * 2 ^ 44.
Proof. intros h Hh. change (2 ^ 64) with (2 ^ 20 * 2 ^ 44). rewrite Z.mul_mod_distr_r by lia. reflexivity. Qed.

Lemma dp_pro_run : forall regs (M rom : word -> option byte) (raw : word) (s trp size mC k1 k2 : Z),
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 trp -> getr regs 11 = Z_to_bv 64 size -> getr regs 1 = raw ->
  0x634000 <= s - 224 -> s < 2 ^ 64 -> 4096 <= trp -> trp + 8 * size < 2 ^ 64 -> 1 <= size <= 30 ->
  0 <= mC < 2 ^ 64 -> 0 <= k1 < 2 ^ 64 -> 0 <= k2 < 2 ^ 64 ->
  cellA M 0x102e8 8 mC -> cellA M 0x10310 8 k1 -> cellA M 0x103d0 8 k2 -> wrA M (s - 224) 224 ->
  exists regs' h0,
    msteps ASEGS (mkst regs (0x80128 : word) M rom) (mkst regs' (0x801d8 : word) (dp_frame M s trp size raw regs) rom)
    /\ getr regs' 11 = Z_to_bv 64 trp /\ getr regs' 14 = Z_to_bv 64 (trp + 8 * size) /\ getr regs' 10 = Z_to_bv 64 mC /\ getr regs' 12 = Z_to_bv 64 h0
    /\ 0 <= h0 < 2 ^ 64 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 DEP /\ getr regs' 2 = Z_to_bv 64 (s - 112)
    /\ (forall r : reg, r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> ~ (10 <= U r <= 16) -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw s trp size mC k1 k2 H2 H10 H11 H1 Hs Hs' Ht Ht' Hsz HmC Hk1 Hk2 CmC Ck1 Ck2 W.
  destruct (zb_fresh (size * k1)) as [u1 [R1 E1]].
  destruct (zb_fresh (Z.lxor u1 k2)) as [h0 [R0 E0]].
  unfold dp_frame, DEP.
  eexists _, h0. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - zstep F_80128 D_80128.                                                       (* [comment removed for export] *)
    stepn F_8012c D_8012c.                                                       (* [comment removed for export] *)
    stepn F_80130 D_80130.                                                       (* [comment removed for export] *)
    zstep F_80134 D_80134.                                                       (* [comment removed for export] *)
    zstep F_80138 D_80138.                                                       (* [comment removed for export] *)
    zstep F_8013c D_8013c.                                                       (* [comment removed for export] *)
    zstep F_80140 D_80140.                                                       (* [comment removed for export] *)
    stepn F_80144 D_80144.                                                       (* [comment removed for export] *)
    zstep F_80148 D_80148.                                                       (* [comment removed for export] *)
    zsd F_8014c D_8014c (s - 8) (U raw) ltac:(rewok W).                             (* [comment removed for export] *)
    zsd F_80150 D_80150 (s - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_80154 D_80154 (s - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_80158 D_80158 (s - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_8015c D_8015c (s - 40) (U (getr regs 19)) ltac:(rewok W).
    zsd F_80160 D_80160 (s - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_80164 D_80164 (s - 56) (U (getr regs 21)) ltac:(rewok W).
    zsd F_80168 D_80168 (s - 64) (U (getr regs 22)) ltac:(rewok W).
    zsd F_8016c D_8016c (s - 72) (U (getr regs 23)) ltac:(rewok W).
    zsd F_80170 D_80170 (s - 80) (U (getr regs 24)) ltac:(rewok W).
    zsd F_80174 D_80174 (s - 88) (U (getr regs 25)) ltac:(rewok W).                (* [comment removed for export] *)
    zstep F_80178 D_80178.                                                       (* [comment removed for export] *)
    zstep F_8017c D_8017c.                                                       (* [comment removed for export] *)
    zsd F_80180 D_80180 (s - 104) trp ltac:(rewok W).                              (* [comment removed for export] *)
    zsd F_80184 D_80184 (s - 96) size ltac:(rewok W).                              (* [comment removed for export] *)
    zbtk F_80188 D_80188.                                                        (* [comment removed for export] *)
    stepn F_80190 D_80190. rwH. unfold v_addiw. rewrite art_u_lit by lia.
    replace (bv_swrap 32 (size + 0)) with size by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).   (* [comment removed for export] *)
    zstep F_80194 D_80194.                                                       (* [comment removed for export] *)
    zbft F_80198 D_80198.                                                        (* [comment removed for export] *)
    zbft F_8019c D_8019c.                                                        (* [comment removed for export] *)
    stepn F_801a0 D_801a0. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small size (2 ^ 32)) by lia.   (* [comment removed for export] *)
    stepn F_801a4 D_801a4.                                                       (* [comment removed for export] *)
    stepn F_801a8 D_801a8.                                                       (* [comment removed for export] *)
    stepn F_801ac D_801ac.                                                       (* [comment removed for export] *)
    stepn F_801b0 D_801b0.                                                       (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (C1 : cellA X 0x10310 8 k1) by zcell; assert (C2 : cellA X 0x103d0 8 k2) by zcell; assert (C0 : cellA X 0x102e8 8 mC) by zcell end.
    zld F_801b4 D_801b4 0x10310 C1.                                              (* [comment removed for export] *)
    stepn F_801b8 D_801b8. rwH.                                                  (* [comment removed for export] *)
    match goal with |- context [v_and (Z_to_bv 64 size) ?L] =>
      replace (v_and (Z_to_bv 64 size) L) with (Z_to_bv 64 size : word)
        by (symmetry; replace L with (Z_to_bv 64 (Z.ones 32) : word) by (apply bv_eq; vm_compute; reflexivity);
            rewrite art_zb_and by (change (Z.ones 32) with 4294967295; lia); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia) end.
    stepn F_801bc D_801bc.                                                       (* [comment removed for export] *)
    zld F_801c0 D_801c0 0x103d0 C2.                                              (* [comment removed for export] *)
    zld F_801c4 D_801c4 0x102e8 C0.                                              (* [comment removed for export] *)
    zstep F_801c8 D_801c8. rewrite E1.                                           (* [comment removed for export] *)
    zstep F_801cc D_801cc.                                                       (* [comment removed for export] *)
    stepn F_801d0 D_801d0. rwH. rewrite art_zb_xor by lia. rewrite E0.           (* [comment removed for export] *)
    zstep F_801d4 D_801d4.                                                       (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dp_mid_run : forall regs (M rom : word -> option byte) (hN mC N : Z),
  getr regs 12 = Z_to_bv 64 hN -> getr regs 13 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 mC -> getr regs 9 = Z_to_bv 64 DEP ->
  0 <= hN < 2 ^ 64 -> 0 <= mC < 2 ^ 64 -> 0 <= N < 2 ^ 16 ->
  (forall b, 0 <= b < 2 ^ 20 -> exists v, cellA M (DEP + 4 * b) 4 v /\ 0 <= v <= N) ->
  exists regs' h b v,
    msteps ASEGS (mkst regs (0x801fc : word) M rom) (mkst regs' (0x80268 : word) M rom)
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
  - stepn F_801fc D_801fc.                                                       (* [comment removed for export] *)
    stepn F_80200 D_80200.                                                       (* [comment removed for export] *)
    zstep F_80204 D_80204. rewrite E1.                                           (* [comment removed for export] *)
    stepn F_80208 D_80208.                                                       (* [comment removed for export] *)
    stepn F_8020c D_8020c.                                                       (* [comment removed for export] *)
    stepn F_80210 D_80210.                                                       (* [comment removed for export] *)
    stepn F_80214 D_80214. rwH. rewrite art_zb_srli by lia.                      (* [comment removed for export] *)
    stepn F_80218 D_80218. rwH. rewrite art_zb_xor by lia. rewrite E2.           (* [comment removed for export] *)
    zstep F_8021c D_8021c. rewrite E3.                                           (* [comment removed for export] *)
    stepn F_80220 D_80220. rwH. rewrite art_zb_xor by lia. rewrite E4.           (* [comment removed for export] *)
    zstep F_80224 D_80224. rewrite E5.                                           (* [comment removed for export] *)
    stepn F_80228 D_80228. rwH. rewrite art_zb_srli by lia.                      (* [comment removed for export] *)
    stepn F_8022c D_8022c. rwH. rewrite art_zb_xor by lia. rewrite E6.           (* [comment removed for export] *)
    zstep F_80230 D_80230. rewrite E7.                                           (* [comment removed for export] *)
    stepn F_80234 D_80234. rwH. rewrite art_zb_srli by lia.                      (* [comment removed for export] *)
    stepn F_80238 D_80238. rwH. rewrite art_zb_xor by lia. rewrite Eh.           (* [comment removed for export] *)
    zstep F_8023c D_8023c.                                                       (* [comment removed for export] *)
    replace (Z_to_bv 64 (h * 2 ^ 44) : word) with (Z_to_bv 64 (b * 2 ^ 44) : word)
      by (apply art_zb_eq; rewrite (mod_mul_pow44 h) by lia; subst b; rewrite Z.mod_small; [reflexivity | nia]).
    stepn F_80240 D_80240. rwH. rewrite (art_zb_srli_exact (b * 2 ^ 44) 42 (4 * b)) by lia.   (* [comment removed for export] *)
    zstep F_80244 D_80244.                                                       (* [comment removed for export] *)
    zlw F_80248 D_80248 (1836568 + 4 * b) Cv.                                    (* [comment removed for export] *)
    stepn F_8024c D_8024c.                                                       (* [comment removed for export] *)
    zstep F_80250 D_80250.                                                       (* [comment removed for export] *)
    stepfence F_80254 D_80254.
    stepn F_80258 D_80258. rwH.                                                  (* [comment removed for export] *)
    match goal with |- context [v_and (Z_to_bv 64 v) ?L] =>
      replace (v_and (Z_to_bv 64 v) L) with (Z_to_bv 64 v : word)
        by (symmetry; replace L with (Z_to_bv 64 (Z.ones 31) : word) by (apply bv_eq; vm_compute; reflexivity);
            rewrite art_zb_and by (change (Z.ones 31) with 2147483647; lia); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia) end.
    stepn F_8025c D_8025c.                                                       (* [comment removed for export] *)
    zstep F_80260 D_80260.                                                       (* [comment removed for export] *)
    zstep F_80264 D_80264.                                                       (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dp_epi_run : forall (regs0 regs : bvmap 5 word) (X rom : word -> option byte) (raw : word) (s : Z),
  getr regs 2 = Z_to_bv 64 (s - 112) -> ret_ok raw -> 4096 <= s - 112 -> s < 2 ^ 64 ->
  cellA X (s - 8) 8 (U raw) -> cellA X (s - 16) 8 (U (getr regs0 8)) -> cellA X (s - 24) 8 (U (getr regs0 9)) ->
  cellA X (s - 32) 8 (U (getr regs0 18)) -> cellA X (s - 40) 8 (U (getr regs0 19)) -> cellA X (s - 48) 8 (U (getr regs0 20)) ->
  cellA X (s - 56) 8 (U (getr regs0 21)) -> cellA X (s - 64) 8 (U (getr regs0 22)) -> cellA X (s - 72) 8 (U (getr regs0 23)) ->
  cellA X (s - 80) 8 (U (getr regs0 24)) -> cellA X (s - 88) 8 (U (getr regs0 25)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x8036c : word) X rom) (mkst regs' raw X rom)
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = raw
    /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18 /\ getr regs' 19 = getr regs0 19
    /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21 /\ getr regs' 22 = getr regs0 22 /\ getr regs' 23 = getr regs0 23
    /\ getr regs' 24 = getr regs0 24 /\ getr regs' 25 = getr regs0 25
    /\ (forall r : reg, r <> 1%bv -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> ~ (18 <= U r <= 25) -> getr regs' r = getr regs r).
Proof.
  intros regs0 regs X rom raw s H2 Hret Hs Hs' L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11.
  eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]].
  - zld F_8036c D_8036c (s - 8) L1. rewrite Z_to_bv_bv_unsigned.                 (* [comment removed for export] *)
    zld F_80370 D_80370 (s - 16) L2. rewrite Z_to_bv_bv_unsigned.
    zld F_80374 D_80374 (s - 24) L3. rewrite Z_to_bv_bv_unsigned.
    zld F_80378 D_80378 (s - 32) L4. rewrite Z_to_bv_bv_unsigned.
    zld F_8037c D_8037c (s - 40) L5. rewrite Z_to_bv_bv_unsigned.
    zld F_80380 D_80380 (s - 48) L6. rewrite Z_to_bv_bv_unsigned.
    zld F_80384 D_80384 (s - 56) L7. rewrite Z_to_bv_bv_unsigned.
    zld F_80388 D_80388 (s - 64) L8. rewrite Z_to_bv_bv_unsigned.
    zld F_8038c D_8038c (s - 72) L9. rewrite Z_to_bv_bv_unsigned.
    zld F_80390 D_80390 (s - 80) L10. rewrite Z_to_bv_bv_unsigned.
    zld F_80394 D_80394 (s - 88) L11. rewrite Z_to_bv_bv_unsigned.                (* [comment removed for export] *)
    zstep F_80398 D_80398.                                                       (* [comment removed for export] *)
    stepret F_8039c D_8039c raw ltac:(rwH; reflexivity).
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
