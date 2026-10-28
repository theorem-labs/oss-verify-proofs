(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_unwind_chain RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxLearn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nf_regs (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  den rho (rget S X1) x1 /\ den rho (rget S X2) x2 /\ den rho (rget S X4) x4 /\ den rho (rget S X8) x8 /\ den rho (rget S X10) x10
  /\ den rho (rget S X11) x11 /\ den rho (rget S X12) x12.
Proof.
  intros H. repeat split.
  - exact (H (Z_to_bv 5 1)). - exact (H (Z_to_bv 5 2)). - exact (H (Z_to_bv 5 4)). - exact (H (Z_to_bv 5 8)). - exact (H (Z_to_bv 5 10)).
  - exact (H (Z_to_bv 5 11)). - exact (H (Z_to_bv 5 12)).
Qed.

Lemma ret_pc_wbv (ra : w64) : ret_pc (wbv ra) = wbv (w_and ra w_notone).
Proof. rewrite wbv_and, wbv_notone. reflexivity. Qed.

Lemma R_return (rho : valuation) (S : sstate) (res : hval) (M' : HxMem.mem) (abs : abstab) (nx : int) (ra : w64)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (F F' : bvmap 5 word) (pc : word) (fc fc' : bv 32) (rv : option word) (m' ro : word -> option byte) :
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = wbv ra -> den rho res a0' -> Rmem ctasegs rho M' m' ->
  R ctasegs rho (SS (w_and ra w_notone) (rf_set (havoc_caller_saved (s_regs S)) X10 res) RNone M' abs nx)
    (MS (mkR x1 x2 x3 x4 t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
        F' (ret_pc x1) fc' None m' ro).
Proof.
  intros HRg E1 Hd HRm. unfold R. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS s_pc s_regs s_resv s_mem].
  split; [reflexivity|]. split; [rewrite E1; apply ret_pc_wbv|]. split.
  { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS]. eapply (Rregs_return rho (s_regs S) res); [exact HRg | exact Hd]. }
  split; [reflexivity | exact HRm].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma region_ok_ro (rho : valuation) (t : int) (rg : region) (m m' : word -> option byte) :
  region_ok ctasegs rho t rg m -> rg_wr rg = false ->
  (forall i, 0 <= i < to_Z (rg_size rg) -> mrd ctasegs m' (wa (rbase rho t rg + i)) = mrd ctasegs m (wa (rbase rho t rg + i))) ->
  region_ok ctasegs rho t rg m'.
Proof.
  intros Hok Hw Hk. pose proof Hok as (_ & _ & _ & _ & _ & _ & _ & Hb).
  apply (region_ok_upd ctasegs rho t rg rg m m' Hok); [repeat split|].
  intros i Hi. destruct (Hb i Hi) as (b & Eb & Kb & _). exists b. split; [rewrite (Hk i Hi); exact Eb|]. split; [exact Kb|]. rewrite Hw. discriminate.
Qed.

(* [comment removed for export] *)
Lemma same_byte_kept (m m' : word -> option byte) (a : word) : m' a = m a ->
  mrd ctasegs m' a = mrd ctasegs m a /\ (wview ctasegs m a <> None -> wview ctasegs m' a <> None).
Proof. intros E. unfold mrd, wview. rewrite E. split; [reflexivity | auto]. Qed.

(* [comment removed for export] *)
Lemma Rmem_after (rho : valuation) (M : HxMem.mem) (t : int) (rg rg' : region) (m m' : word -> option byte) :
  Rmem ctasegs rho M m -> mget M t = Some rg -> same_dir rg rg' -> region_ok ctasegs rho t rg' m' ->
  (forall t2 rg2, mget M t2 = Some rg2 -> t2 <> t -> region_ok ctasegs rho t2 rg2 m') ->
  Rmem ctasegs rho (mset M t rg') m'.
Proof.
  intros [HR Hsep] Eg Hd Hok Hk. split.
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg' rg2 (mget_lt M t rg Eg) G) as [[-> ->]|[Hne G2]]; [exact Hok | exact (Hk t2 rg2 G2 Hne)].
  - exact (regions_sep_mset_same rho M t rg rg' Eg Hd Hsep).
Qed.

(* [comment removed for export] *)
Lemma bytes_at_mrd (m : word -> option byte) (A : Z) (bs : list byte) (i : Z) :
  bytes_at ctasegs m A bs -> 0 <= i < Z.of_nat (length bs) -> mrd ctasegs m (wa (A + i)) = nth_error bs (Z.to_nat i).
Proof. intros (_ & _ & H) Hi. specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. exact H. Qed.

Lemma bytes_at_same (m m' : word -> option byte) (A : Z) (bs : list byte) (i : Z) :
  bytes_at ctasegs m A bs -> bytes_at ctasegs m' A bs -> 0 <= i < Z.of_nat (length bs) ->
  mrd ctasegs m' (wa (A + i)) = mrd ctasegs m (wa (A + i)).
Proof. intros H H' Hi. rewrite (bytes_at_mrd m A bs i H Hi), (bytes_at_mrd m' A bs i H' Hi). reflexivity. Qed.

(* [comment removed for export] *)
Lemma acc_granule_zero (m : word -> option byte) (a : Z) : a mod 8 = 0 -> acc ctasegs m a 8 ->
  mrd ctasegs m (wa (shad a)) = Some (Z_to_bv 8 0).
Proof.
  intros Ha Hacc. destruct (Hacc 7 ltac:(lia)) as (b & Hb & Hs).
  assert (Esh : shad (a + 7) = shad a).
  { unfold shad. f_equal. symmetry. apply Z.div_unique with (r := 7 + 0); [lia|]. pose proof (Z.div_mod a 8 ltac:(lia)). lia. }
  rewrite Esh in Hb. pose proof (bytes_at_mrd m (shad a) [b] 0 Hb ltac:(cbn; lia)) as E. rewrite Z.add_0_r in E.
  change (nth_error [b] (Z.to_nat 0)) with (Some b) in E. rewrite E. f_equal.
  assert (Em : (a + 7) mod 8 = 7) by (rewrite Z.add_mod, Ha by lia; reflexivity).
  unfold sh_ok in Hs. rewrite Em in Hs. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fresh_region_ok (rho : valuation) (t n al : int) (wr : bool) (m : word -> option byte) (A : Z) :
  rho t = A -> 0 < A -> A + to_Z n < two63 -> to_Z n < 2 ^ 62 -> to_Z al < 63 -> A mod 2 ^ to_Z al = 0 ->
  wr_at ctasegs m A (to_Z n) ->
  region_ok ctasegs rho t (RG None n al wr DUnk (depth_for 60 n 0) IEmpty) m.
Proof.
  intros Er Hpos Hhi H62 Hal Hmod (_ & _ & Hw). destruct (depth_for_ok n H62) as [Hd1 Hd2].
  apply (region_ok_fresh ctasegs rho t None n al wr (depth_for 60 n 0) m); unfold rbase; cbn [rg_abs]; rewrite ?Er; try assumption.
  intros i Hi. split; [exact (wview_mrd ctasegs m _ asegs_wr_rd (Hw i Hi)) | intros _; exact (Hw i Hi)].
Qed.

Lemma byteZ_0 (j : Z) : byteZ 0 j = 0.
Proof. unfold byteZ. rewrite Zdiv_0_l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zero_region_ok (rho : valuation) (t n : int) (m : word -> option byte) (A : Z) :
  rho t = A -> 0 <= A -> A + to_Z n < two63 -> to_Z n < 2 ^ 62 ->
  bytes_at ctasegs m A (repeat z8 (Z.to_nat (to_Z n))) ->
  region_ok ctasegs rho t (shadow_region n false DZero) m.
Proof.
  intros Er Hpos Hhi H62 Hb. destruct (depth_for_ok n H62) as [Hd1 Hd2]. pose proof (to_Z_bounded n) as Bn.
  unfold shadow_region, region_ok, rbase. cbn [rg_abs rg_size rg_al rg_wr rg_d]. rewrite Er. change (to_Z 0%uint63) with 0.
  split; [split; [exact Hpos | right; reflexivity]|]. split; [exact Hhi|]. split; [exact H62|]. split; [exact Hd1|]. split; [exact Hd2|].
  split; [lia|]. split; [apply Z.mod_1_r|].
  intros i Hi. exists z8. split.
  - rewrite (bytes_at_mrd m A _ i Hb) by (rewrite repeat_length; lia). apply nth_error_repeat. lia.
  - split; [|discriminate]. unfold rg_kb, rd_cell. cbn [rg_d rg_cells rg_dflt]. rewrite iget_empty. cbn [dflt_cell cell_kb].
    change (to_Z 255%uint63) with 255. rewrite testbit_255 by (apply Z.mod_pos_bound; lia). cbn [kb_ok].
    change (wZ w_zero) with 0. rewrite byteZ_0. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ushadow_region_shape (n : int) : 0 < to_Z n <= 64512 ->
  rg_abs (ushadow_region n) = None /\ rg_wr (ushadow_region n) = false /\ rg_al (ushadow_region n) = 0%uint63
  /\ to_Z (rg_size (ushadow_region n)) = shsz (to_Z n) /\ rg_d (ushadow_region n) = depth_for 60 (rg_size (ushadow_region n)) 0
  /\ rg_dflt (ushadow_region n) = DZero.
Proof.
  intros Hn.
  assert (Esz : to_Z ((n + 7) >> 3)%uint63 = shsz (to_Z n)).
  { rewrite phi_shr3, add_spec. change (to_Z 7%uint63) with 7. rewrite Z.mod_small by (rewrite wB_eq; unfold two63; lia). reflexivity. }
  unfold ushadow_region. destruct (n land 7 =? 0)%uint63; cbn [rg_abs rg_wr rg_al rg_size rg_d rg_dflt]; repeat split; assumption.
Qed.

Lemma ushadow_region_ok (rho : valuation) (t n : int) (m : word -> option byte) (A : Z) :
  rho t = A -> 0 <= A -> A + shsz (to_Z n) < two63 -> 0 < to_Z n <= 64512 ->
  bytes_at ctasegs m A (ushadow (to_Z n)) ->
  region_ok ctasegs rho t (ushadow_region n) m.
Proof.
  intros Er Hpos Hhi Hn Hb.
  destruct (ushadow_region_shape n Hn) as (Ea & Ew & Eal & Esz & Ed & Edf).
  pose proof (shsz_bounds (to_Z n) ltac:(lia)) as Bs.
  assert (H62 : to_Z (rg_size (ushadow_region n)) < 2 ^ 62) by lia.
  destruct (depth_for_ok _ H62) as [Hd1 Hd2]. rewrite <- Ed in Hd1, Hd2.
  pose proof (ushadow_length (to_Z n) ltac:(lia)) as Hlen.
  unfold region_ok, rbase. rewrite Ea, Er, Eal, Esz, Ew. change (to_Z 0%uint63) with 0.
  split; [split; [exact Hpos | right; reflexivity]|]. split; [exact Hhi|]. split; [lia|]. split; [rewrite <- Esz; exact Hd1|]. split; [exact Hd2|].
  split; [lia|]. split; [apply Z.mod_1_r|].
  intros i Hi.
  assert (Hnth : exists b, nth_error (ushadow (to_Z n)) (Z.to_nat i) = Some b
            /\ bv_unsigned b = (if i <? to_Z n / 8 then 0 else to_Z n mod 8)).
  { unfold ushadow. destruct (Z.ltb_spec i (to_Z n / 8)) as [L|L].
    - exists z8. split; [|reflexivity]. rewrite nth_error_app1 by (rewrite repeat_length; lia). apply nth_error_repeat. lia.
    - rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length.
      destruct (Z.eqb_spec (to_Z n mod 8) 0) as [E|E]; [exfalso; unfold shsz in Hi; Z.div_mod_to_equations; lia|].
      replace (Z.to_nat i - Z.to_nat (to_Z n / 8))%nat with 0%nat by (unfold shsz in Hi; Z.div_mod_to_equations; lia).
      cbn [nth_error]. eexists. split; [reflexivity|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      rewrite Z.mod_small by (Z.div_mod_to_equations; lia). destruct (Z.ltb_spec i (to_Z n / 8)); [lia | reflexivity]. }
  destruct Hnth as (b & Hnb & Hbv). exists b.
  split; [rewrite (bytes_at_mrd m A _ i Hb) by lia; exact Hnb|]. split; [|discriminate].
  (* [comment removed for export] *)
  unfold rg_kb, rd_cell. rewrite Edf. unfold ushadow_region in *.
  destruct (eqbP (n land 7) 0%uint63) as [E7|E7]; cbn [rg_d rg_cells rg_dflt rg_size] in *.
  - (* [comment removed for export] *)
    rewrite iget_empty. cbn [dflt_cell cell_kb]. change (to_Z 255%uint63) with 255. rewrite testbit_255 by (apply Z.mod_pos_bound; lia).
    cbn [kb_ok]. change (wZ w_zero) with 0. rewrite byteZ_0, Hbv.
    assert (E8 : to_Z n mod 8 = 0) by (rewrite <- phi_land7; exact E7).
    destruct (Z.ltb_spec i (to_Z n / 8)); [reflexivity|]. exfalso. unfold shsz in Hi. Z.div_mod_to_equations. lia.
  - assert (E8 : to_Z n mod 8 <> 0) by (rewrite <- phi_land7; intros X; apply E7; rewrite X; reflexivity).
    set (q := (n >> 3)%uint63) in *.
    assert (Eq : to_Z q = to_Z n / 8) by (unfold q; apply phi_shr3).
    assert (Eq3 : to_Z (q >> 3)%uint63 = to_Z n / 8 / 8) by (rewrite phi_shr3, Eq; reflexivity).
    assert (Eq7 : to_Z (q land 7)%uint63 = (to_Z n / 8) mod 8) by (rewrite phi_land7, Eq; reflexivity).
    rewrite iget_iset, iget_empty.
    assert (Hiq : i <= to_Z n / 8 /\ to_Z n / 8 < shsz (to_Z n)) by (unfold shsz in *; Z.div_mod_to_equations; lia).
    set (d := depth_for 60 ((n + 7) >> 3)%uint63 0) in *.
    assert (Hk : to_Z n / 8 / 8 < 2 ^ Z.of_nat d) by (Z.div_mod_to_equations; nia).
    rewrite of_Z_spec, Eq3, (Z.mod_small (i / 8)) by (rewrite wB_eq; unfold two63; Z.div_mod_to_equations; lia).
    rewrite (Z.mod_small (to_Z n / 8 / 8)) by (split; [Z.div_mod_to_equations; lia | exact Hk]).
    rewrite (Z.mod_small (i / 8)) by (split; [Z.div_mod_to_equations; lia | apply (Z.le_lt_trans _ (to_Z n / 8 / 8)); [Z.div_mod_to_equations; lia | exact Hk]]).
    destruct (Z.eqb_spec (to_Z n / 8 / 8) (i / 8)) as [Ec|Ec].
    + (* [comment removed for export] *)
      cbn [cell_kb]. rewrite sub_spec, lsl_spec, add_spec, Eq7. change (to_Z 1%uint63) with 1.
      assert (Hm8 : 0 <= to_Z n / 8 mod 8 < 8) by (apply Z.mod_pos_bound; lia).
      assert (Hp : 2 ^ (to_Z n / 8 mod 8 + 1) <= 2 ^ 8) by (apply Z.pow_le_mono_r; lia).
      rewrite (Z.mod_small (to_Z n / 8 mod 8 + 1)) by (rewrite wB_eq; unfold two63; lia).
      rewrite (Z.mod_small (1 * 2 ^ (to_Z n / 8 mod 8 + 1))) by (rewrite wB_eq; unfold two63; lia).
      rewrite (Z.mod_small) by (rewrite wB_eq; unfold two63; split; [lia|]; apply (Z.le_lt_trans _ (2 ^ 8)); lia).
      rewrite Z.mul_1_l. replace (2 ^ (to_Z n / 8 mod 8 + 1) - 1) with (Z.ones (to_Z n / 8 mod 8 + 1)) by (rewrite Z.ones_equiv; lia).
      rewrite Z.testbit_ones by lia.
      assert (Him : 0 <= i mod 8 <= to_Z n / 8 mod 8) by (Z.div_mod_to_equations; nia).
      replace ((0 <=? i mod 8) && (i mod 8 <? to_Z n / 8 mod 8 + 1)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). cbn [kb_ok].
      rewrite Hbv. unfold wZ. cbn [wh wl]. rewrite Z.add_0_l, lsl_spec, mul_spec, phi_land7, Eq7. change (to_Z 8%uint63) with 8.
      assert (Hsm : 0 <= to_Z n mod 8 * 2 ^ (8 * (to_Z n / 8 mod 8)) < 2 ^ 62).
      { split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]|].
        apply (Z.lt_le_trans _ (8 * 2 ^ (8 * 7))); [|cbn; lia]. pose proof (Z.pow_le_mono_r 2 (8 * (to_Z n / 8 mod 8)) (8 * 7) ltac:(lia) ltac:(lia)).
        pose proof (Z.mod_pos_bound (to_Z n) 8 ltac:(lia)). nia. }
      rewrite (Z.mod_small (8 * _) wB) by (rewrite wB_eq; unfold two63; lia).
      rewrite (Z.mod_small (_ * _) wB) by (rewrite wB_eq; unfold two63; lia).
      unfold byteZ. symmetry.
      destruct (Z.ltb_spec i (to_Z n / 8)) as [L|L].
      * (* [comment removed for export] *)
        assert (Hlt : i mod 8 < to_Z n / 8 mod 8) by (Z.div_mod_to_equations; nia).
        replace (8 * (to_Z n / 8 mod 8)) with (8 * (i mod 8) + 8 * (to_Z n / 8 mod 8 - i mod 8)) by lia.
        rewrite Z.pow_add_r by lia. rewrite Z.mul_assoc, (Z.mul_comm (to_Z n mod 8)), <- Z.mul_assoc, (Z.mul_comm (2 ^ (8 * (i mod 8)))), Z.div_mul by (apply Z.pow_nonzero; lia).
        replace (8 * (to_Z n / 8 mod 8 - i mod 8)) with (8 + 8 * (to_Z n / 8 mod 8 - i mod 8 - 1)) by lia.
        rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
        rewrite (Z.mul_comm 256), Z.mul_assoc, Z.mod_mul by lia. reflexivity.
      * assert (Ei : i = to_Z n / 8) by lia. subst i.
        rewrite Z.div_mul by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by (Z.div_mod_to_equations; lia). reflexivity.
    + (* [comment removed for export] *)
      cbn [dflt_cell cell_kb]. change (to_Z 255%uint63) with 255. rewrite testbit_255 by (apply Z.mod_pos_bound; lia).
      cbn [kb_ok]. change (wZ w_zero) with 0. rewrite byteZ_0, Hbv.
      destruct (Z.ltb_spec i (to_Z n / 8)); [reflexivity|]. exfalso. apply Ec. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ro_kept (m m' : word -> option byte) (a : Z) :
  mem_inv ctasegs m -> mem_inv ctasegs m' -> 65536 <= a < 1679360 -> mrd ctasegs m' (wa a) = mrd ctasegs m (wa a).
Proof. intros MI MI' Ha. unfold mrd. rewrite (ro_none m a MI Ha), (ro_none m' a MI' Ha). reflexivity. Qed.

Lemma cells_at_same (m m' : word -> option byte) (A : Z) (cs : list Cells.cell) (i : Z) :
  cells_at ctasegs m A cs -> cells_at ctasegs m' A cs -> 0 <= i < Z.of_nat (cells_size cs) ->
  mrd ctasegs m' (wa (A + i)) = mrd ctasegs m (wa (A + i)).
Proof.
  intros [Hwf Hb] [_ Hb'] Hi. apply (bytes_at_same m m' A (cells_bytes cs) i Hb Hb'). rewrite (cells_bytes_length cs Hwf). exact Hi.
Qed.

Lemma sh_tag_Z (t : int) : to_Z t < 1000000 -> to_Z (sh_tag t) = to_Z t + 1.
Proof.
  intros Ht. unfold sh_tag. rewrite add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. pose proof (to_Z_bounded t). rewrite wB_eq. unfold two63. lia.
Qed.

Lemma sh_tag_inj (t t' : int) : to_Z t < 1000000 -> to_Z t' < 1000000 -> sh_tag t = sh_tag t' -> t = t'.
Proof. intros H H' E. apply to_Z_inj. pose proof (f_equal to_Z E) as E'. rewrite (sh_tag_Z t H), (sh_tag_Z t' H') in E'. lia. Qed.

(* [comment removed for export] *)
Lemma live_remove_cons (p p' n' : Z) (l : list (Z * Z)) :
  live_remove p ((p', n') :: l) = if (p' =? p) then live_remove p l else (p', n') :: live_remove p l.
Proof. unfold live_remove. cbn. destruct (p' =? p); cbn; reflexivity. Qed.

Lemma live_remove_keep (p : Z) (l : list (Z * Z)) : (forall p' n', In (p', n') l -> p' <> p) -> live_remove p l = l.
Proof.
  induction l as [|[p' n'] l IH]; intros H; [reflexivity|]. rewrite live_remove_cons.
  destruct (Z.eqb_spec p' p) as [E|E]; [exfalso; exact (H p' n' (or_introl eq_refl) E)|]. f_equal. apply IH.
  intros p2 n2 Hin. apply (H p2 n2). right. exact Hin.
Qed.

Lemma live_remove_blk (f : int -> Z * Z) (t : int) (p : Z) (CL : list (Z * Z)) : forall bl : list int,
  List.NoDup bl -> In t bl -> fst (f t) = p -> (forall b, In b bl -> b <> t -> fst (f b) <> p) -> (forall p' n', In (p', n') CL -> p' <> p) ->
  live_remove p (map f bl ++ CL) = map f (remove_tag t bl) ++ CL.
Proof.
  induction bl as [|b bl IH]; intros Hnd Hin Ep Hne HCL; [destruct Hin|].
  apply List.NoDup_cons_iff in Hnd as [Hni Hnd]. cbn [map app remove_tag].
  destruct (f b) as [pb nb] eqn:Efb. rewrite live_remove_cons.
  destruct (eqbP b t) as [E|E].
  - apply to_Z_inj in E. subst b. rewrite Efb in Ep. cbn [fst] in Ep. subst pb. rewrite Z.eqb_refl.
    apply live_remove_keep. intros p' n' Hin'. apply in_app_or in Hin' as [Hin'|Hin']; [|exact (HCL p' n' Hin')].
    apply in_map_iff in Hin' as (b' & Eb' & Hb'). intros Epp.
    apply (Hne b' (or_intror Hb')); [intros ->; exact (Hni Hb') | rewrite Eb'; exact Epp].
  - assert (Nbt : b <> t) by (intros ->; apply E; reflexivity).
    pose proof (Hne b (or_introl eq_refl) Nbt) as Ef. rewrite Efb in Ef. cbn [fst] in Ef.
    destruct (Z.eqb_spec pb p) as [Ef'|Ef']; [contradiction|]. cbn [map app]. rewrite Efb. f_equal.
    apply IH; [exact Hnd | destruct Hin as [->|Hin]; [contradiction | exact Hin] | exact Ep | | exact HCL].
    intros b' Hb' Nb'. apply (Hne b' (or_intror Hb') Nb').
Qed.

Lemma remove_tag_In (t x : int) (l : list int) : In x (remove_tag t l) -> In x l.
Proof.
  induction l as [|b l IH]; cbn [remove_tag]; [auto|]. destruct (eqbP b t) as [E|E]; [intros H; right; exact H|].
  intros [->|H]; [left; reflexivity | right; exact (IH H)].
Qed.

Lemma remove_tag_other (t x : int) (l : list int) : In x l -> x <> t -> In x (remove_tag t l).
Proof.
  induction l as [|b l IH]; cbn [remove_tag]; [auto|]. intros [->|H] Hne.
  - destruct (eqbP x t) as [E|E]; [apply to_Z_inj in E; contradiction | left; reflexivity].
  - destruct (eqbP b t) as [E|E]; [exact H | right; exact (IH H Hne)].
Qed.

Lemma remove_tag_NoDup (t : int) (l : list int) : List.NoDup l -> List.NoDup (remove_tag t l) /\ ~ In t (remove_tag t l).
Proof.
  induction l as [|b l IH]; intros Hnd; cbn [remove_tag]; [split; [constructor | intros []]|].
  apply List.NoDup_cons_iff in Hnd as [Hni Hnd]. destruct (eqbP b t) as [E|E].
  - apply to_Z_inj in E. subst b. split; assumption.
  - destruct (IH Hnd) as [I1 I2]. split.
    + constructor; [intros H; exact (Hni (remove_tag_In t b l H)) | exact I1].
    + intros [->|H]; [apply E; reflexivity | exact (I2 H)].
Qed.

Lemma remove_tag_length (t : int) (l : list int) : In t l -> Datatypes.S (length (remove_tag t l)) = length l.
Proof.
  induction l as [|b l IH]; intros Hin; [destruct Hin|]. cbn [remove_tag length]. destruct (eqbP b t) as [E|E]; [reflexivity|].
  cbn [length]. f_equal. apply IH. destruct Hin as [->|Hin]; [exfalso; apply E; reflexivity | exact Hin].
Qed.

Lemma even_up_spec (t0 : int) : to_Z t0 < 1000000 ->
  tag_even (even_up t0) = true /\ to_Z t0 <= to_Z (even_up t0) <= to_Z t0 + 1.
Proof.
  intros Ht. unfold even_up. destruct (tag_even t0) eqn:E; [split; [exact E | lia]|].
  pose proof (tag_even_false_spec t0 E) as Hm. pose proof (to_Z_bounded t0) as Bt.
  assert (E1 : to_Z (t0 + 1)%uint63 = to_Z t0 + 1) by (rewrite add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
  split; [|lia]. unfold tag_even. apply Uint63.eqb_spec. apply to_Z_inj. rewrite land_spec'. change (to_Z 1%uint63) with (Z.ones 1).
  rewrite Z.land_ones by lia. rewrite E1. change (2 ^ 1) with 2. change (to_Z 0%uint63) with 0.
  rewrite Z.add_mod, Hm by lia. reflexivity.
Qed.

Lemma add2_Z (t : int) : to_Z t < 1000000 -> to_Z (t + 2)%uint63 = to_Z t + 2.
Proof. intros Ht. rewrite add_spec. change (to_Z 2%uint63) with 2. apply Z.mod_small. pose proof (to_Z_bounded t). rewrite wB_eq. unfold two63. lia. Qed.

Section Hooks.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis PMc_fdfs : fdfs_only PMc.
Hypothesis PMc_mat : mat_stable PMc.
Variable T : TSet.
Variables (CL : list (Z * Z)) (lo sp0 r : Z) (m0 : word -> option byte) (cr0 anc : Z) (xp : xpar).
Hypothesis H_r : r = 0 \/ r = 16.

(* [comment removed for export] *)
Hypothesis XP_ro : rg_wr (xp_rgsh xp) = false.
Hypothesis XP_stk : stk_okx (xp_stk xp).
Hypothesis IMGSH_OK : forall Σ m rho t, ART RT Σ m -> region_ok ctasegs rho t (xp_rgsh xp) m.

Notation FMemA := (FMem RT CL lo sp0 r m0 cr0 anc xp).
Notation FInvA := (FInv RT CL lo sp0 r m0 cr0 anc xp).
Notation JA := (J RT PMc T).
Notation B0A := (B0 sp0 r xp).

Lemma B0_mod8 : sp0 mod 32 = r -> B0A mod 8 = 0.
Proof.
  intros H. unfold B0. destruct XP_stk as (E & _). pose proof (Z.div_mod (xp_stk xp) 32 ltac:(lia)) as D2. rewrite E in D2.
  pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite H in D.
  replace (sp0 - r - xp_stk xp) with (0 + (4 * (sp0 / 32) - 4 * (xp_stk xp / 32)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_after_rt (g : ghost RT) (rho rho2 : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (Σ' : rts RT) (L : list (Z * Z)) (spc : Z) (tx : int) (d n : Z) :
  FMemA g rho cd M nx m -> Rmem ctasegs rho2 M m -> agree_below nx rho rho2 ->
  ART RT Σ' m' -> mem_inv ctasegs m' -> rt_pres_ex L (rt_frames RT (g_S RT g)) spc d n m m' -> rt_sp0 RT Σ' = rt_sp0 RT (g_S RT g) ->
  (forall b, In b (x_blocks cd) -> b <> tx -> In (rho b, rsize M b) L /\ In (rho b, rsize M b) (rt_live RT Σ')) ->
  (forall e, In e CL -> In e L /\ In e (rt_live RT Σ')) ->
  forall t3 rg3, mget M t3 = Some rg3 -> t3 <> T_STK -> t3 <> tx -> t3 <> sh_tag tx -> to_Z tx < 1000000 ->
    (forall i, 0 <= i < to_Z (rg_size rg3) -> ~ (d <= rbase rho2 t3 rg3 + i < d + n)) ->
    region_ok ctasegs rho2 t3 rg3 m'.
Proof.
  intros HF [HRg Hsep] Hag HART' MI' Hpres Esp0 HL HLc t3 rg3 Eg3 Hn1 Hntx Hnstx Htx Hdn.
  pose proof HF as HF0.
  destruct HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & Hcnt & Hagr & Hsp0a & Hcb).
  pose proof (HRg t3 rg3 Eg3) as Hok. pose proof Hok as (Bx0 & Bx1 & _). unfold two63 in Bx1.
  assert (KEPT : (forall i, 0 <= i < to_Z (rg_size rg3) -> m' (wa (rbase rho2 t3 rg3 + i)) = m (wa (rbase rho2 t3 rg3 + i))) -> region_ok ctasegs rho2 t3 rg3 m').
  { intros Hk. apply (region_ok_frame ctasegs rho2 t3 rg3 m m' Hok). intros i Hi. apply same_byte_kept. exact (Hk i Hi). }
  assert (PRES : forall i, 0 <= i < to_Z (rg_size rg3) -> 0 <= rbase rho2 t3 rg3 + i < 2 ^ 64 ->
            aclient L (rt_frames RT (g_S RT g)) spc (rbase rho2 t3 rg3 + i) -> m' (wa (rbase rho2 t3 rg3 + i)) = m (wa (rbase rho2 t3 rg3 + i))).
  { intros i Hi Ha Hc. apply Hpres; rewrite wa_unsigned by lia; [exact Hc | exact (Hdn i Hi)]. }
  pose proof (Hcls t3 rg3 Eg3) as C. unfold rbase in *. destruct (rg_abs rg3) as [a0|] eqn:Ea.
  - destruct C as [(C1 & C2 & _)|[(w0 & C & Cw0) [Cimg _]]].
    { apply KEPT. intros i Hi. lia. }
    assert (Kro : w0 = false -> rg_wr rg3 = false) by (intros ->; destruct (rg_wr rg3); [discriminate (Cw0 eq_refl) | reflexivity]).
    destruct (static_facts _ _ _ C) as (S1 & S2 & S3 & _ & _ & S6).
    destruct S6 as [(K1 & K2 & K3)|[(K1 & K2 & K3)|[K|[(K1 & K2 & K3)|[(K1 & K2 & K3)|(K1 & K2 & K3)]]]]].
    + (* [comment removed for export] *) apply (region_ok_ro rho2 t3 rg3 m m' Hok (Kro K3)). unfold rbase. rewrite Ea. intros i Hi. apply ro_kept; [exact Hmi | exact MI' | lia].
    + (* [comment removed for export] *) apply (region_ok_ro rho2 t3 rg3 m m' Hok (Kro K3)). unfold rbase. rewrite Ea. intros i Hi.
      destruct (af_client_consts RT AF _ _ HART) as (_ & _ & _ & _ & Hrp). destruct (af_client_consts RT AF _ _ HART') as (_ & _ & _ & _ & Hrp').
      unfold RELRO_LO, RELRO_HI in *. rewrite (Hrp (wa (to_Z a0 + i))), (Hrp' (wa (to_Z a0 + i))) by (rewrite wa_unsigned by lia; unfold RELRO_LO, RELRO_HI; lia). reflexivity.
    + (* [comment removed for export] *) apply KEPT. intros i Hi. apply (PRES i Hi); [lia|]. right. left. apply K. lia.
    + (* [comment removed for export] *) apply (region_ok_ro rho2 t3 rg3 m m' Hok (Kro K3)). unfold rbase. rewrite Ea. intros i Hi. rewrite K1 in *.
      destruct (af_client_consts RT AF _ _ HART) as (_ & Q2 & _ & Q4 & _). destruct (af_client_consts RT AF _ _ HART') as (_ & Q2' & _ & Q4' & _).
      unfold g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
      destruct (Z_lt_le_dec i 8) as [L8|L8].
      * exact (cells_at_same m m' _ _ i Q2 Q2' ltac:(cbn; lia)).
      * replace (6758456 + i) with (6758464 + (i - 8)) by lia. exact (cells_at_same m m' _ _ (i - 8) Q4 Q4' ltac:(cbn; lia)).
    + (* [comment removed for export] *) apply (region_ok_ro rho2 t3 rg3 m m' Hok (Kro K3)). unfold rbase. rewrite Ea. intros i Hi. rewrite K1 in *.
      exact (cells_at_same m m' _ _ i (proj1 (af_tsd RT AF _ _ HART)) (proj1 (af_tsd RT AF _ _ HART')) ltac:(cbn; lia)).
    + (* [comment removed for export] *) rewrite (Cimg K1). apply (IMGSH_OK Σ' m' rho2 t3 HART').
  - destruct C as [(C1 & _)|[(-> & Es & Ew)|[(Hin & Ew)|[(b & Hin & -> & Es & Ew)|[(Hin & Es & Ew)|[(f & Hin & -> & Es & Ew)|[(nc & wc & Hin & Es & Cw)|(b & nc & wc & Hin & -> & Es & Ew)]]]]]]]; [contradiction | | | | | | |].
    + (* [comment removed for export] *)
      apply (region_ok_ro rho2 _ rg3 m m' Hok Ew). unfold rbase. rewrite Ea. intros i Hi.
      assert (E2 : rho2 (sh_tag T_STK) = shad B0A) by (rewrite (Hag (sh_tag T_STK)) by (change (to_Z (sh_tag T_STK)) with 3; change (to_Z NEXT0) with 32 in Hnx0; lia); exact Hrss).
      rewrite E2. pose proof (B0_mod8 Hl4) as Hm8. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1).
      assert (Hi8 : 8 * i + 8 <= xp_stk xp + r).
      { rewrite Es in Hi. pose proof (Z.div_mod (xp_stk xp + r) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (xp_stk xp + r) 8 ltac:(lia)). lia. }
      rewrite <- (shad_add8 B0A i).
      assert (Hacc : forall Σx mx, ART RT Σx mx -> rt_sp0 RT Σx = rt_sp0 RT (g_S RT g) -> mrd ctasegs mx (wa (shad (B0A + 8 * i))) = Some (Z_to_bv 8 0)).
      { intros Σx mx Hx Ex. apply acc_granule_zero; [rewrite Z.add_mod, Hm8, Z.mul_comm, Z.mod_mul by lia; reflexivity|].
        apply (af_acc_stack RT AF Σx mx _ _ Hx); [rewrite Ex; unfold B0 in *; lia | unfold B0, USTACK_TOP in *; lia]. }
      rewrite (Hacc _ _ HART eq_refl), (Hacc _ _ HART' Esp0). reflexivity.
    + (* [comment removed for export] *)
      apply KEPT. intros i Hi. assert (E2 : rho2 t3 = rho t3) by (apply Hag; exact (Htags t3 rg3 Eg3)).
      destruct (HL t3 Hin Hntx) as [HinL _]. rewrite (rsize_get M t3 rg3 Eg3) in HinL.
      destruct (wr_facts RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd M nx m t3 rg3 (rho t3 + i)) as (_ & _ & Hr47);
        [unfold FMem; cbv zeta; tauto | exact Eg3 | exact Ew | unfold rbase; rewrite Ea; lia |].
      apply (PRES i Hi); rewrite E2; [lia|]. right; right; left. exists (rho t3), (to_Z (rg_size rg3)). split; [exact HinL | lia].
    + (* [comment removed for export] *)
      apply (region_ok_ro rho2 _ rg3 m m' Hok Ew). unfold rbase. rewrite Ea. intros i Hi.
      destruct (Htl b ltac:(apply in_or_app; left; exact Hin)) as (Tev & Tlo & Thi).
      assert (Hbtx : b <> tx) by (intros ->; apply Hnstx; reflexivity).
      assert (E2 : rho2 (sh_tag b) = shad (rho b)).
      { rewrite (Hag (sh_tag b)) by (rewrite sh_tag_Z by lia; lia). exact (proj1 (Hrsh b ltac:(apply in_or_app; left; exact Hin))). }
      rewrite E2. destruct (proj1 Hlink b Hin) as (rgb & Egb & _ & _ & Hsz0). rewrite (rsize_get M b rgb Egb) in Es.
      destruct (HL b Hin Hbtx) as [_ HinS']. rewrite (rsize_get M b rgb Egb) in HinS'.
      assert (HinS : In (rho b, to_Z (rg_size rgb)) (rt_live RT (g_S RT g))).
      { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. rewrite (rsize_get M b rgb Egb). auto. }
      pose proof (af_sh_live RT AF _ _ _ _ HART HinS) as Q. pose proof (af_sh_live RT AF _ _ _ _ HART' HinS') as Q'.
      apply (bytes_at_same m m' _ _ i Q Q'). pose proof (to_Z_bounded (rg_size rgb)). rewrite ushadow_length by lia. lia.
    + (* [comment removed for export] *)
      apply KEPT. intros i Hi. assert (E2 : rho2 t3 = rho t3) by (apply Hag; exact (Htags t3 rg3 Eg3)).
      destruct (wr_facts RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd M nx m t3 rg3 (rho t3 + i)) as (_ & _ & Hr47);
        [unfold FMem; cbv zeta; tauto | exact Eg3 | exact Ew | unfold rbase; rewrite Ea; lia |].
      apply (PRES i Hi); rewrite E2; [lia|]. right; right; right; left. exists (rho t3), (fcls (rsize M t3)). split.
      * rewrite Hfr. unfold frm_list. apply in_map_iff. exists t3. auto.
      * rewrite (rsize_get M t3 rg3 Eg3), (fcls_size _ Es). lia.
    + (* [comment removed for export] *)
      apply KEPT. intros i Hi.
      destruct (Htl f ltac:(apply in_or_app; right; exact Hin)) as (Tev & Tlo & Thi).
      assert (E2 : rho2 (sh_tag f) = shad (rho f)).
      { rewrite (Hag (sh_tag f)) by (rewrite sh_tag_Z by lia; lia). exact (proj1 (Hrsh f ltac:(apply in_or_app; right; exact Hin))). }
      destruct (wr_facts RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd M nx m (sh_tag f) rg3 (shad (rho f) + i)) as (_ & _ & Hr47);
        [unfold FMem; cbv zeta; tauto | exact Eg3 | exact Ew | unfold rbase; rewrite Ea, (proj1 (Hrsh f ltac:(apply in_or_app; right; exact Hin))); lia |].
      destruct (proj2 Hlink f Hin) as (rgf & Egf & _ & _ & Hfsz). pose proof (fsz_facts _ Hfsz) as (Fb & F8 & F64 & Fd).
      rewrite (rsize_get M f rgf Egf) in Es.
      apply (PRES i Hi); rewrite E2; [lia|]. right; right; right; right. exists (rho f), (fcls (rsize M f)). split.
      * rewrite Hfr. unfold frm_list. apply in_map_iff. exists f. auto.
      * rewrite (rsize_get M f rgf Egf), (fcls_size _ Hfsz).
        replace (rho f + (to_Z (rg_size rgf) + 8)) with (rho f + 8 * ((to_Z (rg_size rgf) + 8) / 8)) by (Z.div_mod_to_equations; lia). rewrite shad_add8. lia.
    + (* [comment removed for export] *)
      apply KEPT. intros i Hi. destruct (Hcb t3 nc wc Hin) as (HinCL & Hn0 & Hn8 & Tev & Tr & Hsh & Hwcb & Hcal).
      assert (E2 : rho2 t3 = rho t3) by (apply Hag; exact (Htags t3 rg3 Eg3)).
      destruct (HLc _ HinCL) as [HinL _].
      assert (HinS : In (rho t3, nc) (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact HinCL).
      destruct (af_live_range RT AF _ _ _ _ HART HinS) as (P1 & P2 & _). pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r.
      apply (PRES i Hi); rewrite E2; [unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia|]. right; right; left. exists (rho t3), nc. split; [exact HinL | lia].
    + (* [comment removed for export] *)
      apply (region_ok_ro rho2 _ rg3 m m' Hok Ew). unfold rbase. rewrite Ea. intros i Hi.
      destruct (Hcb b nc wc Hin) as (HinCL & Hn0 & Hn8 & Tev & Tr & Hsh & Hwcb & Hcal).
      assert (Hlt : to_Z (sh_tag b) < to_Z nx) by exact (Htags _ _ Eg3).
      assert (E2 : rho2 (sh_tag b) = shad (rho b)) by (rewrite (Hag (sh_tag b)) by exact Hlt; exact Hsh).
      rewrite E2. destruct (HLc _ HinCL) as [_ HinS'].
      assert (HinS : In (rho b, nc) (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact HinCL).
      pose proof (af_sh_live RT AF _ _ _ _ HART HinS) as Q. pose proof (af_sh_live RT AF _ _ _ _ HART' HinS') as Q'.
      apply (bytes_at_same m m' _ _ i Q Q'). unfold ushadow. rewrite Hn8. cbn [Z.eqb]. rewrite app_nil_r, repeat_length.
      rewrite Z2Nat.id by (apply Z.div_pos; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cell_ptr_bytes (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (k : int) (t' : int) (o' : w64) :
  region_ok ctasegs rho t rg m -> rd_cell ctasegs rg k = CP t' o' -> 8 * to_Z k + 8 <= to_Z (rg_size rg) ->
  bytes_at ctasegs m (rbase rho t rg + 8 * to_Z k) (le8 (pword rho t' o'))
  /\ (rg_wr rg = true -> wr_at ctasegs m (rbase rho t rg + 8 * to_Z k) 8).
Proof.
  intros Hok Hc Hfit. pose proof (to_Z_bounded k) as Bk.
  pose proof (region_bytes ctasegs rho t rg m (8 * to_Z k) (le8 (pword rho t' o')) Hok ltac:(lia)) as H. rewrite length_le8 in H.
  apply H; [exact Hfit|]. intros i b0 En b Kb.
  assert (Hi : (i < 8)%nat).
  { assert (X : nth_error (le8 (pword rho t' o')) i <> None) by congruence. apply nth_error_Some in X. rewrite length_le8 in X. exact X. }
  unfold le8, word_to_le_bytes in En. pose proof (bv_unsigned_in_range 64 (pword rho t' o')) as Hw.
  rewrite (nth_Z_to_le_bytes 8 (bv_unsigned (pword rho t' o')) i ltac:(lia) Hi) in En. injection En as <-.
  unfold rg_kb in Kb.
  assert (Ek : of_Z ((8 * to_Z k + Z.of_nat i) / 8) = k).
  { apply to_Z_inj. rewrite of_Z_small; [|split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; destruct Hok as (_ & _ & H62 & _); lia]].
    symmetry. apply Z.div_unique with (r := Z.of_nat i); lia. }
  assert (Em : (8 * to_Z k + Z.of_nat i) mod 8 = Z.of_nat i) by (symmetry; apply Z.mod_unique with (q := to_Z k); lia).
  rewrite Ek, Em, Hc in Kb. cbn [cell_kb kb_ok] in Kb. apply byte_of_eq. exact Kb.
Qed.

Lemma stk_word_sound (rho : valuation) (t : int) (rgs : region) (m : word -> option byte) (off : int) (v : hval) :
  region_ok ctasegs rho t rgs m -> rg_wr rgs = true ->
  stk_word ctasegs rgs off = Some v -> to_Z off mod 8 = 0 -> to_Z off + 8 <= to_Z (rg_size rgs) ->
  exists x, den rho v x /\ bytes_at ctasegs m (rbase rho t rgs + to_Z off) (le8 x) /\ wr_at ctasegs m (rbase rho t rgs + to_Z off) 8.
Proof.
  intros Hok Hw H Hal Hfit. unfold stk_word in H.
  assert (Ek : 8 * to_Z (off >> 3)%uint63 = to_Z off).
  { rewrite lsr_spec. change (2 ^ to_Z 3%uint63) with 8. pose proof (Z.div_mod (to_Z off) 8 ltac:(lia)). lia. }
  destruct (rd_cell ctasegs rgs (off >> 3)%uint63) as [w km|t' o'|tn on] eqn:Ec.
  - destruct (eqbP km 255%uint63) as [E|E]; [|discriminate]. apply to_Z_inj in E. subst km. injection H as <-.
    destruct (cell_word_bytes ctasegs rho t rgs m _ w Hok Ec ltac:(lia)) as [Hb Hwr]. rewrite Ek in Hb, Hwr.
    exists (wbv w). split; [reflexivity|]. split; [exact Hb | exact (Hwr Hw)].
  - injection H as <-. destruct (cell_ptr_bytes rho t rgs m _ t' o' Hok Ec ltac:(lia)) as [Hb Hwr]. rewrite Ek in Hb, Hwr.
    exists (pword rho t' o'). split; [reflexivity|]. split; [exact Hb | exact (Hwr Hw)].
  - discriminate H.
Qed.

Lemma rw_cells_two (m : word -> option byte) (A : Z) (v1 v2 : word) :
  bytes_at ctasegs m A (le8 v1) -> wr_at ctasegs m A 8 -> bytes_at ctasegs m (A + 8) (le8 v2) -> wr_at ctasegs m (A + 8) 8 ->
  rw_cells ctasegs m A [C8 v1; C8 v2].
Proof.
  intros B1 W1 B2 W2. split.
  - split; [cbn; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|]. rewrite length_le8. exact B2.
  - cbn [cells_size csize]. destruct W1 as (P1 & P2 & P3). destruct W2 as (Q1 & Q2 & Q3). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z_lt_le_dec i 8) as [L|L]; [apply P3; lia|]. replace (A + i) with (A + 8 + (i - 8)) by lia. apply Q3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive skind (Σ : rts RT) (a n : Z) : Prop :=
| SStack : a = B0A -> n = xp_stk xp + r -> skind Σ a n
| SBlock : In (a, n) (rt_live RT Σ) -> 0 < n -> a mod 8 = 0 -> skind Σ a n
| SImage : a = 0x10000 -> n = SEGTOP_A - 0x10000 -> skind Σ a n.

Inductive rkind (Σ : rts RT) (b s : Z) (wr : bool) : Prop :=
| KKilled : s = 0 -> b = 0 -> rkind Σ b s wr
| KImage : 0x10000 <= b -> b + s <= SEGTOP_A -> rkind Σ b s wr
| KShadowRO : forall a n, skind Σ a n -> b = shad a -> s = shsz n -> wr = false -> rkind Σ b s wr
| KStack : b = B0A -> s = xp_stk xp + r -> rkind Σ b s wr
| KBlock : In (b, s) (rt_live RT Σ) -> 0 < s -> rkind Σ b s wr
| KFrame : forall k, In (b, k) (rt_frames RT Σ) -> s = fs_size k - 8 -> rkind Σ b s wr
| KFrameSh : forall f k, In (f, k) (rt_frames RT Σ) -> b = shad f -> s = fs_size k / 8 -> rkind Σ b s wr.

Lemma shad_end (a n : Z) : n mod 8 = 0 -> shad (a + n) = shad a + n / 8.
Proof. intros H. pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D at 1. apply shad_add8. Qed.

Lemma uw_walk_sound (rho : valuation) (rgs : region) (m : word -> option byte) (lo' : Z) :
  region_ok ctasegs rho T_STK rgs m -> rg_abs rgs = None -> rg_wr rgs = true ->
  rho T_STK + to_Z (rg_size rgs) <= USTACK_TOP -> to_Z IMG_TOP <= lo' -> lo' <= rho T_STK -> rho T_STK mod 8 = 0 ->
  0 <= rho T_S0 < 2 ^ 64 -> (rho T_S0 <= lo' \/ rho T_S0 mod 8 <> 0 \/ 2 ^ 63 <= rho T_S0) ->
  forall (fuel : nat) (f : int) (fp : hval) (ras : list int) (x : word),
    uw_walk ctasegs T_STK T_S0 IMG_TOP fuel rgs f fp = Some ras -> den rho fp x -> to_Z f <= to_Z (rg_size rgs) ->
    uw_chain USTACK_TOP m (rho T_STK + to_Z f) (bv_unsigned x) (map to_Z ras).
Proof.
  intros Hok Eabs Hwr Htop Himg Hlo Hm8 Hr0 Hroot. pose proof Hok as (Bx0 & Bx1 & Bx2 & _). unfold rbase in Bx0, Bx1. rewrite Eabs in Bx0, Bx1. unfold two63 in Bx1.
  induction fuel as [|fuel IH]; intros f fp ras x H Hd Hf; [discriminate|]. cbn [uw_walk] in H.
  pose proof (to_Z_bounded f) as Bf.
  destruct fp as [w|t o| |]; [| |discriminate|discriminate].
  - (* [comment removed for export] *)
    destruct (wh w || negb (wl w land 7 =? 0)%uint63 || (wl w <? IMG_TOP)%uint63) eqn:E; [|discriminate]. injection H as <-.
    cbn [map uw_chain]. cbn [den] in Hd. subst x. rewrite wbv_unsigned. unfold fp_stop.
    destruct (wh w) eqn:Eh.
    + right; right. rewrite wZ_split, Eh. cbn [Z.b2z]. pose proof (to_Z_bounded (wl w)). change two63 with (2 ^ 63). lia.
    + assert (Ew : wZ w = to_Z (wl w)) by (rewrite wZ_split, Eh; cbn [Z.b2z]; lia). rewrite Ew. cbn [orb] in E.
      destruct (eqbP (wl w land 7)%uint63 0%uint63) as [E7|E7].
      * cbn [negb orb] in E. apply ltb_spec in E. left. lia.
      * right; left. rewrite land_spec' in E7. change (to_Z 7%uint63) with (Z.ones 3) in E7. rewrite Z.land_ones in E7 by lia. exact E7.
  - destruct (eqbP t T_STK) as [Et|Et].
    + (* [comment removed for export] *)
      apply to_Z_inj in Et. subst t.
      destruct (negb (wh o) && (f + 16 <=? wl o)%uint63 && (wl o land 7 =? 0)%uint63 && (wl o <=? rg_size rgs)%uint63) eqn:Eck; [|discriminate].
      apply andb_prop in Eck as [Eck Ec4]. apply andb_prop in Eck as [Eck Ec3]. apply andb_prop in Eck as [Ec1 Ec2].
      apply negb_true_iff in Ec1. apply leb_spec in Ec2, Ec4.
      destruct (eqbP (wl o land 7)%uint63 0%uint63) as [E7|E7]; [|discriminate].
      rewrite land_spec' in E7. change (to_Z 7%uint63) with (Z.ones 3) in E7. rewrite Z.land_ones in E7 by lia. change (to_Z 0%uint63) with 0 in E7. change (2 ^ 3) with 8 in E7.
      pose proof (to_Z_bounded (wl o)) as Bo. pose proof (to_Z_bounded (rg_size rgs)) as Bs.
      assert (Ef16 : to_Z (f + 16)%uint63 = to_Z f + 16) by (rewrite add_spec; change (to_Z 16%uint63) with 16; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
      rewrite Ef16 in Ec2.
      assert (Eo16 : to_Z (wl o - 16)%uint63 = to_Z (wl o) - 16) by (rewrite sub_spec; change (to_Z 16%uint63) with 16; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
      assert (Eo8 : to_Z (wl o - 8)%uint63 = to_Z (wl o) - 8) by (rewrite sub_spec; change (to_Z 8%uint63) with 8; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
      destruct (stk_word ctasegs rgs (wl o - 16)%uint63) as [fp'|] eqn:E1; [|discriminate].
      destruct (stk_word ctasegs rgs (wl o - 8)%uint63) as [[ra| | |]|] eqn:E2; try discriminate.
      destruct (wh ra) eqn:Era; [discriminate|].
      destruct (uw_walk ctasegs T_STK T_S0 IMG_TOP fuel rgs (wl o) fp') as [l|] eqn:El; [|discriminate]. injection H as <-.
      assert (Ex : bv_unsigned x = rho T_STK + to_Z (wl o)).
      { cbn [den] in Hd. subst x. unfold pword. rewrite wZ_split, Ec1. cbn [Z.b2z]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
        unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). lia. }
      destruct (stk_word_sound rho T_STK rgs m _ fp' Hok Hwr E1) as (x1 & D1 & Hb1 & Hw1);
        [rewrite Eo16; replace (to_Z (wl o) - 16) with (to_Z (wl o) + (-2) * 8) by ring; rewrite Z.mod_add by lia; exact E7 | rewrite Eo16; lia |].
      destruct (stk_word_sound rho T_STK rgs m _ (VC ra) Hok Hwr E2) as (x2 & D2 & Hb2 & Hw2);
        [rewrite Eo8; replace (to_Z (wl o) - 8) with (to_Z (wl o) + (-1) * 8) by ring; rewrite Z.mod_add by lia; exact E7 | rewrite Eo8; lia |].
      unfold rbase in Hb1, Hw1, Hb2, Hw2. rewrite Eabs in Hb1, Hw1, Hb2, Hw2. rewrite Eo16 in Hb1, Hw1. rewrite Eo8 in Hb2, Hw2. cbn [den] in D2. subst x2.
      cbn [map uw_chain]. rewrite Ex. split; [lia|]. split; [rewrite Z.add_mod, E7, Hm8 by lia; reflexivity|].
      split; [lia|]. exists (bv_unsigned x1). split; [pose proof (bv_unsigned_in_range 64 x1) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr|]. split.
      * rewrite Z_to_bv_bv_unsigned.
        assert (Era' : Z_to_bv 64 (to_Z (wl ra)) = wbv ra) by (unfold wbv; rewrite wZ_split, Era; cbn [Z.b2z]; f_equal; lia).
        rewrite Era'. apply rw_cells_two.
        -- replace (rho T_STK + to_Z (wl o) + -16) with (rho T_STK + (to_Z (wl o) - 16)) by ring. exact Hb1.
        -- replace (rho T_STK + to_Z (wl o) + -16) with (rho T_STK + (to_Z (wl o) - 16)) by ring. exact Hw1.
        -- replace (rho T_STK + to_Z (wl o) + -16 + 8) with (rho T_STK + (to_Z (wl o) - 8)) by ring. exact Hb2.
        -- replace (rho T_STK + to_Z (wl o) + -16 + 8) with (rho T_STK + (to_Z (wl o) - 8)) by ring. exact Hw2.
      * exact (IH (wl o) fp' l x1 El D1 Ec4).
    + (* [comment removed for export] *)
      destruct (eqbP t T_S0) as [Es|Es]; [|discriminate]. apply to_Z_inj in Es. subst t. cbn [andb] in H.
      destruct (is_zero o) eqn:Ez; [|discriminate]. injection H as <-. apply is_zero_spec in Ez. subst o.
      cbn [map uw_chain]. cbn [den] in Hd. subst x. unfold pword. change (wZ w_zero) with 0. rewrite Z.add_0_r, Z_to_bv_unsigned.
      rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
      unfold fp_stop. destruct Hroot as [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
Qed.

Lemma fs_size_facts (k : nat) : 64 <= fs_size k /\ fs_size k mod 64 = 0 /\ fs_size k / 8 = (fs_size k - 8) / 8 + 1 /\ (fs_size k - 8) mod 8 = 0.
Proof.
  unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia.
  assert (H1 : 1 <= 2 ^ Z.of_nat k) by (change 1 with (2 ^ 0) at 1; apply Z.pow_le_mono_r; lia).
  set (x := 2 ^ Z.of_nat k) in *. clearbody x.
  repeat split; Z.div_mod_to_equations; nia.
Qed.

Lemma region_loc (g : ghost RT) (rho rho2 : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte) (t2 : int) (rg2 : region) :
  FMemA g rho cd M nx m -> agree_below nx rho rho2 -> mget M t2 = Some rg2 ->
  rkind (g_S RT g) (rbase rho2 t2 rg2) (to_Z (rg_size rg2)) (rg_wr rg2).
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & Hcnt & Hagr & Hsp0a & Hcb) Hag Eg.
  pose proof (Hcls t2 rg2 Eg) as C. pose proof (Htags t2 rg2 Eg) as Hlt. pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r.
  pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1). change (to_Z NEXT0) with 32 in *.
  unfold rbase. destruct (rg_abs rg2) as [a|] eqn:Ea.
  - destruct C as [(C1 & C2 & _)|[(w0 & C & Cw0) _]]; [apply KKilled; assumption|].
    assert (Kro : w0 = false -> rg_wr rg2 = false) by (intros ->; destruct (rg_wr rg2); [discriminate (Cw0 eq_refl) | reflexivity]).
    destruct (static_facts _ _ _ C) as (S1 & S2 & S3 & [S4|[S4a S4b]] & _ & S6).
    + apply KImage; lia.
    + destruct S6 as [(K1 & K2 & K3)|[(K1 & K2 & K3)|[K|[(K1 & K2 & K3)|[(K1 & K2 & K3)|(K1 & K2 & K3)]]]]];
        try (exfalso; unfold IMGSH_LO, IMGSH_HI, RELRO_LO, RELRO_HI, g_shadow_memory_dynamic_address in *; lia).
      * exfalso. pose proof (client_static_range _ (K (to_Z a) ltac:(lia))) as X. unfold IMGSH_LO in *. lia.
      * apply (KShadowRO _ _ _ _ 0x10000 (SEGTOP_A - 0x10000)); [apply SImage; reflexivity | rewrite K1; reflexivity | rewrite K1 in K2; unfold IMGSH_LO, IMGSH_HI in *; change (shsz (SEGTOP_A - 65536)) with 1537536; lia | exact (Kro K3)].
  - destruct C as [(-> & Es & _)|[(-> & Es & Ew)|[(Hin & Ew)|[(b & Hin & -> & Es & Ew)|[(Hin & Es & Ew)|[(f & Hin & -> & Es & Ew)|[(nc & wc & Hin & Es & Cw)|(b & nc & wc & Hin & -> & Es & Ew)]]]]]]].
    + apply KStack; [rewrite (Hag T_STK) by (change (to_Z T_STK) with 2; lia); exact Hrs | exact Es].
    + rewrite (Hag (sh_tag T_STK)) by (change (to_Z (sh_tag T_STK)) with 3; lia). rewrite Hrss, Es.
      assert (H8 : (xp_stk xp + r) mod 8 = 0) by (clear - ESTK32 H_r; destruct H_r as [-> | ->]; lia).
      apply (KShadowRO _ _ _ _ B0A (xp_stk xp + r)); [apply SStack; reflexivity | reflexivity | rewrite shsz_mul8 by exact H8; reflexivity | exact Ew].
    + destruct (proj1 Hlink t2 Hin) as (rgb & Egb & _ & _ & Hs0). rewrite Eg in Egb. injection Egb as <-.
      rewrite (Hag t2 Hlt). apply KBlock; [|exact Hs0].
      rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists t2. rewrite (rsize_get M t2 rg2 Eg). auto.
    + destruct (Htl b ltac:(apply in_or_app; left; exact Hin)) as (_ & T1 & T2).
      destruct (proj1 Hlink b Hin) as (rgb & Egb & _ & _ & Hs0). rewrite (rsize_get M b rgb Egb) in Es.
      destruct (Hrsh b ltac:(apply in_or_app; left; exact Hin)) as [Hshb Hal].
      rewrite (Hag (sh_tag b)) by (rewrite sh_tag_Z by lia; lia). rewrite Hshb, Es.
      assert (HinL : In (rho b, to_Z (rg_size rgb)) (rt_live RT (g_S RT g))).
      { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. rewrite (rsize_get M b rgb Egb). auto. }
      apply (KShadowRO _ _ _ _ (rho b) (to_Z (rg_size rgb))); [apply SBlock; assumption | reflexivity | reflexivity | exact Ew].
    + rewrite (Hag t2 Hlt). apply (KFrame _ _ _ _ (fcls (to_Z (rg_size rg2)))); [| rewrite (fcls_size _ Es); lia].
      rewrite Hfr. unfold frm_list. apply in_map_iff. exists t2. rewrite (rsize_get M t2 rg2 Eg). auto.
    + destruct (Htl f ltac:(apply in_or_app; right; exact Hin)) as (_ & T1 & T2).
      destruct (proj2 Hlink f Hin) as (rgf & Egf & _ & _ & Hfsz). rewrite (rsize_get M f rgf Egf) in Es.
      rewrite (Hag (sh_tag f)) by (rewrite sh_tag_Z by lia; lia). rewrite (proj1 (Hrsh f ltac:(apply in_or_app; right; exact Hin))).
      apply (KFrameSh _ _ _ _ (rho f) (fcls (to_Z (rg_size rgf)))); [|reflexivity | rewrite (fcls_size _ Hfsz), Es; pose proof (fsz_facts _ Hfsz); lia].
      rewrite Hfr. unfold frm_list. apply in_map_iff. exists f. rewrite (rsize_get M f rgf Egf). auto.
    + destruct (Hcb t2 nc wc Hin) as (HinCL & Hn0 & Hn8 & _). rewrite (Hag t2 Hlt), Es. apply KBlock; [|exact Hn0].
      rewrite Hlive. apply in_or_app. right. exact HinCL.
    + destruct (Hcb b nc wc Hin) as (HinCL & Hn0 & Hn8 & _ & _ & Hsh & _ & Hcal). rewrite (Hag (sh_tag b) Hlt), Hsh, Es.
      assert (HinL : In (rho b, nc) (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact HinCL).
      apply (KShadowRO _ _ _ _ (rho b) nc); [apply SBlock; [exact HinL | exact Hn0 | exact Hcal] | reflexivity | rewrite shsz_mul8 by exact Hn8; reflexivity | exact Ew].
Qed.

(* [comment removed for export] *)
Lemma region_loc_clobbered (g : ghost RT) (rho rho2 : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte)
    (rgs : region) (o : int) (t2 : int) (rg2 : region) :
  FMemA g rho cd M nx m -> agree_below nx rho rho2 -> mget M T_STK = Some rgs ->
  mget (mset M T_STK (drop_below rgs o)) t2 = Some rg2 ->
  rkind (g_S RT g) (rbase rho2 t2 rg2) (to_Z (rg_size rg2)) (rg_wr rg2).
Proof.
  intros HF Hag Egs G. destruct (mget_mset_cases M T_STK t2 _ rg2 (mget_lt M T_STK rgs Egs) G) as [[-> ->]|[_ G']].
  - exact (region_loc g rho rho2 cd M nx m T_STK rgs HF Hag Egs).
  - exact (region_loc g rho rho2 cd M nx m t2 rg2 HF Hag G').
Qed.

(* [comment removed for export] *)
Definition loc_bounds (Σ : rts RT) : Prop :=
  rt_sp0 RT Σ - STACK_WIN <= lo /\ lo <= B0A /\ sp0 + 16 <= USTACK_TOP /\ sp0 mod 32 = r.

Lemma FMem_loc_bounds (g : ghost RT) (rho : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte) :
  FMemA g rho cd M nx m -> loc_bounds (g_S RT g) /\ ART RT (g_S RT g) m.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HART & _ & _ & HB & _). exact (conj HB HART). Qed.

Lemma skind_facts (Σ : rts RT) (m : word -> option byte) (a n : Z) :
  ART RT Σ m -> loc_bounds Σ -> skind Σ a n -> 0 < a /\ 0 < n /\ a + n + 8 <= 2 ^ 47 /\ a mod 8 = 0.
Proof.
  intros HART (L1 & L2 & L3 & L4) K. pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1).
  destruct K as [-> -> | Hin H0 H8 | -> ->].
  - unfold B0, SEGTOP_A, STACK_WIN, USTACK_TOP in *. split; [lia|]. split; [destruct H_r; lia|]. split; [lia|].
    apply B0_mod8. exact L4.
  - destruct (af_live_range RT AF _ _ _ _ HART Hin) as (P1 & P2 & _). unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *.
    split; [lia|]. split; [lia|]. split; [lia | exact H8].
  - unfold SEGTOP_A. split; [lia|]. split; [lia|]. split; [lia | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma skind_shadow (Σ : rts RT) (m : word -> option byte) (a n : Z) :
  ART RT Σ m -> loc_bounds Σ -> skind Σ a n -> SH_LO < shad a /\ shad a + shsz n < SH_HI /\ shad a + shsz n = shad (a + 8 * shsz n) /\ a + n <= a + 8 * shsz n < a + n + 8.
Proof.
  intros HART HB K. destruct (skind_facts Σ m a n HART HB K) as (F1 & F2 & F3 & F4).
  pose proof (shsz_bounds n ltac:(lia)) as Bs.
  pose proof (shad_range a ltac:(lia)) as R1. pose proof (shad_range (a + 8 * shsz n) ltac:(lia)) as R2.
  rewrite <- (shad_add8 a (shsz n)) in *. unfold SH_LO, SH_HI in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma kind_apart_block (Σ Σ' : rts RT) (m m' : word -> option byte) (b s : Z) (wr : bool) (p n px : Z) (l2 : list (Z * Z)) :
  rkind Σ b s wr -> ART RT Σ m -> loc_bounds Σ -> ART RT Σ' m' ->
  rt_live RT Σ' = (p, n) :: l2 -> (forall b0 s0, In (b0, s0) (rt_live RT Σ) -> b0 <> px -> In (b0, s0) l2) ->
  rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  (In (b, s) (rt_live RT Σ) -> 0 < s -> b <> px) -> 0 <= n ->
  p + n <= b \/ b + s <= p.
Proof.
  intros K HART HB HART' El Hl2 Ef Es Hpx Hn.
  assert (HinP : In (p, n) (rt_live RT Σ')) by (rewrite El; left; reflexivity).
  destruct (af_live_range RT AF _ _ _ _ HART' HinP) as (P1 & P2 & P3).
  pose proof (af_live_offshadow RT AF _ _ _ _ HART' HinP) as P4.
  pose proof HB as (L1 & L2 & L3 & L4). rewrite Es in P2.
  destruct K as [-> -> | K1 K2 | a0 n0 K -> -> _ | -> -> | Hin H0 | k Hin -> | f k Hin -> ->].
  - right. lia.
  - destruct P3 as [P3|P3]; [left; lia | right; lia].
  - destruct (skind_shadow Σ m a0 n0 HART HB K) as (Q1 & Q2 & _). unfold SH_LO, SH_HI in *. destruct P4 as [P4|P4]; [left; lia | right; lia].
  - left. unfold B0, STACK_WIN in *. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1). lia.
  - specialize (Hl2 b s Hin (Hpx Hin H0)).
    destruct (af_live_disj RT AF Σ' m' p n b s [] l2 HART' El Hl2) as [D|D]; [left | right]; lia.
  - rewrite <- Ef in Hin. destruct (af_frames_range RT AF _ _ _ _ HART' Hin) as (_ & _ & _ & F4).
    destruct (F4 p n HinP) as [D|D]; [right; lia | left; lia].
  - rewrite <- Ef in Hin. destruct (af_fshadow_apart RT AF _ _ _ _ HART' Hin) as [F1 _].
    pose proof (fs_size_facts k) as (G1 & G2 & G3 & G4).
    rewrite (shad_end f (fs_size k)) in F1 by (Z.div_mod_to_equations; lia). destruct (F1 p n HinP) as [D|D]; [left; lia | right; lia].
Qed.

(* [comment removed for export] *)
Lemma kind_apart_bshadow (Σ Σ' : rts RT) (m m' : word -> option byte) (b s : Z) (p n : Z) :
  rkind Σ b s true -> ART RT Σ m -> loc_bounds Σ -> ART RT Σ' m' ->
  In (p, n) (rt_live RT Σ') -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> 0 <= n -> p mod 8 = 0 ->
  shad p + shsz n <= b \/ b + s <= shad p.
Proof.
  intros K HART HB HART' HinP Ef Es Hn Hp8.
  destruct (af_live_range RT AF _ _ _ _ HART' HinP) as (P1 & P2 & P3). rewrite Es in P2.
  pose proof HB as (L1 & L2 & L3 & L4). pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (af_sp0_win RT AF _ _ HART) as Hsp0w.
  pose proof (shsz_bounds n Hn) as Bs. rewrite (shad_shsz p n Hp8 Hn).
  pose proof (shad_range p ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as R1.
  pose proof (shad_range (p + n) ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as R2.
  assert (R3 : shad (p + 8 * shsz n) <= shad (p + n) + 1).
  { rewrite <- shad_add8. replace (p + n + 8 * 1) with (p + n + 8) by ring. apply shad_mono. lia. }
  unfold SH_LO, SH_HI in *.
  destruct K as [-> -> | K1 K2 | a0 n0 K -> -> Hc | -> -> | Hin H0 | k Hin -> | f k Hin -> ->].
  - right. lia.
  - right. unfold SEGTOP_A in *. lia.
  - discriminate Hc.
  - left. unfold B0, STACK_WIN in *. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1). lia.
  - destruct (af_live_offshadow RT AF _ _ _ _ HART Hin) as [D|D]; [right; lia | left; lia].
  - pose proof (fs_size_facts k) as (G1 & _). destruct (af_frames_hi RT AF _ _ _ _ HART Hin) as [D|D]; [right; lia | left; lia].
  - rewrite <- Ef in Hin. destruct (af_frames_range RT AF _ _ _ _ HART' Hin) as (_ & _ & _ & F4).
    destruct (af_frames_align RT AF _ _ _ _ HART' Hin) as [F64 _]. pose proof (fs_size_facts k) as (G1 & G2 & G3 & G4).
    destruct (F4 p n HinP) as [D|D].
    + right. rewrite <- (shad_end f (fs_size k)) by (Z.div_mod_to_equations; lia). apply shad_mono. exact D.
    + left. rewrite <- (shad_shsz p n Hp8 Hn). apply (shad_cover p n f Hp8); [Z.div_mod_to_equations; lia | exact Hn | exact D].
Qed.

(* [comment removed for export] *)
Lemma kind_apart_frame (Σ Σ' : rts RT) (m m' : word -> option byte) (b s : Z) (wr : bool) (f : Z) (k : nat) :
  rkind Σ b s wr -> ART RT Σ m -> loc_bounds Σ -> ART RT Σ' m' ->
  rt_frames RT Σ' = (f, k) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  (f + fs_size k <= b \/ b + s <= f) /\ (shad f + fs_size k / 8 <= b \/ b + s <= shad f).
Proof.
  intros K HART HB HART' Ef El Es.
  assert (HinF : In (f, k) (rt_frames RT Σ')) by (rewrite Ef; left; reflexivity).
  destruct (af_frames_range RT AF _ _ _ _ HART' HinF) as (F1 & F2 & F3 & F4). rewrite Es in F2.
  pose proof (af_frames_hi RT AF _ _ _ _ HART' HinF) as F5.
  destruct (af_fshadow_apart RT AF _ _ _ _ HART' HinF) as [F6 F7].
  destruct (af_frames_align RT AF _ _ _ _ HART' HinF) as [F64 _].
  pose proof (fs_size_facts k) as (G1 & G2 & G3 & G4).
  pose proof HB as (L1 & L2 & L3 & L4). pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (af_sp0_win RT AF _ _ HART) as Hsp0w.
  assert (E64 : shad (f + fs_size k) = shad f + fs_size k / 8) by (apply shad_end; Z.div_mod_to_equations; lia).
  rewrite E64 in *.
  pose proof (shad_range f ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as R1.
  pose proof (shad_range (f + fs_size k) ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as R2. rewrite E64 in R2.
  assert (SHD : forall a0 n0, a0 mod 8 = 0 -> 0 <= n0 -> f + fs_size k <= a0 \/ a0 + n0 <= f -> shad f + fs_size k / 8 <= shad a0 \/ shad a0 + shsz n0 <= shad f).
  { intros a0 n0 H8 Hn0 [D|D]; [left; pose proof (shad_mono _ _ D) as X; rewrite E64 in X; exact X|].
    right. apply (shad_cover a0 n0 f H8); [Z.div_mod_to_equations; lia | exact Hn0 | exact D]. }
  unfold SH_LO, SH_HI in *.
  destruct K as [-> -> | K1 K2 | a0 n0 K -> -> _ | -> -> | Hin H0 | k' Hin -> | f' k' Hin -> ->].
  - split; right; lia.
  - split; [destruct F3 as [D|D]; [left; lia | right; lia] | right; unfold SEGTOP_A in *; lia].
  - destruct (skind_shadow Σ m a0 n0 HART HB K) as (Q1 & Q2 & _). destruct (skind_facts Σ m a0 n0 HART HB K) as (_ & Q0 & _ & Q8). unfold SH_LO, SH_HI in *.
    split; [destruct F5 as [D|D]; [left; lia | right; lia]|]. apply (SHD a0 n0 Q8 ltac:(lia)).
    destruct K as [-> -> | Hin H0 H8 | -> ->].
    + left. lia.
    + rewrite <- El in Hin. exact (F4 a0 n0 Hin).
    + destruct F3 as [D|D]; [left; lia | right; lia].
  - split; left; [lia | unfold B0, STACK_WIN in *; pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1); lia].
  - rewrite <- El in Hin. split; [exact (F4 b s Hin)|]. destruct (F6 b s Hin) as [D|D]; [right; lia | left; lia].
  - assert (Hin' : In (b, k') (rt_frames RT Σ')) by (rewrite Ef; right; exact Hin).
    pose proof (fs_size_facts k') as (G1' & G2' & G3' & G4').
    split.
    + destruct (af_frames_disj RT AF Σ' m' f k b k' [] (rt_frames RT Σ) HART' Ef Hin) as [D|D]; [left; lia | right; lia].
    + destruct (F7 b k' Hin') as [D|D]; [right; lia | left; lia].
  - assert (Hin' : In (f', k') (rt_frames RT Σ')) by (rewrite Ef; right; exact Hin).
    destruct (af_fshadow_apart RT AF _ _ _ _ HART' Hin') as [_ G7].
    pose proof (fs_size_facts k') as (G1' & G2' & G3' & G4'). destruct (af_frames_align RT AF _ _ _ _ HART' Hin') as [F64' _].
    assert (E64' : shad (f' + fs_size k') = shad f' + fs_size k' / 8) by (apply shad_end; Z.div_mod_to_equations; lia).
    rewrite E64' in G7. split.
    + destruct (G7 f k HinF) as [D|D]; [left; lia | right; lia].
    + destruct (af_frames_disj RT AF Σ' m' f k f' k' [] (rt_frames RT Σ) HART' Ef Hin) as [D|D].
      * left. pose proof (shad_mono _ _ D) as X. rewrite E64 in X. exact X.
      * right. pose proof (shad_mono _ _ D) as X. rewrite E64' in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma xclobber_inv (ts rts_ : int) (S : sstate) (M M' : HxMem.mem) : xclobber_stack rts_ S M = Some M' -> xsp_ok ts S = true ->
  exists o rgs, rget S X2 = VP ts o /\ wh o = false /\ mget M ts = Some rgs /\ rg_abs rgs = None /\ rg_dflt rgs = DUnk
    /\ to_Z (wl o) mod 16 = 0 /\ to_Z rts_ <= to_Z (wl o) /\ to_Z (wl o) <= to_Z (rg_size rgs) /\ rg_wr rgs = true
    /\ M' = mset M ts (drop_below rgs (wl o)).
Proof.
  intros H Hsp. unfold xclobber_stack in H. unfold xsp_ok in Hsp. destruct (rget S X2) as [|t o| |]; try discriminate.
  apply Uint63.eqb_spec in Hsp. subst t.
  destruct (wh o) eqn:Eh; [discriminate|]. destruct (mget M ts) as [rg|] eqn:Eg; [|discriminate].
  destruct (rg_abs rg) eqn:Ea; [discriminate|]. destruct (rg_dflt rg) eqn:Ed; try discriminate.
  destruct ((wl o land 15 =? 0)%uint63 && (rts_ <=? wl o)%uint63 && (wl o <=? rg_size rg)%uint63 && rg_wr rg) eqn:Ec; [|discriminate].
  injection H as <-. apply andb_prop in Ec as [Ec Ew]. apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [E1 E2].
  apply leb_spec in E2, E3. destruct (eqbP (wl o land 15)%uint63 0%uint63) as [E15|E15]; [|discriminate].
  rewrite land_spec' in E15. change (to_Z 15%uint63) with (Z.ones 4) in E15. rewrite Z.land_ones in E15 by lia.
  exists o, rg. repeat (split; [first [reflexivity | assumption]|]). reflexivity.
Qed.

Lemma xret_inv (S S' : sstate) (res : hval) (M : HxMem.mem) (nx : int) : xret S res M nx = Some S' ->
  exists ra, rget S X1 = VC ra /\ s_resv S = RNone
    /\ S' = SS (w_and ra w_notone) (rf_set (havoc_caller_saved (s_regs S)) X10 res) RNone M (s_abs S) nx.
Proof.
  intros H. unfold xret in H. destruct (rget S X1) as [ra| | |]; try discriminate. destruct (s_resv S); try discriminate.
  injection H as <-. exists ra. auto.
Qed.

(* [comment removed for export] *)
Lemma stack_after_call (rho2 : valuation) (rgs : region) (o : int) (m m' : word -> option byte) :
  region_ok ctasegs rho2 T_STK rgs m -> rg_abs rgs = None -> rg_dflt rgs = DUnk -> to_Z (rg_size rgs) = xp_stk xp + r -> rho2 T_STK = B0A ->
  to_Z o mod 8 = 0 -> to_Z o <= to_Z (rg_size rgs) -> sp0 + 16 <= USTACK_TOP -> lo <= B0A ->
  stk ctasegs m' lo (B0A + to_Z o) -> (forall a, B0A + to_Z o <= a < sp0 -> m' (wa a) = m (wa a)) ->
  region_ok ctasegs rho2 T_STK (drop_below rgs o) m'.
Proof.
  intros Hok Eabs Edf Esz Erho Ho8 Ho Htop Hlo Hstk' Hkept. pose proof (region_mapped ctasegs rho2 _ rgs m Hok) as Hmap.
  pose proof Hok as (Bx0 & Bx1 & _). unfold two63 in Bx1. unfold rbase in *. rewrite Eabs in *. rewrite Esz, Erho in *.
  pose proof (to_Z_bounded o) as Bo. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1).
  assert (KEPT : forall i, to_Z o <= i < xp_stk xp + r -> m' (wa (B0A + i)) = m (wa (B0A + i))).
  { intros i Hi. apply Hkept. unfold B0 in *. lia. }
  apply (region_ok_drop ctasegs rho2 T_STK rgs o m m' Hok Edf Ho8); unfold rbase; rewrite Eabs, ?Esz, Erho.
  - intros i Hi. destruct (Z_lt_le_dec i (to_Z o)) as [Lt|Ge].
    + destruct Hstk' as (_ & _ & Hs). destruct (Hs (B0A + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
    + destruct (same_byte_kept m m' _ (KEPT i ltac:(lia))) as [E W]. destruct (Hmap i Hi) as [[b Hb] Hw]. split; [exists b; rewrite E; exact Hb|].
      intros Hwr. apply W, Hw, Hwr.
  - intros i Hi. exact (proj1 (same_byte_kept m m' _ (KEPT i Hi))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ms_nf (rho : valuation) (S : sstate) (ms : machine_state) :
  R ctasegs rho S ms -> s_resv S = RNone -> ms_rom ms = seg_rom ctasegs -> regs_nf (ms_regs ms) ->
  exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            (ms_fregs ms) (wbv (s_pc S)) (ms_fcsr ms) None (ms_mem ms) (seg_rom ctasegs)
    /\ Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                (ms_fregs ms) (wbv (s_pc S)) (ms_fcsr ms) None).
Proof.
  intros (Hsvc & Hpc & HRg & Hrv & _) Erv Hro Hnf. rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Eregs).
  exists x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31.
  split.
  - rewrite (MS_eta ms Hsvc) at 1. rewrite Eregs, Hro, Hrv, Hpc. reflexivity.
  - unfold core_of in HRg. rewrite Eregs, Hrv, Hpc in HRg. exact HRg.
Qed.

(* [comment removed for export] *)
Lemma FMem_law (g : ghost RT) (rho rho2 : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte) :
  FMemA g rho cd M nx m -> agree_below nx rho rho2 -> sh_law (wZ SHBW) rho2 M.
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hroot) & _ & _ & _ & _ & _ & _ & _ & Hcb) Hag s rg Eg Ea Hodd.
  rewrite SHBW_Z. pose proof (Hcls s rg Eg) as C. rewrite Ea in C. change (to_Z NEXT0) with 32 in *.
  assert (Hshad : forall t, to_Z t + 1 < to_Z nx -> rho (sh_tag t) = shad (rho t) -> s = sh_tag t -> rho2 s = rho2 (s - 1)%uint63 / 8 + SHB).
  { intros t Ht E ->. assert (Ht' : to_Z t < 1000000) by lia.
    assert (Ep : (sh_tag t - 1)%uint63 = t).
    { apply to_Z_inj. rewrite sub_spec, (sh_tag_Z t Ht'). change (to_Z 1%uint63) with 1. replace (to_Z t + 1 - 1) with (to_Z t) by ring. apply Z.mod_small. apply to_Z_bounded. }
    rewrite Ep, (Hag (sh_tag t)) by (rewrite sh_tag_Z by lia; lia). rewrite (Hag t) by lia. exact E. }
  destruct C as [(-> & _)|[(-> & _)|[(Hin & _)|[(b & Hin & -> & _)|[(Hin & _)|[(f & Hin & -> & _)|[(nc & wc & Hin & _)|(b & nc & wc & Hin & -> & _)]]]]]]].
  - discriminate Hodd.
  - apply (Hshad T_STK); [change (to_Z T_STK) with 2; lia | rewrite Hrs; exact Hrss | reflexivity].
  - destruct (Htl s ltac:(apply in_or_app; left; exact Hin)) as (Tev & _). congruence.
  - destruct (Htl b ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & Thi).
    apply (Hshad b Thi); [exact (proj1 (Hrsh b ltac:(apply in_or_app; left; exact Hin))) | reflexivity].
  - destruct (Htl s ltac:(apply in_or_app; right; exact Hin)) as (Tev & _). congruence.
  - destruct (Htl f ltac:(apply in_or_app; right; exact Hin)) as (_ & _ & Thi).
    apply (Hshad f Thi); [exact (proj1 (Hrsh f ltac:(apply in_or_app; right; exact Hin))) | reflexivity].
  - destruct (Hcb s nc wc Hin) as (_ & _ & _ & Tev & _). congruence.
  - destruct (Hcb b nc wc Hin) as (_ & _ & _ & _ & Tr & Hsh & _). pose proof (Htags _ _ Eg) as Hlt. rewrite sh_tag_Z in Hlt by lia.
    apply (Hshad b Hlt Hsh eq_refl).
Qed.

(* [comment removed for export] *)
Lemma caller_aclient (X : list (Z * Z)) (F : list (Z * nat)) (spc a : Z) :
  spc <= sp0 -> caller_mem CL sp0 xp a -> aclient (X ++ CL) F spc a.
Proof.
  intros Hsp [[Hc|[Hc|[(p & n & Hin & Hr)|[(f & k & [] & _)|(f & k & [] & _)]]]] _].
  - left. lia.
  - right; left. exact Hc.
  - right; right; left. exists p, n. split; [apply in_or_app; right; exact Hin | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma stk_class (g : ghost RT) (rho : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m : word -> option byte) (rgs : region) :
  FMemA g rho cd M nx m -> mget M T_STK = Some rgs -> rg_abs rgs = None -> to_Z (rg_size rgs) = xp_stk xp + r /\ rg_wr rgs = true.
Proof.
  intros (_ & _ & _ & Htl & _ & _ & Hnx & Hcls & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcb) Eg Ea. pose proof (Hcls T_STK rgs Eg) as C. rewrite Ea in C. change (to_Z NEXT0) with 32 in *.
  assert (Hsh : forall t, to_Z NEXT0 <= to_Z t -> to_Z t + 1 < to_Z nx -> T_STK <> sh_tag t).
  { intros t H1 H2 E. pose proof (f_equal to_Z E) as E'. rewrite sh_tag_Z in E' by lia. change (to_Z T_STK) with 2 in E'. change (to_Z NEXT0) with 32 in H1. lia. }
  destruct C as [(_ & C2 & C3)|[(C1 & _)|[(Hin & _)|[(b & Hin & C1 & _)|[(Hin & _)|[(f & Hin & C1 & _)|[(nc & wc & Hin & _)|(b & nc & wc & Hin & C1 & _)]]]]]]]; [auto | discriminate C1 | | | | | |].
  - destruct (Htl T_STK ltac:(apply in_or_app; left; exact Hin)) as (_ & H1 & _). change (to_Z T_STK) with 2 in H1. lia.
  - destruct (Htl b ltac:(apply in_or_app; left; exact Hin)) as (_ & H1 & H2). exfalso. exact (Hsh b H1 H2 C1).
  - destruct (Htl T_STK ltac:(apply in_or_app; right; exact Hin)) as (_ & H1 & _). change (to_Z T_STK) with 2 in H1. lia.
  - destruct (Htl f ltac:(apply in_or_app; right; exact Hin)) as (_ & H1 & H2). exfalso. exact (Hsh f H1 H2 C1).
  - destruct (Hcb T_STK nc wc Hin) as (_ & _ & _ & _ & Tr & _). change (to_Z T_STK) with 2 in Tr. change (to_Z NEXT0) with 32 in Tr. lia.
  - destruct (Hcb b nc wc Hin) as (_ & _ & _ & _ & Tr & _). exfalso. change (to_Z NEXT0) with 32 in Tr. pose proof (f_equal to_Z C1) as E'. rewrite sh_tag_Z in E' by lia. change (to_Z T_STK) with 2 in E'. lia.
Qed.

(* [comment removed for export] *)
Lemma clobber_dirs (M : HxMem.mem) (rgs : region) (o : int) : mget M T_STK = Some rgs -> rg_wr rgs = true ->
  same_dirs M (mset M T_STK (drop_below rgs o)) /\ ro_same M (mset M T_STK (drop_below rgs o)).
Proof.
  intros Eg Hw. split; [exact (same_dirs_mset M T_STK rgs _ Eg (same_dir_drop_below rgs o))|].
  intros t rg G W. rewrite (mget_mset M T_STK t _ (mget_lt M T_STK rgs Eg)).
  destruct (Z.eqb_spec (to_Z T_STK) (to_Z t)) as [E|E]; [|exact G]. apply to_Z_inj in E. subst t. congruence.
Qed.

(* [comment removed for export] *)
Lemma pres_ex_of_pres (L : list (Z * Z)) (F : list (Z * nat)) (spc : Z) (m m' : word -> option byte) :
  rt_pres L F spc m m' -> rt_pres_ex L F spc 0 0 m m'.
Proof. intros H a Ha _. exact (H a Ha). Qed.

Lemma kept_stack (L : list (Z * Z)) (F : list (Z * nat)) (spc d n : Z) (m m' : word -> option byte) :
  rt_pres_ex L F spc d n m m' -> 0 <= spc -> sp0 + 16 <= USTACK_TOP -> (forall a, spc <= a < sp0 -> ~ (d <= a < d + n)) ->
  forall a, spc <= a < sp0 -> m' (wa a) = m (wa a).
Proof.
  intros H H0 Htop Hd a Ha. apply H; rewrite wa_unsigned by (unfold USTACK_TOP in *; lia); [left; unfold USTACK_TOP in *; lia | exact (Hd a Ha)].
Qed.

Lemma kept_caller (X : list (Z * Z)) (F : list (Z * nat)) (spc d n : Z) (m m' : word -> option byte) :
  rt_pres_ex (X ++ CL) F spc d n m m' -> spc <= sp0 -> (forall a, caller_mem CL sp0 xp a -> ~ (d <= a < d + n)) ->
  forall a : word, caller_mem CL sp0 xp (bv_unsigned a) -> m' a = m a.
Proof. intros H Hsp Hd a Hc. apply H; [exact (caller_aclient X F spc _ Hsp Hc) | exact (Hd _ Hc)]. Qed.

(* [comment removed for export] *)
Lemma FMem_after_call (g : ghost RT) (rho : valuation) (cd : xcd) (M M' : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (Σ' : rts RT) (spc : Z) :
  FMemA g rho cd M nx m ->
  ART RT Σ' m' -> mem_inv ctasegs m' -> stk ctasegs m' lo spc ->
  (forall a, spc <= a < sp0 -> m' (wa a) = m (wa a)) -> (forall a : word, caller_mem CL sp0 xp (bv_unsigned a) -> m' a = m a) ->
  rt_live RT Σ' = rt_live RT (g_S RT g) -> rt_frames RT Σ' = rt_frames RT (g_S RT g) -> rt_sp0 RT Σ' = rt_sp0 RT (g_S RT g) ->
  rt_credit RT (g_S RT g) - 1 <= rt_credit RT Σ' ->
  same_dirs M M' -> ro_same M M' -> B0A <= spc <= sp0 ->
  FMemA (GH RT Σ') rho (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd)) M' nx m'.
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr & Hsp0a)
         HART' MI' Hstk' Hk1 Hk2 El Ef Es Ecr Hd Hro Hspc.
  unfold FMem. cbv zeta. cbn [g_S x_blocks x_frames x_calls x_nb].
  split; [rewrite El, (blk_list_same_dirs rho M M' _ Hd); exact Hlive|]. split; [rewrite Ef, (frm_list_same_dirs rho M M' _ Hd); exact Hfr|]. split; [exact Hnd|]. split; [exact Htl|].
  split; [exact (same_dirs_tags M M' nx Hd Htags)|]. split; [exact Hnx0|]. split; [exact Hnx|].
  split; [exact (same_dirs_class r xp XP_ro M M' _ _ Hd Hro Hcls)|]. split; [exact (same_dirs_link M M' _ _ Hd Hlink)|]. split; [exact Hrho|].
  split; [exact HART'|]. split; [exact MI'|].
  split.
  { destruct (stk_split ctasegs m lo spc sp0 Hstk ltac:(unfold B0 in *; lia)) as [_ Hup].
    apply (stk_merge ctasegs m' lo spc sp0 Hstk'); [|unfold B0 in *; lia].
    destruct Hup as (U1 & U2 & U3). split; [exact U1|]. split; [exact U2|]. intros a Ha. destruct (U3 a Ha) as [Hw Hb].
    destruct (same_byte_kept m m' _ (Hk1 a Ha)) as [E1 E2]. split; [exact (E2 Hw) | rewrite E1; exact Hb]. }
  split; [rewrite Es; auto|]. split; [split; [assumption | repeat split; lia]|].      (* [comment removed for export] *) split; [|rewrite Es; exact Hsp0a].
  intros a Hc. rewrite <- (Hagr a Hc). exact (Hk2 a Hc).
Qed.

(* [comment removed for export] *)
Lemma regions_after_call (g : ghost RT) (rho rho2 : valuation) (cd : xcd) (M : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (Σ' : rts RT) (L : list (Z * Z)) (o : w64) (rgs : region) (tx td : int) (d n : Z) :
  FMemA g rho cd M nx m -> Rmem ctasegs rho2 M m -> agree_below nx rho rho2 ->
  mget M T_STK = Some rgs -> rg_abs rgs = None -> rg_dflt rgs = DUnk -> rg_wr rgs = true ->
  to_Z (wl o) mod 16 = 0 -> to_Z (wl o) <= to_Z (rg_size rgs) ->
  ART RT Σ' m' -> mem_inv ctasegs m' -> stk ctasegs m' lo (B0A + to_Z (wl o)) ->
  rt_pres_ex L (rt_frames RT (g_S RT g)) (B0A + to_Z (wl o)) d n m m' -> rt_sp0 RT Σ' = rt_sp0 RT (g_S RT g) ->
  (forall b, In b (x_blocks cd) -> b <> tx -> In (rho b, rsize M b) L /\ In (rho b, rsize M b) (rt_live RT Σ')) ->
  (forall e, In e CL -> In e L /\ In e (rt_live RT Σ')) ->
  to_Z tx < 1000000 -> td <> T_STK ->
  (forall t3 rg3, mget M t3 = Some rg3 -> t3 <> td -> forall i, 0 <= i < to_Z (rg_size rg3) -> ~ (d <= rbase rho2 t3 rg3 + i < d + n)) ->
  forall t3 rg3, mget (mset M T_STK (drop_below rgs (wl o))) t3 = Some rg3 -> t3 <> tx -> t3 <> sh_tag tx -> t3 <> td ->
    region_ok ctasegs rho2 t3 rg3 m'.
Proof.
  intros HF HRm2 Hag Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' Hpres Es HL HLc Htx Htd Hdn t3 rg3 G3 N1 N2 N3.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & Hcnt & Hagr).
  destruct (stk_class g rho cd M nx m rgs HF Egs Eabs) as [Esz _].
  assert (E2 : rho2 T_STK = B0A) by (rewrite (Hag T_STK) by (change (to_Z T_STK) with 2; change (to_Z NEXT0) with 32 in Hnx0; lia); exact Hrs).
  destruct (mget_mset_cases M T_STK t3 _ rg3 (mget_lt M T_STK rgs Egs) G3) as [[-> ->]|[Hne G3']].
  - apply (stack_after_call rho2 rgs (wl o) m m' (proj1 HRm2 T_STK rgs Egs) Eabs Edf Esz E2); try assumption.
    + replace (to_Z (wl o)) with (0 + (2 * (to_Z (wl o) / 16)) * 8) by (pose proof (Z.div_mod (to_Z (wl o)) 16 ltac:(lia)); lia). rewrite Z.mod_add by lia. reflexivity.
    + pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (to_Z_bounded (wl o)) as Bo.
      apply (kept_stack L (rt_frames RT (g_S RT g)) (B0A + to_Z (wl o)) d n m m' Hpres); [unfold B0, SEGTOP_A, STACK_WIN in *; lia | exact Hl3 |].
      intros a Ha. pose proof (Hdn T_STK rgs Egs (not_eq_sym Htd) (a - B0A)) as X. unfold rbase in X. rewrite Eabs, E2, Esz in X.
      replace (B0A + (a - B0A)) with a in X by lia. apply X. unfold B0 in *. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1). lia.
  - apply (region_after_rt g rho rho2 cd M nx m m' Σ' L (B0A + to_Z (wl o)) tx d n HF HRm2 Hag HART' MI' Hpres Es HL HLc t3 rg3 G3' Hne N1 N2 Htx).
    exact (Hdn t3 rg3 G3' N3).
Qed.

(* [comment removed for export] *)
Lemma FMem_update (g : ghost RT) (rho rho' : valuation) (cd : xcd) (M M' : HxMem.mem) (nx nx' : int) (m m' : word -> option byte)
    (Σ' : rts RT) (spc : Z) (bl' fl' : list int) (calls' nb' : Z) :
  FMemA g rho cd M nx m -> agree_below nx rho rho' -> to_Z nx <= to_Z nx' -> to_Z nx' < 1000000 ->
  ART RT Σ' m' -> mem_inv ctasegs m' -> stk ctasegs m' lo spc -> B0A <= spc <= sp0 ->
  (forall a, spc <= a < sp0 -> m' (wa a) = m (wa a)) -> (forall a : word, caller_mem CL sp0 xp (bv_unsigned a) -> m' a = m a) ->
  rt_sp0 RT Σ' = rt_sp0 RT (g_S RT g) ->
  rt_live RT Σ' = blk_list rho' M' bl' ++ CL -> rt_frames RT Σ' = frm_list rho' M' fl' ->
  List.NoDup (bl' ++ fl') ->
  (forall t, In t (bl' ++ fl') -> tag_even t = true /\ to_Z NEXT0 <= to_Z t /\ to_Z t + 1 < to_Z nx') ->
  (forall t rg, mget M' t = Some rg -> to_Z t < to_Z nx') ->
  region_class r xp M' bl' fl' -> live_link M' bl' fl' ->
  (forall t, In t (bl' ++ fl') -> rho' (sh_tag t) = shad (rho' t) /\ rho' t mod 8 = 0) ->
  Z.of_nat (length bl') = nb' -> 0 <= calls' -> cr0 - calls' <= rt_credit RT Σ' ->
  FMemA (GH RT Σ') rho' (XCD bl' fl' calls' nb') M' nx' m'.
Proof.
  intros (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hr0 & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr & Hsp0a)
         Hag Hnx1 Hnx2 HART' MI' Hstk' Hspc Hk1 Hk2 Es El Ef Hnd' Htl' Htags' Hcls' Hlink' Hrsh' Enb Hcalls Hcr.
  unfold FMem. cbv zeta. cbn [g_S x_blocks x_frames x_calls x_nb]. change (to_Z NEXT0) with 32 in *.
  split; [exact El|]. split; [exact Ef|]. split; [exact Hnd'|]. split; [exact Htl'|]. split; [exact Htags'|]. split; [change (to_Z NEXT0) with 32; lia|]. split; [exact Hnx2|].
  split; [exact Hcls'|]. split; [exact Hlink'|].
  split.
  { rewrite (Hag T_STK) by (change (to_Z T_STK) with 2; lia). rewrite (Hag (sh_tag T_STK)) by (change (to_Z (sh_tag T_STK)) with 3; lia).
    rewrite (Hag T_S0) by (change (to_Z T_S0) with 19; lia). auto. }
  split; [exact HART'|]. split; [exact MI'|].
  split.
  { destruct (stk_split ctasegs m lo spc sp0 Hstk ltac:(unfold B0 in *; lia)) as [_ Hup].
    apply (stk_merge ctasegs m' lo spc sp0 Hstk'); [|unfold B0 in *; lia].
    destruct Hup as (U1 & U2 & U3). split; [exact U1|]. split; [exact U2|]. intros a Ha. destruct (U3 a Ha) as [Hw Hb].
    destruct (same_byte_kept m m' _ (Hk1 a Ha)) as [E1 E2]. split; [exact (E2 Hw) | rewrite E1; exact Hb]. }
  split; [rewrite Es; auto|]. split; [split; [assumption | repeat split; lia]|].      (* [comment removed for export] *) split; [intros a Hc; rewrite <- (Hagr a Hc); exact (Hk2 a Hc)|].
  destruct Hsp0a as [Hsp0a Hcb]. split; [rewrite Es; exact Hsp0a|].
  intros t n w Hin. destruct (Hcb t n w Hin) as (C1 & C2 & C3 & C4 & (C5 & C6) & C7 & C8 & C9).
  assert (Hst : to_Z (sh_tag t) = to_Z t + 1) by (apply sh_tag_Z; lia).
  rewrite (Hag t) by lia. rewrite (Hag (sh_tag t)) by lia. repeat split; try assumption; lia.
Qed.

End Hooks.
