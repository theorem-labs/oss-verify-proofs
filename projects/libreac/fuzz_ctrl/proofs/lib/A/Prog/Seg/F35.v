(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths and module names changed; 717 of its 758 lines of code are new or changed and 110 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F31.v, with its module names, addresses and numbers changed; 595 of its 836 lines of code are new or changed and 517 lines of the source are left out. *)
(* Segment F35 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x82888-0x82898, inside the row_of_block loop
   (plan-asan section 2 row F35, call BCMP@0x82898).
   v1.9.0: moved onto a Theorem Labs lane's v1.9 cut bundle (a working branch, 2026-10-28); the commit messages name the
   builds that check it and the FACTS sha of each.

     0x82888  beqz a0,828a0   -- a0 is declaration_of's result for row i.  F34 calls declaration_of on the row at
                                 s4 = T + 296 i with the 32-byte row slot at s9 = fr + 64, and every catalogue row
                                 satisfies decl_ok (declaration_of_rows), so a0 = 1 and the branch is NOT taken.
                                 The cut at 0x828a0 is the second exit of this segment; it is reached only by that
                                 branch, so the segment proves it vacuously (the ubsan twin W03 does the same).
     0x8288c  li a2,32
     0x82890  mv a0,s6        -- s6 = phi + 18, the 32 block bytes of turn j (the row path needs len >= 50).
     0x82894  mv a1,s9        -- s9 = fr + 64, the row slot declaration_of filled with decl_i i.
     0x82898  jal wrapper_bcmp -> 0x8289c with a0 = memcmp_model blk (decl_i i) 32.

   The wrapper compares the 32 bytes at a0 with the 32 bytes at a1 and checks that both ranges are marked usable in
   the shadow map; both are addressable (the block from HB(phi, len) with len >= 50, the row slot from the cut), so
   the error path is not reached.  It writes only its own [sp - 4560, sp) stack window.

   Cuts: every cut is SlotInv.v's official one (entry Inv_A82888_at, exits Inv_A8289c_at and Inv_A828a0_at, with
   the bundles FLSI, RL (whose tail is FLSX) and LT); this file defines no cut and no bundle.  The wrapper's
   contract is the Section Hypothesis HBC; it asks mem_inv of the caller's memory, which no cut carries (FRA keeps
   ro_agree only), so the run is made on the normalized memory (MemNorm.evt_normalize, f35_call).  FRA moves across
   the run by Tac_b5.sl_callee_keep (the run writes only the wrapper's window), ENT by Tac_slot.ent_store and
   ent_mat, and FLSI / FLSX / LK / LT because the spill area, the frame, the block and the harness block are apart
   from that window. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 is the plain one here; the slot's
   cuts (ENT reads the FP state) are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* v1.9.0 values: bcmp_wrap_c.v / memcmp_c.v (a Theorem Labs lane 3eade53eef2) and AsanRT.v's RT_REALS / RT_GOT_CF / RT_CF
   (a Theorem Labs lane 48004cf7bfc). *)
Local Definition BCMP : Z := 0x97b0c.
Local Definition REAL_BCMP : Z := 0xa17f0.
Local Definition REAL_MEMCMP : Z := 0xa17e8.
Local Definition GOT_CF : Z := 0x9fac0.
Local Definition CF : Z := 0x13a3a8.
Local Definition MEMCMP : Z := 0x97bdc.
Local Notation memcmp_model := SF.memcmp_model.

(* ---------------- model facts of turn j (image-A twins of the ubsan Tac_b8 lemmas) ---------------- *)

Lemma f35_bz_range : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f35_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (f35_bz_range (nthb inp (Z.to_nat c))). pose proof (f35_bz_range (nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma f35_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0, nlen. lia.
  - change (fc inp (S j)) with (f_next inp (fc inp j)). pose proof (f35_fL_nonneg inp (fc inp j)).
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f35_t_facts : forall inp j,
  0 <= t_c inp j <= nlen inp /\ t_left inp j = nlen inp - t_c inp j /\
  0 <= t_h inp j <= t_left inp j /\ 0 <= t_len inp j <= t_left inp j - t_h inp j /\
  t_body inp j = t_c inp j + t_h inp j.
Proof.
  intros inp j. pose proof (f35_fc_range inp j) as R. pose proof (f35_fL_nonneg inp (fc inp j)) as L.
  unfold t_c, t_left, t_h, t_len, t_body. unfold f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f35_len_nonneg : forall inp j, 0 <= t_len inp j.
Proof. intros inp j. pose proof (f35_t_facts inp j) as (_ & _ & _ & (H & _) & _). exact H. Qed.

Lemma f35_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (f35_t_facts inp j) as (R & EL & (H1 & H2) & (H3 & H4) & EB).
  unfold t_phi, f_phi. rewrite length_firstn, length_skipn.
  change (f_len inp (fc inp j)) with (t_len inp j). change (f_body inp (fc inp j)) with (t_body inp j).
  unfold nlen in *. lia.
Qed.

Lemma f35_phi_lenZ : forall inp j, Z.of_nat (length (t_phi inp j)) = t_len inp j.
Proof. intros inp j. rewrite f35_phi_length. apply Z2Nat.id. apply f35_len_nonneg. Qed.

Lemma f35_k_big : forall inp j, t_k inp j <> 0 -> 50 <= t_len inp j.
Proof.
  intros inp j K. destruct (Z_le_gt_dec 50 (t_len inp j)) as [H|H]; [exact H|].
  exfalso. apply K. unfold t_k. apply ctrlparse_none. intros (HC & _ & _). lia.
Qed.

(* The row path needs kind 9, and a non-zero kind needs a frame of at least 50 bytes. *)
Lemma f35_rowsel_big : forall inp j, t_rowsel inp j = true -> 50 <= t_len inp j.
Proof.
  intros inp j H. unfold t_rowsel in H. apply andb_prop in H as [H _]. apply andb_prop in H as [Hk _].
  apply Z.eqb_eq in Hk. apply f35_k_big. rewrite Hk. discriminate.
Qed.

Lemma f35_fr50_firstn : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app.
  replace (50 - length bs)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

(* A window that ends inside a prefix does not see the prefix. *)
Lemma f35_fsf : forall (A : Type) (l : list A) (a b c : nat), (a + b <= c)%nat ->
  firstn b (skipn a (firstn c l)) = firstn b (skipn a l).
Proof.
  intros A l; induction l as [|x l IH]; intros a b c H.
  - rewrite !firstn_nil, !skipn_nil, !firstn_nil. reflexivity.
  - destruct c as [|c].
    + assert (Ha : a = 0%nat) by lia. assert (Hb : b = 0%nat) by lia. subst a b. reflexivity.
    + destruct a as [|a].
      * destruct b as [|b]; [reflexivity|].
        cbn [firstn skipn]. f_equal. exact (IH 0%nat b c ltac:(lia)).
      * cbn [firstn skipn]. apply IH. lia.
Qed.

(* The 32 block bytes of turn j are the 32 bytes of Phi at offset 18 when len >= 50. *)
Lemma f35_blk : forall inp j, 50 <= t_len inp j -> t_blk inp j = firstn 32 (skipn 18 (t_phi inp j)).
Proof.
  intros inp j H. unfold t_blk, bsl, t_g.
  rewrite f35_fr50_firstn by (rewrite f35_phi_length; lia).
  change (Z.to_nat 18) with 18%nat. change (Z.to_nat 32) with 32%nat.
  apply f35_fsf. lia.
Qed.

Lemma f35_decl_len : forall i, (i < 11)%nat -> length (decl_i (Z.of_nat i)) = 32%nat.
Proof.
  intros i Hi.
  assert (H : forallb (fun k => Nat.eqb (length (decl_i (Z.of_nat k))) 32) (seq 0 11) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Nat.eqb_eq. exact (H i ltac:(apply in_seq; lia)).
Qed.

Lemma f35_byte_eq : forall a b : byte, bv_unsigned a = bv_unsigned b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.

Lemma f35_mm_spec : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. inversion H. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|]. cbn in Hl, Hr, H.
    pose proof (f35_bz_range a) as Ra. pose proof (f35_bz_range b) as Rb. unfold bz in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) H) as [I1 I2]. split; [|exact I2].
      apply f35_byte_eq in E. subst b. split.
      * intros Hv. f_equal. apply I1. exact Hv.
      * intros Hq. apply I1. injection Hq as Hq. exact Hq.
    + inversion H; subst v. split; [|lia]. split; [lia|]. intros Hq. injection Hq as Hab _. subst b. contradiction.
Qed.

Lemma f35_lit0 : forall v, -256 < v < 256 -> (Z_to_bv 64 v = Z_to_bv 64 0 <-> v = 0).
Proof.
  intros v Hv. split; intros E; [|subst; reflexivity].
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. change (0 mod 2 ^ 64) with 0 in E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma f35_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* A spilled word at s1 + off read at the FRA spill base A (the existential base of `spill` is A). *)
Lemma f35_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 312 <= 2 ^ 64 -> 0 <= off <= 304 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal bv_unsigned) in HA'. rewrite !unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* ---------------- the official bundles across a run that misses the spill area and their bytes ----------------
   (the re-cut bundle transports of F32, a working branch b8d1083b061, stated with f35_spill's spill base) *)

Lemma f35_spill_mem : forall regs regs' m m' W off v A,
  rg regs 9 A -> 0 <= A -> A + 312 <= 2 ^ 64 -> 0 <= off <= 304 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x < A + 312 -> outside W x) ->
  spill regs m off v -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A HA H0 H1 Hoff E MU HW Hs.
  pose proof (f35_spill regs m off v A Hs HA H0 H1 Hoff) as Hq.
  exists A. split; [unfold rg in *; rewrite E; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply HW. lia.
Qed.

(* v1.9: PRO's [A + 200] is [A + 208] and PRO gains [A + 32] = fr + 2880 as its 16th conjunct; FLC's slots are
   renumbered (208 / 64 / 72 / 80 / 56 / 48 -> 192 / 80 / 88 / 96 / 72 / 64) and FLC gains [A + 56] = fr + 2889 and
   [A + 48] = fr + 2890 as its 13th and 14th, all spills. *)
Lemma f35_flsi_mem : forall g j fr regs regs' m m' W A,
  rg regs 9 A -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x < A + 312 -> outside W x) ->
  addressable m' (fr + 2624) 6 -> stk rsegs m' fr (fr + 3136) -> addressable m' (fr + 2691) 17 -> f1_IN g m' ->
  addressable m' (fragb fr) 72 -> addressable m' (fr + 2688) 38 ->
  FLSI g j fr regs m -> FLSI g j fr regs' m'.
Proof.
  intros g j fr regs regs' m m' W A HA H0 H1 E MU HW Ha' Hs' Ha17' HIN' Hfb' H38'
    (((S1 & S2 & S4 & S5 & S6 & S7 & S8 & S248p & _ & _ & _ & P184 & P256 & P264 & P272 & P32) & S3 & _ & S144 & _) &
     S216 & S224 & S248 & _ &
     (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & _ & _ & C72 & C64 & C56 & C48)).
  pose proof HIN' as (Hin0' & Hinad' & Hinb').
  pose proof (fun off v (Hoff : 0 <= off <= 304) => f35_spill_mem regs regs' m m' W off v A HA H0 H1 Hoff E MU HW)
    as T.
  unfold FLSI, FLSH, PRO, FLC.
  split.
  { split.
    { split; [exact (T 40 _ ltac:(lia) S1)|]. split; [exact (T 120 _ ltac:(lia) S2)|].
      split; [exact (T 136 _ ltac:(lia) S4)|]. split; [exact (T 160 _ ltac:(lia) S5)|].
      split; [exact (T 168 _ ltac:(lia) S6)|]. split; [exact (T 176 _ ltac:(lia) S7)|].
      split; [exact (T 208 _ ltac:(lia) S8)|]. split; [exact (T 248 _ ltac:(lia) S248p)|].
      split; [exact Ha'|]. split; [exact Hinb'|].
      split; [intros Hn; split; [exact (Hin0' Hn) | exact Hinad']|].
      split; [exact (T 184 _ ltac:(lia) P184)|]. split; [exact (T 256 _ ltac:(lia) P256)|].
      split; [exact (T 264 _ ltac:(lia) P264)|].
      split; [exact (T 272 _ ltac:(lia) P272) | exact (T 32 _ ltac:(lia) P32)]. }
    split; [exact (T 128 _ ltac:(lia) S3)|]. split; [exact Hs'|].
    split; [exact (T 144 _ ltac:(lia) S144) | exact Ha17']. }
  split; [exact (T 216 _ ltac:(lia) S216)|]. split; [exact (T 224 _ ltac:(lia) S224)|].
  split; [exact (T 248 _ ltac:(lia) S248)|]. split; [exact HIN'|].
  split; [exact (T 256 _ ltac:(lia) C256)|]. split; [exact (T 184 _ ltac:(lia) C184)|].
  split; [exact (T 192 _ ltac:(lia) C192)|]. split; [exact (T 80 _ ltac:(lia) C80)|].
  split; [exact (T 88 _ ltac:(lia) C88)|]. split; [exact (T 96 _ ltac:(lia) C96)|].
  split; [exact (T 272 _ ltac:(lia) C272)|]. split; [exact (T 264 _ ltac:(lia) C264)|].
  split; [exact Hfb'|]. split; [exact H38'|].
  split; [exact (T 72 _ ltac:(lia) C72)|]. split; [exact (T 64 _ ltac:(lia) C64)|].
  split; [exact (T 56 _ ltac:(lia) C56) | exact (T 48 _ ltac:(lia) C48)].
Qed.

Lemma f35_flsx_mem : forall g j phi fr regs regs' m m' W A,
  rg regs 9 A -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  munch W m m' -> (forall x, A <= x < A + 312 -> outside W x) ->
  (forall x, phi <= x < phi + flen g j -> outside W x) ->
  FLSI g j fr regs' m' -> FLSX g j phi fr regs m -> FLSX g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W A HA H0 H1 E9 E18 E22 E23 E25 MU HW HWp HI'
    (_ & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  pose proof (f35_phi_length (g_in g) j) as Lp.
  unfold FLSX.
  split; [exact HI'|].
  split; [unfold rg in *; rewrite E18; exact H18|]. split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E23; exact H23|]. split; [unfold rg in *; rewrite E25; exact H25|].
  split.
  { intros Hl. destruct (Hrec Hl) as (Hp0 & Hp1 & Hg & Hph & Hpl).
    assert (Lg : length (t_g (g_in g) j) = 50%nat).
    { unfold flen in Hl. unfold t_g. rewrite f35_fr50_firstn by (rewrite f35_phi_length; lia).
      rewrite length_firstn, f35_phi_length. lia. }
    split; [exact Hp0|]. split; [exact Hp1|].
    split; [eapply fl_bytes; [exact Hg | exact MU |]; rewrite Lg; intros x Hx; apply HWp; lia|].
    split; [eapply fl_bytes; [exact Hph | exact MU |]; rewrite Lp; intros x Hx; apply HWp; unfold flen in *; lia|].
    exact Hpl. }
  split; [exact (f35_spill_mem regs regs' m m' W 152 _ A HA H0 H1 ltac:(lia) E9 MU HW H152)|].
  exact (f35_spill_mem regs regs' m m' W 280 _ A HA H0 H1 ltac:(lia) E9 MU HW H280).
Qed.

(* The frame records LT names (IFS g fr (S j)): the identity record at fr + 2688 keeps its 38 bytes (F32's
   f32_tID_length) and the fragment state at fr + 2768 stays within 72 bytes (F37's f37_FG_len), so both lie in
   [fr + 2688, fr + 2840), inside the frame. *)
Lemma f35_rp_id_len : forall idb len g, length idb = ID_SIZE -> length (rp_id idb len g) = ID_SIZE.
Proof.
  intros idb len g H. unfold rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply ING_length; exact H | exact H].
Qed.

Lemma f35_fg_id_len : forall idb len st g, length idb = ID_SIZE -> length (fg_id idb len st g) = ID_SIZE.
Proof.
  intros idb len st g H. unfold fg_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply ING_length; exact H | exact H].
Qed.

Lemma f35_tID_length : forall inp j, length (t_ID inp j) = ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  cbn [fst_at]. unfold turn. cbv beta zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; apply f35_fg_id_len, f35_rp_id_len; exact IH.
Qed.

Lemma f35_bat_nn : forall bs i, 0 <= bat bs i.
Proof. intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. Qed.

Lemma f35_clear_len : forall st, (length st <= 72)%nat -> (length (fg_clear st) <= 72)%nat.
Proof.
  intros st H. unfold fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia.
Qed.

Lemma f35_FG_step : forall len st g, (length st <= 72)%nat -> (length (fg_st len st g) <= 72)%nat.
Proof.
  intros len st g H. unfold fg_st, fcls, fg_class, fg_next.
  destruct (fg_fr len g) eqn:Efr; cbn [negb orb Z.eqb]; [|exact H].
  pose proof (f35_bat_nn g 26) as Hn0. pose proof (f35_bat_nn st 7) as Hl0.
  destruct (bat g 19 =? 1); cbn [negb].
  - assert (Hn : fg_n g <= 22).
    { unfold fg_fr in Efr. apply andb_prop in Efr as (Ea & _). apply andb_prop in Ea as (_ & E22).
      apply Z.leb_le in E22. exact E22. }
    unfold fg_first, fg_body, bsl, fg_n in *. rewrite !length_app, !length_firstn, !length_skipn.
    cbn [length]. lia.
  - destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|apply f35_clear_len; exact H].
    assert (HT : fg_T st g <= 64).
    { unfold fg_keep in Ek. apply andb_prop in Ek as (_ & ET). apply Z.leb_le in ET. exact ET. }
    destruct (fg_close st g); cbn [negb]; apply f35_clear_len;
      unfold fg_join, fg_body, bsl, fg_T, fg_lf, fg_n in *; rewrite !length_app, !length_firstn, !length_skipn;
      lia.
Qed.

Lemma f35_FG_len : forall inp j, (length (t_FG inp j) <= 72)%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; cbn [fst_at].
  - unfold fs0. cbn [fs_fg]. rewrite z72_length. lia.
  - unfold turn. cbv zeta.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    cbn [fs_fg]; apply f35_FG_step; exact IH.
Qed.

(* v1.9 FSb: the body of the last FIRST fragment, at fr + 2880, is at most 23 bytes (block[9 ..] of a 50-byte
   frame record), so it lies in [fr + 2880, fr + 2915), the 35 addressable bytes FSb names. *)
Lemma f35_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  assert (HG : length (t_g inp j) = 50%nat).
  { unfold t_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. }
  cbn [fst_at]. unfold turn. cbv beta zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn, HG. lia.
Qed.

(* v1.9 FSb: [A + 104] / [A + 112] and the body bytes at fr + 2880 move with the run; their addressability is a
   premise on m', as FLC's ranges are in f35_flsi_mem. *)
Lemma f35_lt_mem : forall g fr j regs regs' m m' W A,
  rg regs 9 A -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x < A + 312 -> outside W x) ->
  (forall x, fr + 2688 <= x < fr + 2840 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x) -> addressable m' (fr + 2880) 35 ->
  LT g fr j regs m -> LT g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W A HA H0 H1 E MU HW HWr HWb Had'
    ((HID & Hidok) & (HFG & Hfgok) & (Q104 & Q112 & Qbody & _ & HFI)).
  pose proof (fun off v (Hoff : 0 <= off <= 304) => f35_spill_mem regs regs' m m' W off v A HA H0 H1 Hoff E MU HW)
    as T.
  pose proof (f35_tID_length (g_in g) (S j)) as LID. pose proof (f35_FG_len (g_in g) (S j)) as LFG.
  unfold ID_SIZE in LID.
  unfold LT, IFS, IDj, FGj, IDb, FGb, FSj, FSb.
  split.
  { split; [|exact Hidok]. unfold IDBe in *. eapply fl_bytes; [exact HID | exact MU |].
    rewrite LID. intros x Hx. apply HWr. lia. }
  split.
  { split; [|exact Hfgok]. unfold FGBe in *. eapply fl_bytes; [exact HFG | exact MU |].
    intros x Hx. apply HWr. lia. }
  split; [exact (T 104 _ ltac:(lia) Q104)|]. split; [exact (T 112 _ ltac:(lia) Q112)|].
  split.
  { eapply fl_bytes; [exact Qbody | exact MU |].
    pose proof (f35_fs_body_len (g_in g) (S j)) as LB. intros x Hx. apply HWb. lia. }
  split; [exact Had' | exact HFI].
Qed.

(* ---------------- the wrapper's run on the normalized memory ----------------
   The wrapper's contract asks mem_inv of the caller's memory; a cut carries only ro_agree (FRA, push 5b).  The
   run is made on the normalized memory (MemNorm.evt_normalize, as SlotInv.v says), and every premise and post
   fact moves across mem_rel: they read bytes through mrd (equal everywhere, mrd_rel) and the writability of bytes
   at or above GT = 0x5fe000 (no read-only byte is there, f35_ro_lo).  F36's bridge (a working branch). *)
Local Definition f35_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Local Lemma f35_rsegs_top : f35_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma f35_find_below : forall segs top x n s,
  f35_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f35_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f35_ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 0x5fe000.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (f35_find_below rsegs 0x5fe000 (bv_unsigned a) 1 s f35_rsegs_top E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

Lemma f35_ro_false : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity].
  pose proof (f35_ro_lo _ E) as L. rewrite wa_unsigned in L by lia. lia.
Qed.

Lemma f35_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi R Hlo.
  split; intros (H0 & H1 & H); (split; [exact H0|]); (split; [exact H1|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb);
    (assert (E : ro_addr rsegs (wa a) = false) by (apply f35_ro_false; lia)).
  - split; [rewrite (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite <- (mrd_rel rsegs m m0 _ R). exact Hb.
  - split; [rewrite <- (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite (mrd_rel rsegs m m0 _ R). exact Hb.
Qed.

Lemma f35_srw_rel : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 R. unfold shadow_rw.
  split; intros H a Ha; destruct (H a Ha) as (Hw & b & Hb);
    (assert (E : ro_addr rsegs (wa a) = false)
       by (apply f35_ro_false; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha;
           lia)).
  - split; [rewrite (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite <- (mrd_rel rsegs m m0 _ R). exact Hb.
  - split; [rewrite <- (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite (mrd_rel rsegs m m0 _ R). exact Hb.
Qed.

Lemma f35_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n R.
  assert (MR : forall a, mrd rsegs m a = mrd rsegs m0 a) by (intros a; exact (mrd_rel rsegs m m0 a R)).
  unfold addressable, addr_byte. setoid_rewrite MR. reflexivity.
Qed.

Lemma f35_cells_rel : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs R)).
  unfold asan_cells. setoid_rewrite BR. reflexivity.
Qed.

Section F35.
Context {fx : AYK.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HBC : BW.bcmp_wrap_contract.

(* ===================== the machine run ===================== *)

(* 0x82888 with a0 = 1: beqz is not taken; the three argument instructions, then the bcmp wrapper on the 32 bytes
   at L = phi + 18 and R = fr + 64. *)
Lemma f35_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (L R : Z) (ls rs : list byte) (v lo : Z),
    a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 L -> s9 = Z_to_bv 64 R ->
    0 <= L -> L + 32 < 2 ^ 64 -> 0 <= R -> R + 32 < 2 ^ 64 ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some v ->
    mem_inv rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BW.BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8289c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BW.BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m L R ls rs v lo -> -> -> HL0 HL1 HR0 HR1 HBL HBR Hmm HMI HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  (* 0x82888 beqz a0 (a0 = 1): not taken *)
  step. try if_false.
  (* 0x8288c li a2,32; 0x82890 mv a0,s6; 0x82894 mv a1,s9; 0x82898 jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HBC as HB. unfold BW.bcmp_wrap_contract in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
  assert (EL0 : bv_unsigned (Z_to_bv 64 (L + 0)) = L) by (rewrite Z.add_0_r; apply unsigned_lit; lia).
  assert (ER0 : bv_unsigned (Z_to_bv 64 (R + 0)) = R) by (rewrite Z.add_0_r; apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply HB with (ls := ls) (rs := rs) (v := v) (lo := lo).
    all: rewrite ?EL, ?ER, ?E32, ?EL0, ?ER0.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 32) with 32%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL32.
    - right; exact HaR32.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  apply evt_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* The wrapper's run from a memory that agrees with the image on its read-only bytes (a cut carries ro_agree, not
   mem_inv): f35_evt run on the normalized memory, with every premise and post fact moved across mem_rel (F36's
   f36_call_norm). *)
Lemma f35_call :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (L R : Z) (ls rs : list byte) (v lo : Z),
    a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 L -> s9 = Z_to_bv 64 R ->
    0 <= L -> L + 32 < 2 ^ 64 -> 0 <= R -> R + 32 < 2 ^ 64 ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some v ->
    ro_agree rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BW.BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8289c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BW.BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m L R ls rs v lo E0 E6 E9 HL0 HL1 HR0 HR1 HBL HBR Hmm HRO HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  pose proof (mem_rel_normalize rsegs m HRO) as Rn.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m (normalize rsegs m) a bs Rn)).
  assert (Hlo : 0x5fe000 <= lo) by (unfold HIGHMEM_BEG in Hlo2; lia).
  eapply LE.evt_mono.
  { eapply (evt_normalize rsegs _ _ Fr _ fc None m (seg_rom rsegs) wx_apart_asan HRO).
    apply (f35_evt ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             Fr fc (normalize rsegs m) L R ls rs v lo E0 E6 E9 HL0 HL1 HR0 HR1).
    - apply BR. exact HBL.
    - apply BR. exact HBR.
    - exact Hmm.
    - exact (mem_inv_normalize rsegs m).
    - apply (proj1 (f35_addr_rel m _ _ _ Rn)). exact HADL.
    - apply (proj1 (f35_addr_rel m _ _ _ Rn)). exact HADR.
    - exact HaL32.
    - exact HaR32.
    - exact HaL7.
    - exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - apply (proj1 (f35_stk_rel m _ _ _ Rn Hlo)). exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - apply (proj1 (f35_cells_rel m _ Rn)). exact HAC.
    - apply (proj1 (f35_srw_rel m _ Rn)). exact HSW.
    - apply BR. exact HRB.
    - apply BR. exact HRM.
    - apply BR. exact HGC.
    - apply BR. exact HC254.
    - apply BR. exact HC255. }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0' &
                  E & MU & WM & _ & ST & _ & _).
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' Rn RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' Rn RM SAME WM)|].
  split; [exact (ro_agree_same rsegs m m' HRO SAME)|].
  apply (proj2 (f35_stk_rel m' m0' _ _ RM Hlo)). exact ST.
Qed.

(* ===================== the segment lemma ===================== *)

Lemma seg_F35 : forall j i : nat,
  Hat2 B APIf ra (Inv_A8289c_at B APIf ra) j i -> Hat2 B APIf ra (Inv_A828a0_at B APIf ra) j i ->
  Hat2 B APIf ra (Inv_A82888_at B APIf ra) j i.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j i H7f0 _ g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & _ & HRL & H10 &
    Hrow & Hadr & HLT).
  subst c. rewrite SEGS.
  pose proof HRL as (Hi10 & Hr20 & Hr24 & Hprev & Hsel & HFLSX).
  pose proof HFLSX as (_ & Hr18 & Hr22 & Hr23 & Hr25 & Hrec & _ & _).
  pose proof HFLSI as
    (((_ & _ & _ & _ & _ & _ & _ & _ & Had2624 & _ & _ & _ & _ & _ & _) & _ & Hfstk & _ & Had2691) &
     _ & _ & _ & HIN & (_ & _ & _ & _ & _ & _ & _ & _ & Hadfg & Had2688 & _ & _)).
  pose proof HLK as (Hj255 & Hr21 & HOUR).
  (* this turn's frame is big: the row path needs kind 9; so the block's a_size is its length, s6 = phi + 18 and
     the guarded record part of FLSX holds *)
  assert (Hbig : 50 <= t_len (g_in g) j) by exact (f35_rowsel_big _ _ Hsel).
  assert (Hflen : flen g j = t_len (g_in g) j) by reflexivity.
  assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  rewrite Hsz in HFRA, HENT.
  assert (Hr22' : rg regs 22 (phi + 18)).
  { assert (Htb : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact Hbig).
    rewrite Htb in Hr22. exact Hr22. }
  destruct (Hrec ltac:(lia)) as (_ & _ & _ & Hphi & _).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel32 & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hplace & _ & _ & _).
  pose proof (fra_app B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HGTfr & Hfapp).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKK : BW.BCMP_WRAP_K = 4560) by reflexivity.
  assert (HHBc : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLEc : LOWMEM_END = 2147450880) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Esp : AC.aspZ regs = sp) by exact Haspz.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HA312 : A + 312 <= 2 ^ 64) by lia.
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGTfr; lia).
  assert (Hhi0 : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH).
  assert (Hfrhi : fr + 3136 <= APPMEM_END)
    by (pose proof (Hfapp (fr + 3135) ltac:(lia)) as Ha; unfold app_mem in Ha; lia).
  assert (Hspapp : sp <= APPMEM_END) by lia.
  (* the live block (phi, len) of this turn *)
  assert (Hin : In (phi, flen g j) (hb1 phi (flen g j) ++ g_H g))
    by (apply in_or_app; left; unfold hb1; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md phi (flen g j) HAH Hin)
    as (_ & Hph0 & Hphstk & Hphend & Hphin).
  assert (Hphsp : phi + flen g j <= AC.aspZ regs - FN_STACK)
    by (eapply Z.le_trans; [exact Hphstk | exact Hwlo]).
  assert (Hplen : length (t_phi (g_in g) j) = Z.to_nat (t_len (g_in g) j)) by apply f35_phi_length.
  assert (HplenZ : Z.of_nat (length (t_phi (g_in g) j)) = t_len (g_in g) j) by apply f35_phi_lenZ.
  (* the two operands of the compare *)
  assert (Hls : length (firstn 32 (skipn 18 (t_phi (g_in g) j))) = 32%nat)
    by (rewrite length_firstn, length_skipn, Hplen; lia).
  assert (Hrs : length (decl_i (Z.of_nat i)) = 32%nat) by (apply f35_decl_len; lia).
  assert (HLb : bytes_at rsegs mem (phi + 18) (firstn 32 (skipn 18 (t_phi (g_in g) j)))).
  { change (phi + 18) with (phi + Z.of_nat 18).
    apply f35_ba_sub; [exact Hphi | rewrite Hplen; lia]. }
  destruct (SF.memcmp_model_total (firstn 32 (skipn 18 (t_phi (g_in g) j))) (decl_i (Z.of_nat i)) 32
              ltac:(lia) ltac:(lia)) as (v & Hv).
  destruct (f35_mm_spec 32 _ _ v Hls Hrs Hv) as [Hiff Hvr].
  (* the runtime cells the wrapper reads *)
  pose proof HRT as HRT2.
  destruct HRT2 as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  assert (HGC : bytes_at rsegs mem GOT_CF (le8 (wa CF))) by exact HGOTCF.
  assert (HRBc : bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)))
    by (apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity).
  assert (HRMc : bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)))
    by (apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity).
  assert (HC254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1]).
  { pose proof (f35_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1]).
  { pose proof (f35_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  (* the wrapper's premises for L = phi + 18 and R = fr + 64 *)
  assert (HadL : addressable mem (phi + 18) 32).
  { apply (addressable_sub mem phi (AC.a_size (flen g j)) 18 32);
      [exact (proj2 HHB) | lia | lia | unfold AC.a_size; lia]. }
  assert (HaL32 : app_mem (phi + 18 + 32)).
  { destruct (Z_le_gt_dec (flen g j) 50) as [He|He].
    - replace (phi + 18 + 32) with (phi + flen g j) by lia.
      destruct Hphend as [H0|H0]; [lia | exact H0].
    - exact (proj1 (Hphin (phi + 18 + 32) ltac:(lia))). }
  assert (HaL7 : app_mem (phi + 18 + 7)) by exact (proj1 (Hphin (phi + 18 + 7) ltac:(lia))).
  assert (HaR32 : app_mem (fr + 64 + 32)) by (apply Hfapp; lia).
  assert (HaR7 : app_mem (fr + 64 + 7)) by (apply Hfapp; lia).
  assert (HdjL : phi + 18 + 32 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= phi + 18) by (left; lia).
  assert (HdjR : fr + 64 + 32 <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= fr + 64).
  { destruct (Hplace BW.BCMP_WRAP_K ltac:(lia)) as [H|H]; [left | right]; lia. }
  assert (HstkW : stk rsegs mem (AC.aspZ regs - BW.BCMP_WRAP_K) (AC.aspZ regs)).
  { destruct (stk_split rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs - BW.BCMP_WRAP_K) (AC.aspZ regs)
                Hwstk ltac:(lia)) as (_ & Hs). exact Hs. }
  assert (HloK : AC.aspZ regs - BW.BCMP_WRAP_K + BW.BCMP_WRAP_K <= AC.aspZ regs) by lia.
  assert (HloH : HIGHMEM_BEG <= AC.aspZ regs - BW.BCMP_WRAP_K) by lia.
  assert (HspA : AC.aspZ regs <= APPMEM_END) by lia.
  assert (HL0 : 0 <= phi + 18) by lia.
  assert (HL1 : phi + 18 + 32 < 2 ^ 64) by lia.
  assert (HR0 : 0 <= fr + 64) by lia.
  assert (HR1 : fr + 64 + 32 < 2 ^ 64) by lia.
  apply (@sl_run_lib fx regs (Z_to_bv 64 0x82888) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x8289c /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\ getr R0 10 = Z_to_bv 64 v /\
       munch [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] mem mem' /\
       wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (AC.aspZ regs - BW.BCMP_WRAP_K) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f35_call with (L := phi + 18) (R := fr + 64)
        (ls := firstn 32 (skipn 18 (t_phi (g_in g) j))) (rs := decl_i (Z.of_nat i)) (v := v)
        (lo := AC.aspZ regs - BW.BCMP_WRAP_K).
      - unfold rg in H10; exact H10.
      - unfold rg in Hr22'; exact Hr22'.
      - unfold rg in Hr25; exact Hr25.
      - exact HL0.
      - exact HL1.
      - exact HR0.
      - exact HR1.
      - exact HLb.
      - exact Hrow.
      - exact Hv.
      - exact Hro.
      - exact HadL.
      - exact Hadr.
      - exact HaL32.
      - exact HaR32.
      - exact HaL7.
      - exact HaR7.
      - exact HdjL.
      - exact HdjR.
      - exact HstkW.
      - exact HloK.
      - exact HloH.
      - exact HspA.
      - exact HAC0.
      - exact HSW0.
      - exact HRBc.
      - exact HRMc.
      - exact HGC.
      - exact HC254.
      - exact HC255. }
    { intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                  & E & MU & WM & RO' & ST').
      eexists _, (Z_to_bv 64 0x8289c), m'. split; [exact E|].
      split; [reflexivity|].
      do 15 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM|]. split; [exact RO' | exact ST']. }
  - intros R0 pc' mem' regs' md' (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 &
      E26 & E10 & MU & WM & HroM & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 v) by (rewrite Hreg; exact E10).
    (* the run writes only W = [sp - 4560, sp): the addresses below it (the block, the harness block), above it (the
       spill area at A >= sp) and the frame (fra_frame's placement) are outside W, and W is app memory *)
    assert (HWlo : forall x, x < AC.aspZ regs - BW.BCMP_WRAP_K ->
              outside [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] x).
    { intros x Hx. cbn [outside]. split; [|exact I]. lia. }
    assert (HWhi : forall x, AC.aspZ regs <= x ->
              outside [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] x).
    { intros x Hx. cbn [outside]. split; [|exact I]. lia. }
    assert (HWfr : forall x, fr <= x < fr + 3136 ->
              outside [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] x).
    { intros x Hx. cbn [outside]. split; [|exact I].
      destruct (Hplace BW.BCMP_WRAP_K ltac:(lia)) as [H|H]; lia. }
    assert (HWA_ : forall x, A <= x < A + 312 -> outside [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] x)
      by (intros x Hx; apply HWhi; lia).
    assert (Hallapp : all_app [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. lia. }
    (* the heap invariant, the runtime's ownership and the stack bounds across the window write *)
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite unsigned_lit by lia.
      cbn [outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (AC.a_laws_store _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as (HAH' & HOWN & HSTKeq & HSTKHIeq).
    (* FRA across the run and the lazy pages (Tac_b5.sl_callee_keep), ENT by Tac_slot.ent_store and ent_mat *)
    assert (Hhdr : AC.aspZ regs <= fr \/ fr + 24 <= AC.aspZ regs - BW.BCMP_WRAP_K)
      by (destruct (Hplace BW.BCMP_WRAP_K ltac:(lia)) as [H|H]; [right | left]; lia).
    assert (Hwin' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g))
      by exact (sl_win_stk B APIf ra g fr (hb1 phi (flen g j)) regs mem md mem' BW.BCMP_WRAP_K HFRA
                  ltac:(lia) MU WM ST').
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md')
      by exact (sl_callee_keep B APIf ra empty FF g fr (hb1 phi (flen g j)) regs regs' mem mem' md md'
                  BW.BCMP_WRAP_K HFRA MU WM Hwin' ltac:(lia) HspA Hhdr Hfrhi Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat).
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md
               [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] HENT HFRA MU).
      - intros x Hx.
        destruct (Z_le_gt_dec (AC.aspZ regs - BW.BCMP_WRAP_K) x) as [L1|L1];
          [destruct (Z_lt_ge_dec x (AC.aspZ regs)) as [L2|L2]|].
        + right; left. lia.
        + left. cbn [Frame.outside]. split; [lia | exact I].
        + left. cbn [Frame.outside]. split; [lia | exact I].
      - exact HSTKeq.
      - exact HSTKHIeq.
      - intros a _ Ho. exact (proj2 (HOWN a) Ho). }
    pose proof (ent_mat APIf g _ mem' md md' HENT' Hmat) as HENT''.
    (* the exit's bundles: the block, the frame's out[] bytes, the row slot, the spills and the harness block are
       apart from W, and W writes no shadow byte *)
    assert (MUu : Frame.munch [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] mem mem')
      by exact (proj1 (fr_munch_ul _ _ _) MU).
    assert (HHB' : HB mem' phi (flen g j)).
    { split; [exact (proj1 HHB)|]. eapply sl_addr_keep; [exact (proj2 HHB) | exact MUu | exact Hallapp]. }
    assert (Had2624' : addressable mem' (fr + 2624) 6)
      by (eapply sl_addr_keep; [exact Had2624 | exact MUu | exact Hallapp]).
    assert (Had2691' : addressable mem' (fr + 2691) 17)
      by (eapply sl_addr_keep; [exact Had2691 | exact MUu | exact Hallapp]).
    assert (Hadfg' : addressable mem' (fragb fr) 72)
      by (eapply sl_addr_keep; [exact Hadfg | exact MUu | exact Hallapp]).
    assert (Had2688' : addressable mem' (fr + 2688) 38)
      by (eapply sl_addr_keep; [exact Had2688 | exact MUu | exact Hallapp]).
    assert (Hfstk' : stk rsegs mem' fr (fr + 3136)).
    { eapply (stk_transport rsegs _ mem mem' fr (fr + 3136)); [exact Hfstk | exact MU | exact WM |].
      intros x Hx. left. apply HWfr. lia. }
    assert (HIN' : f1_IN g mem').
    { destruct HIN as (Hin0 & Hinad & Hinb). split; [exact Hin0|]. split.
      - eapply sl_addr_keep; [exact Hinad | exact MUu | exact Hallapp].
      - eapply fl_bytes; [exact Hinb | exact MU |]. intros x Hx.
        assert (Hn : 0 < g_n g) by (rewrite g_n_len; lia).
        destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md (g_p g) (g_n g) HAH
                    (in_or_app _ _ _ (or_intror (Hin0 Hn)))) as (_ & _ & HpEnd & _).
        rewrite g_n_len in HpEnd. apply HWlo. lia. }
    pose proof (f35_flsi_mem g j fr regs regs' mem mem' _ A Hr9 (proj1 HA64) HA312 Fr9 MU HWA_
                  Had2624' Hfstk' Had2691' HIN' Hadfg' Had2688' HFLSI) as HFLSI'.
    assert (HLK' : LK g fr j regs' mem').
    { split; [exact Hj255|]. split; [unfold rg in *; rewrite Fr21; exact Hr21|].
      unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
      intros x Hx. apply HWfr. unfold OUR in Hx. rewrite length_map, length_seq in Hx. lia. }
    assert (HWp : forall x, phi <= x < phi + flen g j ->
              outside [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] x)
      by (intros x Hx; apply HWlo; lia).
    pose proof (f35_flsx_mem g j phi fr regs regs' mem mem' _ A Hr9 (proj1 HA64) HA312 Fr9 Fr18 Fr22 Fr23 Fr25
                  MU HWA_ HWp HFLSI' HFLSX) as HFLSX'.
    assert (HRL' : RL g j i phi fr regs' mem').
    { split; [exact Hi10|].
      split; [unfold rg in *; rewrite Fr20; exact Hr20|].
      split; [unfold rg in *; rewrite Fr24; exact Hr24|].
      split; [exact Hprev|]. split; [exact Hsel | exact HFLSX']. }
    assert (Hiff' : getr regs' 10 = Z_to_bv 64 0 <-> t_blk (g_in g) j = decl_i (Z.of_nat i)).
    { rewrite Fr10, (f35_lit0 v Hvr), (f35_blk (g_in g) j Hbig). exact Hiff. }
    assert (Hrow' : bytes_at rsegs mem' (fr + 64) (decl_i (Z.of_nat i))).
    { eapply fl_bytes; [exact Hrow | exact MU |]. intros x Hx. apply HWfr. rewrite Hrs in Hx. lia. }
    assert (Hadr' : addressable mem' (fr + 64) 32)
      by (eapply sl_addr_keep; [exact Hadr | exact MUu | exact Hallapp]).
    assert (HWr : forall x, fr + 2688 <= x < fr + 2840 ->
              outside [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] x)
      by (intros x Hx; apply HWfr; lia).
    assert (HWb : forall x, fr + 2880 <= x < fr + 2915 ->
              outside [(AC.aspZ regs - BW.BCMP_WRAP_K, AC.aspZ regs)] x)
      by (intros x Hx; apply HWfr; lia).
    assert (Hadb' : addressable mem' (fr + 2880) 35).
    { destruct HLT as (_ & _ & (_ & _ & _ & Hadb & _)).
      eapply sl_addr_keep; [exact Hadb | exact MUu | exact Hallapp]. }
    pose proof (f35_lt_mem g fr j regs regs' mem mem' _ A Hr9 (proj1 HA64) HA312 Fr9 MU HWA_ HWr HWb Hadb' HLT)
      as HLT'.
    assert (HIexit : Inv_A8289c_at B APIf ra g j i
                       (mkCfg (mkst regs' (Z_to_bv 64 0x8289c) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS, Hsz. split; [reflexivity|].
      split; [exact HFRA''|]. split; [exact HENT''|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|]. split; [exact HFLSI'|].
      split; [exact HLK'|]. split; [exact HRL'|]. split; [exact Hiff'|].
      split; [exact Hrow'|]. split; [exact Hadr' | exact HLT']. }
    pose proof (H7f0 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F35.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
