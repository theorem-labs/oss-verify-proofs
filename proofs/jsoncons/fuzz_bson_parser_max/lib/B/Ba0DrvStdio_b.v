(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Definition PR_CELLS : list (Z * Z * Z) :=
  [(0x140918, 1, 1); (0x140919, 1, 1); (0x1d17bc, 1, 1); (0x13fc38, 8, 0x7fff8000);
   (0x139348, 8, 0x1273fc); (0x139350, 8, 0x121118); (0x1394c8, 8, 0x129900); (0x1394d0, 8, 0x129d04)].

(* [comment removed for export] *)
Definition EX_CELLS : list (Z * Z * Z) :=
  [(1282768, 8, 1282768); (1283280, 8, 1219844); (1295744, 8, 1); (1295824, 1, 0); (1299536, 4, 1); (1299696, 8, 0); (1307804, 1, 1); (1309752, 8, 2147450880); (1313048, 1, 1); (1906656, 8, 18446744073709551615); (1907424, 1, 0); (1299540, 1, 0)].      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DG_CELLS : list (Z * Z * Z) := [(1313048, 1, 1); (1313049, 1, 1); (1906620, 1, 1); (1309752, 8, 2147450880); (1282896, 8, 1184024); (1283272, 8, 1218816)].
(* [comment removed for export] *)
Definition DGS_CELLS : list (Z * Z * Z) :=
  [(1283192, 8, 1221668); (1282824, 8, 1218564); (0x13fc38, 8, 0x7fff8000); (0x140928, 8, 0); (0x140930, 8, 0); (0x140920, 8, 2 ^ 47 - 1); (0x1d1863, 1, 1); (0x140919, 1, 1); (0x1394c8, 8, 0x129900)].

(* [comment removed for export] *)
Lemma rdn_tr : forall (M M' : word -> option byte) a (n : nat) bs,
  rdn ASEGS M (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  rdn ASEGS M' (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M M' a n bs H Ha Hn HF. rewrite <- H. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HF. lia.
Qed.

(* [comment removed for export] *)
Lemma img_cell : forall (MV : word -> option byte) a (n : nat) bs,
  rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> MV (Z_to_bv 64 i) = None) ->
  rdn ASEGS MV (Z_to_bv 64 a) n = Some bs.
Proof. intros MV a n bs H Ha Hn HN. exact (rdn_tr (fun _ => None) MV a n bs H Ha Hn HN). Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Stdio.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hpr : incl PR_CELLS (asc_cells C).
  Variable M0 : word -> option byte.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Lemma vis_low : forall LB LK cr A M (model : Model) a, dinvA LB LK cr A M model -> 0 <= a < 0x696000 -> ahid A model (Z_to_bv 64 a) = false.
  Proof. intros LB LK cr A M model a D Ha. apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a (di_inv _ _ _ _ _ _ _ _ _ _ D)); lia. Qed.
  Lemma vis_stk : forall LB LK cr A M (model : Model) a, dinvA LB LK cr A M model -> usp - 8388608 <= a < 2 ^ 64 -> ahid A model (Z_to_bv 64 a) = false.
  Proof. intros LB LK cr A M model a D Ha. pose proof Hsp. apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a (di_inv _ _ _ _ _ _ _ _ _ _ D)); lia. Qed.

  (* [comment removed for export] *)
  Lemma pr_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) PR_CELLS ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
  Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aiob_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hpr _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x696000).
    { unfold PR_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u_small a) by lia. apply (vis_low _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stk_wr : forall vals ebs MV kn a n,
    know_ok ASEGS (Env (vals_ev vals) ebs) MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    usp - 8388608 <= a -> a + n <= usp ->
    forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true.
  Proof.
    intros vals ebs MV kn a n HK Hw P0 Ha Hn d k Hd Hk.
    pose proof (window_store_ok sp0 vals ebs MV kn (a + d - usp) k HK Hw P0 ltac:(lia) ltac:(lia)) as W.
    replace (usp + (a + d - usp)) with (a + d) in W by ring. exact W.
  Qed.
  Lemma stk_def : forall vals ebs MV kn a n,
    know_ok ASEGS (Env (vals_ev vals) ebs) MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    usp - 8388608 <= a -> a + n <= usp ->
    forall i, 0 <= i < n -> MV (Z_to_bv 64 (a + i)) <> None.
  Proof.
    intros vals ebs MV kn a n HK Hw P0 Ha Hn i Hi. pose proof Hsp.
    pose proof (stk_wr vals ebs MV kn a n HK Hw P0 Ha Hn i 1%nat ltac:(lia) ltac:(lia)) as W.
    apply (store_ok_defined sp0); [lia | exact W].
  Qed.

  (* [comment removed for export] *)
  Lemma stk_sh0 : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model ->
    (usp - 8388608) / 8 + 0x7fff8000 <= x <= (usp - 1) / 8 + 0x7fff8000 ->
    mrestrict (ahid A model) M (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof.
    intros LB LK cr A M model x D Hx. pose proof Hsp as Hsp'. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & STSH & _).
    assert (CE : ahl_ceil ar = usp - 8388608) by (unfold ahl_ceil; rewrite (dla_sptop _ _ _ _ DL); reflexivity).
    assert (IS : in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) x).
    { unfold in_shadow_of, S, SB. rewrite CE, (dla_sptop _ _ _ _ DL). replace (usp - 8388608 + (usp - (usp - 8388608)) - 1) with (usp - 1) by ring. exact Hx. }
    unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ STSH IS).
    apply (di_stksh _ _ _ _ _ _ _ _ _ _ D). unfold in_shadow_of, S, SB, STKTOP. rewrite CE, (dla_sptop _ _ _ _ DL).
    assert (MX : usp <= Z.max usp (ar_stack_top ar)) by lia.
    split; [lia|]. assert ((usp - 1) / 8 <= (usp - 8388608 + (Z.max usp (ar_stack_top ar) - (usp - 8388608)) - 1) / 8) by (apply Z.div_le_mono; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hi_sh0 : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model ->
    shadow_allowed A (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->            (* [comment removed for export] *)
    (usp - 8388608) / 8 + 0x7fff8000 <= x <= (2 ^ 47 - 1) / 8 + 0x7fff8000 ->
    mrestrict (ahid A model) M (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof.
    intros LB LK cr A M model x D SAH Hx. pose proof Hsp as Hsp'.
    assert (CE : ahl_ceil ar = usp - 8388608) by (unfold ahl_ceil; rewrite (dla_sptop _ _ _ _ DL); reflexivity).
    assert (IS : in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x).
    { unfold in_shadow_of, S, SB. rewrite CE. replace (usp - 8388608 + (2 ^ 47 - (usp - 8388608)) - 1) with (2 ^ 47 - 1) by ring. lia. }
    unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ SAH IS). exact (di_hish _ _ _ _ _ _ _ _ _ _ D x IS).
  Qed.

  (* [comment removed for export] *)
  Lemma img_sh0 : forall LB LK cr A M (model : Model) a n x, dinvA LB LK cr A M model ->
    0x10000 <= a -> a + n <= 0x696000 -> 0 < n -> Forall (fun r => a + n <= fst r \/ snd r <= a) (icl_poison IL) ->
    a / 8 + 0x7fff8000 <= x <= (a + n - 1) / 8 + 0x7fff8000 ->
    mrestrict (ahid A model) M (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof.
    intros LB LK cr A M model a n x D Ha Hn Hp HP Hx. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH a n) as (Z0 & SA);
      [rewrite (dla_img_lo _ _ _ _ DL); lia | rewrite (dla_img_hi _ _ _ _ DL); lia | exact Hp | exact HP |].
    assert (IS : in_shadow_of a n x) by (unfold in_shadow_of, S, SB; exact Hx).
    unfold mrestrict. rewrite (vis_of_allowed _ _ _ _ _ SA IS). exact (Z0 x IS).
  Qed.

  (* [comment removed for export] *)
  Lemma kimg_clear : forall E MV kn lo hi, know_ok ASEGS E MV kn -> existsb (kentry_eqb (KImg lo hi)) kn = true ->
    forall i, lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  Proof.
    intros E MV kn lo hi HK Hb. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. exact (proj2 (proj2 X)).
  Qed.
  Lemma kword_lit : forall E MV kn a (w : nat) v, know_ok ASEGS E MV kn -> existsb (kentry_eqb (KWord (SA (ELit 0) a) w v)) kn = true ->
    0 <= a -> a + Z.of_nat w <= 2 ^ 63 ->
    rdn ASEGS MV (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v)).
  Proof.
    intros E MV kn a w v HK Hb Ha Hw. apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok] in X. destruct X as (_ & _ & X).
    unfold adenot, v_addi in X. cbn [a_base a_off edenot] in X. rewrite (u_small 0) in X by lia. rewrite Z.add_0_l in X. exact X.
  Qed.
End Stdio.
End FPX_1.
