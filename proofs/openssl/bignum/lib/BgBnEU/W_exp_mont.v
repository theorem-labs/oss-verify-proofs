(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnDivWords BnModel BnTree BnInv BnBridge BgState BgWords BgInv BgLib BgArith BgMont BgExp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require W_ctx3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit ExpKitArr ValArr W_mod_exp W_exp_simple W_mont PlaceMont W_mont_ctx.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac the_mi := lazymatch goal with H : mem_inv bgusegs _ |- _ => exact H end.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 1376572 => 2
  | 1376576 => 1
  | 1376580 => 2
  | 1376824 => 2
  | 1376828 => 1
  | 1376832 => 2
  | 1377200 => 2
  | 1377304 => 1
  | 1377308 => 2
  | 1377316 => 1
  | 1377320 => 2
  | 1377336 => 1
  | 1377340 => 1
  | 1377344 => 2
  | 1377348 => 1
  | 1377352 => 1
  | 1377356 => 1
  | 1377360 => 1
  | 1377364 => 2
  | 1377372 => 2
  | 1377376 => 1
  | 1377380 => 2
  | 1377444 => 2
  | 1377448 => 1
  | 1377452 => 2
  | 1377456 => 2
  | 1377460 => 1
  | 1377464 => 2
  | 1377472 => 2
  | 1377476 => 1
  | 1377480 => 2
  | 1377520 => 2
  | 1377524 => 2
  | 1377644 => 2
  | 1377672 => 1
  | 1377676 => 1
  | 1377680 => 1
  | 1377684 => 2
  | 1377708 => 1
  | 1377712 => 2
  | 1377716 => 1
  | 1377720 => 1
  | 1377724 => 2
  | 1377780 => 1
  | 1377784 => 2
  | 1377848 => 1
  | 1377852 => 2
  | 1377860 => 1
  | 1377864 => 2
  | 1377916 => 1
  | 1377920 => 1
  | 1377924 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Lemma cb8x3_c8 : forall m A (j1 j2 j3 : list byte) rest, rw_cells bgusegs m A (CB 8 j1 :: CB 8 j2 :: CB 8 j3 :: rest) ->
  exists w e r : word, rw_cells bgusegs m A (C8 w :: C8 e :: C8 r :: rest).
Proof.
  intros m A j1 j2 j3 rest H.
  assert (HL : length j1 = 8%nat /\ length j2 = 8%nat /\ length j3 = 8%nat) by (destruct H as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; tauto).
  destruct HL as (L1 & L2 & L3).
  exists (le_bytes_to_word j1), (le_bytes_to_word j2), (le_bytes_to_word j3).
  change (CB 8 j1 :: CB 8 j2 :: CB 8 j3 :: rest) with ([CB 8 j1; CB 8 j2; CB 8 j3] ++ rest) in H.
  change (C8 (le_bytes_to_word j1) :: C8 (le_bytes_to_word j2) :: C8 (le_bytes_to_word j3) :: rest)
    with ([C8 (le_bytes_to_word j1); C8 (le_bytes_to_word j2); C8 (le_bytes_to_word j3)] ++ rest).
  eapply bk_rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. rewrite !cells_wf_app in *. cbn [cells_wf cell_wf] in *. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite (le8_of_bytes j1 L1), (le8_of_bytes j2 L2), (le8_of_bytes j3 L3). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

Lemma cb8x5_c8 : forall m A (j1 j2 j3 j4 j5 : list byte) rest, rw_cells bgusegs m A (CB 8 j1 :: CB 8 j2 :: CB 8 j3 :: CB 8 j4 :: CB 8 j5 :: rest) ->
  exists z v w e r : word, rw_cells bgusegs m A (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: rest).
Proof.
  intros m A j1 j2 j3 j4 j5 rest H.
  assert (HL : length j1 = 8%nat /\ length j2 = 8%nat /\ length j3 = 8%nat /\ length j4 = 8%nat /\ length j5 = 8%nat)
    by (destruct H as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf; tauto).
  destruct HL as (L1 & L2 & L3 & L4 & L5).
  exists (le_bytes_to_word j1), (le_bytes_to_word j2), (le_bytes_to_word j3), (le_bytes_to_word j4), (le_bytes_to_word j5).
  change (CB 8 j1 :: CB 8 j2 :: CB 8 j3 :: CB 8 j4 :: CB 8 j5 :: rest) with ([CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5] ++ rest) in H.
  change (C8 (le_bytes_to_word j1) :: C8 (le_bytes_to_word j2) :: C8 (le_bytes_to_word j3) :: C8 (le_bytes_to_word j4) :: C8 (le_bytes_to_word j5) :: rest)
    with ([C8 (le_bytes_to_word j1); C8 (le_bytes_to_word j2); C8 (le_bytes_to_word j3); C8 (le_bytes_to_word j4); C8 (le_bytes_to_word j5)] ++ rest).
  eapply bk_rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. rewrite !cells_wf_app in *. cbn [cells_wf cell_wf] in *. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes].
    rewrite (le8_of_bytes j1 L1), (le8_of_bytes j2 L2), (le8_of_bytes j3 L3), (le8_of_bytes j4 L4), (le8_of_bytes j5 L5). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

Lemma val_frame_splitM : forall m X (z v w e r : word) ws rest, length ws = 32%nat ->
  rw_cells bgusegs m X (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: CB 256 (u64s ws) :: rest) ->
  rw_cells bgusegs m X [C8 z; C8 v; C8 w; C8 e; C8 r] /\ u64arr bgusegs m (X + 40) ws /\ rw_cells bgusegs m (X + 296) rest.
Proof.
  intros m X z v w e r ws rest HL H.
  change (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: CB 256 (u64s ws) :: rest) with ([C8 z; C8 v; C8 w; C8 e; C8 r] ++ [CB 256 (u64s ws)] ++ rest) in H.
  apply bk_rw_cells_app in H. destruct H as [H1 H]. apply bk_rw_cells_app in H. destruct H as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3. split; [exact H1|]. split.
  - apply (rw_cells_CB_u64arr bgusegs m (X + 40) ws 256); [rewrite HL; reflexivity| exact H2].
  - replace (X + 296) with (X + Z.of_nat 40 + Z.of_nat 256) by lia. exact H3.
Qed.

Lemma val_frame_joinM : forall m X (z v w e r : word) ws rest, length ws = 32%nat ->
  rw_cells bgusegs m X [C8 z; C8 v; C8 w; C8 e; C8 r] -> u64arr bgusegs m (X + 40) ws -> rw_cells bgusegs m (X + 296) rest ->
  rw_cells bgusegs m X (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: CB 256 (u64s ws) :: rest).
Proof.
  intros m X z v w e r ws rest HL H1 H2 H3.
  change (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: CB 256 (u64s ws) :: rest) with ([C8 z; C8 v; C8 w; C8 e; C8 r] ++ [CB 256 (u64s ws)] ++ rest).
  apply bk_rw_cells_app. split; [exact H1|]. apply bk_rw_cells_app. cbn [cells_size csize Nat.add]. split.
  - apply (rw_cells_CB_u64arr bgusegs m (X + 40) ws 256); [rewrite HL; reflexivity| exact H2].
  - replace (X + Z.of_nat 40 + Z.of_nat 256) with (X + 296) by lia. exact H3.
Qed.

Lemma val_frame_initM : forall m X (z v w e r a0 : word) junk rest,
  rw_cells bgusegs m X (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: C8 a0 :: CB 248 junk :: rest) ->
  exists ws, length ws = 32%nat /\ nth_error ws 0 = Some a0 /\ rw_cells bgusegs m X (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: CB 256 (u64s ws) :: rest).
Proof.
  intros m X z v w e r a0 junk rest H.
  assert (HLj : length junk = 248%nat).
  { destruct H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. tauto. }
  destruct (u64s_exists 31 junk ltac:(rewrite HLj; reflexivity)) as (ws & Hl & E).
  exists (a0 :: ws). split; [cbn; lia|]. split; [reflexivity|].
  change (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: C8 a0 :: CB 248 junk :: rest) with ([C8 z; C8 v; C8 w; C8 e; C8 r] ++ ([C8 a0] ++ [CB 248 junk]) ++ rest) in H.
  change (C8 z :: C8 v :: C8 w :: C8 e :: C8 r :: CB 256 (u64s (a0 :: ws)) :: rest) with ([C8 z; C8 v; C8 w; C8 e; C8 r] ++ [CB 256 (u64s (a0 :: ws))] ++ rest).
  eapply bk_rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. rewrite !cells_wf_app in *. cbn [cells_wf cell_wf] in *. rewrite u64s_length. cbn [length]. rewrite Hl. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes u64s]. rewrite E, !app_nil_r, <- app_assoc. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

Lemma testbit_63 : forall v, 0 <= v < 2 ^ 64 -> Z.testbit v 63 = (2 ^ 63 <=? v).
Proof.
  intros v Hv. destruct (Z.leb_spec (2 ^ 63) v) as [H|H].
  - apply Z.testbit_true; [lia|]. replace (v / 2 ^ 63) with 1 by (apply Z.div_unique with (r := v - 2 ^ 63); lia). reflexivity.
  - apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma nth_error_wlimbs : forall (l : list Z) i, (i < length l)%nat -> nth_error (wlimbs l) i = Some (Z_to_bv 64 (nth i l 0)).
Proof. intros l i H. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' l 0 H). reflexivity. Qed.

Lemma hpl_pl_mont : forall PL x r, hpl PL r -> hpl (pl_set_mont PL x) r.
Proof.
  intros PL x r [N H]. split; [exact N|]. intros p E.
  destruct (mont_ref r) eqn:MR.
  - destruct x as [[a q]|]; [|rewrite (pl_of_mont_none (pl_set_mont PL None) r eq_refl MR) in E; discriminate E].
    destruct (mont_ref_cases r MR) as [-> | [-> | -> ]]; cbn in E; injection E as <-; eauto.
  - rewrite pl_of_set_mont_other in E by exact MR. exact (H p E).
Qed.

Lemma ref_at_mont_fresh : forall st OW PL x r a, pl_mont PL = None -> ref_at st OW PL r a -> ref_at st OW (pl_set_mont PL x) r a.
Proof.
  intros st OW PL x r a E H. destruct (mont_ref r) eqn:MR.
  - exfalso. pose proof (pl_of_mont_none PL r E MR) as N.
    assert (RF : (r < NFIX)%nat) by (destruct (mont_ref_cases r MR) as [-> | [-> | -> ]]; unfold RMontRR, RMontN, RMontNi, NFIX; lia).
    apply (proj1 (ref_at_fixed st OW PL r a RF)) in H. destruct H as (p & Ep & _). rewrite N in Ep. discriminate Ep.
  - apply ref_at_pl_mont_other; [exact MR| exact H].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_IS_ODD_A : Z := 0xffb40.
Definition BN_UCMP_A : Z := 0xfecac.
Definition BN_MONT_CTX_SET : Z := 0x100544.
Definition BN_WEXPAND_A : Z := 0xfe3e0.

Section Proofs.
  Variable CS : Z.
  Hypothesis CS96 : 128 <= CS.
  Hypothesis CSnew : W_ctx3.BN_MONT_CTX_NEW_STACK <= CS.
  Hypothesis CSfree : W_ctx3.BN_MONT_CTX_FREE_STACK <= CS.
  Hypothesis CSwexp : W_expand.BN_WEXPAND_STACK <= CS.
  Definition BN_MOD_EXP_MONT_STACK : Z := 400 + CS.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Hypothesis BN_CTX_start_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_start (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' _ => PL' = PL /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_simple.BN_CTX_START) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_get_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_get (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun r bs' OW' PL' a0' => PL' = PL /\ (exists i, r = RPool i) /\ (exists a, ref_at bs' OW' PL r a /\ a0' = wz a) /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_simple.BN_CTX_GET) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_end_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ OW' PL' _ => PL' = PL /\ OW' = OW))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_simple.BN_CTX_END) fc None m (seg_rom bgusegs)).

  Hypothesis bn_mul_mont_fixed_top_walk : mont3_stmt BN_MUL_MONT_FIXED_TOP CS (bn_mul_mont_fixed_top (tree_ops bptr)).
  Hypothesis bn_to_mont_fixed_top_walk : mont2_stmt BN_TO_MONT_FIXED_TOP CS (bn_to_mont_fixed_top (tree_ops bptr)) false.
  Hypothesis BN_from_montgomery_walk : mont2_stmt BN_FROM_MONTGOMERY CS (BN_from_montgomery (tree_ops bptr)) true.

  Hypothesis BN_MONT_CTX_set_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rd : bnref) (ad am ac : Z) (qm qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rd ad -> rd <> ROne -> pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) -> pl_bn PL RTmod = None ->
    a0 = wz am -> a1 = wz ad -> a2 = wz ac ->
    implM bgusegs (interp (embed (BN_MONT_CTX_set (tree_ops bptr) rd bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_SET) fc None m (seg_rom bgusegs)).

  Hypothesis BN_ucmp_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (r1 r2 : bnref) (a b : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL r1 a -> ref_at bs OW PL r2 b -> r1 <> ROne -> r2 <> ROne -> a0 = wz a -> a1 = wz b ->
    implM bgusegs (interp (embed (BN_ucmp (tree_ops bptr) r1 r2 bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun c bs' OW' PL' a0' => (PL' = PL /\ a0' = Z_to_bv 64 c /\ -2147483648 < c < 2147483648 /\ bs' = bs /\ OW' = OW) /\ c = ucmp_pure (getbn r1 bs) (getbn r2 bs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_UCMP_A) fc None m (seg_rom bgusegs)).

  Hypothesis BN_nnmod_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz am -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_nnmod (tree_ops bptr) rr rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_simple.BN_NNMOD) fc None m (seg_rom bgusegs)).

  Hypothesis BN_set_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr : bnref) (ar w : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> wref PL rr -> 0 <= w < BW -> a0 = wz ar -> a1 = wz w ->
    implM bgusegs (interp (embed (BN_set_word (tree_ops bptr) rr w bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rr bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_exp_simple.BN_SET_WORD) fc None m (seg_rom bgusegs)).

  Definition mont_gueron (bits window : Z) (rr rp rm rq : bnref) (vals : list bnref) (pm : bptr) : BM (M:=btree bptr) (ptr:=bptr) unit :=
    bbind (tree_ops bptr) (bget (tree_ops bptr) rm) (fun m =>
    let j := bn_top m in
    if (j =? 0)%nat then bunr (tree_ops bptr) else
    bbind (tree_ops bptr)
      (if Z.testbit (nth (j - 1) (bn_buf m) 0) 63 then
         if (rq =? rm)%nat then bunr (tree_ops bptr) else
         bbind (tree_ops bptr) (bn_wexpand (tree_ops bptr) rq j) (fun _ =>
         bbind (tree_ops bptr) (bget (tree_ops bptr) rq) (fun rb =>
         bbind (tree_ops bptr) (bget (tree_ops bptr) rm) (fun m =>
         bset (tree_ops bptr) rq (mkBN (bn_d rb) (splice (bn_buf rb) 0 (neg_limbs (firstn j (bn_buf m)))) j (bn_neg rb) (bn_flags rb)))))
       else bn_to_mont_fixed_top (tree_ops bptr) rq ROne) (fun _ =>
    bbind (tree_ops bptr) (exp_window_loop (tree_ops bptr) (bn_mul_mont_fixed_top (tree_ops bptr)) (Z.to_nat bits) rp rq vals window (bits - 1) true) (fun _ =>
    bbind (tree_ops bptr) (BN_from_montgomery (tree_ops bptr) rr rq) (fun _ =>
    bbind (tree_ops bptr) (BN_MONT_CTX_free (tree_ops bptr) pm) (fun _ => BN_CTX_end (tree_ops bptr)))))).

  Definition mont_tail (bits : Z) (rr ra_ rp rm d rq v0 : bnref) (pm : bptr) : BM (M:=btree bptr) (ptr:=bptr) unit :=
    bbind (tree_ops bptr) (bget (tree_ops bptr) ra_) (fun a =>
    bbind (tree_ops bptr) (BN_ucmp (tree_ops bptr) ra_ rm) (fun c =>
    bbind (tree_ops bptr) (if bn_neg a || (0 <=? c) then bbind (tree_ops bptr) (BN_nnmod (tree_ops bptr) v0 ra_ rm) (fun _ => bret (tree_ops bptr) v0)
                           else bret (tree_ops bptr) ra_) (fun aa =>
    bbind (tree_ops bptr) (bn_to_mont_fixed_top (tree_ops bptr) v0 aa) (fun _ =>
    bbind (tree_ops bptr) (exp_table (tree_ops bptr) (bn_mul_mont_fixed_top (tree_ops bptr)) (window_bits bits) v0 d) (fun vals =>
    mont_gueron bits (window_bits bits) rr rp rm rq vals pm))))).

  Definition mont_rest (bits : Z) (rr ra_ rp rm : bnref) : BM (M:=btree bptr) (ptr:=bptr) unit :=
    bbind (tree_ops bptr) (BN_CTX_start (tree_ops bptr)) (fun _ =>
    bbind (tree_ops bptr) (BN_CTX_get (tree_ops bptr)) (fun d =>
    bbind (tree_ops bptr) (BN_CTX_get (tree_ops bptr)) (fun rq =>
    bbind (tree_ops bptr) (BN_CTX_get (tree_ops bptr)) (fun v0 =>
    bbind (tree_ops bptr) (BN_MONT_CTX_new (tree_ops bptr)) (fun pm =>
    bbind (tree_ops bptr) (BN_MONT_CTX_set (tree_ops bptr) rm) (fun _ =>
    mont_tail bits rr ra_ rp rm d rq v0 pm)))))).

  Lemma BN_mod_exp_mont_eq : forall rr ra_ rp rm,
    BN_mod_exp_mont (tree_ops bptr) rr ra_ rp rm =
    bbind (tree_ops bptr) (bget (tree_ops bptr) rm) (fun m =>
      if negb (is_odd_pure m) then bunr (tree_ops bptr)
      else bbind (tree_ops bptr) (any_consttime (tree_ops bptr) [rp; ra_; rm]) (fun ct =>
           if ct then bunr (tree_ops bptr)
           else bbind (tree_ops bptr) (BN_num_bits (tree_ops bptr) rp) (fun bits =>
                if bits =? 0 then exp_bits0 (tree_ops bptr) rr rm else mont_rest bits rr ra_ rp rm))).
  Proof. reflexivity. Qed.

  Section Body.
    Variables (ra gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (lo B : Z) (s : PState) (bs : bstate bptr) (OW LB : list block) (m : mem) (PL0 : placement) (EA : BnRep.err_addrs).
    Variables (rr rp : bnref) (arr arp : Z).
    Variables (ac : Z) (qc : bptr) (am : Z) (qm : bptr).
    Variables (FB SPv : Z).
    Variables (jz jv : word).
    Hypothesis ESPV : SPv = FB + 400.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis GLO' : GLOBALS_TOP <= lo.
    Hypothesis FBlo : lo <= FB.
    Hypothesis FBsp : FB <= SPv.
    Hypothesis SPB : SPv <= B.
    Hypothesis B63 : B < 2^63.
    Hypothesis SPR2 : SPv < 2^64.
    Hypothesis FROK : frames_ok PL0 SPv B.
    Hypothesis LOF : lo <= FB - CS.
    Hypothesis HPC : pl_ctx PL0 = Some (ac, qc).
    Hypothesis HFM : pl_mont PL0 = None.
    Hypothesis AMR : 0 < am < 2^63.
    Hypothesis FB16 : FB mod 16 = 0.

    Local Notation PL := (pl_set_mont PL0 (Some (am, qm))).

    Definition saved : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Definition efrMv (v w e r : word) (ws : list word) : list cell := C8 jz :: C8 v :: C8 w :: C8 e :: C8 r :: CB 256 (u64s ws) :: saved.
    Definition efrM (w e r : word) (ws : list word) : list cell := efrMv jv w e r ws.
    Definition FINALQ : unit * bstate bptr -> PState -> machine_state -> Prop :=
      bn_post ra (Z_to_bv 64 SPv) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL0 EA
              (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL0 /\ a0' = wz 1).

    Lemma HPM : pl_mont PL = Some (am, qm). Proof. reflexivity. Qed.

    Local Ltac kitM :=
      pose proof (kenv_pre LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE;
      pose proof (kenv_post LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST;
      pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B SPv FB CEIL FBlo FBsp SPR2 A) as BPK;
      pose proof (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK) as KOPEN;
      pose proof (kenv_below LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KBELOW;
      assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - FBlo FBsp SPR2 CEIL; lia);
      pose proof GLO' as GLO2; unfold GLOBALS_TOP in GLO2.

    Local Ltac fload ENV :=
      let FR := fresh "FRl" in
      pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _); unfold efrM, efrMv in FR;
      replace (Z_to_bv 64 SPv) with (Z_to_bv 64 (FB + 400)) by (f_equal; clear - ESPV; lia);
      step;
      replace (Z_to_bv 64 (FB + 400)) with (Z_to_bv 64 SPv) by (f_equal; clear - ESPV; lia);
      clear FR.

    Local Ltac fstore ENV LS OFF :=
      let ST := fresh "STs" in let ERR := fresh "ERRs" in let MI := fresh "MIs" in let FR := fresh "FRs" in let errv := fresh "errvs" in
      let MU := fresh "MUs" in let WM := fresh "WMs" in let HEAP := fresh "HEAPs" in let PARTS := fresh "PARTSs" in let HWL := fresh "HWLs" in
      lazymatch type of ENV with
      | kenv _ _ _ _ _ _ _ _ _ _ _ ?stx ?bsx ?mx ?OWx =>
          pose proof ENV as (HEAP & _ & ST & (errv & ERR) & MI & _ & _ & _ & _ & FR & _); unfold efrM, efrMv in FR;
          pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS;
          pose proof (munch_refl [(FB + OFF, FB + OFF + 8)]%Z mx) as MU; pose proof (wmono_refl bgusegs mx) as WM;
          apply hide_intro in ERR;
          replace (Z_to_bv 64 SPv) with (Z_to_bv 64 (FB + 400)) by (f_equal; clear - ESPV; lia);
          step;
          apply hide_elim in ERR;
          replace (Z_to_bv 64 (FB + 400)) with (Z_to_bv 64 SPv) by (f_equal; clear - ESPV; lia);
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) =>
            eapply (rw_cells_transport bgusegs _ mx my) in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; unfold LX_ERRNO, RATP; lia| exact I]];
            assert (HWL : Forall (w_lib bsx OWx PL lo SPv) [(FB + OFF, FB + OFF + 8)]) by (constructor; [left; cbn; lia| constructor]);
            lazymatch type of FR with rw_cells _ _ _ (C8 jz :: C8 ?v1 :: C8 ?w1 :: C8 ?e1 :: C8 ?r1 :: CB 256 (u64s ?ws1) :: _) =>
              fold (efrMv v1 w1 e1 r1 ws1) in FR; try fold (efrM w1 e1 r1 ws1) in FR;
              let E2 := fresh "ENVs" in let L2 := fresh "LSs" in
              pose proof (kenv_silent LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK _ _ stx bsx mx my OWx _ errv ENV PARTS MU WM HWL ST ERR MI FR ltac:(cbn; lia)) as E2;
              assert (L2 : lib_state bsx my OWx PL EA) by
                (assert (WOK : Forall (w_ok OWx LB bsx PL EA SPv []) [(FB + OFF, FB + OFF + 8)]) by (constructor; [apply w_stack; cbn; lia| constructor]);
                 exact (lib_state_frame stx LB _ _ [] bsx mx my OWx PL EA _ HEAP LS MU WM FROK WOK));
              clear ST MI MU WM HWL ERR FR HEAP PARTS ENV LS; rename E2 into ENV; rename L2 into LS
            end
          end
      end.

    Hypothesis HAr : ref_at bs OW PL rr arr.
    Hypothesis WRr : hpl PL0 rr.

    Lemma mont_exit : forall (vf w e : word) ws stK bsK mK OWK (r : bnref) (ar : Z) (ri : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrMv vf w e (Z_to_bv 64 ar) ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri ->
      implM bgusegs (interp (embed (tbind (BN_from_montgomery (tree_ops bptr) rr r bsK)
                                     (fun p => tbind (BN_MONT_CTX_free (tree_ops bptr) qm (snd p)) (fun p0 => BN_CTX_end (tree_ops bptr) (snd p0)))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) x20 x21 (Z_to_bv 64 am) x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x150698) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK HArK Er. kitM. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAr) as HArrK.
      unfold implM. iprefix. step. fload ENVK. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_from_montgomery_walk; [exact PRE5| reflexivity| rewrite ESP; exact FB16| exact HArrK| exact HArK| apply hpl_wref; apply hpl_pl_mont; exact WRr
          | intros _; rewrite Er; unfold RPool, ROne, NFIX; lia| exact HPM| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m14 & OW14 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV14 & LS14). pose proof KP as RS14; apply kpost_refs in RS14.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x1506ac)) with (Z_to_bv 64 0x1506ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. step. if_false. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV14 LS14 LOF) as (errv6 & PRE6).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply (BN_MONT_CTX_free_lwalk_cs HF CS CSfree); [exact PRE6| reflexivity| exact HPM| reflexivity]. }
      cbv beta. intros [u7 bs7] st7 ms7 PO. unfold bn_post in PO. rewrite ESP in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m15 & OW15 & PL' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & ->).
      cbn [fst snd] in *.
      set (PLx := pl_set_mont PL None) in *.
      assert (KP1 : kpost LB PLx EA lo B FB st6 bs6 m14 OW14 st7 bs7 m15 OW15).
      { unfold kpost. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exists errv'; exact P5|]. split; [exact P6|].
        split; [exact P7|]. split; [exact P8|]. split; [exact P9| exact P10]. }
      destruct (kenv_post LB PLx EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK _ _ _ _ _ _ _ _ _ ENV14 KP1) as (ENV15 & LS15).
      clear PRE6 KP1 P1 P2 P3 P4 P5 P6 P7 P8 P9.
      replace (ret_pc (Z_to_bv 64 0x1506c8)) with (Z_to_bv 64 0x1506c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. step.
      destruct (kenv_pre LB PLx EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK _ _ _ _ _ CS ENV15 LS15 LOF) as (errv8 & PRE8).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk; [exact PRE8| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u9 bs9] st9 ms9 PO.
      apply (@bn_post_kpost _ _ LB PLx EA lo B SPv FB CEIL FBlo FBsp SPR2) in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m16 & OW16 & -> & KP & (_ & EOW16)).
      destruct (kenv_post LB PLx EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK _ _ _ _ _ _ _ _ _ ENV15 KP) as (ENV16 & LS16).
      cbn [fst snd] in *. clear PRE8 KP.
      replace (ret_pc (Z_to_bv 64 0x1506d0)) with (Z_to_bv 64 0x1506d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PLx lo B SPv FB s bs OW m _ _ _ _ _ ENV16) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
      unfold PLx in LS16. rewrite (pl_set_mont_fresh PL0 _ HFM) in LS16.
      unfold efrM, efrMv, saved in FRF.
      step. do 13 step. release_frame FRF STF SPv. step. step.
      apply evt_done. unfold FINALQ, bn_post. do 15 eexists. exists m16, OW16, PL0, errvF.
      replace (FB + 400) with SPv by lia. rewrite (unsigned_lit SPv) by lia. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS16|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
    Qed.

    Variables (rm : bnref) (arm : Z).
    Local Notation MUL := (bn_mul_mont_fixed_top (tree_ops bptr)).

    Definition vtab (bsK : bstate bptr) (OWK : list block) (ws : list word) (vals : list bnref) (addrs : list Z) : Prop :=
      length addrs = length vals /\
      forall i, (i < length vals)%nat ->
        nth_error ws i = Some (Z_to_bv 64 (nth i addrs 0)) /\ ref_at bsK OWK PL (nth i vals 0%nat) (nth i addrs 0)
        /\ (exists j, nth i vals 0%nat = RPool j) /\ 0 < nth i addrs 0 < 2^64.

    Lemma vtab_stable : forall bsK OWK bs' OW' ws vals addrs, vtab bsK OWK ws vals addrs -> refs_stable bsK OWK bs' OW' -> vtab bs' OW' ws vals addrs.
    Proof.
      intros bsK OWK bs' OW' ws vals addrs [L H] RS. split; [exact L|]. intros i Hi. destruct (H i Hi) as (H1 & H2 & H3 & H4).
      split; [exact H1|]. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS H2)|]. split; [exact H3| exact H4].
    Qed.

    Lemma vtab_snoc : forall bsK OWK ws vals addrs v a j, vtab bsK OWK ws vals addrs -> (length vals < length ws)%nat ->
      ref_at bsK OWK PL v a -> v = RPool j -> 0 < a < 2^64 ->
      vtab bsK OWK (Arr.upd ws (length vals) (Z_to_bv 64 a)) (vals ++ [v]) (addrs ++ [a]).
    Proof.
      intros bsK OWK ws vals addrs v a j [L H] Hl HA Ev Ha. split; [rewrite !length_app; cbn; lia|].
      intros i Hi. rewrite length_app in Hi. cbn in Hi.
      destruct (Nat.lt_ge_cases i (length vals)) as [Hlt|Hge].
      - destruct (H i Hlt) as (H1 & H2 & H3 & H4). rewrite !app_nth1 by lia.
        split; [rewrite nth_error_upd_other by lia; exact H1|]. split; [exact H2|]. split; [exact H3| exact H4].
      - assert (Ei : i = length vals) by lia. subst i.
        rewrite app_nth2 by lia. rewrite (app_nth2 vals [v] 0%nat) by lia. rewrite L, Nat.sub_diag. cbn [nth].
        split; [apply nth_error_upd_same; exact Hl|]. split; [exact HA|]. split; [exists j; exact Ev| exact Ha].
    Qed.

    Lemma table_body : forall vals addrs stK bsK mK OWK (w e r : word) ws (bits window : Z) (d : bnref) (ad : Z)
        (K : bnref -> bstate bptr -> btree bptr (list bnref * bstate bptr)) (Q : list bnref * bstate bptr -> PState -> machine_state -> Prop)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM w e r ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> (1 <= length vals)%nat -> (length vals < 32)%nat -> 1 < window <= 6 ->
      ref_at bsK OWK PL d ad -> d <> ROne ->
      (forall v av bs2 st2 m2 OW2 ws2 (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
          kenv LB PL lo B SPv FB s bs OW m (efrM w e r ws2) st2 bs2 m2 OW2 -> lib_state bs2 m2 OW2 PL EA -> length ws2 = 32%nat ->
          vtab bs2 OW2 ws2 (vals ++ [v]) (addrs ++ [av]) -> ref_at bs2 OW2 PL d ad -> refs_stable bsK OWK bs2 OW2 ->
          implM bgusegs (interp (embed (K v bs2))) st2 Q
            (MS (mkR (Z_to_bv 64 0x1503d0) (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 am) (Z_to_bv 64 arr) (Z_to_bv 64 (FB + 40 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 arp) (Z_to_bv 64 (Z.of_nat (length vals) + 1)) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 (32 - Z.of_nat (length vals))) (Z_to_bv 64 (window - 1)) t3 t4 t5 t6)
                F (Z_to_bv 64 0x1503d4) fc None m2 (seg_rom bgusegs))) ->
      implM bgusegs (interp (embed (tbind (BN_CTX_get (tree_ops bptr) bsK)
                                           (fun p => tbind (MUL (fst p) (last vals 0%nat) d (snd p)) (fun p0 => K (fst p) (snd p0)))))) stK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 am) (Z_to_bv 64 arr) (Z_to_bv 64 (FB + 40 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 arp) (Z_to_bv 64 (Z.of_nat (length vals) + 1)) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 (32 - Z.of_nat (length vals))) (Z_to_bv 64 (window - 1)) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1503a8) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK LEN VT K1 K32 WB HAd NROd CONT; kitM. unfold MallocRep.wz in *.
      unfold implM. iprefix. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv2 & PRE2).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [v bs2] st2 ms2 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & OW8 & -> & KP & (_ & (vi & Ev) & (av & HAv & ->) & INCL8)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV8 & LS8). pose proof KP as RS8; apply kpost_refs in RS8.
      cbn [fst snd] in *. clear PRE2 KP.
      replace (ret_pc (Z_to_bv 64 0x1503b0)) with (Z_to_bv 64 0x1503b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. hide_ors. ub. unhide.
      pose proof ENV8 as (HEAP8 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS8) as PARTS8.
      assert (FROK8 : frames_ok PL FB B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
      assert (NROv : v <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; lia).
      pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP8 PARTS8 FROK8 HAv NROv) as (Av0 & AvC & _).
      assert (AvR : 0 < av < 2^64) by (clear - Av0 AvC SPR2 SPB B63 ESPV; lia). clear AvC.

      pose proof ENV8 as (_ & _ & ST8 & (errv8 & ERR8) & MI8 & _ & _ & _ & _ & FR8 & _).
      unfold efrM, efrMv in FR8. destruct (val_frame_splitM m8 FB jz jv w e r ws saved LEN FR8) as (F0 & VA & FS). clear FR8.
      assert (IDX : 0 <= Z.of_nat (length vals) < Z.of_nat (length ws)) by (rewrite LEN; lia).
      pose proof (u64arr_store_ok bgusegs m8 (FB + 40) ws (Z.of_nat (length vals)) (wa (FB + 40 + 8 * Z.of_nat (length vals))) VA IDX eq_refl) as SOKW.
      pose proof (u64arr_write bgusegs m8 (FB + 40) ws (Z.of_nat (length vals)) (Z_to_bv 64 av) VA IDX) as U2.
      pose proof (munch_refl [(FB + 40 + 8 * Z.of_nat (length vals), FB + 40 + 8 * Z.of_nat (length vals) + 8)]%Z m8) as MU. pose proof (wmono_refl bgusegs m8) as WM.
      apply hide_intro in ERR8.
      step. store_done. apply hide_elim in ERR8.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      eapply (rw_cells_transport bgusegs _ m8 m9) in ERR8; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; unfold LX_ERRNO, RATP; lia| exact I]].
      rewrite Nat2Z.id in U2.
      pose proof (val_frame_joinM m9 FB jz jv w e r _ saved ltac:(etransitivity; [apply Arr.upd_length| exact LEN]) F0 U2 FS) as FR9.
      fold (efrMv jv w e r (Arr.upd ws (length vals) (Z_to_bv 64 av))) in FR9. fold (efrM w e r (Arr.upd ws (length vals) (Z_to_bv 64 av))) in FR9.
      assert (HWL : Forall (w_lib bs2 OW8 PL lo SPv) [(FB + 40 + 8 * Z.of_nat (length vals), FB + 40 + 8 * Z.of_nat (length vals) + 8)]) by (constructor; [left; cbn; lia| constructor]).
      pose proof (kenv_silent LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK _ _ st2 bs2 m8 m9 OW8 _ errv8
                    ENV8 PARTS8 MU WM HWL ST8 ERR8 ltac:(the_mi) FR9 ltac:(cbn; lia)) as ENV9.
      assert (LS9 : lib_state bs2 m9 OW8 PL EA).
      { assert (WOK : Forall (w_ok OW8 LB bs2 PL EA SPv []) [(FB + 40 + 8 * Z.of_nat (length vals), FB + 40 + 8 * Z.of_nat (length vals) + 8)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
        exact (lib_state_frame st2 LB _ _ [] bs2 m8 m9 OW8 PL EA _ HEAP8 LS8 MU WM FROK WOK). }
      clear ST8 F0 FS MU WM HWL ERR8 FR9.

      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].
      pose proof VT as [VL VT']. pose proof (VT' (length vals - 1)%nat ltac:(lia)) as (Wp & HAprev & (jp & Eprev) & AprevR). clear VT'.
      assert (Wp' : nth_error (Arr.upd ws (length vals) (Z_to_bv 64 av)) (Z.to_nat (Z.of_nat (length vals) - 1)) = Some (Z_to_bv 64 (nth (length vals - 1) addrs 0))).
      { rewrite nth_error_upd_other by lia. replace (Z.to_nat (Z.of_nat (length vals) - 1)) with (length vals - 1)%nat by lia. exact Wp. }
      let a := cur_mem_addr in pose proof (u64arr_read bgusegs m9 (FB + 40) _ (Z.of_nat (length vals) - 1) _ a U2 Wp' ltac:(lia) ltac:(addr_tac)) as RD.
      step. clear RD.

      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV9 LS9 LOF) as (errv3 & PRE3).
      ihere. to_implM.
      eapply implM_embed_bind.
      { rewrite last_nth. eapply bn_mul_mont_fixed_top_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact HAv| exact (ref_at_stable _ _ _ _ PL _ _ RS8 HAprev)| exact (ref_at_stable _ _ _ _ PL _ _ RS8 HAd)
          | rewrite Ev; apply wref_pool| exact NROd| exact HPM| exact HPC
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV9 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 0x1503d0)) with (Z_to_bv 64 0x1503d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS8 RS11) as RS811.
      unfold implM. iprefix. step. if_false.
      ihere. to_implM. eapply CONT; [exact ENV11| exact LS11| etransitivity; [apply Arr.upd_length| exact LEN]| | exact (ref_at_stable _ _ _ _ PL _ _ RS811 HAd)| exact RS811].
      apply (vtab_stable bs2 OW8); [|exact RS11]. eapply vtab_snoc; [eapply vtab_stable; [exact VT| exact RS8]| rewrite LEN; exact K32| exact HAv| exact Ev| exact AvR].
    Qed.

    Definition TABLEQ (e r : word) (bits window : Z) (rq : bnref) (ar : Z) (rv : list bnref * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists wv ws' addrs' mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x24 x27 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      e (Z_to_bv 64 arr) x20 (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) x24 (Z_to_bv 64 bits) (Z_to_bv 64 window) x27 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x150418) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efrM wv e r ws') st' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA /\ length ws' = 32%nat
        /\ vtab (snd rv) OWK' ws' (fst rv) addrs' /\ Z.of_nat (length (fst rv)) = (if 1 <? window then 2 ^ (window - 1) else 1)
        /\ ref_at (snd rv) OWK' PL rq ar.

    Lemma table_loop : forall c vals addrs stK bsK mK OWK (e r : word) ws (bits window : Z) (d : bnref) (ad : Z) (rq : bnref) (ar : Z)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM (Z_to_bv 64 window) e r ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> (1 <= length vals)%nat -> Z.of_nat (length vals) + Z.of_nat (S c) = 2 ^ (window - 1) -> 1 < window <= 6 ->
      ref_at bsK OWK PL d ad -> d <> ROne -> ref_at bsK OWK PL rq ar ->
      implM bgusegs (interp (embed (exp_table_loop (tree_ops bptr) MUL (S c) vals d bsK))) stK
        (TABLEQ e r bits window rq ar)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 am) (Z_to_bv 64 arr) (Z_to_bv 64 (FB + 40 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 arp) (Z_to_bv 64 (Z.of_nat (length vals) + 1)) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 (32 - Z.of_nat (length vals))) (Z_to_bv 64 (window - 1)) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1503a8) fc None mK (seg_rom bgusegs)).
    Proof.
      induction c as [|c IH]; intros until t6; intros ENVK LSK LEN VT K1 KC WB HAd NROd HAq.
      -
        rewrite exp_table_loop_S.
        assert (TS : 2 ^ (window - 1) <= 32) by (replace 32 with (2 ^ 5) by reflexivity; apply Z.pow_le_mono_r; lia).
        eapply (table_body vals addrs stK bsK mK OWK (Z_to_bv 64 window) e r ws bits window d ad
                  (fun v bs' => exp_table_loop (tree_ops bptr) MUL 0 (vals ++ [v]) d bs'));
          [exact ENVK| exact LSK| exact LEN| exact VT| exact K1| clear - KC TS; lia| exact WB| exact HAd| exact NROd|].
        intros v av bs2 st2 m2 OW2 ws2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ENV2 LS2 LEN2 VT2 HAd2 RS2.
        cbv beta. rewrite exp_table_loop_O. cbn [embed interp]. apply implM_interp_ret. unfold MallocRep.wz.
        assert (TS1 : 1 <= 2 ^ (window - 1)) by (clear - WB; assert (0 < 2 ^ (window - 1)) by (apply Z.pow_pos_nonneg; lia); lia).
        step. rewrite !unsigned_lit by (clear - KC TS WB; lia). rewrite (bv_wrap_small 32) by (unfold bv_modulus; clear - KC TS; lia).
        rewrite (Z.mod_small (window - 1) 32) by (clear - WB; lia). rewrite Z.shiftr_div_pow2 by (clear - WB; lia).
        replace ((Z.of_nat (length vals) + 1) / 2 ^ (window - 1)) with 1 by (symmetry; replace (Z.of_nat (length vals) + 1) with (2 ^ (window - 1)) by (clear - KC; lia); apply Z.div_same; clear - TS1; lia).
        rewrite (bn_swrap32_small 1) by lia.
        step. step. step. step. if_false.
        step. fload ENV2. fload ENV2. step.
        apply evt_done. unfold TABLEQ. exists (Z_to_bv 64 window), ws2, (addrs ++ [av]), m2, OW2. do 19 eexists.
        split; [reflexivity|]. cbn [fst snd]. split; [exact ENV2|]. split; [exact LS2|]. split; [exact LEN2|]. split; [exact VT2|]. split; [|exact (ref_at_stable _ _ _ _ PL _ _ RS2 HAq)].
        rewrite length_app. cbn [length]. replace (1 <? window) with true by (symmetry; apply Z.ltb_lt; clear - WB; lia). clear - KC; lia.
      -
        rewrite exp_table_loop_S.
        assert (TS : 2 ^ (window - 1) <= 32) by (replace 32 with (2 ^ 5) by reflexivity; apply Z.pow_le_mono_r; lia).
        eapply (table_body vals addrs stK bsK mK OWK (Z_to_bv 64 window) e r ws bits window d ad
                  (fun v bs' => exp_table_loop (tree_ops bptr) MUL (S c) (vals ++ [v]) d bs'));
          [exact ENVK| exact LSK| exact LEN| exact VT| exact K1| clear - KC TS; lia| exact WB| exact HAd| exact NROd|].
        intros v av bs2 st2 m2 OW2 ws2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ENV2 LS2 LEN2 VT2 HAd2 RS2.

        cbv beta.
        unfold implM. iprefix.
        step. rewrite !unsigned_lit by (clear - KC TS WB; lia). rewrite (bv_wrap_small 32) by (unfold bv_modulus; clear - KC TS; lia).
        rewrite (Z.mod_small (window - 1) 32) by (clear - WB; lia). rewrite Z.shiftr_div_pow2 by (clear - WB; lia).
        rewrite (Z.div_small (Z.of_nat (length vals) + 1) (2 ^ (window - 1))) by (clear - KC; lia).
        rewrite (bn_swrap32_small 0) by lia.
        step. step. step. step. if_true.
        replace (Z.of_nat (length vals) + 2) with (Z.of_nat (length (vals ++ [v])) + 1) by (rewrite length_app; cbn [length]; lia).
        replace (FB + 40 + 8 * Z.of_nat (length vals) + 8) with (FB + 40 + 8 * Z.of_nat (length (vals ++ [v]))) by (rewrite length_app; cbn [length]; lia).
        replace (32 - Z.of_nat (length vals) + -1) with (32 - Z.of_nat (length (vals ++ [v]))) by (rewrite length_app; cbn [length]; lia).
        ihere. to_implM.
        eapply (IH (vals ++ [v]) (addrs ++ [av])); [exact ENV2| exact LS2| exact LEN2| exact VT2| rewrite length_app; cbn [length]; lia
          | rewrite length_app; cbn [length]; clear - KC; lia| exact WB| exact HAd2| exact NROd| exact (ref_at_stable _ _ _ _ PL _ _ RS2 HAq)].
    Qed.

    Definition SQRQ (v w e : word) (ws : list word) (ar : Z) (bsK : bstate bptr) (OWK : list block) (x19 x20 x21 x23 x24 x25 x26 x27 : word)
        (rv : unit * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 am) x19 x20 x21 (Z_to_bv 64 0) x23 x24 x25 x26 x27 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x150638) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efrMv v w e (Z_to_bv 64 ar) ws) st' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA /\ refs_stable bsK OWK (snd rv) OWK'.

    Lemma sqr_loop : forall c stK bsK mK OWK (v w e : word) ws (rq : bnref) (ar : Z) (ri : nat) (x19 x20 x21 x23 x24 x25 x26 x27 : word)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrMv v w e (Z_to_bv 64 ar) ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL rq ar -> rq = RPool ri -> Z.of_nat (S c) < 2 ^ 31 ->
      implM bgusegs (interp (embed (exp_sqr_loop (tree_ops bptr) MUL (S c) rq bsK))) stK
        (SQRQ v w e ws ar bsK OWK x19 x20 x21 x23 x24 x25 x26 x27)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 am) x19 x20 x21 (Z_to_bv 64 (Z.of_nat (S c))) x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x150614) fc None mK (seg_rom bgusegs)).
    Proof.
      induction c as [|c IH]; intros until t6; intros ENVK LSK HArK Er CB; kitM;
        rewrite exp_sqr_loop_S; unfold implM; iprefix;
        fload ENVK;
        do 4 step; step;
        destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3); ihere; to_implM;
        (eapply implM_embed_bind;
         [eapply bn_mul_mont_fixed_top_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact HArK| exact HArK| exact HArK| rewrite Er; apply wref_pool| rewrite Er; unfold RPool, ROne, NFIX; lia| exact HPM| exact HPC
            | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]|]);
        cbv beta; intros [u4 bs4] st4 ms4 PO; (apply BPK in PO; [|intros vv b o p a [E _]; exact E]);
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->));
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11); pose proof KP as RS11; apply kpost_refs in RS11;
        cbn [fst snd] in *; clear PRE3 KP;
        (replace (ret_pc (Z_to_bv 64 0x15062c)) with (Z_to_bv 64 0x15062c) by (symmetry; apply ret_pc_even; [lia| reflexivity]));
        unfold implM; iprefix; step; if_false;
        step; rewrite unsigned_lit by (clear - CB; lia); rewrite (bn_swrap32_small _) by (clear - CB; lia).
      -
        rewrite exp_sqr_loop_O. change (Z.of_nat 1 + -1) with 0.
        step. if_false.
        ihere. cbn [embed interp]. apply implM_interp_ret. apply evt_done.
        unfold SQRQ. exists m11, OW11. do 16 eexists. split; [reflexivity|]. cbn [fst snd].
        split; [exact ENV11|]. split; [exact LS11| exact RS11].
      - replace (Z.of_nat (S (S c)) + -1) with (Z.of_nat (S c)) by lia.
        step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - CB; lia); zify_cond KZ; try (exfalso; clear - KZ; lia).
        ihere. to_implM.
        eapply implM_mono; [eapply IH; [exact ENV11| exact LS11| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HArK)| exact Er| clear - CB; lia]|].
        cbv beta. intros r st' ms' (mK' & OWK' & R); unfold SQRQ. exists mK', OWK'.
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3).
        do 16 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2| eapply refs_stable_trans; [exact RS11| exact K3]].
    Qed.

    Hypothesis HAp : ref_at bs OW PL rp arp.
    Hypothesis NROp : rp <> ROne.
    Lemma lxor_shamt_m : forall t, 0 <= t < 8 ->
      bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 t)) 18446744073709551615)) mod 32 = 31 - t.
    Proof.
      intros t T. assert (E : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7) by lia.
      destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
    Qed.

    Lemma scan_loop : forall c (i wvalue wend : Z) stK bsK mK OWK (v w e r : word) ws (wstart window : Z) (POST : machine_state -> Prop)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrMv v w e r ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> ref_at bsK OWK PL rp arp ->
      1 <= i -> i + Z.of_nat c = window -> (0 < c)%nat -> window <= 6 -> 0 <= wstart < 2 ^ 31 -> 0 <= wend < i -> wend <= wstart -> 1 <= wvalue < 2 ^ (wend + 1) ->
      (forall mK' (wv' we' : Z) (rax' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
          kenv LB PL lo B SPv FB s bs OW m (efrMv v w e r ws) stK bsK mK' OWK -> lib_state bsK mK' OWK PL EA ->
          window_scan (is_bit_set_pure (getbn rp bsK)) wstart c i wvalue wend = (wv', we') ->
          evt bgusegs POST
            (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      x18 x19 x20 (Z_to_bv 64 arp) x22 (Z_to_bv 64 we') (Z_to_bv 64 wstart) (Z_to_bv 64 wv') x18 (Z_to_bv 64 window) t3 t4 t5 t6)
                F (Z_to_bv 64 0x1505dc) fc None mK' (seg_rom bgusegs))) ->
      evt bgusegs POST
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  x18 x19 x20 (Z_to_bv 64 arp) x22 (Z_to_bv 64 wend) (Z_to_bv 64 wstart) (Z_to_bv 64 wvalue) (Z_to_bv 64 window) (Z_to_bv 64 i) t3 t4 t5 t6)
            F (Z_to_bv 64 0x15058c) fc None mK (seg_rom bgusegs)).
    Proof.
      induction c as [|c IH]; intros until t6; intros ENVK LSK HApK I1 IC C0 W6 WS WE WES WV K; [lia|]. kitM.
      assert (P2 : 2 ^ (wend + 1) <= 2 ^ i) by (apply Z.pow_le_mono_r; lia).
      assert (P6 : 2 ^ i <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia).
      pose proof (kenv_open_u LB PL EA lo B SPv FB s bs OW m CEIL FROK) as KOPENU.
      step. step. rewrite (unsigned_lit wstart), (unsigned_lit i) by (clear - WS I1 IC W6; lia). rewrite (bn_swrap32_small (wstart - i)) by (clear - WS I1 IC W6; lia).
      hide_ors. ub. unhide.
      step. rewrite lts_signed by (clear - WS I1 IC W6; lia).
      destruct (Z.ltb_spec (wstart - i) 0) as [LT|GE].
      -
        cbn [negb]. step. step. eapply K; [exact ENVK| exact LSK|]. cbn [window_scan]. replace (wstart - i <? 0) with true by (symmetry; apply Z.ltb_lt; exact LT). reflexivity.
      - cbn [negb].

        destruct (KOPENU _ _ _ _ _ rp arp ENVK LSK HApK NROp) as (Dp & BNp & Up & (OKp1 & OKp2 & OKp3 & OKp4) & _ & SEPp & SEPDp & _ & ALp & UPp).
        pose proof ENVK as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OKp3.
        step. step.
        eapply evt_cut.
        { eapply (BN_is_bit_set_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := arp) (D := Dp) (b := getbn rp bsK) (n := wstart - i);
            [exact BNp | exact ALp | exact UPp | exact Up | exact OKp1 | exact OKp2 | clear - OKp3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS96; lia | exact MIK
            | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDp FBlo FBsp CS96 LOF; lia | reflexivity | reflexivity | clear - GE WS I1; lia]. }
        clear STK MIK.
        intros ms2 PO. unfold bn_small_post in PO.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
        rewrite ESP in *.
        destruct (KBELOW _ _ _ _ m2 _ 16 ENVK LSK ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear MUc WMc MIc STc BNp Up.
        replace (ret_pc (Z_to_bv 64 0x1505a4)) with (Z_to_bv 64 0x1505a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        destruct (is_bit_set_pure (getbn rp bsK) (wstart - i)) eqn:EB; cbn [Z.b2z].
        +
          step. if_false.
          step. rewrite (unsigned_lit i), (unsigned_lit wend) by (clear - I1 WE IC W6; lia). rewrite (bn_swrap32_small (i - wend)) by (clear - I1 WE IC W6; lia).
          pose proof (lor_shiftl_1 wvalue (i - wend) ltac:(clear - WV P2; lia) ltac:(clear - WE; lia)) as LOR.
          assert (WB2 : 1 <= Z.lor (Z.shiftl wvalue (i - wend)) 1 < 2 ^ (i + 1)).
          { rewrite LOR.
            assert (2 <= 2 ^ (i - wend)) by (replace (2 ^ (i - wend)) with (2 * 2 ^ (i - wend - 1)) by (rewrite <- Z.pow_succ_r by (clear - WE; lia); f_equal; clear - WE; lia);
                                           assert (0 < 2 ^ (i - wend - 1)) by (apply Z.pow_pos_nonneg; clear - WE; lia); lia).
            assert (wvalue * 2 ^ (i - wend) <= (2 ^ (wend + 1) - 1) * 2 ^ (i - wend)) by (apply Z.mul_le_mono_nonneg_r; clear - WV WE H; lia).
            assert (2 ^ (wend + 1) * 2 ^ (i - wend) = 2 ^ (i + 1)) by (rewrite <- Z.pow_add_r by (clear - WE; lia); f_equal; clear - WE; lia).
            assert (0 <= wvalue * 2 ^ (i - wend)) by (apply Z.mul_nonneg_nonneg; clear - WV H; lia).
            assert ((2 ^ (wend + 1) - 1) * 2 ^ (i - wend) = 2 ^ (wend + 1) * 2 ^ (i - wend) - 2 ^ (i - wend)) by (clear; lia).
            clear - H H0 H1 H2 H3 WV. lia. }
          assert (P7 : 2 ^ (i + 1) <= 2 ^ 7) by (apply Z.pow_le_mono_r; clear - IC C0 W6; lia).
          assert (SH : 0 <= Z.shiftl wvalue (i - wend) < 2 ^ 7) by (rewrite LOR in WB2; rewrite Z.shiftl_mul_pow2 by (clear - WE; lia); clear - WB2 P7; lia).
          step. ub_chk. step. step.
          step. rewrite (lxor_shamt_m (i - wend)) by (clear - I1 WE IC W6; lia).
          rewrite (unsigned_lit wvalue) by (clear - WV P2 P6; lia). rewrite (bv_wrap_small 32) by (unfold bv_modulus; clear - WV P2 P6; lia).
          rewrite Z.shiftr_div_pow2 by (clear - I1 WE IC W6; lia).
          rewrite (Z.div_small wvalue (2 ^ (31 - (i - wend))))
            by (assert (2 ^ (wend + 1) <= 2 ^ (31 - (i - wend))) by (apply Z.pow_le_mono_r; clear - I1 WE IC W6; lia); clear - WV H; lia).
          rewrite (bn_swrap32_small 0) by lia.
          if_cases KS; zify_cond KS; [exfalso; clear - KS; lia| clear KS].
          step. rewrite (unsigned_lit (i - wend)) by (clear - I1 WE IC W6; lia). rewrite (Z.mod_small (i - wend) 32) by (clear - I1 WE IC W6; lia).
          rewrite (unsigned_lit wvalue) by (clear - WV P2 P6; lia). rewrite (bn_swrap32_small (Z.shiftl wvalue (i - wend))) by (clear - SH; lia).
          step. rewrite (unsigned_lit (Z.shiftl wvalue (i - wend))) by (clear - SH; lia).
          step.

          step. rewrite (swrap32_wrap64 i 1) by (clear - I1 IC W6; lia).
          step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - I1 IC W6; lia); zify_cond KW.
          *
            eapply (IH (i + 1) (Z.lor (Z.shiftl wvalue (i - wend)) 1) i);
              [exact ENV2| exact LS2| exact HApK| clear - I1; lia| clear - IC; lia| clear - IC KW; lia| exact W6| exact WS| clear - I1; lia| clear - GE; lia
              | replace (i + 1) with (i + 1) by reflexivity; exact WB2 |].
            intros mK' wv' we' rax'' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ENV' LS' SC.
            eapply K; [exact ENV'| exact LS'|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB. exact SC.
          *
            step. step. eapply K; [exact ENV2| exact LS2|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB.
            replace c with 0%nat by (clear - IC KW; lia). reflexivity.
        +
          step. if_true.
          step. rewrite (swrap32_wrap64 i 1) by (clear - I1 IC W6; lia).
          step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - I1 IC W6; lia); zify_cond KW.
          * eapply (IH (i + 1) wvalue wend);
              [exact ENV2| exact LS2| exact HApK| clear - I1; lia| clear - IC; lia| clear - IC KW; lia| exact W6| exact WS| clear - WE; lia| exact WES| exact WV|].
            intros mK' wv' we' rax'' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ENV' LS' SC.
            eapply K; [exact ENV'| exact LS'|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB. exact SC.
          * step. step. eapply K; [exact ENV2| exact LS2|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB.
            replace c with 0%nat by (clear - IC KW; lia). reflexivity.
    Qed.

    Definition WINQ (ws : list word) (rq : bnref) (ar : Z) (rv : unit * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists (v' w' e' : word) mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 0) (Z_to_bv 64 arr) x20 x21 (Z_to_bv 64 am) x23 x24 x25 x26 x27 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x150698) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efrMv v' w' e' (Z_to_bv 64 ar) ws) st' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA
        /\ ref_at (snd rv) OWK' PL rq ar.

    Definition WLOOP (f : nat) : Prop := forall (wstart : Z) (start : bool) stK bsK mK OWK (e : word) ws vals addrs (window : Z) (rq : bnref) (ar : Z) (ri : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x25 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrMv (Z_to_bv 64 (Z.lxor (FB + 40) 18446744073709551615)) (Z_to_bv 64 (Z.b2z (negb start))) e (Z_to_bv 64 ar) ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
      0 <= wstart < Z.of_nat f -> wstart < 2 ^ 24 ->
      ref_at bsK OWK PL rq ar -> rq = RPool ri -> ref_at bsK OWK PL rp arp ->
      implM bgusegs (interp (embed (exp_window_loop (tree_ops bptr) MUL f rp rq vals window wstart start bsK))) stK (WINQ ws rq ar)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 arp) (Z_to_bv 64 am) x23 (Z_to_bv 64 wstart) x25 (Z_to_bv 64 window) x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x150534) fc None mK (seg_rom bgusegs)).

    Lemma after_scan : forall f, WLOOP f -> forall (wstart wv we : Z) (start : bool) stK bsK mK OWK ws vals addrs (window : Z) (rq : bnref) (ar : Z) (ri : nat)
        (e : word) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrMv (Z_to_bv 64 (Z.lxor (FB + 40) 18446744073709551615)) (Z_to_bv 64 (Z.b2z (negb start))) e (Z_to_bv 64 ar) ws) stK bsK mK OWK ->
      lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
      0 <= wstart < 2 ^ 24 -> 0 <= we < window -> we <= wstart -> 1 <= wv < 2 ^ (we + 1) -> wstart - (we + 1) < Z.of_nat f ->
      ref_at bsK OWK PL rq ar -> rq = RPool ri -> ref_at bsK OWK PL rp arp ->
      implM bgusegs (interp (embed (tbind ((if start then bret (tree_ops bptr) tt else exp_sqr_loop (tree_ops bptr) MUL (Z.to_nat (we + 1)) rq) bsK)
                                           (fun p2 => tbind (MUL rq rq (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) (snd p2))
                                             (fun p => (if wstart - (we + 1) <? 0 then bret (tree_ops bptr) tt
                                                        else exp_window_loop (tree_ops bptr) MUL f rp rq vals window (wstart - (we + 1)) false) (snd p)))))) stK (WINQ ws rq ar)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  x18 (Z_to_bv 64 arr) (Z_to_bv 64 (Z.shiftr wv 1)) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 we) (Z_to_bv 64 wstart) x25 (Z_to_bv 64 0) (Z_to_bv 64 window) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1505f4) fc None mK (seg_rom bgusegs)).
    Proof.
      intros f REC. intros until t6; intros ENVK LSK LEN VT VL WB WS WE WES WV WF HArK Er HApK. kitM.
      assert (L32 : Z.of_nat (length vals) <= 32).
      { rewrite VL. destruct (1 <? window); [|lia]. change 32 with (2 ^ 5). apply Z.pow_le_mono_r; lia. }
      assert (WV2 : 0 <= Z.shiftr wv 1 < Z.of_nat (length vals)).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite VL.
        assert (2 ^ (we + 1) <= 2 ^ window) by (apply Z.pow_le_mono_r; lia).
        destruct (Z.ltb_spec 1 window) as [Hw|Hw].
        - assert (2 ^ window = 2 * 2 ^ (window - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
        - assert (we = 0) by lia. subst we. change (2 ^ (0 + 1)) with 2 in WV. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }

      assert (TAIL : forall st1 bs1 m1 OW1 (w1 rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x22' : word),
            kenv LB PL lo B SPv FB s bs OW m (efrMv (Z_to_bv 64 (Z.lxor (FB + 40) 18446744073709551615)) w1 e (Z_to_bv 64 ar) ws) st1 bs1 m1 OW1 -> lib_state bs1 m1 OW1 PL EA -> refs_stable bsK OWK bs1 OW1 ->
            implM bgusegs (interp (embed (tbind (MUL rq rq (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) bs1)
                                             (fun p => (if wstart - (we + 1) <? 0 then bret (tree_ops bptr) tt
                                                        else exp_window_loop (tree_ops bptr) MUL f rp rq vals window (wstart - (we + 1)) false) (snd p))))) st1 (WINQ ws rq ar)
              (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0' t1' t2' (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                        (Z_to_bv 64 am) (Z_to_bv 64 arr) (Z_to_bv 64 (Z.shiftr wv 1)) (Z_to_bv 64 arp) x22' (Z_to_bv 64 we) (Z_to_bv 64 wstart) (Z_to_bv 64 (we + 1)) (Z_to_bv 64 0) (Z_to_bv 64 window) t3' t4' t5' t6')
                  F (Z_to_bv 64 0x150638) fc None m1 (seg_rom bgusegs))).
      { intros until x22'. intros ENV1 LS1 RS1.
        pose proof VT as [VTL VT']. destruct (VT' (Z.to_nat (Z.shiftr wv 1)) ltac:(lia)) as (Wi & HAi & (ji & Ei) & AiR). clear VT'.
        pose proof ENV1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR1 & _). unfold efrMv in FR1.
        destruct (val_frame_splitM m1 FB _ _ _ _ _ ws saved LEN FR1) as (_ & VA & _). clear FR1.
        unfold implM. iprefix.
        ub. step. fload ENV1.
        rewrite (unsigned_lit (Z.shiftr wv 1)) by (clear - WV2 L32; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
        rewrite zb_lxor_ones by (clear - ESPV SPB B63 FBlo CEIL; lia).
        ub_chk.
        do 5 step.
        assert (Wi' : nth_error ws (Z.to_nat (Z.shiftr wv 1)) = Some (Z_to_bv 64 (nth (Z.to_nat (Z.shiftr wv 1)) addrs 0))) by exact Wi.
        let a := cur_mem_addr in pose proof (u64arr_read bgusegs m1 (FB + 40) _ (Z.shiftr wv 1) _ a VA Wi' ltac:(lia) ltac:(addr_tac)) as RD.
        step. clear RD VA Wi'.
        fload ENV1.
        do 4 step.
        destruct (KPRE _ _ _ _ _ CS ENV1 LS1 LOF) as (errv3 & PRE3).
        ihere. to_implM.
        eapply implM_embed_bind.
        { eapply bn_mul_mont_fixed_top_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)
            | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HAi)| rewrite Er; apply wref_pool
            | rewrite Ei; unfold RPool, ROne, NFIX; lia| exact HPM| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV1 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
        cbn [fst snd] in *. clear PRE3 KP.
        replace (ret_pc (Z_to_bv 64 0x150678)) with (Z_to_bv 64 0x150678) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (refs_stable_trans _ _ _ _ _ _ RS1 RS11) as RS011.
        unfold implM. iprefix. step. if_false.
        step. rewrite (unsigned_lit (we + 1)) by (clear - WE WB; lia). ub.
        step. rewrite (swrap32_wrap64 (wstart + - (we + 1)) 0) by (clear - WS WE WB; lia). replace (wstart + - (we + 1) + 0) with (wstart - (we + 1)) by lia.
        step. remember (Z_to_bv 64 1) as one1 eqn:E1. fstore ENV11 LS11 16. subst one1.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m12 end.
        step. rewrite lts_signed by (clear - WS WE WB; lia).
        destruct (Z.ltb_spec (wstart - (we + 1)) 0) as [WLT|WGE]; cbn [negb].
        -
          ihere. to_implM. cbv beta iota. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
          unfold WINQ. do 3 eexists. exists m12, OW11. do 23 eexists. split; [reflexivity|]. cbn [snd]. split; [exact ENV11|]. split; [exact LS11| exact (ref_at_stable _ _ _ _ PL _ _ RS011 HArK)].
        -
          fload ENV11. step. change (Z.land 1 1) with (Z.b2z (negb false)) || idtac.
          ihere. to_implM. cbv beta iota.
          eapply (REC (wstart - (we + 1)) false); [exact ENV11| exact LS11| exact LEN| eapply vtab_stable; [exact VT| exact RS011]| exact VL| exact WB| clear - WGE WF; lia| clear - WS WE; lia
            | exact (ref_at_stable _ _ _ _ PL _ _ RS011 HArK)| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS011 HApK)].
      }
      destruct start; cbn [negb Z.b2z]; [rewrite tbind_bret; cbv beta|];
        unfold implM; iprefix; ub; step; step; unfold v_slt, c_lts; ub_lts; fload ENVK; step; step; step.
      -
        if_true. ihere. to_implM. eapply TAIL; [exact ENVK| exact LSK| apply refs_stable_refl].
      -
        if_false.
        replace (Z.to_nat (we + 1)) with (S (Z.to_nat we)) by (clear - WE; lia).
        replace (Z_to_bv 64 (we + 1)) with (Z_to_bv 64 (Z.of_nat (S (Z.to_nat we)))) by (f_equal; clear - WE; lia).
        ihere. to_implM. eapply implM_embed_bind.
        { eapply sqr_loop; [exact ENVK| exact LSK| exact HArK| exact Er| clear - WE WB; lia]. }
        cbv beta. intros [u1 bs1] st1 ms1 (m1 & OW1 & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV1 & LS1 & RS1). cbn [snd] in *.
        replace (Z_to_bv 64 (Z.of_nat (S (Z.to_nat we)))) with (Z_to_bv 64 (we + 1)) by (f_equal; clear - WE; lia).
        eapply TAIL; [exact ENV1| exact LS1| exact RS1].
    Qed.

    Lemma wl_set : forall f, WLOOP f -> forall (wstart : Z) (start : bool) stK bsK mK OWK (e : word) ws vals addrs (window : Z) (rq : bnref) (ar : Z) (ri : nat)
        (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 x25 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrMv (Z_to_bv 64 (Z.lxor (FB + 40) 18446744073709551615)) (Z_to_bv 64 (Z.b2z (negb start))) e (Z_to_bv 64 ar) ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
      0 <= wstart < Z.of_nat (S f) -> wstart < 2 ^ 24 ->
      ref_at bsK OWK PL rq ar -> rq = RPool ri -> ref_at bsK OWK PL rp arp -> is_bit_set_pure (getbn rp bsK) wstart = true ->
      implM bgusegs (interp (embed (exp_window_loop (tree_ops bptr) MUL (S f) rp rq vals window wstart start bsK))) stK (WINQ ws rq ar)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 arp) (Z_to_bv 64 am) x23 (Z_to_bv 64 wstart) x25 (Z_to_bv 64 window) x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x150540) fc None mK (seg_rom bgusegs)).
    Proof.
      intros f IH. intros until t6; intros ENVK LSK LEN VT VL WB WS WS24 HArK Er HApK EB. kitM.
      destruct (window_scan (is_bit_set_pure (getbn rp bsK)) wstart (Z.to_nat (window - 1)) 1 1 0) as [wv we] eqn:SC.
      rewrite (ewl_set MUL f rp rq vals window wstart start bsK wv we EB SC). cbv beta.
      pose proof (window_scan_bnd (is_bit_set_pure (getbn rp bsK)) wstart (Z.to_nat (window - 1)) 1 1 0
                    ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - WS; lia) ltac:(clear; cbn; lia)) as BND.
      rewrite SC in BND. destruct BND as (WE & WES & WV).
      replace (1 + Z.of_nat (Z.to_nat (window - 1))) with window in WE by (clear - WB; lia).
      unfold implM. iprefix.
      step. if_true.
      step.
      step. if_cases KW; zify_cond KW; rewrite ?unsigned_lit, ?signed_small in KW by (clear - WB; lia).
      -
        assert (W1 : window = 1) by (clear - KW WB; lia). subst window.
        change (Z.to_nat (1 - 1)) with 0%nat in SC. cbn [window_scan] in SC. injection SC as <- <-.
        step. step. step. step.
        ihere. to_implM.
        eapply (after_scan f IH wstart 1 0 start stK bsK _ OWK ws vals addrs 1 rq ar ri e);
          [exact ENVK| exact LSK| exact LEN| exact VT| exact VL| exact WB| clear - WS WS24; lia| clear; lia| clear - WS; lia| clear; cbn; lia| clear - WS; lia
          | exact HArK| exact Er| exact HApK].
      -
        step. step. step.
        eapply (scan_loop (Z.to_nat (window - 1)) 1 1 0 stK bsK _ OWK (Z_to_bv 64 (Z.lxor (FB + 40) 18446744073709551615)) (Z_to_bv 64 (Z.b2z (negb start))) e (Z_to_bv 64 ar) ws wstart window);
          [exact ENVK| exact LSK| exact HApK| clear; lia| clear - WB; lia| clear - KW WB; lia| clear - WB; lia| clear - WS WS24; lia| clear; lia| clear - WS; lia
          | clear; cbn; lia|].
        intros mK' wv' we' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ENV' LS' SC'.
        rewrite SC in SC'. injection SC' as <- <-.
        assert (P7 : 2 ^ (we + 1) <= 2 ^ 7) by (apply Z.pow_le_mono_r; clear - WE WB; lia).
        assert (SHR : 0 <= Z.shiftr wv 1 < 2 ^ 7) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 1) with 2; clear - WV P7; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
        step. rewrite (unsigned_lit wv) by (clear - WV P7; lia). rewrite (bn_swrap32_small wv) by (clear - WV P7; lia).
        rewrite (bn_swrap32_small (Z.shiftr wv 1)) by (clear - SHR; lia).
        step.
        ihere. to_implM.
        eapply (after_scan f IH wstart wv we start stK bsK mK' OWK ws vals addrs window rq ar ri e);
          [exact ENV'| exact LS'| exact LEN| exact VT| exact VL| exact WB| clear - WS WS24; lia| exact WE| exact WES| exact WV| clear - WS WE; lia
          | exact HArK| exact Er| exact HApK].
    Qed.

    Lemma window_loop : forall f, WLOOP f.
    Proof.
      induction f as [|f IH]; unfold WLOOP; intros until t6; intros ENVK LSK LEN VT VL WB WS WS24 HArK Er HApK; [exfalso; clear - WS; lia|]. kitM.

      destruct (kenv_open_u LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rp arp ENVK LSK HApK NROp) as (Dp & BNp & Up & (OKp1 & OKp2 & OKp3 & OKp4) & _ & SEPp & SEPDp & _ & ALp & UPp).
      pose proof ENVK as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OKp3.
      unfold implM. iprefix.
      step. step. step.
      eapply evt_cut.
      { eapply (BN_is_bit_set_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := arp) (D := Dp) (b := getbn rp bsK) (n := wstart);
          [exact BNp | exact ALp | exact UPp | exact Up | exact OKp1 | exact OKp2 | clear - OKp3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS96; lia | exact MIK
          | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDp FBlo FBsp CS96 LOF; lia | reflexivity | reflexivity | clear - WS WS24; lia]. }
      clear STK MIK.
      intros ms2 PO. unfold bn_small_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
      rewrite ESP in *.
      destruct (KBELOW _ _ _ _ m2 _ 16 ENVK LSK ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear MUc WMc MIc STc BNp Up.
      replace (ret_pc (Z_to_bv 64 0x150540)) with (Z_to_bv 64 0x150540) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct (is_bit_set_pure (getbn rp bsK) wstart) eqn:EB; cbn [Z.b2z].
      -
        ihere. to_implM.
        eapply (wl_set f IH wstart start stK bsK m2 OWK e ws vals addrs window rq ar ri);
          [exact ENV2| exact LS2| exact LEN| exact VT| exact VL| exact WB| exact WS| exact WS24| exact HArK| exact Er| exact HApK| exact EB].
      -
        rewrite (ewl_clear MUL f rp rq vals window wstart start bsK EB). cbv beta.
        step. if_false.
        assert (NEXT : forall st1 bs1 m1 OW1 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x23' x25' x27' t3' t4' t5' t6' : word),
              kenv LB PL lo B SPv FB s bs OW m (efrMv (Z_to_bv 64 (Z.lxor (FB + 40) 18446744073709551615)) (Z_to_bv 64 (Z.b2z (negb start))) e (Z_to_bv 64 ar) ws) st1 bs1 m1 OW1 -> lib_state bs1 m1 OW1 PL EA -> refs_stable bsK OWK bs1 OW1 ->
              implM bgusegs (interp (embed ((if wstart =? 0 then bret (tree_ops bptr) tt
                                             else exp_window_loop (tree_ops bptr) MUL f rp rq vals window (wstart - 1) start) bs1))) st1 (WINQ ws rq ar)
                (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0' t1' t2' (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                          (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 arp) (Z_to_bv 64 am) x23' (Z_to_bv 64 wstart) x25' (Z_to_bv 64 window) x27' t3' t4' t5' t6')
                    F (Z_to_bv 64 0x150564) fc None m1 (seg_rom bgusegs))).
        { intros until t6'. intros ENV1 LS1 RS1.
          unfold implM. iprefix.
          destruct (Z.eqb_spec wstart 0) as [W0|WN0].
          -
            subst wstart.
            step. if_true.
            ihere. to_implM. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
            unfold WINQ. do 28 eexists. split; [reflexivity|]. cbn [snd]. split; [exact ENV1|]. split; [exact LS1| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)].
          - step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - WS WS24; lia); zify_cond KZ; [exfalso; clear - KZ WN0; lia|].
            step. rewrite (swrap32_wrap64 wstart (-1)) by (clear - WS WS24; lia). replace (wstart + -1) with (wstart - 1) by (clear; lia).
            hide_ors. ub. unhide.
            step. step.
            ihere. to_implM. unfold WLOOP in IH.
            eapply IH; [exact ENV1| exact LS1| exact LEN| eapply vtab_stable; [exact VT| exact RS1]| exact VL| exact WB| clear - WS WN0; lia| clear - WS24; lia
              | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HApK)]. }
        destruct start; cbn [negb Z.b2z].
        +
          rewrite tbind_bret. cbv beta.
          step. if_true.
          ihere. to_implM. eapply NEXT; [exact ENV2| exact LS2| apply refs_stable_refl].
        +
          step. if_false.
          fload ENV2. do 5 step.
          destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv3 & PRE3). ihere. to_implM.
          eapply implM_embed_bind.
          { eapply bn_mul_mont_fixed_top_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact HArK| exact HArK| exact HArK| rewrite Er; apply wref_pool| rewrite Er; unfold RPool, ROne, NFIX; lia| exact HPM| exact HPC
              | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
          cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
          destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
          cbn [fst snd] in *. clear PRE3 KP.
          replace (ret_pc (Z_to_bv 64 0x150560)) with (Z_to_bv 64 0x150560) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          unfold implM. iprefix. step. if_false.
          ihere. to_implM. eapply NEXT; [exact ENV11| exact LS11| exact RS11].
    Qed.

    Lemma L_loop : forall stK bsK mK OWK (wv : word) ws vals addrs (bits window : Z) (rq : bnref) (ar : Z) (ri : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM wv (Z_to_bv 64 0) (Z_to_bv 64 ar) ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      vtab bsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
      0 < bits < 2 ^ 24 ->
      ref_at bsK OWK PL rq ar -> rq = RPool ri ->
      implM bgusegs (interp (embed (tbind (exp_window_loop (tree_ops bptr) MUL (Z.to_nat bits) rp rq vals window (bits - 1) true bsK)
                                      (fun p => tbind (BN_from_montgomery (tree_ops bptr) rr rq (snd p))
                                         (fun p1 => tbind (BN_MONT_CTX_free (tree_ops bptr) qm (snd p1)) (fun p0 => BN_CTX_end (tree_ops bptr) (snd p0))))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) (Z_to_bv 64 (bits - 1)) x25 (Z_to_bv 64 window) x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15051c) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK LEN VT VL WB BITS HArK Er. kitM.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      eapply implM_embed_bind with (Q1 := WINQ ws rq ar).
      2: { cbv beta. intros [u bsW] stW msW (vW & wW & eW & mW & OWW & R).
           destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENVW & LSW & HAW). cbn [snd] in *.
           eapply mont_exit; [exact ENVW| exact LSW| exact HAW| exact Er]. }
      unfold implM. iprefix.
      fstore ENVK LSK 16.
      step. step.
      rewrite (unsigned_lit (SPv + -360)) by lia. replace (SPv + -360) with (FB + 40) by (clear - ESPV; lia).
      fstore ENVK LSK 8.
      fload ENVK. step.
      ihere. to_implM.
      eapply (window_loop (Z.to_nat bits) (bits - 1) true stK bsK _ OWK (Z_to_bv 64 0) ws vals addrs window rq ar ri);
        [exact ENVK| exact LSK| exact LEN| exact VT| exact VL| exact WB| clear - BITS; lia| clear - BITS; lia| exact HArK| exact Er| exact HApK].
    Qed.

    Lemma vtab_one : forall bsK OWK ws v0 av0 vi, nth_error ws 0 = Some (Z_to_bv 64 av0) -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 ->
      vtab bsK OWK ws [v0] [av0].
    Proof.
      intros bsK OWK ws v0 av0 vi W0 HAv Ev AvR. split; [reflexivity|]. intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by (clear - Hi; lia). subst i. cbn [nth].
      split; [exact W0|]. split; [exact HAv|]. split; [exists vi; exact Ev| exact AvR].
    Qed.

    Lemma L_table : forall stK bsK mK OWK (w e r : word) ws (bits window : Z) (d v0 : bnref) (ad av0 : Z) (di vi : nat) (rq : bnref) (ar : Z)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM w e r ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      nth_error ws 0 = Some (Z_to_bv 64 av0) ->
      ref_at bsK OWK PL d ad -> d = RPool di -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 -> 1 < window <= 6 -> ref_at bsK OWK PL rq ar ->
      implM bgusegs (interp (embed (exp_table (tree_ops bptr) MUL window v0 d bsK))) stK (TABLEQ e r bits window rq ar)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 window) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) x22 (Z_to_bv 64 av0) t3 t4 t5 t6)
            F (Z_to_bv 64 0x150374) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK LEN W0 HAd Ed HAv Ev AvR WB HAq. kitM.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; lia).
      assert (NROv : v0 <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; lia).
      assert (P2 : 2 <= 2 ^ (window - 1) <= 32).
      { split; [change 2 with (2 ^ 1) at 1| change 32 with (2 ^ 5)]; apply Z.pow_le_mono_r; clear - WB; lia. }
      unfold exp_table. replace (1 <? window) with true by (symmetry; apply Z.ltb_lt; clear - WB; lia).
      unfold bbind. cbn [bind tree_ops].
      replace (Z.to_nat (2 ^ (window - 1)) - 1)%nat with (S (Z.to_nat (2 ^ (window - 1)) - 2)) by (clear - P2; lia).
      unfold implM. iprefix.
      do 5 step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply bn_mul_mont_fixed_top_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact HAd| exact HAv| exact HAv| rewrite Ed; apply wref_pool| exact NROv| exact HPM| exact HPC
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 0x15038c)) with (Z_to_bv 64 0x15038c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_false.
      step. fstore ENV11 LS11 16.
      step. step. step. step.
      replace (window + -1) with (window - 1) by (clear; lia).
      replace (SPv + -352) with (FB + 40 + 8 * Z.of_nat (length [v0])) by (cbn [length]; clear - ESPV; lia).
      replace (Z_to_bv 64 2) with (Z_to_bv 64 (Z.of_nat (length [v0]) + 1)) by reflexivity. replace (Z_to_bv 64 31) with (Z_to_bv 64 (32 - Z.of_nat (length [v0]))) by reflexivity.
      ihere. to_implM.
      eapply (table_loop (Z.to_nat (2 ^ (window - 1)) - 2) [v0] [av0] st4 bs4 _ OW11 e r ws bits window d ad rq ar);
        [exact ENV11| exact LS11| exact LEN| | cbn [length]; clear; lia| cbn [length]; clear - P2; lia| exact WB| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAd)| exact NROd| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAq)].
      exact (vtab_one bs4 OW11 ws v0 av0 vi W0 (ref_at_stable _ _ _ _ PL _ _ RS11 HAv) Ev AvR).
    Qed.

    Lemma L_cascade : forall stK bsK mK OWK (w e r0 : word) ws (bits : Z) (d v0 rq : bnref) (ad av0 ar : Z) (di vi : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x26 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM w e r0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      nth_error ws 0 = Some (Z_to_bv 64 av0) ->
      ref_at bsK OWK PL d ad -> d = RPool di -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 -> 0 < bits < 2 ^ 24 ->
      ref_at bsK OWK PL rq ar ->
      (forall window (rv : list bnref * bstate bptr) stT msT, 1 <= window <= 6 -> TABLEQ (Z_to_bv 64 0) (Z_to_bv 64 ar) bits window rq ar rv stT msT ->
           implM bgusegs (interp (embed (mont_gueron bits window rr rp rm rq (fst rv) qm (snd rv)))) stT FINALQ msT) ->
      implM bgusegs (interp (embed (tbind (exp_table (tree_ops bptr) MUL (window_bits bits) v0 d bsK)
                                      (fun p => mont_gueron bits (window_bits bits) rr rp rm rq (fst p) qm (snd p))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) x26 (Z_to_bv 64 av0) t3 t4 t5 t6)
            F (Z_to_bv 64 0x150290) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK LEN W0 HAd Ed HAv Ev AvR BITS HAq GUER. kitM.
      remember (window_bits bits) as window eqn:EW.
      unfold implM. iprefix.
      step.
      fstore ENVK LSK 32. fstore ENVK LSK 24.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
      assert (TBL : forall (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x22' t3' t4' t5' t6' : word), 1 < window <= 6 ->
                implM bgusegs (interp (embed (tbind (exp_table (tree_ops bptr) MUL window v0 d bsK)
                                                (fun p => mont_gueron bits window rr rp rm rq (fst p) qm (snd p))))) stK FINALQ
                  (MS (mkR rax' (Z_to_bv 64 FB) gp (wz RATP) t0' t1' t2' (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                            (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 window) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) x22' (Z_to_bv 64 av0) t3' t4' t5' t6')
                      F (Z_to_bv 64 0x150374) fc None mS (seg_rom bgusegs))).
      { intros until t6'. intros WB.
        eapply implM_embed_bind; [eapply (L_table stK bsK mS OWK w (Z_to_bv 64 0) (Z_to_bv 64 ar) ws bits window d v0 ad av0 di vi rq ar);
                                   [exact ENVK| exact LSK| exact LEN| exact W0| exact HAd| exact Ed| exact HAv| exact Ev| exact AvR| exact WB| exact HAq]|].
        cbv beta. intros rv stT msT PO. eapply GUER; [clear - WB; lia| exact PO]. }
      unfold window_bits in EW.
      step. rewrite lts_signed by (clear - BITS; lia).
      destruct (Z.ltb_spec 671 bits) as [B1|B1]; cbn [negb].
      { step. step. subst window. ihere. to_implM. eapply TBL. clear; lia. }
      step. step. rewrite lts_signed by (clear - BITS; lia).
      destruct (Z.ltb_spec 239 bits) as [B2|B2]; cbn [negb].
      { step. step. subst window. ihere. to_implM. eapply TBL. clear; lia. }
      step. step. rewrite lts_signed by (clear - BITS; lia).
      destruct (Z.ltb_spec 79 bits) as [B3|B3]; cbn [negb].
      { step. step. subst window. ihere. to_implM. eapply TBL. clear; lia. }
      step. step. rewrite lts_signed by (clear - BITS; lia).
      replace (23 <? bits) with (negb (bits <? 24)) in EW by (clear; destruct (Z.ltb_spec bits 24); destruct (Z.ltb_spec 23 bits); cbn; lia).
      destruct (Z.ltb_spec bits 24) as [B4|B4]; cbn [negb] in EW |- *.
      2: { step. subst window. ihere. to_implM. eapply TBL. clear; lia. }

      step. clear TBL.
      subst window.
      replace (exp_table (tree_ops bptr) MUL 1 v0 d bsK) with (bret (tree_ops bptr) [v0] bsK) by reflexivity.
      rewrite tbind_bret. cbv beta. cbn [fst snd].
      ihere. to_implM.
      eapply (GUER 1 ([v0], bsK)); [clear; lia|].
      unfold TABLEQ. exists w, ws, [av0]. do 2 eexists. do 19 eexists. split; [reflexivity|]. cbn [fst snd].
      split; [exact ENVK|]. split; [exact LSK|]. split; [exact LEN|]. split; [exact (vtab_one bsK OWK ws v0 av0 vi W0 HAv Ev AvR)|]. split; [reflexivity| exact HAq].
    Qed.

    Hypothesis HAm : ref_at bs OW PL rm arm.
    Hypothesis NROm : rm <> ROne.

    Definition LOOPQ (x1 x2 x3 x5 x6 x8 x9 x10 x11 : word) (e : word) (ws : list word) (vals : list bnref) (addrs : list Z) (bits window : Z) (rq : bnref) (ar : Z)
        (rv : unit * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists mK' OWK' (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) x1 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7
                      x2 x3 (Z_to_bv 64 ar) x5 x6 (Z_to_bv 64 arm) x8 x9 x10 x11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15051c) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efrM (Z_to_bv 64 window) e (Z_to_bv 64 ar) ws) st' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA
        /\ vtab (snd rv) OWK' ws vals addrs /\ ref_at (snd rv) OWK' PL rq ar.

    Definition GFILL_stmt : Prop := forall (e : word) wsT vals addrsT (bits window : Z) (rq : bnref) (ar : Z) (ri : nat) stT (bsT : bstate bptr) mT OWT
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x1 x2 x3 x5 x6 x8 x10 x11 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM (Z_to_bv 64 window) e (Z_to_bv 64 ar) wsT) stT bsT mT OWT -> lib_state bsT mT OWT PL EA ->
      vtab bsT OWT wsT vals addrsT -> ref_at bsT OWT PL rq ar -> rq = RPool ri -> ref_at bsT OWT PL rm arm -> rq <> rm ->
      (1 <= bn_top (getbn rm bsT))%nat -> Z.testbit (nth (bn_top (getbn rm bsT) - 1) (bn_buf (getbn rm bsT)) 0) 63 = true ->
      implM bgusegs (interp (embed (tbind (bn_wexpand (tree_ops bptr) rq (bn_top (getbn rm bsT)) bsT)
                                      (fun p => bset (tree_ops bptr) rq
                                                  (mkBN (bn_d (getbn rq (snd p)))
                                                        (splice (bn_buf (getbn rq (snd p))) 0 (neg_limbs (firstn (bn_top (getbn rm bsT)) (bn_buf (getbn rm (snd p))))))
                                                        (bn_top (getbn rm bsT)) (bn_neg (getbn rq (snd p))) (bn_flags (getbn rq (snd p)))) (snd p))))) stT
        (LOOPQ x1 x2 x3 x5 x6 x8 (Z_to_bv 64 (Z.of_nat (bn_top (getbn rm bsT)))) x10 x11 e wsT vals addrsT bits window rq ar)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) x1 a0 a1 a2 a3 a4 a5 a6 a7
                  x2 x3 (Z_to_bv 64 ar) x5 x6 (Z_to_bv 64 arm) x8 (Z_to_bv 64 (Z.of_nat (bn_top (getbn rm bsT)))) x10 x11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x150490) fc None mT (seg_rom bgusegs)).

    Definition LOOPQ0 (x1 x2 x3 x5 x6 x8 x9 x10 x11 : word) (e : word) (ws : list word) (vals : list bnref) (addrs : list Z) (bits window : Z) (rq : bnref) (ar : Z)
        (rv : unit * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) x1 a0 a1 a2 a3 a4 a5 a6 a7
                      x2 x3 (Z_to_bv 64 ar) x5 x6 (Z_to_bv 64 arm) x8 x9 x10 x11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15051c) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efrM (Z_to_bv 64 window) e (Z_to_bv 64 ar) ws) st' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA
        /\ vtab (snd rv) OWK' ws vals addrs /\ ref_at (snd rv) OWK' PL rq ar.

    Lemma LOOPQ_0 : forall x1 x2 x3 x5 x6 x8 x9 x10 x11 e ws vals addrs bits window rq ar rv st' ms',
      LOOPQ x1 x2 x3 x5 x6 x8 x9 x10 x11 e ws vals addrs bits window rq ar rv st' ms' ->
      LOOPQ0 x1 x2 x3 x5 x6 x8 x9 x10 x11 e ws vals addrs bits window rq ar rv st' ms'.
    Proof.
      intros until ms'. intros (mK' & OWK' & rax & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & H).
      exists mK', OWK', rax, t0, t1, t2, (Z_to_bv 64 ar), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6. exact H.
    Qed.

    Lemma L_gueron : GFILL_stmt -> forall window (rv : list bnref * bstate bptr) stT msT (bits : Z) (rq : bnref) (ar : Z) (ri : nat),
      1 <= window <= 6 -> 0 < bits < 2 ^ 24 -> rq = RPool ri ->
      TABLEQ (Z_to_bv 64 0) (Z_to_bv 64 ar) bits window rq ar rv stT msT ->
      implM bgusegs (interp (embed (mont_gueron bits window rr rp rm rq (fst rv) qm (snd rv)))) stT FINALQ msT.
    Proof.
      intros GFILL window [vals bsT] stT msT bits rq ar ri WB BITS Er (wv & wsT & addrsT & mT & OWT & R).
      destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & x27T & ? & ? & ? & ? & -> & ENVT & LST & LENT & VTT & VLT & HAqT). cbn [fst snd] in *.
      rewrite <- (Z_to_bv_bv_unsigned wv) in ENVT.
      kitM.
      pose proof ENVT as (_ & _ & _ & _ & _ & _ & _ & _ & RST & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RST HAm) as HAmT.
      destruct (kenv_open_u LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rm arm ENVT LST HAmT NROm) as (Dm & BNm & Um & (OKm1 & OKm2 & OKm3 & OKm4) & Am0 & SEPm & SEPDm & _ & ALm & UPm).
      pose proof (rw_cells_bound _ _ _ _ BNm) as (_ & AMB). cbn in AMB.
      unfold mont_gueron, bbind, bget, bunr. cbn [bind ret unreachable tree_ops tbind fst snd]. cbv beta zeta.
      set (bm := getbn rm bsT) in *.
      destruct (Nat.eqb_spec (bn_top bm) 0) as [T0|TN0]; [cbn [embed interp]; apply implM_interp_unr|].
      eapply implM_embed_bind with (Q1 := LOOPQ0 (Z_to_bv 64 ac) (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 (bits - 1))
                                                (Z_to_bv 64 (Z.of_nat (bn_top bm))) (Z_to_bv 64 window) x27T (Z_to_bv 64 0) wsT vals addrsT bits (bv_unsigned wv) rq ar).
      2: { cbv beta. intros [uL bsL] stL msL (mL & OWL & R).
           destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENVL & LSL & VTL & HAqL). cbn [snd] in *.
           eapply L_loop; [exact ENVL| exact LSL| exact LENT| exact VTL| exact VLT| exact WB| exact BITS| exact HAqL| exact Er]. }
      assert (NROq : rq <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
      assert (TOP : 1 <= Z.of_nat (bn_top bm) <= 512) by (unfold BG_DMAX in OKm3; clear - TN0 OKm2 OKm3; lia).
      assert (NTH : nth_error (wlimbs (bn_buf bm)) (Z.to_nat (Z.of_nat (bn_top bm) - 1)) = Some (Z_to_bv 64 (nth (bn_top bm - 1) (bn_buf bm) 0))).
      { replace (Z.to_nat (Z.of_nat (bn_top bm) - 1)) with (bn_top bm - 1)%nat by (clear - TOP; lia). apply nth_error_wlimbs. unfold bn_dmax in OKm2. clear - TN0 OKm2. lia. }
      assert (LIMB : 0 <= nth (bn_top bm - 1) (bn_buf bm) 0 < 2 ^ 64).
      { assert (Hl : limb (nth (bn_top bm - 1) (bn_buf bm) 0)) by (apply (proj1 (List.Forall_nth limb (bn_buf bm)) OKm1); unfold bn_dmax in OKm2; clear - TN0 OKm2; lia).
        unfold limb, BW in Hl. exact Hl. }
      pose proof ENVT as (_ & _ & STT & _ & MIT & _).
      pose proof (u64arr_bound bgusegs _ _ _ Um) as (D0 & BDm0). rewrite ?wlimbs_len in BDm0.
      assert (BDm : 0 <= Dm /\ Dm + 8 * Z.of_nat (bn_top bm) <= 2 ^ 64) by (unfold bn_dmax in OKm2; clear - D0 BDm0 OKm2; lia).
      unfold implM. iprefix.
      unfold bn_cells in BNm.
      step. rewrite ?(unsigned_lit bits) by (clear - BITS; lia). rewrite ?(swrap32_wrap64 bits (-1)) by (clear - BITS; lia). rewrite ?(bn_swrap32_small (bits + -1)) by (clear - BITS; lia).
      replace (bits + -1) with (bits - 1) by (clear; lia).
      ub1 ub_kind.
      step. unfold MallocRep.wz. rewrite (sx32_small (Z.of_nat (bn_top bm))) by (clear - TOP; lia).
      step. rewrite ?(unsigned_lit (Z.of_nat (bn_top bm))) by (clear - TOP; lia). rewrite ?(swrap32_wrap64 (Z.of_nat (bn_top bm)) (-1)) by (clear - TOP; lia). rewrite ?(bn_swrap32_small (Z.of_nat (bn_top bm) + -1)) by (clear - TOP; lia).
      ub1 ub_kind.
      step.
      step. rewrite ?(unsigned_lit (Z.of_nat (bn_top bm) + -1)) by (clear - TOP; lia). rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 3) with 8.
      assert (DR : 0 <= Dm + (Z.of_nat (bn_top bm) + -1) * 8 < 2 ^ 64) by (clear - BDm TOP; lia).
      step. rewrite ?(unsigned_lit Dm) by (clear - BDm TOP; lia). rewrite ?(unsigned_lit ((Z.of_nat (bn_top bm) + -1) * 8)) by (clear - TOP; lia).
      unfold ub_ptr_ok in UPm. destruct (UPm ltac:(clear - TOP; lia)) as (DP & D8).
      hide_ors. ub. unhide.
      fload ENVT.
      hide_ors. ub. unhide.
      let a := cur_mem_addr in pose proof (u64arr_read bgusegs mT Dm _ (Z.of_nat (bn_top bm) - 1) _ a Um NTH ltac:(clear - TOP; lia) ltac:(addr_tac)) as RD.
      step. clear RD.
      step. rewrite bv_lts_zero_r. rewrite (unsigned_lit (nth (bn_top bm - 1) (bn_buf bm) 0)) by exact LIMB. rewrite <- (testbit_63 _ LIMB).
      destruct (Z.testbit (nth (bn_top bm - 1) (bn_buf bm) 0) 63) eqn:ETB.
      -
        destruct (Nat.eqb_spec rq rm) as [EQ|NEQ]; [ihere; to_implM; cbn [embed interp]; apply implM_interp_unr|].
        ihere. to_implM. unfold GFILL_stmt in GFILL.
        eapply implM_mono; [eapply GFILL; [exact ENVT| exact LST| exact VTT| exact HAqT| exact Er| exact HAmT| exact NEQ| fold bm; clear - TN0; lia| exact ETB]|].
        cbv beta. intros rvL stL msL HL. exact (LOOPQ_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL).
      -
        step.
        eapply evt_cut.
        { eapply (BN_value_one_spec _ (Z_to_bv 64 FB)) with (lo := lo); [rewrite ESP; exact STT| rewrite ESP; clear - LOF CS96; lia| exact MIT]. }
        clear STT MIT BNm Um.
        intros ms2 PO. unfold bn_small_post in PO.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
        rewrite ESP in *.
        destruct (KBELOW _ _ _ _ m2 _ 16 ENVT LST ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear MUc WMc MIc STc.
        replace (ret_pc (Z_to_bv 64 0x150474)) with (Z_to_bv 64 0x150474) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        step. step. step. step. step.
        destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv3 & PRE3). ihere. to_implM.
        eapply implM_post_evt.
        { eapply bn_to_mont_fixed_top_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact HAqT| apply ref_at_one| rewrite Er; apply wref_pool| intros X; discriminate X| exact HPM| exact HPC
            | reflexivity| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
        cbn [fst snd] in *. clear PRE3 KP.
        replace (ret_pc (Z_to_bv 64 0x150488)) with (Z_to_bv 64 0x150488) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        step. if_true.
        apply evt_done. unfold LOOPQ0. exists m11, OW11. do 16 eexists. split; [reflexivity|]. cbn [snd].
        split; [exact ENV11|]. split; [exact LS11|]. split; [exact (vtab_stable _ _ _ _ _ _ _ VTT RS11)| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAqT)].
    Qed.

    Variables (ra_ : bnref) (ara : Z).
    Hypothesis HAa : ref_at bs OW PL ra_ ara.
    Hypothesis NROa : ra_ <> ROne.
    Hypothesis HFT : pl_bn PL0 RTmod = None.

    Lemma L_tomont : GFILL_stmt -> forall stK bsK mK OWK (w e r0 : word) ws (bits : Z) (d v0 rq aa : bnref) (ad av0 ar aaddr : Z) (di vi ri : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM w e r0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      nth_error ws 0 = Some (Z_to_bv 64 av0) ->
      ref_at bsK OWK PL d ad -> d = RPool di -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 -> 0 < bits < 2 ^ 24 ->
      ref_at bsK OWK PL rq ar -> rq = RPool ri -> ref_at bsK OWK PL aa aaddr ->
      implM bgusegs (interp (embed (tbind (bn_to_mont_fixed_top (tree_ops bptr) v0 aa bsK)
                                      (fun p0 => tbind (exp_table (tree_ops bptr) MUL (window_bits bits) v0 d (snd p0))
                                                   (fun p => mont_gueron bits (window_bits bits) rr rp rm rq (fst p) qm (snd p)))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 aaddr) (Z_to_bv 64 av0) t3 t4 t5 t6)
            F (Z_to_bv 64 0x150278) fc None mK (seg_rom bgusegs)).
    Proof.
      intros GF. intros until t6; intros ENVK LSK LEN W0 HAd Ed HAv Ev AvR BITS HAq Er HAaa. kitM.
      unfold implM. iprefix.
      step. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply bn_to_mont_fixed_top_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact HAv| exact HAaa| rewrite Ev; apply wref_pool| intros X; discriminate X| exact HPM| exact HPC
          | reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 0x15028c)) with (Z_to_bv 64 0x15028c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. if_false.
      ihere. to_implM.
      eapply (L_cascade st4 bs4 m11 OW11 w e r0 ws bits d v0 rq ad av0 ar di vi);
        [exact ENV11| exact LS11| exact LEN| exact W0| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAd)| exact Ed| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAv)| exact Ev| exact AvR| exact BITS
        | exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAq)|].
      intros window rv stT msT WB TQ. eapply (L_gueron GF); [exact WB| exact BITS| exact Er| exact TQ].
    Qed.

    Definition TOMQ (w e r0 : word) (ws : list word) (d v0 rq : bnref) (ad av0 ar bits : Z)
        (rv : bnref * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists mK' OWK' (aaddr : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 aaddr) (Z_to_bv 64 av0) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x150278) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efrM w e r0 ws) st' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA
        /\ ref_at (snd rv) OWK' PL d ad /\ ref_at (snd rv) OWK' PL v0 av0 /\ ref_at (snd rv) OWK' PL rq ar /\ ref_at (snd rv) OWK' PL (fst rv) aaddr.

    Lemma L_nnmod : forall stK bsK mK OWK (w e r0 : word) ws (bits : Z) (d v0 rq : bnref) (ad av0 ar : Z) (vi : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM w e r0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL d ad -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> ref_at bsK OWK PL rq ar ->
      implM bgusegs (interp (embed (tbind (BN_nnmod (tree_ops bptr) v0 ra_ rm bsK) (fun p0 => TRet (v0, snd p0))))) stK (TOMQ w e r0 ws d v0 rq ad av0 ar bits)
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 ara) (Z_to_bv 64 av0) t3 t4 t5 t6)
            F (Z_to_bv 64 0x15025c) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK HAd HAv Ev HAq. kitM.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAa) as HAaK.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK.
      unfold implM. iprefix.
      step. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_nnmod_walk; [exact PRE3| reflexivity| exact HAv| exact HAaK| exact HAmK| rewrite Ev; apply hpl_pool| exact NROa| exact NROm| exact HPC
          | reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 0x150270)) with (Z_to_bv 64 0x150270) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix. step. step. if_false.
      ihere. cbn [embed interp]. apply implM_interp_ret. apply evt_done.
      unfold TOMQ. exists m11, OW11, av0. do 16 eexists. split; [reflexivity|]. cbn [fst snd].
      split; [exact ENV11|]. split; [exact LS11|]. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAd)|]. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAv)|].
      split; [exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAq)| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAv)].
    Qed.

    Lemma L_tail : GFILL_stmt -> forall stK bsK mK OWK (w e r0 : word) ws (bits : Z) (d v0 rq : bnref) (ad av0 ar : Z) (di vi ri : nat)
        (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM w e r0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      nth_error ws 0 = Some (Z_to_bv 64 av0) ->
      ref_at bsK OWK PL d ad -> d = RPool di -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 -> 0 < bits < 2 ^ 24 ->
      ref_at bsK OWK PL rq ar -> rq = RPool ri ->
      implM bgusegs (interp (embed (mont_tail bits rr ra_ rp rm d rq v0 qm bsK))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 arp) (Z_to_bv 64 am) (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 ara) (Z_to_bv 64 av0) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1502f0) fc None mK (seg_rom bgusegs)).
    Proof.
      intros GF. intros until t6; intros ENVK LSK LEN W0 HAd Ed HAv Ev AvR BITS HAq Er. kitM.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAa) as HAaK.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK.
      destruct (kenv_open_u LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ ra_ ara ENVK LSK HAaK NROa) as (Da & BNa & _ & (_ & _ & _ & OKa4) & _ & _ & _ & _ & ALa & _).
      pose proof (rw_cells_bound _ _ _ _ BNa) as (_ & AAB). cbn in AAB.
      destruct (KOPEN _ _ _ _ _ rm arm ENVK LSK HAmK NROm) as (Dm & _ & _ & (_ & _ & _ & OKm4) & _ & _ & _ & _).
      assert (CTa : has_flag (getbn ra_ bsK) BN_FLG_CONSTTIME = false) by (unfold has_flag, BN_FLG_CONSTTIME; destruct OKa4 as [E|E]; rewrite E; reflexivity).
      assert (CTm : has_flag (getbn rm bsK) BN_FLG_CONSTTIME = false) by (unfold has_flag, BN_FLG_CONSTTIME; destruct OKm4 as [E|E]; rewrite E; reflexivity).
      clear OKa4 OKm4.
      unfold mont_tail, bbind, bget, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
      unfold implM. iprefix.
      step. if_true.
      hide_ors. ub. unhide.
      unfold bn_cells in BNa.
      step. clear BNa.

      assert (JOIN : forall (rv : bnref * bstate bptr) stJ msJ, TOMQ w e r0 ws d v0 rq ad av0 ar bits rv stJ msJ ->
                implM bgusegs (interp (embed (tbind (bn_to_mont_fixed_top (tree_ops bptr) v0 (fst rv) (snd rv))
                                                (fun p1 => tbind (exp_table (tree_ops bptr) MUL (window_bits bits) v0 d (snd p1))
                                                   (fun p2 => mont_gueron bits (window_bits bits) rr rp rm rq (fst p2) qm (snd p2)))))) stJ FINALQ msJ).
      { intros [aa bsJ] stJ msJ (mJ & OWJ & aaddr & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENVJ & LSJ & HAdJ & HAvJ & HAqJ & HAaaJ). cbn [fst snd] in *.
        eapply (L_tomont GF stJ bsJ mJ OWJ w e r0 ws bits d v0 rq aa ad av0 ar aaddr di vi ri);
          [exact ENVJ| exact LSJ| exact LEN| exact W0| exact HAdJ| exact Ed| exact HAvJ| exact Ev| exact AvR| exact BITS| exact HAqJ| exact Er| exact HAaaJ]. }
      destruct (bn_neg (getbn ra_ bsK)) eqn:ENa; cbn [Z.b2z orb].
      -
        step. if_true.
        unfold BN_ucmp, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd]. cbv beta.
        rewrite CTa, CTm. cbn [orb tbind fst snd]. cbv beta.
        ihere. to_implM.
        eapply implM_embed_bind with (Q1 := TOMQ w e r0 ws d v0 rq ad av0 ar bits); [|cbv beta; intros rv stJ msJ PO; exact (JOIN rv stJ msJ PO)].
        eapply (L_nnmod stK bsK mK OWK w e r0 ws bits d v0 rq ad av0 ar vi); [exact ENVK| exact LSK| exact HAd| exact HAv| exact Ev| exact HAq].
      -
        step. if_false.
        step. step. step.
        destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3). ihere. to_implM.
        eapply implM_embed_bind.
        { eapply BN_ucmp_walk; [exact PRE3| reflexivity| exact HAaK| exact HAmK| exact NROa| exact NROm| reflexivity| reflexivity]. }
        cbv beta. intros [c bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [[E _] _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & ((_ & -> & CR & Ebs & EOW) & Ec)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11).
        cbn [fst snd] in *. subst bs4 OW11. clear PRE3 KP Ec.
        replace (ret_pc (Z_to_bv 64 0x150258)) with (Z_to_bv 64 0x150258) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        step. rewrite lts_signed by (clear - CR; lia).
        destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
        +
          replace (0 <=? c) with false by (symmetry; apply Z.leb_gt; exact CN).
          cbn [tbind fst snd]. cbv beta.
          ihere. to_implM.
          eapply (JOIN (ra_, bsK)).
          unfold TOMQ. exists m11, OWK, ara. do 16 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV11|]. split; [exact LS11|]. split; [exact HAd|]. split; [exact HAv|]. split; [exact HAq| exact HAaK].
        +
          replace (0 <=? c) with true by (symmetry; apply Z.leb_le; exact CP).
          ihere. to_implM.
          eapply implM_embed_bind with (Q1 := TOMQ w e r0 ws d v0 rq ad av0 ar bits); [|cbv beta; intros rv stJ msJ PO; exact (JOIN rv stJ msJ PO)].
          eapply (L_nnmod st4 bsK m11 OWK w e r0 ws bits d v0 rq ad av0 ar vi); [exact ENV11| exact LS11| exact HAd| exact HAv| exact Ev| exact HAq].
    Qed.

    Lemma L_set : GFILL_stmt -> forall stK bsK mK OWK (w e r0 : word) ws (bits : Z) (d v0 rq : bnref) (ad av0 ar : Z) (di vi ri : nat)
        (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrM w e r0 ws) stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> length ws = 32%nat ->
      nth_error ws 0 = Some (Z_to_bv 64 av0) ->
      ref_at bsK OWK PL d ad -> d = RPool di -> ref_at bsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 -> 0 < bits < 2 ^ 24 ->
      ref_at bsK OWK PL rq ar -> rq = RPool ri ->
      implM bgusegs (interp (embed (tbind (BN_MONT_CTX_set (tree_ops bptr) rm bsK) (fun p => mont_tail bits rr ra_ rp rm d rq v0 qm (snd p))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) (Z_to_bv 64 am) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 arp) x22 (Z_to_bv 64 arm) (Z_to_bv 64 ad) (Z_to_bv 64 bits) (Z_to_bv 64 ara) (Z_to_bv 64 av0) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1502dc) fc None mK (seg_rom bgusegs)).
    Proof.
      intros GF. intros until t6; intros ENVK LSK LEN W0 HAd Ed HAv Ev AvR BITS HAq Er. kitM.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK.
      unfold implM. iprefix.
      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AMR; lia); zify_cond KZ; [exfalso; clear - KZ AMR; lia| clear KZ].
      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv3 & PRE3). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_MONT_CTX_set_walk; [exact PRE3| reflexivity| rewrite ESP; exact FB16| exact HAmK| exact NROm| exact HPM| exact HPC| exact HFT| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros vv b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m11 & OW11 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV11 & LS11). pose proof KP as RS11; apply kpost_refs in RS11.
      cbn [fst snd] in *. clear PRE3 KP.
      replace (ret_pc (Z_to_bv 64 0x1502f0)) with (Z_to_bv 64 0x1502f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (L_tail GF st4 bs4 m11 OW11 w e r0 ws bits d v0 rq ad av0 ar di vi ri);
        [exact ENV11| exact LS11| exact LEN| exact W0| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAd)| exact Ed| exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAv)| exact Ev| exact AvR| exact BITS
        | exact (ref_at_stable _ _ _ _ PL _ _ RS11 HAq)| exact Er].
    Qed.

  End Body.

  Definition GFILL_all : Prop := forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo B : Z) (s : PState) (bs : bstate bptr)
      (OW LB : list block) (m : mem) (PL0 : placement) (EA : BnRep.err_addrs) (arr arp ac : Z) (qc : bptr) (am : Z) (qm : bptr) (FB SPv : Z) (jz jv : word) (rm : bnref) (arm : Z),
    SPv = FB + 400 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= FB -> FB <= SPv -> SPv <= B -> B < 2^63 -> SPv < 2^64 -> frames_ok PL0 SPv B -> lo <= FB - CS ->
    pl_ctx PL0 = Some (ac, qc) -> pl_mont PL0 = None -> 0 < am < 2^63 ->
    ref_at bs OW (pl_set_mont PL0 (Some (am, qm))) rm arm -> rm <> ROne ->
    GFILL_stmt ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL0 EA am qm FB SPv jz jv rm arm.

  Lemma BN_mod_exp_mont_walk_gf : GFILL_all -> exp_stmt_f BN_MOD_EXP_MONT BN_MOD_EXP_MONT_STACK (BN_mod_exp_mont (tree_ops bptr)) (Some (wz 0)).
  Proof.
    intros GFA. unfold exp_stmt_f. intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAa HAp HAm WRr NROa NROp NROm HPC HFR -> -> -> -> -> A5.
    pose proof (A5 _ eq_refl) as E5. subst a5. clear A5.
    unfold BN_MOD_EXP_MONT_STACK, BN_MOD_EXP_MONT, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 400, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    rewrite BN_mod_exp_mont_eq. unfold any_consttime, BN_num_bits, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd fold_right]. cbv beta.
    unfold implM. iprefix.

    carve_frame 400%nat ST. do 22 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    lazymatch type of FR with rw_cells _ _ _ (CB 296 ?jk :: ?post) =>
      pose proof (rw_cells_split_CB bgusegs m1 (bv_unsigned sp + -400) [] 296 jk post [8; 8; 8; 8; 8; 256]%nat FR eq_refl) as FR'; clear FR; rename FR' into FR;
      cbn [mk_CB_cells app] in FR
    end.
    destruct (cb8x5_c8 _ _ _ _ _ _ _ _ FR) as (jz0 & jv0 & w0 & e0 & r0 & FR'). clear FR. rename FR' into FR.
    lazymatch type of FR with rw_cells _ _ _ (C8 _ :: C8 _ :: C8 _ :: C8 _ :: C8 _ :: CB 256 ?c :: _) => set (vj := c) in FR; clearbody vj end.
    clear junk.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -400, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -400, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -400) by lia.
    assert (FBsp : bv_unsigned sp + -400 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (kenv_open LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL FROK) as KOPEN.
    pose proof (kenv_open_u LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL FROK) as KOPENU.
    pose proof (kenv_below LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KBELOW.
    assert (LOF : lo <= bv_unsigned sp + -400 - CS) by lia.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -400)) = bv_unsigned sp + -400) by (apply unsigned_lit; lia).
    assert (FB16 : (bv_unsigned sp + -400) mod 16 = 0) by (clear - SP16; lia).
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR LS.

    destruct (KOPENU _ _ _ _ _ rm arm ENV LS1 HAm NROm) as (Dm0 & BNm0 & Um0 & (OKm1 & OKm2 & OKm3 & OKm4) & _ & SEPm0 & SEPDm0 & _ & ALm & UPm).
    set (bm := getbn rm bs) in *.
    assert (FLm : 0 <= bn_flags bm <= 1) by (destruct OKm4 as [E|E]; rewrite E; lia).
    assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
    pose proof ENV as (_ & _ & ST1 & _ & MI1 & _).
    pose proof (rw_cells_bound _ _ _ _ BNm0) as (_ & AMB). cbn in AMB.
    eapply evt_cut.
    { eapply (BN_is_odd_spec _ (Z_to_bv 64 (bv_unsigned sp + -400))) with (lo := lo) (A := arm) (D := Dm0) (b := bm);
        [exact BNm0 | exact ALm | exact UPm | exact Um0 | exact OKm1 | exact OKm2 | clear - OKm3; unfold BG_DMAX in OKm3; lia | rewrite ESP; exact ST1 | rewrite ESP; clear - LOF CS96; lia | exact MI1
        | rewrite ESP; clear - SEPm0 FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDm0 FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST1 MI1.
    intros ms1b PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1b & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (KBELOW _ _ _ _ m1b _ 16 ENV LS1 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENVb & LSb). clear ENV LS1 MUc WMc MIc STc BNm0 Um0 SEPm0 SEPDm0.
    rename ENVb into ENV. rename LSb into LS1.
    replace (ret_pc (Z_to_bv 64 0x150138)) with (Z_to_bv 64 0x150138) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (is_odd_pure bm) eqn:ODD; cbn [Z.b2z negb].
    2: {
         step. if_true. ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    step. if_false.
    hide_ors. ub. unhide.

    destruct (KOPEN _ _ _ _ _ rm arm ENV LS1 HAm NROm) as (Dm0' & BNm0 & _ & _ & _ & _ & _ & _). fold bm in BNm0.
    unfold bn_cells in BNm0.
    step. clear BNm0.
    unfold MallocRep.wz. rewrite (sx32_small (Z.of_nat (bn_top bm))) by (clear - OKm2 OKm3; unfold BG_DMAX in OKm3; lia).
    step. step. step.
    rewrite lts_signed by (clear - OKm2 OKm3; unfold BG_DMAX in OKm3; lia).
    replace (1048575 <? Z.of_nat (bn_top bm)) with false by (symmetry; apply Z.ltb_ge; clear - OKm2 OKm3; unfold BG_DMAX in OKm3; lia).

    destruct (KOPENU _ _ _ _ _ rp arp ENV LS1 HAp NROp) as (Dp & BNp & Up & (OKp1 & OKp2 & OKp3 & OKp4) & _ & SEPp & SEPDp & _ & ALp & UPp).
    set (bp := getbn rp bs) in *.
    assert (FLp : 0 <= bn_flags bp <= 1) by (destruct OKp4 as [E|E]; rewrite E; lia).
    assert (CTp : Z.land (bn_flags bp) 4 = 0) by (destruct OKp4 as [E|E]; rewrite E; reflexivity).
    pose proof ENV as (_ & _ & ST1 & _ & MI1 & _).
    step. step. step.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -400))) with (lo := lo) (A := arp) (D := Dp) (b := bp);
        [exact BNp | exact ALp | clear - FLp; lia | rewrite ESP; exact ST1 | rewrite ESP; clear - LOF CS96; lia | exact MI1 | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST1 MI1.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit 4) by lia. rewrite CTp.
    replace (bv_unsigned sp + -400 - 16) with (bv_unsigned sp + -400 - 16) in MUc by reflexivity.
    destruct (KBELOW _ _ _ _ m2 _ 16 ENV LS1 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear ENV LS1 MUc WMc MIc STc BNp Up.
    replace (ret_pc (Z_to_bv 64 0x150164)) with (Z_to_bv 64 0x150164) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_false.

    destruct (KOPENU _ _ _ _ _ ra_ ara ENV2 LS2 HAa NROa) as (Da & BNa & Ua & (OKa1 & OKa2 & OKa3 & OKa4) & _ & SEPa & SEPDa & _ & ALa & UPa).
    set (ba := getbn ra_ bs) in *.
    assert (FLa : 0 <= bn_flags ba <= 1) by (destruct OKa4 as [E|E]; rewrite E; lia).
    assert (CTa : Z.land (bn_flags ba) 4 = 0) by (destruct OKa4 as [E|E]; rewrite E; reflexivity).
    pose proof ENV2 as (_ & _ & ST2 & _ & MI2 & _).
    step. step. step.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -400))) with (lo := lo) (A := ara) (D := Da) (b := ba);
        [exact BNa | exact ALa | clear - FLa; lia | rewrite ESP; exact ST2 | rewrite ESP; clear - LOF CS96; lia | exact MI2 | rewrite ESP; clear - SEPa FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST2 MI2.
    intros ms3 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit 4) by lia. rewrite CTa.
    destruct (KBELOW _ _ _ _ m3 _ 16 ENV2 LS2 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV3 & LS3). clear ENV2 LS2 MUc WMc MIc STc BNa Ua.
    replace (ret_pc (Z_to_bv 64 0x150174)) with (Z_to_bv 64 0x150174) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_false.

    destruct (KOPENU _ _ _ _ _ rm arm ENV3 LS3 HAm NROm) as (Dm & BNm & Um & _ & _ & SEPm & SEPDm & _ & ALm2 & UPm2). fold bm in BNm, Um, SEPDm.
    pose proof ENV3 as (_ & _ & ST3 & _ & MI3 & _).
    step. step. step.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -400))) with (lo := lo) (A := arm) (D := Dm) (b := bm);
        [exact BNm | exact ALm2 | clear - FLm; lia | rewrite ESP; exact ST3 | rewrite ESP; clear - LOF CS96; lia | exact MI3 | rewrite ESP; clear - SEPm FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST3 MI3.
    intros ms4 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit 4) by lia. rewrite CTm.
    destruct (KBELOW _ _ _ _ m4 _ 16 ENV3 LS3 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV4 & LS4). clear ENV3 LS3 MUc WMc MIc STc BNm Um.
    replace (ret_pc (Z_to_bv 64 0x150184)) with (Z_to_bv 64 0x150184) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_true.
    unfold has_flag, BN_FLG_CONSTTIME. fold bp ba bm. rewrite CTa, CTp, CTm. cbn [Z.eqb negb orb andb].

    destruct (KOPENU _ _ _ _ _ rp arp ENV4 LS4 HAp NROp) as (Dp' & BNp & Up & _ & _ & _ & SEPDp' & _ & ALp' & UPp'). fold bp in BNp, Up, SEPDp', UPp'.
    pose proof ENV4 as (_ & _ & ST4 & _ & MI4 & _).
    step. step.
    eapply evt_cut.
    { eapply (BN_num_bits_spec _ (Z_to_bv 64 (bv_unsigned sp + -400))) with (lo := lo) (A := arp) (D := Dp') (b := bp);
        [exact BNp | exact ALp' | exact UPp' | exact Up | exact OKp1 | exact OKp2 | clear - OKp3; unfold BG_DMAX in OKp3; lia | clear - FLp; lia | exact CTp
        | rewrite ESP; exact ST4 | rewrite ESP; clear - LOF CS96; lia | exact MI4
        | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDp' FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST4 MI4.
    intros ms5 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (KBELOW _ _ _ _ m5 _ 128 ENV4 LS4 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV5 & LS5). clear ENV4 LS4 MUc WMc MIc STc BNp Up.
    replace (ret_pc (Z_to_bv 64 0x1501f4)) with (Z_to_bv 64 0x1501f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (num_bits_pure_range bp OKp1) as BITS. unfold BG_DMAX in OKp3.
    replace (getbn rp bs) with bp by reflexivity. rewrite CTp. cbn [Z.eqb negb tbind]. cbv beta.
    set (bits := num_bits_pure bp) in *.
    step. if_cases KB; rewrite ?unsigned_lit in KB by (clear - BITS; lia); zify_cond KB.
    {
      cbn [fst snd]. rewrite KB. cbn [Z.eqb]. unfold exp_bits0, bbind, bget. cbn [bind ret tree_ops tbind fst snd].
      replace (getbn rm bs) with bm by reflexivity.
      destruct (KOPENU _ _ _ _ _ rm arm ENV5 LS5 HAm NROm) as (Dm' & BNm & Um & _ & _ & _ & SEPDm' & _ & ALm' & UPm'). fold bm in BNm, Um, SEPDm', UPm'.
      pose proof ENV5 as (_ & _ & ST5 & _ & MI5 & _).
      step. step. step. step.
      eapply evt_cut.
      { eapply (BN_abs_is_word_spec _ (Z_to_bv 64 (bv_unsigned sp + -400))) with (lo := lo) (A := arm) (D := Dm') (b := bm);
          [exact BNm | exact ALm' | exact UPm' | exact Um | exact OKm1 | exact OKm2 | clear - OKm3; unfold BG_DMAX in OKm3; lia
          | rewrite ESP; exact ST5 | rewrite ESP; clear - LOF CS96; lia | exact MI5
          | rewrite ESP; clear - SEPm FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDm' FBlo FBsp CS96 LOF; lia | reflexivity]. }
      clear ST5 MI5.
      intros ms6 PO. unfold bn_small_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MUc & WMc & MIc & STc & ->).
      rewrite ESP in *. rewrite (unsigned_lit 1) by lia.
      destruct (KBELOW _ _ _ _ m6 _ 16 ENV5 LS5 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV6 & LS6). clear ENV5 LS5 MUc WMc MIc STc BNm Um.
      replace (ret_pc (Z_to_bv 64 0x1502b8)) with (Z_to_bv 64 0x1502b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct (abs_is_word_pure bm 1); cbn [Z.b2z].
      -
        step. if_false. step. step.
        eapply (zero_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
          [clear - LOF CS96; lia | reflexivity | exact ENV6 | exact LS6 | exact HAr | exact (hpl_wref _ _ WRr) |].
        intros m7 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV7 LS7.
        replace (ret_pc (Z_to_bv 64 0x1502c4)) with (Z_to_bv 64 0x1502c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        ihere. to_implM. unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
        pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m _ _ _ _ _ ENV7) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
        step. step. do 13 step. release_frame FRF STF (bv_unsigned sp). step. step.
        apply evt_done. unfold bn_post. do 15 eexists. exists m7, OW, PL, errvF. split; [reflexivity|]. cbn [fst snd].
        split; [exact F1|]. split; [exact LS7|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
        split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
      -
        step. if_true. step. step.
        pose proof ENV6 as (_ & _ & ST6 & _ & _ & _ & _ & _ & _ & FR6 & _).
        do 13 step. release_frame FR6 ST6 (bv_unsigned sp). step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
        ihere. to_implM. unfold BN_one.
        destruct (kenv_tail LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK
                    _ _ _ mX OW CS errv ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                    (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1)
                    ENV6 LS6 ST6 ltac:(clear - LO; lia)) as [[errvX PREX] POSTX].
        rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
        eapply implM_mono; [eapply BN_set_word_walk; [exact PREX| reflexivity| exact HAr| exact (hpl_wref _ _ WRr)| unfold BW; lia| reflexivity| reflexivity]|].
        cbv beta. intros r st' ms' PO. apply POSTX. revert PO. unfold bn_post.
        intros (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m9 & OW9 & PL9 & errv9 & -> & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & (E1 & E2 & _)).
        do 15 eexists. exists m9, OW9, PL9, errv9. split; [reflexivity|].
        split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
        split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact E1| exact E2]. }

    cbn [fst snd]. replace (bits =? 0) with false by (symmetry; apply Z.eqb_neq; exact KB).
    assert (BITS24 : 0 < bits < 2 ^ 24) by (clear - KB BITS OKp2 OKp3; lia).
    destruct HFR as (HF1 & HF2 & HF3 & HFM & HFT).
    unfold mont_rest, bbind. cbn [bind tree_ops tbind fst snd]. cbv beta.

    step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_start_walk; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & OW7 & -> & KP & (_ & INCL7)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV7 & LS7). pose proof KP as RS7; apply kpost_refs in RS7.
    cbn [fst snd] in *. clear PRE1 KP ENV5 LS5.
    replace (ret_pc (Z_to_bv 64 0x150204)) with (Z_to_bv 64 0x150204) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV7 LS7 LOF) as (errv2 & PRE2).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [d bs2] st2 ms2 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & OW8 & -> & KP & (_ & (di & Ed) & (ad & HAd & ->) & INCL8)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV7 KP) as (ENV8 & LS8). pose proof KP as RS8; apply kpost_refs in RS8.
    cbn [fst snd] in *. clear PRE2 KP ENV7 LS7.
    replace (ret_pc (Z_to_bv 64 0x15020c)) with (Z_to_bv 64 0x15020c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV8 LS8 LOF) as (errv2b & PRE2).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [rq bs2b] st2b ms2b PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8b & OW8b & -> & KP & (_ & (ri & Er) & (ar & HAq & ->) & INCL8b)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV8 KP) as (ENV8b & LS8b). pose proof KP as RS8b; apply kpost_refs in RS8b.
    cbn [fst snd] in *. clear PRE2 KP ENV8 LS8.
    replace (ret_pc (Z_to_bv 64 0x150218)) with (Z_to_bv 64 0x150218) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV8b LS8b LOF) as (errv3 & PRE3).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE3| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [v0 bs3] st3 ms3 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & OW9 & -> & KP & (_ & (vi & Ev0) & (av0 & HAv0 & ->) & INCL9)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV8b KP) as (ENV9 & LS9). pose proof KP as RS9; apply kpost_refs in RS9.
    cbn [fst snd] in *. clear PRE3 KP ENV8b LS8b.
    replace (ret_pc (Z_to_bv 64 0x150224)) with (Z_to_bv 64 0x150224) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    pose proof (ref_at_stable _ _ _ _ PL _ _ (refs_stable_trans _ _ _ _ _ _ RS8b RS9) HAd) as HAd9.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS9 HAq) as HAq9.
    pose proof ENV9 as (HEAP9 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS9) as PARTS9.
    assert (FROK9 : frames_ok PL (bv_unsigned sp + -400) B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
    assert (NROv0 : v0 <> ROne) by (rewrite Ev0; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP9 PARTS9 FROK9 HAv0 NROv0) as (Av0 & AvC & _).
    assert (AvR : 0 < av0 < 2^64) by (clear - Av0 AvC SPR; lia). clear AvC.

    pose proof ENV9 as (_ & _ & ST9 & _ & MI9 & _ & _ & _ & _ & FR9 & _).
    pose proof (munch_refl [(bv_unsigned sp + -400 + 40, bv_unsigned sp + -400 + 48)]%Z m9) as MU. pose proof (wmono_refl bgusegs m9) as WM.
    unfold implM. iprefix. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
    destruct (val_frame_initM m10 _ _ _ _ _ _ _ _ _ FR9) as (ws0 & LEN0 & WS0 & FR10).
    assert (HWL : Forall (w_lib bs3 OW9 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -400 + 40, bv_unsigned sp + -400 + 48)]) by (constructor; [left; cbn; lia| constructor]).
    pose proof ENV9 as (_ & _ & _ & (errv9 & ERR9) & _).
    eapply (rw_cells_transport bgusegs _ m9 m10) in ERR9; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; unfold LX_ERRNO, RATP; lia| exact I]].
    pose proof (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL GLO' FBlo FBsp SPB FROK _ _ st3 bs3 m9 m10 OW9 _ errv9
                  ENV9 PARTS9 MU WM HWL ST9 ERR9 ltac:(the_mi) FR10 ltac:(cbn; lia)) as ENV10.
    assert (LS10 : lib_state bs3 m10 OW9 PL EA).
    { assert (WOK : Forall (w_ok OW9 LB bs3 PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -400 + 40, bv_unsigned sp + -400 + 48)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
      exact (lib_state_frame st3 LB _ _ [] bs3 m9 m10 OW9 PL EA _ HEAP9 LS9 MU WM FROK WOK). }
    clear ST9 MI9 FR9 MU WM HWL ERR9 ENV9 LS9 FR10 HEAP9 PARTS9.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].
    step. step.

    step. if_true.
    step.
    destruct (KPRE _ _ _ _ _ CS ENV10 LS10 LOF) as (errv4 & PRE4).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (BN_MONT_CTX_new_lwalk_cs HM CS CSnew); [exact PRE4| reflexivity| exact HFM]. }
    cbv beta. intros [pm bs5] st5 ms5 PO. unfold bn_post in PO. rewrite ESP in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m11 & OW11 & PL' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & (am & -> & -> & AMR & -> & Ebs5)).
    cbn [fst snd] in *. subst bs5.

    set (PLm := pl_set_mont PL (Some (am, pm))) in *.
    assert (KP1 : kpost LB PLm EA lo B (bv_unsigned sp + -400) st3 bs3 m10 OW9 st5 (st_mont_init bs3) m11 ((pm, am, 96) :: OW9)).
    { unfold kpost. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exists errv'; exact P5|]. split; [exact P6|].
      split; [exact P7|]. split; [exact P8|]. split; [exact P9| exact P10]. }
    destruct (kenv_post LB PLm EA lo B (bv_unsigned sp) (bv_unsigned sp + -400) s bs OW m CEIL GLO' FBlo FBsp FROK _ _ _ _ _ _ _ _ _ ENV10 KP1) as (ENV11 & LS11).
    clear PRE4 KP1 P1 P2 P3 P4 P5 P6 P7 P8 P9.
    replace (ret_pc (Z_to_bv 64 0x1502dc)) with (Z_to_bv 64 0x1502dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (ESPV : bv_unsigned sp = bv_unsigned sp + -400 + 400) by (clear; lia).
    pose proof (ref_at_mont_fresh bs OW PL (Some (am, pm)) rm arm HFM HAm) as HAm'.
    pose proof (GFA ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL EA arr arp ac qc am pm (bv_unsigned sp + -400) (bv_unsigned sp) jz0 jv0 rm arm
                  ESPV CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK LOF HPC HFM AMR HAm' NROm) as GF.
    pose proof (L_set ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL EA rr rp arr arp ac qc am pm (bv_unsigned sp + -400) (bv_unsigned sp) jz0 jv0
                  ESPV CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK LOF HPC HFM AMR FB16
                  (ref_at_mont_fresh bs OW PL (Some (am, pm)) rr arr HFM HAr) WRr rm arm
                  (ref_at_mont_fresh bs OW PL (Some (am, pm)) rp arp HFM HAp) NROp HAm' NROm ra_ ara
                  (ref_at_mont_fresh bs OW PL (Some (am, pm)) ra_ ara HFM HAa) NROa HFT GF
                  st5 (st_mont_init bs3) m11 ((pm, am, 96) :: OW9) w0 e0 r0 ws0 bits d v0 rq ad av0 ar di vi ri) as LN.
    unfold FINALQ in LN. rewrite (Z_to_bv_bv_unsigned sp) in LN.
    eapply LN; [exact ENV11| exact LS11| exact LEN0| exact WS0
               | exact (ref_at_mont_fresh _ _ PL (Some (am, pm)) _ _ HFM (ref_at_stable _ _ _ _ PL _ _ P10 HAd9))| exact Ed
               | exact (ref_at_mont_fresh _ _ PL (Some (am, pm)) _ _ HFM (ref_at_stable _ _ _ _ PL _ _ P10 HAv0))| exact Ev0| exact AvR| exact BITS24
               | exact (ref_at_mont_fresh _ _ PL (Some (am, pm)) _ _ HFM (ref_at_stable _ _ _ _ PL _ _ P10 HAq9))| exact Er].
  Qed.

End Proofs.
End WithCeiling0.
