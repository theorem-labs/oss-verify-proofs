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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit ExpKitArr ValArr W_mod_exp W_exp_simple W_mont PlaceMont W_mont_ctx W_exp_mont.
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
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Lemma mw_to_bv_mod64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 18446744073709551616).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma ovf_mulhu : forall w a, 0 <= w < 2^64 -> 0 < a < 2^64 -> negb (mulw w a / a =? w) = negb (w * a / 18446744073709551616 =? 0).
Proof.
  intros w a Hw Ha. unfold mulw, BW. f_equal.
  destruct (Z.lt_ge_cases (w * a) 18446744073709551616) as [L|G].
  - rewrite (Z.mod_small (w * a)) by nia. rewrite Z.div_mul by lia. rewrite (Z.div_small (w * a)) by nia. rewrite !Z.eqb_refl. reflexivity.
  - assert (Q : 1 <= w * a / 18446744073709551616) by (apply Z.div_le_lower_bound; lia).
    replace (w * a / 18446744073709551616 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply Z.eqb_neq. intros E.
    pose proof (Z.mod_pos_bound (w * a) 18446744073709551616 ltac:(lia)) as MB.
    pose proof (Z.div_mod (w * a) 18446744073709551616 ltac:(lia)) as DM.
    assert (LT : (w * a) mod 18446744073709551616 < w * a) by lia.
    assert (LE : (w * a) mod 18446744073709551616 / a < w).
    { apply Z.div_lt_upper_bound; [lia|]. lia. }
    lia.
Qed.

Lemma ovf_mulhu_sq : forall w, 0 <= w < 2^64 -> negb (mulw w w / w =? w) = negb (w * w / 18446744073709551616 =? 0).
Proof.
  intros w Hw. destruct (Z.eq_dec w 0) as [->|NZ]; [reflexivity|]. apply ovf_mulhu; lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma implM_tbind_assoc : forall {A B C} (t : btree bptr A) (f : A -> btree bptr B) (g : B -> btree bptr C) s Q ms,
  implM bgusegs (interp (embed (tbind t (fun a => tbind (f a) g)))) s Q ms ->
  implM bgusegs (interp (embed (tbind (tbind t f) g))) s Q ms.
Proof.
  intros A B C t f g. induction t as [a| |n k IH|p k IH]; intros s Q ms H; cbn [tbind embed lbind interp] in *; try exact H.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1). exact H1.
Qed.

Definition BN_MUL_WORD_A : Z := 0x10b2b0.
Definition BN_DIV_A : Z := 0x10966c.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 1375532 => 2
  | 1375536 => 1
  | 1375540 => 2
  | 1375560 => 2
  | 1375564 => 1
  | 1375568 => 2
  | 1375576 => 2
  | 1375652 => 1
  | 1375656 => 2
  | 1375684 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.

Lemma mw_rem_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A AM D : Z) (b : bignum bptr),
  rw_cells bgusegs m AM (bn_cells D b) -> u64arr bgusegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 -> 0 <= A < 2^64 ->
  (0 < AM /\ AM mod 8 = 0) -> ub_ptr_ok (Z.of_nat (bn_top b)) D -> is_odd_pure b = true ->
  evt bgusegs (fun ms' => exists x11 : word,
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 s7 x11 a2 a3 a4 a5 a6 a7 s2
                                 (Z_to_bv 64 (if (bn_top b =? 1)%nat then A mod (nth 0 (bn_buf b) 0) else A)) s4 (Z_to_bv 64 AM) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x14fd64) fc None m (seg_rom bgusegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 A) s4 (Z_to_bv 64 AM) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14fd2c) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN U LB HT HD HA (PA & PA8) UBP ODD.
  pose proof (rw_cells_bound _ _ _ _ BN) as (_ & AMB). cbn in AMB.
  unfold bn_cells, MallocRep.wz in BN.
  hide_ors. ub. unhide.
  step. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step.
  step. if_cases KT; rewrite ?unsigned_lit in KT by lia; zify_cond KT.
  - replace (bn_top b =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    step. apply evt_done. eexists. reflexivity.
  - replace (bn_top b =? 1)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
    assert (NTH0 : nth_error (wlimbs (bn_buf b)) (Z.to_nat 0) = Some (Z_to_bv 64 (nth 0 (bn_buf b) 0))).
    { apply nth_error_wlimbs. unfold bn_dmax in HT. lia. }
    assert (L0 : 0 <= nth 0 (bn_buf b) 0 < 2^64).
    { assert (Hl : limb (nth 0 (bn_buf b) 0)) by (apply (proj1 (List.Forall_nth limb (bn_buf b)) LB); unfold bn_dmax in HT; lia). unfold limb, BW in Hl. exact Hl. }
    assert (N0 : nth 0 (bn_buf b) 0 <> 0).
    { unfold is_odd_pure in ODD. apply andb_true_iff in ODD. destruct ODD as [_ OD]. intros E0. rewrite E0 in OD. discriminate OD. }
    destruct (UBP ltac:(lia)) as (PD & PD8).
    pose proof (u64arr_bound _ _ _ _ U) as (_ & DB). rewrite wlimbs_len in DB. fold (bn_dmax b) in DB.
    step.
    hide_ors. ub. unhide.
    let a := cur_mem_addr in pose proof (u64arr_read bgusegs m D _ 0 _ a U NTH0 ltac:(lia) ltac:(addr_tac)) as RD.
    step. clear RD.
    hide_ors. ub. unhide.
    step.
    change (mul_div Instr.M_REMU (Z_to_bv 64 A) (Z_to_bv 64 (nth 0 (bn_buf b) 0)))
      with (if (bv_unsigned (Z_to_bv 64 (nth 0 (bn_buf b) 0)) =? 0)%Z then Z_to_bv 64 A else bv_modu (Z_to_bv 64 A) (Z_to_bv 64 (nth 0 (bn_buf b) 0))).
    rewrite (unsigned_lit (nth 0 (bn_buf b) 0)) by exact L0.
    destruct (Z.eqb_spec (nth 0 (bn_buf b) 0) 0) as [E0|_]; [exfalso; exact (N0 E0)|].
    replace (bv_modu (Z_to_bv 64 A) (Z_to_bv 64 (nth 0 (bn_buf b) 0))) with (Z_to_bv 64 (A mod nth 0 (bn_buf b) 0)).
    2: { pose proof (Z.mod_pos_bound A (nth 0 (bn_buf b) 0) ltac:(lia)) as MB.
         apply bv_eq. rewrite bv_modu_unsigned, !unsigned_lit by lia. reflexivity. }
    step. apply evt_done. eexists. reflexivity.
Qed.

Section Proofs.
  Variable CS : Z.
  Hypothesis CS96 : 128 <= CS.
  Hypothesis CSnew : W_ctx3.BN_MONT_CTX_NEW_STACK <= CS.
  Hypothesis CSfree : W_ctx3.BN_MONT_CTX_FREE_STACK <= CS.
  Definition BN_MOD_EXP_MONT_WORD_STACK : Z := 128 + CS.
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

  Hypothesis BN_mod_mul_montgomery_walk : mont3_stmt BN_MOD_MUL_MONTGOMERY CS (BN_mod_mul_montgomery (tree_ops bptr)).
  Hypothesis BN_to_montgomery_walk : mont2_stmt BN_TO_MONTGOMERY CS (BN_to_montgomery (tree_ops bptr)) false.
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
          F (wz W_exp_mont.BN_MONT_CTX_SET) fc None m (seg_rom bgusegs)).

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

  Hypothesis BN_mul_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax w : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
    implM bgusegs (interp (embed (BN_mul_word (tree_ops bptr) rx w bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_WORD_A) fc None m (seg_rom bgusegs)).

  Hypothesis BN_mod_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz 0 -> a1 = wz ar -> a2 = wz ax -> a3 = wz am -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_div (tree_ops bptr) None (Some rr) rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV_A) fc None m (seg_rom bgusegs)).

  Local Notation ops := (tree_ops bptr).
  Local Notation BMu := (BM (M:=btree bptr) (ptr:=bptr)).

  Definition mw_fin (rr rm : bnref) (pm : bptr) (st : bnref * bnref * Z * bool) : BMu unit :=
    let '(r, t, w, r_is_one) := st in
    bbind ops (if w =? 1 then bret ops (r, t) else mw_flush ops r t w r_is_one rm) (fun rt =>
    let '(r, t) := rt in
    let r_is_one := if w =? 1 then r_is_one else false in
    bbind ops (if r_is_one then BN_one ops rr else BN_from_montgomery ops rr r) (fun _ =>
    bbind ops (BN_MONT_CTX_free ops pm) (fun _ => BN_CTX_end ops))).

  Definition mw_rest (bits : Z) (rr : bnref) (a : Z) (rp rm : bnref) : BMu unit :=
    bbind ops (BN_CTX_start ops) (fun _ =>
    bbind ops (BN_CTX_get ops) (fun r =>
    bbind ops (BN_CTX_get ops) (fun t =>
    bbind ops (BN_MONT_CTX_new ops) (fun pm =>
    bbind ops (BN_MONT_CTX_set ops rm) (fun _ =>
    bbind ops (mw_loop ops (Z.to_nat (bits - 1)) a rp rm (r, t, a, true)) (fun st => mw_fin rr rm pm st)))))).

  Lemma BN_mod_exp_mont_word_eq : forall rr a rp rm,
    BN_mod_exp_mont_word ops rr a rp rm =
    bbind ops (any_consttime ops [rp; rm]) (fun ct =>
    if ct then bunr ops
    else bbind ops (bget ops rm) (fun m =>
         if negb (is_odd_pure m) then bunr ops
         else let a := if (bn_top m =? 1)%nat then a mod (nth 0 (bn_buf m) 0) else a in
              bbind ops (BN_num_bits ops rp) (fun bits =>
              if bits =? 0 then exp_bits0 ops rr rm else if a =? 0 then BN_zero ops rr else mw_rest bits rr a rp rm))).
  Proof. reflexivity. Qed.

  Definition mw_k3 (c : nat) (a : Z) (rp rm r t : bnref) (w : Z) (r_is_one : bool) : BMu (bnref * bnref * Z * bool) :=
    bbind ops (bget ops rp) (fun p =>
    if is_bit_set_pure p (Z.of_nat c) then
      let next_w := mulw w a in
      let ovf := negb (next_w / a =? w) in
      bbind ops (if ovf then mw_flush ops r t w r_is_one rm else bret ops (r, t)) (fun rt =>
      let '(r, t) := rt in
      let r_is_one := if ovf then false else r_is_one in
      let w := if ovf then a else next_w in
      mw_loop ops c a rp rm (r, t, w, r_is_one))
    else mw_loop ops c a rp rm (r, t, w, r_is_one)).

  Definition mw_k2 (c : nat) (a : Z) (rp rm r t : bnref) (w : Z) (r_is_one : bool) : BMu (bnref * bnref * Z * bool) :=
    bbind ops (if r_is_one then bret ops tt else BN_mod_mul_montgomery ops r r r) (fun _ => mw_k3 c a rp rm r t w r_is_one).

  Lemma mw_loop_S' : forall c a rp rm r t w r_is_one,
    mw_loop ops (S c) a rp rm (r, t, w, r_is_one) =
      (let next_w := mulw w w in
       let ovf := negb (next_w / w =? w) in
       bbind ops (if ovf then mw_flush ops r t w r_is_one rm else bret ops (r, t)) (fun rt =>
       let '(r, t) := rt in mw_k2 c a rp rm r t (if ovf then 1 else next_w) (if ovf then false else r_is_one))).
  Proof. reflexivity. Qed.

  Lemma mw_loop_O : forall a rp rm st, mw_loop ops 0 a rp rm st = bret ops st.
  Proof. reflexivity. Qed.

  Section Body.
    Variables (ra gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (lo B : Z) (s : PState) (bs : bstate bptr) (OW LB : list block) (m : mem) (PL0 : placement) (EA : BnRep.err_addrs).
    Variables (rr rp : bnref) (arr arp : Z).
    Variables (ac : Z) (qc : bptr) (am : Z) (qm : bptr).
    Variables (FB SPv : Z).
    Hypothesis ESPV : SPv = FB + 128.
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
    Definition efrW (mo t b : word) : list cell := C8 mo :: C8 t :: C8 b :: saved.
    Definition FINALQ : unit * bstate bptr -> PState -> machine_state -> Prop :=
      bn_post ra (Z_to_bv 64 SPv) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL0 EA
              (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL0 /\ a0' = wz 1).

    Lemma HPM : pl_mont PL = Some (am, qm). Proof. reflexivity. Qed.

    Local Ltac kitW :=
      pose proof (kenv_pre LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE;
      pose proof (kenv_post LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST;
      pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B SPv FB CEIL FBlo FBsp SPR2 A) as BPK;
      pose proof (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK) as KOPEN;
      pose proof (kenv_below LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KBELOW;
      assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - FBlo FBsp SPR2 CEIL; lia);
      pose proof GLO' as GLO2; unfold GLOBALS_TOP in GLO2.

    Hypothesis HAr : ref_at bs OW PL rr arr.
    Hypothesis WRr : hpl PL0 rr.

    Variables (rm : bnref) (arm : Z).
    Hypothesis HAp : ref_at bs OW PL rp arp.
    Hypothesis NROp : rp <> ROne.
    Hypothesis HAm : ref_at bs OW PL rm arm.
    Hypothesis NROm : rm <> ROne.
    Variable (a : Z).
    Hypothesis AR : 0 < a < 2^64.

    Local Ltac fload ENV :=
      let FR := fresh "FRl" in
      pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _); unfold efrW in FR;
      replace (Z_to_bv 64 SPv) with (Z_to_bv 64 (FB + 128)) by (f_equal; clear - ESPV; lia);
      step;
      replace (Z_to_bv 64 (FB + 128)) with (Z_to_bv 64 SPv) by (f_equal; clear - ESPV; lia);
      clear FR.

    Local Ltac fstore ENV LS OFF :=
      let ST := fresh "STs" in let ERR := fresh "ERRs" in let MI := fresh "MIs" in let FR := fresh "FRs" in let errv := fresh "errvs" in
      let MU := fresh "MUs" in let WM := fresh "WMs" in let HEAP := fresh "HEAPs" in let PARTS := fresh "PARTSs" in let HWL := fresh "HWLs" in
      lazymatch type of ENV with
      | kenv _ _ _ _ _ _ _ _ _ _ _ ?stx ?bsx ?mx ?OWx =>
          pose proof ENV as (HEAP & _ & ST & (errv & ERR) & MI & _ & _ & _ & _ & FR & _); unfold efrW in FR;
          pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS;
          pose proof (munch_refl [(FB + OFF, FB + OFF + 8)]%Z mx) as MU; pose proof (wmono_refl bgusegs mx) as WM;
          apply hide_intro in ERR;
          replace (Z_to_bv 64 SPv) with (Z_to_bv 64 (FB + 128)) by (f_equal; clear - ESPV; lia);
          step;
          apply hide_elim in ERR;
          replace (Z_to_bv 64 (FB + 128)) with (Z_to_bv 64 SPv) by (f_equal; clear - ESPV; lia);
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) =>
            eapply (rw_cells_transport bgusegs _ mx my) in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; unfold LX_ERRNO, RATP; lia| exact I]];
            assert (HWL : Forall (w_lib bsx OWx PL lo SPv) [(FB + OFF, FB + OFF + 8)]) by (constructor; [left; cbn; lia| constructor]);
            lazymatch type of FR with rw_cells _ _ _ (C8 ?w1 :: C8 ?e1 :: C8 ?r1 :: _) =>
              fold saved in FR; fold (efrW w1 e1 r1) in FR;
              let E2 := fresh "ENVs" in let L2 := fresh "LSs" in
              pose proof (kenv_silent LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK _ _ stx bsx mx my OWx _ errv ENV PARTS MU WM HWL ST ERR MI FR ltac:(cbn; lia)) as E2;
              assert (L2 : lib_state bsx my OWx PL EA) by
                (assert (WOK : Forall (w_ok OWx LB bsx PL EA SPv []) [(FB + OFF, FB + OFF + 8)]) by (constructor; [apply w_stack; cbn; lia| constructor]);
                 exact (lib_state_frame stx LB _ _ [] bsx mx my OWx PL EA _ HEAP LS MU WM FROK WOK));
              clear ST MI MU WM HWL ERR FR HEAP PARTS ENV LS; rename E2 into ENV; rename L2 into LS
            end
          end
      end.

    Lemma mw_exit : forall (t b : word) stK bsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) t b) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      implM bgusegs (interp (embed (tbind (BN_MONT_CTX_free (tree_ops bptr) qm bsK) (fun p0 => BN_CTX_end (tree_ops bptr) (snd p0))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x150084) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK. kitW. unfold MallocRep.wz in *.
      unfold implM. iprefix. step. step. if_false.
      fload ENVK.
      step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv6 & PRE6).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply (BN_MONT_CTX_free_lwalk_cs HF CS CSfree); [exact PRE6| reflexivity| exact HPM| reflexivity]. }
      cbv beta. intros [u7 bs7] st7 ms7 PO. unfold bn_post in PO. rewrite ESP in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m15 & OW15 & PL' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & ->).
      cbn [fst snd] in *.
      set (PLx := pl_set_mont PL None) in *.
      assert (KP1 : kpost LB PLx EA lo B FB stK bsK mK OWK st7 bs7 m15 OW15).
      { unfold kpost. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exists errv'; exact P5|]. split; [exact P6|].
        split; [exact P7|]. split; [exact P8|]. split; [exact P9| exact P10]. }
      destruct (kenv_post LB PLx EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK _ _ _ _ _ _ _ _ _ ENVK KP1) as (ENV15 & LS15).
      clear PRE6 KP1 P1 P2 P3 P4 P5 P6 P7 P8 P9.
      replace (ret_pc (Z_to_bv 64 0x150094)) with (Z_to_bv 64 0x150094) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      unfold implM. iprefix. step. step.
      destruct (kenv_pre LB PLx EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK _ _ _ _ _ CS ENV15 LS15 LOF) as (errv8 & PRE8).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk; [exact PRE8| reflexivity| exact HPC| reflexivity]. }
      cbv beta. intros [u9 bs9] st9 ms9 PO.
      apply (@bn_post_kpost _ _ LB PLx EA lo B SPv FB CEIL FBlo FBsp SPR2) in PO; [|intros v b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m16 & OW16 & -> & KP & (_ & EOW16)).
      destruct (kenv_post LB PLx EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK _ _ _ _ _ _ _ _ _ ENV15 KP) as (ENV16 & LS16).
      cbn [fst snd] in *. clear PRE8 KP.
      replace (ret_pc (Z_to_bv 64 0x15009c)) with (Z_to_bv 64 0x15009c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PLx lo B SPv FB s bs OW m _ _ _ _ _ ENV16) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
      unfold PLx in LS16. rewrite (pl_set_mont_fresh PL0 _ HFM) in LS16.
      unfold efrW, saved in FRF.
      step. step. do 13 step. release_frame FRF STF SPv. step. step.
      apply evt_done. unfold FINALQ, bn_post. do 15 eexists. exists m16, OW16, PL0, errvF.
      replace (FB + 128) with SPv by lia. rewrite (unsigned_lit SPv) by lia. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS16|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
    Qed.

    Lemma mw_from : forall (t b : word) stK bsK mK OWK (r : bnref) (ar : Z) (ri : nat)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x22 x24 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) t b) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri ->
      implM bgusegs (interp (embed (tbind (BN_from_montgomery (tree_ops bptr) rr r bsK) (fun p1 => tbind (BN_MONT_CTX_free (tree_ops bptr) qm (snd p1)) (fun p0 => BN_CTX_end (tree_ops bptr) (snd p0)))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) x19 (Z_to_bv 64 arr) (Z_to_bv 64 arm) x22 (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15006c) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK HArK Er. kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAr) as HArrK.
      unfold implM. iprefix. step. step.
      fload ENVK.
      step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_from_montgomery_walk; [exact PRE5| reflexivity| rewrite ESP; exact FB16| exact HArrK| exact HArK| apply hpl_wref; apply hpl_pl_mont; exact WRr| intros _; rewrite Er; unfold RPool, ROne, NFIX; lia| exact HPM| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x150080)) with (Z_to_bv 64 0x150080) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. if_false.
      ihere. to_implM.
      eapply mw_exit; [exact ENV5| exact LS5].
    Qed.

    Lemma mw_one : forall (t b : word) stK bsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x22 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) t b) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      implM bgusegs (interp (embed (tbind (BN_one (tree_ops bptr) rr bsK) (fun p1 => tbind (BN_MONT_CTX_free (tree_ops bptr) qm (snd p1)) (fun p0 => BN_CTX_end (tree_ops bptr) (snd p0)))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) x19 (Z_to_bv 64 arr) (Z_to_bv 64 arm) x22 (Z_to_bv 64 arp) x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15001c) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK. kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAr) as HArrK.
      unfold BN_one.
      unfold implM. iprefix. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_set_word_walk; [exact PRE5| reflexivity| exact HArrK| apply hpl_wref; apply hpl_pl_mont; exact WRr| unfold BW; lia| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & -> & _)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x150028)) with (Z_to_bv 64 0x150028) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. if_false. step.
      ihere. to_implM.
      eapply mw_exit; [exact ENV5| exact LS5].
    Qed.

    Definition MWQ (rv : (bnref * bnref * Z * bool) * bstate bptr) (st' : PState) (ms' : machine_state) : Prop :=
      exists mK' OWK' (ar at_ : Z) (ri ti : nat) (b : word) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word),
        ms' = MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 0) (Z_to_bv 64 a) (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 (snd (fst (fst rv)))) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26
                      (Z_to_bv 64 (Z.b2z (snd (fst rv)))) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x150010) fc None mK' (seg_rom bgusegs)
        /\ kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) b) st' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA
        /\ ref_at (snd rv) OWK' PL (fst (fst (fst (fst rv)))) ar /\ fst (fst (fst (fst rv))) = RPool ri
        /\ ref_at (snd rv) OWK' PL (snd (fst (fst (fst rv)))) at_ /\ snd (fst (fst (fst rv))) = RPool ti
        /\ 0 <= snd (fst (fst rv)) < 2^64.

    Definition MWHEAD (c : nat) : Prop := forall stK bsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (one : bool)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) (Z_to_bv 64 (Z.of_nat (S c)))) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri -> ref_at bsK OWK PL t at_ -> t = RPool ti -> 0 < w < 2^64 ->
      Z.of_nat (S c) < 2^31 ->
      implM bgusegs (interp (embed (mw_loop ops (S c) a rp rm (r, t, w, one) bsK))) stK MWQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 a) (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 (Z_to_bv 64 (Z.b2z one)) t3 t4 t5 t6)
            F (Z_to_bv 64 0x14fdc4) fc None mK (seg_rom bgusegs)).

    Lemma L_test : forall c, (forall c', c = S c' -> MWHEAD c') -> forall stK bsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (one : bool)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) (Z_to_bv 64 (Z.of_nat c))) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri -> ref_at bsK OWK PL t at_ -> t = RPool ti -> 0 < w < 2^64 ->
      Z.of_nat c < 2^31 ->
      implM bgusegs (interp (embed (mw_loop ops c a rp rm (r, t, w, one) bsK))) stK MWQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 a) (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 (Z_to_bv 64 (Z.b2z one)) t3 t4 t5 t6)
            F (Z_to_bv 64 0x14fef4) fc None mK (seg_rom bgusegs)).
    Proof.
      intros c NEXT. intros until t6; intros ENVK LSK HArK Er HAtK Et WRP C31.
      assert (WR : 0 <= w < 2^64) by (clear - WRP; lia).
      kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      assert (NROr : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
      assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
      unfold implM. iprefix.
      fload ENVK.
      step. rewrite lts_signed by (clear - C31; lia).
      destruct c as [|c'].
      -
        replace (0 <? Z.of_nat 0) with false by reflexivity.
        step.
        ihere. rewrite mw_loop_O. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
        unfold MWQ. cbn [fst snd]. exists mK, OWK, ar, at_, ri, ti. do 19 eexists. split; [reflexivity|].
        split; [exact ENVK|]. split; [exact LSK|]. split; [exact HArK|]. split; [exact Er|]. split; [exact HAtK|]. split; [exact Et| exact WR].
      - replace (0 <? Z.of_nat (S c')) with true by (symmetry; apply Z.ltb_lt; clear; lia).
        ihere. to_implM.
        eapply (NEXT c' eq_refl); [exact ENVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WRP| exact C31].
    Qed.

    Lemma L_k3 : forall c, (forall c', c = S c' -> MWHEAD c') -> forall stK bsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (one : bool)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) (Z_to_bv 64 (Z.of_nat (S c)))) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri -> ref_at bsK OWK PL t at_ -> t = RPool ti -> 0 < w < 2^64 ->
      Z.of_nat (S c) < 2^31 ->
      implM bgusegs (interp (embed (mw_k3 c a rp rm r t w one bsK))) stK MWQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 a) (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) (Z_to_bv 64 (Z.b2z (negb one))) (Z_to_bv 64 (Z.b2z one)) t3 t4 t5 t6)
            F (Z_to_bv 64 0x14fe84) fc None mK (seg_rom bgusegs)).
    Proof.
      intros c NEXT. intros until t6; intros ENVK LSK HArK Er HAtK Et WRP C31.
      assert (WR : 0 <= w < 2^64) by (clear - WRP; lia).
      kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      assert (NROr : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
      assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
      pose proof (L_test c NEXT) as TEST.
      assert (C31' : Z.of_nat c < 2^31) by (clear - C31; lia).
      unfold mw_k3, bbind, bget. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
      unfold implM. iprefix.
      step.
      fload ENVK.
      step. rewrite (swrap32_wrap64 (Z.of_nat (S c)) (-1)) by (clear - C31; lia). replace (Z.of_nat (S c) + -1) with (Z.of_nat c) by (clear; lia).
      step.
      fstore ENVK LSK 16.
      step.
      destruct (kenv_open_u LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rp arp ENVK LSK HApK NROp) as (Dp & BNp & Up & (OKp1 & OKp2 & OKp3 & OKp4) & _ & SEPp & SEPDp & _ & ALp & UPp).
      pose proof ENVK as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OKp3.
      eapply evt_cut.
      { eapply (BN_is_bit_set_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := arp) (D := Dp) (b := getbn rp bsK) (n := Z.of_nat c);
          [exact BNp | exact ALp | exact UPp | exact Up | exact OKp1 | exact OKp2 | clear - OKp3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS96; lia | exact MIK
          | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDp FBlo FBsp CS96 LOF; lia | reflexivity | reflexivity | clear - C31; lia]. }
      clear STK MIK.
      intros ms2 PO. unfold bn_small_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
      rewrite ESP in *.
      destruct (KBELOW _ _ _ _ m2 _ 16 ENVK LSK ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear MUc WMc MIc STc BNp Up ENVK LSK.
      replace (ret_pc (Z_to_bv 64 0x14fe9c)) with (Z_to_bv 64 0x14fe9c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct (is_bit_set_pure (getbn rp bsK) (Z.of_nat c)) eqn:EB; cbn [Z.b2z].
      2: {
           step. if_true. step.
           ihere. to_implM.
           eapply (TEST stK bsK _ OWK r t ar at_ ri ti w one); [exact ENV2| exact LS2| exact HArK| exact Er| exact HAtK| exact Et| exact WRP| exact C31']. }
      step. if_false.
      cbv zeta. rewrite (ovf_mulhu w a WR AR).
      step. rewrite !unsigned_lit by (first [exact WR| clear - AR; lia]). rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 64) with 18446744073709551616.
      replace (a * w) with (w * a) by (clear; lia).
      assert (HI : 0 <= w * a / 18446744073709551616 < 2^64).
      { split; [apply Z.div_pos; [clear - WR AR; nia| clear; lia]|]. apply Z.div_lt_upper_bound; [clear; lia|]. clear - WR AR. nia. }
      step. if_cases KO; rewrite ?unsigned_lit in KO by exact HI; zify_cond KO;
        change 18446744073709551615 with (Z.ones 64) in KO; rewrite Z.land_ones in KO by (clear; lia); change (2 ^ 64) with 18446744073709551616 in KO;
        rewrite Z.mod_small in KO by exact HI.
      {
        replace (w * a / 18446744073709551616 =? 0) with true by (symmetry; apply Z.eqb_eq; exact KO). cbn [negb].
        cbn [tbind fst snd]. cbv beta iota.
        step. rewrite !unsigned_lit by (first [exact WR| clear - AR; lia]).
        rewrite (mw_to_bv_mod64 (a * w)). replace ((a * w) mod 18446744073709551616) with (mulw w a) by (unfold mulw, BW; f_equal; clear; lia).
        step.
        ihere. to_implM.
        eapply (TEST stK bsK _ OWK r t ar at_ ri ti (mulw w a) one); [exact ENV2| exact LS2| exact HArK| exact Er| exact HAtK| exact Et| unfold mulw, BW; pose proof (Z.div_mod (w * a) 18446744073709551616 ltac:(clear; lia)) as DM; rewrite KO in DM; pose proof (Z.mod_pos_bound (w * a) 18446744073709551616 ltac:(clear; lia)) as MB; assert (P : 0 < w * a) by (clear - WRP AR; nia); clear - DM MB P; lia| exact C31']. }
      replace (w * a / 18446744073709551616 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KO). cbn [negb].
      unfold mw_flush, mw_to_mont_word, mw_mod_mul_word, BN_mod, bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
      destruct one; cbn [Z.b2z negb].
      -
        step. step. step. if_true. step.
        destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv5 & PRE5). ihere. to_implM. apply implM_tbind_assoc. apply implM_tbind_assoc.
        eapply implM_embed_bind.
        { eapply BN_set_word_walk; [exact PRE5| reflexivity| exact HArK| rewrite Er; apply wref_pool| unfold BW; exact WR| reflexivity| reflexivity]. }
        cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & -> & _)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
        cbn [fst snd] in *. clear PRE5 KP.
        replace (ret_pc (Z_to_bv 64 0x14ff04)) with (Z_to_bv 64 0x14ff04) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        fload ENV5.
        step. if_false. step. step. step. step.
        destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv6 & PRE6). ihere. to_implM.
        eapply implM_embed_bind.
        { eapply BN_to_montgomery_walk; [exact PRE6| reflexivity| rewrite ESP; exact FB16| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| rewrite Er; apply wref_pool| intros X; discriminate X| exact HPM| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & ->)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
        cbn [fst snd] in *. clear PRE6 KP.
        replace (ret_pc (Z_to_bv 64 0x14ff1c)) with (Z_to_bv 64 0x14ff1c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        step. step. step. step. if_false. step.
        cbn [tbind fst snd]. cbv beta iota.
        ihere. to_implM.
        eapply (TEST st6 bs6 _ OW6 r t ar at_ ri ti a false); [exact ENV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et| clear - AR; lia| exact C31'].
      -
        step. step. step. if_false. step.
        destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv5 & PRE5). ihere. to_implM. apply implM_tbind_assoc.
        eapply implM_embed_bind.
        { eapply BN_mul_word_walk; [exact PRE5| reflexivity| exact HArK| rewrite Er; apply wref_pool| reflexivity| reflexivity| exact WR]. }
        cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & -> & _)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
        cbn [fst snd] in *. clear PRE5 KP.
        replace (ret_pc (Z_to_bv 64 0x14feb8)) with (Z_to_bv 64 0x14feb8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        fload ENV5.
        step. if_false. step. step. step. step. step. step.
        destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv6 & PRE6). ihere. to_implM. apply implM_tbind_assoc.
        eapply implM_embed_bind.
        { eapply BN_mod_walk; [exact PRE6| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAmK)| rewrite Et; apply hpl_pool| exact NROr| exact NROm| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & ->)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
        cbn [fst snd] in *. clear PRE6 KP.
        replace (ret_pc (Z_to_bv 64 0x14fed8)) with (Z_to_bv 64 0x14fed8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        step. step.
        fstore ENV6 LS6 8.
        step. if_false. step.
        cbn [tbind fst snd]. cbv beta iota.
        ihere. to_implM.
        eapply (TEST st6 bs6 _ OW6 t r at_ ar ti ri a false); [exact ENV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er| clear - AR; lia| exact C31'].
    Qed.

    Lemma L_k2 : forall c, (forall c', c = S c' -> MWHEAD c') -> forall stK bsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (ts : word)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) ts (Z_to_bv 64 (Z.of_nat (S c)))) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri -> ref_at bsK OWK PL t at_ -> t = RPool ti -> 0 < w < 2^64 ->
      Z.of_nat (S c) < 2^31 ->
      implM bgusegs (interp (embed (tbind (BN_mod_mul_montgomery ops r r r bsK) (fun p => mw_k3 c a rp rm r t w false (snd p))))) stK MWQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 a) (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) (Z_to_bv 64 at_) (Z_to_bv 64 ar) (Z_to_bv 64 am) x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14fe5c) fc None mK (seg_rom bgusegs)).
    Proof.
      intros c NEXT. intros until t6; intros ENVK LSK HArK Er HAtK Et WRP C31.
      assert (WR : 0 <= w < 2^64) by (clear - WRP; lia).
      kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      assert (NROr : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
      assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
      pose proof (L_k3 c NEXT) as K3.
      unfold implM. iprefix.
      step. step. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_mod_mul_montgomery_walk; [exact PRE5| reflexivity| rewrite ESP; exact FB16| exact HArK| exact HArK| exact HArK| rewrite Er; apply wref_pool| exact NROr| exact HPM| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x14fe74)) with (Z_to_bv 64 0x14fe74) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. step. if_false. step.
      fstore ENV5 LS5 8.
      ihere. to_implM.
      eapply (K3 st5 bs5 _ OW5 r t ar at_ ri ti w false); [exact ENV5| exact LS5| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK)| exact Et| exact WRP| exact C31].
    Qed.

    Lemma mw_round : forall c, (forall c', c = S c' -> MWHEAD c') -> MWHEAD c.
    Proof.
      intros c NEXT. unfold MWHEAD. intros until t6; intros ENVK LSK HArK Er HAtK Et WRP C31.
      assert (WR : 0 <= w < 2^64) by (clear - WRP; lia).
      kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      assert (NROr : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
      assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
      pose proof (L_k3 c NEXT) as K3. pose proof (L_k2 c NEXT) as K2.
      rewrite mw_loop_S'. cbv zeta. rewrite (ovf_mulhu_sq w WR).
      unfold bbind at 1. cbn [bind tree_ops].
      assert (HI : 0 <= w * w / 18446744073709551616 < 2^64).
      { split; [apply Z.div_pos; [clear - WR; nia| clear; lia]|]. apply Z.div_lt_upper_bound; [clear; lia|]. clear - WR. nia. }
      assert (WW : 0 <= mulw w w < 2^64) by (unfold mulw, BW; apply Z.mod_pos_bound; clear; lia).
      unfold implM. iprefix.
      rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 w)) at 1. hide_ors. ub. unhide.
      step. rewrite !unsigned_lit by exact WR. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 64) with 18446744073709551616.
      step. if_cases KO; rewrite ?unsigned_lit in KO by exact HI; zify_cond KO;
        change 18446744073709551615 with (Z.ones 64) in KO; rewrite Z.land_ones in KO by (clear; lia); change (2 ^ 64) with 18446744073709551616 in KO;
        rewrite Z.mod_small in KO by exact HI.
      {
        assert (WWP : 0 < mulw w w < 2^64).
        { unfold mulw, BW. pose proof (Z.div_mod (w * w) 18446744073709551616 ltac:(clear; lia)) as DM. rewrite KO in DM. pose proof (Z.mod_pos_bound (w * w) 18446744073709551616 ltac:(clear; lia)) as MB.
          assert (P : 0 < w * w) by (clear - WRP; nia). clear - DM MB P. lia. }
        replace (w * w / 18446744073709551616 =? 0) with true by (symmetry; apply Z.eqb_eq; exact KO). cbn [negb].
        unfold bret. cbn [ret tree_ops tbind fst snd]. cbv beta iota.
        step. rewrite !unsigned_lit by exact WR.
        rewrite (mw_to_bv_mod64 (w * w)). change ((w * w) mod 18446744073709551616) with (mulw w w).
        unfold mw_k2, bbind, bret. cbn [bind ret tree_ops].
        destruct one; cbn [Z.b2z].
        - step. if_false. step. step.
          cbn [tbind fst snd]. cbv beta.
          ihere. to_implM.
          eapply (K3 stK bsK mK OWK r t ar at_ ri ti (mulw w w) true); [exact ENVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WWP| exact C31].
        - step. if_true.
          fload ENVK. fload ENVK.
          ihere. to_implM.
          eapply (K2 stK bsK mK OWK r t ar at_ ri ti (mulw w w) (Z_to_bv 64 at_)); [exact ENVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WWP| exact C31]. }
      replace (w * w / 18446744073709551616 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KO). cbn [negb].
      unfold mw_flush, mw_to_mont_word, mw_mod_mul_word, BN_mod, bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
      destruct one; cbn [Z.b2z].
      -
        step. step. step. if_false. step.
        destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5). ihere. to_implM. apply implM_tbind_assoc. apply implM_tbind_assoc.
        eapply implM_embed_bind.
        { eapply BN_set_word_walk; [exact PRE5| reflexivity| exact HArK| rewrite Er; apply wref_pool| unfold BW; exact WR| reflexivity| reflexivity]. }
        cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & -> & _)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
        cbn [fst snd] in *. clear PRE5 KP.
        replace (ret_pc (Z_to_bv 64 0x14fde0)) with (Z_to_bv 64 0x14fde0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        step. if_false. step. step.
        fload ENV5.
        step. step. step.
        destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv6 & PRE6). ihere. to_implM.
        eapply implM_embed_bind.
        { eapply BN_to_montgomery_walk; [exact PRE6| reflexivity| rewrite ESP; exact FB16| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| rewrite Er; apply wref_pool| intros X; discriminate X| exact HPM| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & ->)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
        cbn [fst snd] in *. clear PRE6 KP.
        replace (ret_pc (Z_to_bv 64 0x14fdfc)) with (Z_to_bv 64 0x14fdfc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        step. if_false. step.
        fload ENV6.
        step.
        cbn [tbind fst snd]. cbv beta iota. unfold mw_k2, bbind. cbn [bind tree_ops]. cbv beta iota.
        ihere. to_implM.
        eapply (K2 st6 bs6 _ OW6 r t ar at_ ri ti 1 (Z_to_bv 64 at_)); [exact ENV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et| clear; lia| exact C31].
      -
        step. step. step. if_true. step.
        destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5). ihere. to_implM. apply implM_tbind_assoc.
        eapply implM_embed_bind.
        { eapply BN_mul_word_walk; [exact PRE5| reflexivity| exact HArK| rewrite Er; apply wref_pool| reflexivity| reflexivity| exact WR]. }
        cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & -> & _)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
        cbn [fst snd] in *. clear PRE5 KP.
        replace (ret_pc (Z_to_bv 64 0x14fe20)) with (Z_to_bv 64 0x14fe20) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        step. if_false. step.
        fload ENV5.
        step. step. step. step. step.
        destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv6 & PRE6). ihere. to_implM. apply implM_tbind_assoc.
        eapply implM_embed_bind.
        { eapply BN_mod_walk; [exact PRE6| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAmK)| rewrite Et; apply hpl_pool| exact NROr| exact NROm| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
        cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & ->)).
        destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
        cbn [fst snd] in *. clear PRE6 KP.
        replace (ret_pc (Z_to_bv 64 0x14fe40)) with (Z_to_bv 64 0x14fe40) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold implM. iprefix.
        step. if_false. step. step. step. step.
        fload ENV6.
        cbn [tbind fst snd]. cbv beta iota. unfold mw_k2, bbind. cbn [bind tree_ops]. cbv beta iota.
        ihere. to_implM.
        eapply (K2 st6 bs6 _ OW6 t r at_ ar ti ri 1 (Z_to_bv 64 at_)); [exact ENV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er| clear; lia| exact C31].
    Qed.

    Lemma mw_head : forall c, MWHEAD c.
    Proof. induction c as [|c IH]; apply mw_round; intros c' E; [discriminate E| injection E as <-; exact IH]. Qed.

    Lemma L_fin_one : forall stK bsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (b ts : word)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x24 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) ts b) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri -> ref_at bsK OWK PL t at_ -> t = RPool ti -> 0 <= w < 2^64 ->
      w <> 1 ->
      implM bgusegs (interp (embed (mw_fin rr rm qm (r, t, w, true) bsK))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 w) (Z_to_bv 64 arr) (Z_to_bv 64 arm) x19 (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x150044) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK HArK Er HAtK Et WR W1.
      kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      assert (NROr : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
      assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
      unfold mw_fin. cbv zeta. replace (w =? 1) with false by (symmetry; apply Z.eqb_neq; exact W1).
      unfold mw_flush, mw_to_mont_word, mw_mod_mul_word, BN_mod, bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
      unfold implM. iprefix.
      step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5). ihere. to_implM. apply implM_tbind_assoc. apply implM_tbind_assoc.
      eapply implM_embed_bind.
      { eapply BN_set_word_walk; [exact PRE5| reflexivity| exact HArK| rewrite Er; apply wref_pool| unfold BW; exact WR| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & -> & _)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x150050)) with (Z_to_bv 64 0x150050) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. if_false. step. step.
      fload ENV5.
      step. step.
      destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv6 & PRE6). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_to_montgomery_walk; [exact PRE6| reflexivity| rewrite ESP; exact FB16| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| rewrite Er; apply wref_pool| intros X; discriminate X| exact HPM| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
      cbn [fst snd] in *. clear PRE6 KP.
      replace (ret_pc (Z_to_bv 64 0x150068)) with (Z_to_bv 64 0x150068) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. if_false.
      cbn [tbind fst snd]. cbv beta iota.
      ihere. to_implM.
      eapply (mw_from ts b st6 bs6 _ OW6 r ar ri); [exact ENV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er].
    Qed.

    Lemma L_fin_mul : forall stK bsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (b : word)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x24 x26 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) b) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri -> ref_at bsK OWK PL t at_ -> t = RPool ti -> 0 <= w < 2^64 ->
      w <> 1 ->
      implM bgusegs (interp (embed (mw_fin rr rm qm (r, t, w, false) bsK))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) x22 (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1500a0) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK HArK Er HAtK Et WR W1.
      kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      assert (NROr : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
      assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
      unfold mw_fin. cbv zeta. replace (w =? 1) with false by (symmetry; apply Z.eqb_neq; exact W1).
      unfold mw_flush, mw_to_mont_word, mw_mod_mul_word, BN_mod, bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
      unfold implM. iprefix.
      step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5). ihere. to_implM. apply implM_tbind_assoc.
      eapply implM_embed_bind.
      { eapply BN_mul_word_walk; [exact PRE5| reflexivity| exact HArK| rewrite Er; apply wref_pool| reflexivity| reflexivity| exact WR]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & -> & _)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x1500ac)) with (Z_to_bv 64 0x1500ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. if_false. step.
      fload ENV5.
      step. step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv6 & PRE6). ihere. to_implM. apply implM_tbind_assoc.
      eapply implM_embed_bind.
      { eapply BN_mod_walk; [exact PRE6| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAmK)| rewrite Et; apply hpl_pool| exact NROr| exact NROm| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
      cbn [fst snd] in *. clear PRE6 KP.
      replace (ret_pc (Z_to_bv 64 0x1500cc)) with (Z_to_bv 64 0x1500cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      step. step. if_false. step.
      cbn [tbind fst snd]. cbv beta iota.
      ihere. to_implM.
      eapply (mw_from (Z_to_bv 64 at_) b st6 bs6 _ OW6 t at_ ti); [exact ENV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et].
    Qed.

    Lemma L_final : forall stK bsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (one : bool) (b : word)
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) b) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri -> ref_at bsK OWK PL t at_ -> t = RPool ti -> 0 <= w < 2^64 ->
      implM bgusegs (interp (embed (mw_fin rr rm qm (r, t, w, one) bsK))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 a) (Z_to_bv 64 arr) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 (Z_to_bv 64 (Z.b2z one)) t3 t4 t5 t6)
            F (Z_to_bv 64 0x150010) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK HArK Er HAtK Et WR.
      kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAp) as HApK.
      assert (NROr : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).
      assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
      unfold implM. iprefix.
      step.
      step. if_cases KW; rewrite ?unsigned_lit in KW by (first [exact WR| clear; lia]); zify_cond KW.
      -
        assert (W1 : w <> 1) by (clear - KW WR; lia).
        destruct one; cbn [Z.b2z].
        + step. if_false. step.
          ihere. to_implM.
          eapply (L_fin_one stK bsK mK OWK r t ar at_ ri ti w b (Z_to_bv 64 at_)); [exact ENVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WR| exact W1].
        + step. if_true.
          ihere. to_implM.
          eapply (L_fin_mul stK bsK mK OWK r t ar at_ ri ti w b); [exact ENVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WR| exact W1].
      -
        assert (W1 : w = 1) by (clear - KW WR; lia). subst w.
        unfold mw_fin. cbv zeta. change (1 =? 1) with true. unfold bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta iota.
        destruct one; cbn [Z.b2z].
        + step. if_false.
          ihere. to_implM.
          eapply (mw_one (Z_to_bv 64 at_) b stK bsK mK OWK); [exact ENVK| exact LSK].
        + step. if_true.
          ihere. to_implM.
          eapply (mw_from (Z_to_bv 64 at_) b stK bsK mK OWK r ar ri); [exact ENVK| exact LSK| exact HArK| exact Er].
    Qed.

    Hypothesis HFT : pl_bn PL0 RTmod = None.

    Lemma L_set : forall stK bsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (bits : Z) (mo ts b : word)
        (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 x27 t3 t4 t5 t6 : word),
      kenv LB PL lo B SPv FB s bs OW m (efrW mo ts b) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL r ar -> r = RPool ri -> ref_at bsK OWK PL t at_ -> t = RPool ti -> 0 < bits < 2 ^ 24 ->
      implM bgusegs (interp (embed (tbind (BN_MONT_CTX_set ops rm bsK)
                                      (fun p => tbind (mw_loop ops (Z.to_nat (bits - 1)) a rp rm (r, t, a, true) (snd p))
                                                  (fun q => mw_fin rr rm qm (fst q) (snd q)))))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 ac) (Z_to_bv 64 am) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 0) (Z_to_bv 64 a) (Z_to_bv 64 arr) (Z_to_bv 64 arm) x19 (Z_to_bv 64 arp) (Z_to_bv 64 at_) (Z_to_bv 64 ar) (Z_to_bv 64 bits) x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14ffe0) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6; intros ENVK LSK HArK Er HAtK Et BITS. kitW. unfold MallocRep.wz in *.
      pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & RSK & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAm) as HAmK.
      assert (AW : 0 <= a < 2^64) by (clear - AR; lia).
      unfold implM. iprefix.
      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AMR; lia); zify_cond KZ; [exfalso; clear - KZ AMR; lia| clear KZ].
      step. step. step. step.
      destruct (KPRE _ _ _ _ _ CS ENVK LSK LOF) as (errv5 & PRE5). ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BN_MONT_CTX_set_walk; [exact PRE5| reflexivity| rewrite ESP; exact FB16| exact HAmK| exact NROm| exact HPM| exact HPC| exact HFT| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros [u5 bs5] st5 ms5 PO. apply BPK in PO; [|intros vv b0 o p a0' [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & ->)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENVK KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE5 KP.
      replace (ret_pc (Z_to_bv 64 0x14fff4)) with (Z_to_bv 64 0x14fff4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold implM. iprefix.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) as HAr5. pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK) as HAt5.
      step. if_true.
      fstore ENV5 LS5 0.
      hide_ors. ub. unhide.
      step. rewrite lts_signed by (clear - BITS; lia).
      destruct (Z.ltb_spec (bits + -2) 0) as [B1|B2].
      -
        assert (E1 : bits = 1) by (clear - B1 BITS; lia). subst bits.
        change (Z.to_nat (1 - 1)) with 0%nat. rewrite mw_loop_O. unfold bret. cbn [ret tree_ops tbind fst snd]. cbv beta.
        step.
        step. if_cases KA; rewrite ?unsigned_lit in KA by (first [exact AW| clear; lia]); zify_cond KA.
        + assert (A1 : a = 1) by (clear - KA AW; lia).
          unfold mw_fin. cbv zeta. replace (a =? 1) with true by (symmetry; apply Z.eqb_eq; exact A1).
          unfold bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta iota.
          ihere. to_implM.
          eapply (mw_one ts b st5 bs5 _ OW5); [exact ENV5| exact LS5].
        + step.
          ihere. to_implM.
          eapply (L_fin_one st5 bs5 _ OW5 r t ar at_ ri ti a b ts); [exact ENV5| exact LS5| exact HAr5| exact Er| exact HAt5| exact Et| exact AW| clear - KA AW; lia].
      -
        fstore ENV5 LS5 8.
        step. replace (bits + -1) with (Z.of_nat (S (Z.to_nat (bits - 2)))) by (clear - B2; lia).
        fstore ENV5 LS5 16.
        step. step.
        replace (Z.to_nat (bits - 1)) with (S (Z.to_nat (bits - 2))) by (clear - B2; lia).
        ihere. to_implM.
        eapply implM_embed_bind with (Q1 := MWQ).
        { eapply (mw_head (Z.to_nat (bits - 2)) st5 bs5 _ OW5 r t ar at_ ri ti a true);
            [exact ENV5| exact LS5| exact HAr5| exact Er| exact HAt5| exact Et| exact AR| clear - B2 BITS; lia]. }
        cbv beta. intros [[[[rN tN] wN] oneN] bsQ] stQ msQ (mQ & OWQ & ar2 & at2 & ri2 & ti2 & bQ & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENVQ & LSQ & HAr2 & Er2 & HAt2 & Et2 & WR2). cbn [fst snd] in *.
        eapply (L_final stQ bsQ mQ OWQ rN tN ar2 at2 ri2 ti2 wN oneN bQ); [exact ENVQ| exact LSQ| exact HAr2| exact Er2| exact HAt2| exact Et2| exact WR2].
    Qed.

  End Body.

  Lemma BN_mod_exp_mont_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rp rm : bnref) (A : Z) (arr arp arm ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_MOD_EXP_MONT_WORD_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL rp arp -> ref_at bs OW PL rm arm ->
    hpl PL rr -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL -> 0 <= A < BW ->
    a0 = wz arr -> a1 = wz A -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> a5 = wz 0 ->
    implM bgusegs (interp (embed (BN_mod_exp_mont_word (tree_ops bptr) rr A rp rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_EXP_MONT_WORD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAp HAm WRr NROp NROm HPC HFR AB -> -> -> -> -> ->.
    unfold BN_MOD_EXP_MONT_WORD_STACK, BN_MOD_EXP_MONT_WORD, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    rewrite BN_mod_exp_mont_word_eq. unfold any_consttime, BN_num_bits, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd fold_right]. cbv beta.
    unfold implM. iprefix.

    carve_frame 128%nat ST. do 23 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    lazymatch type of FR with rw_cells _ _ _ (CB 24 ?jk :: ?post) =>
      pose proof (rw_cells_split_CB bgusegs m1 (bv_unsigned sp + -128) [] 24 jk post [8; 8; 8]%nat FR eq_refl) as FR'; clear FR; rename FR' into FR;
      cbn [mk_CB_cells app] in FR
    end.
    destruct (cb8x3_c8 _ _ _ _ _ _ FR) as (w0 & e0 & r0 & FR'). clear FR. rename FR' into FR.
    clear junk.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -128, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -128, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -128) by lia.
    assert (FBsp : bv_unsigned sp + -128 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (kenv_open LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL FROK) as KOPEN.
    pose proof (kenv_open_u LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL FROK) as KOPENU.
    pose proof (kenv_below LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KBELOW.
    assert (LOF : lo <= bv_unsigned sp + -128 - CS) by lia.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR LS.

    destruct (KOPENU _ _ _ _ _ rp arp ENV LS1 HAp NROp) as (Dp & BNp & Up & (OKp1 & OKp2 & OKp3 & OKp4) & _ & SEPp & SEPDp & _ & ALp & UPp).
    set (bp := getbn rp bs) in *.
    assert (FLp : 0 <= bn_flags bp <= 1) by (destruct OKp4 as [E|E]; rewrite E; lia).
    assert (CTp : Z.land (bn_flags bp) 4 = 0) by (destruct OKp4 as [E|E]; rewrite E; reflexivity).
    pose proof ENV as (_ & _ & ST1 & _ & MI1 & _).
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -128))) with (lo := lo) (A := arp) (D := Dp) (b := bp);
        [exact BNp | exact ALp | clear - FLp; lia | rewrite ESP; exact ST1 | rewrite ESP; clear - LOF CS96; lia | exact MI1 | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST1 MI1.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit 4) by lia. rewrite CTp.
    replace (bv_unsigned sp + -128 - 16) with (bv_unsigned sp + -128 - 16) in MUc by reflexivity.
    destruct (KBELOW _ _ _ _ m2 _ 16 ENV LS1 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear ENV LS1 MUc WMc MIc STc BNp Up.
    replace (ret_pc (Z_to_bv 64 0x14fc98)) with (Z_to_bv 64 0x14fc98) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_false.

    destruct (KOPENU _ _ _ _ _ rm arm ENV2 LS2 HAm NROm) as (Dm & BNm & Um & (OKm1 & OKm2 & OKm3 & OKm4) & _ & SEPm & SEPDm & _ & ALm & UPm).
    set (bm := getbn rm bs) in *.
    assert (FLm : 0 <= bn_flags bm <= 1) by (destruct OKm4 as [E|E]; rewrite E; lia).
    assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
    pose proof ENV2 as (_ & _ & ST2b & _ & MI2b & _).
    step. step. step.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -128))) with (lo := lo) (A := arm) (D := Dm) (b := bm);
        [exact BNm | exact ALm | clear - FLm; lia | rewrite ESP; exact ST2b | rewrite ESP; clear - LOF CS96; lia | exact MI2b | rewrite ESP; clear - SEPm FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST2b MI2b.
    intros ms3 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit 4) by lia. rewrite CTm.
    destruct (KBELOW _ _ _ _ m3 _ 16 ENV2 LS2 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV3 & LS3). clear ENV2 LS2 MUc WMc MIc STc BNm Um.
    replace (ret_pc (Z_to_bv 64 0x14fca8)) with (Z_to_bv 64 0x14fca8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_true.
    unfold has_flag, BN_FLG_CONSTTIME. fold bp bm. rewrite CTp, CTm. cbn [Z.eqb negb orb andb]. cbv beta.

    destruct (KOPENU _ _ _ _ _ rm arm ENV3 LS3 HAm NROm) as (Dm1 & BNm1 & Um1 & _ & _ & SEPm1 & SEPDm1 & _ & ALm1 & UPm1). fold bm in BNm1, Um1, SEPDm1, UPm1.
    pose proof ENV3 as (_ & _ & ST3 & _ & MI3 & _).
    step. step.
    eapply evt_cut.
    { eapply (BN_is_odd_spec _ (Z_to_bv 64 (bv_unsigned sp + -128))) with (lo := lo) (A := arm) (D := Dm1) (b := bm);
        [exact BNm1 | exact ALm1 | exact UPm1 | exact Um1 | exact OKm1 | exact OKm2 | clear - OKm3; unfold BG_DMAX in OKm3; lia | rewrite ESP; exact ST3 | rewrite ESP; clear - LOF CS96; lia | exact MI3
        | rewrite ESP; clear - SEPm1 FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDm1 FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST3 MI3.
    intros ms4 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (KBELOW _ _ _ _ m4 _ 16 ENV3 LS3 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV4 & LS4). clear ENV3 LS3 MUc WMc MIc STc BNm1 Um1.
    replace (ret_pc (Z_to_bv 64 0x14fd28)) with (Z_to_bv 64 0x14fd28) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [tbind fst snd]. cbv beta iota. fold bm.
    destruct (is_odd_pure bm) eqn:ODD; cbn [Z.b2z negb]; cbv beta iota.
    2: {
         step. if_true. ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    step. if_false.

    destruct (KOPENU _ _ _ _ _ rm arm ENV4 LS4 HAm NROm) as (Dm2 & BNm2 & Um2 & _ & _ & _ & _ & _ & ALm2 & UPm2). fold bm in BNm2, Um2, UPm2.
    eapply evt_cut.
    { eapply mw_rem_walk with (A := A) (AM := arm) (D := Dm2) (b := bm);
        [exact BNm2| exact Um2| exact OKm1| exact OKm2| clear - OKm3; unfold BG_DMAX in OKm3; lia| unfold BW in AB; exact AB| exact ALm2| exact UPm2| exact ODD]. }
    clear BNm2 Um2.
    intros ms' (a1r & ->).
    cbv zeta.
    assert (AW0 : 0 <= (if (bn_top bm =? 1)%nat then A mod nth 0 (bn_buf bm) 0 else A) < 2^64).
    { destruct (bn_top bm =? 1)%nat; [|unfold BW in AB; exact AB].
      assert (Hl : limb (nth 0 (bn_buf bm) 0)).
      { unfold is_odd_pure in ODD. apply andb_true_iff in ODD. destruct ODD as [T0 _]. apply Nat.ltb_lt in T0.
        apply (proj1 (List.Forall_nth limb (bn_buf bm)) OKm1). unfold bn_dmax in OKm2. clear - T0 OKm2. lia. }
      assert (D0 : nth 0 (bn_buf bm) 0 <> 0).
      { unfold is_odd_pure in ODD. apply andb_true_iff in ODD. destruct ODD as [_ OD]. intros E. rewrite E in OD. discriminate OD. }
      unfold limb, BW in Hl. pose proof (Z.mod_pos_bound A (nth 0 (bn_buf bm) 0) ltac:(clear - Hl D0; lia)) as MB. clear - Hl MB. lia. }
    set (a := if (bn_top bm =? 1)%nat then A mod nth 0 (bn_buf bm) 0 else A) in *.

    destruct (KOPENU _ _ _ _ _ rp arp ENV4 LS4 HAp NROp) as (Dp' & BNp & Up & _ & _ & _ & SEPDp' & _ & ALp' & UPp'). fold bp in BNp, Up, SEPDp', UPp'.
    pose proof ENV4 as (_ & _ & ST4 & _ & MI4 & _).
    step.
    eapply evt_cut.
    { eapply (BN_num_bits_spec _ (Z_to_bv 64 (bv_unsigned sp + -128))) with (lo := lo) (A := arp) (D := Dp') (b := bp);
        [exact BNp | exact ALp' | exact UPp' | exact Up | exact OKp1 | exact OKp2 | clear - OKp3; unfold BG_DMAX in OKp3; lia | clear - FLp; lia | exact CTp
        | rewrite ESP; exact ST4 | rewrite ESP; clear - LOF CS96; lia | exact MI4
        | rewrite ESP; clear - SEPp FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDp' FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST4 MI4.
    intros ms5 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (KBELOW _ _ _ _ m5 _ 128 ENV4 LS4 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV5 & LS5). clear ENV4 LS4 MUc WMc MIc STc BNp Up.
    replace (ret_pc (Z_to_bv 64 0x14fd68)) with (Z_to_bv 64 0x14fd68) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      { eapply (BN_abs_is_word_spec _ (Z_to_bv 64 (bv_unsigned sp + -128))) with (lo := lo) (A := arm) (D := Dm') (b := bm);
          [exact BNm | exact ALm' | exact UPm' | exact Um | exact OKm1 | exact OKm2 | clear - OKm3; unfold BG_DMAX in OKm3; lia
          | rewrite ESP; exact ST5 | rewrite ESP; clear - LOF CS96; lia | exact MI5
          | rewrite ESP; clear - SEPm FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDm' FBlo FBsp CS96 LOF; lia | reflexivity]. }
      clear ST5 MI5.
      intros ms6 PO. unfold bn_small_post in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MUc & WMc & MIc & STc & ->).
      rewrite ESP in *. rewrite (unsigned_lit 1) by lia.
      destruct (KBELOW _ _ _ _ m6 _ 16 ENV5 LS5 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV6 & LS6). clear ENV5 LS5 MUc WMc MIc STc BNm Um.
      replace (ret_pc (Z_to_bv 64 0x14ff68)) with (Z_to_bv 64 0x14ff68) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct (abs_is_word_pure bm 1); cbn [Z.b2z].
      -
        step. if_false. step. step.
        eapply (zero_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
          [clear - LOF CS96; lia | reflexivity | exact ENV6 | exact LS6 | exact HAr | exact (hpl_wref _ _ WRr) |].
        intros m7 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV7 LS7.
        replace (ret_pc (Z_to_bv 64 0x14ff74)) with (Z_to_bv 64 0x14ff74) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        ihere. to_implM. unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
        pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m _ _ _ _ _ ENV7) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
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
        destruct (kenv_tail LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK
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
    step. if_cases KA; rewrite ?unsigned_lit in KA by exact AW0; zify_cond KA.
    {
      replace (a =? 0) with true by (symmetry; apply Z.eqb_eq; clear - KA AW0; lia).
      step. step.
      eapply (zero_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
        [clear - LOF CS96; lia | reflexivity | exact ENV5 | exact LS5 | exact HAr | exact (hpl_wref _ _ WRr) |].
      intros m7 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV7 LS7.
      replace (ret_pc (Z_to_bv 64 0x14ff80)) with (Z_to_bv 64 0x14ff80) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      ihere. to_implM. unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
      pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m _ _ _ _ _ ENV7) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
      step. step. step. do 13 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists m7, OW, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LS7|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
    }
    replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KA AW0; lia).
    assert (AR : 0 < a < 2^64) by (clear - KA AW0; lia).
    destruct HFR as (HF1 & HF2 & HF3 & HFM & HFT).
    unfold mw_rest, bbind. cbn [bind tree_ops tbind fst snd]. cbv beta.

    step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV5 LS5 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_start_walk; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & OW7 & -> & KP & (_ & INCL7)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV5 KP) as (ENV7 & LS7). pose proof KP as RS7; apply kpost_refs in RS7.
    cbn [fst snd] in *. clear PRE1 KP ENV5 LS5.
    replace (ret_pc (Z_to_bv 64 0x14fd7c)) with (Z_to_bv 64 0x14fd7c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV7 LS7 LOF) as (errv2 & PRE2).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [r bs2] st2 ms2 PO. apply BPK in PO; [|intros v b o p a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & OW8 & -> & KP & (_ & (ri & Er) & (ar & HAr1 & ->) & INCL8)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV7 KP) as (ENV8 & LS8). pose proof KP as RS8; apply kpost_refs in RS8.
    cbn [fst snd] in *. clear PRE2 KP ENV7 LS7.
    replace (ret_pc (Z_to_bv 64 0x14fd84)) with (Z_to_bv 64 0x14fd84) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV8 LS8 LOF) as (errv3 & PRE3).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE3| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [t bs3] st3 ms3 PO. apply BPK in PO; [|intros v b o p a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & OW9 & -> & KP & (_ & (ti & Et) & (at_ & HAt1 & ->) & INCL9)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV8 KP) as (ENV9 & LS9). pose proof KP as RS9; apply kpost_refs in RS9.
    cbn [fst snd] in *. clear PRE3 KP ENV8 LS8.
    replace (ret_pc (Z_to_bv 64 0x14fd90)) with (Z_to_bv 64 0x14fd90) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS9 HAr1) as HAr9.
    pose proof ENV9 as (HEAP9 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS9) as PARTS9.
    assert (FROK9 : frames_ok PL (bv_unsigned sp + -128) B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
    assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP9 PARTS9 FROK9 HAt1 NROt) as (At0 & AtC & _).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtC SPR; lia). clear AtC HEAP9 PARTS9.
    unfold implM. iprefix.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. step.

    step. if_true.
    step.
    destruct (KPRE _ _ _ _ _ CS ENV9 LS9 LOF) as (errv4 & PRE4).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (BN_MONT_CTX_new_lwalk_cs HM CS CSnew); [exact PRE4| reflexivity| exact HFM]. }
    cbv beta. intros [pm bs5] st5 ms5 PO. unfold bn_post in PO. rewrite ESP in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m11 & OW11 & PL' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & (am & -> & -> & AMR & -> & Ebs5)).
    cbn [fst snd] in *. subst bs5.
    set (PLm := pl_set_mont PL (Some (am, pm))) in *.
    assert (KP1 : kpost LB PLm EA lo B (bv_unsigned sp + -128) st3 bs3 m9 OW9 st5 (st_mont_init bs3) m11 ((pm, am, 96) :: OW9)).
    { unfold kpost. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exists errv'; exact P5|]. split; [exact P6|].
      split; [exact P7|]. split; [exact P8|]. split; [exact P9| exact P10]. }
    destruct (kenv_post LB PLm EA lo B (bv_unsigned sp) (bv_unsigned sp + -128) s bs OW m CEIL GLO' FBlo FBsp FROK _ _ _ _ _ _ _ _ _ ENV9 KP1) as (ENV11 & LS11).
    clear PRE4 KP1 P1 P2 P3 P4 P5 P6 P7 P8 P9.
    replace (ret_pc (Z_to_bv 64 0x14ffe0)) with (Z_to_bv 64 0x14ffe0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (ESPV : bv_unsigned sp = bv_unsigned sp + -128 + 128) by (clear; lia).
    pose proof (L_set ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL EA rr rp arr arp ac qc am pm (bv_unsigned sp + -128) (bv_unsigned sp)
                  ESPV CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK LOF HPC HFM AMR ltac:(clear - SP16; lia)
                  (ref_at_mont_fresh bs OW PL (Some (am, pm)) rr arr HFM HAr) WRr rm arm
                  (ref_at_mont_fresh bs OW PL (Some (am, pm)) rp arp HFM HAp) NROp
                  (ref_at_mont_fresh bs OW PL (Some (am, pm)) rm arm HFM HAm) NROm a AR HFT
                  st5 (st_mont_init bs3) m11 ((pm, am, 96) :: OW9) r t ar at_ ri ti bits w0 e0 r0) as LN.
    unfold FINALQ in LN. rewrite (Z_to_bv_bv_unsigned sp) in LN.
    eapply LN; [exact ENV11| exact LS11
               | exact (ref_at_mont_fresh _ _ PL (Some (am, pm)) _ _ HFM (ref_at_stable _ _ _ _ PL _ _ P10 HAr9))| exact Er
               | exact (ref_at_mont_fresh _ _ PL (Some (am, pm)) _ _ HFM (ref_at_stable _ _ _ _ PL _ _ P10 HAt1))| exact Et| exact BITS24].
  Qed.
End Proofs.
End WithCeiling0.
