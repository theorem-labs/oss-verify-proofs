(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnDivWords BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Cells Step Arr Bytes Frame.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_lshiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF W_set_wordAF W_mul_wordAF W_cmpAF AFrameComp ExpKitAF W_small3A W_calls3AF W_nnmodAF ExpStmtF ExpBodyKitF PlaceMont PlaceKitA W_mont_ctxAF W_mont_freeAF MontKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2855380 => 2
  | 2855384 => 1
  | 2855388 => 2
  | 2855444 => 2
  | 2855448 => 1
  | 2855452 => 2
  | 2855476 => 2
  | 2855556 => 2
  | 2855584 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Local Notation ops := (tree_ops bptr).
Local Notation BMu := (BM (M:=btree bptr) (ptr:=bptr)).

Definition BN_MOD_EXP_MONT_WORD : Z := 0x2b90d4.

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

Lemma ref_at_mont_fresh : forall (st : bstate bptr) OW PL x r a, pl_mont PL = None -> ref_at st OW PL r a -> ref_at st OW (pl_set_mont PL x) r a.
Proof.
  intros st OW PL x r a E H. destruct (mont_ref r) eqn:MR.
  - exfalso. pose proof (pl_of_mont_none PL r E MR) as N.
    assert (RF : (r < NFIX)%nat) by (destruct (mont_ref_cases r MR) as [-> | [-> | -> ]]; unfold RMontRR, RMontN, RMontNi, NFIX; lia).
    apply (proj1 (ref_at_fixed st OW PL r a RF)) in H. destruct H as (p & Ep & _). rewrite N in Ep. discriminate Ep.
  - apply ref_at_pl_mont_other; [exact MR| exact H].
Qed.

Lemma ref_at_mont_enter : forall (st : bstate bptr) OW PL r a (b : block) x, pl_mont PL = None -> ref_at st OW PL r a ->
  ref_at (st_mont_init st) (b :: OW) (pl_set_mont PL x) r a.
Proof.
  intros st OW PL r a b x E H. unfold st_mont_init. apply ref_at_setbn, ref_at_setbn, ref_at_setbn, ref_at_set_mont.
  apply ref_at_mont_fresh; [exact E|]. eapply ref_at_ow_mono; [| exact H]. intros y Hy. right. exact Hy.
Qed.

Lemma mw_rem_walkA : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mb m : mem) (W : list (Z * Z)) (A AM D : Z) (b : bignum bptr),
  rw_cells bgbsegs m AM (BnRepDefs.bn_cells D b) -> u64arr bgbsegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) <= 512 -> 0 <= A < 2^64 ->
  acc bgbsegs mb AM 24 -> AM mod 8 = 0 -> 0 < AM -> AM + 24 <= 140737488355328 ->
  acc bgbsegs mb D (8 * Z.of_nat (bn_top b)) -> D mod 8 = 0 -> 0 <= D /\ D + 8 * Z.of_nat (bn_top b) <= 140737488355328 ->
  munch W mb m -> offshW W -> ub_ptr_ok (Z.of_nat (bn_top b)) D -> is_odd_pure b = true ->
  evt bgbsegs (fun ms' => exists x11 : word,
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 s7 x11 a2 a3 a4 a5 a6 a7
                   s2 s4 (Z_to_bv 64 (if (bn_top b =? 1)%nat then A mod (nth 0 (bn_buf b) 0) else A)) (Z_to_bv 64 AM) (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 2855488) fc None m (seg_rom bgbsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s4 (Z_to_bv 64 A) (Z_to_bv 64 AM) (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 2855392) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN U LB HT HD HA ACC AL A0 AC ACCD ALD BD MU OFF UBP ODD.
  unfold BnRepDefs.bn_cells, MallocRep.wz in BN.
  do 3 step. shl_with ACC AL. chk0.
  step. rewrite (sx32_small (Z.of_nat (bn_top b))) by (clear - HT HD; lia).
  step.
  step. if_cases KT; rewrite ?unsigned_lit in KT by (clear - HT HD; lia); zify_cond KT.
  - replace (bn_top b =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; clear - KT; lia).
    step. apply evt_done. eexists. reflexivity.
  - replace (bn_top b =? 1)%nat with true by (symmetry; apply Nat.eqb_eq; clear - KT; lia).
    assert (NTH0 : nth_error (wlimbs (bn_buf b)) (Z.to_nat 0) = Some (Z_to_bv 64 (nth 0 (bn_buf b) 0))).
    { apply nth_error_wlimbs. unfold bn_dmax in HT. clear - HT KT. lia. }
    assert (L0 : 0 <= nth 0 (bn_buf b) 0 < 2^64).
    { assert (Hl : limb (nth 0 (bn_buf b) 0)) by (apply (proj1 (List.Forall_nth limb (bn_buf b)) LB); unfold bn_dmax in HT; clear - HT KT; lia). unfold limb, BW in Hl. exact Hl. }
    destruct (UBP ltac:(clear - KT; lia)) as (PD0 & PD8).
    assert (N0 : nth 0 (bn_buf b) 0 <> 0).
    { unfold is_odd_pure in ODD. apply andb_true_iff in ODD. destruct ODD as [_ OD]. intros E0. rewrite E0 in OD. discriminate OD. }
    do 2 step. shl_with ACC AL. chk0.
    step.
    hide_ors. ub. unhide.
    do 2 step. shl_limb ACCD ALD BD 0. chk0.
    let a := cur_mem_addr in pose proof (u64arr_read bgbsegs m D _ 0 _ a U NTH0 ltac:(clear; lia) ltac:(addr_tac)) as RD.
    step. clear RD.
    rewrite ?(unsigned_lit (nth 0 (bn_buf b) 0)) by exact L0.
    hide_ors. ub. unhide.
    step.
    change (mul_div Instr.M_REMU (Z_to_bv 64 A) (Z_to_bv 64 (nth 0 (bn_buf b) 0)))
      with (if (bv_unsigned (Z_to_bv 64 (nth 0 (bn_buf b) 0)) =? 0)%Z then Z_to_bv 64 A else bv_modu (Z_to_bv 64 A) (Z_to_bv 64 (nth 0 (bn_buf b) 0))).
    rewrite (unsigned_lit (nth 0 (bn_buf b) 0)) by exact L0.
    destruct (Z.eqb_spec (nth 0 (bn_buf b) 0) 0) as [E0|_]; [exfalso; exact (N0 E0)|].
    + replace (bv_modu (Z_to_bv 64 A) (Z_to_bv 64 (nth 0 (bn_buf b) 0))) with (Z_to_bv 64 (A mod nth 0 (bn_buf b) 0)).
      2: { pose proof (Z.mod_pos_bound A (nth 0 (bn_buf b) 0) ltac:(clear - L0 N0; lia)) as MB.
           apply bv_eq. rewrite bv_modu_unsigned, !unsigned_lit by (clear - HA L0 MB; lia). reflexivity. }
      step. apply evt_done. eexists. reflexivity.
Qed.

Section Body.
Context {AR1 : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR1).
Local Notation AF := (@ar_AF AR1).
Local Notation PMc := (@ar_PMc AR1).
Local Notation ACEIL := (@BnHeapA.ACEIL AR1).
Local Notation AHEAP := (@BnHeapA.AHEAP AR1).

Section Proofs.

  Variables (CS CMM CFM CMS : Z).
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CSsetw : BN_SET_WORD_STACK <= CS.
  Hypothesis CSmulw : BN_MUL_WORD_STACK <= CS.
  Hypothesis CSdiv : BN_DIV_TOP_STACK <= CS.
  Hypothesis CSnb : BN_NUM_BITS_STACK <= CS.
  Hypothesis CSnew : BN_MONT_CTX_NEW_STACK <= CS.
  Hypothesis CSfree : BN_MONT_CTX_FREE_STACK <= CS.
  Hypothesis CMM0 : 0 <= CMM.
  Hypothesis CFM0 : 0 <= CFM.
  Hypothesis CMS0 : 0 <= CMS.

  Hypothesis BN_mod_mul_montgomery_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ rb : bnref) (ar aa ab am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x225d38 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> ref_at ls OW PL rb ab -> wref PL rr -> rb <> ROne -> nbuf PL ra_ -> nbuf PL rb ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz ab -> a3 = wz am -> a4 = wz ac ->
    implA (BN_mod_mul_montgomery (tree_ops bptr) rr ra_ rb ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x225d38) fc None m (seg_rom bgbsegs)).
  Hypothesis BN_to_montgomery_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x225750 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> nbuf PL ra_ ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (BN_to_montgomery (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x225750) fc None m (seg_rom bgbsegs)).
  Hypothesis BN_from_montgomery_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CFM ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x22646c (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> ra_ <> ROne ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (BN_from_montgomery (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CFM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x22646c) fc None m (seg_rom bgbsegs)).
  Hypothesis BN_MONT_CTX_set_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rd : bnref) (ad am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMS ->
    fr_room 3 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x2267e8 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rd ad -> rd <> ROne -> pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) -> pl_bn PL RTmod = None ->
    a0 = wz am -> a1 = wz ad -> a2 = wz ac ->
    implA (BN_MONT_CTX_set (tree_ops bptr) rd ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMS (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x2267e8) fc None m (seg_rom bgbsegs)).

  Definition MW_FLC : Z := 2 * MC + CMM + BN_DIV_FT_COST.
  Definition MW_ROUNDC : Z := 2 * MW_FLC + CMM.
  Definition EXP_MW_TOTAL : Z := 4 * MC + CMS + 32768 * MW_ROUNDC + MW_FLC + CFM + MC.
  Definition BN_MOD_EXP_MONT_WORD_STACK : Z := 128 + CS.

  Lemma MC0 : 0 <= MC. Proof. unfold MC. lia. Qed.
  Lemma DC0 : 0 <= BN_DIV_FT_COST. Proof. unfold BN_DIV_FT_COST, MC. lia. Qed.
  Lemma FLC0 : 0 <= MW_FLC. Proof. unfold MW_FLC. pose proof MC0. pose proof DC0. lia. Qed.
  Lemma ROUNDC0 : 0 <= MW_ROUNDC. Proof. unfold MW_ROUNDC. pose proof FLC0. lia. Qed.

  Section Fixed.

    Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (ls : bstate bptr) (m : mem) (OW LB : list block) (PL0 : placement) (EA : BnRepDefs.err_addrs).
    Variables (lo : Z) (ras : list Z).
    Variables (rr rp rm : bnref) (arr arp arm ac : Z) (qc : bptr).
    Local Notation FB := (bv_unsigned sp + -128).
    Local Notation SPv := (bv_unsigned sp).
    Local Notation TOTAL := EXP_MW_TOTAL.
    Hypothesis LOK : lo <= FB - CS.
    Hypothesis ROOM : fr_room 3 ls OW LB.
    Hypothesis TIGHT : cnt_bal ls OW + Z.of_nat (length LB) + 72 <= LIVE_MAX.
    Hypothesis CTX : uk_ctx BN_MOD_EXP_MONT_WORD (bv_unsigned ra :: ras).
    Hypothesis HPC : pl_ctx PL0 = Some (ac, qc).
    Hypothesis HFM : pl_mont PL0 = None.
    Hypothesis HFT : pl_bn PL0 RTmod = None.
    Hypothesis HAr : ref_at ls OW PL0 rr arr.
    Hypothesis HAp : ref_at ls OW PL0 rp arp.
    Hypothesis HAm : ref_at ls OW PL0 rm arm.
    Hypothesis WRr : hpl PL0 rr.
    Hypothesis NROp : rp <> ROne.
    Hypothesis NROm : rm <> ROne.

    Definition efrW (mo t b : word) : list cell := [C8 mo; C8 t; C8 b; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
    Definition MWPOST : unit * bstate bptr -> rts RT -> machine_state -> Prop :=
      bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL0 EA TOTAL
               (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL0 /\ a0' = wz 1).
    Local Notation Q := MWPOST.

    Lemma NROr : rr <> ROne. Proof. exact (proj1 (hpl_wref _ _ WRr)). Qed.

    Ltac lstep v := step;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
      | |- _ => idtac
      end.

    Ltac strip2 l := lazymatch l with
      | cons _ (cons _ nil) => constr:(@nil cell)
      | cons ?x ?t => let r := strip2 t in constr:(cons x r)
      end.

    Ltac relocal EV LS MU WM ST MI FR FSZ EV' LS' :=
      unfold efrW in FSZ; cbn [app cells_size csize Nat.add] in FSZ;
      lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
        destruct (cenv_localA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ EV LS MU WM ltac:(clear; lia) ltac:(clear - FSZ; lia) ST MI FR
                    ltac:(cbn [cells_size csize Nat.add app]; clear - FSZ; lia)) as (EV' & LS') end.

    Local Ltac kit EV :=
      pose proof EV as (OK & _);
      pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROKK & _ & _);
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK (proj1 (proj2 EV))) as ESP;
      pose proof (AH_ceil _ _ _ _ (proj1 (proj2 EV))) as (CE1 & CE2 & CE3); unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CE1, CE2, CE3;
      assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia);
      assert (LOFB16 : lo <= FB - 16) by (clear - LOK CS16; lia);
      pose proof MC0 as MCP; pose proof DC0 as DCP; pose proof FLC0 as FLP; pose proof ROUNDC0 as RCP.

    Lemma mw_retA : forall (mo t b : word) used ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      cenvA LB PL0 lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m (efrW mo t b) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL0 EA -> used <= TOTAL ->
      implA (TRet (tt, lsK)) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7
                   x18 x20 x22 x21 x19 x23 x24 x25 x26 (Z_to_bv 64 1) t3 t4 t5 t6)
            F (Z_to_bv 64 2855304) fc None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc. intros EVK LSK USED. kit EVK. unfold MallocRep.wz in *.
      apply implA_ret_evt.
      destruct (cenv_finalA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ EVK LSK USED) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      pose proof EVK as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). unfold efrW in FRF. cbn [app] in FRF.
      step. do 13 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold MWPOST, bn_postA. do 17 eexists. exists mK, OWK, PL0. split; [reflexivity|]. cbn [fst snd].
      split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
      split; reflexivity.
    Qed.

    Section Scope.
      Variables (am : Z) (qm : bptr).
      Hypothesis AMR : 0 < am < 2 ^ 63.
      Local Notation PL := (pl_set_mont PL0 (Some (am, qm))).
      Local Notation CENV := (cenvA LB PL lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m).
      Lemma HPM : pl_mont PL = Some (am, qm). Proof. reflexivity. Qed.
      Lemma HPCS : pl_ctx PL = Some (ac, qc). Proof. exact HPC. Qed.
      Lemma ROOMS : fr_room 3 ls ((qm, am, 96) :: OW) LB.
      Proof. apply fr_room_mont; [exact ROOM | clear - TIGHT; unfold block in *; lia]. Qed.
      Lemma WRrS : wref PL rr. Proof. apply hpl_wref. apply hpl_pl_mont. exact WRr. Qed.
      Lemma HArS : ref_at ls ((qm, am, 96) :: OW) PL rr arr.
      Proof. apply ref_at_mont_fresh; [exact HFM|]. eapply ref_at_ow_mono; [| exact HAr]. intros b Hb. right. exact Hb. Qed.
      Lemma HApS : ref_at ls ((qm, am, 96) :: OW) PL rp arp.
      Proof. apply ref_at_mont_fresh; [exact HFM|]. eapply ref_at_ow_mono; [| exact HAp]. intros b Hb. right. exact Hb. Qed.
      Lemma HAmS : ref_at ls ((qm, am, 96) :: OW) PL rm arm.
      Proof. apply ref_at_mont_fresh; [exact HFM|]. eapply ref_at_ow_mono; [| exact HAm]. intros b Hb. right. exact Hb. Qed.

      Lemma mw_exitA : forall (t b : word) used ΣK lsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) t b) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> used <= TOTAL ->
        implA (bbind ops (BN_MONT_CTX_free ops qm) (fun _ => BN_CTX_end ops) lsK) ΣK Q
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) x20 x22 x21 x19 x23 x24 x25 x26 x27 t3 t4 t5 t6)
              F (Z_to_bv 64 2856288) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc. intros EVK LSK USED. kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        apply implA_from_evt. step. step. if_false. step. step.

        apply evt_done.
        eapply (mont_free_callA (fun _ => BN_CTX_end ops) Q LB PL0 EA lo SPv FB s0 ra ras TOTAL Σ ls OW m _ _ ΣK lsK mK OWK am qm);
          [ exact EVK | exact LSK | exact HFM | reflexivity | clear - LOK CSfree; lia | exact USED | reflexivity
          | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9388 CTX) |].
        intros ΣF lsF mF OWF z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 FF fcF EVF LSF.
        rewrite (ret_pc_even 2856304) by (clear; lia).
        pose proof EVF as (OKF & _).
        unfold MallocRep.wz. apply implA_from_evt. do 2 step.

        apply evt_done.
        eapply implA_post.
        { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OWF) (LB := LB) (PL := PL0) (EA := EA);
            [| reflexivity | exact HPC | reflexivity].
          eapply cenv_preA; [exact EVF | exact LSF | clear - LOK CSend; lia | clear - USED MCP; lia]. }
        cbv beta. intros [uE lsE] ΣE msE PO.
        apply (bn_postA_cpost LB PL0 EA lo SPv FB TOTAL Σ ls OW) in PO; [| exact OKF | exact (proj1 (proj2 EVF))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FE & fcE & mE & OWE & PLE & -> & CPE & (EPLE & EOWE)).
        subst PLE. specialize (CPE eq_refl).
        destruct (cenv_postA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EVF CPE) as (EVE & LSE).
        rewrite (ret_pc_even 2856312) by (clear; lia).
        unfold MallocRep.wz. apply implA_from_evt. step.
        apply evt_done. destruct uE. eapply mw_retA; [exact EVE | exact LSE | clear - USED MCP; lia].
      Qed.

      Lemma mw_fromA : forall (t b : word) used ΣK lsK mK OWK (r : bnref) (ar : Z) (ri : nat)
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x22 x24 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) t b) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> used + CFM <= TOTAL ->
        ref_at lsK OWK PL r ar -> r = RPool ri ->
        implA (bbind ops (BN_from_montgomery ops rr r) (fun _ => bbind ops (BN_MONT_CTX_free ops qm) (fun _ => BN_CTX_end ops)) lsK) ΣK Q
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) x22 (Z_to_bv 64 arm) x19 (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 x27 t3 t4 t5 t6)
              F (Z_to_bv 64 2856264) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc. intros EVK LSK KCOST HArK Er. kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HArS) as HArrK.
        unfold bbind at 1. cbn [bind tree_ops].
        apply implA_from_evt. do 5 step.
        apply evt_done.
        eapply implA_bind.
        { eapply (BN_from_montgomery_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA);
            [| | | reflexivity | exact HArrK | exact HArK | exact WRrS | rewrite Er; unfold RPool, ROne, NFIX; clear; lia | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity].
          - eapply cenv_preA; [exact EVK | exact LSK | exact LOK | clear - KCOST CFM0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9374 CTX).
        }
        cbv beta. intros [ueA lseA] ΣeA mseA PO.
        apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FeA & fceA & meA & OWeA & PLeA & -> & CPeA & (EPLeA & ->)).
        subst PLeA. specialize (CPeA eq_refl).
        destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EVK CPeA) as (EVeA & LSeA).
        clear CPeA.
        rewrite (ret_pc_even 2856284) by (clear; lia).
        unfold MallocRep.wz. apply implA_from_evt. step. if_false.
        apply evt_done. eapply mw_exitA; [exact EVeA | exact LSeA | clear - KCOST; lia].
      Qed.

      Lemma mw_oneA : forall (t b : word) used ΣK lsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x22 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) t b) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> used + MC <= TOTAL ->
        implA (bbind ops (BN_one ops rr) (fun _ => bbind ops (BN_MONT_CTX_free ops qm) (fun _ => BN_CTX_end ops)) lsK) ΣK Q
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) x22 (Z_to_bv 64 arm) x19 (Z_to_bv 64 arp) x24 x25 x26 x27 t3 t4 t5 t6)
              F (Z_to_bv 64 2856184) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc. intros EVK LSK KCOST. kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HArS) as HArrK.
        unfold BN_one. unfold bbind at 1. cbn [bind tree_ops].
        apply implA_from_evt. do 3 step.
        apply evt_done.
        eapply implA_bind.
        { eapply (BN_set_word_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rx := rr) (ax := arr) (w := 1);
            [| | | reflexivity | exact HArrK | exact WRrS | reflexivity | reflexivity | clear; lia].
          - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSsetw; lia | exact KCOST].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b931c CTX).
        }
        cbv beta. intros [ueA lseA] ΣeA mseA PO.
        apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FeA & fceA & meA & OWeA & PLeA & -> & CPeA & (EPLeA & -> & _)).
        subst PLeA. specialize (CPeA eq_refl).
        destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EVK CPeA) as (EVeA & LSeA).
        clear CPeA.
        rewrite (ret_pc_even 2856196) by (clear; lia).
        unfold MallocRep.wz. apply implA_from_evt. step. if_false. step.
        apply evt_done. eapply mw_exitA; [exact EVeA | exact LSeA | clear - KCOST; lia].
      Qed.

      Lemma L_fin_oneA : forall used ΣK lsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (b ts : word)
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x24 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) ts b) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL r ar -> r = RPool ri -> ref_at lsK OWK PL t at_ -> t = RPool ti -> 0 <= w < 2^64 ->
        w <> 1 -> used + MW_FLC + CFM <= TOTAL ->
        implA (mw_fin rr rm qm (r, t, w, true) lsK) ΣK Q
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 w) (Z_to_bv 64 arm) x19 (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 x27 t3 t4 t5 t6)
              F (Z_to_bv 64 2856224) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc; intros EVK LSK HArK Er HAtK Et WR W1 KCOST.
        kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAmS) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HApS) as HApK.
        assert (NROq : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; clear; lia).
        assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; clear; lia).
        assert (WRq : wref PL r) by (rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri))).
        assert (NBq : nbuf PL r) by (rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri))).
        assert (HPt : hpl PL t) by (rewrite Et; exact (hpl_pool PL ti)).
        unfold MW_FLC in KCOST.
        unfold mw_fin. cbv zeta. replace (w =? 1) with false by (symmetry; apply Z.eqb_neq; exact W1).
        unfold mw_flush, mw_to_mont_word, mw_mod_mul_word, BN_mod, bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
        apply implA_from_evt. do 3 step.
        apply evt_done.
        apply implA_tbind_assoc. apply implA_tbind_assoc. eapply implA_bind.
        { eapply (BN_set_word_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rx := r) (ax := ar) (w := w);
            [| | | reflexivity | exact HArK | exact WRq | reflexivity | reflexivity | exact WR].
          - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSsetw; lia | clear - KCOST MCP DCP FLP RCP CMM0 CFM0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9344 CTX).
        }
        cbv beta. intros [u5 ls5] Σ5 ms5 PO.
        apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & -> & _)).
        subst PL5. specialize (CP5 eq_refl).
        destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EVK CP5) as (EV5 & LS5).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5. clear CP5.
        rewrite (ret_pc_even 2856236) by (clear; lia).
        pose proof EV5 as (_ & _ & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold efrW in FR5. cbn [app] in FR5.
        unfold MallocRep.wz. apply implA_from_evt.
        step. if_false. do 5 step.
        apply evt_done.
        eapply implA_bind.
        { eapply (BN_to_montgomery_walkA) with (lo := lo) (OW := OW5) (LB := LB) (PL := PL) (EA := EA) (rr := r) (ra_ := r);
            [| | | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact WRq | exact NBq | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity].
          - eapply cenv_preA; [exact EV5 | exact LS5 | exact LOK | clear - KCOST MCP DCP FLP RCP CMM0 CFM0; lia].
          - eapply cenv_roomA; [exact EV5 | exact ROOMS | clear; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV5).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b935c CTX).
        }
        cbv beta. intros [u6 ls6] Σ6 ms6 PO.
        apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV5))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & PL6 & -> & CP6 & (EPL6 & ->)).
        subst PL6. specialize (CP6 eq_refl).
        destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EV5 CP6) as (EV6 & LS6).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP6) as RS6. clear CP6.
        rewrite (ret_pc_even 2856260) by (clear; lia).
        pose proof EV6 as (_ & _ & ST6 & MI6 & _ & _ & _ & _ & FR6 & FSZ6 & _). unfold efrW in FR6. cbn [app] in FR6.
        unfold MallocRep.wz. apply implA_from_evt.
        step. if_false.
        cbn [tbind fst snd]. cbv beta iota.
        apply evt_done.
        eapply (mw_fromA ts b _ _ ls6 m6 OW6 r ar ri); [exact EV6 | exact LS6 | clear - KCOST MCP DCP FLP RCP CMM0 CFM0; lia | exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)) | exact Er].
      Qed.

      Lemma L_fin_mulA : forall used ΣK lsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (b : word)
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x24 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) b) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL r ar -> r = RPool ri -> ref_at lsK OWK PL t at_ -> t = RPool ti -> 0 <= w < 2^64 ->
        w <> 1 -> used + MW_FLC + CFM <= TOTAL ->
        implA (mw_fin rr rm qm (r, t, w, false) lsK) ΣK Q
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) x22 (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 x27 t3 t4 t5 t6)
              F (Z_to_bv 64 2856316) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc; intros EVK LSK HArK Er HAtK Et WR W1 KCOST.
        kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAmS) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HApS) as HApK.
        assert (NROq : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; clear; lia).
        assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; clear; lia).
        assert (WRq : wref PL r) by (rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri))).
        assert (NBq : nbuf PL r) by (rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri))).
        assert (HPt : hpl PL t) by (rewrite Et; exact (hpl_pool PL ti)).
        unfold MW_FLC in KCOST.
        unfold mw_fin. cbv zeta. replace (w =? 1) with false by (symmetry; apply Z.eqb_neq; exact W1).
        unfold mw_flush, mw_to_mont_word, mw_mod_mul_word, BN_mod, bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
        apply implA_from_evt. do 3 step.
        apply evt_done.
        apply implA_tbind_assoc. eapply implA_bind.
        { eapply (BN_mul_word_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rx := r) (ax := ar) (w := w);
            [| | | reflexivity | exact HArK | exact WRq | reflexivity | reflexivity | exact WR].
          - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSmulw; lia | clear - KCOST MCP DCP FLP RCP CMM0 CFM0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b93a0 CTX).
        }
        cbv beta. intros [u5 ls5] Σ5 ms5 PO.
        apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & -> & _)).
        subst PL5. specialize (CP5 eq_refl).
        destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EVK CP5) as (EV5 & LS5).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5. clear CP5.
        rewrite (ret_pc_even 2856328) by (clear; lia).
        pose proof EV5 as (_ & _ & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold efrW in FR5. cbn [app] in FR5.
        unfold MallocRep.wz. apply implA_from_evt.
        step. if_false. do 7 step.
        apply evt_done.
        apply implA_tbind_assoc. eapply implA_bind.
        { eapply (BN_div_walkA) with (lo := lo) (OW := OW5) (LB := LB) (PL := PL) (EA := EA) (dv := None) (rm := Some t) (adv := 0) (arm := at_) (num := r) (dvs := rm);
            [| | | reflexivity | exact HPCS | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAmK) | intros d0 Ed0; discriminate Ed0 | intros r0 Er0; injection Er0 as <-; exact HPt | exact NROq | exact NROm | exact NBq | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
          - eapply cenv_preA; [exact EV5 | exact LS5 | clear - LOK CSdiv; lia | clear - KCOST MCP DCP FLP RCP CMM0 CFM0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV5).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b93c0 CTX).
        }
        cbv beta. intros [u6 ls6] Σ6 ms6 PO.
        apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV5))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & PL6 & -> & CP6 & (EPL6 & ->)).
        subst PL6. specialize (CP6 eq_refl).
        destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EV5 CP6) as (EV6 & LS6).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP6) as RS6. clear CP6.
        rewrite (ret_pc_even 2856360) by (clear; lia).
        pose proof EV6 as (_ & _ & ST6 & MI6 & _ & _ & _ & _ & FR6 & FSZ6 & _). unfold efrW in FR6. cbn [app] in FR6.
        unfold MallocRep.wz. apply implA_from_evt.
        step. step. if_false. step.
        cbn [tbind fst snd]. cbv beta iota.
        apply evt_done.
        eapply (mw_fromA (Z_to_bv 64 at_) b _ _ ls6 m6 OW6 t at_ ti); [exact EV6 | exact LS6 | clear - KCOST MCP DCP FLP RCP CMM0 CFM0; lia | exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK)) | exact Et].
      Qed.

      Lemma L_finalA : forall used ΣK lsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (one : bool) (b : word)
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x24 x26 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) b) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL r ar -> r = RPool ri -> ref_at lsK OWK PL t at_ -> t = RPool ti -> 0 <= w < 2^64 ->
        used + MW_FLC + CFM + MC <= TOTAL ->
        implA (mw_fin rr rm qm (r, t, w, one) lsK) ΣK Q
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) x22 (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 (Z_to_bv 64 (Z.b2z one)) t3 t4 t5 t6)
              F (Z_to_bv 64 2856172) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc; intros EVK LSK HArK Er HAtK Et WR KCOST.
        kit EVK. unfold MallocRep.wz in *.
        apply implA_from_evt.
        step.
        step. if_cases KW; rewrite ?unsigned_lit in KW by (first [exact WR| clear; lia]); zify_cond KW.
        -
          assert (W1 : w <> 1) by (clear - KW WR; lia).
          destruct one; cbn [Z.b2z].
          + step. if_false. step.
            apply evt_done.
            eapply (L_fin_oneA used ΣK lsK mK OWK r t ar at_ ri ti w b (Z_to_bv 64 at_)); [exact EVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WR| exact W1| clear - KCOST MCP; lia].
          + step. if_true.
            apply evt_done.
            eapply (L_fin_mulA used ΣK lsK mK OWK r t ar at_ ri ti w b); [exact EVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WR| exact W1| clear - KCOST MCP; lia].
        -
          assert (W1 : w = 1) by (clear - KW WR; lia). subst w.
          unfold mw_fin. cbv zeta. change (1 =? 1) with true. cbv iota.
          destruct one; cbn [Z.b2z].
          + step. if_false.
            apply evt_done.
            eapply (mw_oneA (Z_to_bv 64 at_) b used ΣK lsK mK OWK); [exact EVK| exact LSK| clear - KCOST MCP FLP CFM0; lia].
          + step. if_true.
            apply evt_done.
            eapply (mw_fromA (Z_to_bv 64 at_) b used ΣK lsK mK OWK r ar ri); [exact EVK| exact LSK| clear - KCOST MCP FLP CFM0; lia| exact HArK| exact Er].
      Qed.

      Variable a : Z.
      Hypothesis AR : 0 < a < 2^64.

      Definition MWQA (U : Z) (rv : (bnref * bnref * Z * bool) * bstate bptr) (Σ' : rts RT) (ms' : machine_state) : Prop :=
        exists mK' OWK' used' (ar at_ : Z) (ri ti : nat) (b : word) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
          ms' = MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 a) (Z_to_bv 64 arm) (Z_to_bv 64 (snd (fst (fst rv)))) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 (Z_to_bv 64 (Z.b2z (snd (fst rv)))) t3 t4 t5 t6)
                   F (Z_to_bv 64 2856172) fc None mK' (seg_rom bgbsegs)
          /\ CENV (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) b) used' Σ' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA
          /\ ref_at (snd rv) OWK' PL (fst (fst (fst (fst rv)))) ar /\ fst (fst (fst (fst rv))) = RPool ri
          /\ ref_at (snd rv) OWK' PL (snd (fst (fst (fst rv)))) at_ /\ snd (fst (fst (fst rv))) = RPool ti
          /\ 0 <= snd (fst (fst rv)) < 2^64 /\ used' <= U.

      Definition MWHEAD (c : nat) : Prop := forall U used ΣK lsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (one : bool)
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) (Z_to_bv 64 (Z.of_nat (S c)))) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL r ar -> r = RPool ri -> ref_at lsK OWK PL t at_ -> t = RPool ti -> 0 < w < 2^64 ->
        Z.of_nat (S c) < 2^31 -> used + Z.of_nat (S c) * MW_ROUNDC <= U -> U <= TOTAL ->
        implA (mw_loop ops (S c) a rp rm (r, t, w, one) lsK) ΣK (MWQA U)
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 a) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 (Z_to_bv 64 (Z.b2z one)) t3 t4 t5 t6)
              F (Z_to_bv 64 2855584) fc None mK (seg_rom bgbsegs)).

      Lemma L_testA : forall c, (forall c', c = S c' -> MWHEAD c') -> forall U used ΣK lsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (one : bool)
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) (Z_to_bv 64 (Z.of_nat c))) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL r ar -> r = RPool ri -> ref_at lsK OWK PL t at_ -> t = RPool ti -> 0 < w < 2^64 ->
        Z.of_nat c < 2^31 -> used + Z.of_nat c * MW_ROUNDC <= U -> U <= TOTAL ->
        implA (mw_loop ops c a rp rm (r, t, w, one) lsK) ΣK (MWQA U)
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 a) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) x26 (Z_to_bv 64 (Z.b2z one)) t3 t4 t5 t6)
              F (Z_to_bv 64 2855888) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros c NEXT. intros until fc; intros EVK LSK HArK Er HAtK Et WRP C31 KCOST UT.
        assert (WR : 0 <= w < 2^64) by (clear - WRP; lia).
        kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        apply implA_from_evt.
        step.
        step.

        rewrite lts_signed by (clear - C31; lia).
        destruct c as [|c'].
        -
          replace (0 <? Z.of_nat 0) with false by reflexivity.
          step.
          apply evt_done. rewrite mw_loop_O. unfold bret. cbn [ret tree_ops]. apply implA_ret.
          unfold MWQA. cbn [fst snd]. exists mK, OWK, used, ar, at_, ri, ti. do 21 eexists. split; [reflexivity|].
          split; [exact EVK|]. split; [exact LSK|]. split; [exact HArK|]. split; [exact Er|]. split; [exact HAtK|]. split; [exact Et|]. split; [exact WR|].
          clear - KCOST. lia.
        -
          replace (0 <? Z.of_nat (S c')) with true by (symmetry; apply Z.ltb_lt; clear; lia).
          apply evt_done.
          eapply (NEXT c' eq_refl U used ΣK lsK mK OWK r t ar at_ ri ti w one); [exact EVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WRP| exact C31| exact KCOST| exact UT].
      Qed.

      Lemma L_k3A : forall c, (forall c', c = S c' -> MWHEAD c') -> forall U used ΣK lsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (one : bool)
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) (Z_to_bv 64 at_) (Z_to_bv 64 (Z.of_nat (S c)))) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL r ar -> r = RPool ri -> ref_at lsK OWK PL t at_ -> t = RPool ti -> 0 < w < 2^64 ->
        Z.of_nat (S c) < 2^31 -> used + MW_FLC + Z.of_nat c * MW_ROUNDC <= U -> U <= TOTAL ->
        implA (mw_k3 c a rp rm r t w one lsK) ΣK (MWQA U)
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 a) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) x24 (Z_to_bv 64 ar) (Z_to_bv 64 (Z.b2z (negb one))) (Z_to_bv 64 (Z.b2z one)) t3 t4 t5 t6)
              F (Z_to_bv 64 2855776) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros c NEXT. intros until fc; intros EVK LSK HArK Er HAtK Et WRP C31 KCOST UT.
        assert (WR : 0 <= w < 2^64) by (clear - WRP; lia).
        kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAmS) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HApS) as HApK.
        assert (NROq : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; clear; lia).
        assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; clear; lia).
        assert (WRq : wref PL r) by (rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri))).
        assert (NBq : nbuf PL r) by (rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri))).
        assert (HPt : hpl PL t) by (rewrite Et; exact (hpl_pool PL ti)).
        assert (CRP : 0 <= Z.of_nat c * MW_ROUNDC) by (apply Z.mul_nonneg_nonneg; [clear; lia | exact RCP]).
        set (POT := Z.of_nat c * MW_ROUNDC) in *.
        unfold MW_FLC in KCOST, FLP.
        pose proof (L_testA c NEXT U) as TEST.
        assert (C31' : Z.of_nat c < 2^31) by (clear - C31; lia).
        unfold mw_k3, bbind, bget. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
        pose proof (munch_refl [(FB, FB + 24)]%Z mK) as MU. pose proof (wmono_refl bgbsegs mK) as WM.
        apply implA_from_evt.
        step. step.
        step. rewrite (swrap32_wrap64 (Z.of_nat (S c)) (-1)) by (clear - C31; lia). replace (Z.of_nat (S c) + -1) with (Z.of_nat c) by (clear; lia).
        step.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
        relocal EVK LSK MU WM STK MIK FRK FSZK EVS LSS. clear MU WM STK MIK FRK FSZK.
        step.

        eapply (is_bit_set_callA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m LOFB16); [exact EVS | exact LSS | exact HApK | exact NROp | clear - C31; lia |].
        intros m2 y0T y1T y2T y4T y5T y6T y7T y8T y9T y10T y11T y12T y13T y14T EV2 LS2.
        rewrite (ret_pc_even 2855800) by (clear; lia).
        pose proof EV2 as (_ & _ & ST2 & MI2 & _ & _ & _ & _ & FR2 & FSZ2 & _). unfold efrW in FR2. cbn [app] in FR2.
        destruct (is_bit_set_pure (getbn rp lsK) (Z.of_nat c)) eqn:EB; cbn [Z.b2z].
        2: {
             step. if_true. step.
             apply evt_done.
             eapply (TEST used ΣK lsK m2 OWK r t ar at_ ri ti w one); [exact EV2| exact LS2| exact HArK| exact Er| exact HAtK| exact Et| exact WRP| exact C31'| clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT]. }
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
          apply evt_done.
          eapply (TEST used ΣK lsK m2 OWK r t ar at_ ri ti (mulw w a) one); [exact EV2| exact LS2| exact HArK| exact Er| exact HAtK| exact Et| unfold mulw, BW; pose proof (Z.div_mod (w * a) 18446744073709551616 ltac:(clear; lia)) as DM; rewrite KO in DM; pose proof (Z.mod_pos_bound (w * a) 18446744073709551616 ltac:(clear; lia)) as MB; assert (P : 0 < w * a) by (clear - WRP AR; nia); clear - DM MB P; lia| exact C31'| clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT]. }
        replace (w * a / 18446744073709551616 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KO). cbn [negb].
        unfold mw_flush, mw_to_mont_word, mw_mod_mul_word, BN_mod, bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
        destruct one; cbn [Z.b2z negb].
        -
          step. step. step. if_true. step.
          apply evt_done.
          apply implA_tbind_assoc. apply implA_tbind_assoc. eapply implA_bind.
          { eapply (BN_set_word_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rx := r) (ax := ar) (w := w);
              [| | | reflexivity | exact HArK | exact WRq | reflexivity | reflexivity | exact WR].
            - eapply cenv_preA; [exact EV2 | exact LS2 | clear - LOK CSsetw; lia | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b91f8 CTX).
          }
          cbv beta. intros [u5 ls5] Σ5 ms5 PO.
          apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV2))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & -> & _)).
          subst PL5. specialize (CP5 eq_refl).
          destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EV2 CP5) as (EV5 & LS5).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5. clear CP5.
          rewrite (ret_pc_even 2855904) by (clear; lia).
          pose proof EV5 as (_ & _ & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold efrW in FR5. cbn [app] in FR5.
          unfold MallocRep.wz. apply implA_from_evt.
          step. step. if_false. step. step. step. step.
          apply evt_done.
          eapply implA_bind.
          { eapply (BN_to_montgomery_walkA) with (lo := lo) (OW := OW5) (LB := LB) (PL := PL) (EA := EA) (rr := r) (ra_ := r);
              [| | | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact WRq | exact NBq | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EV5 | exact LS5 | exact LOK | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
            - eapply cenv_roomA; [exact EV5 | exact ROOMS | clear; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV5).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9210 CTX).
          }
          cbv beta. intros [u6 ls6] Σ6 ms6 PO.
          apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV5))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & PL6 & -> & CP6 & (EPL6 & ->)).
          subst PL6. specialize (CP6 eq_refl).
          destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EV5 CP6) as (EV6 & LS6).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP6) as RS6. clear CP6.
          rewrite (ret_pc_even 2855928) by (clear; lia).
          pose proof EV6 as (_ & _ & ST6 & MI6 & _ & _ & _ & _ & FR6 & FSZ6 & _). unfold efrW in FR6. cbn [app] in FR6.
          unfold MallocRep.wz. apply implA_from_evt.
          step. step. step. step. if_false. step.
          cbn [tbind fst snd]. cbv beta iota.
          apply evt_done.
          eapply (TEST _ _ ls6 m6 OW6 r t ar at_ ri ti a false); [exact EV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et| clear - AR; lia| exact C31'| clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT].
        -
          step. step. step. if_false. step.
          apply evt_done.
          apply implA_tbind_assoc. eapply implA_bind.
          { eapply (BN_mul_word_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rx := r) (ax := ar) (w := w);
              [| | | reflexivity | exact HArK | exact WRq | reflexivity | reflexivity | exact WR].
            - eapply cenv_preA; [exact EV2 | exact LS2 | clear - LOK CSmulw; lia | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b91ac CTX).
          }
          cbv beta. intros [u5 ls5] Σ5 ms5 PO.
          apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV2))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & -> & _)).
          subst PL5. specialize (CP5 eq_refl).
          destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EV2 CP5) as (EV5 & LS5).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5. clear CP5.
          rewrite (ret_pc_even 2855828) by (clear; lia).
          pose proof EV5 as (_ & _ & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold efrW in FR5. cbn [app] in FR5.
          unfold MallocRep.wz. apply implA_from_evt.
          step. step. if_false. step. step. step. step. step. step.
          apply evt_done.
          apply implA_tbind_assoc. eapply implA_bind.
          { eapply (BN_div_walkA) with (lo := lo) (OW := OW5) (LB := LB) (PL := PL) (EA := EA) (dv := None) (rm := Some t) (adv := 0) (arm := at_) (num := r) (dvs := rm);
              [| | | reflexivity | exact HPCS | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAmK) | intros d0 Ed0; discriminate Ed0 | intros r0 Er0; injection Er0 as <-; exact HPt | exact NROq | exact NROm | exact NBq | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EV5 | exact LS5 | clear - LOK CSdiv; lia | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV5).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b91cc CTX).
          }
          cbv beta. intros [u6 ls6] Σ6 ms6 PO.
          apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV5))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & PL6 & -> & CP6 & (EPL6 & ->)).
          subst PL6. specialize (CP6 eq_refl).
          destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EV5 CP6) as (EV6 & LS6).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP6) as RS6. clear CP6.
          rewrite (ret_pc_even 2855860) by (clear; lia).
          pose proof EV6 as (_ & _ & ST6 & MI6 & _ & _ & _ & _ & FR6 & FSZ6 & _). unfold efrW in FR6. cbn [app] in FR6.
          unfold MallocRep.wz. apply implA_from_evt.
          pose proof (munch_refl [(FB, FB + 24)]%Z m6) as MU. pose proof (wmono_refl bgbsegs m6) as WM.
          step. step.
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
          relocal EV6 LS6 MU WM ST6 MI6 FR6 FSZ6 EV7 LS7. clear MU WM ST6 MI6 FR6 FSZ6.
          step. if_false. step.
          cbn [tbind fst snd]. cbv beta iota.
          apply evt_done.
          eapply (TEST _ _ ls6 m7 OW6 t r at_ ar ti ri a false); [exact EV7| exact LS7| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er| clear - AR; lia| exact C31'| clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT].
      Qed.

      Lemma L_k2A : forall c, (forall c', c = S c' -> MWHEAD c') -> forall U used ΣK lsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (w : Z) (ts : word)
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW (Z_to_bv 64 am) ts (Z_to_bv 64 (Z.of_nat (S c)))) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL r ar -> r = RPool ri -> ref_at lsK OWK PL t at_ -> t = RPool ti -> 0 < w < 2^64 ->
        Z.of_nat (S c) < 2^31 -> used + CMM + MW_FLC + Z.of_nat c * MW_ROUNDC <= U -> U <= TOTAL ->
        implA (tbind (BN_mod_mul_montgomery ops r r r lsK) (fun p => mw_k3 c a rp rm r t w false (snd p))) ΣK (MWQA U)
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 a) (Z_to_bv 64 arm) (Z_to_bv 64 w) (Z_to_bv 64 arp) (Z_to_bv 64 at_) (Z_to_bv 64 ar) (Z_to_bv 64 am) x27 t3 t4 t5 t6)
              F (Z_to_bv 64 2855736) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros c NEXT. intros until fc; intros EVK LSK HArK Er HAtK Et WRP C31 KCOST UT.
        assert (WR : 0 <= w < 2^64) by (clear - WRP; lia).
        kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAmS) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HApS) as HApK.
        assert (NROq : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; clear; lia).
        assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; clear; lia).
        assert (WRq : wref PL r) by (rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri))).
        assert (NBq : nbuf PL r) by (rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri))).
        assert (HPt : hpl PL t) by (rewrite Et; exact (hpl_pool PL ti)).
        assert (CRP : 0 <= Z.of_nat c * MW_ROUNDC) by (apply Z.mul_nonneg_nonneg; [clear; lia | exact RCP]).
        set (POT := Z.of_nat c * MW_ROUNDC) in *.
        unfold MW_FLC in KCOST, FLP.
        pose proof (L_k3A c NEXT U) as K3.
        apply implA_from_evt.
        do 6 step.
        apply evt_done.
        eapply implA_bind.
        { eapply (BN_mod_mul_montgomery_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rr := r) (ra_ := r) (rb := r);
            [| | | | reflexivity | exact HArK | exact HArK | exact HArK | exact WRq | exact NROq | exact NBq | exact NBq | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
          - eapply cenv_preA; [exact EVK | exact LSK | exact LOK | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
          - eapply cenv_roomA; [exact EVK | exact ROOMS | clear; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9168 CTX).
        }
        cbv beta. intros [u5 ls5] Σ5 ms5 PO.
        apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & ->)).
        subst PL5. specialize (CP5 eq_refl).
        destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EVK CP5) as (EV5 & LS5).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5. clear CP5.
        rewrite (ret_pc_even 2855760) by (clear; lia).
        pose proof EV5 as (_ & _ & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold efrW in FR5. cbn [app] in FR5.
        unfold MallocRep.wz. apply implA_from_evt.
        pose proof (munch_refl [(FB, FB + 24)]%Z m5) as MU. pose proof (wmono_refl bgbsegs m5) as WM.
        step. step. if_false. step.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
        relocal EV5 LS5 MU WM ST5 MI5 FR5 FSZ5 EV7 LS7. clear MU WM ST5 MI5 FR5 FSZ5.
        apply evt_done.
        eapply (K3 _ _ ls5 m7 OW5 r t ar at_ ri ti w false); [exact EV7| exact LS7| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK)| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK)| exact Et| exact WRP| exact C31| fold POT; unfold MW_FLC; clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT].
      Qed.

      Lemma mw_roundA : forall c, (forall c', c = S c' -> MWHEAD c') -> MWHEAD c.
      Proof.
        intros c NEXT. unfold MWHEAD. intros until fc; intros EVK LSK HArK Er HAtK Et WRP C31 KCOST UT.
        assert (WR : 0 <= w < 2^64) by (clear - WRP; lia).
        rewrite Nat2Z.inj_succ in KCOST. unfold Z.succ in KCOST. rewrite Z.mul_add_distr_r, Z.mul_1_l in KCOST.
        kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAmS) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HApS) as HApK.
        assert (NROq : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; clear; lia).
        assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; clear; lia).
        assert (WRq : wref PL r) by (rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri))).
        assert (NBq : nbuf PL r) by (rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri))).
        assert (HPt : hpl PL t) by (rewrite Et; exact (hpl_pool PL ti)).
        assert (CRP : 0 <= Z.of_nat c * MW_ROUNDC) by (apply Z.mul_nonneg_nonneg; [clear; lia | exact RCP]).
        set (POT := Z.of_nat c * MW_ROUNDC) in *.
        unfold MW_FLC in KCOST, FLP.
        unfold MW_ROUNDC at 1 in KCOST. unfold MW_FLC in KCOST.
        pose proof (L_k3A c NEXT U) as K3. pose proof (L_k2A c NEXT U) as K2.
        rewrite mw_loop_S'. cbv zeta. rewrite (ovf_mulhu_sq w WR).
        unfold bbind at 1. cbn [bind tree_ops].
        assert (HI : 0 <= w * w / 18446744073709551616 < 2^64).
        { split; [apply Z.div_pos; [clear - WR; nia| clear; lia]|]. apply Z.div_lt_upper_bound; [clear; lia|]. clear - WR. nia. }
        assert (WW : 0 <= mulw w w < 2^64) by (unfold mulw, BW; apply Z.mod_pos_bound; clear; lia).
        apply implA_from_evt.
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
            apply evt_done.
            eapply (K3 used ΣK lsK mK OWK r t ar at_ ri ti (mulw w w) true); [exact EVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WWP| exact C31| fold POT; unfold MW_FLC; clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT].
          - step. if_true.
            step. step.
            apply evt_done.
            eapply (K2 used ΣK lsK mK OWK r t ar at_ ri ti (mulw w w) (Z_to_bv 64 at_)); [exact EVK| exact LSK| exact HArK| exact Er| exact HAtK| exact Et| exact WWP| exact C31| fold POT; unfold MW_FLC; clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT]. }
        replace (w * w / 18446744073709551616 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KO). cbn [negb].
        unfold mw_flush, mw_to_mont_word, mw_mod_mul_word, BN_mod, bbind, bret. cbn [bind ret tree_ops tbind fst snd]. cbv beta.
        destruct one; cbn [Z.b2z].
        -
          step. step. step. if_false. step.
          apply evt_done.
          apply implA_tbind_assoc. apply implA_tbind_assoc. eapply implA_bind.
          { eapply (BN_set_word_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rx := r) (ax := ar) (w := w);
              [| | | reflexivity | exact HArK | exact WRq | reflexivity | reflexivity | exact WR].
            - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSsetw; lia | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b90d4 CTX).
          }
          cbv beta. intros [u5 ls5] Σ5 ms5 PO.
          apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & -> & _)).
          subst PL5. specialize (CP5 eq_refl).
          destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EVK CP5) as (EV5 & LS5).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5. clear CP5.
          rewrite (ret_pc_even 2855612) by (clear; lia).
          pose proof EV5 as (_ & _ & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold efrW in FR5. cbn [app] in FR5.
          unfold MallocRep.wz. apply implA_from_evt.
          step. if_false. step. step. step. step. step. step.
          apply evt_done.
          eapply implA_bind.
          { eapply (BN_to_montgomery_walkA) with (lo := lo) (OW := OW5) (LB := LB) (PL := PL) (EA := EA) (rr := r) (ra_ := r);
              [| | | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact WRq | exact NBq | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EV5 | exact LS5 | exact LOK | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
            - eapply cenv_roomA; [exact EV5 | exact ROOMS | clear; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV5).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b90f0 CTX).
          }
          cbv beta. intros [u6 ls6] Σ6 ms6 PO.
          apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV5))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & PL6 & -> & CP6 & (EPL6 & ->)).
          subst PL6. specialize (CP6 eq_refl).
          destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EV5 CP6) as (EV6 & LS6).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP6) as RS6. clear CP6.
          rewrite (ret_pc_even 2855640) by (clear; lia).
          pose proof EV6 as (_ & _ & ST6 & MI6 & _ & _ & _ & _ & FR6 & FSZ6 & _). unfold efrW in FR6. cbn [app] in FR6.
          unfold MallocRep.wz. apply implA_from_evt.
          step. if_false. step. step. step.
          cbn [tbind fst snd]. cbv beta iota. unfold mw_k2, bbind. cbn [bind tree_ops]. cbv beta iota.
          apply evt_done.
          eapply (K2 _ _ ls6 m6 OW6 r t ar at_ ri ti 1 (Z_to_bv 64 at_)); [exact EV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et| clear; lia| exact C31| fold POT; unfold MW_FLC; clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT].
        -
          step. step. step. if_true. step.
          apply evt_done.
          apply implA_tbind_assoc. eapply implA_bind.
          { eapply (BN_mul_word_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rx := r) (ax := ar) (w := w);
              [| | | reflexivity | exact HArK | exact WRq | reflexivity | reflexivity | exact WR].
            - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSmulw; lia | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9114 CTX).
          }
          cbv beta. intros [u5 ls5] Σ5 ms5 PO.
          apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & -> & _)).
          subst PL5. specialize (CP5 eq_refl).
          destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EVK CP5) as (EV5 & LS5).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5. clear CP5.
          rewrite (ret_pc_even 2855676) by (clear; lia).
          pose proof EV5 as (_ & _ & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold efrW in FR5. cbn [app] in FR5.
          unfold MallocRep.wz. apply implA_from_evt.
          step. if_false. step. step. step. step. step. step. step.
          apply evt_done.
          apply implA_tbind_assoc. eapply implA_bind.
          { eapply (BN_div_walkA) with (lo := lo) (OW := OW5) (LB := LB) (PL := PL) (EA := EA) (dv := None) (rm := Some t) (adv := 0) (arm := at_) (num := r) (dvs := rm);
              [| | | reflexivity | exact HPCS | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) | exact (ref_at_stable _ _ _ _ PL _ _ RS5 HAmK) | intros d0 Ed0; discriminate Ed0 | intros r0 Er0; injection Er0 as <-; exact HPt | exact NROq | exact NROm | exact NBq | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EV5 | exact LS5 | clear - LOK CSdiv; lia | clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV5).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9134 CTX).
          }
          cbv beta. intros [u6 ls6] Σ6 ms6 PO.
          apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV5))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & PL6 & -> & CP6 & (EPL6 & ->)).
          subst PL6. specialize (CP6 eq_refl).
          destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EV5 CP6) as (EV6 & LS6).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP6) as RS6. clear CP6.
          rewrite (ret_pc_even 2855708) by (clear; lia).
          pose proof EV6 as (_ & _ & ST6 & MI6 & _ & _ & _ & _ & FR6 & FSZ6 & _). unfold efrW in FR6. cbn [app] in FR6.
          unfold MallocRep.wz. apply implA_from_evt.
          step. if_false. step. step. step. step. step.
          cbn [tbind fst snd]. cbv beta iota. unfold mw_k2, bbind. cbn [bind tree_ops]. cbv beta iota.
          apply evt_done.
          eapply (K2 _ _ ls6 m6 OW6 t r at_ ar ti ri 1 (Z_to_bv 64 at_)); [exact EV6| exact LS6| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK))| exact Et| exact (ref_at_stable _ _ _ _ PL _ _ RS6 (ref_at_stable _ _ _ _ PL _ _ RS5 HArK))| exact Er| clear; lia| exact C31| fold POT; unfold MW_FLC; clear - KCOST UT MCP DCP FLP RCP CRP CMM0 CFM0; lia| exact UT].
      Qed.

      Lemma mw_headA : forall c, MWHEAD c.
      Proof. induction c as [|c IH]; apply mw_roundA; intros c' E; [discriminate E| injection E as <-; exact IH]. Qed.

      Lemma L_setA : forall used ΣK lsK mK OWK (r t : bnref) (ar at_ : Z) (ri ti : nat) (bits : Z) (mo ts b : word)
          (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV (efrW mo ts b) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL r ar -> r = RPool ri -> ref_at lsK OWK PL t at_ -> t = RPool ti -> 0 < bits <= 32768 ->
        used + CMS + 32768 * MW_ROUNDC + MW_FLC + CFM + MC <= TOTAL ->
        implA (tbind (BN_MONT_CTX_set ops rm lsK)
                 (fun p => tbind (mw_loop ops (Z.to_nat (bits - 1)) a rp rm (r, t, a, true) (snd p))
                             (fun q => mw_fin rr rm qm (fst q) (snd q)))) ΣK Q
          (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) (Z_to_bv 64 am) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 a) (Z_to_bv 64 arm) x19 (Z_to_bv 64 arp) (Z_to_bv 64 at_) (Z_to_bv 64 ar) (Z_to_bv 64 bits) x27 t3 t4 t5 t6)
              F (Z_to_bv 64 2856124) fc None mK (seg_rom bgbsegs)).
      Proof.
        intros until fc; intros EVK LSK HArK Er HAtK Et BITS KCOST.
        kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). unfold efrW in FRK. cbn [app] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAmS) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HApS) as HApK.
        assert (NROq : r <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; clear; lia).
        assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; clear; lia).
        assert (WRq : wref PL r) by (rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri))).
        assert (NBq : nbuf PL r) by (rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri))).
        assert (HPt : hpl PL t) by (rewrite Et; exact (hpl_pool PL ti)).
        assert (AW : 0 <= a < 2^64) by (clear - AR; lia).
        apply implA_from_evt.
        step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by (clear - AMR; lia); [exfalso; clear - KZ AMR; lia| clear KZ].
        step. step. step. step.
        apply evt_done.
        eapply implA_bind.
        { eapply (BN_MONT_CTX_set_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (rd := rm) (ad := arm);
            [| | | | reflexivity | exact HAmK | exact NROm | exact HPM | exact HPCS | exact HFT | reflexivity | reflexivity | reflexivity].
          - eapply cenv_preA; [exact EVK | exact LSK | exact LOK | clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia].
          - eapply cenv_roomA; [exact EVK | exact ROOMS | clear; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b92e8 CTX).
        }
        cbv beta. intros [u5 ls5] Σ5 ms5 PO.
        apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & ->)).
        subst PL5. specialize (CP5 eq_refl).
        destruct (cenv_postA LB PL EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls ((qm, am, 96) :: OW) m _ _ _ _ _ _ _ _ _ _ _ EVK CP5) as (EV5 & LS5).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5. clear CP5.
        rewrite (ret_pc_even 2856144) by (clear; lia).
        pose proof EV5 as (_ & _ & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold efrW in FR5. cbn [app] in FR5.
        unfold MallocRep.wz. apply implA_from_evt.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HArK) as HAr5. pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HAtK) as HAt5.
        pose proof (munch_refl [(FB, FB + 24)]%Z m5) as MU. pose proof (wmono_refl bgbsegs m5) as WM.
        step. if_true.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        relocal EV5 LS5 MU WM ST5 MI5 FR5 FSZ5 EV6 LS6.
        step. rewrite (swrap32_wrap64 bits (-2)) by (clear - BITS; lia).

        hide_ors. ub. unhide.
        step. rewrite lts_signed by (clear - BITS; lia).
        destruct (Z.ltb_spec (bits + -2) 0) as [B1|B2'].
        2: assert (B2 : 2 <= bits) by (clear - B2'; lia).
        -
          assert (E1 : bits = 1) by (clear - B1 BITS; lia). subst bits.
          change (Z.to_nat (1 - 1)) with 0%nat. rewrite mw_loop_O. unfold bret. cbn [ret tree_ops tbind fst snd]. cbv beta.
          step.
          step. if_cases KA; rewrite ?unsigned_lit in KA by (first [exact AW| clear; lia]); zify_cond KA.
          2: { step. apply evt_done.
               eapply (L_fin_oneA _ _ ls5 m6 OW5 r t ar at_ ri ti a b ts); [exact EV6| exact LS6| exact HAr5| exact Er| exact HAt5| exact Et| exact AW| clear - KA AW; lia| clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia]. }
          + assert (A1 : a = 1) by (clear - KA AW; lia).
            unfold mw_fin. cbv zeta. replace (a =? 1) with true by (symmetry; apply Z.eqb_eq; exact A1). cbv iota.
            apply evt_done.
            eapply (mw_oneA ts b _ _ ls5 m6 OW5); [exact EV6| exact LS6| clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia].
        -
          step.
          step. replace (bits + -1) with (Z.of_nat (S (Z.to_nat (bits - 2)))) by (clear - B2; lia).
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
          relocal EV5 LS5 MU WM ST5 MI5 FR5 FSZ5 EV7 LS7. clear EV5 LS5 EV6 LS6 MU WM ST5 MI5 FR5 FSZ5.
          step. step.
          replace (Z.to_nat (bits - 1)) with (S (Z.to_nat (bits - 2))) by (clear - B2; lia).
          assert (POTB : Z.of_nat (S (Z.to_nat (bits - 2))) * MW_ROUNDC <= 32768 * MW_ROUNDC) by (apply Z.mul_le_mono_nonneg_r; [exact RCP | clear - B2 BITS; lia]).
          apply evt_done.
          eapply implA_bind with (Q1 := MWQA (used + CMS + 32768 * MW_ROUNDC)).
          { eapply (mw_headA (Z.to_nat (bits - 2)) (used + CMS + 32768 * MW_ROUNDC) _ _ ls5 m7 OW5 r t ar at_ ri ti a true);
              [exact EV7| exact LS7| exact HAr5| exact Er| exact HAt5| exact Et| exact AR| clear - B2 BITS; lia
              | clear - POTB; lia | clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia]. }
          cbv beta. intros [[[[rN tN] wN] oneN] lsQ] ΣQ msQ (mQ & OWQ & usedQ & ar2 & at2 & ri2 & ti2 & bQ & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & EVQ & LSQ & HAr2 & Er2 & HAt2 & Et2 & WR2 & UQ). cbn [fst snd] in *.
          eapply (L_finalA usedQ ΣQ lsQ mQ OWQ rN tN ar2 at2 ri2 ti2 wN oneN bQ); [exact EVQ| exact LSQ| exact HAr2| exact Er2| exact HAt2| exact Et2| exact WR2| clear - UQ KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia].
      Qed.

    End Scope.

    Lemma L_restA : forall (a : Z) used ΣK lsK mK OWK (bits : Z) (w0 w1 w2 : word)
        (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      0 < a < 2^64 ->
      cenvA LB PL0 lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m (efrW w0 w1 w2) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL0 EA ->
      0 < bits <= 32768 -> used + 4 * MC + CMS + 32768 * MW_ROUNDC + MW_FLC + CFM + MC <= TOTAL ->
      implA (mw_rest bits rr a rp rm lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) (Z_to_bv 64 bits) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 arr) (Z_to_bv 64 a) (Z_to_bv 64 arm) x19 (Z_to_bv 64 arp) x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 2855500) fc None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc; intros AR EVK LSK BITS KCOST. kit EVK. unfold MallocRep.wz in *.
      unfold mw_rest. unfold bbind at 1. cbn [bind tree_ops].
      apply implA_from_evt. do 3 step.
        apply evt_done.
        eapply implA_bind.
        { eapply (BN_CTX_start_walkA) with (lo := lo) (OW := OWK) (LB := LB) (PL := PL0) (EA := EA);
            [| | | reflexivity | exact HPC | reflexivity].
          - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSstart; lia | clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9070 CTX).
        }
        cbv beta. intros [us lss] Σs mss PO.
        apply (bn_postA_cpost LB PL0 EA lo SPv FB TOTAL Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fs & fcs & ms & OWs & PLs & -> & CPs & (EPLs & INCLs)).
        subst PLs. specialize (CPs eq_refl).
        destruct (cenv_postA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EVK CPs) as (EVs & LSs).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPs) as RSs. clear CPs.
        rewrite (ret_pc_even 2855512) by (clear; lia).
        pose proof EVs as (_ & _ & STs & MIs & _ & _ & _ & _ & FRs & FSZs & _). unfold efrW in FRs. cbn [app] in FRs.
        unfold MallocRep.wz. apply implA_from_evt.
        cbv beta. unfold bbind at 1. cbn [bind tree_ops].
        do 2 step.
        apply evt_done.
        eapply implA_bind.
        { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWs) (LB := LB) (PL := PL0) (EA := EA);
            [| | | reflexivity | exact HPC | reflexivity].
          - eapply cenv_preA; [exact EVs | exact LSs | clear - LOK CSget; lia | clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVs).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9078 CTX).
        }
        cbv beta. intros [u1 ls1] Σ1 ms1 PO.
        apply (bn_postA_cpost LB PL0 EA lo SPv FB TOTAL Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVs))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & (ri & Er) & (ar & HAr1 & ->) & INCL1)).
        subst PL1. specialize (CP1 eq_refl).
        destruct (cenv_postA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EVs CP1) as (EV1 & LS1).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1. clear CP1.
        rewrite (ret_pc_even 2855520) by (clear; lia).
        pose proof EV1 as (_ & _ & ST1 & MI1 & _ & _ & _ & _ & FR1 & FSZ1 & _). unfold efrW in FR1. cbn [app] in FR1.
        unfold MallocRep.wz. apply implA_from_evt.
        cbv beta. unfold bbind at 1. cbn [bind tree_ops].
        do 3 step.
        apply evt_done.
        eapply implA_bind.
        { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OW1) (LB := LB) (PL := PL0) (EA := EA);
            [| | | reflexivity | exact HPC | reflexivity].
          - eapply cenv_preA; [exact EV1 | exact LS1 | clear - LOK CSget; lia | clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b9084 CTX).
        }
        cbv beta. intros [u2 ls2] Σ2 ms2 PO.
        apply (bn_postA_cpost LB PL0 EA lo SPv FB TOTAL Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & OW2 & PL2 & -> & CP2 & (EPL2 & (ti & Et) & (at_ & HAt2 & ->) & INCL2)).
        subst PL2. specialize (CP2 eq_refl).
        destruct (cenv_postA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV1 CP2) as (EV2 & LS2).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP2) as RS2. clear CP2.
        rewrite (ret_pc_even 2855532) by (clear; lia).
        pose proof EV2 as (_ & _ & ST2 & MI2 & _ & _ & _ & _ & FR2 & FSZ2 & _). unfold efrW in FR2. cbn [app] in FR2.
        unfold MallocRep.wz. apply implA_from_evt.
        cbv beta.
        pose proof (proj1 (proj2 EV2)) as HEAP2. pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
        assert (NROt : u2 <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; clear; lia).
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROKK HAt2 NROt) as (At0 & AtC & _).
        assert (AtR : 0 < at_ < 2^64) by (unfold BnHeapA.ACEIL, STACK_WIN in *; clear - At0 AtC CE1 CE2 CE3; lia). clear AtC.
        step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); [exfalso; clear - KZ AtR; lia| clear KZ].
        step. step.
        step. if_true.
        step.
        apply evt_done.
        eapply (mont_new_callA _ Q LB PL0 EA lo SPv FB s0 ra ras TOTAL Σ ls OW m _ _ (used + 4 * MC));
          [ exact EV2 | exact LS2 | exact HFM | reflexivity | clear - LOK CSnew; lia | clear - MCP; lia | clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia | reflexivity
          | clear - TIGHT; unfold block in *; lia
          | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_word_2b92d4 CTX) |].
        intros qm am Σn mn n0 n1 n2 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 Fn fcn AMR EVn LSn.
        rewrite (ret_pc_even 2856124) by (clear; lia). unfold MallocRep.wz.
        eapply (L_setA am qm AMR a AR _ _ _ mn _ u1 u2 ar at_ ri ti bits w0 w1 w2);
          [ exact EVn | exact LSn
          | exact (ref_at_mont_enter _ _ _ _ _ (qm, am, 96) (Some (am, qm)) HFM (ref_at_stable _ _ _ _ _ _ _ RS2 HAr1)) | exact Er
          | exact (ref_at_mont_enter _ _ _ _ _ (qm, am, 96) (Some (am, qm)) HFM HAt2) | exact Et | exact BITS | clear - KCOST MCP DCP FLP RCP CMM0 CFM0 CMS0; lia ].
    Qed.

    Lemma bn_postA_res_wk : forall {A : Type} (ra' sp' gp' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
        Σ' (st : bstate bptr) OW' LB' lo' m' PL' EA' C (RES RES' : A -> bstate bptr -> list block -> placement -> word -> Prop) r Σ2 ms2,
      bn_postA ra' sp' gp' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ' st OW' LB' lo' m' PL' EA' C RES r Σ2 ms2 ->
      (forall a ls2 OW2 PL2 a0', RES a ls2 OW2 PL2 a0' -> RES' a ls2 OW2 PL2 a0') ->
      bn_postA ra' sp' gp' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ' st OW' LB' lo' m' PL' EA' C RES' r Σ2 ms2.
    Proof.
      intros until ms2. intros PO HR. unfold bn_postA in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & E & HEAP2 & LS2 & ST2 & MI2 & AXP2 & CRED2 & CNT2 & RST2 & RES2).
      exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F2, fc2, m2, OW2, PL2.
      split; [exact E|]. split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact AXP2|].
      split; [exact CRED2|]. split; [exact CNT2|]. split; [exact RST2| apply HR; exact RES2].
    Qed.

    Lemma mw_mainA : forall (A : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      bn_preA Σ ls m OW LB PL0 EA sp lo BN_MOD_EXP_MONT_WORD_STACK TOTAL ->
      uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras ->
      0 <= A < BW ->
      implA (BN_mod_exp_mont_word ops rr A rp rm ls) Σ Q
        (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz arr) (wz A) (wz arp) (wz arm) (wz ac) (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz BN_MOD_EXP_MONT_WORD) fc None m (seg_rom bgbsegs)).
    Proof.
      intros until fc. intros PRE UW AB.
      pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
      pose proof MC0 as MCP. pose proof DC0 as DCP. pose proof FLC0 as FLP. pose proof ROUNDC0 as RCP.
      assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia).
      assert (T0 : 0 <= TOTAL) by (unfold EXP_MW_TOTAL; clear - MCP FLP RCP CFM0 CMS0; lia).
      unfold BN_MOD_EXP_MONT_WORD, MallocRep.wz. unfold BW in AB.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
      pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
      destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
      pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.

      set (bp := getbn rp ls). set (bm := getbn rm ls).
      assert (HVp : vref rp ls) by (eapply ref_at_valid; [exact LS | exact HAp]).
      assert (HVm : vref rm ls) by (eapply ref_at_valid; [exact LS | exact HAm]).
      pose proof (st_wf_ok _ _ (proj1 PARTS) HVp NROp) as (OKp1 & OKp2 & OKp3 & OKp4). fold bp in OKp1, OKp2, OKp3, OKp4.
      pose proof (st_wf_ok _ _ (proj1 PARTS) HVm NROm) as (OKm1 & OKm2 & OKm3 & OKm4). fold bm in OKm1, OKm2, OKm3, OKm4.
      unfold BG_DMAX in OKp3, OKm3.
      assert (CTp : Z.land (bn_flags bp) 4 = 0) by (destruct OKp4 as [E|E]; rewrite E; reflexivity).
      assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
      clear OKp4 OKm4.

      rewrite BN_mod_exp_mont_word_eq. unfold any_consttime, BN_num_bits, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd fold_right]. cbv beta.
      fold bp bm. unfold has_flag, BN_FLG_CONSTTIME. rewrite CTp, CTm. cbn [Z.eqb negb orb andb]. cbv beta.
      apply implA_from_evt.

      carve_frame 128%nat ST. do 13 step. do 6 step. do 3 step. do 3 step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.

      lazymatch type of FR with rw_cells _ _ _ (CB 24 ?jk :: ?post) =>
        pose proof (rw_cells_split_CB bgbsegs mP (bv_unsigned sp + -128) [] 24 jk post [8; 8; 8]%nat FR eq_refl) as FR'; clear FR; rename FR' into FR;
        cbn [mk_CB_cells app] in FR
      end.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
      assert (HWL : Forall (w_lib ls OW PL0 lo (bv_unsigned sp)) [(bv_unsigned sp + -128, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
      assert (WOK : Forall (w_ok OW LB ls PL0 EA (bv_unsigned sp) []) [(bv_unsigned sp + -128, bv_unsigned sp)]).
      { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
      pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL0 EA _ HEAP LS MU WM FROK WOK) as LS0.
      lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
        assert (EV0 : cenvA LB PL0 lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) TOTAL Σ ls OW m p 0 Σ ls mP OW) end.
      { unfold cenvA, cenv_ok.
        split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
                split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
        split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
        split; [exact ST|]. split; [exact MI|].
        split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
        split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
        split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
        eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }

      pose proof (cenv_pre_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EV0) as WF0. cbn [cells_wf cell_wf app] in WF0.
      destruct WF0 as (L0 & L1 & L2 & _).
      destruct (cb8_word _ L0) as (w0 & E0). destruct (cb8_word _ L1) as (w1 & E1). destruct (cb8_word _ L2) as (w2 & E2).
      assert (EVR : cenvA LB PL0 lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) TOTAL Σ ls OW m (efrW w0 w1 w2) 0 Σ ls mP OW).
      { eapply cenv_recastA; [exact EV0 | | |].
        - unfold efrW. cbn [cells_wf cell_wf app]. repeat split.
        - unfold efrW. cbn [cells_bytes cbytes app]. rewrite E0, E1, E2. reflexivity.
        - reflexivity. }
      clear EV0 HEAP ST MI MU WM HWL WOK FR PRE E0 E1 E2 L0 L1 L2 CEIL LO SPT SP16 CNT CRED FAL NOFR FROK MCP DCP FLP RCP CS16 ESP C1 C2 C3 SPR SHB1 SHB2.
      rename EVR into EV0.
      kit EV0.

      eapply (get_flags_callA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m LOFB16); [exact EV0 | exact LS0 | exact HAp | exact NROp |].
      intros mB y0B y1B y2B y4B y5B y6B y7B y8B y9B y10B y11B y12B y13B y14B EVB LSB.
      rewrite (ret_pc_even 2855232) by (clear; lia).
      fold bp. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTp.
      step. change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.

      step. step. step.
      eapply (get_flags_callA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m LOFB16); [exact EVB | exact LSB | exact HAm | exact NROm |].
      intros mC y0C y1C y2C y4C y5C y6C y7C y8C y9C y10C y11C y12C y13C y14C EVC LSC.
      rewrite (ret_pc_even 2855248) by (clear; lia).
      fold bm. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTm.
      step. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.

      step. step.
      eapply (is_odd_callA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m LOFB16); [exact EVC | exact LSC | exact HAm | exact NROm |].
      intros mA y0A y1A y2A y4A y5A y6A y7A y8A y9A y10A y11A y12A y13A y14A EVA LSA.
      rewrite (ret_pc_even 2855376) by (clear; lia). fold bm.
      destruct (is_odd_pure bm) eqn:ODD; cbn [Z.b2z negb]; [| apply evt_done; apply implA_unr].
      cbv beta zeta. fold bp bm. unfold has_flag, BN_FLG_CONSTTIME. rewrite ?CTp, ?CTm. cbn [Z.eqb negb orb andb]. cbv beta.
      step. if_false.

      destruct (open_for_read LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ _ _ 16 EVA LSA HAm NROm ltac:(clear; lia) LOFB16)
        as (Dm & BNm & _ & Um & _ & _ & _ & SEPm & _ & _ & ACCm & ALm & ACCDm & ALDm & BDm & _ & Am0 & UBPm).
      fold bm in BNm, Um, ACCDm, BDm, UBPm.
      pose proof (munch_refl (@nil (Z * Z)) mA) as MU0.
      assert (AmR : 0 < arm < 2^64) by (clear - Am0 SEPm FBSP SPT; unfold USTACK_TOP in *; lia).
      hide_ors. ub. unhide.
      eapply evt_cut.
      { eapply (mw_rem_walkA) with (mb := mA) (W := @nil (Z * Z)) (A := A) (AM := arm) (D := Dm) (b := bm);
          [ exact BNm | exact Um | exact OKm1 | exact OKm2 | clear - OKm3; lia | exact AB | exact ACCm | exact ALm | exact Am0
          | clear - SEPm FBSP SPT; unfold USTACK_TOP in *; lia | exact ACCDm | exact ALDm | exact BDm | exact MU0 | exact I | exact UBPm | exact ODD ]. }
      cbv beta. intros msR (x11R & ->).
      clear BNm Um ACCm ACCDm MU0.
      set (a := if (bn_top bm =? 1)%nat then A mod nth 0 (bn_buf bm) 0 else A) in *.
      assert (AW : 0 <= a < 2^64).
      { subst a. destruct (bn_top bm =? 1)%nat eqn:ET; [| exact AB].
        destruct (Z.eq_dec (nth 0 (bn_buf bm) 0) 0) as [E0|N0]; [rewrite E0, Z.mod_0_r; exact AB|].
        assert (Hl : limb (nth 0 (bn_buf bm) 0)) by (apply (proj1 (List.Forall_nth limb (bn_buf bm)) OKm1); apply Nat.eqb_eq in ET; unfold bn_dmax in OKm2; clear - OKm2 ET; lia).
        unfold limb, BW in Hl. pose proof (Z.mod_pos_bound A (nth 0 (bn_buf bm) 0) ltac:(clear - Hl N0; lia)) as MB. clear - MB Hl. lia. }

      step.
      eapply (num_bits_callA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m); [exact EVA | exact LSA | exact HAp | exact NROp | unfold BN_NUM_BITS_STACK in *; clear - LOK CSnb; lia |].
      intros mE y0E y1E y2E y4E y5E y6E y7E y8E y9E y10E y11E y12E y13E y14E EVE LSE.
      rewrite (ret_pc_even 2855492) by (clear; lia).
      pose proof (num_bits_pure_range bp OKp1) as BITS.
      fold bp. cbn [Z.eqb negb]. cbv beta. cbn [tbind fst snd]. cbv beta. set (bits := num_bits_pure bp) in *.
      assert (BITSR : bits <= 32768) by (clear - BITS OKp2 OKp3; lia).
      step. if_cases KB; rewrite ?unsigned_lit in KB by (clear - BITS BITSR; lia); zify_cond KB.
      2: {
           replace (bits =? 0) with false by (symmetry; apply Z.eqb_neq; exact KB).
           step. if_cases KA; rewrite ?unsigned_lit in KA by (clear - AW; lia); zify_cond KA.
           -
             replace (a =? 0) with true by (symmetry; apply Z.eqb_eq; exact KA).
             step. step.
             eapply (zero_callA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m LOFB16); [exact EVE | exact LSE | exact HAr | exact (hpl_wref _ _ WRr) |].
             intros mG z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 lsG EVG LSG.
             rewrite (ret_pc_even 2856028) by (clear; lia).
             unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
             step. step.
             apply evt_done. eapply mw_retA; [exact EVG | exact LSG | exact T0].
           -
             replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; exact KA).
             apply evt_done.
             eapply (L_restA a 0 Σ ls mE OW bits w0 w1 w2); [clear - AW KA; lia | exact EVE | exact LSE | clear - BITS KB BITSR; lia | unfold EXP_MW_TOTAL; clear - MCP; lia]. }

      replace (bits =? 0) with true by (symmetry; apply Z.eqb_eq; exact KB).
      unfold exp_bits0, bbind, bget. cbn [bind ret tree_ops tbind fst snd]. fold bm.
      step. step. step. step.
      eapply (abs_is_word_callA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m LOFB16); [exact EVE | exact LSE | exact HAm | exact NROm |].
      intros mF y0F y1F y2F y4F y5F y6F y7F y8F y9F y10F y11F y12F y13F y14F EVF LSF.
      rewrite (ret_pc_even 2856004) by (clear; lia).
      fold bm. rewrite (unsigned_lit 1) by (clear; lia).
      destruct (abs_is_word_pure bm 1); cbn [Z.b2z].
      -
        step. change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false. cbv iota. step. step.
        eapply (zero_callA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m LOFB16); [exact EVF | exact LSF | exact HAr | exact (hpl_wref _ _ WRr) |].
        intros mG z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 lsG EVG LSG.
        rewrite (ret_pc_even 2856016) by (clear; lia).
        unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
        step.
        apply evt_done. eapply mw_retA; [exact EVG | exact LSG | exact T0].
      -
        step. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota. step. step.
        pose proof EVF as (_ & _ & STT & _ & _ & _ & _ & _ & FRT & _ & _). unfold efrW in FRT. cbn [app] in FRT.
        do 13 step. release_frame FRT STT (bv_unsigned sp). step. step.
        apply evt_done.
        destruct (cenv_tailA LB PL0 EA lo SPv FB s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ BN_SET_WORD_STACK MC ras
                    ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    (fun (_ : unit) (_ : bstate bptr) (OW' : list block) (PL' : placement) (a0' : word) =>
                       PL' = PL0 /\ a0' = wz 1 /\ (forall q A0 n, In (q, A0, n) OW -> bn_d (getbn rr ls) <> Some q -> In (q, A0, n) OW'))
                    EVF LSF STT ltac:(clear - LOK CSsetw; lia) ltac:(unfold EXP_MW_TOTAL; clear - MCP FLP RCP CFM0 CMS0; lia) eq_refl) as (PREX & UWX & POSTX).
        rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
        unfold BN_one.
        eapply implA_mono.
        { eapply (BN_set_word_walkA ra sp) with (lo := lo) (ras := ras) (rx := rr) (ax := arr) (w := 1) (OW := OW) (LB := LB) (PL := PL0) (EA := EA);
            [exact PREX | exact UWX | exact (uk_ctx_tail _ _ _ E_BN_mod_exp_mont_word_2b92d0 CTX) | reflexivity | exact HAr | exact (hpl_wref _ _ WRr) | reflexivity | reflexivity | clear; lia]. }
        cbv beta. intros r Σ' ms' PO. unfold MWPOST. eapply bn_postA_res_wk; [apply POSTX; exact PO |].
        cbv beta. intros ? ? ? ? ? (H1 & H2 & _). split; [exact H1 | exact H2].
    Qed.

  End Fixed.

  Definition BN_MOD_EXP_MONT_WORD_COST : Z := EXP_MW_TOTAL.

  Lemma BN_mod_exp_mont_word_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rp rm : bnref) (A : Z) (arr arp arm ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo BN_MOD_EXP_MONT_WORD_STACK BN_MOD_EXP_MONT_WORD_COST ->
    fr_room 4 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MOD_EXP_MONT_WORD (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr arr -> ref_at ls OW PL rp arp -> ref_at ls OW PL rm arm ->
    hpl PL rr -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL -> 0 <= A < BW ->
    a0 = wz arr -> a1 = wz A -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> a5 = wz 0 ->
    implA (BN_mod_exp_mont_word (tree_ops bptr) rr A rp rm ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_MOD_EXP_MONT_WORD_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_EXP_MONT_WORD) fc None m (seg_rom bgbsegs)).
  Proof.
    intros until qc. intros PRE ROOM UW CTX -> HAr HAp HAm HPr NROp NROm HPC HFR AB -> -> -> -> -> ->.
    destruct HFR as (_ & _ & _ & HFM & HFT).
    pose proof PRE as (_ & _ & _ & _ & _ & LO & _).
    unfold BN_MOD_EXP_MONT_WORD_COST in *.
    eapply (mw_mainA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls m OW LB PL EA lo ras rr rp rm arr arp arm ac qc);
      [ unfold BN_MOD_EXP_MONT_WORD_STACK in LO; clear - LO; lia
      | exact (fr_room_le 4 3 ls OW LB ROOM ltac:(clear; lia))
      | destruct ROOM as [_ R]; clear - R; unfold block in *; lia
      | exact CTX | exact HPC | exact HFM | exact HFT | exact HAr | exact HAp | exact HAm | exact HPr | exact NROp | exact NROm
      | exact PRE | exact UW | exact AB ].
  Qed.
End Proofs.
End Body.
