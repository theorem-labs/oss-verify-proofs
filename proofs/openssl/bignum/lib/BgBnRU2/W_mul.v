(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnDivWords BnModel BnTree BnInv BnSpecs BnMInv BnBridge BgState BgInv BgLib BgWords BgArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import BnCalls.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_num_bits_word BnCallsU WU_mul_normal WU_mul_recursive WU_mul_part_recursive HxComba8U WU_kara_final WU_kara_closed.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves BnAssoc.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves BnRKit W_expand W_ctx W_ctx_get W_ctx_end W_mul_core.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnR Require Import BgLive DivModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnAU Require BnAKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Local Notation ops := (tree_ops bptr).

Definition disp_normal (rr : bnref) (la lb : list Z) (top : nat) : BM (M := btree bptr) unit :=
  bbind ops (bn_wexpand ops rr top) (fun _ =>
  bbind ops (bget ops rr) (fun r =>
  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 (mul_normal la lb)) top (bn_neg r) (bn_flags r)))).

Definition disp_comba8 (rr : bnref) (la lb : list Z) : BM (M := btree bptr) unit :=
  bbind ops (bn_wexpand ops rr 16) (fun _ =>
  bbind ops (bget ops rr) (fun r =>
  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 (mul_comba8 la lb)) 16 (bn_neg r) (bn_flags r)))).

Definition disp_part (rr t : bnref) (la lb : list Z) (al bl top kj : nat) : BM (M := btree bptr) unit :=
  bbind ops (bn_wexpand ops t (8 * Nat.pow 2 kj)) (fun _ =>
  bbind ops (bn_wexpand ops rr (8 * Nat.pow 2 kj)) (fun _ =>
  bbind ops (bget ops t) (fun tb =>
  bbind ops (bget ops rr) (fun r =>
  let '(ro, to) := mul_part_recursive kj kj la lb (al - Nat.pow 2 kj) (bl - Nat.pow 2 kj) (firstn (4 * Nat.pow 2 kj) (bn_buf r)) (bn_buf tb) in
  bbind ops (bset ops t (bn_with_buf tb to)) (fun _ =>
  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 ro) top (bn_neg r) (bn_flags r))))))).

Definition disp_rec (rr t : bnref) (la lb : list Z) (al bl top kj : nat) : BM (M := btree bptr) unit :=
  bbind ops (bn_wexpand ops t (4 * Nat.pow 2 kj)) (fun _ =>
  bbind ops (bn_wexpand ops rr (4 * Nat.pow 2 kj)) (fun _ =>
  bbind ops (bget ops t) (fun tb =>
  bbind ops (bget ops rr) (fun r =>
  let '(ro, to) := mul_recursive kj la lb (Nat.pow 2 kj - al) (Nat.pow 2 kj - bl) (firstn (2 * Nat.pow 2 kj) (bn_buf r)) (bn_buf tb) in
  bbind ops (bset ops t (bn_with_buf tb to)) (fun _ =>
  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 ro) top (bn_neg r) (bn_flags r))))))).

Definition disp_kara (rr : bnref) (la lb : list Z) (al bl top kj : nat) : BM (M := btree bptr) unit :=
  bbind ops (BN_CTX_get ops) (fun t =>
  if ((Nat.pow 2 kj <? al) || (Nat.pow 2 kj <? bl))%nat then disp_part rr t la lb al bl top kj else disp_rec rr t la lb al bl top kj).

Lemma kara_kj_facts : forall al bl : nat, (16 <= al)%nat -> (16 <= bl)%nat -> (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
  Z.of_nat al < 8388608 -> Z.of_nat bl < 8388608 ->
  let kj := Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1) in
  let j := Nat.pow 2 kj in
  (4 <= kj <= 23)%nat /\ (j <= Nat.max al bl)%nat /\ (Nat.max al bl < 2 * j)%nat /\ Z.of_nat kj = num_bits_word (Z.of_nat (Nat.max al bl)) - 1.
Proof.
  intros al bl Ha Hb H1 H2 HA HB. cbv zeta. set (mx := Nat.max al bl).
  assert (Hm16 : 16 <= Z.of_nat mx) by (subst mx; lia).
  assert (Hm : Z.of_nat mx < 8388608) by (subst mx; lia).
  destruct (num_bits_word_spec (Z.of_nat mx) ltac:(lia)) as (B1 & B2 & B3).
  set (bits := num_bits_word (Z.of_nat mx)) in *.
  set (kj := Z.to_nat (bits - 1)). assert (Ekj : Z.of_nat kj = bits - 1) by (subst kj; lia).
  assert (Ej : Z.of_nat (Nat.pow 2 kj) = 2 ^ (bits - 1)) by (rewrite Nat2Z.inj_pow, Ekj; reflexivity).
  assert (Hk4 : 4 <= bits - 1).
  { destruct (Z.lt_ge_cases (bits - 1) 4) as [Hlt|]; [exfalso|assumption].
    assert (2 ^ bits <= 2 ^ 4) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (Hk23 : bits - 1 <= 23).
  { destruct (Z.le_gt_cases (bits - 1) 23) as [|Hgt]; [assumption|exfalso].
    assert (2 ^ 24 <= 2 ^ (bits - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (E2 : 2 ^ bits = 2 * 2 ^ (bits - 1)).
  { replace bits with (Z.succ (bits - 1)) at 1 by lia. apply Z.pow_succ_r. lia. }
  split; [lia|]. split; [lia|]. split; [lia | exact Ekj].
Qed.

Definition mul_res (br : bignum bptr) (w : list Z) (top : nat) : bignum bptr :=
  mkBN (bn_d br) (splice (bn_buf br) 0 w) top (bn_neg br) (bn_flags br).

Lemma mul_res_ok : forall br w top, bg_ok br -> limbs w -> (length w <= bn_dmax br)%nat -> (top <= bn_dmax br)%nat -> bg_ok (mul_res br w top).
Proof.
  intros br w top (O1 & O2 & O3 & O4) LW HW HT. unfold bg_ok, mul_res, bn_dmax in *. cbn [bn_buf bn_top bn_flags].
  rewrite splice_length by lia. split; [apply splice_limbs; assumption|]. auto.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_MUL_FIXED_TOP : Z := 0x1026d8.
Definition BN_MUL_FIXED_STACK : Z := 112 + 9216.

Lemma open_ro_any : forall s OW LB m st PL EA r a,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> ref_at st OW PL r a ->
  exists D, ro_cells bgusegs m a (bn_cells D (getbn r st)).
Proof.
  intros s OW LB m st PL EA r a HEAP LS HA. pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open_ro [] st m OW PL EA r a LS ND HA ltac:(intros [])) as ((D & RO & _) & _). exists D. exact RO.
Qed.

Lemma ro_cells_app_l : forall m A cs1 cs2, ro_cells bgusegs m A (cs1 ++ cs2) -> ro_cells bgusegs m A cs1.
Proof. intros m A cs1 cs2. unfold ro_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, bytes_at_app. tauto. Qed.

Lemma opnd_ok : forall r (st : bstate bptr), st_wf st -> vref r st ->
  limbs (bn_buf (getbn r st)) /\ (bn_top (getbn r st) <= bn_dmax (getbn r st))%nat /\ Z.of_nat (bn_dmax (getbn r st)) <= 512.
Proof.
  intros r st WFS HV. destruct (Nat.eq_dec r ROne) as [->|NE].
  - pose proof (st_wf_okv ROne st WFS HV) as (L1 & L2). split; [exact L1|]. split; [exact L2|].
    destruct WFS as (_ & _ & E & _). rewrite E. unfold bn_dmax, bn_const_one. cbn. lia.
  - pose proof (st_wf_ok r st WFS HV NE) as (L1 & L2 & L3 & _). unfold BG_DMAX in L3. auto.
Qed.

Lemma opnd_view : forall s OW LB m st PL EA SPX BX rr R Dr x X k,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX -> mem_inv bgusegs m ->
  ref_at st OW PL rr R -> hpl PL rr -> rw_cells bgusegs m R (bn_cells Dr (getbn rr st)) -> bn_arr m OW (pl_of PL rr) Dr (getbn rr st) ->
  (0 < bn_dmax (getbn rr st))%nat ->
  ref_at st OW PL x X -> (k <= bn_top (getbn x st))%nat -> x <> rr ->
  exists Dx, ro_cells bgusegs m X [C8 (wz Dx)] /\ limbs_at bgusegs m Dx (firstn k (bn_buf (getbn x st)))
    /\ 0 < X /\ (X + 24 <= alloc_ceiling \/ (SPX <= X /\ X + 24 < 2^63))
    /\ 0 <= Dx /\ (Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) <= alloc_ceiling \/ (SPX <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) < 2^63))
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) <= R)
    /\ (Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) <= Dr)
    /\ ub_ptr_ok (Z.of_nat k) Dx.
Proof.
  intros s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK MI HR HP SR ARR HD0 HX Hk NE.
  destruct (Nat.eq_dec x ROne) as [->|NX].
  2:{ destruct (operand_view_ne s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK HR HP SR ARR HX NX Hk NE)
        as (Dx & HXd & HLX & _ & ARRX & X0 & XC & DX0 & DXC & _ & SXA & _ & ALX).
      assert (UBX : ub_ptr_ok (Z.of_nat k) Dx).
      { intros K0. apply (bn_arr_ualign s OW LB m st PL EA x Dx _ HEAP (lib_state_h_parts _ _ _ _ _ _ LS) ARRX).
        pose proof (opnd_ok x st (proj1 (lib_state_h_parts _ _ _ _ _ _ LS)) (ref_at_valid _ _ _ _ _ _ _ _ LS HX)) as (_ & TD & _). lia. }
      exists Dx. split; [exact (proj1 HXd)|]. split; [exact HLX|]. auto 10. }
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
  pose proof (ref_at_fun _ _ _ _ _ _ ND HX (ref_at_one st OW PL)) as EX. subst X.
  destruct (lib_state_open_ro [] st m OW PL EA ROne CONST_ONE LS ND HX ltac:(intros [])) as ((D & RO & ARO) & _).
  assert (EONE : getbn ROne st = bn_const_one) by (destruct WFS as (_ & _ & E & _); exact E).
  rewrite EONE in *. unfold bn_arr in ARO. rewrite pl_of_one in ARO. cbn [bn_d bn_const_one] in ARO. destruct ARO as [-> _].
  destruct (bn_arr_facts_w st OW PL EA SPX BX s LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (_ & _ & D0 & DC & DRI & _).
  pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & _).
  pose proof alloc_ceiling_range as CR.
  unfold bn_dmax in *. exists DATA_ONE. cbn [bn_buf bn_const_one length].
  split. { unfold bn_cells in RO. eapply (ro_cells_app_l m CONST_ONE [C8 (wz DATA_ONE)]). exact RO. }
  split.
  { destruct k as [|k]; [cbn [firstn]; apply limbs_at_nil; unfold DATA_ONE; lia|].
    cbn [firstn]. rewrite firstn_nil. pose proof (data_one_cells m MI) as DO. unfold ro_cells, cells_at in DO. exact (proj2 DO). }
  unfold CONST_ONE, DATA_ONE, ub_ptr_ok in *. repeat split; try lia.
Qed.

Lemma ref_at_rng : forall st OW PL EA SPX BX s LB m r a,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a ->
  0 < a /\ (a + 24 <= alloc_ceiling \/ (SPX <= a /\ a + 24 < 2^63)).
Proof.
  intros st OW PL EA SPX BX s LB m r a HEAP LS FROK HA. pose proof alloc_ceiling_range as CR.
  destruct (Nat.eq_dec r ROne) as [->|NE].
  - pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (ref_at_fun _ _ _ _ _ _ ND HA (ref_at_one st OW PL)) as E. subst a. unfold CONST_ONE. lia.
  - pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    destruct (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NE) as (A0 & AC & _). auto.
Qed.

Lemma ref_at_ualign_any : forall s OW LB m st PL EA r a,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> ref_at st OW PL r a -> a mod 8 = 0.
Proof.
  intros s OW LB m st PL EA r a HEAP LS HA.
  destruct (Nat.eq_dec r ROne) as [->|NE].
  - pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (ref_at_fun _ _ _ _ _ _ ND HA (ref_at_one st OW PL)) as E. subst a. unfold CONST_ONE. lia.
  - exact (proj2 (ref_at_ualign s OW LB m st PL EA r a HEAP (lib_state_h_parts _ _ _ _ _ _ LS) HA NE)).
Qed.

Definition mul_frame (jb : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition mul_join (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
    (jb : list byte) (rr x y : bnref) (R X Y ac : Z) (na nb : bool)
    (v : unit * bstate bptr) (st' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m' OW',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F (Z_to_bv 64 0x102940) fc None m' (seg_rom bgusegs)
    /\ kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st' (snd v) m' OW'
    /\ lib_state (snd v) m' OW' PL EA
    /\ ref_at (snd v) OW' PL rr R /\ ref_at (snd v) OW' PL x X /\ ref_at (snd v) OW' PL y Y
    /\ bn_neg (getbn x (snd v)) = na /\ bn_neg (getbn y (snd v)) = nb.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma mul_end : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (rr x y : bnref) (R X Y ac : Z) (qc : bptr) (na nb : bool) (v : unit * bstate bptr) (st' : PState) (ms' : machine_state),
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    hpl PL rr -> pl_ctx PL = Some (ac, qc) ->
    mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac na nb v st' ms' ->
    implM bgusegs (interp (embed (BN_CTX_end ops (setbn rr (bn_with_neg (getbn rr (snd v)) (xorb na nb)) (snd v))))) st'
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1)) ms'.
  Proof.
    intros until ms'. intros CEIL GLO LO SPB B63 FROK HP HPC (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x22 & x23 & x24 & x25 & x26 & x27 & t3 & t4 & t5 & t6
                                             & mE & OWE & -> & ENV & LS & HR & HX & HY & ENA & ENB).
    destruct v as [[] bsE]. cbn [fst snd] in *. pose proof (proj1 HP) as NRO.
    unfold BN_MUL_FIXED_STACK in LO. unfold mul_frame in ENV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (open_ro_any st' OWE LB mE bsE PL EA x X HEAP LS HX) as (Dx & SX).
    destruct (open_ro_any st' OWE LB mE bsE PL EA y Y HEAP LS HY) as (Dy & SY).
    unfold bn_cells, MallocRep.wz in SX, SY. rewrite ENA in SX. rewrite ENB in SY.
    destruct (lib_state_open [] bsE mE OWE PL EA rr R LS ND HR ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w bsE OWE PL EA (bv_unsigned sp) B st' LB mE rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    set (b := getbn rr bsE) in *.
    unfold bn_cells, MallocRep.wz in SR.
    assert (NA : 0 <= Z.b2z na <= 1) by (destruct na; cbn; lia).
    assert (NB : 0 <= Z.b2z nb <= 1) by (destruct nb; cbn; lia).
    pose proof (munch_refl [(R, R + 24)]%Z mE) as MU. pose proof (wmono_refl bgusegs mE) as WM.
    unfold implM. iprefix.
    zstep. rewrite (land7 R (proj2 (ref_at_ualign st' OWE LB mE bsE PL EA rr R HEAP PARTS HR NRO))). chk_lit.
    zstep. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
    zstep. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
    zstep.
    setreg 10%Z (Z_to_bv 64 (Z.b2z (xorb na nb))) ltac:(clear; destruct na, nb; reflexivity).
    clear SX SY.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    assert (HWL : Forall (w_lib bsE OWE PL lo (bv_unsigned sp)) [(R, R + 24)]).
    { constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia] | constructor]. }
    assert (WOK : Forall (w_ok OWE LB bsE PL EA (bv_unsigned sp) [rr]) [(R, R + 24)]).
    { constructor; [eapply (w_struct OWE LB bsE PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR | exact NRO | cbn; lia | cbn; lia] | constructor]. }
    set (bsN := setbn rr (bn_with_neg b (xorb na nb)) bsE).
    assert (LSN : lib_state bsN m1 OWE PL EA).
    { unfold lib_state, bsN. eapply (lib_state_close [] bsE m1 OWE PL EA rr R); [| exact ND | exact HR | exact NRO | | |].
      - eapply (lib_state_frame st' LB (bv_unsigned sp) B); [exact HEAP| exact LSH| exact MU| exact WM| exact FROK| exact WOK].
      - exists Dr. split; [unfold bn_cells, bn_with_neg, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; exact SR|].
        eapply bn_arr_of_u64arr; [exact ARR | exact U].
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, bn_with_neg, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
    assert (ENVN : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st' bsN m1 OWE).
    { apply kenv_setbn.
      eapply (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv);
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST | unfold LX_ERRNO, RATP; exact ERR | exact MI | exact FR | exact FSZ]. }
    clear ENV LS LSH SR U ARR ST ERR MI FR MU WM HWL WOK HEAP AUX LXP FA SO RS.
    zstep. if_cases KE; zify_cond KE; [|exfalso; apply KE; reflexivity]. clear KE.
    do 4 zstep.

    destruct (KPRE _ _ _ _ _ BN_CTX_END_STACK ENVN LSN ltac:(unfold BN_CTX_END_STACK; lia)) as (errvE & PREE).
    ihere. to_implM. fold b. fold bsN.
    eapply implM_post_evt.
    { eapply BN_CTX_end_walk; [exact PREE| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [uE bsF] stF msF PO. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mF & OWF & -> & KP & (_ & EOWF)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENVN KP) as (ENVF & LSF).
    cbn [fst snd] in *. clear PREE KP.
    replace (ret_pc (Z_to_bv 64 1059200)) with (Z_to_bv 64 1059200) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m _ _ _ _ _ ENVF) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    unfold mul_frame in FRF.
    zstep. do 13 zstep.
    release_frame FRF STF (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold bn_post. do 15 eexists. exists mF, OWF, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LSF|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
  Qed.

  Lemma mul_finish1 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st2 : PState) (bs2 : bstate bptr) (m2 : mem) (OW2 : list block) (rr x y : bnref) (R X Y ac Dr n8 CST : Z)
      (w : list Z) (topn : nat) (x22 x23 x24 x25 x26 x27 : word) (ms' : machine_state),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st2 bs2 m2 OW2 ->
    lib_state bs2 m2 OW2 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> 0 <= CST -> lo <= bv_unsigned sp - 112 - CST -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs2 OW2 PL rr R -> hpl PL rr -> ref_at bs2 OW2 PL x X -> ref_at bs2 OW2 PL y Y -> rr <> x -> rr <> y ->
    rw_cells bgusegs m2 R (bn_cells Dr (getbn rr bs2)) -> bn_arr m2 OW2 (pl_of PL rr) Dr (getbn rr bs2) ->
    limbs w -> (0 < length w <= bn_dmax (getbn rr bs2))%nat -> (topn <= bn_dmax (getbn rr bs2))%nat -> n8 = 8 * Z.of_nat (length w) ->
    mulc_post sp gp (wz RATP) F fc m2 lo R Dr (getbn rr bs2) sp (Z_to_bv 64 ac) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R)
              x22 x23 x24 x25 x26 x27 [(Dr, Dr + n8); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)] topn w (fun _ => True) ms' ->
    mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac
             (bn_neg (getbn x bs2)) (bn_neg (getbn y bs2)) (tt, setbn rr (mul_res (getbn rr bs2) w topn) bs2) st2 ms'.
  Proof.
    intros until ms'. intros ENV LS CEIL GLO HCST LO SPB B63 FROK HR HP HX HY NEX NEY SR ARR LW [HW0 HWD] HTD ->
      (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & -> & MU & WM & MI3 & SR3 & HR3 & ST3 & _).
    pose proof (proj1 HP) as NRO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] bs2 m2 OW2 PL EA rr R LS ND HR ltac:(intros []) NRO) as (_ & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w bs2 OW2 PL EA (bv_unsigned sp) B st2 LB m2 rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (U & LENW & D0 & DC & DRI & DSEP).
    pose proof (DSEP rr R HR) as DSR.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    set (br := getbn rr bs2) in *.
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
    unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct (bn_arr_null PL rr m2 OW2 Dr br PWF (hpl_wref PL rr HP) Edr ltac:(unfold bn_arr; rewrite Edr; exact ARR)) as [_ Eb]. rewrite Eb in LBR. cbn [length] in LBR. lia. }
    destruct ARR as [HinR _].
    set (W := [(Dr, Dr + 8 * Z.of_nat (length w)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]) in *.
    assert (HWL : Forall (w_lib bs2 OW2 PL lo (bv_unsigned sp)) W).
    { constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | clear - HWD; lia]|].
      constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | clear - Ra1 Ra2; lia]|].
      constructor; [left; cbn [fst snd]; clear - LO HCST; lia | constructor]. }
    assert (WOK : Forall (w_ok OW2 LB bs2 PL EA (bv_unsigned sp) [rr]) W).
    { constructor; [eapply (w_limbs OW2 LB bs2 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; clear; lia | cbn [fst snd]; fold br; clear - HWD; lia]|].
      constructor; [eapply (w_struct OW2 LB bs2 PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR | exact NRO | cbn; clear; lia | cbn; clear; lia]|].
      constructor; [apply w_stack; cbn [fst snd]; clear - LO HCST CEIL; lia | constructor]. }
    assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (rewrite splice_length; [exact LBR| rewrite LBR; clear - HWD; lia]).
    set (bsN := setbn rr (mul_res br w topn) bs2).
    assert (LSN : lib_state bsN m3 OW2 PL EA).
    { unfold lib_state, bsN. eapply (lib_state_close [] bs2 m3 OW2 PL EA rr R); [| exact ND | exact HR | exact NRO | | |].
      - eapply (lib_state_frame st2 LB (bv_unsigned sp) B); [exact HEAP| exact LSH| exact MU| exact WM| exact FROK| exact WOK].
      - exists Dr. split; [unfold bn_cells, mul_res, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR3|].
        unfold bn_arr, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, LSP.
        split; [exact HinR|].
        eapply BnAKit.arr_splice0; [exact U | exact MU | exact WM | exact HR3 | rewrite LBR; clear - HWD; lia | |]; subst W; cbn [disjoint_from]; rewrite ?LBR; clear - DSR DC CEIL LO HCST HWD; lia.
      - apply mul_res_ok; [exact OKR | exact LW | clear - HWD; lia | exact HTD].
      - apply ids_ok_setbn_same; [exact IDS | exact HVR |]. unfold bn_blocks, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
    unfold mul_join. do 22 eexists. exists m3, OW2. split; [reflexivity|]. cbn [fst snd]. fold bsN.
    split.
    { apply kenv_setbn.
      eapply (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv);
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST3 | | exact MI3 | | exact FSZ].
      - eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold LX_ERRNO, RATP. subst W. cbn. clear - DRI D0 SAI SA0 GLO LO HCST HWD HW0. lia.
      - eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. subst W. cbn. clear - DC SAC CEIL LO HCST HWD. lia. }
    split; [exact LSN|].
    split; [apply ref_at_setbn; exact HR|]. split; [apply ref_at_setbn; exact HX|]. split; [apply ref_at_setbn; exact HY|].
    unfold bsN. rewrite !getbn_setbn_other by assumption. split; reflexivity.
  Qed.

  Lemma mul_finish2 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st3 : PState) (bs3 : bstate bptr) (m3 : mem) (OW3 : list block) (rr t x y : bnref) (R TT X Y ac Dr Dt nr8 CST : Z)
      (w tw : list Z) (topn : nat) (x22 x23 x24 x25 x26 x27 : word) (ms' : machine_state),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st3 bs3 m3 OW3 ->
    lib_state bs3 m3 OW3 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> 0 <= CST -> lo <= bv_unsigned sp - 112 - CST -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs3 OW3 PL rr R -> hpl PL rr -> ref_at bs3 OW3 PL t TT -> hpl PL t -> ref_at bs3 OW3 PL x X -> ref_at bs3 OW3 PL y Y ->
    rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
    rw_cells bgusegs m3 R (bn_cells Dr (getbn rr bs3)) -> bn_arr m3 OW3 (pl_of PL rr) Dr (getbn rr bs3) ->
    rw_cells bgusegs m3 TT (bn_cells Dt (getbn t bs3)) -> bn_arr m3 OW3 (pl_of PL t) Dt (getbn t bs3) ->
    limbs w -> (0 < length w <= bn_dmax (getbn rr bs3))%nat -> (topn <= bn_dmax (getbn rr bs3))%nat -> nr8 = 8 * Z.of_nat (length w) ->
    limbs tw -> length tw = bn_dmax (getbn t bs3) -> (0 < bn_dmax (getbn t bs3))%nat ->
    mulc_post sp gp (wz RATP) F fc m3 lo R Dr (getbn rr bs3) sp (Z_to_bv 64 ac) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R)
              x22 x23 x24 x25 x26 x27
              [(Dr, Dr + nr8); (Dt, Dt + 8 * Z.of_nat (length (bn_buf (getbn t bs3)))); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]
              topn w (fun m' => limbs_at bgusegs m' Dt tw) ms' ->
    mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac
             (bn_neg (getbn x bs3)) (bn_neg (getbn y bs3))
             (tt, setbn rr (mul_res (getbn rr bs3) w topn) (setbn t (bn_with_buf (getbn t bs3) tw) bs3)) st3 ms'.
  Proof.
    intros until ms'. intros ENV LS CEIL GLO HCST LO SPB B63 FROK HR HP HT HPT HX HY NEX NEY NTR NTX NTY SR ARR STT ARRT LW [HW0 HWD] HTD -> LTW NTW HT0
      (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m4 & -> & MU & WM & MI4 & SR4 & HR4 & ST4 & HT4).
    pose proof (proj1 HP) as NRO. pose proof (proj1 HPT) as NROT.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] bs3 m3 OW3 PL EA rr R LS ND HR ltac:(intros []) NRO) as (_ & OKR & LSH1).
    destruct (lib_state_open [rr] bs3 m3 OW3 PL EA t TT LSH1 ND HT ltac:(intros [E|[]]; apply NTR; symmetry; exact E) NROT) as (_ & OKT & LSH2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w bs3 OW3 PL EA (bv_unsigned sp) B st3 LB m3 rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (U & _ & D0 & DC & DRI & DSEP).
    destruct (bn_arr_facts_w bs3 OW3 PL EA (bv_unsigned sp) B st3 LB m3 t Dt HEAP PARTS FROK HVT (hpl_wref PL t HPT) ARRT) as (UT & _ & DT0 & DTC & DTI & DSEPT).
    pose proof (DSEP rr R HR) as DSR. pose proof (DSEP t TT HT) as DSRT. pose proof (DSEPT rr R HR) as DSTR. pose proof (DSEPT t TT HT) as DSTT.
    pose proof (struct_disj st3 OW3 LB m3 HEAP bs3 PL EA _ _ PARTS FROK t rr TT R NTR HT HR) as SDT.
    pose proof (bn_arrs_disj st3 OW3 LB m3 bs3 PL EA (bv_unsigned sp) B rr t R TT Dr Dt HEAP LS FROK ltac:(congruence) HR HT NRO NROT ARR ARRT) as ADJ.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HT HPT) as (TA0 & TAC & TAI & (qt & At & nt & Hint & Rt1 & Rt2)).
    set (br := getbn rr bs3) in *. set (tb := getbn t bs3) in *.
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity. assert (LBT : length (bn_buf tb) = bn_dmax tb) by reflexivity.
    unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct (bn_arr_null PL rr m3 OW3 Dr br PWF (hpl_wref PL rr HP) Edr ltac:(unfold bn_arr; rewrite Edr; exact ARR)) as [_ Eb]. rewrite Eb in LBR. cbn [length] in LBR. lia. }
    destruct ARR as [HinR _].
    unfold bn_arr in ARRT. destruct (bn_d tb) as [pt|] eqn:Edt.
    2:{ exfalso. destruct (bn_arr_null PL t m3 OW3 Dt tb PWF (hpl_wref PL t HPT) Edt ltac:(unfold bn_arr; rewrite Edt; exact ARRT)) as [_ Eb]. rewrite Eb in LBT. cbn [length] in LBT. lia. }
    destruct ARRT as [HinT _].
    rewrite LBT in MU.
    set (W := [(Dr, Dr + 8 * Z.of_nat (length w)); (Dt, Dt + 8 * Z.of_nat (bn_dmax tb)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]) in *.
    assert (HWL : Forall (w_lib bs3 OW3 PL lo (bv_unsigned sp)) W).
    { constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | clear - HWD; lia]|].
      constructor; [right; left; exists (pt, Dt, 8 * Z.of_nat (bn_dmax tb)); cbn [blk_addr blk_size fst snd]; split; [exact HinT | clear; lia]|].
      constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | clear - Ra1 Ra2; lia]|].
      constructor; [left; cbn [fst snd]; clear - LO HCST; lia | constructor]. }
    assert (WOK : Forall (w_ok OW3 LB bs3 PL EA (bv_unsigned sp) [t; rr]) W).
    { constructor; [eapply (w_limbs OW3 LB bs3 PL EA (bv_unsigned sp) false [t; rr] _ rr pr Dr); [right; left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; clear; lia | cbn [fst snd]; fold br; clear - HWD; lia]|].
      constructor; [eapply (w_limbs OW3 LB bs3 PL EA (bv_unsigned sp) false [t; rr] _ t pt Dt); [left; reflexivity | exact HVT | exact Edt | exact HinT | cbn [fst snd]; clear; lia | cbn [fst snd]; fold tb; clear; lia]|].
      constructor; [eapply (w_struct OW3 LB bs3 PL EA (bv_unsigned sp) false [t; rr] _ rr R); [right; left; reflexivity | exact HR | exact NRO | cbn; clear; lia | cbn; clear; lia]|].
      constructor; [apply w_stack; cbn [fst snd]; clear - LO HCST CEIL; lia | constructor]. }
    pose proof (lib_state_frame st3 LB (bv_unsigned sp) B [t; rr] bs3 m3 m4 OW3 PL EA _ HEAP LSH2 MU WM FROK WOK) as LSH2'.

    set (tb' := bn_with_buf tb tw).
    assert (LSH1' : lib_state_h [rr] (setbn t tb' bs3) m4 OW3 PL EA).
    { eapply (lib_state_close [rr] bs3 m4 OW3 PL EA t TT); [exact LSH2' | exact ND | exact HT | exact NROT | | |].
      - exists Dt. split.
        + unfold tb', bn_cells, bn_with_buf, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite NTW.
          eapply rw_cells_transport; [exact STT | exact MU | exact WM |]. subst W. cbn. clear - DSRT DSTT SDT TAC CEIL LO HCST HWD. lia.
        + unfold bn_arr, tb', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite Edt, NTW.
          split; [exact HinT|]. apply u64arr_of_limbs_at; [exact HT4|]. rewrite NTW.
          apply (limbarr_limbs_at bgusegs) in UT. destruct UT as [_ HWT]. eapply wr_at_transport; [exact HWT | exact WM].
      - destruct OKT as (O1 & O2 & O3 & O4). unfold bg_ok, tb', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite NTW. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVT |]. unfold bn_blocks, tb', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite NTW. reflexivity. }

    assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (rewrite splice_length; [exact LBR| rewrite LBR; clear - HWD; lia]).
    set (bs3' := setbn t tb' bs3) in *.
    assert (EGR : getbn rr bs3' = br) by (unfold bs3'; apply getbn_setbn_other; exact NTR).
    assert (HR' : ref_at bs3' OW3 PL rr R) by (apply ref_at_setbn; exact HR).
    assert (HVR' : vref rr bs3') by (eapply ref_at_valid; [exact LSH1' | exact HR']).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSH1') as PARTS'; pose proof PARTS' as (_ & _ & IDS' & _ & _).
    assert (LSN : lib_state (setbn rr (mul_res br w topn) bs3') m4 OW3 PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs3' m4 OW3 PL EA rr R); [exact LSH1' | exact ND | exact HR' | exact NRO | | |].
      - exists Dr. split; [unfold bn_cells, mul_res, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR4|].
        unfold bn_arr, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, LSP.
        split; [exact HinR|].
        eapply BnAKit.arr_splice0; [exact U | exact MU | exact WM | exact HR4 | rewrite LBR; clear - HWD; lia | |]; subst W; cbn [disjoint_from]; rewrite ?LBR; clear - DSR ADJ DC CEIL LO HCST HWD; lia.
      - apply mul_res_ok; [exact OKR | exact LW | clear - HWD; lia | exact HTD].
      - apply ids_ok_setbn_same; [exact IDS' | exact HVR' |]. rewrite EGR. unfold bn_blocks, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
    unfold mul_join. do 22 eexists. exists m4, OW3. split; [reflexivity|]. cbn [fst snd]. fold tb'. fold bs3'.
    split.
    { apply kenv_setbn. apply kenv_setbn.
      eapply (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv);
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST4 | | exact MI4 | | exact FSZ].
      - eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold LX_ERRNO, RATP. subst W. cbn. clear - DRI DTI D0 DT0 SAI SA0 GLO LO HCST HWD HW0 HT0. lia.
      - eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. subst W. cbn. clear - DC DTC SAC CEIL LO HCST HWD. lia. }
    split; [exact LSN|].
    split; [apply ref_at_setbn; exact HR'|]. split; [apply ref_at_setbn; apply ref_at_setbn; exact HX|]. split; [apply ref_at_setbn; apply ref_at_setbn; exact HY|].
    unfold bs3'. rewrite !getbn_setbn_other by assumption. split; reflexivity.
  Qed.

  Lemma mul_path_normal : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st1 : PState) (bs1 : bstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y ac : Z) (al bl : nat)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 x27 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st1 bs1 m1 OW1 ->
    lib_state bs1 m1 OW1 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs1 OW1 PL rr R -> hpl PL rr -> ref_at bs1 OW1 PL x X -> ref_at bs1 OW1 PL y Y -> rr <> x -> rr <> y ->
    al = bn_top (getbn x bs1) -> bl = bn_top (getbn y bs1) -> (0 < al)%nat -> (0 < bl)%nat ->
    implM bgusegs (interp (embed (disp_normal rr (firstn al (bn_buf (getbn x bs1))) (firstn bl (bn_buf (getbn y bs1))) (al + bl) bs1))) st1
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac
                (bn_neg (getbn x bs1)) (bn_neg (getbn y bs1)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
               (Z_to_bv 64 (Z.of_nat bl)) x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1028a4) fc None m1 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HX HY NEX NEY EAL EBL HAL HBL.
    pose proof (proj1 HP) as NRO.
    pose proof LO as LO'. unfold BN_MUL_FIXED_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS1; pose proof PARTS1 as (WFS1 & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
    pose proof (st_wf_ok rr bs1 WFS1 HVR NRO) as (_ & TDR1 & _).
    pose proof (opnd_ok x bs1 WFS1 HVX) as (LMX & TDX & DMX). pose proof (opnd_ok y bs1 WFS1 HVY) as (LMY & TDY & DMY).
    set (la := firstn al (bn_buf (getbn x bs1))). set (lb := firstn bl (bn_buf (getbn y bs1))).
    assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
    assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
    unfold implM. iprefix. do 2 zstep.

    destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO'; lia)) as (errv1 & PRE1).
    zstep.
    ihere. to_implM. unfold disp_normal. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 rr (al + bl) bs1 HVR TDR1)|].
      eapply (bn_wexpand_walk HM HF) with (r := rr) (a := R) (words := (al + bl)%nat);
        [exact PRE1 | reflexivity | exact HR | exact (hpl_wref PL rr HP) | reflexivity | unfold MallocRep.wz; f_equal; clear; lia
        | clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia]. }
    cbv beta. intros [u2 bs2] st2 ms2 [PO LEAF]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & -> & HDM & WRES & BST)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS; apply kpost_refs in RS.
    cbn [fst snd] in *. clear PRE1 KP ENV LS.
    replace (ret_pc (Z_to_bv 64 1058992)) with (Z_to_bv 64 1058992) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS HR) as HR2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS HX) as HX2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS HY) as HY2.
    destruct LEAF as (LOTH & _).
    assert (EGX : getbn x bs2 = getbn x bs1) by (apply LOTH; exact NEX).
    assert (EGY : getbn y bs2 = getbn y bs1) by (apply LOTH; exact NEY).

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.

    pose proof ENV2 as (HEAP2 & _ & ST2 & _ & MI2 & _).
    destruct (open_full st2 OW2 LB m2 bs2 PL EA (bv_unsigned sp) B rr R HEAP2 LS2 FROK HR2 HP) as (Dr & SR & ARR & OKR & UR & SA0 & SAC & DR0 & DRC & DSEPR).
    assert (HD0 : (0 < bn_dmax (getbn rr bs2))%nat) by (clear - HDM HAL; lia).
    destruct (opnd_view st2 OW2 LB m2 bs2 PL EA (bv_unsigned sp) B rr R Dr x X al HEAP2 LS2 FROK MI2 HR2 HP SR ARR HD0 HX2 ltac:(rewrite EGX; clear - EAL; lia) ltac:(congruence))
      as (Dx & HXd & HLX & X0' & XC' & DX0 & DXC & SXA & ALX & UBX).
    destruct (opnd_view st2 OW2 LB m2 bs2 PL EA (bv_unsigned sp) B rr R Dr y Y bl HEAP2 LS2 FROK MI2 HR2 HP SR ARR HD0 HY2 ltac:(rewrite EGY; clear - EBL; lia) ltac:(congruence))
      as (Dy & HYd & HLY & Y0' & YC' & DY0 & DYC & SYA & ALY & UBY).
    rewrite EGX in HLX, DXC, SXA, ALX. rewrite EGY in HLY, DYC, SYA, ALY. fold la in HLX. fold lb in HLY.
    pose proof (mul_normal_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY)) as (LW & _ & NW).
    rewrite LLA, LLB in NW.
    replace ((al =? 0)%nat || (bl =? 0)%nat) with false in NW by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; lia).
    specialize (DSEPR rr R HR2).
    set (br := getbn rr bs2) in *.
    replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    eapply evt_mono.
    { eapply (mulc_normal sp gp (wz RATP) F fc m2 lo R X Y Dr Dx Dy 9216 br la lb).
      - unfold mulc_pre. rewrite LLA, LLB.
        split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|]. split; [exact (bg_okm _ OKR)|].
        split; [clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
        split; [clear - SA0 SAC X0' XC' Y0' YC' DR0 DRC DX0 DXC DY0 DYC CEIL LO' SPR TDX TDY EAL EBL B63 SPB; unfold bn_dmax in *; lia|].
        split; [exact DSEPR|]. split; [clear - SXA TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - SYA TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - ALX TDX EAL; unfold bn_dmax in *; lia | clear - ALY TDY EBL; unfold bn_dmax in *; lia].
      - unfold mulc_upre.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st2 OW2 LB m2 bs2 PL EA rr R HEAP2 (lib_state_h_parts _ _ _ _ _ _ LS2) HR2 (proj1 HP)))|].
        split; [intros _; apply (bn_arr_ualign st2 OW2 LB m2 bs2 PL EA rr Dr br HEAP2 (lib_state_h_parts _ _ _ _ _ _ LS2) ARR); exact HD0|].
        split; [intros _; apply UBX; clear - HAL; lia | intros _; apply UBY; clear - HBL; lia].
      - unfold mulc_mem. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
        split; [exact HLX|]. split; [exact HLY|]. split; [exact ST2 | exact MI2].
      - rewrite LLA, LLB. exact HDM.
      - lia. }
    intros ms' PO.
    eapply (mul_finish1 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb st2 bs2 m2 OW2 rr x y R X Y ac Dr
              (8 * (Z.of_nat (length la) + Z.of_nat (length lb))) 9216 (mul_normal la lb) (length la + length lb)%nat) in PO;
      [ | exact ENV2 | exact LS2 | exact CEIL | exact GLO' | lia | clear - LO'; lia | exact SPB | exact B63 | exact FROK | exact HR2 | exact HP | exact HX2 | exact HY2 | exact NEX | exact NEY
        | exact SR | | exact LW | | | ].
    - rewrite EGX, EGY in PO. fold br. rewrite LLA, LLB in PO. exact PO.
    - subst br. exact ARR.
    - rewrite NW. fold br. clear - HDM HAL. lia.
    - rewrite LLA, LLB. fold br. exact HDM.
    - rewrite NW, LLA, LLB. clear. lia.
  Qed.

  Lemma mul_path_comba8 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st1 : PState) (bs1 : bstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y ac : Z)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st1 bs1 m1 OW1 ->
    lib_state bs1 m1 OW1 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs1 OW1 PL rr R -> hpl PL rr -> ref_at bs1 OW1 PL x X -> ref_at bs1 OW1 PL y Y -> rr <> x -> rr <> y ->
    bn_top (getbn x bs1) = 8%nat -> bn_top (getbn y bs1) = 8%nat ->
    implM bgusegs (interp (embed (disp_comba8 rr (firstn 8 (bn_buf (getbn x bs1))) (firstn 8 (bn_buf (getbn y bs1))) bs1))) st1
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac
                (bn_neg (getbn x bs1)) (bn_neg (getbn y bs1)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x102794) fc None m1 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HX HY NEX NEY EAL0 EBL0.
    set (al := 8%nat). set (bl := 8%nat).
    assert (EAL : al = bn_top (getbn x bs1)) by (symmetry; exact EAL0). assert (EBL : bl = bn_top (getbn y bs1)) by (symmetry; exact EBL0).
    pose proof (proj1 HP) as NRO.
    pose proof LO as LO'. unfold BN_MUL_FIXED_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS1; pose proof PARTS1 as (WFS1 & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
    pose proof (st_wf_ok rr bs1 WFS1 HVR NRO) as (_ & TDR1 & _).
    pose proof (opnd_ok x bs1 WFS1 HVX) as (LMX & TDX & DMX). pose proof (opnd_ok y bs1 WFS1 HVY) as (LMY & TDY & DMY).
    set (la := firstn al (bn_buf (getbn x bs1))). set (lb := firstn bl (bn_buf (getbn y bs1))).
    assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
    assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
    unfold implM. iprefix. do 2 zstep.

    destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO'; lia)) as (errv1 & PRE1).
    zstep.
    ihere. to_implM. unfold disp_comba8. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 rr 16 bs1 HVR TDR1)|].
      eapply (bn_wexpand_walk HM HF) with (r := rr) (a := R) (words := 16%nat);
        [exact PRE1 | reflexivity | exact HR | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | clear; lia]. }
    cbv beta. intros [u2 bs2] st2 ms2 [PO LEAF]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & -> & HDM & WRES & BST)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS; apply kpost_refs in RS.
    cbn [fst snd] in *. clear PRE1 KP ENV LS.
    replace (ret_pc (Z_to_bv 64 1058720)) with (Z_to_bv 64 1058720) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS HR) as HR2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS HX) as HX2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS HY) as HY2.
    destruct LEAF as (LOTH & _).
    assert (EGX : getbn x bs2 = getbn x bs1) by (apply LOTH; exact NEX).
    assert (EGY : getbn y bs2 = getbn y bs1) by (apply LOTH; exact NEY).

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.

    pose proof ENV2 as (HEAP2 & _ & ST2 & _ & MI2 & _).
    destruct (open_full st2 OW2 LB m2 bs2 PL EA (bv_unsigned sp) B rr R HEAP2 LS2 FROK HR2 HP) as (Dr & SR & ARR & OKR & UR & SA0 & SAC & DR0 & DRC & DSEPR).
    assert (HD0 : (0 < bn_dmax (getbn rr bs2))%nat) by (clear - HDM; lia).
    destruct (opnd_view st2 OW2 LB m2 bs2 PL EA (bv_unsigned sp) B rr R Dr x X al HEAP2 LS2 FROK MI2 HR2 HP SR ARR HD0 HX2 ltac:(rewrite EGX; clear - EAL; lia) ltac:(congruence))
      as (Dx & HXd & HLX & X0' & XC' & DX0 & DXC & SXA & ALX & UBX).
    destruct (opnd_view st2 OW2 LB m2 bs2 PL EA (bv_unsigned sp) B rr R Dr y Y bl HEAP2 LS2 FROK MI2 HR2 HP SR ARR HD0 HY2 ltac:(rewrite EGY; clear - EBL; lia) ltac:(congruence))
      as (Dy & HYd & HLY & Y0' & YC' & DY0 & DYC & SYA & ALY & UBY).
    rewrite EGX in HLX, DXC, SXA, ALX. rewrite EGY in HLY, DYC, SYA, ALY. fold la in HLX. fold lb in HLY.
    pose proof (mul_comba8_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY) LLA LLB) as (LW & NW & _).
    specialize (DSEPR rr R HR2).
    set (br := getbn rr bs2) in *.
    eapply evt_mono.
    { eapply (mulc_comba8 sp gp (wz RATP) F fc m2 lo R X Y Dr Dx Dy 9216 br la lb) with (CS8 := HxComba8U.CS8).
      - unfold mulc_pre. rewrite LLA, LLB.
        split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|]. split; [exact (bg_okm _ OKR)|].
        split; [clear; subst al bl; lia|].
        split; [clear - SA0 SAC X0' XC' Y0' YC' DR0 DRC DX0 DXC DY0 DYC CEIL LO' SPR TDX TDY EAL EBL B63 SPB; unfold bn_dmax in *; lia|].
        split; [exact DSEPR|]. split; [clear - SXA TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - SYA TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - ALX TDX EAL; unfold bn_dmax in *; lia | clear - ALY TDY EBL; unfold bn_dmax in *; lia].
      - unfold mulc_upre.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st2 OW2 LB m2 bs2 PL EA rr R HEAP2 (lib_state_h_parts _ _ _ _ _ _ LS2) HR2 (proj1 HP)))|].
        split; [intros _; apply (bn_arr_ualign st2 OW2 LB m2 bs2 PL EA rr Dr br HEAP2 (lib_state_h_parts _ _ _ _ _ _ LS2) ARR); exact HD0|].
        split; [intros _; apply UBX; subst al; lia | intros _; apply UBY; subst bl; lia].
      - unfold mulc_mem. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
        split; [exact HLX|]. split; [exact HLY|]. split; [exact ST2 | exact MI2].
      - exact HxComba8U.comba8_uok.
      - unfold HxComba8U.CS8. clear. lia.
      - exact LLA.
      - exact LLB.
      - exact HDM. }
    intros ms' PO.
    eapply (mul_finish1 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb st2 bs2 m2 OW2 rr x y R X Y ac Dr
              (8 * 16) 9216 (mul_comba8 la lb) 16%nat) in PO;
      [ | exact ENV2 | exact LS2 | exact CEIL | exact GLO' | lia | clear - LO'; lia | exact SPB | exact B63 | exact FROK | exact HR2 | exact HP | exact HX2 | exact HY2 | exact NEX | exact NEY
        | exact SR | | exact LW | | | ].
    - rewrite EGX, EGY in PO. fold br. exact PO.
    - subst br. exact ARR.
    - rewrite NW. fold br. clear - HDM. lia.
    - fold br. exact HDM.
    - rewrite NW. reflexivity.
  Qed.

  Lemma mul_path_rec : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st2 : PState) (bs2 : bstate bptr) (m2 : mem) (OW2 : list block) (rr t x y : bnref) (R TT X Y ac : Z) (al bl kj : nat)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st2 bs2 m2 OW2 ->
    lib_state bs2 m2 OW2 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs2 OW2 PL rr R -> hpl PL rr -> ref_at bs2 OW2 PL t TT -> hpl PL t -> ref_at bs2 OW2 PL x X -> x <> ROne -> ref_at bs2 OW2 PL y Y -> y <> ROne ->
    rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
    al = bn_top (getbn x bs2) -> bl = bn_top (getbn y bs2) ->
    (1 <= kj <= 23)%nat -> (al <= Nat.pow 2 kj)%nat -> (bl <= Nat.pow 2 kj)%nat -> (Nat.pow 2 kj - al <= 1)%nat -> (Nat.pow 2 kj - bl <= 1)%nat ->
    implM bgusegs (interp (embed (disp_rec rr t (firstn al (bn_buf (getbn x bs2))) (firstn bl (bn_buf (getbn y bs2))) al bl (al + bl) kj bs2))) st2
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac
                (bn_neg (getbn x bs2)) (bn_neg (getbn y bs2)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
               (Z_to_bv 64 (Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kj))) (Z_to_bv 64 TT) (Z_to_bv 64 (2 * Z.of_nat (Nat.pow 2 kj))) t3 t4 t5 t6)
          F (Z_to_bv 64 0x102840) fc None m2 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HT HPT HX NX HY NY NEX NEY NTR NTX NTY EAL EBL HKJ HALJ HBLJ HDA HDB.
    pose proof (proj1 HP) as NRO. pose proof (proj1 HPT) as NROT.
    pose proof LO as LO'. unfold BN_MUL_FIXED_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS2; pose proof PARTS2 as (WFS2 & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
    pose proof (st_wf_ok t bs2 WFS2 HVT NROT) as (_ & TDT2 & _).
    assert (PJ : 2 <= Z.of_nat (Nat.pow 2 kj) <= 8388608).
    { rewrite Nat2Z.inj_pow. change (Z.of_nat 2) with 2. split.
      - change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia.
      - change 8388608 with (2 ^ 23). apply Z.pow_le_mono_r; lia. }
    set (j := Nat.pow 2 kj) in *.
    assert (EJ : Z.of_nat j = 2 ^ Z.of_nat kj) by (subst j; rewrite Nat2Z.inj_pow; reflexivity).
    assert (HKJ' : (1 <= kj <= 26)%nat) by (clear - HKJ; lia).
    unfold implM. iprefix. do 2 zstep.
    rewrite (bn_swrap32_small (2 * Z.of_nat j + 1073741824)) by (clear - PJ; lia).
    zstep. rewrite lts_small by (clear - PJ; lia). if_cases C; [exfalso; zify_cond C; clear - C PJ; lia | clear C].
    zstep.
    setreg 27%Z (Z_to_bv 64 (Z.of_nat (4 * j)))
      ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2; rewrite bn_swrap32_small by (clear - PJ; lia); clear; lia).
    do 2 zstep.

    destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO'; lia)) as (errv1 & PRE1).
    zstep.
    ihere. to_implM. unfold disp_rec. unfold bbind at 1. cbn [bind tree_ops]. fold j.
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 t (4 * j) bs2 HVT TDT2)|].
      eapply (bn_wexpand_walk HM HF) with (r := t) (a := TT) (words := (4 * j)%nat);
        [exact PRE1 | reflexivity | exact HT | exact (hpl_wref PL t HPT) | reflexivity | reflexivity | clear - PJ; lia]. }
    cbv beta. intros [u3 bs3] st3 ms3 [PO LEAF3]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP3 & (_ & -> & HDM3 & WRES3 & BST3)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP3) as (ENV3 & LS3). pose proof KP3 as RS3; apply kpost_refs in RS3.
    cbn [fst snd] in *. clear PRE1 KP3 ENV LS.
    replace (ret_pc (Z_to_bv 64 1058908)) with (Z_to_bv 64 1058908) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HR) as HR3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HT) as HT3.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HX) as HX3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HY) as HY3.
    destruct LEAF3 as (LOTH3 & _).

    pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as PARTS3; pose proof PARTS3 as (WFS3 & _).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV3) PARTS3 HT3 HPT) as (TA0 & TAC & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KT; zify_cond KT; [exfalso; clear - KT TA0 TAC CEIL LO' SPR; lia|]. clear KT.
    do 2 zstep.

    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS3 HR3) as HVR3.
    pose proof (st_wf_ok rr bs3 WFS3 HVR3 NRO) as (_ & TDR3 & _).
    destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV3 LS3 ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO'; lia)) as (errv3 & PRE3).
    zstep.
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops fst snd].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 rr (4 * j) bs3 HVR3 TDR3)|].
      eapply (bn_wexpand_walk HM HF) with (r := rr) (a := R) (words := (4 * j)%nat);
        [exact PRE3 | reflexivity | exact HR3 | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | clear - PJ; lia]. }
    cbv beta. intros [u4 bs4] st4 ms4 [PO LEAF4]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP4 & (_ & -> & HDM4 & WRES4 & BST4)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP4) as (ENV4 & LS4). pose proof KP4 as RS4; apply kpost_refs in RS4.
    cbn [fst snd] in *. clear PRE3 KP4 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1058924)) with (Z_to_bv 64 1058924) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HR3) as HR4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HT3) as HT4.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HX3) as HX4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HY3) as HY4.
    destruct LEAF4 as (LOTH4 & _).
    assert (EGX : getbn x bs4 = getbn x bs2) by (rewrite (LOTH4 x NEX); apply LOTH3; exact NTX).
    assert (EGY : getbn y bs4 = getbn y bs2) by (rewrite (LOTH4 y NEY); apply LOTH3; exact NTY).
    assert (EGT : getbn t bs4 = getbn t bs3) by (apply LOTH4; congruence).
    clear HVR3 TDR3 PARTS3 WFS3 WRES3 WRES4 BST3 BST4.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    set (la := firstn al (bn_buf (getbn x bs2))). set (lb := firstn bl (bn_buf (getbn y bs2))).
    destruct (mul_recursive kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf (getbn rr bs4))) (bn_buf (getbn t bs4))) as [ro to] eqn:EMR.
    cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.

    pose proof ENV4 as (HEAP4 & _ & ST4 & _ & MI4 & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4; pose proof PARTS4 as (WFS4 & _).
    destruct (open_full st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B rr R HEAP4 LS4 FROK HR4 HP) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (open_full st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B t TT HEAP4 LS4 FROK HT4 HPT) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
    destruct (operand_view_ne st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B rr R Dr x X al HEAP4 LS4 FROK HR4 HP SR ARR HX4 NX ltac:(rewrite EGX; clear - EAL; lia) ltac:(congruence))
      as (Dx & HXd & HLX & UX & ARRX & X0 & XC & DX0 & DXC & _ & S2 & _ & DRX).
    destruct (operand_view_ne st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B rr R Dr y Y bl HEAP4 LS4 FROK HR4 HP SR ARR HY4 NY ltac:(rewrite EGY; clear - EBL; lia) ltac:(congruence))
      as (Dy & HYd & HLY & UY & ARRY & Y0 & YC & DY0 & DYC & _ & S3 & _ & DRY).
    pose proof (bn_arrs_disj st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B t x TT X Dt Dx HEAP4 LS4 FROK NTX HT4 HX4 NROT NX ARRT ARRX) as DTX.
    pose proof (bn_arrs_disj st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B t y TT Y Dt Dy HEAP4 LS4 FROK NTY HT4 HY4 NROT NY ARRT ARRY) as DTY.
    pose proof (bn_arrs_disj st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B rr t R TT Dr Dt HEAP4 LS4 FROK ltac:(congruence) HR4 HT4 NRO NROT ARR ARRT) as DRT.
    pose proof (DSEPR rr R HR4) as S1. pose proof (DSEPT rr R HR4) as S4.
    clear DSEPR DSEPT.
    rewrite EGX in *. rewrite EGY in *. rewrite <- EGT in HDM3.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HX4) as HVX4. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HY4) as HVY4.
    pose proof (opnd_ok x bs4 WFS4 HVX4) as (LMX & TDX & DMX). pose proof (opnd_ok y bs4 WFS4 HVY4) as (LMY & TDY & DMY).
    rewrite EGX in LMX, TDX, DMX. rewrite EGY in LMY, TDY, DMY.
    pose proof OKT as (LMT & _).
    assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
    assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
    assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
    assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
    fold la in HLX. fold lb in HLY.
    set (br := getbn rr bs4) in *. set (tb := getbn t bs4) in *.
    assert (HD2 : (2 * j <= bn_dmax br)%nat) by (clear - HDM4; lia).
    assert (HSC : (scratch_rec kj <= length (bn_buf tb))%nat).
    { pose proof (scratch_rec_le kj) as H. fold j in H. unfold bn_dmax in HDM3. clear - H HDM3. lia. }
    pose proof OKR as (LBR & _).
    assert (LRl : length (firstn (2 * j) (bn_buf br)) = (2 * j)%nat) by (apply firstn_length_le; unfold bn_dmax in HD2; exact HD2).
    pose proof (mul_recursive_spec kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf br)) (bn_buf tb) HLla HLlb
                  ltac:(apply limbs_firstn; exact LBR) LMT ltac:(lia) HDA HDB ltac:(rewrite LLA; clear - HALJ; lia) ltac:(rewrite LLB; clear - HBLJ; lia) LRl HSC) as MP.
    rewrite EMR in MP. destruct MP as (LRO & NRO' & _ & LTO & NTO).
    replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    eapply evt_mono.
    { eapply (mulc_rec sp gp (wz RATP) F fc m4 lo R X Y Dr Dx Dy 9216 br la lb) with (CS8 := kara_uleaf HxComba8U.CS8) (k := kj) (da := (j - al)%nat) (db := (j - bl)%nat)
        (TT := TT) (Dt := Dt) (Tl := bn_buf tb).
      - unfold mulc_pre. rewrite LLA, LLB.
        split; [exact HLla|]. split; [exact HLlb|]. split; [exact (bg_okm _ OKR)|].
        split; [clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
        split; [clear - R0 RC X0 XC Y0 YC DR0 DRC DX0 DXC DY0 DYC CEIL LO' SPR TDX TDY EAL EBL B63 SPB; unfold bn_dmax in *; lia|].
        split; [exact S1|]. split; [clear - S2 TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - S3 TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - DRX TDX EAL; unfold bn_dmax in *; lia | clear - DRY TDY EBL; unfold bn_dmax in *; lia].
      - unfold mulc_upre.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st4 OW4 LB m4 bs4 PL EA rr R HEAP4 PARTS4 HR4 NRO))|].
        split; [intros _; apply (bn_arr_ualign st4 OW4 LB m4 bs4 PL EA rr Dr br HEAP4 PARTS4 ARR); clear - HDM4 PJ; lia|].
        split; [intros _; eapply (bn_arr_ualign st4 OW4 LB m4 bs4 PL EA x Dx _ HEAP4 PARTS4 ARRX);
                  first [clear - TDX EAL HALJ HDA PJ; unfold bn_dmax in *; lia | clear - TDX EAL HALJ PJ; unfold bn_dmax in *; lia]
               | intros _; eapply (bn_arr_ualign st4 OW4 LB m4 bs4 PL EA y Dy _ HEAP4 PARTS4 ARRY);
                  first [clear - TDY EBL HBLJ HDB PJ; unfold bn_dmax in *; lia | clear - TDY EBL HBLJ PJ; unfold bn_dmax in *; lia]].
      - unfold mulc_mem. split; [exact SR|]. split; [exact UR|]. split; [exact (proj1 HXd)|]. split; [exact (proj1 HYd)|].
        split; [exact HLX|]. split; [exact HLY|]. split; [exact ST4 | exact MI4].
      - apply bn_mul_recursive_closed.
      - unfold rec_ustack, kara_uleaf, HxComba8U.CS8. clear - HKJ. lia.
      - unfold mulc_tpre. rewrite LLA, LLB.
        split; [exact LMT|]. split; [apply (BnAKit.d_cell m4 TT Dt _ STT)|].
        split; [apply limbs_at_of_u64arr; exact UT|].
        split; [apply (limbarr_limbs_at bgusegs) in UT; exact (proj2 UT)|].
        split; [clear - DT0 DTC CEIL; unfold bn_dmax in *; lia|]. split; [clear - S4; unfold bn_dmax in *; lia|].
        split; [clear - DTX TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - DTY TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - DRT; unfold bn_dmax in *; lia|].
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st4 OW4 LB m4 bs4 PL EA t TT HEAP4 PARTS4 HT4 NROT))|].
        intros _; apply (bn_arr_ualign st4 OW4 LB m4 bs4 PL EA t Dt tb HEAP4 PARTS4 ARRT). clear - HDM3 PJ. unfold bn_dmax in *. lia.
      - exact HKJ' .
      - exact HDA.
      - exact HDB.
      - rewrite LLA. clear - HALJ. lia.
      - rewrite LLB. clear - HBLJ. lia.
      - exact HD2.
      - exact HSC. }
    intros ms' PO. rewrite EMR in PO. cbn [fst snd] in PO. rewrite LLA, LLB in PO.
    eapply (mul_finish2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb st4 bs4 m4 OW4 rr t x y R TT X Y ac Dr Dt
              (8 * Z.of_nat (2 * j)) 9216 ro to (al + bl)%nat) in PO;
      [ | exact ENV4 | exact LS4 | exact CEIL | exact GLO' | lia | clear - LO'; lia | exact SPB | exact B63 | exact FROK | exact HR4 | exact HP | exact HT4 | exact HPT | exact HX4 | exact HY4
        | exact NEX | exact NEY | exact NTR | exact NTX | exact NTY | exact SR | exact ARR | exact STT | exact ARRT
        | exact LRO | | | | exact LTO | | ].
    - rewrite EGX, EGY in PO. fold br tb in PO. unfold mul_res in PO. exact PO.
    - rewrite NRO', LRl. fold br. clear - HD2 PJ. lia.
    - fold br. clear - HDM4 HALJ HBLJ. lia.
    - rewrite NRO', LRl. reflexivity.
    - rewrite NTO. reflexivity.
    - fold tb. clear - HDM3 PJ. lia.
  Qed.

  Lemma mul_path_part : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st2 : PState) (bs2 : bstate bptr) (m2 : mem) (OW2 : list block) (rr t x y : bnref) (R TT X Y ac : Z) (al bl kj : nat)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st2 bs2 m2 OW2 ->
    lib_state bs2 m2 OW2 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs2 OW2 PL rr R -> hpl PL rr -> ref_at bs2 OW2 PL t TT -> hpl PL t -> ref_at bs2 OW2 PL x X -> x <> ROne -> ref_at bs2 OW2 PL y Y -> y <> ROne ->
    rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
    al = bn_top (getbn x bs2) -> bl = bn_top (getbn y bs2) ->
    (3 <= kj <= 23)%nat -> (Nat.pow 2 kj <= al)%nat -> (Nat.pow 2 kj <= bl)%nat -> (al < 2 * Nat.pow 2 kj)%nat -> (bl < 2 * Nat.pow 2 kj)%nat ->
    (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
    implM bgusegs (interp (embed (disp_part rr t (firstn al (bn_buf (getbn x bs2))) (firstn bl (bn_buf (getbn y bs2))) al bl (al + bl) kj bs2))) st2
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac
                (bn_neg (getbn x bs2)) (bn_neg (getbn y bs2)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
               (Z_to_bv 64 (Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kj))) (Z_to_bv 64 TT) (Z_to_bv 64 (2 * Z.of_nat (Nat.pow 2 kj))) t3 t4 t5 t6)
          F (Z_to_bv 64 0x1028e0) fc None m2 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HT HPT HX NX HY NY NEX NEY NTR NTX NTY EAL EBL HKJ HALJ HBLJ HAL2 HBL2 HD1 HD2'.
    pose proof (proj1 HP) as NRO. pose proof (proj1 HPT) as NROT.
    pose proof LO as LO'. unfold BN_MUL_FIXED_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS2; pose proof PARTS2 as (WFS2 & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
    pose proof (st_wf_ok t bs2 WFS2 HVT NROT) as (_ & TDT2 & _).
    assert (PJ : 2 <= Z.of_nat (Nat.pow 2 kj) <= 8388608).
    { rewrite Nat2Z.inj_pow. change (Z.of_nat 2) with 2. split.
      - change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia.
      - change 8388608 with (2 ^ 23). apply Z.pow_le_mono_r; lia. }
    set (j := Nat.pow 2 kj) in *.
    assert (EJ : Z.of_nat j = 2 ^ Z.of_nat kj) by (subst j; rewrite Nat2Z.inj_pow; reflexivity).
    assert (HKJ' : (kj <= 26)%nat) by (clear - HKJ; lia).
    unfold implM. iprefix. zstep.
    setreg 10%Z (Z_to_bv 64 0)
      ltac:(f_equal; rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; clear - PJ; lia);
            rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_small by (change (2 ^ 29) with 536870912; clear - PJ; lia); reflexivity).
    chk_lit.
    zstep.
    setreg 27%Z (Z_to_bv 64 (Z.of_nat (8 * j)))
      ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; rewrite bn_swrap32_small by (clear - PJ; lia); clear; lia).
    do 2 zstep.

    destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO'; lia)) as (errv1 & PRE1).
    zstep.
    ihere. to_implM. unfold disp_part. unfold bbind at 1. cbn [bind tree_ops]. fold j.
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 t (8 * j) bs2 HVT TDT2)|].
      eapply (bn_wexpand_walk HM HF) with (r := t) (a := TT) (words := (8 * j)%nat);
        [exact PRE1 | reflexivity | exact HT | exact (hpl_wref PL t HPT) | reflexivity | reflexivity | clear - PJ; lia]. }
    cbv beta. intros [u3 bs3] st3 ms3 [PO LEAF3]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP3 & (_ & -> & HDM3 & WRES3 & BST3)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP3) as (ENV3 & LS3). pose proof KP3 as RS3; apply kpost_refs in RS3.
    cbn [fst snd] in *. clear PRE1 KP3 ENV LS.
    replace (ret_pc (Z_to_bv 64 1059064)) with (Z_to_bv 64 1059064) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HR) as HR3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HT) as HT3.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HX) as HX3. pose proof (ref_at_stable _ _ _ _ PL _ _ RS3 HY) as HY3.
    destruct LEAF3 as (LOTH3 & _).

    pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as PARTS3; pose proof PARTS3 as (WFS3 & _).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV3) PARTS3 HT3 HPT) as (TA0 & TAC & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KT; zify_cond KT; [exfalso; clear - KT TA0 TAC CEIL LO' SPR; lia|]. clear KT.
    do 2 zstep.

    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS3 HR3) as HVR3.
    pose proof (st_wf_ok rr bs3 WFS3 HVR3 NRO) as (_ & TDR3 & _).
    destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV3 LS3 ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO'; lia)) as (errv3 & PRE3).
    zstep.
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops fst snd].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves2 rr (8 * j) bs3 HVR3 TDR3)|].
      eapply (bn_wexpand_walk HM HF) with (r := rr) (a := R) (words := (8 * j)%nat);
        [exact PRE3 | reflexivity | exact HR3 | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | clear - PJ; lia]. }
    cbv beta. intros [u4 bs4] st4 ms4 [PO LEAF4]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP4 & (_ & -> & HDM4 & WRES4 & BST4)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP4) as (ENV4 & LS4). pose proof KP4 as RS4; apply kpost_refs in RS4.
    cbn [fst snd] in *. clear PRE3 KP4 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1059080)) with (Z_to_bv 64 1059080) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HR3) as HR4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HT3) as HT4.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HX3) as HX4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HY3) as HY4.
    destruct LEAF4 as (LOTH4 & _).
    assert (EGX : getbn x bs4 = getbn x bs2) by (rewrite (LOTH4 x NEX); apply LOTH3; exact NTX).
    assert (EGY : getbn y bs4 = getbn y bs2) by (rewrite (LOTH4 y NEY); apply LOTH3; exact NTY).
    assert (EGT : getbn t bs4 = getbn t bs3) by (apply LOTH4; congruence).
    clear HVR3 TDR3 PARTS3 WFS3 WRES3 WRES4 BST3 BST4.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    set (la := firstn al (bn_buf (getbn x bs2))). set (lb := firstn bl (bn_buf (getbn y bs2))).
    destruct (mul_part_recursive kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf (getbn rr bs4))) (bn_buf (getbn t bs4))) as [ro to] eqn:EMR.
    cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.

    pose proof ENV4 as (HEAP4 & _ & ST4 & _ & MI4 & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4; pose proof PARTS4 as (WFS4 & _).
    destruct (open_full st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B rr R HEAP4 LS4 FROK HR4 HP) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (open_full st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B t TT HEAP4 LS4 FROK HT4 HPT) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
    destruct (operand_view_ne st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B rr R Dr x X al HEAP4 LS4 FROK HR4 HP SR ARR HX4 NX ltac:(rewrite EGX; clear - EAL; lia) ltac:(congruence))
      as (Dx & HXd & HLX & UX & ARRX & X0 & XC & DX0 & DXC & _ & S2 & _ & DRX).
    destruct (operand_view_ne st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B rr R Dr y Y bl HEAP4 LS4 FROK HR4 HP SR ARR HY4 NY ltac:(rewrite EGY; clear - EBL; lia) ltac:(congruence))
      as (Dy & HYd & HLY & UY & ARRY & Y0 & YC & DY0 & DYC & _ & S3 & _ & DRY).
    pose proof (bn_arrs_disj st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B t x TT X Dt Dx HEAP4 LS4 FROK NTX HT4 HX4 NROT NX ARRT ARRX) as DTX.
    pose proof (bn_arrs_disj st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B t y TT Y Dt Dy HEAP4 LS4 FROK NTY HT4 HY4 NROT NY ARRT ARRY) as DTY.
    pose proof (bn_arrs_disj st4 OW4 LB m4 bs4 PL EA (bv_unsigned sp) B rr t R TT Dr Dt HEAP4 LS4 FROK ltac:(congruence) HR4 HT4 NRO NROT ARR ARRT) as DRT.
    pose proof (DSEPR rr R HR4) as S1. pose proof (DSEPT rr R HR4) as S4.
    clear DSEPR DSEPT.
    rewrite EGX in *. rewrite EGY in *. rewrite <- EGT in HDM3.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HX4) as HVX4. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HY4) as HVY4.
    pose proof (opnd_ok x bs4 WFS4 HVX4) as (LMX & TDX & DMX). pose proof (opnd_ok y bs4 WFS4 HVY4) as (LMY & TDY & DMY).
    rewrite EGX in LMX, TDX, DMX. rewrite EGY in LMY, TDY, DMY.
    pose proof OKT as (LMT & _).
    assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
    assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
    assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
    assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
    fold la in HLX. fold lb in HLY.
    set (br := getbn rr bs4) in *. set (tb := getbn t bs4) in *.
    assert (HD2 : (4 * j <= bn_dmax br)%nat) by (clear - HDM4; lia).
    assert (HSC : (8 * j <= length (bn_buf tb))%nat) by (unfold bn_dmax in HDM3; exact HDM3).
    pose proof OKR as (LBR & _).
    assert (LRl : length (firstn (4 * j) (bn_buf br)) = (4 * j)%nat) by (apply firstn_length_le; unfold bn_dmax in HD2; exact HD2).
    pose proof (mul_part_recursive_spec kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf br)) (bn_buf tb) HLla HLlb
                  ltac:(apply limbs_firstn; exact LBR) LMT ltac:(lia) ltac:(lia) ltac:(clear - HAL2 HALJ; lia) ltac:(clear - HBL2 HBLJ; lia)
                  ltac:(clear - HD1 HD2' HALJ HBLJ; lia) ltac:(clear - HD1 HD2' HALJ HBLJ; lia)
                  ltac:(rewrite LLA; clear - HALJ; lia) ltac:(rewrite LLB; clear - HBLJ; lia) LRl HSC) as MP.
    rewrite EMR in MP. destruct MP as (LRO & NRO' & _ & LTO & NTO).
    replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    eapply evt_mono.
    { eapply (mulc_part sp gp (wz RATP) F fc m4 lo R X Y Dr Dx Dy 9216 br la lb) with (CS8 := kara_uleaf HxComba8U.CS8) (fuel := kj) (k := kj) (tna := (al - j)%nat) (tnb := (bl - j)%nat)
        (TT := TT) (Dt := Dt) (Tl := bn_buf tb).
      - unfold mulc_pre. rewrite LLA, LLB.
        split; [exact HLla|]. split; [exact HLlb|]. split; [exact (bg_okm _ OKR)|].
        split; [clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
        split; [clear - R0 RC X0 XC Y0 YC DR0 DRC DX0 DXC DY0 DYC CEIL LO' SPR TDX TDY EAL EBL B63 SPB; unfold bn_dmax in *; lia|].
        split; [exact S1|]. split; [clear - S2 TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - S3 TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - DRX TDX EAL; unfold bn_dmax in *; lia | clear - DRY TDY EBL; unfold bn_dmax in *; lia].
      - unfold mulc_upre.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st4 OW4 LB m4 bs4 PL EA rr R HEAP4 PARTS4 HR4 NRO))|].
        split; [intros _; apply (bn_arr_ualign st4 OW4 LB m4 bs4 PL EA rr Dr br HEAP4 PARTS4 ARR); clear - HDM4 PJ; lia|].
        split; [intros _; eapply (bn_arr_ualign st4 OW4 LB m4 bs4 PL EA x Dx _ HEAP4 PARTS4 ARRX);
                  first [clear - TDX EAL HALJ HDA PJ; unfold bn_dmax in *; lia | clear - TDX EAL HALJ PJ; unfold bn_dmax in *; lia]
               | intros _; eapply (bn_arr_ualign st4 OW4 LB m4 bs4 PL EA y Dy _ HEAP4 PARTS4 ARRY);
                  first [clear - TDY EBL HBLJ HDB PJ; unfold bn_dmax in *; lia | clear - TDY EBL HBLJ PJ; unfold bn_dmax in *; lia]].
      - unfold mulc_mem. split; [exact SR|]. split; [exact UR|]. split; [exact (proj1 HXd)|]. split; [exact (proj1 HYd)|].
        split; [exact HLX|]. split; [exact HLY|]. split; [exact ST4 | exact MI4].
      - apply bn_mul_part_recursive_closed.
      - unfold part_ustack, rec_ustack, kara_uleaf, HxComba8U.CS8. clear - HKJ. lia.
      - unfold mulc_tpre. rewrite LLA, LLB.
        split; [exact LMT|]. split; [apply (BnAKit.d_cell m4 TT Dt _ STT)|].
        split; [apply limbs_at_of_u64arr; exact UT|].
        split; [apply (limbarr_limbs_at bgusegs) in UT; exact (proj2 UT)|].
        split; [clear - DT0 DTC CEIL; unfold bn_dmax in *; lia|]. split; [clear - S4; unfold bn_dmax in *; lia|].
        split; [clear - DTX TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - DTY TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - DRT; unfold bn_dmax in *; lia|].
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st4 OW4 LB m4 bs4 PL EA t TT HEAP4 PARTS4 HT4 NROT))|].
        intros _; apply (bn_arr_ualign st4 OW4 LB m4 bs4 PL EA t Dt tb HEAP4 PARTS4 ARRT). clear - HDM3 PJ. unfold bn_dmax in *. lia.
      - clear - HKJ; lia.
      - lia.
      - exact HKJ'.
      - clear - HAL2 HALJ; lia.
      - clear - HBL2 HBLJ; lia.
      - clear - HD1 HD2' HALJ HBLJ; lia.
      - clear - HD1 HD2' HALJ HBLJ; lia.
      - rewrite LLA. clear - HALJ. lia.
      - rewrite LLB. clear - HBLJ. lia.
      - exact HD2.
      - exact HSC. }
    intros ms' PO. rewrite EMR in PO. cbn [fst snd] in PO. rewrite LLA, LLB in PO.
    eapply (mul_finish2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb st4 bs4 m4 OW4 rr t x y R TT X Y ac Dr Dt
              (8 * Z.of_nat (4 * j)) 9216 ro to (al + bl)%nat) in PO;
      [ | exact ENV4 | exact LS4 | exact CEIL | exact GLO' | lia | clear - LO'; lia | exact SPB | exact B63 | exact FROK | exact HR4 | exact HP | exact HT4 | exact HPT | exact HX4 | exact HY4
        | exact NEX | exact NEY | exact NTR | exact NTX | exact NTY | exact SR | exact ARR | exact STT | exact ARRT
        | exact LRO | | | | exact LTO | | ].
    - rewrite EGX, EGY in PO. fold br tb in PO. unfold mul_res in PO. exact PO.
    - rewrite NRO', LRl. fold br. clear - HD2 PJ. lia.
    - fold br. clear - HDM4 HAL2 HBL2. lia.
    - rewrite NRO', LRl. reflexivity.
    - rewrite NTO. reflexivity.
    - fold tb. clear - HDM3 PJ. lia.
  Qed.

  Lemma mul_path_kara : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (st1 : PState) (bs1 : bstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y ac : Z) (qc : bptr) (al bl : nat)
      (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x25 x26 x27 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st1 bs1 m1 OW1 ->
    lib_state bs1 m1 OW1 PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs1 OW1 PL rr R -> hpl PL rr -> ref_at bs1 OW1 PL x X -> x <> ROne -> ref_at bs1 OW1 PL y Y -> y <> ROne -> rr <> x -> rr <> y ->
    (rr < NFIX + gx_used (st_ctx bs1))%nat -> (x < NFIX + gx_used (st_ctx bs1))%nat -> (y < NFIX + gx_used (st_ctx bs1))%nat ->
    pl_ctx PL = Some (ac, qc) ->
    al = bn_top (getbn x bs1) -> bl = bn_top (getbn y bs1) ->
    (16 <= al)%nat -> (16 <= bl)%nat -> (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
    implM bgusegs (interp (embed (disp_kara rr (firstn al (bn_buf (getbn x bs1))) (firstn bl (bn_buf (getbn y bs1))) al bl (al + bl)
                                  (Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1)) bs1))) st1
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac
                (bn_neg (getbn x bs1)) (bn_neg (getbn y bs1)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 ac) a0 (Z_to_bv 64 (Z.of_nat al - Z.of_nat bl))
               a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
               (Z_to_bv 64 (Z.of_nat bl)) x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1027f4) fc None m1 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP HX NX HY NY NEX NEY LVR LVX LVY HPC EAL EBL HA16 HB16 HAB HBA.
    pose proof (proj1 HP) as NRO.
    pose proof LO as LO'. unfold BN_MUL_FIXED_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS1; pose proof PARTS1 as (WFS1 & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
    pose proof (opnd_ok x bs1 WFS1 HVX) as (_ & TDX & DMX). pose proof (opnd_ok y bs1 WFS1 HVY) as (_ & TDY & DMY).
    assert (AL23 : Z.of_nat al < 8388608) by (clear - EAL TDX DMX; unfold bn_dmax in *; lia).
    assert (BL23 : Z.of_nat bl < 8388608) by (clear - EBL TDY DMY; unfold bn_dmax in *; lia).
    pose proof (kara_kj_facts al bl HA16 HB16 HAB HBA AL23 BL23) as KF. cbv zeta in KF.
    set (mx := Nat.max al bl) in *. set (kj := Z.to_nat (num_bits_word (Z.of_nat mx) - 1)) in *. destruct KF as (HKJ & HJ1 & HJ2 & EKJ).
    set (j := Nat.pow 2 kj) in *.
    assert (EJ : Z.of_nat j = 2 ^ Z.of_nat kj) by (subst j; rewrite Nat2Z.inj_pow; reflexivity).
    assert (PJ : Z.of_nat j <= 8388608) by (clear - HJ1 AL23 BL23; subst mx; lia).

    assert (CONT : forall w, w = Z_to_bv 64 (Z.of_nat mx) ->
      implM bgusegs (interp (embed (disp_kara rr (firstn al (bn_buf (getbn x bs1))) (firstn bl (bn_buf (getbn y bs1))) al bl (al + bl) kj bs1))) st1
        (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr x y R X Y ac
                  (bn_neg (getbn x bs1)) (bn_neg (getbn y bs1)))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 ac) w (Z_to_bv 64 (Z.of_nat al - Z.of_nat bl))
                 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
                 (Z_to_bv 64 (Z.of_nat bl)) x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x102800) fc None m1 (seg_rom bgusegs))).
    2:{ unfold implM. iprefix. zstep. zstep. rewrite lts_signed by (clear - AL23 BL23; lia). if_cases KI; zify_cond KI.
        - ihere. to_implM. apply CONT. f_equal. subst mx. clear - KI. lia.
        - zstep. ihere. to_implM. apply CONT. f_equal. subst mx. clear - KI. lia. }
    intros w ->.
    pose proof ENV as (HEAP1 & _ & ST1 & (errv1 & ERR1) & MI1 & _ & _ & _ & _ & FR1 & FSZ1).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    unfold implM. iprefix. zstep.

    eapply evt_cut.
    { eapply (BN_num_bits_word_uspec (Z_to_bv 64 1058820) (Z_to_bv 64 (bv_unsigned sp + -112))) with (lo := lo);
        [rewrite ESP; exact ST1 | rewrite ESP; clear - LO'; lia | exact MI1]. }
    intros ms' (n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & n8 & n9 & n10 & n11 & n12 & n13 & mN & -> & MUn & WMn & MIn & STn).
    rewrite ESP in MUn, STn. rewrite (unsigned_lit (Z.of_nat mx)) by (clear - AL23 BL23; subst mx; lia).
    replace (ret_pc (Z_to_bv 64 1058820)) with (Z_to_bv 64 1058820) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (HWLn : Forall (w_lib bs1 OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112)]) by (constructor; [left; cbn [fst snd]; clear - LO'; lia | constructor]).
    assert (WOKn : Forall (w_ok OW1 LB bs1 PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112)]) by (constructor; [apply w_stack; cbn; clear - LO' CEIL; lia | constructor]).
    pose proof (lib_state_frame st1 LB _ _ [] bs1 m1 mN OW1 PL EA _ HEAP1 LS MUn WMn FROK WOKn) as LSn.
    assert (ENVn : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st1 bs1 mN OW1).
    { eapply (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (errv' := errv1);
        [exact ENV | exact PARTS1 | exact MUn | exact WMn | exact HWLn | exact STn | | exact MIn | | exact FSZ1].
      - eapply rw_cells_transport; [exact ERR1 | exact MUn | exact WMn |]. unfold LX_ERRNO, RATP. cbn. clear - GLO LO'. lia.
      - eapply rw_cells_transport; [exact FR1 | exact MUn | exact WMn |]. cbn. clear. lia. }
    clear HEAP1 ST1 ERR1 MI1 FR1 ENV LS MUn WMn STn MIn HWLn WOKn.
    zstep.
    replace (num_bits_word (Z.of_nat mx)) with (Z.of_nat kj + 1) by (clear - EKJ; lia).
    rewrite (bn_swrap32_small (Z.of_nat kj + 1 + -1)) by (clear - HKJ; lia).
    replace (Z.of_nat kj + 1 + -1) with (Z.of_nat kj) by (clear; lia).
    zstep. rewrite lts_small by (clear - HKJ; lia). if_cases C; [exfalso; zify_cond C; clear - C; lia | clear C].
    zstep.
    chk ltac:(fun C => clear - C HKJ; lia).
    do 2 zstep.
    rewrite (sllw_small 1 (Z.of_nat kj)) by (clear - HKJ PJ EJ; lia).
    setreg 25%Z (Z_to_bv 64 (Z.of_nat j)) ltac:(f_equal; clear - EJ; lia).
    do 2 zstep.
    rewrite (bn_swrap32_small (Z.of_nat j + Z.of_nat j)) by (clear - PJ; lia).
    chk ltac:(fun C => clear - C; lia).
    setreg 27%Z (Z_to_bv 64 (2 * Z.of_nat j)) ltac:(f_equal; clear; lia).
    zstep.

    pose proof (st_wf_get_pre bs1 WFS1) as (GP1 & GP2 & GP3).
    destruct (KPRE _ _ _ _ _ BN_CTX_GET_STACK ENVn LSn ltac:(unfold BN_CTX_GET_STACK; clear - LO'; lia)) as (errv2 & PRE2).
    zstep.
    ihere. to_implM. unfold disp_kara. unfold bbind at 1. cbn [bind tree_ops]. fold j.
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (BN_CTX_get_leaves bs1 GP1 GP2)|].
      first [eapply (BN_CTX_get_walk HM HF) | eapply (BN_CTX_get_walk HM)]; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [t bs2] st2 ms2 [PO LEAF]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP2 & (_ & (ti & Et) & (TT & HT & ->) & INCL2)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENVn KP2) as (ENV2 & LS2). pose proof KP2 as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE2 KP2 ENVn LSn.
    replace (ret_pc (Z_to_bv 64 1058864)) with (Z_to_bv 64 1058864) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HR) as HR2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HX) as HX2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HY) as HY2.
    destruct LEAF as (ET & _ & _ & LOTH & _). cbn [fst snd] in ET, LOTH.
    assert (ETU : t = RPool (gx_used (st_ctx bs1))) by (rewrite ET, GP3; reflexivity).
    assert (NTR : t <> rr) by (rewrite ETU; clear - LVR; unfold RPool; lia).
    assert (NTX : t <> x) by (rewrite ETU; clear - LVX; unfold RPool; lia).
    assert (NTY : t <> y) by (rewrite ETU; clear - LVY; unfold RPool; lia).
    assert (HPT : hpl PL t) by (rewrite Et; apply hpl_pool).
    assert (EGX : getbn x bs2 = getbn x bs1) by (apply LOTH; rewrite <- ET; congruence).
    assert (EGY : getbn y bs2 = getbn y bs1) by (apply LOTH; rewrite <- ET; congruence).

    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENV2) PARTS2 HT HPT) as (TA0 & TAC & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KT; zify_cond KT; [exfalso; clear - KT TA0 TAC CEIL LO' SPR; lia|]. clear KT.
    zstep.
    assert (EAL2 : al = bn_top (getbn x bs2)) by (rewrite EGX; exact EAL).
    assert (EBL2 : bl = bn_top (getbn y bs2)) by (rewrite EGY; exact EBL).
    rewrite <- EGX, <- EGY.
    zstep. if_cases KA; zify_cond KA.
    {
      replace ((j <? al)%nat || (j <? bl)%nat) with true by (symmetry; apply orb_true_iff; left; apply Nat.ltb_lt; clear - KA; lia).
      ihere. to_implM.
      eapply mul_path_part; try eassumption; [clear - HKJ; lia | clear - KA; lia | subst mx; clear - KA HAB HBA; lia | subst mx; clear - HJ2; lia | subst mx; clear - HJ2; lia]. }
    zstep. if_cases KB'; zify_cond KB'.
    {
      replace ((j <? al)%nat || (j <? bl)%nat) with true by (symmetry; apply orb_true_iff; right; apply Nat.ltb_lt; clear - KB'; lia).
      ihere. to_implM.
      eapply mul_path_part; try eassumption; [clear - HKJ; lia | subst mx; clear - KB' HAB HBA; lia | clear - KB'; lia | subst mx; clear - HJ2; lia | subst mx; clear - HJ2; lia]. }

    replace ((j <? al)%nat || (j <? bl)%nat) with false by (symmetry; apply orb_false_iff; split; apply Nat.ltb_ge; [clear - KA | clear - KB']; lia).
    ihere. to_implM.
    eapply mul_path_rec; try eassumption; [clear - HKJ; lia | clear - KA; lia | clear - KB'; lia | subst mx; clear - HJ1 KA KB' HAB HBA; lia | subst mx; clear - HJ1 KA KB' HAB HBA; lia].
  Qed.

  Lemma mul_zero_path : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (jb : list byte) (m1 : mem) (rr : bnref) (R : Z)
      (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) s bs m1 OW ->
    lib_state bs m1 OW PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B -> B < 2^63 -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs OW PL rr R -> hpl PL rr ->
    evt bgusegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1)
                       (tt, setbn rr (bn_zero_pure (getbn rr bs)) bs) s)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1027cc) fc None m1 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB B63 FROK HR HP.
    pose proof LO as LO'. unfold BN_MUL_FIXED_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    unfold MallocRep.wz.
    zstep. zstep.
    eapply (zero_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
      [clear - LO'; lia | reflexivity | exact ENV | exact LS | exact HR | exact (hpl_wref PL rr HP) |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1058772)) with (Z_to_bv 64 1058772) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m _ _ _ _ _ ENV3) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    unfold mul_frame in FRF.
    do 3 zstep. do 13 zstep.
    release_frame FRF STF (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold bn_post. do 15 eexists. exists m3, OW, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS3|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
  Qed.

  Lemma bn_mul_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_MUL_FIXED_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> hpl PL rr -> ry <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz ac ->
    implM bgusegs (interp (embed (bn_mul_fixed_top (tree_ops bptr) rr rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_FIXED_TOP) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros PRE -> HR HX HY HP NY HPC -> -> -> ->. pose proof (proj1 HP) as NRO.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof LO as LO'. unfold BN_MUL_FIXED_STACK in LO'.
    unfold BN_MUL_FIXED_TOP, MallocRep.wz.

    unfold bn_mul_fixed_top. rewrite bn_live_run.
    destruct (live_refs (st_ctx bs) [rr; rx; ry]) eqn:LIVE; [| cbn [embed interp]; apply implM_interp_unr]. apply live_refs_true_iff in LIVE.
    pose proof (Forall_inv LIVE) as LVR. pose proof (Forall_inv (Forall_inv_tail LIVE)) as LVX.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail LIVE))) as LVY. clear LIVE.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
    destruct (open_ro_any s OW LB m bs PL EA rx ax HEAP LS HX) as (Dx0 & SX).
    destruct (open_ro_any s OW LB m bs PL EA ry ay HEAP LS HY) as (Dy0 & SY).
    pose proof (ref_at_rng _ _ _ _ _ _ _ _ _ _ _ HEAP LS FROK HX) as (X0 & XC).
    pose proof (ref_at_rng _ _ _ _ _ _ _ _ _ _ _ HEAP LS FROK HY) as (Y0 & YC).
    pose proof (ref_at_ualign_any s OW LB m bs PL EA rx ax HEAP LS HX) as ALX0. pose proof (ref_at_ualign_any s OW LB m bs PL EA ry ay HEAP LS HY) as ALY0.
    pose proof (opnd_ok rx bs WFS HVX) as (_ & TDX & DMX). pose proof (opnd_ok ry bs WFS HVY) as (_ & TDY & DMY).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & SAI & _).
    assert (ArR : 0 < ar < 2^64) by (clear - SA0 SAC CEIL LO' SPR; lia).
    assert (AxR : 0 < ax < 2^64) by (clear - X0 XC CEIL LO' SPR B63 SPB; lia).
    assert (AyR : 0 < ay < 2^64) by (clear - Y0 YC CEIL LO' SPR B63 SPB; lia).
    unfold bn_cells, MallocRep.wz in SX, SY.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    unfold bbind at 1 2. unfold bget at 1 2. cbn [bind ret tree_ops tbind fst snd].
    set (al := bn_top (getbn rx bs)) in *. set (bl := bn_top (getbn ry bs)) in *.
    assert (AL23 : Z.of_nat al < 8388608) by (clear - TDX DMX; unfold bn_dmax in *; lia).
    assert (BL23 : Z.of_nat bl < 8388608) by (clear - TDY DMY; unfold bn_dmax in *; lia).
    unfold implM. iprefix.
    carve_frame 112%nat ST. do 15 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL0 : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 112, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 112, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK0) as LS0.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jbv :: _) =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (mul_frame jbv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) s bs m1 OW);
      [| set (jb := jbv) in * ]
    end.
    { unfold kenv, mul_frame. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL0 SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (LOF : lo <= bv_unsigned sp - BN_MUL_FIXED_STACK) by (unfold BN_MUL_FIXED_STACK; lia).
    chk ltac:(fun C => clear - C X0 XC AxR; lia).
    do 3 zstep. rewrite (land7 ax ALX0). chk_lit.
    zstep.
    chk ltac:(fun C => clear - C Y0 YC AyR; lia).
    zstep. rewrite (land7 ay ALY0). chk_lit.
    zstep. rewrite (sx32_small (Z.of_nat al)) by (clear - AL23; lia).
    zstep. if_cases KA0; zify_cond KA0.
    {
      replace ((al =? 0)%nat || (bl =? 0)%nat) with true by (symmetry; apply orb_true_iff; left; apply Nat.eqb_eq; clear - KA0; lia).
      ihere. to_implM. unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
      eapply mul_zero_path; [exact ENV | exact LS0 | exact CEIL | exact GLO' | exact LOF | exact SPB | exact B63 | exact FROK | exact HR | exact HP]. }
    zstep. rewrite (sx32_small (Z.of_nat bl)) by (clear - BL23; lia).
    zstep. if_cases KB0; zify_cond KB0.
    {
      replace ((al =? 0)%nat || (bl =? 0)%nat) with true by (symmetry; apply orb_true_iff; right; apply Nat.eqb_eq; clear - KB0; lia).
      ihere. to_implM. unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
      eapply mul_zero_path; [exact ENV | exact LS0 | exact CEIL | exact GLO' | exact LOF | exact SPB | exact B63 | exact FROK | exact HR | exact HP]. }
    replace ((al =? 0)%nat || (bl =? 0)%nat) with false by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; [clear - KA0 | clear - KB0]; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat al + Z.of_nat bl)) by (clear - AL23 BL23; lia).
    zstep.
    chk ltac:(fun C => clear - C; lia).
    do 2 zstep.

    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPK.
    destruct (KPRE _ _ _ _ _ BN_CTX_START_STACK ENV LS0 ltac:(unfold BN_CTX_START_STACK; clear - LO'; lia)) as (errv1 & PRE1).
    zstep.
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply BnLeaves.implM_embed_leaves; [apply (BN_CTX_start_leaves bs)|].
      first [eapply (BN_CTX_start_walk HM HF) | eapply (BN_CTX_start_walk HM)]; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 [PO LEAF1]. apply BPK in PO; [|intros v9 b9 o9 p9 a9 [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW1 & -> & KP1 & (_ & INCL1)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP1) as (ENV1 & LS1). pose proof KP1 as RS1; apply kpost_refs in RS1.
    cbn [fst snd] in *. clear PRE1 KP1 ENV LS0 SX SY.
    replace (ret_pc (Z_to_bv 64 1058656)) with (Z_to_bv 64 1058656) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HR) as HR1. pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HX) as HX1. pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HY) as HY1.
    destruct LEAF1 as (LB1 & LP1 & LU1 & LI1).
    assert (EG1 : forall r, getbn r bs1 = getbn r bs) by (intros r; unfold getbn; rewrite LB1; reflexivity).

    cbn [fst snd]. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind with (Q1 := mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr rx ry ar ax ay ac
                                            (bn_neg (getbn rx bs)) (bn_neg (getbn ry bs))).
    2:{ cbv beta. intros [uE bsE] stE msE J. cbn [fst snd].
        unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
        eapply (mul_end ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B jb rr rx ry ar ax ay ac qc
                  (bn_neg (getbn rx bs)) (bn_neg (getbn ry bs)) (uE, bsE) stE msE CEIL GLO' LOF SPB B63 FROK HP HPC J). }

    pose proof ENV1 as (HEAP1 & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as PARTS1.
    unfold implM. iprefix.
    zstep. if_cases KRX; rewrite ?unsigned_lit in KRX by (clear - ArR AxR; lia); zify_cond KRX.
    { assert (E : rr = rx).
      { destruct (Nat.eq_dec rr rx) as [E|NE]; [exact E|exfalso].
        pose proof (struct_disj st1 OW1 LB m2 HEAP1 bs1 PL EA _ _ PARTS1 FROK rr rx ar ax NE HR1 HX1) as SD.
        clear - KRX SD. lia. }
      subst rx. rewrite Nat.eqb_refl.
      ihere. to_implM. cbn [orb bunr unreachable tree_ops embed interp]. apply implM_interp_unr. }
    assert (NEX : rr <> rx) by (intros E; subst rx; apply KRX; rewrite (ref_at_fun _ _ _ _ _ _ (RH_nodup_l _ _ _ _ HEAP1) HR1 HX1); reflexivity).
    zstep.
    zstep. if_cases KRY; rewrite ?unsigned_lit in KRY by (clear - ArR AyR; lia); zify_cond KRY.
    2:{ assert (E : rr = ry).
      { destruct (Nat.eq_dec rr ry) as [E|NE]; [exact E|exfalso].
        pose proof (struct_disj st1 OW1 LB m2 HEAP1 bs1 PL EA _ _ PARTS1 FROK rr ry ar ay NE HR1 HY1) as SD.
        clear - KRY SD. lia. }
      subst ry. rewrite Nat.eqb_refl.
      ihere. to_implM. rewrite orb_true_r. cbn [bunr unreachable tree_ops embed interp]. apply implM_interp_unr. }
    assert (NEY : rr <> ry) by (intros E; subst ry; apply KRY; rewrite (ref_at_fun _ _ _ _ _ _ (RH_nodup_l _ _ _ _ HEAP1) HR1 HY1); reflexivity).
    replace (rr =? rx)%nat with false by (symmetry; apply Nat.eqb_neq; exact NEX).
    replace (rr =? ry)%nat with false by (symmetry; apply Nat.eqb_neq; exact NEY). cbn [orb].
    clear KRX KRY.
    assert (EAL1 : al = bn_top (getbn rx bs1)) by (rewrite EG1; reflexivity).
    assert (EBL1 : bl = bn_top (getbn ry bs1)) by (rewrite EG1; reflexivity).
    assert (LVR1 : (rr < NFIX + gx_used (st_ctx bs1))%nat) by (rewrite LU1; exact LVR).
    assert (LVX1 : (rx < NFIX + gx_used (st_ctx bs1))%nat) by (rewrite LU1; exact LVX).
    assert (LVY1 : (ry < NFIX + gx_used (st_ctx bs1))%nat) by (rewrite LU1; exact LVY).
    rewrite <- (EG1 rx), <- (EG1 ry).
    zstep. rewrite (bn_swrap32_small (Z.of_nat al - Z.of_nat bl)) by (clear - AL23 BL23; lia).
    zstep. replace (Z.of_nat al + - Z.of_nat bl) with (Z.of_nat al - Z.of_nat bl) by (clear; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep.
    eassert (CONT : ((al =? bl)%nat && (al =? 8)%nat = false) -> _).
    2:{ zstep. if_cases K8A; zify_cond K8A.
        { apply CONT. apply andb_false_iff. right. apply Nat.eqb_neq. clear - K8A. lia. }
        zstep. if_cases K8B; zify_cond K8B.
        { apply CONT. apply andb_false_iff. left. apply Nat.eqb_neq.
          intros E. apply K8B. rewrite E. rewrite Z.sub_diag. reflexivity. }

        assert (E8A : al = 8%nat) by (clear - K8A; lia).
        assert (E8B : bl = 8%nat).
        { rewrite land64_zero_iff in K8B by (clear - AL23 BL23; lia). clear - K8A K8B. lia. }
        rewrite E8A, E8B. cbn [Nat.eqb andb].
        ihere. to_implM.
        eapply mul_path_comba8; try eassumption; [rewrite <- EAL1; exact E8A | rewrite <- EBL1; exact E8B]. }
    intros ENC. rewrite ENC.
    zstep.
    assert (HAL : (0 < al)%nat) by (clear - KA0; lia). assert (HBL : (0 < bl)%nat) by (clear - KB0; lia).
    zstep. rewrite lts_small by (clear - AL23; lia). if_cases K16A; zify_cond K16A.
    { replace (16 <=? al)%nat with false by (symmetry; apply Nat.leb_gt; clear - K16A; lia). cbn [andb].
      ihere. to_implM. eapply mul_path_normal; eassumption. }
    zstep. rewrite lts_small by (clear - BL23; lia). if_cases K16B; zify_cond K16B.
    { replace (16 <=? bl)%nat with false by (symmetry; apply Nat.leb_gt; clear - K16B; lia). rewrite andb_false_r. cbn [andb].
      ihere. to_implM. eapply mul_path_normal; eassumption. }
    zstep.
    change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616.
    rewrite (bn_swrap32_mod (Z.of_nat al - Z.of_nat bl) 1) by (clear - AL23 BL23; lia).
    zstep.
    zstep. if_cases KU; zify_cond KU.
    {
      assert (KU' : ~ (0 <= Z.of_nat al - Z.of_nat bl + 1 <= 2)).
      { intros H. apply (land64_le_small (Z.of_nat al - Z.of_nat bl + 1) 2 ltac:(clear - AL23 BL23; lia) ltac:(lia)) in H. clear - H KU. lia. }
      replace ((16 <=? al)%nat && (16 <=? bl)%nat && (al <=? bl + 1)%nat && (bl <=? al + 1)%nat) with false.
      2:{ symmetry. apply andb_false_iff. destruct (Nat.leb_spec bl (al + 1)) as [H1|H1]; [|right; reflexivity].
          left. apply andb_false_iff. right. apply Nat.leb_gt. clear - KU' H1. lia. }
      ihere. to_implM. eapply mul_path_normal; eassumption. }

    assert (KU' : 0 <= Z.of_nat al - Z.of_nat bl + 1 <= 2) by (apply (land64_le_small (Z.of_nat al - Z.of_nat bl + 1) 2 ltac:(clear - AL23 BL23; lia) ltac:(lia)); exact KU).
    replace ((16 <=? al)%nat && (16 <=? bl)%nat && (al <=? bl + 1)%nat && (bl <=? al + 1)%nat) with true.
    2:{ symmetry. rewrite !andb_true_iff. repeat split; apply Nat.leb_le; [clear - K16A | clear - K16B | clear - KU' | clear - KU']; lia. }
    assert (NX : rx <> ROne).
    { intros E. subst rx. destruct WFS as (_ & _ & EONE & _). unfold al in K16A. rewrite EONE in K16A. cbn in K16A. clear - K16A. lia. }
    ihere. to_implM.
    eapply mul_path_kara; try eassumption; [clear - K16A; lia | clear - K16B; lia | clear - KU'; lia | clear - KU'; lia].
  Qed.

  Lemma bn_pre_mono : forall s bs m OW LB PL EA sp lo B errv K K',
    bn_pre s bs m OW LB PL EA sp lo B errv K' -> K <= K' -> bn_pre s bs m OW LB PL EA sp lo B errv K.
  Proof.
    intros s bs m OW LB PL EA sp lo B errv K K' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) H.
    unfold bn_pre. repeat (split; [assumption|]). split; [lia|]. split; assumption.
  Qed.

  Lemma bn_mul_fixed_top_walk_cs : forall (CS : Z), BN_MUL_FIXED_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> hpl PL rr -> ry <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz ac ->
    implM bgusegs (interp (embed (bn_mul_fixed_top (tree_ops bptr) rr rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_FIXED_TOP) fc None m (seg_rom bgusegs)).
  Proof. intros CS HCS. intros until qc. intros PRE. eapply bn_mul_fixed_top_walk. exact (bn_pre_mono _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS). Qed.

End Proofs.
End WithCeiling0.
