(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnDivWords BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX BnKaraMem BnNumBits.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac WU_num_bits_word BnCallsU WU_mul_normal WU_mul_recursive WU_mul_part_recursive WU_kara_final.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnArr DivModel.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface W_small W_small2 W_expand W_ctx W_ctx_end W_ctx_get W_top BnLeaves BnCall.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnUAlign BnUKit BnUKit2.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure W_mul_core.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAU Require Import BnAKit BnAUKit W_mul_core.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ops := (tree_ops bptr).

Definition nonpool (r : bnref) : Prop := forall i, r <> RPool i.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition mul_res (br : bignum bptr) (w : list Z) (top : nat) : bignum bptr :=
  mkBN (bn_d br) (splice (bn_buf br) 0 w) top (bn_neg br) (bn_flags br).

Lemma mul_res_okm : forall br w top, bn_okm br -> limbs w -> (length w <= bn_dmax br)%nat -> (top <= bn_dmax br)%nat -> bn_okm (mul_res br w top).
Proof.
  intros br w top (O1 & O2 & O3 & O4) LW HW HT. unfold bn_okm, mul_res, bn_dmax in *. cbn [bn_buf bn_top bn_flags].
  rewrite splice_length by lia. split; [apply splice_limbs; assumption|]. auto.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_MUL_FIXED_TOP : Z := 0x116cb4.
Definition BN_MUL : Z := 0x116c6c.
Definition BN_MUL_FIXED_STACK : Z := 112 + 9216.
Definition BN_MUL_STACK : Z := 32 + BN_MUL_FIXED_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable CS8 : Z.
  Hypothesis CS8_0 : 0 <= CS8.
  Hypothesis CS8_max : CS8 <= 1024.
  Hypothesis comba8_ok : comba8_uspec CS8.

  (* [comment removed for export] *)
  Definition mul_frame (jb : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
    [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition mul_join (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (rr x y : bnref) (R X Y : Z) (na nb : bool)
      (v : unit * lstate bptr) (st' : PState) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m' OW',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F (Z_to_bv 64 0x116f1c) fc None m' (seg_rom usegs)
      /\ cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st' (snd v) m' OW'
      /\ lib_state (snd v) m' OW' AD EA
      /\ ref_at (snd v) OW' AD rr R /\ ref_at (snd v) OW' AD x X /\ ref_at (snd v) OW' AD y Y
      /\ bn_neg (getbn x (snd v)) = na /\ bn_neg (getbn y (snd v)) = nb.

  Lemma mul_end : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (rr x y : bnref) (R X Y : Z) (na nb : bool) (v : unit * lstate bptr) (st' : PState) (ms' : machine_state),
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B ->
    mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y na nb v st' ms' ->
    implM usegs (interp (embed (BN_CTX_end ops (setbn rr (bn_with_neg (getbn rr (snd v)) (xorb na nb)) (snd v))))) st'
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1)) ms'.
  Proof.
    intros until ms'. intros CEIL GLO LO SPB (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x22 & x23 & x24 & x25 & x26 & x27 & t3 & t4 & t5 & t6
                                             & mE & OWE & -> & ENV & LS & HR & HX & HY & ENA & ENB).
    destruct v as [[] lsE]. cbn [fst snd] in *.
    unfold BN_MUL_FIXED_STACK in LO. unfold mul_frame in ENV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPC.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3063488 - 164) with 3063324 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (open_ro st' OWE LB mE lsE AD EA x X HEAP LS HX) as (Dx & SX & _).
    destruct (open_ro st' OWE LB mE lsE AD EA y Y HEAP LS HY) as (Dy & SY & _).
    unfold bn_cells, MallocRep.wz in SX, SY. rewrite ENA in SX. rewrite ENB in SY.
    destruct (lib_state_open [] lsE mE OWE AD EA rr R LS ND HR ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (bn_arr_facts st' OWE LB mE HEAP lsE AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR).
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    set (b := getbn rr lsE) in *.
    unfold bn_cells, MallocRep.wz in SR. unfold GLOBALS_TOP in GLO.
    assert (NA : 0 <= Z.b2z na <= 1) by (destruct na; cbn; lia).
    assert (NB : 0 <= Z.b2z nb <= 1) by (destruct nb; cbn; lia).
    pose proof (munch_refl [(R, R + 24)]%Z mE) as MU. pose proof (wmono_refl usegs mE) as WM.
    unfold implM. iprefix.
    zstep. rewrite (land7 R (proj2 (ref_at_ualign st' OWE LB mE lsE AD rr R HEAP ADB HR))). chk_lit.
    zstep. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
    zstep. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
    zstep.
    setreg 10%Z (Z_to_bv 64 (Z.b2z (xorb na nb))) ltac:(clear; destruct na, nb; reflexivity).
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HWL : Forall (w_lib OWE lo (bv_unsigned sp)) [(R, R + 24)]).
    { constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia] | constructor]. }
    assert (WOK : Forall (w_ok OWE LB lsE AD EA [rr]) [(R, R + 24)]).
    { constructor; [eapply (w_struct OWE LB lsE AD EA false [rr] _ rr R); [left; reflexivity | exact HR | cbn; lia | cbn; lia] | constructor]. }
    set (lsN := setbn rr (bn_with_neg b (xorb na nb)) lsE).
    assert (LSN : lib_state lsN m1 OWE AD EA).
    { unfold lib_state, lsN. eapply (lib_state_close [] lsE m1 OWE AD EA rr R); [| exact ND | exact HR | | |].
      - eapply lib_state_frame; [exact HEAP | exact LSH | exact MU | exact WM | exact WOK].
      - exists Dr. split; [unfold bn_cells, bn_with_neg, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; exact SR|].
        eapply bn_arr_of_u64arr; [exact ARR | exact U].
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bn_okm, bn_with_neg, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
    assert (ENVN : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st' lsN m1 OWE).
    { apply cenv_setbn.
      eapply (cenv_silent LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL ltac:(unfold GLOBALS_TOP; lia) FBlo FBsp SPB) with (errv' := errv);
        [exact ENV | exact MU | exact WM | exact HWL | exact ST | unfold LX_ERRNO, RATP; exact ERR | exact MI | exact FR | cbn; lia]. }
    clear SR U MU WM LSH ENV LS.
    zstep. if_cases KE; zify_cond KE; [|exfalso; apply KE; reflexivity]. clear KE.
    do 4 zstep.
    (* [comment removed for export] *)
    destruct (CPRE _ _ _ _ _ BN_CTX_END_STACK ENVN LSN ltac:(unfold BN_CTX_END_STACK; lia)) as (errvE & PREE).
    ihere. to_implM. fold b. fold lsN.
    eapply implM_post_evt.
    { eapply BN_CTX_end_walk with (lo := lo) (B := B) (errv := errvE) (OW := OWE) (LB := LB) (AD := AD) (EA := EA); [exact PREE | reflexivity | reflexivity]. }
    cbv beta. intros [uE lsF] stF msF PO. apply BPC in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & mF & OWF & -> & CPF & _).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENVN CPF) as (ENVF & LSF).
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1142620)) with (Z_to_bv 64 1142620) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (cenv_final LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m _ _ _ _ _ ENVF LSF)
      as (F1 & F2 & F3 & (errvF & F4) & F5 & F6 & F7 & F8 & F9).
    pose proof ENVF as (_ & _ & STF & _ & MIF & _ & _ & _ & _ & FRF & _). unfold mul_frame in FRF.
    zstep. do 13 zstep.
    release_frame FRF STF (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold bn_post. do 15 eexists. exists mF, OWF, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mul_finish1 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (st2 : PState) (ls2 : lstate bptr) (m2 : mem) (OW2 : list block) (rr x y : bnref) (R X Y Dr n8 CST : Z)
      (w : list Z) (topn : nat) (x22 x23 x24 x25 x26 x27 : word) (ms' : machine_state),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st2 ls2 m2 OW2 ->
    lib_state ls2 m2 OW2 AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> 0 <= CST -> lo <= bv_unsigned sp - 112 - CST -> bv_unsigned sp <= B ->
    ref_at ls2 OW2 AD rr R -> ref_at ls2 OW2 AD x X -> ref_at ls2 OW2 AD y Y -> rr <> x -> rr <> y ->
    rw_cells usegs m2 R (bn_cells Dr (getbn rr ls2)) -> bn_arr m2 OW2 Dr (getbn rr ls2) ->
    limbs w -> (0 < length w <= bn_dmax (getbn rr ls2))%nat -> (topn <= bn_dmax (getbn rr ls2))%nat -> n8 = 8 * Z.of_nat (length w) ->
    mulc_post sp gp (wz RATP) F fc m2 lo R Dr (getbn rr ls2) sp (Z_to_bv 64 (ad_ctx AD)) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R)
              x22 x23 x24 x25 x26 x27 [(Dr, Dr + n8); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)] topn w (fun _ => True) ms' ->
    mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
             (bn_neg (getbn x ls2)) (bn_neg (getbn y ls2)) (tt, setbn rr (mul_res (getbn rr ls2) w topn) ls2) st2 ms'.
  Proof.
    intros until ms'. intros ENV LS CEIL GLO HCST LO SPB HR HX HY NEX NEY SR ARR LW [HW0 HWD] HTD -> 
      (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & -> & MU & WM & MI3 & SR3 & HR3 & ST3 & _).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3063488 - 164) with 3063324 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] ls2 m2 OW2 AD EA rr R LS ND HR ltac:(intros [])) as (_ & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (bn_arr_facts st2 OW2 LB m2 HEAP ls2 AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
    pose proof (DSEP rr R HR) as DSR.
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    set (br := getbn rr ls2) in *.
    unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct ARR as [_ Eb]. unfold bn_dmax in HWD. rewrite Eb in HWD. cbn [length] in HWD. lia. }
    destruct ARR as [HinR _].
    pose proof (RH_range _ _ _ _ _ _ _ HEAP HinR) as (_ & _ & _ & _ & DRI).
    unfold GLOBALS_TOP in GLO.
    assert (HWL : Forall (w_lib OW2 lo (bv_unsigned sp)) [(Dr, Dr + 8 * Z.of_nat (length w)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]).
    { constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
      constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
      constructor; [left; cbn [fst snd]; lia | constructor]. }
    assert (WOK : Forall (w_ok OW2 LB ls2 AD EA [rr]) [(Dr, Dr + 8 * Z.of_nat (length w)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]).
    { constructor; [eapply (w_limbs OW2 LB ls2 AD EA false [rr] _ rr pr Dr); [left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
      constructor; [eapply (w_struct OW2 LB ls2 AD EA false [rr] _ rr R); [left; reflexivity | exact HR | cbn; lia | cbn; lia]|].
      constructor; [apply w_stack; cbn; lia | constructor]. }
    assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (apply splice_length; unfold bn_dmax in *; lia).
    set (lsN := setbn rr (mul_res br w topn) ls2).
    assert (LSN : lib_state lsN m3 OW2 AD EA).
    { unfold lib_state, lsN. eapply (lib_state_close [] ls2 m3 OW2 AD EA rr R); [| exact ND | exact HR | | |].
      - eapply lib_state_frame; [exact HEAP | exact LSH | exact MU | exact WM | exact WOK].
      - exists Dr. split; [unfold bn_cells, mul_res, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR3|].
        unfold bn_arr, mul_res. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LSP.
        split; [exact HinR|].
        eapply arr_splice0; [exact U | exact MU | exact WM | exact HR3 | unfold bn_dmax in *; lia | |].
        + cbn [disjoint_from]. lia.
        + cbn [disjoint_from]. unfold bn_dmax in *. lia.
      - apply mul_res_okm; assumption.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR |]. unfold bn_blocks, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
    unfold mul_join. do 22 eexists. exists m3, OW2. split; [reflexivity|]. cbn [fst snd]. fold lsN.
    split.
    { apply cenv_setbn.
      eapply (cenv_silent LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL ltac:(unfold GLOBALS_TOP; lia) FBlo FBsp SPB) with (errv' := errv);
        [exact ENV | exact MU | exact WM | exact HWL | exact ST3 | | exact MI3 | | exact FSZ].
      - eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold LX_ERRNO, RATP. cbn. lia.
      - eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. cbn. lia. }
    split; [exact LSN|].
    split; [apply ref_at_setbn; exact HR|]. split; [apply ref_at_setbn; exact HX|]. split; [apply ref_at_setbn; exact HY|].
    unfold lsN. rewrite !getbn_setbn_other by assumption. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mul_finish2 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (st3 : PState) (ls3 : lstate bptr) (m3 : mem) (OW3 : list block) (rr t x y : bnref) (R TT X Y Dr Dt nr8 CST : Z)
      (w tw : list Z) (topn : nat) (x22 x23 x24 x25 x26 x27 : word) (ms' : machine_state),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st3 ls3 m3 OW3 ->
    lib_state ls3 m3 OW3 AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> 0 <= CST -> lo <= bv_unsigned sp - 112 - CST -> bv_unsigned sp <= B ->
    ref_at ls3 OW3 AD rr R -> ref_at ls3 OW3 AD t TT -> ref_at ls3 OW3 AD x X -> ref_at ls3 OW3 AD y Y ->
    rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
    rw_cells usegs m3 R (bn_cells Dr (getbn rr ls3)) -> bn_arr m3 OW3 Dr (getbn rr ls3) ->
    rw_cells usegs m3 TT (bn_cells Dt (getbn t ls3)) -> bn_arr m3 OW3 Dt (getbn t ls3) ->
    limbs w -> (0 < length w <= bn_dmax (getbn rr ls3))%nat -> (topn <= bn_dmax (getbn rr ls3))%nat -> nr8 = 8 * Z.of_nat (length w) ->
    limbs tw -> length tw = bn_dmax (getbn t ls3) -> (0 < bn_dmax (getbn t ls3))%nat ->
    mulc_post sp gp (wz RATP) F fc m3 lo R Dr (getbn rr ls3) sp (Z_to_bv 64 (ad_ctx AD)) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R)
              x22 x23 x24 x25 x26 x27
              [(Dr, Dr + nr8); (Dt, Dt + 8 * Z.of_nat (length (bn_buf (getbn t ls3)))); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]
              topn w (fun m' => limbs_at usegs m' Dt tw) ms' ->
    mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
             (bn_neg (getbn x ls3)) (bn_neg (getbn y ls3))
             (tt, setbn rr (mul_res (getbn rr ls3) w topn) (setbn t (bn_with_buf (getbn t ls3) tw) ls3)) st3 ms'.
  Proof.
    intros until ms'. intros ENV LS CEIL GLO HCST LO SPB HR HT HX HY NEX NEY NTR NTX NTY SR ARR STT ARRT LW [HW0 HWD] HTD -> LTW NTW HT0
      (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m4 & -> & MU & WM & MI4 & SR4 & HR4 & ST4 & HT4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3063488 - 164) with 3063324 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] ls3 m3 OW3 AD EA rr R LS ND HR ltac:(intros [])) as (_ & OKR & LSH1).
    destruct (lib_state_open [rr] ls3 m3 OW3 AD EA t TT LSH1 ND HT ltac:(intros [E|[]]; apply NTR; symmetry; exact E)) as (_ & OKT & LSH2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (bn_arr_facts st3 OW3 LB m3 HEAP ls3 AD EA IDS ADB rr Dr HVR ARR) as (U & _ & D0 & DC & _ & DSEP).
    destruct (bn_arr_facts st3 OW3 LB m3 HEAP ls3 AD EA IDS ADB t Dt HVT ARRT) as (UT & _ & DT0 & DTC & _ & DSEPT).
    pose proof (DSEP rr R HR) as DSR. pose proof (DSEP t TT HT) as DSRT. pose proof (DSEPT rr R HR) as DSTR. pose proof (DSEPT t TT HT) as DSTT.
    pose proof (struct_disj st3 OW3 LB m3 HEAP ls3 AD EA IDS ADB t rr TT R NTR HT HR) as SDT.
    pose proof (bn_arrs_disj st3 OW3 LB m3 ls3 AD EA rr t R TT Dr Dt HEAP LS ltac:(congruence) HR HT ARR ARRT) as ADJ.
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    destruct (ref_at_inb _ _ _ _ _ ADB HT) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hint) as (TA0 & _ & _ & TAC & TAI).
    set (br := getbn rr ls3) in *. set (tb := getbn t ls3) in *.
    unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct ARR as [_ Eb]. unfold bn_dmax in HWD. rewrite Eb in HWD. cbn [length] in HWD. lia. }
    destruct ARR as [HinR _].
    unfold bn_arr in ARRT. destruct (bn_d tb) as [pt|] eqn:Edt.
    2:{ exfalso. destruct ARRT as [_ Eb]. unfold bn_dmax in HT0. rewrite Eb in HT0. cbn [length] in HT0. lia. }
    destruct ARRT as [HinT _].
    pose proof (RH_range _ _ _ _ _ _ _ HEAP HinR) as (_ & _ & _ & _ & DRI).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP HinT) as (_ & _ & _ & _ & DTI).
    unfold GLOBALS_TOP in GLO. fold (bn_dmax tb) in MU.
    assert (HWL : Forall (w_lib OW3 lo (bv_unsigned sp)) [(Dr, Dr + 8 * Z.of_nat (length w)); (Dt, Dt + 8 * Z.of_nat (bn_dmax tb)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]).
    { constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
      constructor; [right; exists (pt, Dt, 8 * Z.of_nat (bn_dmax tb)); cbn [blk_addr blk_size fst snd]; split; [exact HinT | lia]|].
      constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
      constructor; [left; cbn [fst snd]; lia | constructor]. }
    assert (WOK : Forall (w_ok OW3 LB ls3 AD EA [t; rr]) [(Dr, Dr + 8 * Z.of_nat (length w)); (Dt, Dt + 8 * Z.of_nat (bn_dmax tb)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]).
    { constructor; [eapply (w_limbs OW3 LB ls3 AD EA false [t; rr] _ rr pr Dr); [right; left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
      constructor; [eapply (w_limbs OW3 LB ls3 AD EA false [t; rr] _ t pt Dt); [left; reflexivity | exact HVT | exact Edt | exact HinT | cbn [fst snd]; lia | cbn [fst snd]; fold tb; lia]|].
      constructor; [eapply (w_struct OW3 LB ls3 AD EA false [t; rr] _ rr R); [right; left; reflexivity | exact HR | cbn; lia | cbn; lia]|].
      constructor; [apply w_stack; cbn; lia | constructor]. }
    pose proof (lib_state_frame st3 LB [t; rr] ls3 m3 m4 OW3 AD EA _ HEAP LSH2 MU WM WOK) as LSH2'.
    (* [comment removed for export] *)
    set (tb' := bn_with_buf tb tw).
    assert (LSH1' : lib_state_h [rr] (setbn t tb' ls3) m4 OW3 AD EA).
    { eapply (lib_state_close [rr] ls3 m4 OW3 AD EA t TT); [exact LSH2' | exact ND | exact HT | | |].
      - exists Dt. split.
        + unfold tb', bn_cells, bn_with_buf, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite NTW.
          eapply rw_cells_transport; [exact STT | exact MU | exact WM |]. cbn. lia.
        + unfold bn_arr, tb', bn_with_buf. cbn [bn_d]. rewrite Edt. unfold bn_dmax at 1. cbn [bn_buf]. rewrite NTW.
          split; [exact HinT|]. apply u64arr_of_limbs_at; [exact HT4|]. rewrite NTW.
          apply (limbarr_limbs_at usegs) in UT. destruct UT as [_ HWT]. eapply wr_at_transport; [exact HWT | exact WM].
      - destruct OKT as (O1 & O2 & O3 & O4). unfold bn_okm, tb', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite NTW. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVT |]. unfold bn_blocks, tb', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite NTW. reflexivity. }
    (* [comment removed for export] *)
    assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (apply splice_length; unfold bn_dmax in *; lia).
    set (ls3' := setbn t tb' ls3) in *.
    assert (EGR : getbn rr ls3' = br) by (unfold ls3'; apply getbn_setbn_other; exact NTR).
    assert (HR' : ref_at ls3' OW3 AD rr R) by (apply ref_at_setbn; exact HR).
    pose proof (valid_refm_setbn t rr tb' ls3 HVR) as HVR'. fold ls3' in HVR'.
    destruct (lib_state_h_parts _ _ _ _ _ _ LSH1') as (IDS' & _ & _ & _).
    assert (LSN : lib_state (setbn rr (mul_res br w topn) ls3') m4 OW3 AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls3' m4 OW3 AD EA rr R); [exact LSH1' | exact ND | exact HR' | | |].
      - exists Dr. split; [unfold bn_cells, mul_res, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR4|].
        unfold bn_arr, mul_res. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LSP.
        split; [exact HinR|].
        eapply arr_splice0; [exact U | exact MU | exact WM | exact HR4 | unfold bn_dmax in *; lia | |].
        + cbn [disjoint_from]. lia.
        + cbn [disjoint_from]. unfold bn_dmax in *. lia.
      - apply mul_res_okm; [exact OKR | exact LW | lia | exact HTD].
      - apply ids_ok_setbn_same; [exact IDS' | exact HVR' |]. rewrite EGR. unfold bn_blocks, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
    unfold mul_join. do 22 eexists. exists m4, OW3. split; [reflexivity|]. cbn [fst snd]. fold tb'. fold ls3'.
    split.
    { apply cenv_setbn. apply cenv_setbn.
      eapply (cenv_silent LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL ltac:(unfold GLOBALS_TOP; lia) FBlo FBsp SPB) with (errv' := errv);
        [exact ENV | exact MU | exact WM | exact HWL | exact ST4 | | exact MI4 | | exact FSZ].
      - eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold LX_ERRNO, RATP. cbn. lia.
      - eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. cbn. lia. }
    split; [exact LSN|].
    split; [apply ref_at_setbn; exact HR'|]. split; [apply ref_at_setbn; apply ref_at_setbn; exact HX|]. split; [apply ref_at_setbn; apply ref_at_setbn; exact HY|].
    unfold ls3'. rewrite !getbn_setbn_other by assumption. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mul_path_normal : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (st1 : PState) (ls1 : lstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z) (al bl : nat)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 x27 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st1 ls1 m1 OW1 ->
    lib_state ls1 m1 OW1 AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B ->
    ref_at ls1 OW1 AD rr R -> ref_at ls1 OW1 AD x X -> ref_at ls1 OW1 AD y Y -> rr <> x -> rr <> y ->
    al = bn_top (getbn x ls1) -> bl = bn_top (getbn y ls1) -> (0 < al)%nat -> (0 < bl)%nat ->
    implM usegs (interp (embed (disp_normal rr (firstn al (bn_buf (getbn x ls1))) (firstn bl (bn_buf (getbn y ls1))) (al + bl) ls1))) st1
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
                (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
               (Z_to_bv 64 (Z.of_nat bl)) x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x116e80) fc None m1 (seg_rom usegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR HX HY NEX NEY EAL EBL HAL HBL.
    unfold BN_MUL_FIXED_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPC.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK1).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
    pose proof (st_okm_getbn rr ls1 SOK1 HVR) as (_ & TDR1 & _).
    pose proof (st_okm_getbn x ls1 SOK1 HVX) as (LMX & TDX & DMX & _). pose proof (st_okm_getbn y ls1 SOK1 HVY) as (LMY & TDY & DMY & _).
    unfold BN_WORDS_MAX in DMX, DMY.
    set (la := firstn al (bn_buf (getbn x ls1))). set (lb := firstn bl (bn_buf (getbn y ls1))).
    assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
    assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
    unfold implM. iprefix. do 3 zstep.
    (* [comment removed for export] *)
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM. unfold disp_normal. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (bn_wexpand_leaves rr (al + bl) ls1 HVR TDR1)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW1) (LB := LB) (AD := AD) (EA := EA)
        (r := rr) (a := R) (words := (al + bl)%nat);
        [exact PRE1 | reflexivity | exact HR | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia]. }
    cbv beta. intros [u2 ls2] st2 ms2 [PO LEAF]. apply BPC in PO. cbn [fst snd] in PO, LEAF.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & -> & CP & (-> & HDM & _ & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV2 & LS2).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -112) _ _ _ _ _ _ _ _ CP) as RS.
    replace (ret_pc (Z_to_bv 64 1142412)) with (Z_to_bv 64 1142412) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS _ _ HR) as HR2. pose proof (RS _ _ HX) as HX2. pose proof (RS _ _ HY) as HY2.
    destruct LEAF as (LOTH & _).
    assert (EGX : getbn x ls2 = getbn x ls1) by (apply LOTH; exact NEX).
    assert (EGY : getbn y ls2 = getbn y ls1) by (apply LOTH; exact NEY).
    clear PRE1 CP ENV LS.
    (* [comment removed for export] *)
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    (* [comment removed for export] *)
    pose proof ENV2 as (HEAP2 & _ & ST2 & _ & MI2 & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_open [] ls2 m2 OW2 AD EA rr R LS2 ND2 HR2 ltac:(intros [])) as ((Dr & SR & ARR) & OKR & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HR2) as HVR2.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & _ & _).
    destruct (bn_arr_facts st2 OW2 LB m2 HEAP2 ls2 AD EA IDS2 ADB2 rr Dr HVR2 ARR) as (UR & _ & DR0 & DRC & _ & DSEPR).
    destruct (ref_at_inb _ _ _ _ _ ADB2 HR2) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hins) as (SA0 & _ & _ & SAC & _).
    destruct (operand_view_ne st2 OW2 LB m2 ls2 AD EA rr R Dr x X al HEAP2 LS2 HR2 SR ARR HX2 ltac:(rewrite EGX; lia) ltac:(congruence))
      as (Dx & HXd & HLX & _ & ARRX & X0' & XC' & DX0 & DXC & _ & SXA & _ & ALX).
    destruct (operand_view_ne st2 OW2 LB m2 ls2 AD EA rr R Dr y Y bl HEAP2 LS2 HR2 SR ARR HY2 ltac:(rewrite EGY; lia) ltac:(congruence))
      as (Dy & HYd & HLY & _ & ARRY & Y0' & YC' & DY0 & DYC & _ & SYA & _ & ALY).
    rewrite EGX in HLX, DXC, SXA, ALX. rewrite EGY in HLY, DYC, SYA, ALY. fold la in HLX. fold lb in HLY.
    pose proof (mul_normal_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY)) as (LW & _ & NW).
    rewrite LLA, LLB in NW.
    replace ((al =? 0)%nat || (bl =? 0)%nat) with false in NW by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; lia).
    specialize (DSEPR rr R HR2).
    set (br := getbn rr ls2) in *.
    replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    eapply evt_mono.
    { eapply (mulc_normal sp gp (wz RATP) F fc m2 lo R X Y Dr Dx Dy 9216 br la lb).
      - unfold mulc_pre. rewrite LLA, LLB. unfold GLOBALS_TOP in *.
        split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|]. split; [exact OKR|].
        split; [clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
        split; [clear - SA0 SAC Ra1 Ra2 X0' XC' Y0' YC' DR0 DRC DX0 DXC DY0 DYC CEIL LO SPR TDX TDY EAL EBL; unfold bn_dmax in *; lia|].
        split; [exact DSEPR|]. split; [clear - SXA TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - SYA TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - ALX TDX EAL; unfold bn_dmax in *; lia | clear - ALY TDY EBL; unfold bn_dmax in *; lia].
      - unfold mulc_upre.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st2 OW2 LB m2 ls2 AD rr R HEAP2 ADB2 HR2))|].
        split; [apply (bn_arr_ualign st2 OW2 LB m2 Dr br 1 HEAP2 ARR); first [clear - HDM HAL; lia | clear - HDM; lia]|].
        split; [apply (bn_arr_ualign st2 OW2 LB m2 Dx (getbn x ls2) 1 HEAP2 ARRX); rewrite EGX; first [clear - TDX EAL HAL; lia | clear - TDX EAL0; lia]
               | apply (bn_arr_ualign st2 OW2 LB m2 Dy (getbn y ls2) 1 HEAP2 ARRY); rewrite EGY; first [clear - TDY EBL HBL; lia | clear - TDY EBL0; lia]].
      - unfold mulc_mem. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
        split; [exact HLX|]. split; [exact HLY|]. split; [exact ST2 | exact MI2].
      - rewrite LLA, LLB. exact HDM.
      - lia. }
    intros ms' PO.
    eapply (mul_finish1 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb st2 ls2 m2 OW2 rr x y R X Y Dr
              (8 * (Z.of_nat (length la) + Z.of_nat (length lb))) 9216 (mul_normal la lb) (length la + length lb)%nat) in PO;
      [ | exact ENV2 | exact LS2 | exact CEIL | exact GLO | lia | lia | exact SPB | exact HR2 | exact HX2 | exact HY2 | exact NEX | exact NEY
        | exact SR | | exact LW | | | ].
    - rewrite EGX, EGY in PO. fold br. rewrite LLA, LLB in PO. exact PO.
    - subst br. unfold bn_arr in *. exact ARR.
    - rewrite NW. fold br. clear - HDM HAL. lia.
    - rewrite LLA, LLB. fold br. exact HDM.
    - rewrite NW, LLA, LLB. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mul_path_comba8 : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (st1 : PState) (ls1 : lstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st1 ls1 m1 OW1 ->
    lib_state ls1 m1 OW1 AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B ->
    ref_at ls1 OW1 AD rr R -> ref_at ls1 OW1 AD x X -> ref_at ls1 OW1 AD y Y -> rr <> x -> rr <> y ->
    bn_top (getbn x ls1) = 8%nat -> bn_top (getbn y ls1) = 8%nat ->
    implM usegs (interp (embed (disp_comba8 rr (firstn 8 (bn_buf (getbn x ls1))) (firstn 8 (bn_buf (getbn y ls1))) ls1))) st1
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
                (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x116d70) fc None m1 (seg_rom usegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR HX HY NEX NEY EAL0 EBL0.
    set (al := 8%nat). set (bl := 8%nat).
    assert (EAL : al = bn_top (getbn x ls1)) by (symmetry; exact EAL0). assert (EBL : bl = bn_top (getbn y ls1)) by (symmetry; exact EBL0).
    unfold BN_MUL_FIXED_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPC.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK1).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
    pose proof (st_okm_getbn rr ls1 SOK1 HVR) as (_ & TDR1 & _).
    pose proof (st_okm_getbn x ls1 SOK1 HVX) as (LMX & TDX & DMX & _). pose proof (st_okm_getbn y ls1 SOK1 HVY) as (LMY & TDY & DMY & _).
    unfold BN_WORDS_MAX in DMX, DMY.
    set (la := firstn al (bn_buf (getbn x ls1))). set (lb := firstn bl (bn_buf (getbn y ls1))).
    assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
    assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
    unfold implM. iprefix. do 3 zstep.
    (* [comment removed for export] *)
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM. unfold disp_comba8. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (bn_wexpand_leaves rr 16 ls1 HVR TDR1)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW1) (LB := LB) (AD := AD) (EA := EA)
        (r := rr) (a := R) (words := 16%nat);
        [exact PRE1 | reflexivity | exact HR | reflexivity | reflexivity | lia]. }
    cbv beta. intros [u2 ls2] st2 ms2 [PO LEAF]. apply BPC in PO. cbn [fst snd] in PO, LEAF.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & -> & CP & (-> & HDM & _ & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV2 & LS2).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -112) _ _ _ _ _ _ _ _ CP) as RS.
    replace (ret_pc (Z_to_bv 64 1142140)) with (Z_to_bv 64 1142140) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS _ _ HR) as HR2. pose proof (RS _ _ HX) as HX2. pose proof (RS _ _ HY) as HY2.
    destruct LEAF as (LOTH & _).
    assert (EGX : getbn x ls2 = getbn x ls1) by (apply LOTH; exact NEX).
    assert (EGY : getbn y ls2 = getbn y ls1) by (apply LOTH; exact NEY).
    clear PRE1 CP ENV LS.
    (* [comment removed for export] *)
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    (* [comment removed for export] *)
    pose proof ENV2 as (HEAP2 & _ & ST2 & _ & MI2 & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_open [] ls2 m2 OW2 AD EA rr R LS2 ND2 HR2 ltac:(intros [])) as ((Dr & SR & ARR) & OKR & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HR2) as HVR2.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & _ & _).
    destruct (bn_arr_facts st2 OW2 LB m2 HEAP2 ls2 AD EA IDS2 ADB2 rr Dr HVR2 ARR) as (UR & _ & DR0 & DRC & _ & DSEPR).
    destruct (ref_at_inb _ _ _ _ _ ADB2 HR2) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hins) as (SA0 & _ & _ & SAC & _).
    destruct (operand_view_ne st2 OW2 LB m2 ls2 AD EA rr R Dr x X al HEAP2 LS2 HR2 SR ARR HX2 ltac:(rewrite EGX; lia) ltac:(congruence))
      as (Dx & HXd & HLX & _ & ARRX & X0' & XC' & DX0 & DXC & _ & SXA & _ & ALX).
    destruct (operand_view_ne st2 OW2 LB m2 ls2 AD EA rr R Dr y Y bl HEAP2 LS2 HR2 SR ARR HY2 ltac:(rewrite EGY; lia) ltac:(congruence))
      as (Dy & HYd & HLY & _ & ARRY & Y0' & YC' & DY0 & DYC & _ & SYA & _ & ALY).
    rewrite EGX in HLX, DXC, SXA, ALX. rewrite EGY in HLY, DYC, SYA, ALY. fold la in HLX. fold lb in HLY.
    pose proof (mul_comba8_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY) LLA LLB) as (LW & NW & _).
    specialize (DSEPR rr R HR2).
    set (br := getbn rr ls2) in *.
    eapply evt_mono.
    { eapply (mulc_comba8 sp gp (wz RATP) F fc m2 lo R X Y Dr Dx Dy 9216 br la lb) with (CS8 := CS8).
      - unfold mulc_pre. rewrite LLA, LLB. unfold GLOBALS_TOP in *.
        split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|]. split; [exact OKR|].
        split; [clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
        split; [clear - SA0 SAC Ra1 Ra2 X0' XC' Y0' YC' DR0 DRC DX0 DXC DY0 DYC CEIL LO SPR TDX TDY EAL EBL; unfold bn_dmax in *; lia|].
        split; [exact DSEPR|]. split; [clear - SXA TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - SYA TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - ALX TDX EAL; unfold bn_dmax in *; lia | clear - ALY TDY EBL; unfold bn_dmax in *; lia].
      - unfold mulc_upre.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st2 OW2 LB m2 ls2 AD rr R HEAP2 ADB2 HR2))|].
        split; [apply (bn_arr_ualign st2 OW2 LB m2 Dr br 1 HEAP2 ARR); first [clear - HDM HAL; lia | clear - HDM; lia]|].
        split; [apply (bn_arr_ualign st2 OW2 LB m2 Dx (getbn x ls2) 1 HEAP2 ARRX); rewrite EGX; first [clear - TDX EAL HAL; lia | clear - TDX EAL0; lia]
               | apply (bn_arr_ualign st2 OW2 LB m2 Dy (getbn y ls2) 1 HEAP2 ARRY); rewrite EGY; first [clear - TDY EBL HBL; lia | clear - TDY EBL0; lia]].
      - unfold mulc_mem. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
        split; [exact HLX|]. split; [exact HLY|]. split; [exact ST2 | exact MI2].
      - exact comba8_ok.
      - lia.
      - exact LLA.
      - exact LLB.
      - exact HDM. }
    intros ms' PO.
    eapply (mul_finish1 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb st2 ls2 m2 OW2 rr x y R X Y Dr
              (8 * 16) 9216 (mul_comba8 la lb) 16%nat) in PO;
      [ | exact ENV2 | exact LS2 | exact CEIL | exact GLO | lia | lia | exact SPB | exact HR2 | exact HX2 | exact HY2 | exact NEX | exact NEY
        | exact SR | | exact LW | | | ].
    - rewrite EGX, EGY in PO. fold br. exact PO.
    - subst br. unfold bn_arr in *. exact ARR.
    - rewrite NW. fold br. clear - HDM. lia.
    - fold br. exact HDM.
    - rewrite NW. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mul_path_rec : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (st2 : PState) (ls2 : lstate bptr) (m2 : mem) (OW2 : list block) (rr t x y : bnref) (R TT X Y : Z) (al bl kj : nat)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st2 ls2 m2 OW2 ->
    lib_state ls2 m2 OW2 AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B ->
    ref_at ls2 OW2 AD rr R -> ref_at ls2 OW2 AD t TT -> ref_at ls2 OW2 AD x X -> ref_at ls2 OW2 AD y Y ->
    rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
    al = bn_top (getbn x ls2) -> bl = bn_top (getbn y ls2) ->
    (1 <= kj <= 23)%nat -> (al <= Nat.pow 2 kj)%nat -> (bl <= Nat.pow 2 kj)%nat -> (Nat.pow 2 kj - al <= 1)%nat -> (Nat.pow 2 kj - bl <= 1)%nat ->
    implM usegs (interp (embed (disp_rec rr t (firstn al (bn_buf (getbn x ls2))) (firstn bl (bn_buf (getbn y ls2))) al bl (al + bl) kj ls2))) st2
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
                (bn_neg (getbn x ls2)) (bn_neg (getbn y ls2)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
               (Z_to_bv 64 (Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kj))) (Z_to_bv 64 TT) (Z_to_bv 64 (2 * Z.of_nat (Nat.pow 2 kj))) t3 t4 t5 t6)
          F (Z_to_bv 64 0x116e1c) fc None m2 (seg_rom usegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR HT HX HY NEX NEY NTR NTX NTY EAL EBL HKJ HALJ HBLJ HDA HDB.
    unfold BN_MUL_FIXED_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPC.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
    pose proof (st_okm_getbn t ls2 SOK2 HVT) as (_ & TDT2 & _).
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
    do 3 zstep.
    (* [comment removed for export] *)
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM. unfold disp_rec. unfold bbind at 1. cbn [bind tree_ops]. fold j.
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (bn_wexpand_leaves t (4 * j) ls2 HVT TDT2)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW2) (LB := LB) (AD := AD) (EA := EA)
        (r := t) (a := TT) (words := (4 * j)%nat);
        [exact PRE1 | reflexivity | exact HT | reflexivity | reflexivity | clear - PJ; lia]. }
    cbv beta. intros [u3 ls3] st3 ms3 [PO LEAF3]. apply BPC in PO. cbn [fst snd] in PO, LEAF3.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m3 & OW3 & -> & CP3 & (-> & HDM3 & _ & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP3) as (ENV3 & LS3).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -112) _ _ _ _ _ _ _ _ CP3) as RS3.
    replace (ret_pc (Z_to_bv 64 1142328)) with (Z_to_bv 64 1142328) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS3 _ _ HR) as HR3. pose proof (RS3 _ _ HT) as HT3. pose proof (RS3 _ _ HX) as HX3. pose proof (RS3 _ _ HY) as HY3.
    destruct LEAF3 as (LOTH3 & _).
    clear PRE1 CP3 ENV LS.
    (* [comment removed for export] *)
    destruct (lib_state_h_parts _ _ _ _ _ _ LS3) as (_ & ADB3 & _ & SOK3).
    destruct (ref_at_inb _ _ _ _ _ ADB3 HT3) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV3) Hint) as (TA0 & _ & _ & TAC & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KT; zify_cond KT; [exfalso; clear - KT TA0 Rt1 TAC Rt2; lia|]. clear KT.
    do 3 zstep.
    (* [comment removed for export] *)
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS3 HR3) as HVR3.
    pose proof (st_okm_getbn rr ls3 SOK3 HVR3) as (_ & TDR3 & _).
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV3 LS3 ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv3 & PRE3).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops fst snd].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (bn_wexpand_leaves rr (4 * j) ls3 HVR3 TDR3)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv3) (OW := OW3) (LB := LB) (AD := AD) (EA := EA)
        (r := rr) (a := R) (words := (4 * j)%nat);
        [exact PRE3 | reflexivity | exact HR3 | reflexivity | reflexivity | clear - PJ; lia]. }
    cbv beta. intros [u4 ls4] st4 ms4 [PO LEAF4]. apply BPC in PO. cbn [fst snd] in PO, LEAF4.
    destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m4 & OW4 & -> & CP4 & (-> & HDM4 & _ & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV3 CP4) as (ENV4 & LS4).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -112) _ _ _ _ _ _ _ _ CP4) as RS4.
    replace (ret_pc (Z_to_bv 64 1142344)) with (Z_to_bv 64 1142344) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS4 _ _ HR3) as HR4. pose proof (RS4 _ _ HT3) as HT4. pose proof (RS4 _ _ HX3) as HX4. pose proof (RS4 _ _ HY3) as HY4.
    destruct LEAF4 as (LOTH4 & _).
    assert (EGX : getbn x ls4 = getbn x ls2) by (rewrite (LOTH4 x NEX); apply LOTH3; exact NTX).
    assert (EGY : getbn y ls4 = getbn y ls2) by (rewrite (LOTH4 y NEY); apply LOTH3; exact NTY).
    assert (EGT : getbn t ls4 = getbn t ls3) by (apply LOTH4; congruence).
    clear PRE3 CP4 ENV3 LS3 HVR3 TDR3 ADB3 SOK3 Hint.
    (* [comment removed for export] *)
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    set (la := firstn al (bn_buf (getbn x ls2))). set (lb := firstn bl (bn_buf (getbn y ls2))).
    destruct (mul_recursive kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf (getbn rr ls4))) (bn_buf (getbn t ls4))) as [ro to] eqn:EMR.
    cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    (* [comment removed for export] *)
    pose proof ENV4 as (HEAP4 & _ & ST4 & _ & MI4 & _).
    destruct (open_full st4 OW4 LB m4 ls4 AD EA rr R HEAP4 LS4 HR4) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (open_full st4 OW4 LB m4 ls4 AD EA t TT HEAP4 LS4 HT4) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
    destruct (open_full st4 OW4 LB m4 ls4 AD EA x X HEAP4 LS4 HX4) as (Dx & SX & ARRX & OKX & UX & X0 & XC & DX0 & DXC & DSEPX).
    destruct (open_full st4 OW4 LB m4 ls4 AD EA y Y HEAP4 LS4 HY4) as (Dy & SY & ARRY & OKY & UY & Y0 & YC & DY0 & DYC & DSEPY).
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA rr x R X Dr Dx HEAP4 LS4 NEX HR4 HX4 ARR ARRX) as DRX.
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA rr y R Y Dr Dy HEAP4 LS4 NEY HR4 HY4 ARR ARRY) as DRY.
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA t x TT X Dt Dx HEAP4 LS4 NTX HT4 HX4 ARRT ARRX) as DTX.
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA t y TT Y Dt Dy HEAP4 LS4 NTY HT4 HY4 ARRT ARRY) as DTY.
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA rr t R TT Dr Dt HEAP4 LS4 ltac:(congruence) HR4 HT4 ARR ARRT) as DRT.
    pose proof (DSEPR rr R HR4) as S1. pose proof (DSEPX rr R HR4) as S2. pose proof (DSEPY rr R HR4) as S3. pose proof (DSEPT rr R HR4) as S4.
    rewrite EGX in *. rewrite EGY in *. rewrite <- EGT in HDM3.
    pose proof OKX as (LMX & TDX & DMX & _). pose proof OKY as (LMY & TDY & DMY & _). pose proof OKT as (LMT & _). unfold BN_WORDS_MAX in DMX, DMY.
    assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
    assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
    assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
    assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
    set (br := getbn rr ls4) in *. set (tb := getbn t ls4) in *.
    assert (HD2 : (2 * j <= bn_dmax br)%nat) by (clear - HDM4; lia).
    assert (HSC : (scratch_rec kj <= length (bn_buf tb))%nat).
    { pose proof (scratch_rec_le kj). fold j in H. unfold bn_dmax in HDM3. clear - H HDM3. lia. }
    pose proof OKR as (LBR & _).
    assert (LRl : length (firstn (2 * j) (bn_buf br)) = (2 * j)%nat) by (apply firstn_length_le; unfold bn_dmax in HD2; exact HD2).
    pose proof (mul_recursive_spec kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf br)) (bn_buf tb) HLla HLlb
                  ltac:(apply limbs_firstn; exact LBR) LMT ltac:(lia) HDA HDB ltac:(rewrite LLA; clear - HALJ; lia) ltac:(rewrite LLB; clear - HBLJ; lia) LRl HSC) as MP.
    rewrite EMR in MP. destruct MP as (LRO & NRO & _ & LTO & NTO).
    replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    eapply evt_mono.
    { eapply (mulc_rec sp gp (wz RATP) F fc m4 lo R X Y Dr Dx Dy 9216 br la lb) with (CS8 := kara_uleaf CS8) (k := kj) (da := (j - al)%nat) (db := (j - bl)%nat)
        (TT := TT) (Dt := Dt) (Tl := bn_buf tb).
      - unfold mulc_pre. rewrite LLA, LLB. unfold GLOBALS_TOP in *.
        split; [exact HLla|]. split; [exact HLlb|]. split; [exact OKR|].
        split; [clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
        split; [clear - R0 RC X0 XC Y0 YC DR0 DRC DX0 DXC DY0 DYC CEIL LO SPR TDX TDY EAL EBL; unfold bn_dmax in *; lia|].
        split; [exact S1|]. split; [clear - S2 TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - S3 TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - DRX TDX EAL; unfold bn_dmax in *; lia | clear - DRY TDY EBL; unfold bn_dmax in *; lia].
      - unfold mulc_upre.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st4 OW4 LB m4 ls4 AD rr R HEAP4 (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS4))) HR4))|].
        split; [apply (bn_arr_ualign st4 OW4 LB m4 Dr br 1 HEAP4 ARR); clear - HDM4 PJ; lia|].
        split; [eapply (bn_arr_ualign st4 OW4 LB m4 Dx _ 1 HEAP4 ARRX);
                  first [clear - TDX EAL HALJ HDA PJ; unfold bn_dmax in *; lia | clear - TDX EAL HALJ PJ; unfold bn_dmax in *; lia]
               | eapply (bn_arr_ualign st4 OW4 LB m4 Dy _ 1 HEAP4 ARRY);
                  first [clear - TDY EBL HBLJ HDB PJ; unfold bn_dmax in *; lia | clear - TDY EBL HBLJ PJ; unfold bn_dmax in *; lia]].
      - unfold mulc_mem. split; [exact SR|]. split; [exact UR|]. split; [apply (d_cell m4 X Dx _ SX)|]. split; [apply (d_cell m4 Y Dy _ SY)|].
        split; [subst la; apply limbs_at_firstn; exact UX|]. split; [subst lb; apply limbs_at_firstn; exact UY|]. split; [exact ST4 | exact MI4].
      - apply (bn_mul_recursive_ufinal CS8 CS8_0 comba8_ok).
      - unfold rec_ustack, kara_uleaf. clear - HKJ CS8_0 CS8_max. lia.
      - unfold mulc_tpre. rewrite LLA, LLB. unfold GLOBALS_TOP in *.
        split; [exact LMT|]. split; [apply (d_cell m4 TT Dt _ STT)|].
        split; [apply limbs_at_of_u64arr; exact UT|].
        split; [apply (limbarr_limbs_at usegs) in UT; exact (proj2 UT)|].
        split; [clear - DT0 DTC CEIL; unfold bn_dmax in *; lia|]. split; [clear - S4; unfold bn_dmax in *; lia|].
        split; [clear - DTX TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - DTY TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - DRT; unfold bn_dmax in *; lia|].
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st4 OW4 LB m4 ls4 AD t TT HEAP4 (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS4))) HT4))|].
        apply (bn_arr_ualign st4 OW4 LB m4 Dt tb 1 HEAP4 ARRT). clear - HDM3 PJ. unfold bn_dmax in *. lia.
      - exact HKJ' .
      - exact HDA.
      - exact HDB.
      - rewrite LLA. clear - HALJ. lia.
      - rewrite LLB. clear - HBLJ. lia.
      - exact HD2.
      - exact HSC. }
    intros ms' PO. rewrite EMR in PO. cbn [fst snd] in PO. rewrite LLA, LLB in PO.
    eapply (mul_finish2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb st4 ls4 m4 OW4 rr t x y R TT X Y Dr Dt
              (8 * Z.of_nat (2 * j)) 9216 ro to (al + bl)%nat) in PO;
      [ | exact ENV4 | exact LS4 | exact CEIL | exact GLO | lia | lia | exact SPB | exact HR4 | exact HT4 | exact HX4 | exact HY4
        | exact NEX | exact NEY | exact NTR | exact NTX | exact NTY | exact SR | exact ARR | exact STT | exact ARRT
        | exact LRO | | | | exact LTO | | ].
    - rewrite EGX, EGY in PO. fold br tb in PO. unfold mul_res in PO. exact PO.
    - rewrite NRO, LRl. fold br. clear - HD2 PJ. lia.
    - fold br. clear - HDM4 HALJ HBLJ. lia.
    - rewrite NRO, LRl. reflexivity.
    - rewrite NTO. reflexivity.
    - fold tb. clear - HDM3 PJ. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mul_path_part : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (st2 : PState) (ls2 : lstate bptr) (m2 : mem) (OW2 : list block) (rr t x y : bnref) (R TT X Y : Z) (al bl kj : nat)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st2 ls2 m2 OW2 ->
    lib_state ls2 m2 OW2 AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B ->
    ref_at ls2 OW2 AD rr R -> ref_at ls2 OW2 AD t TT -> ref_at ls2 OW2 AD x X -> ref_at ls2 OW2 AD y Y ->
    rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
    al = bn_top (getbn x ls2) -> bl = bn_top (getbn y ls2) ->
    (3 <= kj <= 23)%nat -> (Nat.pow 2 kj <= al)%nat -> (Nat.pow 2 kj <= bl)%nat -> (al < 2 * Nat.pow 2 kj)%nat -> (bl < 2 * Nat.pow 2 kj)%nat ->
    (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
    implM usegs (interp (embed (disp_part rr t (firstn al (bn_buf (getbn x ls2))) (firstn bl (bn_buf (getbn y ls2))) al bl (al + bl) kj ls2))) st2
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
                (bn_neg (getbn x ls2)) (bn_neg (getbn y ls2)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
               (Z_to_bv 64 (Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kj))) (Z_to_bv 64 TT) (Z_to_bv 64 (2 * Z.of_nat (Nat.pow 2 kj))) t3 t4 t5 t6)
          F (Z_to_bv 64 0x116ebc) fc None m2 (seg_rom usegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR HT HX HY NEX NEY NTR NTX NTY EAL EBL HKJ HALJ HBLJ HAL2 HBL2 HD1 HD2'.
    unfold BN_MUL_FIXED_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPC.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
    pose proof (st_okm_getbn t ls2 SOK2 HVT) as (_ & TDT2 & _).
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
    do 3 zstep.
    (* [comment removed for export] *)
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM. unfold disp_part. unfold bbind at 1. cbn [bind tree_ops]. fold j.
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (bn_wexpand_leaves t (8 * j) ls2 HVT TDT2)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW2) (LB := LB) (AD := AD) (EA := EA)
        (r := t) (a := TT) (words := (8 * j)%nat);
        [exact PRE1 | reflexivity | exact HT | reflexivity | reflexivity | clear - PJ; lia]. }
    cbv beta. intros [u3 ls3] st3 ms3 [PO LEAF3]. apply BPC in PO. cbn [fst snd] in PO, LEAF3.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m3 & OW3 & -> & CP3 & (-> & HDM3 & _ & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP3) as (ENV3 & LS3).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -112) _ _ _ _ _ _ _ _ CP3) as RS3.
    replace (ret_pc (Z_to_bv 64 1142484)) with (Z_to_bv 64 1142484) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS3 _ _ HR) as HR3. pose proof (RS3 _ _ HT) as HT3. pose proof (RS3 _ _ HX) as HX3. pose proof (RS3 _ _ HY) as HY3.
    destruct LEAF3 as (LOTH3 & _).
    clear PRE1 CP3 ENV LS.
    (* [comment removed for export] *)
    destruct (lib_state_h_parts _ _ _ _ _ _ LS3) as (_ & ADB3 & _ & SOK3).
    destruct (ref_at_inb _ _ _ _ _ ADB3 HT3) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV3) Hint) as (TA0 & _ & _ & TAC & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KT; zify_cond KT; [exfalso; clear - KT TA0 Rt1 TAC Rt2; lia|]. clear KT.
    do 3 zstep.
    (* [comment removed for export] *)
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS3 HR3) as HVR3.
    pose proof (st_okm_getbn rr ls3 SOK3 HVR3) as (_ & TDR3 & _).
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV3 LS3 ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv3 & PRE3).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops fst snd].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (bn_wexpand_leaves rr (8 * j) ls3 HVR3 TDR3)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv3) (OW := OW3) (LB := LB) (AD := AD) (EA := EA)
        (r := rr) (a := R) (words := (8 * j)%nat);
        [exact PRE3 | reflexivity | exact HR3 | reflexivity | reflexivity | clear - PJ; lia]. }
    cbv beta. intros [u4 ls4] st4 ms4 [PO LEAF4]. apply BPC in PO. cbn [fst snd] in PO, LEAF4.
    destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m4 & OW4 & -> & CP4 & (-> & HDM4 & _ & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV3 CP4) as (ENV4 & LS4).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -112) _ _ _ _ _ _ _ _ CP4) as RS4.
    replace (ret_pc (Z_to_bv 64 1142500)) with (Z_to_bv 64 1142500) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS4 _ _ HR3) as HR4. pose proof (RS4 _ _ HT3) as HT4. pose proof (RS4 _ _ HX3) as HX4. pose proof (RS4 _ _ HY3) as HY4.
    destruct LEAF4 as (LOTH4 & _).
    assert (EGX : getbn x ls4 = getbn x ls2) by (rewrite (LOTH4 x NEX); apply LOTH3; exact NTX).
    assert (EGY : getbn y ls4 = getbn y ls2) by (rewrite (LOTH4 y NEY); apply LOTH3; exact NTY).
    assert (EGT : getbn t ls4 = getbn t ls3) by (apply LOTH4; congruence).
    clear PRE3 CP4 ENV3 LS3 HVR3 TDR3 ADB3 SOK3 Hint.
    (* [comment removed for export] *)
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    set (la := firstn al (bn_buf (getbn x ls2))). set (lb := firstn bl (bn_buf (getbn y ls2))).
    destruct (mul_part_recursive kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf (getbn rr ls4))) (bn_buf (getbn t ls4))) as [ro to] eqn:EMR.
    cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    (* [comment removed for export] *)
    pose proof ENV4 as (HEAP4 & _ & ST4 & _ & MI4 & _).
    destruct (open_full st4 OW4 LB m4 ls4 AD EA rr R HEAP4 LS4 HR4) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (open_full st4 OW4 LB m4 ls4 AD EA t TT HEAP4 LS4 HT4) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
    destruct (open_full st4 OW4 LB m4 ls4 AD EA x X HEAP4 LS4 HX4) as (Dx & SX & ARRX & OKX & UX & X0 & XC & DX0 & DXC & DSEPX).
    destruct (open_full st4 OW4 LB m4 ls4 AD EA y Y HEAP4 LS4 HY4) as (Dy & SY & ARRY & OKY & UY & Y0 & YC & DY0 & DYC & DSEPY).
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA rr x R X Dr Dx HEAP4 LS4 NEX HR4 HX4 ARR ARRX) as DRX.
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA rr y R Y Dr Dy HEAP4 LS4 NEY HR4 HY4 ARR ARRY) as DRY.
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA t x TT X Dt Dx HEAP4 LS4 NTX HT4 HX4 ARRT ARRX) as DTX.
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA t y TT Y Dt Dy HEAP4 LS4 NTY HT4 HY4 ARRT ARRY) as DTY.
    pose proof (bn_arrs_disj st4 OW4 LB m4 ls4 AD EA rr t R TT Dr Dt HEAP4 LS4 ltac:(congruence) HR4 HT4 ARR ARRT) as DRT.
    pose proof (DSEPR rr R HR4) as S1. pose proof (DSEPX rr R HR4) as S2. pose proof (DSEPY rr R HR4) as S3. pose proof (DSEPT rr R HR4) as S4.
    rewrite EGX in *. rewrite EGY in *. rewrite <- EGT in HDM3.
    pose proof OKX as (LMX & TDX & DMX & _). pose proof OKY as (LMY & TDY & DMY & _). pose proof OKT as (LMT & _). unfold BN_WORDS_MAX in DMX, DMY.
    assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
    assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
    assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
    assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
    set (br := getbn rr ls4) in *. set (tb := getbn t ls4) in *.
    assert (HD2 : (4 * j <= bn_dmax br)%nat) by (clear - HDM4; lia).
    assert (HSC : (8 * j <= length (bn_buf tb))%nat) by (unfold bn_dmax in HDM3; exact HDM3).
    pose proof OKR as (LBR & _).
    assert (LRl : length (firstn (4 * j) (bn_buf br)) = (4 * j)%nat) by (apply firstn_length_le; unfold bn_dmax in HD2; exact HD2).
    pose proof (mul_part_recursive_spec kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf br)) (bn_buf tb) HLla HLlb
                  ltac:(apply limbs_firstn; exact LBR) LMT ltac:(lia) ltac:(lia) ltac:(clear - HAL2 HALJ; lia) ltac:(clear - HBL2 HBLJ; lia)
                  ltac:(clear - HD1 HD2' HALJ HBLJ; lia) ltac:(clear - HD1 HD2' HALJ HBLJ; lia)
                  ltac:(rewrite LLA; clear - HALJ; lia) ltac:(rewrite LLB; clear - HBLJ; lia) LRl HSC) as MP.
    rewrite EMR in MP. destruct MP as (LRO & NRO & _ & LTO & NTO).
    replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    eapply evt_mono.
    { eapply (mulc_part sp gp (wz RATP) F fc m4 lo R X Y Dr Dx Dy 9216 br la lb) with (CS8 := kara_uleaf CS8) (fuel := kj) (k := kj) (tna := (al - j)%nat) (tnb := (bl - j)%nat)
        (TT := TT) (Dt := Dt) (Tl := bn_buf tb).
      - unfold mulc_pre. rewrite LLA, LLB. unfold GLOBALS_TOP in *.
        split; [exact HLla|]. split; [exact HLlb|]. split; [exact OKR|].
        split; [clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
        split; [clear - R0 RC X0 XC Y0 YC DR0 DRC DX0 DXC DY0 DYC CEIL LO SPR TDX TDY EAL EBL; unfold bn_dmax in *; lia|].
        split; [exact S1|]. split; [clear - S2 TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - S3 TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - DRX TDX EAL; unfold bn_dmax in *; lia | clear - DRY TDY EBL; unfold bn_dmax in *; lia].
      - unfold mulc_upre.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st4 OW4 LB m4 ls4 AD rr R HEAP4 (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS4))) HR4))|].
        split; [apply (bn_arr_ualign st4 OW4 LB m4 Dr br 1 HEAP4 ARR); clear - HDM4 PJ; lia|].
        split; [eapply (bn_arr_ualign st4 OW4 LB m4 Dx _ 1 HEAP4 ARRX);
                  first [clear - TDX EAL HALJ HDA PJ; unfold bn_dmax in *; lia | clear - TDX EAL HALJ PJ; unfold bn_dmax in *; lia]
               | eapply (bn_arr_ualign st4 OW4 LB m4 Dy _ 1 HEAP4 ARRY);
                  first [clear - TDY EBL HBLJ HDB PJ; unfold bn_dmax in *; lia | clear - TDY EBL HBLJ PJ; unfold bn_dmax in *; lia]].
      - unfold mulc_mem. split; [exact SR|]. split; [exact UR|]. split; [apply (d_cell m4 X Dx _ SX)|]. split; [apply (d_cell m4 Y Dy _ SY)|].
        split; [subst la; apply limbs_at_firstn; exact UX|]. split; [subst lb; apply limbs_at_firstn; exact UY|]. split; [exact ST4 | exact MI4].
      - apply (bn_mul_part_recursive_ufinal CS8 CS8_0 comba8_ok).
      - unfold part_ustack, rec_ustack, kara_uleaf. clear - HKJ CS8_0 CS8_max. lia.
      - unfold mulc_tpre. rewrite LLA, LLB. unfold GLOBALS_TOP in *.
        split; [exact LMT|]. split; [apply (d_cell m4 TT Dt _ STT)|].
        split; [apply limbs_at_of_u64arr; exact UT|].
        split; [apply (limbarr_limbs_at usegs) in UT; exact (proj2 UT)|].
        split; [clear - DT0 DTC CEIL; unfold bn_dmax in *; lia|]. split; [clear - S4; unfold bn_dmax in *; lia|].
        split; [clear - DTX TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - DTY TDY EBL; unfold bn_dmax in *; lia|].
        split; [clear - DRT; unfold bn_dmax in *; lia|].
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st4 OW4 LB m4 ls4 AD t TT HEAP4 (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS4))) HT4))|].
        apply (bn_arr_ualign st4 OW4 LB m4 Dt tb 1 HEAP4 ARRT). clear - HDM3 PJ. unfold bn_dmax in *. lia.
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
    eapply (mul_finish2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb st4 ls4 m4 OW4 rr t x y R TT X Y Dr Dt
              (8 * Z.of_nat (4 * j)) 9216 ro to (al + bl)%nat) in PO;
      [ | exact ENV4 | exact LS4 | exact CEIL | exact GLO | lia | lia | exact SPB | exact HR4 | exact HT4 | exact HX4 | exact HY4
        | exact NEX | exact NEY | exact NTR | exact NTX | exact NTY | exact SR | exact ARR | exact STT | exact ARRT
        | exact LRO | | | | exact LTO | | ].
    - rewrite EGX, EGY in PO. fold br tb in PO. unfold mul_res in PO. exact PO.
    - rewrite NRO, LRl. fold br. clear - HD2 PJ. lia.
    - fold br. clear - HDM4 HAL2 HBL2. lia.
    - rewrite NRO, LRl. reflexivity.
    - rewrite NTO. reflexivity.
    - fold tb. clear - HDM3 PJ. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mul_path_kara : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (st1 : PState) (ls1 : lstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z) (al bl : nat)
      (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x25 x26 x27 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st1 ls1 m1 OW1 ->
    lib_state ls1 m1 OW1 AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B ->
    ref_at ls1 OW1 AD rr R -> ref_at ls1 OW1 AD x X -> ref_at ls1 OW1 AD y Y -> rr <> x -> rr <> y ->
    nonpool rr -> nonpool x -> nonpool y ->
    al = bn_top (getbn x ls1) -> bl = bn_top (getbn y ls1) ->
    (16 <= al)%nat -> (16 <= bl)%nat -> (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
    implM usegs (interp (embed (disp_kara rr (firstn al (bn_buf (getbn x ls1))) (firstn bl (bn_buf (getbn y ls1))) al bl (al + bl)
                                  (Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1)) ls1))) st1
      (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
                (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 (Z_to_bv 64 (Z.of_nat al - Z.of_nat bl))
               a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
               (Z_to_bv 64 (Z.of_nat bl)) x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x116dd0) fc None m1 (seg_rom usegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR HX HY NEX NEY NPR NPX NPY EAL EBL HA16 HB16 HAB HBA.
    pose proof LO as LO'. unfold BN_MUL_FIXED_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPC.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK1).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
    pose proof (st_okm_getbn x ls1 SOK1 HVX) as (_ & TDX & DMX & _). pose proof (st_okm_getbn y ls1 SOK1 HVY) as (_ & TDY & DMY & _).
    unfold BN_WORDS_MAX in DMX, DMY.
    assert (AL23 : Z.of_nat al < 8388608) by (clear - EAL TDX DMX; unfold bn_dmax in *; lia).
    assert (BL23 : Z.of_nat bl < 8388608) by (clear - EBL TDY DMY; unfold bn_dmax in *; lia).
    pose proof (kara_kj_facts al bl HA16 HB16 HAB HBA AL23 BL23) as KF. cbv zeta in KF.
    set (mx := Nat.max al bl) in *. set (kj := Z.to_nat (num_bits_word (Z.of_nat mx) - 1)) in *. destruct KF as (HKJ & HJ1 & HJ2 & EKJ).
    set (j := Nat.pow 2 kj) in *.
    assert (EJ : Z.of_nat j = 2 ^ Z.of_nat kj) by (subst j; rewrite Nat2Z.inj_pow; reflexivity).
    assert (PJ : Z.of_nat j <= 8388608) by (clear - HJ1 AL23 BL23; subst mx; lia).
    (* [comment removed for export] *)
    assert (CONT : forall w, w = Z_to_bv 64 (Z.of_nat mx) ->
      implM usegs (interp (embed (disp_kara rr (firstn al (bn_buf (getbn x ls1))) (firstn bl (bn_buf (getbn y ls1))) al bl (al + bl) kj ls1))) st1
        (mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
                  (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) w (Z_to_bv 64 (Z.of_nat al - Z.of_nat bl))
                 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat al))
                 (Z_to_bv 64 (Z.of_nat bl)) x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x116ddc) fc None m1 (seg_rom usegs))).
    2:{ unfold implM. iprefix. zstep. zstep. rewrite lts_signed by (clear - AL23 BL23; lia). if_cases KI; zify_cond KI.
        - ihere. to_implM. apply CONT. f_equal. subst mx. clear - KI. lia.
        - zstep. ihere. to_implM. apply CONT. f_equal. subst mx. clear - KI. lia. }
    intros w ->.
    pose proof ENV as (HEAP1 & _ & ST1 & (errv1 & ERR1) & MI1 & _ & _ & _ & _ & FR1 & FSZ1).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    unfold implM. iprefix. zstep.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (BN_num_bits_word_uspec (Z_to_bv 64 1142240) (Z_to_bv 64 (bv_unsigned sp + -112))) with (lo := lo);
        [rewrite ESP; exact ST1 | rewrite ESP; lia | exact MI1]. }
    intros ms' (n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & n8 & n9 & n10 & n11 & n12 & n13 & mN & -> & MUn & WMn & MIn & STn).
    rewrite ESP in MUn, STn. rewrite (unsigned_lit (Z.of_nat mx)) by (clear - AL23 BL23; subst mx; lia).
    replace (ret_pc (Z_to_bv 64 1142240)) with (Z_to_bv 64 1142240) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (HWLn : Forall (w_lib OW1 lo (bv_unsigned sp)) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112)]) by (constructor; [left; cbn [fst snd]; lia | constructor]).
    assert (WOKn : Forall (w_ok OW1 LB ls1 AD EA []) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112)]) by (constructor; [apply w_stack; cbn; lia | constructor]).
    pose proof (lib_state_frame st1 LB [] ls1 m1 mN OW1 AD EA _ HEAP1 LS MUn WMn WOKn) as LSn.
    assert (ENVn : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) st1 ls1 mN OW1).
    { eapply (cenv_silent LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO FBlo FBsp SPB) with (errv' := errv1);
        [exact ENV | exact MUn | exact WMn | exact HWLn | exact STn | | exact MIn | | exact FSZ1].
      - eapply rw_cells_transport; [exact ERR1 | exact MUn | exact WMn |]. unfold LX_ERRNO, RATP, GLOBALS_TOP in *. cbn. lia.
      - eapply rw_cells_transport; [exact FR1 | exact MUn | exact WMn |]. cbn. lia. }
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
    do 2 zstep.
    (* [comment removed for export] *)
    destruct SOK1 as (_ & _ & _ & _ & _ & _ & (_ & _ & CKPS & _)).
    destruct (CPRE _ _ _ _ _ BN_CTX_GET_STACK ENVn LSn ltac:(unfold BN_CTX_GET_STACK; lia)) as (errv2 & PRE2).
    ihere. to_implM. unfold disp_kara. unfold bbind at 1. cbn [bind tree_ops]. fold j.
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (BN_CTX_get_leaves ls1 CKPS)|].
      eapply (BN_CTX_get_walk HM) with (lo := lo) (B := B) (errv := errv2) (OW := OW1) (LB := LB) (AD := AD) (EA := EA); [exact PRE2 | reflexivity | reflexivity]. }
    cbv beta. intros [t ls2] st2 ms2 [PO LEAF]. apply BPC in PO. cbn [fst snd] in PO, LEAF.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & -> & CP2 & ((TT & HT & ->) & _)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENVn CP2) as (ENV2 & LS2).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -112) _ _ _ _ _ _ _ _ CP2) as RS2.
    replace (ret_pc (Z_to_bv 64 1142284)) with (Z_to_bv 64 1142284) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS2 _ _ HR) as HR2. pose proof (RS2 _ _ HX) as HX2. pose proof (RS2 _ _ HY) as HY2.
    unfold get_leaf in LEAF. cbn [fst snd] in LEAF. destruct LEAF as (ET & _ & _ & LOTH).
    assert (NTR : t <> rr) by (rewrite ET; intros E; symmetry in E; exact (NPR _ E)).
    assert (NTX : t <> x) by (rewrite ET; intros E; symmetry in E; exact (NPX _ E)).
    assert (NTY : t <> y) by (rewrite ET; intros E; symmetry in E; exact (NPY _ E)).
    assert (EGX : getbn x ls2 = getbn x ls1) by (apply LOTH; rewrite <- ET; congruence).
    assert (EGY : getbn y ls2 = getbn y ls1) by (apply LOTH; rewrite <- ET; congruence).
    clear PRE2 CP2 ENVn LSn CKPS.
    (* [comment removed for export] *)
    destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (_ & ADB2 & _ & _).
    destruct (ref_at_inb _ _ _ _ _ ADB2 HT) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV2) Hint) as (TA0 & _ & _ & TAC & _).
    unfold MallocRep.wz. unfold implM. iprefix.
    zstep. if_cases KT; zify_cond KT; [exfalso; clear - KT TA0 Rt1 TAC Rt2; lia|]. clear KT.
    zstep.
    assert (EAL2 : al = bn_top (getbn x ls2)) by (rewrite EGX; exact EAL).
    assert (EBL2 : bl = bn_top (getbn y ls2)) by (rewrite EGY; exact EBL).
    rewrite <- EGX, <- EGY.
    zstep. if_cases KA; zify_cond KA.
    { (* [comment removed for export] *)
      replace ((j <? al)%nat || (j <? bl)%nat) with true by (symmetry; apply orb_true_iff; left; apply Nat.ltb_lt; clear - KA; lia).
      ihere. to_implM.
      eapply mul_path_part; try eassumption; [clear - HKJ; lia | clear - KA; lia | subst mx; clear - KA HAB HBA; lia | subst mx; clear - HJ2; lia | subst mx; clear - HJ2; lia]. }
    zstep. if_cases KB'; zify_cond KB'.
    { (* [comment removed for export] *)
      replace ((j <? al)%nat || (j <? bl)%nat) with true by (symmetry; apply orb_true_iff; right; apply Nat.ltb_lt; clear - KB'; lia).
      ihere. to_implM.
      eapply mul_path_part; try eassumption; [clear - HKJ; lia | subst mx; clear - KB' HAB HBA; lia | clear - KB'; lia | subst mx; clear - HJ2; lia | subst mx; clear - HJ2; lia]. }
    (* [comment removed for export] *)
    replace ((j <? al)%nat || (j <? bl)%nat) with false by (symmetry; apply orb_false_iff; split; apply Nat.ltb_ge; [clear - KA | clear - KB']; lia).
    ihere. to_implM.
    eapply mul_path_rec; try eassumption; [clear - HKJ; lia | clear - KA; lia | clear - KB'; lia | subst mx; clear - HJ1 KA KB' HAB HBA; lia | subst mx; clear - HJ1 KA KB' HAB HBA; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma mul_zero_path : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (jb : list byte) (m1 : mem) (rr : bnref) (R : Z)
      (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) s ls m1 OW ->
    lib_state ls m1 OW AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_MUL_FIXED_STACK -> bv_unsigned sp <= B ->
    ref_at ls OW AD rr R ->
    evt usegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1)
                       (tt, setbn rr (bn_zero_pure (getbn rr ls)) ls) s)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz RATP) t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x116da8) fc None m1 (seg_rom usegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR.
    unfold BN_MUL_FIXED_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    pose proof ENV as (HEAP & _ & ST & (errv & ERR) & MI & _ & _ & _ & _ & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3063488 - 164) with 3063324 in ERR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] ls m1 OW AD EA rr R LS ND HR ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (bn_arr_facts s OW LB m1 HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR).
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    set (b := getbn rr ls) in *.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    unfold GLOBALS_TOP in GLO.
    zstep. zstep.
    eapply evt_cut.
    { eapply (BN_zero_ex_spec (Z_to_bv 64 1142192) (Z_to_bv 64 (bv_unsigned sp + -112))) with (A := R) (D := Dr) (b := b) (lo := lo);
        [exact SR | exact (ref_at_ualign s OW LB m1 ls AD rr R HEAP ADB HR) | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; lia | reflexivity]. }
    intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MUz & WMz & MIz & STz & SRz).
    rewrite ESP in MUz, STz.
    replace (ret_pc (Z_to_bv 64 1142192)) with (Z_to_bv 64 1142192) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112); (R, R + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [|constructor].
      right. exists (qs, As, ns). cbn [blk_addr blk_size fst snd]. split; [exact Hins | lia]. }
    assert (WOK : Forall (w_ok OW LB ls AD EA [rr]) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112); (R, R + 24)]).
    { constructor; [apply w_stack; cbn; lia|]. constructor; [|constructor].
      eapply (w_struct OW LB ls AD EA false [rr] _ rr R); [left; reflexivity | exact HR | cbn; lia | cbn; lia]. }
    assert (ENV3 : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
                        s (setbn rr (bn_zero_pure b) ls) m3 OW).
    { apply cenv_setbn.
      eapply (cenv_silent LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL ltac:(unfold GLOBALS_TOP; lia) FBlo FBsp SPB) with (errv' := errv);
        [exact ENV | exact MUz | exact WMz | exact HWL | exact STz | | exact MIz | | exact FSZ].
      - eapply rw_cells_transport; [exact ERR | exact MUz | exact WMz |]. unfold LX_ERRNO, RATP. cbn. lia.
      - eapply rw_cells_transport; [exact FR | exact MUz | exact WMz |]. cbn. lia. }
    assert (LS3 : lib_state (setbn rr (bn_zero_pure b) ls) m3 OW AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls m3 OW AD EA rr R); [| exact ND | exact HR | | |].
      - eapply lib_state_frame; [exact HEAP | exact LSH | exact MUz | exact WMz | exact WOK].
      - exists Dr. split; [exact SRz|]. eapply bn_arr_of_u64arr; [exact ARR|].
        eapply u64arr_transport; [exact U | exact MUz | exact WMz |]. cbn [disjoint_from]. rewrite LENW. lia.
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bn_okm, bn_zero_pure, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. repeat split; [exact O1 | lia | exact O3 | exact O4].
      - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
    pose proof (cenv_final LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m _ _ _ _ _ ENV3 LS3)
      as (F1 & F2 & F3 & (errvF & F4) & F5 & F6 & F7 & F8 & F9).
    pose proof ENV3 as (_ & _ & STF & _ & MIF & _ & _ & _ & _ & FRF & _). unfold mul_frame in FRF.
    clear SR U MUz WMz MIz STz SRz FR ST MI ERR.
    do 3 zstep. do 13 zstep.
    release_frame FRF STF (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold bn_post. do 15 eexists. exists m3, OW, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. reflexivity.
  Qed.

  Lemma bn_mul_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rr x y : bnref) (R X Y : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_MUL_FIXED_STACK -> tp = wz RATP ->
    ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y ->
    a0 = wz R -> a1 = wz X -> a2 = wz Y -> a3 = wz (ad_ctx AD) ->
    nonpool rr -> nonpool x -> nonpool y ->
    implM usegs (interp (embed (bn_mul_fixed_top (tree_ops bptr) rr x y ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_FIXED_TOP) fc None m (seg_rom usegs)).
  Proof.
    intros until Y. intros PRE -> HR HX HY -> -> -> -> NPR NPX NPY.
    pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
    unfold BN_MUL_FIXED_STACK in LO.
    unfold BN_MUL_FIXED_TOP, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (open_ro_u s OW LB m ls AD EA x X HEAP LS HX) as (Dx0 & SX & OKX & _ & X0 & XC & _ & _ & ALX0 & _).
    destruct (open_ro_u s OW LB m ls AD EA y Y HEAP LS HY) as (Dy0 & SY & OKY & _ & Y0 & YC & _ & _ & ALY0 & _).
    pose proof OKX as (_ & TDX & DMX & _). pose proof OKY as (_ & TDY & DMY & _). unfold BN_WORDS_MAX in DMX, DMY.
    unfold bn_cells, MallocRep.wz in SX, SY.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3063488 - 164) with 3063324 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    unfold bn_mul_fixed_top. unfold bbind at 1 2. unfold bget at 1 2. cbn [bind ret tree_ops tbind fst snd].
    set (al := bn_top (getbn x ls)) in *. set (bl := bn_top (getbn y ls)) in *.
    assert (AL23 : Z.of_nat al < 8388608) by (clear - TDX DMX; unfold bn_dmax in *; lia).
    assert (BL23 : Z.of_nat bl < 8388608) by (clear - TDY DMY; unfold bn_dmax in *; lia).
    unfold implM. iprefix.
    carve_frame 112%nat ST. do 15 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL0 : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -112, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK0) as LS0.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jbv :: _) =>
      assert (ENV : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m (mul_frame jbv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) s ls m1 OW);
      [| set (jb := jbv) in * ]
    end.
    { unfold cenv, mul_frame. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL0 SPB); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL0 CEIL GLO'); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (LOF : lo <= bv_unsigned sp - BN_MUL_FIXED_STACK) by (unfold BN_MUL_FIXED_STACK; lia).
    chk ltac:(fun C => clear - C X0 XC; lia).
    do 3 zstep. rewrite (land7 X (hide_elim _ ALX0)). chk_lit.
    zstep.
    chk ltac:(fun C => clear - C Y0 YC; lia).
    zstep. rewrite (land7 Y (hide_elim _ ALY0)). chk_lit.
    zstep. rewrite (sx32_small (Z.of_nat al)) by (clear - AL23; lia).
    zstep. if_cases KA0; zify_cond KA0.
    { (* [comment removed for export] *)
      replace ((al =? 0)%nat || (bl =? 0)%nat) with true by (symmetry; apply orb_true_iff; left; apply Nat.eqb_eq; clear - KA0; lia).
      ihere. to_implM. unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
      eapply mul_zero_path; [exact ENV | exact LS0 | exact CEIL | exact GLO' | exact LOF | exact SPB | exact HR]. }
    zstep. rewrite (sx32_small (Z.of_nat bl)) by (clear - BL23; lia).
    zstep. if_cases KB0; zify_cond KB0.
    { (* [comment removed for export] *)
      replace ((al =? 0)%nat || (bl =? 0)%nat) with true by (symmetry; apply orb_true_iff; right; apply Nat.eqb_eq; clear - KB0; lia).
      ihere. to_implM. unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
      eapply mul_zero_path; [exact ENV | exact LS0 | exact CEIL | exact GLO' | exact LOF | exact SPB | exact HR]. }
    replace ((al =? 0)%nat || (bl =? 0)%nat) with false by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; [clear - KA0 | clear - KB0]; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat al + Z.of_nat bl)) by (clear - AL23 BL23; lia).
    zstep.
    chk ltac:(fun C => clear - C; lia).
    do 3 zstep.
    (* [comment removed for export] *)
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO' FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s ls OW m CEIL GLO' FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPC.
    destruct (CPRE _ _ _ _ _ BN_CTX_START_STACK ENV LS0 ltac:(unfold BN_CTX_START_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (BN_CTX_start_leaves ls)|].
      eapply (BN_CTX_start_walk HM) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (AD := AD) (EA := EA); [exact PRE1 | reflexivity | reflexivity]. }
    cbv beta. intros [u1 ls1] st1 ms1 [PO LEAF1]. apply BPC in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & -> & CP1 & _).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP1) as (ENV1 & LS1).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -112) _ _ _ _ _ _ _ _ CP1) as RS1.
    replace (ret_pc (Z_to_bv 64 1142076)) with (Z_to_bv 64 1142076) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS1 _ _ HR) as HR1. pose proof (RS1 _ _ HX) as HX1. pose proof (RS1 _ _ HY) as HY1.
    unfold start_leaf in LEAF1. cbn [fst snd] in LEAF1. destruct LEAF1 as (EG1 & _).
    clear PRE1 CP1 ENV LS0 SX SY.
    (* [comment removed for export] *)
    cbn [fst snd]. unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind with (Q1 := mul_join ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
                                            (bn_neg (getbn x ls)) (bn_neg (getbn y ls))).
    2:{ cbv beta. intros [uE lsE] stE msE J. cbn [fst snd].
        unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
        eapply (mul_end ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B jb rr x y R X Y
                  (bn_neg (getbn x ls)) (bn_neg (getbn y ls)) (uE, lsE) stE msE CEIL GLO' LOF SPB J). }
    (* [comment removed for export] *)
    pose proof ENV1 as (HEAP1 & _).
    destruct (lib_state_h_parts _ _ _ _ _ _ LS1) as (IDS1 & ADB1 & _ & _).
    destruct (ref_at_inb _ _ _ _ _ ADB1 HR1) as (qr & Ar & nr & _ & Hinr & Rr1 & Rr2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP1 Hinr) as (RA0 & _ & _ & RAC & _).
    destruct (ref_at_inb _ _ _ _ _ ADB1 HX1) as (qx & Ax & nx & _ & Hinx & Rx1 & Rx2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP1 Hinx) as (XA0 & _ & _ & XAC & _).
    destruct (ref_at_inb _ _ _ _ _ ADB1 HY1) as (qy & Ay & ny & _ & Hiny & Ry1 & Ry2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP1 Hiny) as (YA0 & _ & _ & YAC & _).
    unfold implM. iprefix.
    zstep. if_cases KRX; zify_cond KRX.
    { assert (E : rr = x).
      { destruct (bnref_eq_dec rr x) as [E|NE]; [exact E|exfalso].
        pose proof (struct_disj st1 OW1 LB m2 HEAP1 ls1 AD EA IDS1 ADB1 rr x R X NE HR1 HX1) as SD.
        clear - KRX SD. lia. }
      subst x. replace (bnref_eqb rr rr) with true by (clear; destruct rr; cbn; try reflexivity; symmetry; apply Nat.eqb_refl).
      ihere. to_implM. cbn [orb bunr unreachable tree_ops embed interp]. apply implM_interp_unr. }
    assert (NEX : rr <> x) by (intros E; subst x; apply KRX; rewrite (ref_at_fun _ _ _ _ _ _ (RH_nodup_l _ _ _ _ HEAP1) HR1 HX1); reflexivity).
    zstep.
    zstep. if_cases KRY; zify_cond KRY.
    2:{ assert (E : rr = y).
      { destruct (bnref_eq_dec rr y) as [E|NE]; [exact E|exfalso].
        pose proof (struct_disj st1 OW1 LB m2 HEAP1 ls1 AD EA IDS1 ADB1 rr y R Y NE HR1 HY1) as SD.
        clear - KRY SD. lia. }
      subst y. replace (bnref_eqb rr rr) with true by (clear; destruct rr; cbn; try reflexivity; symmetry; apply Nat.eqb_refl).
      ihere. to_implM. rewrite orb_true_r. cbn [bunr unreachable tree_ops embed interp]. apply implM_interp_unr. }
    assert (NEY : rr <> y) by (intros E; subst y; apply KRY; rewrite (ref_at_fun _ _ _ _ _ _ (RH_nodup_l _ _ _ _ HEAP1) HR1 HY1); reflexivity).
    rewrite (bnref_eqb_neq rr x NEX), (bnref_eqb_neq rr y NEY). cbn [orb].
    clear KRX KRY.
    assert (EAL1 : al = bn_top (getbn x ls1)) by (rewrite EG1; reflexivity).
    assert (EBL1 : bl = bn_top (getbn y ls1)) by (rewrite EG1; reflexivity).
    rewrite <- (EG1 x), <- (EG1 y).
    (* [comment removed for export] *)
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
        (* [comment removed for export] *)
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
    { (* [comment removed for export] *)
      assert (KU' : ~ (0 <= Z.of_nat al - Z.of_nat bl + 1 <= 2)).
      { intros H. apply (land64_le_small (Z.of_nat al - Z.of_nat bl + 1) 2 ltac:(clear - AL23 BL23; lia) ltac:(lia)) in H. clear - H KU. lia. }
      replace ((16 <=? al)%nat && (16 <=? bl)%nat && (al <=? bl + 1)%nat && (bl <=? al + 1)%nat) with false.
      2:{ symmetry. apply andb_false_iff. destruct (Nat.leb_spec bl (al + 1)) as [H1|H1]; [|right; reflexivity].
          left. apply andb_false_iff. right. apply Nat.leb_gt. clear - KU' H1. lia. }
      ihere. to_implM. eapply mul_path_normal; eassumption. }
    (* [comment removed for export] *)
    assert (KU' : 0 <= Z.of_nat al - Z.of_nat bl + 1 <= 2) by (apply (land64_le_small (Z.of_nat al - Z.of_nat bl + 1) 2 ltac:(clear - AL23 BL23; lia) ltac:(lia)); exact KU).
    replace ((16 <=? al)%nat && (16 <=? bl)%nat && (al <=? bl + 1)%nat && (bl <=? al + 1)%nat) with true.
    2:{ symmetry. rewrite !andb_true_iff. repeat split; apply Nat.leb_le; [clear - K16A | clear - K16B | clear - KU' | clear - KU']; lia. }
    ihere. to_implM.
    eapply mul_path_kara; try eassumption; [clear - K16A; lia | clear - K16B; lia | clear - KU'; lia | clear - KU'; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma mul_ctop_call : forall (POST : machine_state -> Prop) (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B SPv FB : Z)
      (s0 : PState) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem) (fr : list cell)
      (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= FB - 16 -> FB <= SPv -> SPv <= B -> SPv < 2^64 ->
    cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st (setbn r (bn_correct_top_pure (getbn r ls)) ls) m' OW ->
        lib_state (setbn r (bn_correct_top_pure (getbn r ls)) ls) m' OW AD EA ->
        evt usegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom usegs))) ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_CORRECT_TOP) fc None m (seg_rom usegs)).
  Proof.
    intros until fc. intros CEIL GLO' LOFB FBSP SPB SPR ENV LS HA K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW AD EA r ar LS ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts st OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & _ & D0 & DC & DI & SEP). fold b in U, DC, DI, SEP.
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & AI).
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; lia).
    unfold LX_ERRNO, RATP in ERR. change (3063488 - 164) with 3063324 in ERR. unfold BN_WORDS_MAX in OK3. unfold GLOBALS_TOP in GLO'.
    eapply evt_cut.
    { eapply bn_correct_top_spec with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | exact (ref_at_ualign st OW LB m ls AD r ar HEAP ADB HA) | exact (bn_arr_ualign st OW LB m D b (bn_top b) HEAP ARR OK2) | exact U | exact OK1 | exact OK2 | lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia | rewrite ESP; left; lia | exact SEPr | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    assert (U' : u64arr usegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [left; lia|]. split; [lia| exact I]. }
    eapply (rw_cells_transport usegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; lia|]; split; [right; lia| exact I]].
    eapply (rw_cells_transport usegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia|]; split; [lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls AD EA [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst]; lia|].
      constructor; [eapply (w_struct OW LB ls AD EA false [r] _ r ar); [left; reflexivity| exact HA| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib OW lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [right; exists (q, A, n); cbn; auto| constructor]. }
    assert (LS' : lib_state (setbn r (bn_correct_top_pure b) ls) m' OW AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW AD EA r ar); [| exact ND | exact HA | | |].
      - exact (lib_state_frame st LB [r] ls m m' OW AD EA _ HEAP LSH MUc WMc WOK).
      - exists D. split; [exact RES|]. unfold bn_arr in *. unfold bn_correct_top_pure, bn_dmax in *. cbn [bn_d bn_buf].
        destruct (bn_d b) as [p|]; [split; [exact (proj1 ARR)| exact U'] | exact ARR].
      - destruct (strip_top_spec (bn_buf b) (bn_top b) OK2) as (S1 & _ & _).
        unfold bn_okm, bn_correct_top_pure, bn_dmax, BN_WORDS_MAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [lia|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact IDS | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbn.
    eapply (cenv_silent LB AD lo B SPv FB s0 ls0 OW0 m0 CEIL ltac:(unfold GLOBALS_TOP; exact GLO') ltac:(lia) FBSP SPB fr fr);
      [exact ENV | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR | exact FSZ].
  Qed.


  Lemma BN_mul_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rr x y : bnref) (R X Y : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_MUL_STACK -> tp = wz RATP ->
    ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y ->
    a0 = wz R -> a1 = wz X -> a2 = wz Y -> a3 = wz (ad_ctx AD) ->
    nonpool rr -> nonpool x -> nonpool y ->
    implM usegs (interp (embed (BN_mul (tree_ops bptr) rr x y ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL) fc None m (seg_rom usegs)).
  Proof.
    intros until Y. intros PRE -> HR HX HY -> -> -> -> NPR NPX NPY.
    pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
    unfold BN_MUL_STACK, BN_MUL_FIXED_STACK in LO.
    unfold BN_MUL, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3063488 - 164) with 3063324 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    unfold BN_mul. unfold bbind at 1. cbn [bind tree_ops].
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 6 zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL0 : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK0) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -32) s ls OW m fr s ls m1 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL0 SPB); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL0 CEIL GLO'); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -32) by lia.
    assert (FBsp : bv_unsigned sp + -32 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s ls OW m CEIL GLO' FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s ls OW m CEIL GLO' FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) CEIL FBlo FBsp SPR2 A) as BPC.
    clear HEAP LS AUX ST ERR MI MU WM HWL0 WOK0 FR PRE.
    (* [comment removed for export] *)
    destruct (CPRE _ _ _ _ _ BN_MUL_FIXED_STACK ENV LS0 ltac:(unfold BN_MUL_FIXED_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply bn_mul_fixed_top_walk with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (AD := AD) (EA := EA)
        (rr := rr) (x := x) (y := y) (R := R) (X := X) (Y := Y);
        [exact PRE1 | reflexivity | exact HR | exact HX | exact HY | reflexivity | reflexivity | reflexivity | reflexivity | exact NPR | exact NPX | exact NPY]. }
    cbv beta. intros [[] ls2] st2 ms2 PO. apply BPC in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & -> & CP & ->).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV2 & LS2).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -32) _ _ _ _ _ _ _ _ CP) as RS.
    replace (ret_pc (Z_to_bv 64 1141900)) with (Z_to_bv 64 1141900) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS _ _ HR) as HR2.
    (* [comment removed for export] *)
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_interp_ret.
    unfold MallocRep.wz. do 3 zstep.
    eapply (mul_ctop_call _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -32)); [exact CEIL | exact GLO' | lia | exact FBsp | exact SPB | exact SPR2 | exact ENV2 | exact LS2 | exact HR2 |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1141912)) with (Z_to_bv 64 1141912) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (cenv_final LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s ls OW m _ _ _ _ _ ENV3 LS3)
      as (F1 & F2 & F3 & (errvF & F4) & F5 & F6 & F7 & F8 & F9).
    pose proof ENV3 as (_ & _ & STF & _ & MIF & _ & _ & _ & _ & FRF & _).
    zstep. do 4 zstep.
    release_frame FRF STF (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold bn_post. do 15 eexists. exists m3, OW2, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
