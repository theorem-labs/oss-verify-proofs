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
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnAddSpec BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface W_expand BnCall.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnUAlign.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure W_uadd_core.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAU Require Import BnAKit BnAUKit W_uadd_core.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Local Notation ops := (tree_ops bptr).

(* [comment removed for export] *)
Definition uadd_rest (rr x y : bnref) (max min : nat) : BM (M := btree bptr) unit :=
  bbind ops (bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_top r max))) (fun _ =>
  bbind ops (if (max =? 0)%nat then bret ops tt
             else bbind ops (bget ops x) (fun a => bbind ops (bget ops y) (fun b => bbind ops (bget ops rr) (fun r =>
                  let '(s, carry) := add_words (firstn min (bn_buf a)) (firstn min (bn_buf b)) in
                  let '(s2, carry) := add_carry_words (slice (bn_buf a) min (max - min)) carry in
                  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 (s ++ s2 ++ [carry])) (max + Z.to_nat carry) (bn_neg r) (bn_flags r))))))
    (fun _ => bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_neg r false)))).

Lemma uadd_body_eq : forall rr x y (ls : lstate bptr),
  uadd_body rr x y ls =
  tbind (bn_wexpand ops rr (bn_top (getbn x ls) + 1) ls) (fun p => uadd_rest rr x y (bn_top (getbn x ls)) (bn_top (getbn y ls)) (snd p)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma buf_after_top : forall rr x (ls : lstate bptr) t, valid_refm rr ls ->
  bn_buf (getbn x (setbn rr (bn_with_top (getbn rr ls) t) ls)) = bn_buf (getbn x ls).
Proof.
  intros rr x ls t HV. destruct (bnref_eq_dec rr x) as [->|NE].
  - rewrite getbn_setbn_same_m by exact HV. reflexivity.
  - rewrite getbn_setbn_other by exact NE. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma uadd_rest_eq : forall rr x y (ls : lstate bptr) max min,
  valid_refm rr ls -> (min <= max)%nat -> (max <= length (bn_buf (getbn x ls)))%nat -> (min <= length (bn_buf (getbn y ls)))%nat ->
  uadd_rest rr x y max min ls =
  TRet (tt, setbn rr (uadd_bn (getbn rr ls) (firstn max (bn_buf (getbn x ls))) (firstn min (bn_buf (getbn y ls)))) ls).
Proof.
  intros rr x y ls max min HV Hmm Hx Hy.
  unfold uadd_rest, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
  set (ls1 := setbn rr (bn_with_top (getbn rr ls) max) ls).
  assert (HV1 : valid_refm rr ls1) by (apply valid_refm_setbn; exact HV).
  assert (LA : length (firstn max (bn_buf (getbn x ls))) = max) by (apply firstn_length_le; exact Hx).
  assert (LB : length (firstn min (bn_buf (getbn y ls))) = min) by (apply firstn_length_le; exact Hy).
  unfold uadd_bn, uadd_top, uadd_buf. rewrite LA.
  destruct (Nat.eqb_spec max 0) as [E0|N0].
  - cbn [tbind fst snd]. subst ls1. rewrite getbn_setbn_same_m by exact HV. rewrite setbn_setbn_same.
    unfold bn_with_neg, bn_with_top. cbn [bn_d bn_buf bn_top bn_neg bn_flags]. rewrite E0. reflexivity.
  - assert (EA : bn_buf (getbn x ls1) = bn_buf (getbn x ls)) by (apply buf_after_top; exact HV).
    assert (EB : bn_buf (getbn y ls1) = bn_buf (getbn y ls)) by (apply buf_after_top; exact HV).
    rewrite EA, EB. rewrite (slice_of_firstn (bn_buf (getbn x ls)) min max Hmm).
    unfold uadd_lists. rewrite LB. rewrite firstn_firstn, Nat.min_l by exact Hmm.
    destruct (add_words (firstn min (bn_buf (getbn x ls))) (firstn min (bn_buf (getbn y ls)))) as [sv cv].
    destruct (add_carry_words (skipn min (firstn max (bn_buf (getbn x ls)))) cv) as [sv2 cv2].
    cbn [tbind fst snd]. subst ls1. rewrite !getbn_setbn_same_m by (try apply valid_refm_setbn; exact HV). rewrite !setbn_setbn_same.
    unfold bn_with_neg, bn_with_top. cbn [bn_d bn_buf bn_top bn_neg bn_flags fst snd]. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wexpand_res_top : forall r words (ls ls' : lstate bptr) x, wexpand_res r words ls ls' -> valid_refm r ls ->
  bn_top (getbn x ls') = bn_top (getbn x ls).
Proof.
  intros r words ls ls' x [[_ ->]|[_ [pn ->]]] HV; [reflexivity|].
  destruct (bnref_eq_dec r x) as [->|NE]; [rewrite getbn_setbn_same_m by exact HV; reflexivity | rewrite getbn_setbn_other by exact NE; reflexivity].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_UADD : Z := 0x119c04.
Definition BN_UADD_STACK : Z := 64 + BN_WEXPAND_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  (* [comment removed for export] *)
  Definition uarith_res (rr : bnref) (ls : lstate bptr) (OW : list block) : unit -> lstate bptr -> list block -> word -> Prop :=
    fun _ ls' OW' a0' => a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rr ls) <> Some q -> In (q, A, n) OW').

  (* [comment removed for export] *)
  Lemma uadd_tail : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B : Z)
      (m1 : mem) (rr x y : bnref) (R X Y : Z)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 t3 t4 t5 t6 : word),
    cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] s ls m1 OW ->
    lib_state ls m1 OW AD EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_UADD_STACK -> bv_unsigned sp <= B ->
    ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y ->
    (bn_top (getbn y ls) <= bn_top (getbn x ls))%nat ->
    implM usegs (interp (embed (uadd_body rr x y ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (uarith_res rr ls OW))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 R) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 X) x19 (Z_to_bv 64 Y) x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x119c68) fc None m1 (seg_rom usegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB HR HX HY HTOPS.
    unfold BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -64) by lia.
    assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m CEIL GLO FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m CEIL GLO FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPC.
    (* [comment removed for export] *)
    pose proof ENV as (HEAP1 & _ & ST1 & _ & MI1 & _).
    destruct (open_ro s OW LB m1 ls AD EA x X HEAP1 LS HX) as (Dx0 & SX & OKX & _ & X0 & XC & _).
    destruct (open_ro s OW LB m1 ls AD EA y Y HEAP1 LS HY) as (Dy0 & SY & OKY & _ & Y0 & YC & _).
    pose proof OKX as (_ & TDX & DMX & _). pose proof OKY as (_ & TDY & DMY & _). unfold BN_WORDS_MAX in DMX, DMY.
    unfold bn_cells, MallocRep.wz in SX, SY.
    set (max := bn_top (getbn x ls)) in *. set (min := bn_top (getbn y ls)) in *.
    unfold implM. iprefix.
    zstep. rewrite (sx32_small (Z.of_nat max)) by (clear - TDX DMX; unfold bn_dmax in *; lia).
    zstep. rewrite (sx32_small (Z.of_nat min)) by (clear - TDY DMY; unfold bn_dmax in *; lia).
    zstep.
    zstep. rewrite (bn_swrap32_small (Z.of_nat max - Z.of_nat min)) by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
    replace (Z.of_nat max + - Z.of_nat min)%Z with (Z.of_nat max - Z.of_nat min)%Z by (clear; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat max + 1)) by (clear - TDX DMX; unfold bn_dmax in *; lia).
    zstep. rewrite lts_small by (clear - TDX DMX; unfold bn_dmax in *; lia). if_cases C; [exfalso; zify_cond C; clear - C; lia | clear C].
    zstep. zstep.
    (* [comment removed for export] *)
    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
 rewrite uadd_body_eq. fold max min.
    eapply implM_embed_bind.
    { eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (AD := AD) (EA := EA)
        (r := rr) (a := R) (words := (max + 1)%nat);
        [exact PRE1 | reflexivity | exact HR | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - TDX DMX; unfold bn_dmax in *; lia]. }
    cbv beta. intros [u1 ls1] st1 ms1 PO.
 apply BPC in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & -> & CP & (-> & HDM & WRES & STAB)).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -64) _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1154188)) with (Z_to_bv 64 1154188) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (RS _ _ HR) as HR1. pose proof (RS _ _ HX) as HX1. pose proof (RS _ _ HY) as HY1.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR1) as HVR1.
    assert (ETX : bn_top (getbn x ls1) = max) by (apply (wexpand_res_top rr (max + 1) ls ls1 x WRES HVR)).
    assert (ETY : bn_top (getbn y ls1) = min) by (apply (wexpand_res_top rr (max + 1) ls ls1 y WRES HVR)).
    clear SX SY OKX OKY TDX TDY Dx0 Dy0 HEAP1 ST1 MI1 PRE1 CP.
    (* [comment removed for export] *)
    pose proof ENV1 as (HEAP2 & AUX2 & ST2 & (errv2 & ERR2) & MI2 & LXP2 & FA2 & SO2 & _ & FR2 & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_open [] ls1 m2 OW1 AD EA rr R LS1 ND2 HR1 ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
    destruct (lib_state_h_parts _ _ _ _ _ _ LS1) as (IDS1 & ADB1 & ERRB1 & SOK1).
    destruct (bn_arr_facts st1 OW1 LB m2 HEAP2 ls1 AD EA IDS1 ADB1 rr Dr HVR1 ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
    destruct (ref_at_inb _ _ _ _ _ ADB1 HR1) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hins) as (SA0 & _ & _ & SAC & SAI).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HX1) as HVX1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HY1) as HVY1.
    pose proof (st_okm_getbn x ls1 SOK1 HVX1) as (LMX & TDX & _). pose proof (st_okm_getbn y ls1 SOK1 HVY1) as (LMY & TDY & _).
    destruct (operand_view_u st1 OW1 LB m2 ls1 AD EA rr R Dr x X max HEAP2 LS1 HR1 SR ARR HX1 ltac:(rewrite ETX; lia))
      as (Dx & HXd & HLX & X0' & XC' & DX0 & DXC & SXR & SXA & ALX & UPX & _).
    destruct (operand_view_u st1 OW1 LB m2 ls1 AD EA rr R Dr y Y min HEAP2 LS1 HR1 SR ARR HY1 ltac:(rewrite ETY; lia))
      as (Dy & HYd & HLY & Y0' & YC' & DY0 & DYC & SYR & SYA & ALY & UPY & _).
    set (br := getbn rr ls1) in *.
    set (la := firstn max (bn_buf (getbn x ls1))) in *. set (lb := firstn min (bn_buf (getbn y ls1))) in *.
    assert (LLA : length la = max) by (subst la; apply firstn_length_le; rewrite <- ETX; exact TDX).
    assert (LLB : length lb = min) by (subst lb; apply firstn_length_le; rewrite <- ETY; exact TDY).
    (* [comment removed for export] *)
    rewrite (uadd_rest_eq rr x y ls1 max min HVR1 HTOPS) by (unfold bn_dmax in *; lia). fold br la lb.
    cbn [embed interp]. apply implM_interp_ret.
    replace (Z_to_bv 64 (Z.of_nat max - Z.of_nat min)) with (Z_to_bv 64 (Z.of_nat (length la) - Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat max)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat min)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    eapply evt_mono.
    { eapply (uadd_ucore ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (R := R) (A := X) (B := Y)
        (Dr := Dr) (Da := Dx) (Db := Dy) (br := br) (la := la) (lb := lb).
      - unfold uadd_pre. rewrite LLA, LLB. specialize (DSEPR rr R HR1). fold br in DSEPR.
        split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|].
        split; [exact HTOPS|]. split; [exact OKR|]. split; [exact HDM|].
        split; [unfold GLOBALS_TOP in *; lia|]. split; [lia|]. split; [lia|]. split; [exact DSEPR|]. split; [exact SXA|]. split; [exact SYA|].
        split; [exact ALX | exact ALY].
      - unfold uadd_upre. rewrite LLA, LLB.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st1 OW1 LB m2 ls1 AD rr R HEAP2 ADB1 HR1))|].
        split; [apply (bn_arr_ualign st1 OW1 LB m2 Dr br max HEAP2 ARR); clear - HDM; lia|].
        split; [exact UPX|]. split; [exact UPY|]. lia.
      - unfold core_mem. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
        split; [exact HLX|]. split; [exact HLY|]. split; [exact FR2|]. split; [exact ST2 | exact MI2]. }
    (* [comment removed for export] *)
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU & WM & MI3 & SR3 & UR3 & ST3).
    assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
    assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
    assert (HMM : (length lb <= length la)%nat) by (rewrite LLA, LLB; exact HTOPS).
    assert (HDD : (length la + 1 <= bn_dmax br)%nat) by (rewrite LLA; exact HDM).
    pose proof (uadd_buf_length br la lb HLla HLlb HMM HDD) as LU.
    pose proof (uadd_bn_okm br la lb HLla HLlb HMM HDD OKR) as OKF.
    (* [comment removed for export] *)
    unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct ARR as [_ Eb]. unfold bn_dmax in HDD. rewrite Eb in HDD. cbn [length] in HDD. lia. }
    destruct ARR as [HinR _].
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 HinR) as (_ & _ & _ & _ & DRI).
    rewrite LLA in MU.
    assert (HWL : Forall (w_lib OW1 lo (bv_unsigned sp)) [(Dr, Dr + 8 * (Z.of_nat max + 1)); (R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)]).
    { constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
      constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
      constructor; [left; cbn [fst snd]; lia | constructor]. }
    assert (WOK : Forall (w_ok OW1 LB ls1 AD EA [rr]) [(Dr, Dr + 8 * (Z.of_nat max + 1)); (R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)]).
    { constructor; [eapply (w_limbs OW1 LB ls1 AD EA false [rr] _ rr pr Dr); [left; reflexivity | exact HVR1 | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
      constructor; [eapply (w_struct OW1 LB ls1 AD EA false [rr] _ rr R); [left; reflexivity | exact HR1 | cbn; lia | cbn; lia]|].
      constructor; [apply w_stack; cbn; lia | constructor]. }
    unfold bn_post. exists t0', t1', t2', (Z_to_bv 64 1), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3, OW1, errv2.
    split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MU WM HWL CEIL)|].
    split.
    { unfold lib_state. eapply (lib_state_close [] ls1 m3 OW1 AD EA rr R); [| exact ND2 | exact HR1 | | exact OKF |].
      - eapply lib_state_frame; [exact HEAP2 | exact LSH | exact MU | exact WM | exact WOK].
      - exists Dr. split; [exact SR3|]. unfold bn_arr, uadd_bn. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LU.
        split; [exact HinR | exact UR3].
      - apply ids_ok_setbn_same; [exact IDS1 | exact HVR1 |]. unfold bn_blocks, uadd_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite LU. reflexivity. }
    split; [exact (seg_auxv _ _ _ _ _ _ _ _ _ HEAP2 AUX2 MU WM HWL SPB GLO)|].
    split; [exact ST3|].
    split. { eapply rw_cells_transport; [exact ERR2 | exact MU | exact WM |]. unfold LX_ERRNO, RATP, GLOBALS_TOP in *. cbn. lia. }
    split; [exact MI3|].
    split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP2 MU WM HWL CEIL GLO). lia. }
    split; [exact FA2|]. split; [exact SO2|].
    split. { intros r0 a0' H0. apply ref_at_setbn. apply RS. exact H0. }
    unfold uarith_res. split; [reflexivity | exact STAB].
  Qed.

  Lemma BN_uadd_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rr ra_ rb_ : bnref) (R A Bb : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_UADD_STACK -> tp = wz RATP ->
    ref_at ls OW AD rr R -> ref_at ls OW AD ra_ A -> ref_at ls OW AD rb_ Bb ->
    a0 = wz R -> a1 = wz A -> a2 = wz Bb ->
    implM usegs (interp (embed (BN_uadd (tree_ops bptr) rr ra_ rb_ ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (uarith_res rr ls OW))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_UADD) fc None m (seg_rom usegs)).
  Proof.
    intros until Bb. intros PRE -> HR HA HB -> -> ->.
    pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
    pose proof LO as LO'. unfold BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    unfold BN_UADD, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (open_ro_u s OW LB m ls AD EA ra_ A HEAP LS HA) as (Da0 & SA & OKA & _ & A0 & AC & _ & _ & ALA & _).
    destruct (open_ro_u s OW LB m ls AD EA rb_ Bb HEAP LS HB) as (Db0 & SB & OKB & _ & B0 & BC & _ & _ & ALB & _).
    pose proof OKA as (_ & TDA & DMA & _). pose proof OKB as (_ & TDB & DMB & _). unfold BN_WORDS_MAX in DMA, DMB.
    unfold bn_cells, MallocRep.wz in SA, SB.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3063488 - 164) with 3063324 in ERR. unfold GLOBALS_TOP in GLO.
    rewrite BN_uadd_unfold.
    unfold implM. iprefix.
    carve_frame 64%nat ST. do 10 zstep.
    chk ltac:(fun C => clear - C A0; lia).
    do 3 zstep. rewrite (land7 A (hide_elim _ ALA)). chk_lit.
    chk ltac:(fun C => clear - C B0; lia).
    zstep. rewrite (land7 Bb (hide_elim _ ALB)). chk_lit.
    zstep. rewrite (sx32_small (Z.of_nat (bn_top (getbn ra_ ls)))) by (clear - TDA DMA; unfold bn_dmax in *; lia).
    zstep. rewrite (sx32_small (Z.of_nat (bn_top (getbn rb_ ls)))) by (clear - TDB DMB; unfold bn_dmax in *; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
    assert (GLO' : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; lia).
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m fr s ls m1 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL GLO'); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    zstep. rewrite lts_small by (clear - TDA DMA TDB DMB; unfold bn_dmax in *; lia).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (bn_top (getbn ra_ ls) <? bn_top (getbn rb_ ls))%nat with true by (symmetry; apply Nat.ltb_lt; clear - K; lia).
      zstep. zstep.
      ihere. to_implM.
      eapply (uadd_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B m1 rr rb_ ra_ R Bb A);
        [exact ENV | exact LS1 | exact CEIL | exact GLO' | exact LO | exact SPB | exact HR | exact HB | exact HA | clear - K; lia].
    - replace (bn_top (getbn ra_ ls) <? bn_top (getbn rb_ ls))%nat with false by (symmetry; apply Nat.ltb_ge; clear - K; lia).
      zstep. zstep.
      ihere. to_implM.
      eapply (uadd_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s ls OW LB AD EA lo B m1 rr ra_ rb_ R A Bb);
        [exact ENV | exact LS1 | exact CEIL | exact GLO' | exact LO | exact SPB | exact HR | exact HA | exact HB | clear - K; lia].
  Qed.
End Proofs.
End WithCeiling0.
