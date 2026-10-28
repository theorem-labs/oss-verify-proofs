(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnDivWords BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr BnLeaves DivModel.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX BnRepX2 ImplA ImplAX BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA W_smallA W_topA BnAKitA BnCallA W_callsA AsStruct2 AW_num_bits_word W_lshiftA W_copyA W_ctxA W_ctx_endA W_ctx_getA W_fuzzA BnKaraMemA BnCallsKA AW_mul_recursive AW_mul_part_recursive AW_kara_closedA AW_mul_core W_div_tailA W_divA W_bndivA W_mulA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2418040 => 2
  | 2418052 => 1
  | 2418056 => 2
  | 2418100 => 2
  | 2418104 => 1
  | 2418108 => 2
  | 2418152 => 1
  | 2418156 => 2
  | 2418200 => 1
  | 2418204 => 2
  | 2418236 => 2
  | 2418240 => 1
  | 2418244 => 2
  | 2418404 => 2
  | 2418408 => 1
  | 2418412 => 2
  | 2418428 => 1
  | 2418432 => 2
  | 2418460 => 1
  | 2418464 => 1
  | 2418468 => 2
  | 2418508 => 2
  | 2418512 => 1
  | 2418516 => 1
  | 2418520 => 2
  | 2418640 => 2
  | 2418644 => 1
  | 2418648 => 2
  | 2418752 => 1
  | 2418756 => 2
  | 2418796 => 2
  | 2418800 => 1
  | 2418804 => 1
  | 2418808 => 2
  | 2418932 => 1
  | 2418936 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).

Lemma srliw29_small : forall v, 0 <= v < 536870912 -> Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 v) 29)) 18446744073709551615 = 0.
Proof.
  intros v H. unfold bv_wrap. replace (bv_modulus 32) with 4294967296 by reflexivity.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 29) with 536870912.
  rewrite Z.div_small by lia. reflexivity.
Qed.
Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_ml_start := (E_bn_mul_fixed_top_24b828 : uk_call BN_MUL_FIXED_TOP 0x24e5f8 BN_CTX_START).
Local Notation E_ml_get1 := (E_bn_mul_fixed_top_24b83c : uk_call BN_MUL_FIXED_TOP 0x24e60c BN_CTX_GET).
Local Notation E_ml_wexpc := (E_bn_mul_fixed_top_24b85c : uk_call BN_MUL_FIXED_TOP 0x24e638 BN_WEXPAND).
Local Notation E_ml_get2 := (E_bn_mul_fixed_top_24b90c : uk_call BN_MUL_FIXED_TOP 0x24e70c BN_CTX_GET).
Local Notation E_ml_wexpr1 := (E_bn_mul_fixed_top_24b940 : uk_call BN_MUL_FIXED_TOP 0x24e734 BN_WEXPAND).
Local Notation E_ml_wexpr2 := (E_bn_mul_fixed_top_24b950 : uk_call BN_MUL_FIXED_TOP 0x24e744 BN_WEXPAND).
Local Notation E_ml_wexpn := (E_bn_mul_fixed_top_24b9c8 : uk_call BN_MUL_FIXED_TOP 0x24e7cc BN_WEXPAND).
Local Notation E_ml_wexpp1 := (E_bn_mul_fixed_top_24ba44 : uk_call BN_MUL_FIXED_TOP 0x24e854 BN_WEXPAND).
Local Notation E_ml_wexpp2 := (E_bn_mul_fixed_top_24ba54 : uk_call BN_MUL_FIXED_TOP 0x24e864 BN_WEXPAND).
Local Notation E_mul_ft := (E_BN_mul_24b768 : uk_call BN_MUL 0x24e514 BN_MUL_FIXED_TOP).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma implA_ret_cps : forall {A} (a : A) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  cps bsegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc (Q a Σ)) -> implA (TRet a) Σ Q ms.
Proof.
  intros A a Σ Q ms H X Φ S T c Hc Hk. apply (H T c Hc). intros c' Hc'. apply Hk. exists a, X, Σ. split; [exact S | exact Hc'].
Qed.

Lemma arr_block : forall m OW D (b : bignum bptr), bn_arr m OW D b -> (0 < bn_dmax b)%nat ->
  exists p, bn_d b = Some p /\ In (p, D, 8 * Z.of_nat (bn_dmax b)) OW.
Proof.
  intros m OW D b ARR HD. unfold bn_arr in ARR. destruct (bn_d b) as [p|] eqn:E.
  - exists p. split; [reflexivity | exact (proj1 ARR)].
  - exfalso. destruct ARR as [_ Eb]. unfold bn_dmax in HD. rewrite Eb in HD. cbn in HD. lia.
Qed.

(* [comment removed for export] *)
Lemma ax_pres_of_icall2 : forall Σ OW LB m m' SP X d1 n1 b1 d2 n2 b2,
  AHEAP Σ OW LB m -> In b1 OW -> blk_addr b1 <= d1 -> d1 + n1 <= blk_addr b1 + blk_size b1 ->
  In b2 OW -> blk_addr b2 <= d2 -> d2 + n2 <= blk_addr b2 + blk_size b2 -> ACEIL <= SP ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d1 <= a < d1 + n1) /\ ~ (d2 <= a < d2 + n2)) m m' ->
  ax_pres LB SP X m m'.
Proof.
  intros Σ OW LB m m' SP X d1 n1 b1 d2 n2 b2 HEAP Hb1 H11 H12 Hb2 H21 H22 HSP AG. eapply agree_on_mono; [exact AG|]. intros x [_ Hc].
  assert (OUT : forall b d n, In b OW -> blk_addr b <= d -> d + n <= blk_addr b + blk_size b -> ~ (d <= x < d + n)).
  { intros b d n Hb H1 H2 HAr. destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]].
    + pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & _). lia.
    + eapply (blk_not_static Σ OW LB m b x HEAP Hb); [lia | exact Hc].
    + assert (NE : blk_id b0 <> blk_id b).
      { intros E. pose proof (AH_nodup _ _ _ _ HEAP) as NDA. rewrite map_app in NDA.
        eapply (nodup_app_disj _ _ (blk_id b) NDA); [apply in_map; exact Hb | rewrite <- E; apply in_map; exact Hb0]. }
      pose proof (AH_disjoint_gen _ _ _ _ b0 b HEAP (in_or_app _ _ _ (or_intror Hb0)) (in_or_app _ _ _ (or_introl Hb)) NE) as DJ. lia. }
  split; [|split; [exact (OUT b1 d1 n1 Hb1 H11 H12) | exact (OUT b2 d2 n2 Hb2 H21 H22)]].
  destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]]; [left; exact Hc | right; left; exact Hc | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]].
Qed.

Section EnvI2.
  Variables (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem).

  Lemma cenv_icall2A : forall pre used Σ ls m m' OW d1 n1 b1 d2 n2 b2,
    cenvA LB AD lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
    In b1 OW -> blk_addr b1 <= d1 -> d1 + n1 <= blk_addr b1 + blk_size b1 ->
    In b2 OW -> blk_addr b2 <= d2 -> d2 + n2 <= blk_addr b2 + blk_size b2 ->
    AHEAP Σ OW LB m' -> stk bsegs m' lo FB -> mem_inv bsegs m' ->
    agree_on (fun a => aclient_addr (OW ++ LB) FB a /\ ~ (d1 <= a < d1 + n1) /\ ~ (d2 <= a < d2 + n2)) m m' ->
    cenvA LB AD lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m' OW.
  Proof.
    intros pre used Σ ls m m' OW d1 n1 b1 d2 n2 b2 (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) Hb1 H11 H12 Hb2 H21 H22 HEAP' ST' MI' AG.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _).
    pose proof (AH_range_gen _ _ _ _ b1 HEAP (in_or_app _ _ _ (or_introl Hb1))) as (_ & _ & _ & BC1 & _).
    pose proof (AH_range_gen _ _ _ _ b2 HEAP (in_or_app _ _ _ (or_introl Hb2))) as (_ & _ & _ & BC2 & _).
    assert (AG' : agree_on (fun a => FB <= a < USTACK_TOP) m m').
    { eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in Ha. split; [left; exact Ha|]. unfold BnHeapA.ACEIL in *. lia. }
    unfold cenvA. split; [exact OK|]. split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
    split. { eapply ax_pres_trans; [exact AXP|]. eapply ax_pres_weaken; [eapply (ax_pres_of_icall2 Σ OW LB m m' FB LIBW_A d1 n1 b1 d2 n2 b2 HEAP Hb1 H11 H12 Hb2 H21 H22 ltac:(lia) AG) | clear - FBSP; lia]. }
    split; [exact CR|]. split; [exact CNT|]. split; [exact RS|].
    split. { eapply rw_cells_agree; [exact AG' | exact FR |]. intros a Ha. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha.
             unfold USTACK_TOP in *. lia. }
    split; [exact FSZ|].
    unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
    apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AG'|]. intros a Ha. cbv beta in *. lia.
  Qed.
End EnvI2.

(* [comment removed for export] *)
Lemma mul_finish2A : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (TOTAL used : Z) (w0 : word)
    (Σ4 : rts RT) (ls4 : lstate bptr) (m4 mc m5 : mem) (OW4 : list block) (rr t x y : bnref) (R TT X Y Dr Dt nr8 : Z)
    (w tw : list Z) (topn : nat) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word),
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ4 ls4 m4 OW4 ->
  used <= TOTAL -> lib_state ls4 m4 OW4 AD EA -> lo <= bv_unsigned sp - 112 - MUL_CST ->
  ref_at ls4 OW4 AD rr R -> ref_at ls4 OW4 AD t TT -> ref_at ls4 OW4 AD x X -> ref_at ls4 OW4 AD y Y ->
  rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
  rw_cells bsegs m4 R (bn_cells Dr (getbn rr ls4)) -> bn_arr m4 OW4 Dr (getbn rr ls4) ->
  rw_cells bsegs m4 TT (bn_cells Dt (getbn t ls4)) -> bn_arr m4 OW4 Dt (getbn t ls4) ->
  limbs w -> (0 < length w <= bn_dmax (getbn rr ls4))%nat -> (topn <= bn_dmax (getbn rr ls4))%nat -> nr8 = 8 * Z.of_nat (length w) ->
  limbs tw -> length tw = bn_dmax (getbn t ls4) -> (0 < bn_dmax (getbn t ls4))%nat ->
  (* [comment removed for export] *)
  AHEAP Σ4 OW4 LB mc ->
  agree_on (fun a => aclient_addr (OW4 ++ LB) (bv_unsigned sp + -112) a /\ ~ (Dr <= a < Dr + nr8) /\ ~ (Dt <= a < Dt + 8 * Z.of_nat (bn_dmax (getbn t ls4)))) m4 mc ->
  limbs_at bsegs mc Dr w -> limbs_at bsegs mc Dt tw -> mem_inv bsegs mc -> stk bsegs mc lo (bv_unsigned sp + -112) ->
  (* [comment removed for export] *)
  munch [(R, R + 24)]%Z mc m5 -> wmono bsegs mc m5 -> mem_inv bsegs m5 -> stk bsegs m5 lo (bv_unsigned sp + -112) ->
  rw_cells bsegs m5 R [C8 (wz Dr); C4 (wz (Z.of_nat topn)); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls4)))); C4 (wz (Z.b2z (bn_neg (getbn rr ls4)))); C4 (wz (bn_flags (getbn rr ls4)))] ->
  mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras TOTAL rr x y R X Y
            (bn_neg (getbn x ls4)) (bn_neg (getbn y ls4))
            (tt, setbn rr (mul_res (getbn rr ls4) w topn) (setbn t (bn_with_buf (getbn t ls4) tw) ls4)) Σ4
            (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) x22 x23 x24 x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
                F' (Z_to_bv 64 MULC_TAIL) fc' None m5 (seg_rom bsegs)).
Proof.
  intros until t6. intros ENV USED LS LO HR HT HX HY NEX NEY NTR NTX NTY SR ARR STT ARRT LW [HW0 HWD] HTD -> LTW NTW HT0
         HEAPc AGc HRO HTO MIc STc MU5 WM5 MI5 ST5 SR5.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  rewrite MUL_CST_val in LO.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW). unfold mul_frame in FR. cbn [app] in FR.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls4 m4 OW4 AD EA rr R LS ND HR ltac:(intros [])) as (_ & OKR & LSH1).
  destruct (lib_state_open [rr] ls4 m4 OW4 AD EA t TT LSH1 ND HT ltac:(intros [E|[]]; apply NTR; symmetry; exact E)) as (_ & OKT & LSH2).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (bn_arr_facts Σ4 OW4 LB m4 HEAP ls4 AD EA IDS ADB rr Dr HVR ARR) as (U & _ & D0 & DC & _ & DSEP).
  destruct (bn_arr_facts Σ4 OW4 LB m4 HEAP ls4 AD EA IDS ADB t Dt HVT ARRT) as (UT & _ & DT0 & DTC & _ & DSEPT).
  pose proof (DSEP rr R HR) as DSR. pose proof (DSEP t TT HT) as DSRT. pose proof (DSEPT rr R HR) as DSTR. pose proof (DSEPT t TT HT) as DSTT.
  pose proof (struct_disj Σ4 OW4 LB m4 HEAP ls4 AD EA IDS ADB t rr TT R NTR HT HR) as SDT.
  pose proof (bn_arrs_disj Σ4 OW4 LB m4 ls4 AD EA rr t R TT Dr Dt HEAP LS ltac:(congruence) HR HT ARR ARRT) as ADJ.
  destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
  destruct (ref_at_inb _ _ _ _ _ ADB HT) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hint) as (TA0 & _ & _ & TAC & TAI).
  set (br := getbn rr ls4) in *. set (tb := getbn t ls4) in *.
  destruct (arr_block _ _ _ _ ARR ltac:(clear - HWD HW0; lia)) as (pr & Edr & HinR).
  destruct (arr_block _ _ _ _ ARRT HT0) as (pt & Edt & HinT).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HinR) as (_ & _ & _ & _ & DRI).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HinT) as (_ & _ & _ & _ & DTI).
  (* [comment removed for export] *)
  assert (INR : In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) (OW4 ++ LB)) by (apply in_or_app; left; exact HinR).
  assert (INT : In (pt, Dt, 8 * Z.of_nat (bn_dmax tb)) (OW4 ++ LB)) by (apply in_or_app; left; exact HinT).
  pose proof (cenv_icall2A LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ _
                Dr (8 * Z.of_nat (length w)) (pr, Dr, 8 * Z.of_nat (bn_dmax br)) Dt (8 * Z.of_nat (bn_dmax tb)) (pt, Dt, 8 * Z.of_nat (bn_dmax tb))
                ENV HinR ltac:(cbn [blk_addr blk_size fst snd]; lia) ltac:(cbn [blk_addr blk_size fst snd]; lia)
                HinT ltac:(cbn [blk_addr blk_size fst snd]; lia) ltac:(cbn [blk_addr blk_size fst snd]; lia) HEAPc STc MIc AGc) as ENVc.
  assert (LSHc : lib_state_h [t; rr] ls4 mc OW4 AD EA).
  { eapply (lib_state_h_icall2 Σ4 LB false [t; rr] ls4 m4 mc OW4 AD EA _ Dr (8 * Z.of_nat (length w)) Dt (8 * Z.of_nat (bn_dmax tb)) HEAP LSH2 AGc).
    - eapply (w_limbs OW4 LB ls4 AD EA false [t; rr] _ rr pr Dr); [right; left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia].
    - eapply (w_limbs OW4 LB ls4 AD EA false [t; rr] _ t pt Dt); [left; reflexivity | exact HVT | exact Edt | exact HinT | cbn [fst snd]; lia | cbn [fst snd]; fold tb; lia]. }
  eapply (rw_cells_agree _ _ _ _ _ AGc) in STT; [| intros a Ha; cbn in Ha; split;
     [right; right; exists (qt, At, nt); split; [apply in_or_app; left; exact Hint | cbn; clear - Ha Rt1 Rt2; lia] | clear - Ha DSRT DSTT HWD HW0; lia]].
  unfold bn_cells in STT. eapply (rw_cells_transport bsegs _ mc m5) in STT; [| exact MU5 | exact WM5 | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - SDT; lia | exact I]].
  eapply (rw_cells_agree _ _ _ _ _ AGc) in FR; [| intros a Ha; cbn in Ha; split;
     [left; unfold USTACK_TOP; clear - Ha SPT; lia | unfold BnHeapA.ACEIL in *; clear - Ha DC DTC CEIL LO HWD; lia]].
  eapply (rw_cells_transport bsegs _ mc m5) in FR; [| exact MU5 | exact WM5 | cbn [disjoint_from cells_size csize Nat.add]; split; [unfold BnHeapA.ACEIL in *; clear - SAC Ra2 CEIL LO; lia | exact I]].
  destruct (AH_acc _ _ _ _ _ HEAPc INT) as [WRT _]. destruct (AH_acc _ _ _ _ _ HEAPc INR) as [WRR _]. cbn [blk_addr blk_size fst snd] in WRT, WRR.
  assert (UTW : u64arr bsegs m5 Dt (wlimbs tw)).
  { eapply u64arr_transport; [| exact MU5 | exact WM5 | cbn [disjoint_from]; rewrite wlimbs_len, NTW; split; [clear - DSTR; lia | exact I]].
    apply limbarr_limbs_at. split; [exact HTO|]. rewrite NTW. exact WRT. }
  apply (proj1 (limbarr_split bsegs m4 Dr (bn_buf br) (length w) ltac:(unfold bn_dmax in HWD; exact HWD))) in U. destruct U as [_ Uhi].
  eapply (u64arr_agree _ _ _ _ _ AGc) in Uhi; [| intros a Ha; rewrite wlimbs_len, length_skipn in Ha; split;
     [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); split; [exact INR | cbn [blk_addr blk_size fst snd]; unfold bn_dmax in *; clear - Ha HWD; lia]
     | unfold bn_dmax in *; clear - Ha ADJ HWD; lia]].
  eapply (u64arr_transport bsegs _ mc m5) in Uhi; [| exact MU5 | exact WM5 | cbn [disjoint_from]; rewrite wlimbs_len, length_skipn; unfold bn_dmax in *; split; [clear - DSR HWD; lia | exact I]].
  assert (HRO5 : limbs_at bsegs m5 Dr w) by (eapply limbs_at_transport; [exact HRO | exact MU5 | cbn [disjoint_from]; unfold bn_dmax in *; split; [clear - DSR HWD; lia | exact I]]).
  assert (UR5 : u64arr bsegs m5 Dr (wlimbs (splice (bn_buf br) 0 w))).
  { unfold splice. rewrite firstn_O. cbn [app Nat.add]. apply limbarr_app. split; [| exact Uhi].
    apply limbarr_limbs_at. split; [exact HRO5|]. eapply wr_at_transport; [| exact WM5]. rewrite <- (Z.add_0_r Dr) at 1; eapply wr_at_sub; [exact WRR | lia | lia | unfold bn_dmax in *; clear - HWD; lia]. }
  clear Uhi HRO HRO5 HTO WRT WRR.
  assert (HWL : Forall (w_lib OW4 lo (bv_unsigned sp)) [(R, R + 24)]).
  { constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia] | constructor]. }
  assert (WOK : Forall (w_ok OW4 LB ls4 AD EA [t; rr]) [(R, R + 24)]).
  { constructor; [eapply (w_struct OW4 LB ls4 AD EA false [t; rr] _ rr R); [right; left; reflexivity | exact HR | cbn; lia | cbn; lia] | constructor]. }
  pose proof (lib_state_frame Σ4 LB [t; rr] ls4 mc m5 OW4 AD EA _ HEAPc LSHc MU5 WM5 WOK) as LSH2'.
  (* [comment removed for export] *)
  set (tb' := bn_with_buf tb tw).
  assert (LSH1' : lib_state_h [rr] (setbn t tb' ls4) m5 OW4 AD EA).
  { eapply (lib_state_close [rr] ls4 m5 OW4 AD EA t TT); [exact LSH2' | exact ND | exact HT | | |].
    - exists Dt. split.
      + unfold tb', bn_cells, bn_with_buf, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite NTW. exact STT.
      + unfold bn_arr, tb', bn_with_buf. cbn [bn_d]. rewrite Edt. unfold bn_dmax at 1. cbn [bn_buf]. rewrite NTW. split; [exact HinT | exact UTW].
    - destruct OKT as (O1 & O2 & O3 & O4). unfold bn_okm, tb', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite NTW. auto.
    - apply ids_ok_setbn_same; [exact IDS | exact HVT |]. unfold bn_blocks, tb', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite NTW. reflexivity. }
  (* [comment removed for export] *)
  assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (apply splice_length; unfold bn_dmax in *; lia).
  set (ls4' := setbn t tb' ls4) in *.
  assert (EGR : getbn rr ls4' = br) by (unfold ls4'; apply getbn_setbn_other; exact NTR).
  assert (HR' : ref_at ls4' OW4 AD rr R) by (apply ref_at_setbn; exact HR).
  pose proof (valid_refm_setbn t rr tb' ls4 HVR) as HVR'. fold ls4' in HVR'.
  destruct (lib_state_h_parts _ _ _ _ _ _ LSH1') as (IDS' & _ & _ & _).
  assert (LSN : lib_state (setbn rr (mul_res br w topn) ls4') m5 OW4 AD EA).
  { unfold lib_state. eapply (lib_state_close [] ls4' m5 OW4 AD EA rr R); [exact LSH1' | exact ND | exact HR' | | |].
    - exists Dr. split; [unfold bn_cells, mul_res, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR5|].
      unfold bn_arr, mul_res. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LSP. split; [exact HinR | exact UR5].
    - apply mul_res_okm; [exact OKR | exact LW | lia | exact HTD].
    - apply ids_ok_setbn_same; [exact IDS' | exact HVR' |]. rewrite EGR. unfold bn_blocks, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
  unfold mul_joinA. do 23 eexists. exists m5, OW4, w0, used. split; [reflexivity|]. cbn [fst snd]. fold tb'. fold ls4'.
  split.
  { apply cenv_setbnA; [| exact HVR' | rewrite EGR; unfold mul_res, bn_blocks; cbn [bn_d bn_buf bn_dmax bn_top]; rewrite ?Edr; reflexivity].
    apply cenv_setbnA; [| exact HVT | fold tb; unfold tb', bn_with_buf, bn_blocks; cbn [bn_d bn_buf bn_dmax bn_top]; rewrite ?Edt; reflexivity].
    eapply (cenv_silentA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m);
      [exact ENVc | exact MU5 | exact WM5 | exact HWL | exact ST5 | exact MI5 | unfold mul_frame; cbn [app]; exact FR | exact FSZ]. }
  split; [exact USED|]. split; [exact LSN|].
  split; [apply ref_at_setbn; exact HR'|]. split; [apply ref_at_setbn; apply ref_at_setbn; exact HX|]. split; [apply ref_at_setbn; apply ref_at_setbn; exact HY|].
  unfold ls4'. rewrite !getbn_setbn_other by assumption. split; reflexivity.
Qed.


(* [comment removed for export] *)
Lemma rw_cells_app_lA : forall (m : mem) a cs1 cs2, rw_cells bsegs m a (cs1 ++ cs2) -> rw_cells bsegs m a cs1.
Proof.
  intros m a cs1 cs2 [[Hw Hb] W]. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 _].
  apply cells_wf_app in Hw as [Hw1 _]. split; [split; [exact Hw1 | exact Hb1]|].
  rewrite cells_size_app, Nat2Z.inj_add in W. destruct W as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros j Hj. apply W2. lia.
Qed.

(* [comment removed for export] *)
Lemma implA_ret_kpost : forall {A} (a : A) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  evt bsegs (kpost Σ (ASTA RT Σ PMc (Q a Σ))) ms -> implA (TRet a) Σ Q ms.
Proof. intros A a Σ Q ms H. apply implA_ret_cps. apply cps_from_evt'. exact H. Qed.

(* [comment removed for export] *)
Lemma core_prems2A : forall Σ OW LB m ls AD EA rr x y R X Y Dr al bl lo SPv,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA -> stk bsegs m lo (SPv + -112) -> mem_inv bsegs m ->
  ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y -> rr <> x -> rr <> y ->
  rw_cells bsegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  (al <= bn_top (getbn x ls))%nat -> (bl <= bn_top (getbn y ls))%nat -> (0 < al)%nat -> (0 < bl)%nat -> (al + bl <= bn_dmax (getbn rr ls))%nat ->
  ACEIL <= lo -> lo <= SPv - 112 - MUL_CST -> SPv + 16 <= USTACK_TOP ->
  exists Dx Dy,
    mulc_preA (Z_to_bv 64 SPv) lo R X Y Dr Dx Dy MUL_CST (getbn rr ls) (firstn al (bn_buf (getbn x ls))) (firstn bl (bn_buf (getbn y ls)))
    /\ mulc_memA (Z_to_bv 64 SPv) m lo R X Y Dr Dx Dy (getbn rr ls) (firstn al (bn_buf (getbn x ls))) (firstn bl (bn_buf (getbn y ls)))
    /\ bn_arr m OW Dx (getbn x ls) /\ bn_arr m OW Dy (getbn y ls).
Proof.
  intros Σ OW LB m ls AD EA rr x y R X Y Dr al bl lo SPv HEAP LS ST MI HR HX HY NEX NEY SR ARR HAL HBL AL0 BL0 HD CEIL LO SPT.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  rewrite MUL_CST_val in LO.
  assert (ESP : bv_unsigned (Z_to_bv 64 SPv) = SPv) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_okm_getbn rr ls SOK HVR) as (OKR1 & OKR2 & OKR3 & OKR4).
  pose proof (st_okm_getbn x ls SOK HVX) as (LMX & TDX & DMX & _). pose proof (st_okm_getbn y ls SOK HVY) as (LMY & TDY & DMY & _).
  unfold BN_WORDS_MAX in DMX, DMY, OKR3.
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (UR & _ & DR0 & DRC & _ & DSEPR).
  destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
  destruct (operand_view_ne Σ OW LB m ls AD EA rr R Dr x X al HEAP LS HR SR ARR HX HAL ltac:(congruence))
    as (Dx & HXd & HLX & UX & ARRX & X0' & XC' & DX0 & DXC & SXR & SXA & _ & ALX).
  destruct (operand_view_ne Σ OW LB m ls AD EA rr R Dr y Y bl HEAP LS HR SR ARR HY HBL ltac:(congruence))
    as (Dy & HYd & HLY & UY & ARRY & Y0' & YC' & DY0 & DYC & SYR & SYA & _ & ALY).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HR) as (ACR & ALR & OFR).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HX) as (ACX & ALXs & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HY) as (ACY & ALYs & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACDR & ALDR & OFDR).
  destruct (arr_shA _ _ _ _ _ _ HEAP ARRX) as (ACDX & ALDX & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP ARRY) as (ACDY & ALDY & _).
  destruct (arr_pos _ _ _ _ _ _ HEAP ARR ltac:(lia)) as (PDR & IDR).
  destruct (arr_pos _ _ _ _ _ _ HEAP ARRX ltac:(lia)) as (PDX & _).
  destruct (arr_pos _ _ _ _ _ _ HEAP ARRY ltac:(lia)) as (PDY & _).
  assert (LLA : length (firstn al (bn_buf (getbn x ls))) = al) by (apply firstn_length_le; exact (Nat.le_trans _ _ _ HAL TDX)).
  assert (LLB : length (firstn bl (bn_buf (getbn y ls))) = bl) by (apply firstn_length_le; exact (Nat.le_trans _ _ _ HBL TDY)).
  exists Dx, Dy. split; [|split; [|split; [exact ARRX | exact ARRY]]].
  - unfold mulc_preA. rewrite LLA, LLB, ESP.
    split; [apply limbs_firstn; exact LMX|]. split; [apply limbs_firstn; exact LMY|]. split; [exact (conj OKR1 (conj OKR2 (conj OKR3 OKR4)))|].
    split; [clear - HAL HBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
    split; [rewrite MUL_CST_val; unfold BnHeapA.ACEIL in *; clear - SA0 SAC Ra1 Ra2 X0' XC' Y0' YC' DR0 DRC DX0 DXC DY0 DYC CEIL LO SPT TDX TDY HAL HBL; unfold bn_dmax in *; lia|].
    split; [exact (DSEPR rr R HR)|]. split; [clear - SXA TDX HAL; unfold bn_dmax in *; lia|]. split; [clear - SYA TDY HBL; unfold bn_dmax in *; lia|].
    split; [clear - ALX TDX HAL; unfold bn_dmax in *; lia|]. split; [clear - ALY TDY HBL; unfold bn_dmax in *; lia|].
    split; [clear - SXR SYR; lia|].
    split; [exact (conj ALR (conj ALXs (conj ALYs (conj ALDR (conj ALDX ALDY)))))|].
    unfold SHHI. split; [exact OFR|]. split; [exact OFDR|]. split; [unfold BnHeapA.ACEIL in *; clear - C2 CEIL; lia|].
    split; [exact IDR|]. split; [exact PDR|]. split; [exact PDX|]. split; [exact PDY|]. exact SAC0 || (pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (_ & _ & _ & _ & SAI); clear - SAI Ra1 Ra2; lia).
  - unfold mulc_memA. rewrite LLA, LLB, ESP.
    split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|]. split; [exact HLX|]. split; [exact HLY|].
    split; [exact ST|]. split; [exact MI|]. split; [exact (AH_shb _ _ _ _ HEAP)|].
    split; [exact ACR|]. split; [eapply acc_sub; [exact ACX | lia | lia]|]. split; [eapply acc_sub; [exact ACY | lia | lia]|].
    split; [exact ACDR|]. split; [eapply acc_sub; [exact ACDX | lia | clear - TDX HAL; unfold bn_dmax in *; lia]|].
    eapply acc_sub; [exact ACDY | lia | clear - TDY HBL; unfold bn_dmax in *; lia].
Qed.
(* [comment removed for export] *)
Lemma rec_stack_fits : forall kj, (kj <= 23)%nat -> rec_stackA CS8A kj <= MUL_CST.
Proof.
  intros kj H. unfold MUL_CST. pose proof (part_stackA_rec CS8A kj). pose proof (part_stackA_mono CS8A kj 23 H). lia.
Qed.
Lemma part_stack_fits : forall kj, (kj <= 23)%nat -> part_stackA CS8A kj <= MUL_CST.
Proof. intros kj H. unfold MUL_CST. apply part_stackA_mono. exact H. Qed.

Lemma MC_nonneg : 0 <= MC.
Proof. unfold MC. lia. Qed.

(* [comment removed for export] *)
Lemma mul_path_recA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (used : Z)
    (Σ2 : rts RT) (ls2 : lstate bptr) (m2 : mem) (OW2 : list block) (rr t x y : bnref) (R TT X Y : Z) (al bl kj : nat)
    (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m
        (mul_frame (Z_to_bv 64 TT) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ2 ls2 m2 OW2 ->
  used + 2 * MC <= BN_MUL_TOP_COST -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls2 m2 OW2 AD EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls2 OW2 AD rr R -> ref_at ls2 OW2 AD t TT -> ref_at ls2 OW2 AD x X -> ref_at ls2 OW2 AD y Y ->
  rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
  al = bn_top (getbn x ls2) -> bl = bn_top (getbn y ls2) ->
  (1 <= kj <= 23)%nat -> (al <= Nat.pow 2 kj)%nat -> (bl <= Nat.pow 2 kj)%nat -> (Nat.pow 2 kj - al <= 1)%nat -> (Nat.pow 2 kj - bl <= 1)%nat ->
  implA (disp_rec rr t (firstn al (bn_buf (getbn x ls2))) (firstn bl (bn_buf (getbn y ls2))) al bl (al + bl) kj ls2) Σ2
    (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST rr x y R X Y (bn_neg (getbn x ls2)) (bn_neg (getbn y ls2)))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) (Z_to_bv 64 TT) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat bl))
             (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kj))) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 kj))) t3 t4 t5 t6)
        F (Z_to_bv 64 0x24e71c) fc None m2 (seg_rom bsegs)).
Proof.
  intros until t6. intros ENV USED CTX LS LO HR HT HX HY NEX NEY NTR NTX NTY EAL EBL HKJ HALJ HBLJ HDA HDB.
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof MC_nonneg as MCP.
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
  unfold MallocRep.wz. apply implA_from_evt.

  ub. zstep.
  setreg 27%Z (Z_to_bv 64 (Z.of_nat (4 * j))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); change (2 ^ 1) with 2; rewrite bn_swrap32_small by (clear - PJ; lia); clear - PJ; lia).
  zstep. step.
  (* [comment removed for export] *)
  apply evt_done. unfold disp_rec. unfold bbind at 1. cbn [bind tree_ops]. fold j.
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves t (4 * j) ls2 HVT TDT2)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW2) (LB := LB) (AD := AD) (EA := EA) (r := t) (a := TT) (words := (4 * j)%nat);
      [| | | reflexivity | exact HT | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - PJ; lia].
    - eapply cenv_preA; [exact ENV | exact LS | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USED MCP; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_wexpr1 CTX). }
  cbv beta. intros [u3 ls3] Σ3 ms3 [PO LEAF3].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP].
  cbn [fst snd] in PO, LEAF3.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F3 & fc3 & m3 & OW3 & -> & CP3 & (-> & HDM3 & _ & _)).
  assert (E3 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m
                 (mul_frame (Z_to_bv 64 TT) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ3 ls3 m3 OW3
               /\ lib_state ls3 m3 OW3 AD EA) by (eapply cenv_postA; [exact ENV | exact CP3]).
  destruct E3 as (ENV3 & LS3).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
  fix_ret.
  pose proof (RS3 _ _ HR) as HR3. pose proof (RS3 _ _ HT) as HT3. pose proof (RS3 _ _ HX) as HX3. pose proof (RS3 _ _ HY) as HY3.
  destruct LEAF3 as (LOTH3 & _).
  clear CP3 ENV LS.
  (* [comment removed for export] *)
  pose proof ENV3 as (_ & HEAP3 & _).
  destruct (lib_state_h_parts _ _ _ _ _ _ LS3) as (_ & ADB3 & _ & SOK3).
  destruct (ref_at_inb _ _ _ _ _ ADB3 HT3) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP3 Hint) as (TA0 & _ & _ & TAC & _).
  apply implA_from_evt.
  ub; zstep. if_cases KT; zify_cond KT. { exfalso. rewrite ?unsigned_lit in KT by (unfold BnHeapA.ACEIL in *; clear - TA0 Rt1 Rt2 TAC CEIL LO SPR; lia).
                                     unfold BnHeapA.ACEIL in *. clear - KT TA0 Rt1 Rt2 TAC CEIL LO SPR. lia. }
  clear KT.
  do 2 (ub; zstep). ub; step.
  (* [comment removed for export] *)
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS3 HR3) as HVR3.
  pose proof (st_okm_getbn rr ls3 SOK3 HVR3) as (_ & TDR3 & _).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops fst snd].
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves rr (4 * j) ls3 HVR3 TDR3)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW3) (LB := LB) (AD := AD) (EA := EA) (r := rr) (a := R) (words := (4 * j)%nat);
      [| | | reflexivity | exact HR3 | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - PJ; lia].
    - eapply cenv_preA; [exact ENV3 | exact LS3 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USED MCP; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV3).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_wexpr2 CTX). }
  cbv beta. intros [u4 ls4] Σ4 ms4 [PO LEAF4].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP3].
  cbn [fst snd] in PO, LEAF4.
  destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F4 & fc4 & m4 & OW4 & -> & CP4 & (-> & HDM4 & _ & _)).
  assert (E4 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m
                 (mul_frame (Z_to_bv 64 TT) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC + MC) Σ4 ls4 m4 OW4
               /\ lib_state ls4 m4 OW4 AD EA) by (eapply cenv_postA; [exact ENV3 | exact CP4]).
  destruct E4 as (ENV4 & LS4).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
  fix_ret.
  pose proof (RS4 _ _ HR3) as HR4. pose proof (RS4 _ _ HT3) as HT4. pose proof (RS4 _ _ HX3) as HX4. pose proof (RS4 _ _ HY3) as HY4.
  destruct LEAF4 as (LOTH4 & _).
  assert (EGX : getbn x ls4 = getbn x ls2) by (rewrite (LOTH4 x NEX); apply LOTH3; exact NTX).
  assert (EGY : getbn y ls4 = getbn y ls2) by (rewrite (LOTH4 y NEY); apply LOTH3; exact NTY).
  assert (EGT : getbn t ls4 = getbn t ls3) by (apply LOTH4; congruence).
  clear CP4 ENV3 LS3 HVR3 TDR3 ADB3 SOK3 Hint HEAP3.
  (* [comment removed for export] *)
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  destruct (mul_recursive kj (firstn al (bn_buf (getbn x ls2))) (firstn bl (bn_buf (getbn y ls2))) (j - al) (j - bl) (firstn (2 * j) (bn_buf (getbn rr ls4))) (bn_buf (getbn t ls4)))
    as [ro to] eqn:EMR.
  cbn [bind ret tree_ops tbind fst snd].
  apply implA_ret_kpost.
  (* [comment removed for export] *)
  pose proof ENV4 as (_ & HEAP4 & ST4 & MI4 & _ & _ & _ & _ & FR4 & _).
  destruct (open_full Σ4 OW4 LB m4 ls4 AD EA rr R HEAP4 LS4 HR4) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
  destruct (open_full Σ4 OW4 LB m4 ls4 AD EA t TT HEAP4 LS4 HT4) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HX4) as HVX4. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HY4) as HVY4.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS4) as (_ & ADB4 & _ & SOK4).
  pose proof (st_okm_getbn x ls4 SOK4 HVX4) as (LMX & TDX & DMX & _). pose proof (st_okm_getbn y ls4 SOK4 HVY4) as (LMY & TDY & DMY & _).
  unfold BN_WORDS_MAX in DMX, DMY.
  rewrite EGX in *. rewrite EGY in *. rewrite <- EGT in HDM3.
  set (br := getbn rr ls4) in *. set (tb := getbn t ls4) in *.
  assert (HAL0 : (0 < al)%nat) by (clear - HKJ HALJ HDA PJ; lia).
  assert (HBL0 : (0 < bl)%nat) by (clear - HKJ HBLJ HDB PJ; lia).
  assert (HD2 : (2 * j <= bn_dmax br)%nat) by (clear - HDM4; lia).
  destruct (core_prems2A Σ4 OW4 LB m4 ls4 AD EA rr x y R X Y Dr al bl lo (bv_unsigned sp) HEAP4 LS4 ST4 MI4 HR4 HX4 HY4 NEX NEY SR ARR
              ltac:(rewrite EGX; lia) ltac:(rewrite EGY; lia) HAL0 HBL0 ltac:(fold br; clear - HDM4 HALJ HBLJ; lia) CEIL
              ltac:(unfold BN_MUL_FIXED_STACKA in LO'; clear - LO'; lia) ltac:(unfold USTACK_TOP; clear - SPT; lia)) as (Dx & Dy & PREA & MEMA & ARRX & ARRY).
  pose proof (bn_arrs_disj Σ4 OW4 LB m4 ls4 AD EA t x TT X Dt Dx HEAP4 LS4 NTX HT4 HX4 ARRT ARRX) as DTX.
  pose proof (bn_arrs_disj Σ4 OW4 LB m4 ls4 AD EA t y TT Y Dt Dy HEAP4 LS4 NTY HT4 HY4 ARRT ARRY) as DTY.
  pose proof (bn_arrs_disj Σ4 OW4 LB m4 ls4 AD EA rr t R TT Dr Dt HEAP4 LS4 ltac:(congruence) HR4 HT4 ARR ARRT) as DRT.
  rewrite EGX in PREA, MEMA, ARRX, DTX. rewrite EGY in PREA, MEMA, ARRY, DTY.
  set (la := firstn al (bn_buf (getbn x ls2))) in *. set (lb := firstn bl (bn_buf (getbn y ls2))) in *.
  fold br in PREA, MEMA. fold tb in DTX, DTY, DRT. fold br in DRT.
  rewrite Z_to_bv_bv_unsigned in PREA, MEMA.
  pose proof (DSEPT rr R HR4) as S4. fold tb in S4.
  pose proof OKT as (LMT & _).
  assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL at 1; exact TDX).
  assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL at 1; exact TDY).
  assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
  assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
  assert (HSC : (scratch_rec kj <= length (bn_buf tb))%nat).
  { pose proof (scratch_rec_le kj). fold j in H. unfold bn_dmax in HDM3. clear - H HDM3. lia. }
  pose proof OKR as (LBR & _).
  assert (LRl : length (firstn (2 * j) (bn_buf br)) = (2 * j)%nat) by (apply firstn_length_le; unfold bn_dmax in HD2; exact HD2).
  pose proof (mul_recursive_spec kj la lb (j - al) (j - bl) (firstn (2 * j) (bn_buf br)) (bn_buf tb) HLla HLlb
                ltac:(apply limbs_firstn; exact LBR) LMT ltac:(lia) HDA HDB ltac:(rewrite LLA; clear - HALJ; lia) ltac:(rewrite LLB; clear - HBLJ; lia) LRl HSC) as MP.
  rewrite EMR in MP. destruct MP as (LRO & NRO & _ & LTO & NTO).
  (* [comment removed for export] *)
  destruct (arr_block _ _ _ _ ARR ltac:(clear - HD2 PJ; lia)) as (pr & Edr & HinR).
  destruct (arr_block _ _ _ _ ARRT ltac:(clear - HDM3 PJ; lia)) as (pt & Edt & HinT).
  destruct (arr_block _ _ _ _ ARRX ltac:(clear - HAL0 TDX EAL; lia)) as (px & Edx & HinX).
  destruct (arr_block _ _ _ _ ARRY ltac:(clear - HBL0 TDY EBL; lia)) as (py & Edy & HinY).
  destruct (arr_shA _ _ _ _ _ _ HEAP4 ARR) as (_ & ALDR & _). destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRT) as (_ & ALDT & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRX) as (_ & ALDX & _). destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRY) as (_ & ALDY & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP4 LS4 HT4) as (ACT & ALT & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRT) as (ACDT & _ & _).
  assert (SLOT : rw_cells bsegs m4 (bv_unsigned sp + -112) [C8 (Z_to_bv 64 TT)]).
  { eapply (rw_cells_app_lA m4 _ [C8 (Z_to_bv 64 TT)]). unfold mul_frame in FR4. cbn [app] in FR4 |- *. exact FR4. }
  (* [comment removed for export] *)
  ub; zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (unfold BnHeapA.ACEIL in *; clear - R0 RC CEIL LO SPR; lia).
                                     unfold BnHeapA.ACEIL in *. clear - KZ R0 RC CEIL LO SPR. lia. }
  clear KZ.
  replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
  eapply (mulc_recA sp gp (Z_to_bv 64 TP_A) m4 lo R X Y Dr Dx Dy MUL_CST br la lb PREA MEMA Σ4 _ OW4 LB
            (pr, Dr, 8 * Z.of_nat (bn_dmax br)) (pt, Dt, 8 * Z.of_nat (bn_dmax tb)) (px, Dx, 8 * Z.of_nat (bn_dmax (getbn x ls2))) (py, Dy, 8 * Z.of_nat (bn_dmax (getbn y ls2)))
            kj (j - al)%nat (j - bl)%nat TT Dt (bn_buf tb)).
  - apply rec_stack_fits. clear - HKJ. lia.
  - unfold mulc_tpreA. rewrite LLA, LLB. unfold BnHeapA.ACEIL in *.
    split; [exact LMT|]. split; [apply (d_cell m4 TT Dt _ STT)|].
    split; [apply limbs_at_of_u64arr; exact UT|].
    split; [apply (limbarr_limbs_at bsegs) in UT; exact (proj2 UT)|].
    split; [clear - DT0 DTC CEIL; unfold bn_dmax in *; lia|]. split; [clear - S4; unfold bn_dmax in *; lia|].
    split; [clear - DTX TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - DTY TDY EBL; unfold bn_dmax in *; lia|].
    split; [clear - DRT; unfold bn_dmax in *; lia|].
    split; [eapply acc_sub; [exact ACT | lia | lia]|]. pose proof (AH_range _ _ _ _ _ _ _ HEAP4 HinT) as (DTpos & _).
    split; [split; [exact ALT | clear - T0 TC CEIL; lia]|]. split; [exact ALDT | exact DTpos].
  - exact HKJ'.
  - exact HDA.
  - exact HDB.
  - rewrite LLA. clear - HALJ. lia.
  - rewrite LLB. clear - HBLJ. lia.
  - exact HD2.
  - exact HSC.
  - exact SLOT.
  - split; [exact HEAP4|]. split.
    { unfold kara_blocks. cbn [blk_addr blk_size fst snd]. rewrite LLA, LLB.
      split; [exact HinR|]. split; [exact HinT|]. split; [apply in_or_app; left; exact HinX|]. split; [apply in_or_app; left; exact HinY|].
      split; [clear - HD2; unfold bn_dmax in *; lia|]. split; [unfold bn_dmax; clear; lia|].
      split; [clear - TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - TDY EBL; unfold bn_dmax in *; lia|].
      exact (conj ALDR (conj ALDT (conj ALDX ALDY))). }
    split; [exact CEIL|]. split; [unfold USTACK_TOP; clear - SPT; lia|]. split; [exact FB16 | reflexivity].
  - (* [comment removed for export] *)
    intros mc u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 w3 w4 w5 w6 F5 fc5 HEAPc AGc WMc MIc HRO HTO STc.
    destruct (ref_at_inb _ _ _ _ _ ADB4 HR4) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP4 Hins) as (SA0 & _ & _ & SAC & SAI).
    assert (INS : In (qs, As, ns) (OW4 ++ LB)) by (apply in_or_app; left; exact Hins).
    pose proof (AH_acc_in _ _ _ _ (qs, As, ns) R 24 HEAPc INS Ra1 Ra2) as ACRc.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP4 LS4 HR4) as (_ & ALR & OFR).
    pose proof (DSEPR rr R HR4) as S1. fold br in S1.
    assert (SRc : rw_cells bsegs mc R (bn_cells Dr br)).
    { eapply (rw_cells_agree _ _ _ _ _ AGc); [exact SR|]. intros a Ha. cbn in Ha. split;
        [right; right; exists (qs, As, ns); split; [exact INS | cbn; clear - Ha Ra1 Ra2; lia] | clear - Ha S1 S4 HD2; unfold bn_dmax in *; lia]. }
    unfold bn_cells in SRc.
    pose proof (munch_refl [(R, R + 24)]%Z mc) as MU5. pose proof (wmono_refl bsegs mc) as WM5.
    assert (OFF : offshW [(R, R + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFR; lia).
    assert (ARR24 : 0 < R /\ R + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - R0 RC CEIL LO SPR SPT; lia).
    apply hide_intro in OFR. apply hide_intro in SAI. apply hide_intro in S1. apply hide_intro in S4.
    apply hide_intro in DTX. apply hide_intro in DTY. apply hide_intro in DRT.
    pose proof MIc as MIk. pose proof STc as STk. apply hide_intro in MIk. apply hide_intro in STk.
    ub; step.                                                     (* [comment removed for export] *)
    do 3 (ub; zstep). shl_with ACRc ALR. ub; chk0.                      (* [comment removed for export] *)
    ub; zstep.                                                    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with STx : stk _ mx _ _, MIx : mem_inv _ mx |- _ => rename STx into ST5; rename MIx into MI5; rename mx into m5 end end.
    apply evt_done. unfold kpost. apply cps_done.
    apply hide_elim in MIk. apply hide_elim in STk.
    rewrite EMR in HRO, HTO. cbn [fst snd] in HRO, HTO.
    rewrite <- EGX, <- EGY.
    eapply (mul_finish2A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F5 fc5 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST (used + MC + MC)
              (Z_to_bv 64 TT) Σ4 ls4 m4 mc m5 OW4 rr t x y R TT X Y Dr Dt (8 * Z.of_nat (2 * j)) ro to (al + bl)%nat);
      [ exact ENV4 | clear - USED; lia | exact LS4 | rewrite MUL_CST_val; clear - LO; lia
      | exact HR4 | exact HT4 | exact HX4 | exact HY4 | exact NEX | exact NEY | exact NTR | exact NTX | exact NTY
      | exact SR | exact ARR | exact STT | exact ARRT
      | exact LRO | rewrite NRO, LRl; fold br; clear - HD2 PJ; lia | fold br; clear - HDM4 HALJ HBLJ; lia | rewrite NRO, LRl; reflexivity
      | exact LTO | rewrite NTO; reflexivity | fold tb; clear - HDM3 PJ; lia
      | exact HEAPc | exact AGc | exact HRO | exact HTO | exact MIk | exact STk
      | exact MU5 | exact WM5 | exact MI5 | exact ST5
      | rewrite Nat2Z.inj_add, <- LLA, <- LLB; exact SRc ].
Qed.

(* [comment removed for export] *)
Lemma mul_path_partA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (used : Z)
    (Σ2 : rts RT) (ls2 : lstate bptr) (m2 : mem) (OW2 : list block) (rr t x y : bnref) (R TT X Y : Z) (al bl kj : nat)
    (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m
        (mul_frame (Z_to_bv 64 TT) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ2 ls2 m2 OW2 ->
  used + 2 * MC <= BN_MUL_TOP_COST -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls2 m2 OW2 AD EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls2 OW2 AD rr R -> ref_at ls2 OW2 AD t TT -> ref_at ls2 OW2 AD x X -> ref_at ls2 OW2 AD y Y ->
  rr <> x -> rr <> y -> t <> rr -> t <> x -> t <> y ->
  al = bn_top (getbn x ls2) -> bl = bn_top (getbn y ls2) ->
  (3 <= kj <= 23)%nat -> (Nat.pow 2 kj <= al)%nat -> (Nat.pow 2 kj <= bl)%nat -> (al < 2 * Nat.pow 2 kj)%nat -> (bl < 2 * Nat.pow 2 kj)%nat ->
  (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
  implA (disp_part rr t (firstn al (bn_buf (getbn x ls2))) (firstn bl (bn_buf (getbn y ls2))) al bl (al + bl) kj ls2) Σ2
    (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST rr x y R X Y (bn_neg (getbn x ls2)) (bn_neg (getbn y ls2)))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) (Z_to_bv 64 TT) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat bl))
             (Z_to_bv 64 (Z.of_nat (Nat.pow 2 kj))) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 kj))) t3 t4 t5 t6)
        F (Z_to_bv 64 0x24e840) fc None m2 (seg_rom bsegs)).
Proof.
  intros until t6. intros ENV USED CTX LS LO HR HT HX HY NEX NEY NTR NTX NTY EAL EBL HKJ HALJ HBLJ HAL2 HBL2 HD1 HD2'.
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof MC_nonneg as MCP.
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
  unfold MallocRep.wz. apply implA_from_evt.

  ub1 ub_kind. zstep. if_cases Cub; zify_cond Cub. { exfalso. apply Cub. apply srliw29_small. clear - PJ. lia. } clear Cub.
  zstep.
  setreg 27%Z (Z_to_bv 64 (Z.of_nat (8 * j))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); change (2 ^ 2) with 4; rewrite bn_swrap32_small by (clear - PJ; lia); clear - PJ; lia).
  zstep. step.
  (* [comment removed for export] *)
  apply evt_done. unfold disp_part. unfold bbind at 1. cbn [bind tree_ops]. fold j.
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves t (8 * j) ls2 HVT TDT2)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW2) (LB := LB) (AD := AD) (EA := EA) (r := t) (a := TT) (words := (8 * j)%nat);
      [| | | reflexivity | exact HT | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - PJ; lia].
    - eapply cenv_preA; [exact ENV | exact LS | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USED MCP; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_wexpp1 CTX). }
  cbv beta. intros [u3 ls3] Σ3 ms3 [PO LEAF3].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP].
  cbn [fst snd] in PO, LEAF3.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F3 & fc3 & m3 & OW3 & -> & CP3 & (-> & HDM3 & _ & _)).
  assert (E3 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m
                 (mul_frame (Z_to_bv 64 TT) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ3 ls3 m3 OW3
               /\ lib_state ls3 m3 OW3 AD EA) by (eapply cenv_postA; [exact ENV | exact CP3]).
  destruct E3 as (ENV3 & LS3).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
  fix_ret.
  pose proof (RS3 _ _ HR) as HR3. pose proof (RS3 _ _ HT) as HT3. pose proof (RS3 _ _ HX) as HX3. pose proof (RS3 _ _ HY) as HY3.
  destruct LEAF3 as (LOTH3 & _).
  clear CP3 ENV LS.
  (* [comment removed for export] *)
  pose proof ENV3 as (_ & HEAP3 & _).
  destruct (lib_state_h_parts _ _ _ _ _ _ LS3) as (_ & ADB3 & _ & SOK3).
  destruct (ref_at_inb _ _ _ _ _ ADB3 HT3) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP3 Hint) as (TA0 & _ & _ & TAC & _).
  apply implA_from_evt.
  ub; zstep. if_cases KT; zify_cond KT. { exfalso. rewrite ?unsigned_lit in KT by (unfold BnHeapA.ACEIL in *; clear - TA0 Rt1 Rt2 TAC CEIL LO SPR; lia).
                                     unfold BnHeapA.ACEIL in *. clear - KT TA0 Rt1 Rt2 TAC CEIL LO SPR. lia. }
  clear KT.
  do 2 (ub; zstep). ub; step.
  (* [comment removed for export] *)
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS3 HR3) as HVR3.
  pose proof (st_okm_getbn rr ls3 SOK3 HVR3) as (_ & TDR3 & _).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops fst snd].
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves rr (8 * j) ls3 HVR3 TDR3)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW3) (LB := LB) (AD := AD) (EA := EA) (r := rr) (a := R) (words := (8 * j)%nat);
      [| | | reflexivity | exact HR3 | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - PJ; lia].
    - eapply cenv_preA; [exact ENV3 | exact LS3 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USED MCP; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV3).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_wexpp2 CTX). }
  cbv beta. intros [u4 ls4] Σ4 ms4 [PO LEAF4].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP3].
  cbn [fst snd] in PO, LEAF4.
  destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F4 & fc4 & m4 & OW4 & -> & CP4 & (-> & HDM4 & _ & _)).
  assert (E4 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m
                 (mul_frame (Z_to_bv 64 TT) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC + MC) Σ4 ls4 m4 OW4
               /\ lib_state ls4 m4 OW4 AD EA) by (eapply cenv_postA; [exact ENV3 | exact CP4]).
  destruct E4 as (ENV4 & LS4).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
  fix_ret.
  pose proof (RS4 _ _ HR3) as HR4. pose proof (RS4 _ _ HT3) as HT4. pose proof (RS4 _ _ HX3) as HX4. pose proof (RS4 _ _ HY3) as HY4.
  destruct LEAF4 as (LOTH4 & _).
  assert (EGX : getbn x ls4 = getbn x ls2) by (rewrite (LOTH4 x NEX); apply LOTH3; exact NTX).
  assert (EGY : getbn y ls4 = getbn y ls2) by (rewrite (LOTH4 y NEY); apply LOTH3; exact NTY).
  assert (EGT : getbn t ls4 = getbn t ls3) by (apply LOTH4; congruence).
  clear CP4 ENV3 LS3 HVR3 TDR3 ADB3 SOK3 Hint HEAP3.
  (* [comment removed for export] *)
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  destruct (mul_part_recursive kj kj (firstn al (bn_buf (getbn x ls2))) (firstn bl (bn_buf (getbn y ls2))) (al - j) (bl - j) (firstn (4 * j) (bn_buf (getbn rr ls4))) (bn_buf (getbn t ls4)))
    as [ro to] eqn:EMR.
  cbn [bind ret tree_ops tbind fst snd].
  apply implA_ret_kpost.
  (* [comment removed for export] *)
  pose proof ENV4 as (_ & HEAP4 & ST4 & MI4 & _ & _ & _ & _ & FR4 & _).
  destruct (open_full Σ4 OW4 LB m4 ls4 AD EA rr R HEAP4 LS4 HR4) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
  destruct (open_full Σ4 OW4 LB m4 ls4 AD EA t TT HEAP4 LS4 HT4) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HX4) as HVX4. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HY4) as HVY4.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS4) as (_ & ADB4 & _ & SOK4).
  pose proof (st_okm_getbn x ls4 SOK4 HVX4) as (LMX & TDX & DMX & _). pose proof (st_okm_getbn y ls4 SOK4 HVY4) as (LMY & TDY & DMY & _).
  unfold BN_WORDS_MAX in DMX, DMY.
  rewrite EGX in *. rewrite EGY in *. rewrite <- EGT in HDM3.
  set (br := getbn rr ls4) in *. set (tb := getbn t ls4) in *.
  assert (HAL0 : (0 < al)%nat) by (clear - HALJ PJ; lia).
  assert (HBL0 : (0 < bl)%nat) by (clear - HBLJ PJ; lia).
  assert (HD2 : (4 * j <= bn_dmax br)%nat) by (clear - HDM4; lia).
  destruct (core_prems2A Σ4 OW4 LB m4 ls4 AD EA rr x y R X Y Dr al bl lo (bv_unsigned sp) HEAP4 LS4 ST4 MI4 HR4 HX4 HY4 NEX NEY SR ARR
              ltac:(rewrite EGX; lia) ltac:(rewrite EGY; lia) HAL0 HBL0 ltac:(fold br; clear - HDM4 HAL2 HBL2; lia) CEIL
              ltac:(unfold BN_MUL_FIXED_STACKA in LO'; clear - LO'; lia) ltac:(unfold USTACK_TOP; clear - SPT; lia)) as (Dx & Dy & PREA & MEMA & ARRX & ARRY).
  pose proof (bn_arrs_disj Σ4 OW4 LB m4 ls4 AD EA t x TT X Dt Dx HEAP4 LS4 NTX HT4 HX4 ARRT ARRX) as DTX.
  pose proof (bn_arrs_disj Σ4 OW4 LB m4 ls4 AD EA t y TT Y Dt Dy HEAP4 LS4 NTY HT4 HY4 ARRT ARRY) as DTY.
  pose proof (bn_arrs_disj Σ4 OW4 LB m4 ls4 AD EA rr t R TT Dr Dt HEAP4 LS4 ltac:(congruence) HR4 HT4 ARR ARRT) as DRT.
  rewrite EGX in PREA, MEMA, ARRX, DTX. rewrite EGY in PREA, MEMA, ARRY, DTY.
  set (la := firstn al (bn_buf (getbn x ls2))) in *. set (lb := firstn bl (bn_buf (getbn y ls2))) in *.
  fold br in PREA, MEMA. fold tb in DTX, DTY, DRT. fold br in DRT.
  rewrite Z_to_bv_bv_unsigned in PREA, MEMA.
  pose proof (DSEPT rr R HR4) as S4. fold tb in S4.
  pose proof OKT as (LMT & _).
  assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL at 1; exact TDX).
  assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL at 1; exact TDY).
  assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
  assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
  assert (HSC : (8 * j <= length (bn_buf tb))%nat) by (unfold bn_dmax in HDM3; exact HDM3).
  pose proof OKR as (LBR & _).
  assert (LRl : length (firstn (4 * j) (bn_buf br)) = (4 * j)%nat) by (apply firstn_length_le; unfold bn_dmax in HD2; exact HD2).
  pose proof (mul_part_recursive_spec kj kj la lb (al - j) (bl - j) (firstn (4 * j) (bn_buf br)) (bn_buf tb) HLla HLlb
                ltac:(apply limbs_firstn; exact LBR) LMT ltac:(lia) ltac:(lia) ltac:(clear - HAL2 HALJ; lia) ltac:(clear - HBL2 HBLJ; lia)
                ltac:(clear - HD1 HD2' HALJ HBLJ; lia) ltac:(clear - HD1 HD2' HALJ HBLJ; lia)
                ltac:(rewrite LLA; clear - HALJ; lia) ltac:(rewrite LLB; clear - HBLJ; lia) LRl HSC) as MP.
  rewrite EMR in MP. destruct MP as (LRO & NRO & _ & LTO & NTO).
  (* [comment removed for export] *)
  destruct (arr_block _ _ _ _ ARR ltac:(clear - HD2 PJ; lia)) as (pr & Edr & HinR).
  destruct (arr_block _ _ _ _ ARRT ltac:(clear - HDM3 PJ; lia)) as (pt & Edt & HinT).
  destruct (arr_block _ _ _ _ ARRX ltac:(clear - HAL0 TDX EAL; lia)) as (px & Edx & HinX).
  destruct (arr_block _ _ _ _ ARRY ltac:(clear - HBL0 TDY EBL; lia)) as (py & Edy & HinY).
  destruct (arr_shA _ _ _ _ _ _ HEAP4 ARR) as (_ & ALDR & _). destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRT) as (_ & ALDT & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRX) as (_ & ALDX & _). destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRY) as (_ & ALDY & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP4 LS4 HT4) as (ACT & ALT & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRT) as (ACDT & _ & _).
  assert (SLOT : rw_cells bsegs m4 (bv_unsigned sp + -112) [C8 (Z_to_bv 64 TT)]).
  { eapply (rw_cells_app_lA m4 _ [C8 (Z_to_bv 64 TT)]). unfold mul_frame in FR4. cbn [app] in FR4 |- *. exact FR4. }
  (* [comment removed for export] *)
  ub; zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (unfold BnHeapA.ACEIL in *; clear - R0 RC CEIL LO SPR; lia).
                                     unfold BnHeapA.ACEIL in *. clear - KZ R0 RC CEIL LO SPR. lia. }
  clear KZ.
  replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
  eapply (mulc_partA sp gp (Z_to_bv 64 TP_A) m4 lo R X Y Dr Dx Dy MUL_CST br la lb PREA MEMA Σ4 _ OW4 LB
            (pr, Dr, 8 * Z.of_nat (bn_dmax br)) (pt, Dt, 8 * Z.of_nat (bn_dmax tb)) (px, Dx, 8 * Z.of_nat (bn_dmax (getbn x ls2))) (py, Dy, 8 * Z.of_nat (bn_dmax (getbn y ls2)))
            kj kj (al - j)%nat (bl - j)%nat TT Dt (bn_buf tb)).
  - apply part_stack_fits. clear - HKJ. lia.
  - unfold mulc_tpreA. rewrite LLA, LLB. unfold BnHeapA.ACEIL in *.
    split; [exact LMT|]. split; [apply (d_cell m4 TT Dt _ STT)|].
    split; [apply limbs_at_of_u64arr; exact UT|].
    split; [apply (limbarr_limbs_at bsegs) in UT; exact (proj2 UT)|].
    split; [clear - DT0 DTC CEIL; unfold bn_dmax in *; lia|]. split; [clear - S4; unfold bn_dmax in *; lia|].
    split; [clear - DTX TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - DTY TDY EBL; unfold bn_dmax in *; lia|].
    split; [clear - DRT; unfold bn_dmax in *; lia|].
    split; [eapply acc_sub; [exact ACT | lia | lia]|]. pose proof (AH_range _ _ _ _ _ _ _ HEAP4 HinT) as (DTpos & _).
    split; [split; [exact ALT | clear - T0 TC CEIL; lia]|]. split; [exact ALDT | exact DTpos].
  - clear - HKJ. lia.
  - clear. lia.
  - exact HKJ'.
  - clear - HAL2 HALJ. lia.
  - clear - HBL2 HBLJ. lia.
  - clear - HD1 HD2' HALJ HBLJ. lia.
  - clear - HD1 HD2' HALJ HBLJ. lia.
  - rewrite LLA. clear - HALJ. lia.
  - rewrite LLB. clear - HBLJ. lia.
  - exact HD2.
  - exact HSC.
  - exact SLOT.
  - split; [exact HEAP4|]. split.
    { unfold kara_blocks. cbn [blk_addr blk_size fst snd]. rewrite LLA, LLB.
      split; [exact HinR|]. split; [exact HinT|]. split; [apply in_or_app; left; exact HinX|]. split; [apply in_or_app; left; exact HinY|].
      split; [clear - HD2; unfold bn_dmax in *; lia|]. split; [unfold bn_dmax; clear; lia|].
      split; [clear - TDX EAL; unfold bn_dmax in *; lia|]. split; [clear - TDY EBL; unfold bn_dmax in *; lia|].
      exact (conj ALDR (conj ALDT (conj ALDX ALDY))). }
    split; [exact CEIL|]. split; [unfold USTACK_TOP; clear - SPT; lia|]. split; [exact FB16 | reflexivity].
  - (* [comment removed for export] *)
    intros mc u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 w3 w4 w5 w6 F5 fc5 HEAPc AGc WMc MIc HRO HTO STc.
    destruct (ref_at_inb _ _ _ _ _ ADB4 HR4) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP4 Hins) as (SA0 & _ & _ & SAC & SAI).
    assert (INS : In (qs, As, ns) (OW4 ++ LB)) by (apply in_or_app; left; exact Hins).
    pose proof (AH_acc_in _ _ _ _ (qs, As, ns) R 24 HEAPc INS Ra1 Ra2) as ACRc.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP4 LS4 HR4) as (_ & ALR & OFR).
    pose proof (DSEPR rr R HR4) as S1. fold br in S1.
    assert (SRc : rw_cells bsegs mc R (bn_cells Dr br)).
    { eapply (rw_cells_agree _ _ _ _ _ AGc); [exact SR|]. intros a Ha. cbn in Ha. split;
        [right; right; exists (qs, As, ns); split; [exact INS | cbn; clear - Ha Ra1 Ra2; lia] | clear - Ha S1 S4 HD2; unfold bn_dmax in *; lia]. }
    unfold bn_cells in SRc.
    pose proof (munch_refl [(R, R + 24)]%Z mc) as MU5. pose proof (wmono_refl bsegs mc) as WM5.
    assert (OFF : offshW [(R, R + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFR; lia).
    assert (ARR24 : 0 < R /\ R + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - R0 RC CEIL LO SPR SPT; lia).
    apply hide_intro in OFR. apply hide_intro in SAI. apply hide_intro in S1. apply hide_intro in S4.
    apply hide_intro in DTX. apply hide_intro in DTY. apply hide_intro in DRT.
    pose proof MIc as MIk. pose proof STc as STk. apply hide_intro in MIk. apply hide_intro in STk.
    do 3 (ub; zstep). shl_with ACRc ALR. ub; chk0.                      (* [comment removed for export] *)
    ub; zstep.                                                    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with STx : stk _ mx _ _, MIx : mem_inv _ mx |- _ => rename STx into ST5; rename MIx into MI5; rename mx into m5 end end.
    apply evt_done. unfold kpost. apply cps_done.
    apply hide_elim in MIk. apply hide_elim in STk.
    rewrite EMR in HRO, HTO. cbn [fst snd] in HRO, HTO.
    rewrite <- EGX, <- EGY.
    eapply (mul_finish2A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F5 fc5 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST (used + MC + MC)
              (Z_to_bv 64 TT) Σ4 ls4 m4 mc m5 OW4 rr t x y R TT X Y Dr Dt (8 * Z.of_nat (4 * j)) ro to (al + bl)%nat);
      [ exact ENV4 | clear - USED; lia | exact LS4 | rewrite MUL_CST_val; clear - LO; lia
      | exact HR4 | exact HT4 | exact HX4 | exact HY4 | exact NEX | exact NEY | exact NTR | exact NTX | exact NTY
      | exact SR | exact ARR | exact STT | exact ARRT
      | exact LRO | rewrite NRO, LRl; fold br; clear - HD2 PJ; lia | fold br; clear - HDM4 HAL2 HBL2; lia | rewrite NRO, LRl; reflexivity
      | exact LTO | rewrite NTO; reflexivity | fold tb; clear - HDM3 PJ; lia
      | exact HEAPc | exact AGc | exact HRO | exact HTO | exact MIk | exact STk
      | exact MU5 | exact WM5 | exact MI5 | exact ST5
      | rewrite Nat2Z.inj_add, <- LLA, <- LLB; exact SRc ].
Qed.


(* [comment removed for export] *)
Lemma kara_kj_factsA : forall al bl : nat, (16 <= al)%nat -> (16 <= bl)%nat -> (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
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
Lemma mul_path_karaA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (used : Z) (w0 : word)
    (Σ1 : rts RT) (ls1 : lstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z) (al bl : nat)
    (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x25 x27 t3 t4 t5 t6 : word),
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ1 ls1 m1 OW1 ->
  used + 3 * MC <= BN_MUL_TOP_COST -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls1 m1 OW1 AD EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls1 OW1 AD rr R -> ref_at ls1 OW1 AD x X -> ref_at ls1 OW1 AD y Y -> rr <> x -> rr <> y ->
  nonpool rr -> nonpool x -> nonpool y ->
  al = bn_top (getbn x ls1) -> bl = bn_top (getbn y ls1) ->
  (16 <= al)%nat -> (16 <= bl)%nat -> (al <= bl + 1)%nat -> (bl <= al + 1)%nat ->
  implA (disp_kara rr (firstn al (bn_buf (getbn x ls1))) (firstn bl (bn_buf (getbn y ls1))) al bl (al + bl)
                   (Z.to_nat (num_bits_word (Z.of_nat (Nat.max al bl)) - 1)) ls1) Σ1
    (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST rr x y R X Y (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 (Z_to_bv 64 (Z.of_nat al - Z.of_nat bl))
             a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat bl))
             x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24e6d0) fc None m1 (seg_rom bsegs)).
Proof.
  intros until t6. intros ENV USED CTX LS LO HR HX HY NEX NEY NPR NPX NPY EAL EBL HA16 HB16 HAB HBA.
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof MC_nonneg as MCP.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK1).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_okm_getbn x ls1 SOK1 HVX) as (_ & TDX & DMX & _). pose proof (st_okm_getbn y ls1 SOK1 HVY) as (_ & TDY & DMY & _).
  unfold BN_WORDS_MAX in DMX, DMY.
  assert (AL23 : Z.of_nat al < 8388608) by (clear - EAL TDX DMX; unfold bn_dmax in *; lia).
  assert (BL23 : Z.of_nat bl < 8388608) by (clear - EBL TDY DMY; unfold bn_dmax in *; lia).
  pose proof (kara_kj_factsA al bl HA16 HB16 HAB HBA AL23 BL23) as KF. cbv zeta in KF.
  set (mx := Nat.max al bl) in *. set (kj := Z.to_nat (num_bits_word (Z.of_nat mx) - 1)) in *. destruct KF as (HKJ & HJ1 & HJ2 & EKJ).
  set (j := Nat.pow 2 kj) in *.
  assert (EJ : Z.of_nat j = 2 ^ Z.of_nat kj) by (subst j; rewrite Nat2Z.inj_pow; reflexivity).
  assert (PJ : Z.of_nat j <= 8388608) by (clear - HJ1 AL23 BL23; subst mx; lia).
  (* [comment removed for export] *)
  assert (CONT : forall w, w = Z_to_bv 64 (Z.of_nat mx) ->
    implA (disp_kara rr (firstn al (bn_buf (getbn x ls1))) (firstn bl (bn_buf (getbn y ls1))) al bl (al + bl) kj ls1) Σ1
      (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST rr x y R X Y (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) w (Z_to_bv 64 (Z.of_nat al - Z.of_nat bl))
               a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat bl))
               x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24e6dc) fc None m1 (seg_rom bsegs))).
  2:{ apply implA_from_evt. ub; zstep. ub; zstep. rewrite lts_signed by (clear - AL23 BL23; lia). if_cases KI; zify_cond KI.
      - apply evt_done. apply CONT. f_equal. subst mx. clear - KI. lia.
      - ub; zstep. apply evt_done. apply CONT. f_equal. subst mx. clear - KI. lia. }
  intros w ->.
  pose proof ENV as (_ & HEAP1 & ST1 & MI1 & _ & _ & _ & _ & FR1 & FSZ1 & _).
  unfold MallocRep.wz. apply implA_from_evt.
  (* [comment removed for export] *)
  ub; step.
  eapply evt_cut.
  { eapply (BN_num_bits_word_aspec (Z_to_bv 64 0x24e6e0) (Z_to_bv 64 (bv_unsigned sp + -112))) with (lo := lo);
      [rewrite ESP; exact ST1 | rewrite ESP; lia | exact MI1]. }
  intros ms' (n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & n8 & n9 & n10 & n11 & n12 & n13 & mN & -> & MUn & WMn & MIn & STn).
  rewrite ESP in MUn, STn. rewrite (unsigned_lit (Z.of_nat mx)) by (clear - AL23 BL23; subst mx; lia).
  fix_ret.
  assert (HWLn : Forall (w_lib OW1 lo (bv_unsigned sp)) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112)]) by (constructor; [left; cbn [fst snd]; lia | constructor]).
  assert (WOKn : Forall (w_ok OW1 LB ls1 AD EA []) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112)]) by (constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia | constructor]).
  pose proof (lib_state_frame Σ1 LB [] ls1 m1 mN OW1 AD EA _ HEAP1 LS MUn WMn WOKn : lib_state ls1 mN OW1 AD EA) as LSn.
  assert (ENVn : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ1 ls1 mN OW1).
  { eapply (cenv_silentA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m);
      [exact ENV | exact MUn | exact WMn | exact HWLn | exact STn | exact MIn | | exact FSZ1].
    eapply rw_cells_transport; [exact FR1 | exact MUn | exact WMn |]. cbn. lia. }
  clear HEAP1 ST1 MI1 FR1 ENV LS MUn WMn STn MIn HWLn WOKn.

  assert (HBITS : 1 <= num_bits_word (Z.of_nat mx) <= 24) by (clear - HKJ EKJ; subst mx; lia).
  zstep. rewrite (bn_swrap32_small (num_bits_word (Z.of_nat mx) + -1)) by (clear - HBITS; lia).
  setreg 11%Z (Z_to_bv 64 (Z.of_nat kj)) ltac:(f_equal; clear - EKJ; subst mx; lia).
  ub. zstep. zstep.
  rewrite (sllw_small 1 (Z.of_nat kj)) by (clear - HKJ PJ EJ; lia).
  setreg 25%Z (Z_to_bv 64 (Z.of_nat j)) ltac:(f_equal; clear - EJ; lia).
  zstep.
  setreg 27%Z (Z_to_bv 64 (Z.of_nat (2 * j))) ltac:(f_equal; clear - PJ; lia).
  ub. zstep. step.
  (* [comment removed for export] *)
  destruct SOK1 as (_ & _ & _ & _ & _ & _ & CK1).
  apply evt_done. unfold disp_kara. unfold bbind at 1. cbn [bind tree_ops]. fold j.
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_get_leaves ls1); exact (proj1 (proj2 (proj2 CK1)))|].
    eapply (BN_CTX_get_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB) (AD := AD) (EA := EA); [| | | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENVn | exact LSn | unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USED MCP; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENVn).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_get2 CTX). }
  cbv beta. intros [t ls2] Σ2 ms2 [PO LEAF].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVn))].
  cbn [fst snd] in PO, LEAF.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & CP2 & ((TT & HT & ->) & _)).
  assert (E2 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ2 ls2 m2 OW2
               /\ lib_state ls2 m2 OW2 AD EA) by (eapply cenv_postA; [exact ENVn | exact CP2]).
  destruct E2 as (ENV2 & LS2).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP2) as RS2.
  fix_ret. unfold MallocRep.wz.
  pose proof (RS2 _ _ HR) as HR2. pose proof (RS2 _ _ HX) as HX2. pose proof (RS2 _ _ HY) as HY2.
  unfold get_leaf in LEAF. cbn [fst snd] in LEAF. destruct LEAF as (ET & _ & _ & LOTH).
  assert (NTR : t <> rr) by (rewrite ET; intros E; symmetry in E; exact (NPR _ E)).
  assert (NTX : t <> x) by (rewrite ET; intros E; symmetry in E; exact (NPX _ E)).
  assert (NTY : t <> y) by (rewrite ET; intros E; symmetry in E; exact (NPY _ E)).
  assert (EGX : getbn x ls2 = getbn x ls1) by (apply LOTH; rewrite <- ET; congruence).
  assert (EGY : getbn y ls2 = getbn y ls1) by (apply LOTH; rewrite <- ET; congruence).
  clear CP2 ENVn LSn CK1.
  (* [comment removed for export] *)
  destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (_ & ADB2 & _ & _).
  destruct (ref_at_inb _ _ _ _ _ ADB2 HT) as (qt & At & nt & _ & Hint & Rt1 & Rt2).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV2)) Hint) as (TA0 & _ & _ & TAC & _).
  apply implA_from_evt.
  ub; zstep. if_cases KT; zify_cond KT. { exfalso. rewrite ?unsigned_lit in KT by (unfold BnHeapA.ACEIL in *; clear - TA0 Rt1 Rt2 TAC CEIL LO SPR; lia).
                                     unfold BnHeapA.ACEIL in *. clear - KT TA0 Rt1 Rt2 TAC CEIL LO SPR. lia. }
  clear KT.
  assert (HWLs : forall OWx, Forall (w_lib OWx lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp)]) by (intros OWx; constructor; [left; cbn; lia| constructor]).
  assert (WOKs : forall OWx lsx, Forall (w_ok OWx LB lsx AD EA []) [(bv_unsigned sp + -112, bv_unsigned sp)]).
  { intros OWx lsx; constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  env_openA ENV2. unfold mul_frame in FRe. cbn [app] in FRe.
  step.                                                     (* [comment removed for export] *)
  env_closeA HWLs WOKs ENV2 LS2 ENV3 LS3.
  fold (mul_frame (Z_to_bv 64 TT) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) in ENV3.
  assert (EAL2 : al = bn_top (getbn x ls2)) by (rewrite EGX; exact EAL).
  assert (EBL2 : bl = bn_top (getbn y ls2)) by (rewrite EGY; exact EBL).
  rewrite <- EGX, <- EGY.

  zstep. rewrite ?unsigned_lit by (clear - AL23 BL23 PJ; lia). if_cases KA; zify_cond KA.
  { (* [comment removed for export] *)
    replace ((j <? al)%nat || (j <? bl)%nat) with true by (symmetry; apply orb_true_iff; left; apply Nat.ltb_lt; clear - KA; lia).
    apply evt_done.
    eapply mul_path_partA; try eassumption; [clear - USED; lia | clear - HKJ; lia | clear - KA; lia | subst mx; clear - KA HAB HBA; lia | subst mx; clear - HJ2; lia | subst mx; clear - HJ2; lia]. }
  zstep. rewrite ?unsigned_lit by (clear - AL23 BL23 PJ; lia). if_cases KB'; zify_cond KB'.
  { (* [comment removed for export] *)
    replace ((j <? al)%nat || (j <? bl)%nat) with true by (symmetry; apply orb_true_iff; right; apply Nat.ltb_lt; clear - KB'; lia).
    apply evt_done.
    eapply mul_path_partA; try eassumption; [clear - USED; lia | clear - HKJ; lia | subst mx; clear - KB' HAB HBA; lia | clear - KB'; lia | subst mx; clear - HJ2; lia | subst mx; clear - HJ2; lia]. }
  (* [comment removed for export] *)
  replace ((j <? al)%nat || (j <? bl)%nat) with false by (symmetry; apply orb_false_iff; split; apply Nat.ltb_ge; [clear - KA | clear - KB']; lia).
  apply evt_done.
  eapply mul_path_recA; try eassumption; [clear - USED; lia | clear - HKJ; lia | clear - KA; lia | clear - KB'; lia | subst mx; clear - HJ1 KA KB' HAB HBA; lia | subst mx; clear - HJ1 KA KB' HAB HBA; lia].
Qed.

(* [comment removed for export] *)
Lemma mul_zero_pathA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (TOTAL : Z) (w0 : word)
    (m1 : mem) (rr : bnref) (R : Z)
    (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) 0 Σ ls m1 OW ->
  0 <= TOTAL -> lib_state ls m1 OW AD EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls OW AD rr R ->
  evt bsegs (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA TOTAL (fun _ _ _ a0' => a0' = wz 1)
                      (tt, setbn rr (bn_zero_pure (getbn rr ls)) ls) Σ)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24e6a8) fc None m1 (seg_rom bsegs)).
Proof.
  intros until t6. intros ENV HT LS LO HR.
  unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW). unfold mul_frame in FR. cbn [app] in FR.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m1 OW AD EA rr R LS ND HR ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (bn_arr_facts Σ OW LB m1 HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
  specialize (DSEP rr R HR).
  destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HR) as (ACR & ALR & OFR).
  set (b := getbn rr ls) in *.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  unfold MallocRep.wz. ub; zstep. ub; step.
  eapply evt_cut.
  { eapply (BN_zero_ex_specA (Z_to_bv 64 0x24e6b0) (Z_to_bv 64 (bv_unsigned sp + -112))) with (lo := lo) (A := R) (D := Dr) (b := b);
      [exact SR | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; unfold BnHeapA.ACEIL in *; lia
      | exact (AH_shb _ _ _ _ HEAP) | exact ACR | exact ALR | unfold SHHI, BnHeapA.ACEIL in *; lia | exact OFR | reflexivity | clear - SA0 Ra1; lia]. }
  intros ms' PO. unfold bn_small_postA in PO.
  destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MUz & WMz & MIz & STz & SRz).
  rewrite ESP in MUz, STz. fix_ret.
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112); (R, R + 24)]).
  { constructor; [left; cbn [fst snd]; lia|]. constructor; [|constructor].
    right. exists (qs, As, ns). cbn [blk_addr blk_size fst snd]. split; [exact Hins | lia]. }
  assert (WOK : Forall (w_ok OW LB ls AD EA [rr]) [(bv_unsigned sp + -112 - 16, bv_unsigned sp + -112); (R, R + 24)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [|constructor].
    eapply (w_struct OW LB ls AD EA false [rr] _ rr R); [left; reflexivity | exact HR | cbn; lia | cbn; lia]. }
  eapply (rw_cells_transport bsegs _ m1 m3) in FR; [| exact MUz | exact WMz | cbn; unfold BnHeapA.ACEIL in *; lia].
  assert (ENV3 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) 0
                   Σ (setbn rr (bn_zero_pure b) ls) m3 OW).
  { apply cenv_setbnA; [| exact HVR | reflexivity].
    eapply (cenv_silentA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m);
      [exact ENV | exact MUz | exact WMz | exact HWL | exact STz | exact MIz | unfold mul_frame; cbn [app]; exact FR | exact FSZ]. }
  assert (LS3 : lib_state (setbn rr (bn_zero_pure b) ls) m3 OW AD EA).
  { unfold lib_state. eapply (lib_state_close [] ls m3 OW AD EA rr R); [| exact ND | exact HR | | |].
    - eapply lib_state_frame; [exact HEAP | exact LSH | exact MUz | exact WMz | exact WOK].
    - exists Dr. split; [exact SRz|]. eapply bn_arr_of_u64arr; [exact ARR|].
      eapply u64arr_transport; [exact U | exact MUz | exact WMz |]. cbn [disjoint_from]. rewrite LENW. lia.
    - destruct OKR as (O1 & O2 & O3 & O4). unfold bn_okm, bn_zero_pure, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. repeat split; [exact O1 | lia | exact O3 | exact O4].
    - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
  pose proof (cenv_finalA LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ ENV3 LS3 HT)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  clear SR U MUz WMz MIz SRz ST MI.
  ub; zstep. ub; step.
  ub; zstep. do 13 (ub; step).
  release_frame FR STz (bv_unsigned sp). ub; step. ub; step.
  apply evt_done. unfold bn_postA. do 17 eexists. exists m3, OW. split; [reflexivity|]. cbn [fst snd].
  split; [exact F1|]. split; [exact F2|]. split; [exact STz|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
  split; [exact F6|]. split; [exact F7|]. reflexivity.
Qed.

Lemma bn_mul_fixed_top_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (rr x y : bnref) (R X Y : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_MUL_FIXED_STACKA BN_MUL_TOP_COST ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y ->
  a0 = wz R -> a1 = wz X -> a2 = wz Y -> a3 = wz (ad_ctx AD) ->
  nonpool rr -> nonpool x -> nonpool y ->
  implA (bn_mul_fixed_top (tree_ops bptr) rr x y ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA BN_MUL_TOP_COST (fun _ _ _ a0' => a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_MUL_FIXED_TOP) fc None m (seg_rom bsegs)).
Proof.
  intros until Y. intros PRE UW CTX -> HR HX HY -> -> -> -> NPR NPX NPY.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  assert (LOF : lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA) by exact LO'.
  unfold BN_MUL_FIXED_TOP, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof MC_nonneg as MCP.
  destruct (open_ro Σ OW LB m ls AD EA x X HEAP LS HX) as (Dx0 & SX & OKX & _ & X0 & XC & _).
  destruct (open_ro Σ OW LB m ls AD EA y Y HEAP LS HY) as (Dy0 & SY & OKY & _ & Y0 & YC & _).
  pose proof OKX as (_ & TDX & DMX & _). pose proof OKY as (_ & TDY & DMY & _). unfold BN_WORDS_MAX in DMX, DMY.
  unfold bn_cells, MallocRep.wz in SX, SY.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HX) as (ACX & ALX & OFX).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HY) as (ACY & ALY & OFY).
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  unfold bn_mul_fixed_top. unfold bbind at 1 2. unfold bget at 1 2. cbn [bind ret tree_ops tbind fst snd].
  set (al := bn_top (getbn x ls)) in *. set (bl := bn_top (getbn y ls)) in *.
  assert (AL23 : Z.of_nat al < 8388608) by (clear - TDX DMX; unfold bn_dmax in *; lia).
  assert (BL23 : Z.of_nat bl < 8388608) by (clear - TDY DMY; unfold bn_dmax in *; lia).
  assert (AX : 0 < X /\ X + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - X0 XC CEIL LO SPR SPT; lia).
  assert (AY : 0 < Y /\ Y + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Y0 YC CEIL LO SPR SPT; lia).
  apply hide_intro in OFX. apply hide_intro in OFY.
  apply implA_from_evt.
  carve_frame 112%nat ST. do 15 step.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  ub. do 2 zstep. ub. do 2 zstep. do 3 step.   (* [comment removed for export] *)
  zstep. do 2 zstep. shl_with ACX ALX.   (* [comment removed for export] *)
  chk0.
  ub. zstep. do 2 zstep. shl_with ACY ALY.                             (* [comment removed for export] *)
  step. rewrite (sx32_small (Z.of_nat al)) by (clear - AL23; lia).   (* [comment removed for export] *)
  chk0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp - 112, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp - 112, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
  apply rw_cells_CB8_hd in FR.
  lazymatch type of FR with rw_cells _ _ _ ?fr =>
    let pre := drop2 fr in
    assert (ENV : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m pre 0 Σ ls m1 OW)
  end.
  { unfold cenvA, cenv_ok. split; [repeat split; try assumption; try (unfold USTACK_TOP; lia); clear - SP16; Z.div_mod_to_equations; lia|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    match goal with STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ => split; [exact STx|]; split; [exact MIx|] end.
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  lazymatch type of ENV with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    lazymatch pre with C8 ?w :: _ =>
      change pre with (mul_frame w s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) in ENV; set (w0 := w) in * end end.
  pose proof ENV as (OK & HEAP1 & _).
  ub; zstep. if_cases KA0; zify_cond KA0.
  { (* [comment removed for export] *)
    replace ((al =? 0)%nat || (bl =? 0)%nat) with true by (symmetry; apply orb_true_iff; left; apply Nat.eqb_eq; clear - KA0; lia).
    apply evt_done. unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
    eapply mul_zero_pathA; [exact ENV | clear; unfold BN_MUL_TOP_COST, MC; lia | exact LS1 | exact LOF | exact HR]. }
  step. rewrite (sx32_small (Z.of_nat bl)) by (clear - BL23; lia).      (* [comment removed for export] *)
  zstep. if_cases KB0; zify_cond KB0.
  { (* [comment removed for export] *)
    replace ((al =? 0)%nat || (bl =? 0)%nat) with true by (symmetry; apply orb_true_iff; right; apply Nat.eqb_eq; clear - KB0; lia).
    apply evt_done. unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
    eapply mul_zero_pathA; [exact ENV | clear; unfold BN_MUL_TOP_COST, MC; lia | exact LS1 | exact LOF | exact HR]. }
  replace ((al =? 0)%nat || (bl =? 0)%nat) with false by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; [clear - KA0 | clear - KB0]; lia).

  zstep. rewrite (bn_swrap32_small (Z.of_nat al + Z.of_nat bl)) by (clear - AL23 BL23; lia).
  ub. zstep. step.
  (* [comment removed for export] *)
  clear SX SY MU WM HWL WOK FR SHB1 SHB2.
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_start_leaves ls)|].
    eapply (BN_CTX_start_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB) (AD := AD) (EA := EA); [| | | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENV | exact LS1 | unfold BN_CTX_START_STACK, CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear; unfold BN_MUL_TOP_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_start CTX). }
  cbv beta. intros [u1 ls1] Σ1 ms1 [PO LEAF1].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F1 & fc1 & m2 & OW1 & -> & CP1 & _).
  assert (E1 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m
                 (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (0 + MC) Σ1 ls1 m2 OW1
               /\ lib_state ls1 m2 OW1 AD EA) by (eapply cenv_postA; [exact ENV | exact CP1]).
  destruct E1 as (ENV1 & LS1').
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
  fix_ret. unfold MallocRep.wz.
  pose proof (RS1 _ _ HR) as HR1. pose proof (RS1 _ _ HX) as HX1. pose proof (RS1 _ _ HY) as HY1.
  unfold start_leaf in LEAF1. cbn [fst snd] in LEAF1. destruct LEAF1 as (EG1 & _).
  clear CP1 ENV LS1.
  (* [comment removed for export] *)
  cbn [fst snd]. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind with (Q1 := mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST rr x y R X Y
                                     (bn_neg (getbn x ls)) (bn_neg (getbn y ls))).
  2:{ cbv beta. intros [uE lsE] ΣE msE J. cbn [fst snd].
      unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
      eapply (mul_endA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST rr x y R X Y
                (bn_neg (getbn x ls)) (bn_neg (getbn y ls)) (uE, lsE) ΣE msE LOF J). }
  (* [comment removed for export] *)
  pose proof ENV1 as (_ & HEAP2 & _).
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS1') as (IDS1 & ADB1 & _ & _).
  destruct (ref_at_inb _ _ _ _ _ ADB1 HR1) as (qr & Ar & nr & _ & Hinr & Rr1 & Rr2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinr) as (RA0 & _ & _ & RAC & _).
  destruct (ref_at_inb _ _ _ _ _ ADB1 HX1) as (qx & Ax & nx & _ & Hinx & Rx1 & Rx2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinx) as (XA0 & _ & _ & XAC & _).
  destruct (ref_at_inb _ _ _ _ _ ADB1 HY1) as (qy & Ay & ny & _ & Hiny & Ry1 & Ry2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hiny) as (YA0 & _ & _ & YAC & _).
  apply implA_from_evt.
  ub; zstep. if_cases KRX; zify_cond KRX.
  { assert (E : rr = x).
    { destruct (bnref_eq_dec rr x) as [E|NE]; [exact E|exfalso].
      pose proof (struct_disj Σ1 OW1 LB m2 HEAP2 ls1 AD EA IDS1 ADB1 rr x R X NE HR1 HX1) as SD.
      rewrite ?unsigned_lit in KRX by (unfold BnHeapA.ACEIL in *; lia). clear - KRX SD. lia. }
    subst x. replace (bnref_eqb rr rr) with true by (clear; destruct rr; cbn; try reflexivity; symmetry; apply Nat.eqb_refl).
    apply evt_done. cbn [orb bunr unreachable tree_ops]. apply implA_unr. }
  assert (NEX : rr <> x) by (intros E; subst x; apply KRX; rewrite (ref_at_fun _ _ _ _ _ _ ND2 HR1 HX1); reflexivity).
  ub; zstep.
  ub; zstep. if_cases KRY; zify_cond KRY.
  2:{ assert (E : rr = y).
      { destruct (bnref_eq_dec rr y) as [E|NE]; [exact E|exfalso].
        pose proof (struct_disj Σ1 OW1 LB m2 HEAP2 ls1 AD EA IDS1 ADB1 rr y R Y NE HR1 HY1) as SD.
        rewrite ?unsigned_lit in KRY by (unfold BnHeapA.ACEIL in *; lia). clear - KRY SD. lia. }
      subst y. replace (bnref_eqb rr rr) with true by (clear; destruct rr; cbn; try reflexivity; symmetry; apply Nat.eqb_refl).
      apply evt_done. rewrite orb_true_r. cbn [bunr unreachable tree_ops]. apply implA_unr. }
  assert (NEY : rr <> y) by (intros E; subst y; apply KRY; rewrite (ref_at_fun _ _ _ _ _ _ ND2 HR1 HY1); reflexivity).
  rewrite (bnref_eqb_neq rr x NEX), (bnref_eqb_neq rr y NEY). cbn [orb].
  clear KRX KRY.
  assert (EAL1 : al = bn_top (getbn x ls1)) by (rewrite EG1; reflexivity).
  assert (EBL1 : bl = bn_top (getbn y ls1)) by (rewrite EG1; reflexivity).
  rewrite <- (EG1 x), <- (EG1 y).

  zstep. rewrite (bn_swrap32_small (Z.of_nat al - Z.of_nat bl)) by (clear - AL23 BL23; lia).
  ub. zstep.
  eassert (CONT : ((al =? bl)%nat && (al =? 8)%nat = false) -> _).
  2:{ zstep. if_cases K8A; zify_cond K8A.
      { apply CONT. apply andb_false_iff. right. apply Nat.eqb_neq. clear - K8A. lia. }
      zstep. if_cases K8B; zify_cond K8B.
      {
        apply CONT. apply andb_false_iff. left. apply Nat.eqb_neq. intros E. apply K8B. rewrite E, Z.sub_diag. reflexivity. }
      (* [comment removed for export] *)
      assert (E8A : al = 8%nat) by (clear - K8A; lia).
      assert (E8B : bl = 8%nat).
      { change 18446744073709551615 with (Z.ones 64) in K8B. rewrite Z.land_ones in K8B by (clear; lia). change (2 ^ 64) with 18446744073709551616 in K8B.
        clear - K8A K8B AL23 BL23. Z.div_mod_to_equations. lia. }
      rewrite E8A, E8B. cbn [Nat.eqb andb].
      apply evt_done.
      eapply mul_path_comba8A; try eassumption; try (clear; unfold BN_MUL_TOP_COST, MC; lia); [rewrite <- EAL1; exact E8A | rewrite <- EBL1; exact E8B]. }
  intros ENC. rewrite ENC.
  zstep.
  assert (HAL : (0 < al)%nat) by (clear - KA0; lia). assert (HBL : (0 < bl)%nat) by (clear - KB0; lia).
  zstep. rewrite lts_small by (clear - AL23; lia). if_cases K16A; zify_cond K16A.
  { replace (16 <=? al)%nat with false by (symmetry; apply Nat.leb_gt; clear - K16A; lia). cbn [andb].
    apply evt_done. eapply mul_path_normalA; try eassumption; clear; unfold BN_MUL_TOP_COST, MC; lia. }
  zstep. rewrite lts_small by (clear - BL23; lia). if_cases K16B; zify_cond K16B.
  { replace (16 <=? bl)%nat with false by (symmetry; apply Nat.leb_gt; clear - K16B; lia). rewrite andb_false_r. cbn [andb].
    apply evt_done. eapply mul_path_normalA; try eassumption; clear; unfold BN_MUL_TOP_COST, MC; lia. }
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
    apply evt_done. eapply mul_path_normalA; try eassumption; clear; unfold BN_MUL_TOP_COST, MC; lia. }
  (* [comment removed for export] *)
  assert (KU' : 0 <= Z.of_nat al - Z.of_nat bl + 1 <= 2) by (apply (land64_le_small (Z.of_nat al - Z.of_nat bl + 1) 2 ltac:(clear - AL23 BL23; lia) ltac:(lia)); exact KU).
  replace ((16 <=? al)%nat && (16 <=? bl)%nat && (al <=? bl + 1)%nat && (bl <=? al + 1)%nat) with true.
  2:{ symmetry. rewrite !andb_true_iff. repeat split; apply Nat.leb_le; [clear - K16A | clear - K16B | clear - KU' | clear - KU']; lia. }
  apply evt_done.
  eapply mul_path_karaA; try eassumption; try (clear; unfold BN_MUL_TOP_COST, MC; lia); [clear - K16A; lia | clear - K16B; lia | clear - KU'; lia | clear - KU'; lia].
Qed.

(* [comment removed for export] *)
Lemma BN_mul_walkA : BN_mul_walkA_stmt BN_MUL_TOP_STACK BN_MUL_TOP_COST.
Proof.
  unfold BN_mul_walkA_stmt.
  intros until ay. intros PRE UW CTX -> HR HX HY -> -> -> -> NPR NPX NPY.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  pose proof LO as LO'. unfold BN_MUL_TOP_STACK, BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  unfold BN_MUL, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  unfold BN_mul.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply implA_from_evt.
  carve_frame 32%nat ST. do 6 step. zstep. step.           (* [comment removed for export] *)
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp - 32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp - 32, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]).
  pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
  match goal with FRx : rw_cells _ m1 (bv_unsigned sp + -32) ?fr, STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ =>
    let pre := drop2 fr in
    assert (ENV : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m pre 0 Σ ls m1 OW);
    [ unfold cenvA, cenv_ok; split; [repeat split; try assumption; try (unfold USTACK_TOP; lia); clear - SP16; Z.div_mod_to_equations; lia|];
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|];
      split; [exact STx|]; split; [exact MIx|];
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|];
      split; [lia|]; split; [apply cnt_eq_refl|]; split; [apply refs_stable_refl|];
      split; [cbn [app]; exact FRx|]; split; [cbn; lia|]; unfold uw_opt;
      eapply uw_chain_munch_nw; [exact UW | exact MU |]; constructor; [cbn; lia | constructor]
    | ] end.
  pose proof ENV as (OK & HEAP1 & _).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply (bn_mul_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB) (AD := AD) (EA := EA)
             (rr := rr) (x := rx) (y := ry) (R := ar) (X := ax) (Y := ay);
      [| | | reflexivity | exact HR | exact HX | exact HY | reflexivity | reflexivity | reflexivity | reflexivity | exact NPR | exact NPX | exact NPY].
    - eapply cenv_preA; [exact ENV | exact LS1 | unfold BN_MUL_FIXED_STACKA; rewrite MUL_CST_val; clear - LO; lia | lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_mul_ft CTX). }
  cbv beta. intros [u1 ls1] Σ1 ms1 PO.
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -32) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m3 & OW1 & -> & CP1 & ->).
  lazymatch type of ENV with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    assert (E1 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m pre (0 + BN_MUL_TOP_COST) Σ1 ls1 m3 OW1 /\ lib_state ls1 m3 OW1 AD EA)
      by (eapply cenv_postA; [exact ENV | exact CP1]) end.
  destruct E1 as (ENV1 & LS1').
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
  fix_ret. unfold MallocRep.wz.
  clear CP1.
  (* [comment removed for export] *)
  pose proof (RS1 _ _ HR) as HR1.
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
  unfold MallocRep.wz.
  zstep. zstep. step.
  eapply (ctop_callA LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m ltac:(clear - LO; lia) _ _ _ Σ1 ls1 m3 OW1 rr ar);
    [exact ENV1 | exact LS1' | exact HR1 |].
  intros m4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2.
  fix_ret.
  (* [comment removed for export] *)
  pose proof (cenv_finalA LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m _ _ _ _ _ _ ENV2 LS2 ltac:(lia))
    as (F1' & F2 & F3 & F4 & F5 & F6 & F7).
  env_openA ENV2.
  zstep. do 4 step.
  release_frame FRe STe (bv_unsigned sp). step. step.
  apply evt_done. unfold bn_postA. do 17 eexists. exists m4, OW1. split; [reflexivity|]. cbn [fst snd].
  split; [exact F1'|]. split; [exact F2|]. split; [exact STe|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
  split; [exact F6|]. split; [exact F7|]. reflexivity.
Qed.







End WithRT.
