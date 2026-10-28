(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr BnLeaves DivModel.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX BnRepX2 ImplA ImplAX BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA W_smallA W_topA BnAKitA BnCallA W_callsA AsStruct2 AW_num_bits_word W_lshiftA W_copyA W_ctxA W_ctx_endA W_ctx_getA W_fuzzA BnKaraMemA BnCallsKA AW_mul_recursive AW_mul_part_recursive AW_kara_closedA AW_mul_core W_div_tailA W_divA W_bndivA.
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
Definition mul_res (br : bignum bptr) (w : list Z) (top : nat) : bignum bptr :=
  mkBN (bn_d br) (splice (bn_buf br) 0 w) top (bn_neg br) (bn_flags br).

Lemma mul_res_okm : forall br w top, bn_okm br -> limbs w -> (length w <= bn_dmax br)%nat -> (top <= bn_dmax br)%nat -> bn_okm (mul_res br w top).
Proof.
  intros br w top (O1 & O2 & O3 & O4) LW HW HT. unfold bn_okm, mul_res, bn_dmax in *. cbn [bn_buf bn_top bn_flags].
  rewrite splice_length by lia. split; [apply splice_limbs; assumption|]. auto.
Qed.

Definition BN_MUL_FIXED_TOP : Z := 0x24e53c.
Definition BN_MUL : Z := 0x24e4f4.
(* [comment removed for export] *)
Definition MUL_CST : Z := part_stackA CS8A 23.
Definition BN_MUL_FIXED_STACKA : Z := 112 + MUL_CST.
Definition BN_MUL_TOP_STACK : Z := 32 + BN_MUL_FIXED_STACKA.
(* [comment removed for export] *)
Definition BN_MUL_TOP_COST : Z := 4 * MC.

Lemma MUL_CST_val : MUL_CST = 73216.
Proof. reflexivity. Qed.

Lemma rw_cells_CB8_hd : forall segs m A bs rest, rw_cells segs m A (CB 8 bs :: rest) -> rw_cells segs m A (C8 (le_bytes_to_word bs) :: rest).
Proof.
  intros segs m A bs rest H. pose proof H as [[[L W] _] _].
  eapply bk_rw_cells_recast; [exact H | cbn; split; [exact I | exact W] | cbn [cells_bytes cbytes]; rewrite dv_le8_of_bytes by exact L; reflexivity | reflexivity].
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

Lemma implA_post_evt : forall {A} (t : btree bptr A) Σ (Q1 Q : A -> rts RT -> machine_state -> Prop) ms,
  implA t Σ Q1 ms -> (forall a Σ' ms', Q1 a Σ' ms' -> evt bsegs (Q a Σ') ms') -> implA t Σ Q ms.
Proof.
  intros A t Σ Q1 Q ms H HK X Φ S T c Hc Hk.
  apply (H X Φ S T c Hc).
  intros c' (a & X' & Σ' & HΦ & Hc').
  apply (asta_evtA Σ' (Q1 a Σ') (Q a Σ') (HK a Σ') T c' Hc').
  intros c'' Hc''. apply Hk. exists a, X', Σ'. split; [exact HΦ | exact Hc''].
Qed.

(* [comment removed for export] *)
Definition mul_frame (w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 : word) : list cell :=
  [C8 w0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].

(* [comment removed for export] *)
Definition mul_joinA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (TOTAL : Z)
    (rr x y : bnref) (R X Y : Z) (na nb : bool)
    (v : unit * lstate bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 x27 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' w0 used,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) x22 x23 x24 x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
             F' (Z_to_bv 64 MULC_TAIL) fc' None m' (seg_rom bsegs)
    /\ cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ' (snd v) m' OW'
    /\ used <= TOTAL
    /\ lib_state (snd v) m' OW' AD EA
    /\ ref_at (snd v) OW' AD rr R /\ ref_at (snd v) OW' AD x X /\ ref_at (snd v) OW' AD y Y
    /\ bn_neg (getbn x (snd v)) = na /\ bn_neg (getbn y (snd v)) = nb.

Lemma mul_endA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (TOTAL : Z)
    (rr x y : bnref) (R X Y : Z) (na nb : bool) (v : unit * lstate bptr) (Σ' : rts RT) (ms' : machine_state),
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras TOTAL rr x y R X Y na nb v Σ' ms' ->
  implA (BN_CTX_end ops (setbn rr (bn_with_neg (getbn rr (snd v)) (xorb na nb)) (snd v))) Σ'
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA TOTAL (fun _ _ _ a0' => a0' = wz 1)) ms'.
Proof.
  intros until ms'. intros LO (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x22 & x23 & x24 & x25 & x27 & t3 & t4 & t5 & t6 & FE & fcE
                             & mE & OWE & w0 & used & -> & ENV & USED & LS & HR & HX & HY & ENA & ENB).
  destruct v as [[] lsE]. cbn [fst snd] in *.
  unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW). unfold mul_frame in FR. cbn [app] in FR.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (open_ro Σ' OWE LB mE lsE AD EA x X HEAP LS HX) as (Dx & SX & _ & _ & X0 & XC & _).
  destruct (open_ro Σ' OWE LB mE lsE AD EA y Y HEAP LS HY) as (Dy & SY & _ & _ & Y0 & YC & _).
  unfold bn_cells, MallocRep.wz in SX, SY. rewrite ENA in SX. rewrite ENB in SY.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HX) as (ACX & ALX & OFX).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HY) as (ACY & ALY & OFY).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HR) as (ACR & ALR & OFR).
  destruct (lib_state_open [] lsE mE OWE AD EA rr R LS ND HR ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (bn_arr_facts Σ' OWE LB mE HEAP lsE AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
  specialize (DSEP rr R HR).
  destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
  set (b := getbn rr lsE) in *.
  unfold bn_cells, MallocRep.wz in SR.
  assert (NA : 0 <= Z.b2z na <= 1) by (destruct na; cbn; lia).
  assert (NB : 0 <= Z.b2z nb <= 1) by (destruct nb; cbn; lia).
  assert (AX : 0 < X /\ X + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - X0 XC CEIL LO SPR SPT; lia).
  assert (AY : 0 < Y /\ Y + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Y0 YC CEIL LO SPR SPT; lia).
  assert (ARR24 : 0 < R /\ R + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SA0 SAC Ra1 Ra2 CEIL LO SPR SPT; lia).
  pose proof (munch_refl [(R, R + 24)]%Z mE) as MU. pose proof (wmono_refl bsegs mE) as WM.
  assert (OFF : offshW [(R, R + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFR; lia).
  apply hide_intro in OFX. apply hide_intro in OFY. apply hide_intro in OFR. apply hide_intro in SAI. apply hide_intro in DI.
  apply implA_from_evt.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ub. zstep.   (* [comment removed for export] *)
  do 2 zstep. shl_with ACY ALY. chk0.   (* [comment removed for export] *)
  zstep. do 2 zstep. shl_with ACX ALX.   (* [comment removed for export] *)
  step. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).   (* [comment removed for export] *)
  chk0.
  zstep. do 2 zstep. shl_with ACR ALR.
  step. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
  chk0.
  zstep.
  setreg 10%Z (Z_to_bv 64 (Z.b2z (xorb na nb))) ltac:(clear; destruct na, nb; reflexivity).
  zstep.                                                    (* [comment removed for export] *)
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
  match goal with STx : stk _ m1 _ _, MIx : mem_inv _ m1, FRx : rw_cells _ m1 (bv_unsigned sp + -112) _ |- _ =>
    assert (ENVN : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ' lsN m1 OWE);
    [ apply cenv_setbnA; [| exact HVR | reflexivity];
      eapply (cenv_silentA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m);
        [exact ENV | exact MU | exact WM | exact HWL | exact STx | exact MIx | unfold mul_frame; cbn [app]; exact FRx | cbn; lia]
    | ] end.
  clear SR U MU WM LSH ENV LS.
  ub; zstep. if_cases KE; zify_cond KE; [|exfalso; apply KE; reflexivity]. clear KE.
  ub; zstep. ub; step.                                              (* [comment removed for export] *)
  ub; zstep. ub; step.                                              (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evt_done. fold b. fold lsN.
  eapply implA_post_evt.
  { eapply BN_CTX_end_walkA with (lo := lo) (OW := OWE) (LB := LB) (AD := AD) (EA := EA); [| reflexivity | reflexivity].
    eapply cenv_preA; [exact ENVN | exact LSN | unfold BN_CTX_END_STACK; clear - LO; lia | clear - USED; lia]. }
  cbv beta. intros [uE lsF] ΣF msF PO.
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) TOTAL Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVN))].
  cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & FF & fcF & mF & OWF & -> & CPF & _).
  assert (EF : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + 0) ΣF lsF mF OWF
               /\ lib_state lsF mF OWF AD EA) by (eapply cenv_postA; [exact ENVN | exact CPF]).
  destruct EF as (ENVF & LSF).
  cbn [fst snd] in *.
  fix_ret.
  pose proof (cenv_finalA LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ ENVF LSF ltac:(clear - USED; lia))
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  env_openA ENVF. unfold mul_frame in FRe. cbn [app] in FRe.
  ub; zstep. do 13 (ub; step).
  release_frame FRe STe (bv_unsigned sp). ub; step. ub; step.
  apply evt_done. unfold bn_postA. do 17 eexists. exists mF, OWF. split; [reflexivity|]. cbn [fst snd].
  split; [exact F1|]. split; [exact F2|]. split; [exact STe|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
  split; [exact F6|]. split; [exact F7|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mul_finish1A : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (TOTAL used : Z) (w0 : word)
    (Σ2 : rts RT) (ls2 : lstate bptr) (m2 : mem) (OW2 : list block) (rr x y : bnref) (R X Y Dr n8 CST : Z)
    (w : list Z) (topn : nat) (x22 x23 x24 x25 x27 : word) (ms' : machine_state),
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ2 ls2 m2 OW2 ->
  used <= TOTAL -> lib_state ls2 m2 OW2 AD EA ->
  0 <= CST -> lo <= bv_unsigned sp - 112 - CST ->
  ref_at ls2 OW2 AD rr R -> ref_at ls2 OW2 AD x X -> ref_at ls2 OW2 AD y Y -> rr <> x -> rr <> y ->
  rw_cells bsegs m2 R (bn_cells Dr (getbn rr ls2)) -> bn_arr m2 OW2 Dr (getbn rr ls2) ->
  limbs w -> (0 < length w <= bn_dmax (getbn rr ls2))%nat -> (topn <= bn_dmax (getbn rr ls2))%nat -> n8 = 8 * Z.of_nat (length w) ->
  mulc_postA sp gp (wz TP_A) m2 lo R Dr (getbn rr ls2) F fc sp (Z_to_bv 64 (ad_ctx AD)) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R)
             x22 x23 x24 x25 x27 [(Dr, Dr + n8); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)] topn w (fun _ => True) ms' ->
  mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras TOTAL rr x y R X Y
            (bn_neg (getbn x ls2)) (bn_neg (getbn y ls2)) (tt, setbn rr (mul_res (getbn rr ls2) w topn) ls2) Σ2 ms'.
Proof.
  intros until ms'. intros ENV USED LS HCST LO HR HX HY NEX NEY SR ARR LW [HW0 HWD] HTD ->
    (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & -> & MU & WM & MI3 & SR3 & HR3 & ST3 & _).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW). unfold mul_frame in FR. cbn [app] in FR.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls2 m2 OW2 AD EA rr R LS ND HR ltac:(intros [])) as (_ & OKR & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (bn_arr_facts Σ2 OW2 LB m2 HEAP ls2 AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
  pose proof (DSEP rr R HR) as DSR.
  destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
  set (br := getbn rr ls2) in *.
  unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
  2:{ exfalso. destruct ARR as [_ Eb]. unfold bn_dmax in HWD. rewrite Eb in HWD. cbn [length] in HWD. lia. }
  destruct ARR as [HinR _].
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HinR) as (_ & _ & _ & _ & DRI).
  assert (HWL : Forall (w_lib OW2 lo (bv_unsigned sp)) [(Dr, Dr + 8 * Z.of_nat (length w)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]).
  { constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
    constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
    constructor; [left; cbn [fst snd]; lia | constructor]. }
  assert (WOK : Forall (w_ok OW2 LB ls2 AD EA [rr]) [(Dr, Dr + 8 * Z.of_nat (length w)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]).
  { constructor; [eapply (w_limbs OW2 LB ls2 AD EA false [rr] _ rr pr Dr); [left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
    constructor; [eapply (w_struct OW2 LB ls2 AD EA false [rr] _ rr R); [left; reflexivity | exact HR | cbn; lia | cbn; lia]|].
    constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
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
    - apply mul_res_okm; [exact OKR | exact LW | lia | exact HTD].
    - apply ids_ok_setbn_same; [exact IDS | exact HVR |]. unfold bn_blocks, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
  unfold mul_joinA. do 23 eexists. exists m3, OW2, w0, used. split; [reflexivity|]. cbn [fst snd]. fold lsN.
  split.
  { apply cenv_setbnA; [| exact HVR | fold br; unfold mul_res, bn_blocks; cbn [bn_d bn_buf bn_dmax bn_top]; rewrite ?Edr; reflexivity].
    eapply (cenv_silentA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m);
      [exact ENV | exact MU | exact WM | exact HWL | exact ST3 | exact MI3 | | exact FSZ].
    unfold mul_frame. cbn [app]. eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. cbn. unfold BnHeapA.ACEIL in *. lia. }
  split; [exact USED|]. split; [exact LSN|].
  split; [apply ref_at_setbn; exact HR|]. split; [apply ref_at_setbn; exact HX|]. split; [apply ref_at_setbn; exact HY|].
  unfold lsN. rewrite !getbn_setbn_other by assumption. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arr_pos : forall Σ OW LB m D (b : bignum bptr), AHEAP Σ OW LB m -> bn_arr m OW D b -> (0 < bn_dmax b)%nat ->
  0 < D /\ (D + 8 * Z.of_nat (bn_dmax b) <= 65536 \/ 12570624 <= D).
Proof.
  intros Σ OW LB m D b HEAP ARR HD. unfold bn_arr in ARR. destruct (bn_d b) as [p|] eqn:E.
  - destruct ARR as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & _ & AI). lia.
  - destruct ARR as [_ Eb]. exfalso. unfold bn_dmax in HD. rewrite Eb in HD. cbn in HD. lia.
Qed.

(* [comment removed for export] *)
Lemma core_premsA : forall Σ OW LB m ls AD EA rr x y R X Y Dr al bl lo SPv,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA -> stk bsegs m lo (SPv + -112) -> mem_inv bsegs m ->
  ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y -> rr <> x -> rr <> y ->
  rw_cells bsegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  (al <= bn_top (getbn x ls))%nat -> (bl <= bn_top (getbn y ls))%nat -> (0 < al)%nat -> (0 < bl)%nat -> (al + bl <= bn_dmax (getbn rr ls))%nat ->
  ACEIL <= lo -> lo <= SPv - 112 - MUL_CST -> SPv + 16 <= USTACK_TOP ->
  exists Dx Dy,
    mulc_preA (Z_to_bv 64 SPv) lo R X Y Dr Dx Dy MUL_CST (getbn rr ls) (firstn al (bn_buf (getbn x ls))) (firstn bl (bn_buf (getbn y ls)))
    /\ mulc_memA (Z_to_bv 64 SPv) m lo R X Y Dr Dx Dy (getbn rr ls) (firstn al (bn_buf (getbn x ls))) (firstn bl (bn_buf (getbn y ls))).
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
  exists Dx, Dy. split.
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
Lemma mul_path_normalA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (used : Z) (w0 : word)
    (Σ1 : rts RT) (ls1 : lstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z) (al bl : nat)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x27 t3 t4 t5 t6 : word),
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ1 ls1 m1 OW1 ->
  used + MC <= BN_MUL_TOP_COST -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls1 m1 OW1 AD EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls1 OW1 AD rr R -> ref_at ls1 OW1 AD x X -> ref_at ls1 OW1 AD y Y -> rr <> x -> rr <> y ->
  al = bn_top (getbn x ls1) -> bl = bn_top (getbn y ls1) -> (0 < al)%nat -> (0 < bl)%nat ->
  implA (disp_normal rr (firstn al (bn_buf (getbn x ls1))) (firstn bl (bn_buf (getbn y ls1))) (al + bl) ls1) Σ1
    (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST rr x y R X Y (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat bl)) x25
             (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24e7c0) fc None m1 (seg_rom bsegs)).
Proof.
  intros until t6. intros ENV USED CTX LS LO HR HX HY NEX NEY EAL EBL HAL HBL.
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK1).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_okm_getbn rr ls1 SOK1 HVR) as (_ & TDR1 & _).
  pose proof (st_okm_getbn x ls1 SOK1 HVX) as (LMX & TDX & DMX & _). pose proof (st_okm_getbn y ls1 SOK1 HVY) as (LMY & TDY & DMY & _).
  unfold BN_WORDS_MAX in DMX, DMY.
  set (la := firstn al (bn_buf (getbn x ls1))). set (lb := firstn bl (bn_buf (getbn y ls1))).
  assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
  assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
  unfold MallocRep.wz. apply implA_from_evt. do 2 (ub; zstep). ub; step.
  (* [comment removed for export] *)
  apply evt_done. unfold disp_normal. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves rr (al + bl) ls1 HVR TDR1)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB) (AD := AD) (EA := EA) (r := rr) (a := R) (words := (al + bl)%nat);
      [| | | reflexivity | exact HR | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia].
    - eapply cenv_preA; [exact ENV | exact LS | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | exact USED].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_wexpn CTX). }
  cbv beta. intros [u2 ls2] Σ2 ms2 [PO LEAF].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP].
  cbn [fst snd] in PO, LEAF.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & CP & (-> & HDM & _ & _)).
  assert (E2 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ2 ls2 m2 OW2
               /\ lib_state ls2 m2 OW2 AD EA) by (eapply cenv_postA; [exact ENV | exact CP]).
  destruct E2 as (ENV2 & LS2).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
  fix_ret.
  pose proof (RS _ _ HR) as HR2. pose proof (RS _ _ HX) as HX2. pose proof (RS _ _ HY) as HY2.
  destruct LEAF as (LOTH & _).
  assert (EGX : getbn x ls2 = getbn x ls1) by (apply LOTH; exact NEX).
  assert (EGY : getbn y ls2 = getbn y ls1) by (apply LOTH; exact NEY).
  clear CP ENV LS.
  (* [comment removed for export] *)
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
  (* [comment removed for export] *)
  pose proof ENV2 as (_ & HEAP2 & ST2 & MI2 & _).
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  destruct (lib_state_open [] ls2 m2 OW2 AD EA rr R LS2 ND2 HR2 ltac:(intros [])) as ((Dr & SR & ARR) & OKR & _).
  destruct (core_premsA Σ2 OW2 LB m2 ls2 AD EA rr x y R X Y Dr al bl lo (bv_unsigned sp) HEAP2 LS2 ST2 MI2 HR2 HX2 HY2 NEX NEY SR ARR
              ltac:(rewrite EGX; lia) ltac:(rewrite EGY; lia) HAL HBL HDM CEIL ltac:(unfold BN_MUL_FIXED_STACKA in LO'; clear - LO'; lia) ltac:(unfold USTACK_TOP; clear - SPT; lia)) as (Dx & Dy & PREA & MEMA).
  rewrite EGX, EGY in PREA, MEMA. fold la lb in PREA. fold la lb in MEMA.
  pose proof (mul_normal_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY)) as (LW & _ & NW).
  rewrite LLA, LLB in NW.
  replace ((al =? 0)%nat || (bl =? 0)%nat) with false in NW by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; lia).
  set (br := getbn rr ls2) in *.
  rewrite Z_to_bv_bv_unsigned in PREA, MEMA.
  pose proof PREA as (_ & _ & _ & _ & (R0 & R24 & _) & _).
  ub; zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ R0 R24 LO SPR. lia. }
  clear KZ.
  replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
  eapply evt_mono.
  { eapply (mulc_normalA sp gp (Z_to_bv 64 TP_A) m2 lo R X Y Dr Dx Dy MUL_CST br la lb PREA MEMA F2 fc2).
    - rewrite LLA, LLB. exact HDM.
    - rewrite MUL_CST_val. lia. }
  intros ms' PO.
  eapply (mul_finish1A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST (used + MC) w0 Σ2 ls2 m2 OW2 rr x y R X Y Dr
            (8 * (Z.of_nat (length la) + Z.of_nat (length lb))) MUL_CST (mul_normal la lb) (length la + length lb)%nat) in PO;
    [ | exact ENV2 | exact USED | exact LS2 | rewrite MUL_CST_val; lia | rewrite MUL_CST_val; clear - LO; lia | exact HR2 | exact HX2 | exact HY2 | exact NEX | exact NEY
      | exact SR | | exact LW | | | ].
  - rewrite EGX, EGY in PO. fold br. rewrite LLA, LLB in PO. exact PO.
  - subst br. unfold bn_arr in *. exact ARR.
  - rewrite NW. fold br. clear - HDM HAL. lia.
  - rewrite LLA, LLB. fold br. exact HDM.
  - rewrite NW, LLA, LLB. lia.
Qed.

(* [comment removed for export] *)
Lemma mul_path_comba8A : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z) (used : Z) (w0 : word)
    (Σ1 : rts RT) (ls1 : lstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x27 t3 t4 t5 t6 : word),
  cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ1 ls1 m1 OW1 ->
  used + MC <= BN_MUL_TOP_COST -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls1 m1 OW1 AD EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls1 OW1 AD rr R -> ref_at ls1 OW1 AD x X -> ref_at ls1 OW1 AD y Y -> rr <> x -> rr <> y ->
  bn_top (getbn x ls1) = 8%nat -> bn_top (getbn y ls1) = 8%nat ->
  implA (disp_comba8 rr (firstn 8 (bn_buf (getbn x ls1))) (firstn 8 (bn_buf (getbn y ls1))) ls1) Σ1
    (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST rr x y R X Y (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 8) (Z_to_bv 64 16) (Z_to_bv 64 8) x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24e62c) fc None m1 (seg_rom bsegs)).
Proof.
  intros until t6. intros ENV USED CTX LS LO HR HX HY NEX NEY EAL0 EBL0.
  set (al := 8%nat). set (bl := 8%nat).
  assert (EAL : al = bn_top (getbn x ls1)) by (symmetry; exact EAL0). assert (EBL : bl = bn_top (getbn y ls1)) by (symmetry; exact EBL0).
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK1).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_okm_getbn rr ls1 SOK1 HVR) as (_ & TDR1 & _).
  pose proof (st_okm_getbn x ls1 SOK1 HVX) as (LMX & TDX & DMX & _). pose proof (st_okm_getbn y ls1 SOK1 HVY) as (LMY & TDY & DMY & _).
  unfold BN_WORDS_MAX in DMX, DMY.
  set (la := firstn al (bn_buf (getbn x ls1))). set (lb := firstn bl (bn_buf (getbn y ls1))).
  assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
  assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
  unfold MallocRep.wz. apply implA_from_evt. do 2 (ub; zstep). ub; step.
  (* [comment removed for export] *)
  apply evt_done. unfold disp_comba8. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves rr 16 ls1 HVR TDR1)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB) (AD := AD) (EA := EA) (r := rr) (a := R) (words := 16%nat);
      [| | | reflexivity | exact HR | reflexivity | reflexivity | lia].
    - eapply cenv_preA; [exact ENV | exact LS | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | exact USED].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_wexpc CTX). }
  cbv beta. intros [u2 ls2] Σ2 ms2 [PO LEAF].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP].
  cbn [fst snd] in PO, LEAF.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & CP & (-> & HDM & _ & _)).
  assert (E2 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ2 ls2 m2 OW2
               /\ lib_state ls2 m2 OW2 AD EA) by (eapply cenv_postA; [exact ENV | exact CP]).
  destruct E2 as (ENV2 & LS2).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
  fix_ret.
  pose proof (RS _ _ HR) as HR2. pose proof (RS _ _ HX) as HX2. pose proof (RS _ _ HY) as HY2.
  destruct LEAF as (LOTH & _).
  assert (EGX : getbn x ls2 = getbn x ls1) by (apply LOTH; exact NEX).
  assert (EGY : getbn y ls2 = getbn y ls1) by (apply LOTH; exact NEY).
  clear CP ENV LS.
  (* [comment removed for export] *)
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
  (* [comment removed for export] *)
  pose proof ENV2 as (_ & HEAP2 & ST2 & MI2 & _).
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  destruct (lib_state_open [] ls2 m2 OW2 AD EA rr R LS2 ND2 HR2 ltac:(intros [])) as ((Dr & SR & ARR) & OKR & _).
  destruct (core_premsA Σ2 OW2 LB m2 ls2 AD EA rr x y R X Y Dr al bl lo (bv_unsigned sp) HEAP2 LS2 ST2 MI2 HR2 HX2 HY2 NEX NEY SR ARR
              ltac:(rewrite EGX; lia) ltac:(rewrite EGY; lia) ltac:(lia) ltac:(lia) ltac:(subst al bl; lia) CEIL ltac:(unfold BN_MUL_FIXED_STACKA in LO'; clear - LO'; lia) ltac:(unfold USTACK_TOP; clear - SPT; lia))
    as (Dx & Dy & PREA & MEMA).
  rewrite EGX, EGY in PREA, MEMA. fold la lb in PREA. fold la lb in MEMA.
  pose proof (mul_comba8_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY) LLA LLB) as (LW & NW & _).
  set (br := getbn rr ls2) in *.
  rewrite Z_to_bv_bv_unsigned in PREA, MEMA.
  pose proof PREA as (_ & _ & _ & _ & (R0 & R24 & _) & _).
  ub; zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ R0 R24 LO SPR. lia. }
  clear KZ.
  pose proof (mulc_comba8A sp gp (Z_to_bv 64 TP_A) m2 lo R X Y Dr Dx Dy MUL_CST br la lb PREA MEMA CS8A F2 fc2) as CORE.
  rewrite LLA, LLB in CORE. change (Z.of_nat al) with 8 in CORE. change (Z.of_nat bl) with 8 in CORE.
  eapply evt_mono.
  { eapply CORE; [exact comba8_okA | rewrite MUL_CST_val; unfold CS8A; lia | reflexivity | reflexivity | exact HDM]. }
  clear CORE. intros ms' PO.
  eapply (mul_finish1A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m Σ ls OW LB AD EA lo ras BN_MUL_TOP_COST (used + MC) w0 Σ2 ls2 m2 OW2 rr x y R X Y Dr
            (8 * 16) MUL_CST (mul_comba8 la lb) 16%nat) in PO;
    [ | exact ENV2 | exact USED | exact LS2 | rewrite MUL_CST_val; lia | rewrite MUL_CST_val; clear - LO; lia | exact HR2 | exact HX2 | exact HY2 | exact NEX | exact NEY
      | exact SR | | exact LW | | | ].
  - rewrite EGX, EGY in PO. fold br. exact PO.
  - subst br. unfold bn_arr in *. exact ARR.
  - rewrite NW. fold br. clear - HDM. lia.
  - fold br. exact HDM.
  - rewrite NW. reflexivity.
Qed.

End WithRT.
