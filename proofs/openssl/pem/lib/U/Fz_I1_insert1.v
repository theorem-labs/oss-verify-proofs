(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma le8_of_bytes' : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (Printf_lib.bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma cb8_c8_in' : forall m A pre post bs, rw_cells usegs m A (pre ++ CB 8 bs :: post) -> rw_cells usegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes' by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Lemma agree_munch : forall (W : list (Z * Z)) (P : Z -> Prop) m m', agree_on P m m' -> (forall a, outside W a -> P a) -> munch W m m'.
Proof.
  intros W P m m' AG HW x Hx. pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
  destruct (AG (bv_unsigned x) XR (HW _ Hx)) as [E _]. rewrite wa_unsigned_id in E. exact E.
Qed.


(* [comment removed for export] *)
Lemma split_close : forall (T : bptr -> Prop) s LBall LB L m m' (sp' : word) tp lo Bd SP lh pl pb B nmb na bks p nn stay' moved' s0 LB0 L0 m0,
  cstate s LBall LB L m sp' tp lo Bd -> lh_raw DVERR m LBall L lh pl pb B nmb na bks ->
  0 <= p < nn -> nn < na -> nth (Z.to_nat nn) bks [] = [] ->
  mem_inv usegs m' -> wmono usegs m m' ->
  chain DVERR m' LBall L (B + 8 * p) stay' -> chain DVERR m' LBall L (B + 8 * nn) moved' ->
  Permutation (stay' ++ moved') (nth (Z.to_nat p) bks []) ->
  agree_on (fun a => ~ ((lh + 56 <= a < lh + 68) \/ split_W (B + 8 * p) (B + 8 * nn) (nth (Z.to_nat p) bks []) a)) m m' ->
  cframe T [] SP s0 LB0 L0 m0 s LBall L m -> alloc_ceiling <= SP -> lo <= bv_unsigned sp' ->
  (forall b, In b LBall -> lh_T pl pb bks (blk_id b) -> forall b0, In b0 LB0 -> ~ T (blk_id b0) -> blk_id b0 <> blk_id b) ->
  cstate s LBall LB L m' sp' tp lo Bd
  /\ cframe T [] SP s0 LB0 L0 m0 s LBall L m'
  /\ lh_raw DVERR m' LBall L lh pl pb B nmb na (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))
  /\ Permutation (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))) (concat bks).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros T s LBall LB L m m' sp' tp lo Bd SP lh pl pb B nmb na bks p nn stay' moved' s0 LB0 L0 m0 CST RAW PR NNA EMP MI' WM' CS CM PM AG FRM HSP LSP TFR.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & (lb & LATCH) & _ & GLO).
  pose proof RAW as (OL & RL & OB & RB & LEN & CH & ND).
  destruct (split_raw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP RAW PR NNA EMP CS CM PM AG) as [RAW' PMC].
  set (nsp := nth (Z.to_nat p) bks []) in *.
  set (W := ((lh + 56, lh + 68) :: split_ivs (B + 8 * p) (B + 8 * nn) nsp)%Z).
  assert (MU' : munch W m m').
  { eapply agree_munch; [exact AG|]. intros a Ha. unfold W in Ha. cbn [outside] in Ha. destruct Ha as [H1 H2]. apply split_ivs_outside in H2. tauto. }
  assert (OWNP : forall q A, In (q, A) nsp -> In (q, A, 24) LBall /\ 0 < A /\ A + 24 <= alloc_ceiling).
  { intros q A Hq. pose proof (CH p ltac:(lia)) as CP. split; [exact (proj1 (chain_owns _ _ _ _ _ _ CP q A Hq))|].
    destruct CP as (c0 & SS & _). exact (lseg_ranges _ _ _ _ _ _ _ SS q A Hq). }
  assert (BLKS : Forall (fun iv => exists b, In b LBall /\ lh_T pl pb bks (blk_id b) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) W).
  { unfold W, split_ivs. constructor; [| constructor; [| constructor]].
    - exists (pl, lh, 104). split; [exact (proj1 OL)|]. split; [left; reflexivity|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    - exists (pb, B, 8 * na). split; [exact (proj1 OB)|]. split; [right; left; reflexivity|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    - exists (pb, B, 8 * na). split; [exact (proj1 OB)|]. split; [right; left; reflexivity|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    - apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as ([q A] & <- & Hq). cbn [fst snd].
      exists (q, A, 24). split; [exact (proj1 (OWNP q A Hq))|]. split; [| unfold blk_addr, blk_size; cbn [fst snd]; lia].
      right; right. apply in_map_iff. exists (q, A). split; [reflexivity|]. eapply in_nth_concat. exact Hq. }
  assert (BR : forall b, In b LBall -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (RHEAP_block_range_proof _ _ _ b HP Hb)).
  assert (OUTW : forall a, (alloc_ceiling <= a \/ (0x10000 <= a < 0x353000)) -> outside W a).
  { intros a Ha. clear - BLKS BR Ha. induction BLKS as [|[x y] W0 (b & Hb & _ & H1 & H2) _ IH]; cbn [outside]; [exact I|]. split; [| exact IH].
    cbn [fst snd] in H1, H2. destruct (BR b Hb) as (_ & _ & _ & X1 & X2). lia. }
  pose proof (agree_on_of_munch _ _ _ MU' WM') as AGW.
  split. { eapply (cstate_seg' W _ _ _ _ m m' sp' sp' tp lo Bd Bd); [exact CST| exact MU'| exact WM'| exact MI'| | lia| lia| | | exact SPB].
    - eapply Forall_impl; [| exact BLKS]. intros [x y] (b & Hb & _ & H1 & H2). cbn [fst snd] in H1, H2. apply (cwin_block _ _ _ b); assumption.
    - exists lb. eapply rw_cells_agree; [exact AGW| exact LATCH|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply OUTW. unfold LX_FLAGS in Ha. lia.
    - eapply stk_agree; [exact AGW| exact ST|]. intros a Ha. apply OUTW. lia. }
  split; [| split; [exact RAW'| exact PMC]].
  eapply cframe_seg; [exact FRM| exact MU'| exact WM'| exact HP| exact HSP|].
  eapply Forall_impl; [| exact BLKS]. intros [x y] (b & Hb & TB & H1 & H2). cbn [fst snd] in H1, H2. apply (cseg_ok_block _ _ _ _ _ b); try assumption. exact (TFR b Hb TB).
Qed.


(* [comment removed for export] *)
Definition lhi_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (m : mem) (lo Bd lh : Z) (pl pb : bptr) (nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data : Z)
    : nat -> @clist bptr -> PState -> machine_state -> Prop :=
  fun f1 L1 st1 ms1 => exists (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 hs : word) (m1 : mem) (LBall1 : list block)
                              (pb1 : bptr) (B1 nmb1 : Z) (g1 : lh_geo) (bks1 : list (list (bptr * Z))) (j0 : list byte),
    ms1 = MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y1 y2 y3 sp (Z_to_bv 64 lh) y4 y5 y6 y7 y8 y9 y10 y11
                  (Z_to_bv 64 data) y12 y13 y14 y15 s7 s8 s9 s10 s11 y16 y17 y18 y19)
             F (Z_to_bv 64 0xe9c70) fc None m1 (seg_rom usegs)
    /\ (f - 2 <= f1)%nat
    /\ cstate st1 LBall1 LB L1 m1 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd
    /\ cframe (lh_T pl pb bks) [] (bv_unsigned sp) s LBall L m st1 LBall1 L1 m1
    /\ lh_rep DVERR m1 LBall1 L1 ERR_FNS lh pl pb1 B1 nmb1 g1 bks1 /\ g_items g1 = g_items g
    /\ rw_cells usegs m1 (bv_unsigned sp + -80) (lhi_frame j0 hs ra s0 s1 s2 s3 s4 s5 s6)
    /\ cgrow L L1 (wA nmb1 - wA nmb) (wB nmb1 - wB nmb) (wBig nmb1 - wBig nmb) /\ nmb <= nmb1 <= 8 * g_na g1
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ lh_T pl pb bks q -> ~ lh_T pl pb1 bks1 q).

(* [comment removed for export] *)
Definition lhi_double_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (m : mem) (lo Bd lh : Z) (pl pb : bptr) (nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data : Z)
    : nat -> @clist bptr -> PState -> machine_state -> Prop :=
  fun f2 L2 st2 ms2 => exists (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 x40 x48 err pad : word) (m2 : mem) (LBall2 : list block) (pb2 : bptr) (B2 nmb2 : Z),
    ms2 = MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y1 y2 y3 sp (Z_to_bv 64 lh) (Z_to_bv 64 (g_nn g)) (Z_to_bv 64 0) y4 y5 y6 y7 y8 y9
                  (Z_to_bv 64 data) (Z_to_bv 64 (g_p g)) (Z_to_bv 64 (g_na g)) (Z_to_bv 64 (g_pmax g)) y10 s7 s8 s9 s10 s11 y11 y12 y13 y14)
             F (Z_to_bv 64 0xe9d14) fc None m2 (seg_rom usegs)
    /\ (f - 2 <= f2)%nat
    /\ cstate st2 LBall2 LB L2 m2 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd
    /\ cframe (fun q => q = pl \/ q = pb) [] (bv_unsigned sp + -80) s LBall L m st2 LBall2 L2 m2
    /\ lh_raw DVERR m2 LBall2 L2 lh pl pb2 B2 nmb2 (2 * g_na g) (bks ++ repeat [] (Z.to_nat (g_na g)))
    /\ rw_cells usegs m2 lh (lhs_cells B2 (g_nn g) (2 * g_na g) (g_p g) (g_na g) (g_items g) x40 x48 err pad)
    /\ cgrow L L2 (wA nmb2 - wA nmb) (wB nmb2 - wB nmb) (wBig nmb2 - wBig nmb) /\ nmb <= nmb2 <= 16 * g_na g
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pb -> q <> pb2).

Definition lhi_double_stmt : Prop :=
  forall (sp gp tp s7 s8 s9 s10 s11 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data lo Bd : Z),
  (2 <= f)%nat -> croom L 1 1 (LHA_MAX + 8192) ->
  cstate s LBall LB L m (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd -> 80 <= bv_unsigned sp ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> nmb <= 8 * g_na g ->
  lo <= bv_unsigned sp - LHI_STACK ->
  climpl f L s
    (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp z1 z2 z3 sp (Z_to_bv 64 lh) z4 z5 z6 z7 z8 z9 z10 z11
             (Z_to_bv 64 data) (Z_to_bv 64 (g_p g)) (Z_to_bv 64 (g_na g)) (Z_to_bv 64 (g_pmax g)) z12 s7 s8 s9 s10 s11 z13 z14 z15 z16)
        F (Z_to_bv 64 0xe9cbc) fc None m (seg_rom usegs))
    (lhi_double_post sp gp tp s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd lh pl pb nmb g bks data).

Lemma lhi_head : lhi_double_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data lo Bd : Z),
  (2 <= f)%nat -> croom L 1 1 (LHA_MAX + 8192) ->
  cstate s LBall LB L m sp tp lo Bd ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> nmb <= 8 * g_na g ->
  lo <= bv_unsigned sp - LHI_STACK ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lh) (Z_to_bv 64 data) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_LH_INSERT) fc None m (seg_rom usegs))
    (lhi_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd lh pl pb nmb g bks data).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros DBL ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lh pl pb B nmb g bks data lo Bd
         Hf ROOM CST REP NMB SLO.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_LH_INSERT in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP) as (S_LB & S_N & S_X & S_F).
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SCm) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6). unfold LH_KMAX in G6.
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SCm.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (lh + 96, lh + 100)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OL)) as (LH0 & LH16 & _ & LHC & _). pose proof (cown_al8 _ _ _ _ _ _ _ _ HP OB) as (BAL & _). cprefix. step. carve_frame 80%nat ST. do 8 step. step. step. ubs_if. do 3 step. ubs_if. step.
  rewrite (zx32_small (g_nn g)) by lia. cstep. step. ubs_if. do 3 step.
  step. step. rewrite m_divu by (rewrite unsigned_lit by lia; lia).
  assert (EDIV : Z.land (Z.land (g_items g ≪ 8) 18446744073709551615 / g_nn g) 18446744073709551615 = g_items g * 256 / g_nn g).
  { change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
    rewrite (Z.mod_small (g_items g * 256)) by lia. apply Z.mod_small. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  apply (rw_cells_split_CB usegs _ _ [] 16 _ _ [8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  apply (cb8_c8_in' _ _ [CB 8 _] _ _) in FR. cbn [app] in FR.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG0.
  assert (OUTB : forall i a, 0 <= i < g_na g -> bucket_fp B bks i a -> a < alloc_ceiling /\ ~ (lh <= a < lh + 104)).
  { intros i a Hi [Ha|(q & A & Hq & Ha)]; [lia|].
    assert (LI : (Z.to_nat i < length bks)%nat) by lia. destruct (S_N _ q A LI Hq) as [X1 _]. pose proof (CH i Hi) as (c0 & SS & _).
    pose proof (lseg_ranges _ _ _ _ _ _ _ SS q A Hq). lia. }
  assert (INL : In (pl, lh, 104) LBall) by exact (proj1 OL).
  assert (CSTc : cstate s LBall LB L mc (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m mc _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| eassumption| | lia| lia| | rewrite unsigned_lit by lia; exact ST| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor; [| constructor]]. apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INL) as (_ & _ & _ & _ & X). lia. }
  assert (FRc : cframe (lh_T pl pb bks) [] (bv_unsigned sp) s LBall L m s LBall L mc).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
    apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
    intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. left. reflexivity. }
  assert (REPc : lh_rep DVERR mc LBall L ERR_FNS lh pl pb B nmb g bks).
  { eapply (lh_rep_upd DVERR m mc LBall L LBall L ERR_FNS lh pl pb B nmb g g bks bks (fun _ => False) REP); try reflexivity; try assumption.
    - intros i. right. intros X. exact X.
    - exists x40, x48, (Z_to_bv 64 0), pad. unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz. exact SCm.
    - intros q A n nm _ X. exact X.
    - intros i Hi [].
    - intros i Hi _. split; [reflexivity|]. eapply agree_on_mono; [exact AG0|]. intros a Ha. destruct (OUTB i a Hi Ha) as [X1 X2]. cbn [outside]. lia. }
  step. if_cases K; zify_cond K.
  2:{ (* [comment removed for export] *)
    chere. apply climpl_done. unfold lhi_mid.
    do 21 eexists. exists mc, LBall, pb, B, nmb, g, bks. eexists.
    split; [reflexivity|]. split; [lia|]. split; [exact CSTc|]. split; [exact FRc|]. split; [exact REPc|]. split; [reflexivity|].
    split; [unfold lhi_frame; exact FR|].
    split; [rewrite !Z.sub_diag; apply cgrow_refl|]. split; [lia|]. intros q _ X. exact X. }
  rewrite EDIV in K.
  assert (LOAD : 2 * g_nn g <= g_items g).
  { pose proof (Z.mul_div_le (g_items g * 256) (g_nn g) ltac:(lia)) as X. clear - X K GB. nia. }
  do 3 step. rewrite (zx32_small (g_p g)), (zx32_small (g_na g)) by lia.
  step. step.
  rewrite (Printf_lib.sx32_lit (g_pmax g)) by lia. rewrite (unsigned_lit (g_p g)) by lia. rewrite (Printf_lib.swrap32_small (g_p g + 1)) by lia.
  pose proof (lh_rep_raw _ _ _ _ _ _ _ _ _ _ _ _ REPc) as RAWc.
  pose proof REPc as (_ & _ & _ & _ & _ & _ & _ & CHc & _ & _).
  assert (ENN : nth (Z.to_nat (g_nn g)) bks [] = []) by (apply EMP; lia).
  if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { (* [comment removed for export] *)
    destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP) as (_ & S_N' & _ & _).
    eapply evt_cut.
    { eapply (lhi_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc LBall L lh B (g_nn g) (g_na g) (g_p g) (g_p g + 1) (g_pmax g) (g_pmax g) (g_na g) (g_items g)
               x40 x48 (Z_to_bv 64 0) pad (nth (Z.to_nat (g_p g)) bks []) s m); try lia; try assumption.
      - apply CHc. lia.
      - rewrite <- ENN. apply CHc. lia.
      - eapply bucket_nsep; [exact HP| exact REP| lia| lia| lia].
      - apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([q A] & E & Hq). cbn [snd] in E. subst X.
        assert (LI : (Z.to_nat (g_p g) < length bks)%nat) by lia. exact (proj1 (S_N _ q A LI Hq)). }
    intros ms' (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & m' & stay' & moved' & -> & MI' & WM' & SC' & CS' & CM' & PM' & AG').
    assert (PRc : 0 <= g_p g < g_nn g) by lia. assert (NNAc : g_nn g < g_na g) by lia. assert (HSPc : alloc_ceiling <= bv_unsigned sp) by lia.
    assert (LSPc : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80))) by (rewrite unsigned_lit by lia; lia).
    destruct (split_close (lh_T pl pb bks) _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) _ _ _ _ _ _ _ _ _ _ _ s LBall L m CSTc RAWc PRc NNAc ENN MI' WM' CS' CM' PM' AG' FRc HSPc LSPc)
      as (CST' & FRM' & RAW' & PMC').
    { intros bb Hb TB bb0 _ NT E. apply NT. rewrite E. exact TB. }
    chere. apply climpl_done. unfold lhi_mid.
    set (g1 := mkGeo (g_nn g + 1) (g_na g) (g_p g + 1) (g_pmax g) (g_items g)).
    do 21 eexists. exists m', LBall, pb, B, nmb, g1. eexists. eexists.
    split; [reflexivity|]. split; [lia|]. split; [exact CST'|]. split; [exact FRM'|].
    split. { apply lh_rep_of_raw; [exact RAW'| | |].
      - unfold lh_geo_ok, g1, LH_KMAX. cbn [g_nn g_na g_p g_pmax g_items]. clear - G1 G2 G3 G4 G5 G6 K2 LOAD. lia.
      - exists x40, x48, (Z_to_bv 64 0), pad. unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz, g1. cbn [g_nn g_na g_p g_pmax g_items]. exact SC'.
      - intros i Hi. unfold g1 in Hi. cbn [g_nn g_na] in Hi. rewrite !nth_lupd_ne by lia. apply EMP. lia. }
    split; [reflexivity|].
    split. { unfold lhi_frame. eapply rw_cells_agree; [exact AG'| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha BAD.
      unfold split_W in BAD. destruct BAD as [BAD|[BAD|[BAD|(q & A & Hq & BAD)]]]; try lia.
      pose proof (CH (g_p g) ltac:(lia)) as (c0 & SS & _). pose proof (lseg_ranges _ _ _ _ _ _ _ SS q A Hq). lia. }
    split; [rewrite !Z.sub_diag; apply cgrow_refl|]. split; [unfold g1; cbn [g_na]; lia|].
    intros q _ NT [E|[E|E]]; [apply NT; left; exact E| apply NT; right; left; exact E|].
    apply NT. right; right. eapply Permutation_in; [apply Permutation_map; exact PMC'| exact E]. }
  (* [comment removed for export] *)
  assert (PRc : 0 <= g_p g < g_nn g) by lia. assert (NNA2 : g_nn g < 2 * g_na g) by lia. assert (HSPc : alloc_ceiling <= bv_unsigned sp) by lia.
  assert (LSPc : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80))) by (rewrite unsigned_lit by lia; lia).
  unfold lhi_double_stmt in DBL.
  chere. eapply climpl_seq.
  { eapply (DBL sp gp tp s7 s8 s9 s10 s11) with (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (data := data) (lo := lo) (Bd := Bd);
      [exact Hf| exact ROOM| exact CSTc| lia| exact REPc| exact NMB| unfold LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia]. }
  intros f2 L2 st2 ms2 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & x40' & x48' & err' & pad' & m2 & LBall2 & pb2 & B2 & nmb2
                        & -> & FU2 & CST2 & FRM2 & RAW2 & SC2 & GR2 & NMB2 & FRESH2).
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  set (bks2 := bks ++ repeat [] (Z.to_nat (g_na g))) in *.
  assert (LEN2 : length bks = Z.to_nat (g_na g)) by lia.
  assert (ENN2 : nth (Z.to_nat (g_nn g)) bks2 [] = []) by (unfold bks2; rewrite app_nth1 by lia; exact ENN).
  assert (CC2 : concat bks2 = concat bks) by (unfold bks2; rewrite concat_app, concat_repeat_nil, app_nil_r; reflexivity).
  assert (EMP2 : forall i, g_nn g <= i -> nth (Z.to_nat i) bks2 [] = []).
  { intros i Hi. unfold bks2. destruct (Z_lt_le_dec i (g_na g)) as [X|X]; [rewrite app_nth1 by lia; apply EMP; lia|]. rewrite app_nth2 by lia. apply nth_repeat. }
  destruct (lh_sep_raw _ _ _ _ _ _ _ _ _ _ _ _ HP2 RAW2) as (S_LB2 & S_N2 & _ & _).
  pose proof RAW2 as (OL2 & _ & OB2 & RB2 & LENb2 & CH2 & ND2).
  pose proof (cown_al8 _ _ _ _ _ _ _ _ HP2 OB2) as (B2AL & _). cprefix. eapply evt_cut.
  { eapply (lhi_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 LBall2 L2 lh B2 (g_nn g) (2 * g_na g) (g_p g) 0 (g_pmax g) (g_na g) (g_na g) (g_items g)
             x40' x48' err' pad' (nth (Z.to_nat (g_p g)) bks2 []) st2 m2); try lia; try assumption.
    - apply CH2. lia.
    - rewrite <- ENN2. apply CH2. lia.
    - eapply bucket_nsep_raw; [exact HP2| exact RAW2| lia| lia| lia].
    - apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([q A] & E & Hq). cbn [snd] in E. subst X.
      assert (LI : (Z.to_nat (g_p g) < length bks2)%nat) by lia. exact (proj1 (S_N2 _ q A LI Hq)). }
  intros ms' (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & m' & stay' & moved' & -> & MI' & WM' & SC' & CS' & CM' & PM' & AG').
  assert (FRM02 : cframe (lh_T pl pb bks) [] (bv_unsigned sp) s LBall L m st2 LBall2 L2 m2).
  { eapply cframe_call; [exact FRc| exact FRM2| lia| intros a X; exact X|]. intros q _ NT [E|E]; apply NT; [left; exact E| right; left; exact E]. }
  destruct (split_close (lh_T pl pb bks) _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) _ _ _ _ _ _ _ _ _ _ _ s LBall L m CST2 RAW2 PRc NNA2 ENN2 MI' WM' CS' CM' PM' AG' FRM02 HSPc LSPc)
    as (CST' & FRM' & RAW' & PMC').
  { intros bb Hb TB bb0 Hb0 NT E. destruct TB as [TB|[TB|TB]].
    - apply NT. rewrite E, TB. left. reflexivity.
    - apply (FRESH2 (blk_id bb0)); [left; apply in_map; exact Hb0| | rewrite E; exact TB]. intros X. apply NT. right; left. exact X.
    - apply NT. rewrite E. right; right. rewrite <- CC2. exact TB. }
  chere. apply climpl_done. unfold lhi_mid.
  set (g1 := mkGeo (g_nn g + 1) (2 * g_na g) 0 (g_na g) (g_items g)).
  do 21 eexists. exists m', LBall2, pb2, B2, nmb2, g1. eexists. eexists.
  split; [reflexivity|]. split; [exact FU2|]. split; [exact CST'|]. split; [exact FRM'|].
  split. { apply lh_rep_of_raw; [exact RAW'| | |].
    - unfold lh_geo_ok, g1, LH_KMAX. cbn [g_nn g_na g_p g_pmax g_items]. clear - G1 G2 G3 G4 G5 G6 K2 LOAD. lia.
    - exists x40', x48', err', pad'. unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz, g1. cbn [g_nn g_na g_p g_pmax g_items]. exact SC'.
    - intros i Hi. unfold g1 in Hi. cbn [g_nn g_na] in Hi. rewrite !nth_lupd_ne by lia. apply EMP2. lia. }
  split; [reflexivity|].
  split. { unfold lhi_frame. eapply rw_cells_agree; [exact AG'| exact (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM2) FR ltac:(lia))|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha BAD.
    unfold split_W in BAD. destruct BAD as [BAD|[BAD|[BAD|(q & A & Hq & BAD)]]]; try lia.
    pose proof (CH2 (g_p g) ltac:(lia)) as (c0 & SS & _). pose proof (lseg_ranges _ _ _ _ _ _ _ SS q A Hq). lia. }
  split; [exact GR2|]. split; [unfold g1; cbn [g_na]; lia|].
  intros q QIN NT [E|[E|E]]; [apply NT; left; exact E| |].
  - apply (FRESH2 q QIN); [| exact E]. intros X. apply NT. right; left. exact X.
  - apply NT. right; right. rewrite <- CC2. eapply Permutation_in; [apply Permutation_map; exact PMC'| exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition lh_insert_res (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z)))
    : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pb' B' nmb' g' bks',
    lh_rep DVERR m' LBall' L' ERR_FNS lh pl pb' B' nmb' g' bks'
    /\ g_items g <= g_items g' <= g_items g + 1
    /\ nmb <= nmb' <= 8 * g_na g'
    /\ cgrow L L' (1 + (wA nmb' - wA nmb)) (wB nmb' - wB nmb) (wBig nmb' - wBig nmb)
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ lh_T pl pb bks q -> ~ lh_T pl pb' bks' q).

Definition lh_insert_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data lo Bd : Z),
  (3 <= f)%nat -> croom L 1 1 (LHA_MAX + 8192) ->
  cstate s LBall LB L m sp tp lo Bd ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> 0 <= nmb <= 8 * g_na g -> g_items g < LH_KMAX -> DVERR data ->
  lo <= bv_unsigned sp - LHI_STACK -> bv_unsigned sp mod 16 = 0 -> a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 data ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_LH_INSERT) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (lh_T pl pb bks) [] 3 1 1 (LHA_MAX + 8192)
           (lh_insert_res LBall L lh pl pb nmb g bks)).

Theorem lh_insert_of : lhi_double_stmt -> crypto_malloc_stmt -> lh_insert_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros DBL CM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lh pl pb B nmb g bks data lo Bd
         Hf ROOM CST REP NMB ITEMS DVD SLO SA -> ->.
  destruct (cstate_B _ _ _ _ _ _ _ _ _ CST) as (SPB & _ & _).
  eapply climpl_seq.
  { eapply (lhi_head DBL) with (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (data := data) (lo := lo) (Bd := Bd);
      [lia| exact ROOM| exact CST| exact REP| lia| exact SLO]. }
  intros f1 L1 st1 ms1 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & hs & m1 & LBall1 & pb1 & B1 & nmb1
                        & g1 & bks1 & j0 & -> & FU1 & CST1 & FRM1 & REP1 & IT1 & FR1 & GR1 & NMB1 & TK1).
  pose proof (lh_geo_bounds g1 (proj1 REP1)) as GB1.
  destruct (w_delta nmb nmb1 ltac:(lia)) as (WD1 & WD2 & WD3 & WD4).
  pose proof (w_nonneg nmb) as (_ & _ & WN3).
  assert (ROOM1 : croom L1 1 0 0).
  { unfold croom, cgrow, LHA_MAX in *. clear - ROOM GR1 WD1 WD2 WD3 GB1 NMB1. lia. }
  eapply climpl_mono.
  { eapply (lhi_tail CM) with (lh := lh) (pl := pl) (pb := pb1) (B := B1) (nmb := nmb1) (g := g1) (bks := bks1) (data := data) (lo := lo) (Bd := Bd) (j0 := j0) (hs := hs);
      [lia| exact ROOM1| exact CST1| exact SPB| exact REP1| lia| exact DVD| exact FR1| exact SLO| exact SA]. }
  intros f' L' s' ms' (v & m' & LBall' & g' & bks' & RET & FU' & GR' & CST' & FRM' & TK' & REP' & E1 & E2 & E3 & E4 & IT').
  exists v, m', LBall'.
  pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR') as GRT.
  split; [exact RET|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact GRT| | |]; unfold LHA_MAX; clear - WD1 WD2 WD3 GB1 NMB1 WN3; lia. }
  split; [exact CST'|].
  split. { eapply cframe_call; [exact FRM1| exact FRM'| lia| intros a X; exact X| exact TK1]. }
  exists pb1, B1, nmb1, g', bks'.
  split; [exact REP'|]. split; [lia|]. split; [rewrite E2; lia|].
  split. { eapply cgrow_weaken; [exact GRT| | |]; lia. }
  intros q QIN NT. apply TK'; [| exact (TK1 q QIN NT)].
  destruct FRM1 as (_ & [KP1 KP2] & _).
  destruct QIN as [X|X].
  - left. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (KP1 b Hb NT).
  - right. apply in_map_iff in X. destruct X as ([q0 nm0] & <- & Hq). cbn [fst] in NT |- *. apply in_map_iff. exists (q0, nm0). split; [reflexivity| exact (KP2 q0 nm0 Hq NT)].
Qed.
End WithCeiling0.
