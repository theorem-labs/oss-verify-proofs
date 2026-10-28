(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_rep Fz_I1_insert1 Fz_I1_load Fz_I1_errload Fz_I1_efirst Fz_I1_crypto.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_sa Fz_T_master Fz_T_slx Fz_I3_base Fz_I3_kit Fz_I3_shelve.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

(* [comment removed for export] *)
Lemma lh_rep_seg : forall s DV m m' LBall L f lh pl pb B nmb g bks W,
  RHEAP s LBall m -> lh_rep DV m LBall L f lh pl pb B nmb g bks -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv => (forall a, fst iv <= a < snd iv -> 0 < a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x353000 <= a) -> False)
                    \/ (exists b, In b LBall /\ ~ lh_T pl pb bks (blk_id b) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
  lh_rep DV m' LBall L f lh pl pb B nmb g bks.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s DV m m' LBall L f lh pl pb B nmb g bks W HP REP MU WM HW.
  pose proof (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP) as OWN.
  eapply lh_rep_agree; [exact REP| | intros q A n nm _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|].
  pose proof REP as (G & OL & _ & _ & OB & _).
  assert (BLK : forall (q : bptr) A n, In (q, A, n) LBall -> lh_T pl pb bks q -> forall a, A <= a < A + n -> outside W a).
  { intros q A n IQ TQ a Ha. pose proof (RHEAP_block_range_proof _ _ _ (q, A, n) HP IQ) as (C0 & _ & _ & C & CI). unfold blk_addr, blk_size in C0, C, CI. cbn [fst snd] in C0, C, CI.
    clear MU. induction HW as [|[x y] W0 H HW IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in H. intros Hin.
    destruct H as [H|(b & Hb & NT & H1 & H2)].
    - apply (H a Hin); clear - Ha C0 C CI; lia.
    - assert (NE : blk_id (q, A, n) <> blk_id b) by (intros E; apply NT; rewrite <- E; exact TQ).
      pose proof (RHEAP_blocks_disjoint_proof _ _ _ (q, A, n) b HP IQ Hb NE) as D. unfold blk_addr, blk_size in D, H1, H2. cbn [fst snd] in D, H1, H2. lia. }
  intros a [Ha|[Ha|(p & A & Hp & Ha)]].
  - eapply (BLK pl lh 104); [exact (proj1 OL)| left; reflexivity| exact Ha].
  - eapply (BLK pb B (8 * g_na g)); [exact (proj1 OB)| right; left; reflexivity| exact Ha].
  - eapply (BLK p A 24); [exact (proj1 (OWN p A Hp))| right; right; apply in_map_iff; exists (p, A); split; [reflexivity| exact Hp]| exact Ha].
Qed.

Definition FZ_INIT_LOADSTR : Z := 0xe219c.
Definition ILS_STACK : Z := 32 + CRS_STACK.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ILS_W : list (Z * Z) := (IC_S + 44, IC_S + 48) :: (0x32e010, 0x32e030) :: SHV_W.

Definition loadstr_res (oldcb w sh : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun _ LBall' L' m' => exists (pm psa pn : bptr) (MK SA P : Z) (u' : byte) (pad top ne : word) (pk pl pb : bptr) (LK lh B : Z),
       els_res ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: (pn, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall)
               ((pb, 128) :: (pl, 104) :: (pk, 40) :: (pn, 128) :: (psa, 32) :: (pm, 72) :: L) lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) NCRYPTO pk LK
               (Z_to_bv 64 1) LBall' L' m'
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pk /\ q <> pl /\ q <> pb /\ q <> pn /\ q <> psa /\ q <> pm)
    /\ In (pm, MK, 72) LBall' /\ In (psa, SA, 32) LBall' /\ In (pn, P, 128) LBall'
    /\ rblock_range MK 72 /\ rblock_range SA 32 /\ rblock_range P 128
    /\ rw_cells usegs m' 0x32dea0 [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' 0x32dea4 [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' 0x32dea8 [C4 (Z_to_bv 64 2)]
    /\ rw_cells usegs m' (RATP + -96) [C8 oldcb] /\ rw_cells usegs m' (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] /\ rw_cells usegs m' (RATP + -150) [C1 u']
    /\ rw_cells usegs m' 0x351c90 [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' 0x351c98 [C4 z64; C4 z64; C4 sh]
    /\ rw_cells usegs m' (0x351890 + 8 * 1) [C8 w] /\ rw_cells usegs m' (0x351890 + 8 * 2) [C8 (Z_to_bv 64 0xe3f98)]
    /\ rw_cells usegs m' (0x351cd0 + 8 * 2) [C8 (Z_to_bv 64 MK)]
    /\ rw_cells usegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
    /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P))
    /\ rw_cells usegs m' P [C8 z64; CB 120 (zeros 120)]
    /\ rw_cells usegs m' ERR_ONCE_CELL (err_statics LK lh)
    /\ rw_cells usegs m' (IC_S + 44) [C4 (Z_to_bv 64 1)]
    (* [comment removed for export] *)
    /\ bv_unsigned ne <= 1.

Definition init_load_strings_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z) (od r0 l0 h0 oldcb tsd w sh kold r44 : word) (ib u : byte),
  (6 + 3 * NCRYPTO <= f)%nat -> croom L (6 + Z.of_nat NCRYPTO) 2 (2 * (LHA_MAX + 8192)) ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - ILS_STACK -> bv_unsigned sp mod 16 = 0 ->
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] ->
  rw_cells usegs m (IC_S + 44) [C4 r44] -> rw_cells usegs m (IC_S + 96) [C8 od] ->
  rw_cells usegs m ERR_ONCE_CELL [C4 z64; C4 r0; C8 l0; C8 h0] ->
  rw_cells usegs m 0x32dea0 [C1 ib] -> rw_cells usegs m 0x32dea4 [C4 z64] -> rw_cells usegs m 0x32dea8 [C4 kold] ->
  rw_cells usegs m (RATP + -96) [C8 oldcb] -> rw_cells usegs m (RATP + -88) [C8 tsd] -> (tsd = z64 \/ tsd = Z_to_bv 64 0x351cd0) -> rw_cells usegs m (RATP + -150) [C1 u] ->
  rw_cells usegs m 0x351c90 [C4 (Z_to_bv 64 1)] -> rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh] ->
  rw_cells usegs m (0x351890 + 8 * 1) [C8 w] -> bv_unsigned w <> 0 -> rw_cells usegs m (0x351890 + 8 * 2) [C8 z64] -> rw_cells usegs m (0x351cd0 + 8 * 2) [C8 z64] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_INIT_LOADSTR) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun _ => False) ILS_W (6 + 3 * NCRYPTO) (6 + Z.of_nat NCRYPTO) 1 (LHA_MAX + 8192)
           (loadstr_res oldcb w sh LBall L)).

Theorem init_load_strings_spec : err_shelve_first_stmt -> err_load_crypto_stmt -> init_load_strings_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros SHV CRY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd od r0 l0 h0 oldcb tsd w sh kold r44 ib u
         Hf ROOM CST SLO SP16 STOP ONCE R44 OD HC IC OC KC CBC TC TV USED NK KL K1 WNZ K2 SLOT2.
  unfold err_shelve_first_stmt in SHV. unfold err_load_crypto_stmt in CRY.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  subst tp.
  unfold ILS_STACK, CRS_STACK, ELF_STACK, GLOBALS_TOP, FZ_INIT_LOADSTR, ERR_ONCE_CELL, RATP, IC_S in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  change (3333664 + 8) with 3333672 in STOP. change (3333664 + 32) with 0x32de40 in ONCE. change (3333664 + 44) with 3333708 in R44. change (3333664 + 96) with 3333760 in OD.
  destruct ROOM as (RA & RB & RC). unfold NCRYPTO in *. change (Z.of_nat 4318) with 4318 in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 3 step. step. step. step.
  apply (cb8_c8_in' _ _ [] _ _) in FR. cbn [app] in FR.
  lazymatch type of FR with rw_cells _ _ _ (C8 ?o :: ?rest) => set (old := o) in FR; clearbody old; change (C8 old :: rest) with ([C8 old] ++ rest) in FR end.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [RES FR]. cbn [cells_size csize Nat.add] in FR. change (Z.of_nat 8) with 8 in FR.
  replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FR by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe (fun _ : bptr => False) ILS_W (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  chere. eapply climpl_seq.
  { eapply SHV with (lo := lo) (Bd := Bd) (res := bv_unsigned sp + -32);
      [lia| unfold croom, LHA_MAX in *; lia| exact CSTa| rewrite unsigned_lit by lia; unfold SHV_STACK; lia| reflexivity| rewrite unsigned_lit by lia; lia| lia| lia| exact RES
      | exact STOP| exact ONCE| exact OD| exact IC| exact OC| exact KC| exact CBC| exact TC| exact TV| exact USED| exact NK| exact KL| exact K1| exact WNZ| exact K2| exact SLOT2]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & SRES).
  destruct SRES as (pm & psa & pn & MK & SA & P & u' & ne & vneg & -> & -> & -> & RNGM & RNGS & RNGP & RES1 & IC1 & OC1 & KC1 & CB1 & TSD1 & USED1 & NK1 & KL1 & K11 & K21 & SLOT1 & BLKM1 & HDR1 & PBLK1 & NE1 & VN0).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. unfold RATP in CB1, TSD1, USED1.
  pose proof FRM1 as (CFR1 & KP1 & _). unfold SHV_W, RATP in CFR1.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  cst_static CFR1 STOP STOP1. cst_static CFR1 ONCE ONCE1. cst_static CFR1 R44 R441. cst_static CFR1 OD OD1. cst_static CFR1 HC HC1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 NDL1].
  (* [comment removed for export] *)
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. th_if_lit. step. chere.
  assert (FRM0 : cframe (fun _ : bptr => False) ILS_W (bv_unsigned sp) s LBall L m st1 ((pn, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall) ((pn, 128) :: (psa, 32) :: (pm, 72) :: L) m1).
  { eapply cframe_call; [exact FRa| exact FRM1| lia| | intros q _ X; exact X]. intros a X. unfold ILS_W. cbn [rin_ivs]. right; right. exact X. }
  clear FRa CSTa CFR1.
  eapply climpl_seq.
  { eapply CRY with (lo := lo) (Bd := Bd) (od := od) (r0 := r0) (l0 := l0) (h0 := h0) (oldcb := oldcb);
      [clear - Hf FU1; lia| unfold croom, cgrow in *; lia| exact CST1| exact STOP1| exact ONCE1| exact OD1| exact HC1| exact CB1| rewrite unsigned_lit by lia; lia ..]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pk & pl & pb & LK & lh & B & ELS & FRESH & NEKL & NEKB & GRE & HCE & CBE)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia). unfold ELF_W, RATP in FRM2. unfold RATP in CBE.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 RES1 ltac:(lia)) as RES2.
  cst_static CFR2 R441 R442. cst_static CFR2 IC1 IC2. cst_static CFR2 OC1 OC2. cst_static CFR2 KC1 KC2. cst_static CFR2 TSD1 TSD2. cst_static CFR2 USED1 USED2.
  cst_static CFR2 NK1 NK2. cst_static CFR2 KL1 KL2. cst_static CFR2 K11 K12. cst_static CFR2 K21 K22. cst_static CFR2 SLOT1 SLOT3.
  assert (INM1 : In (pm, MK, 72) ((pn, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall)) by (right; right; left; reflexivity).
  assert (INS1 : In (psa, SA, 32) ((pn, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall)) by (right; left; reflexivity).
  assert (INP1 : In (pn, P, 128) ((pn, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall)) by (left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pm, MK, 72) CFR2 BLKM1 INM1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add length repeat]; lia)) as BLKM2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (psa, SA, 32) CFR2 HDR1 INS1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size, sa_hdr; cbn [fst snd cells_size csize Nat.add]; lia)) as HDR2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pn, P, 128) CFR2 PBLK1 INP1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add length repeat]; lia)) as PBLK2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 NDL2].
  destruct ELS as [-> ELS']. destruct ELS' as (pb' & B' & nmb' & g' & bks' & REP & IT & NM & GRL & TK & MC & INK2). unfold NCRYPTO in IT, GRL.
  assert (INM2 : In (pm, MK, 72) LBall2) by exact (proj1 KP2 _ INM1 (fun X => X)).
  assert (INS2 : In (psa, SA, 32) LBall2) by exact (proj1 KP2 _ INS1 (fun X => X)).
  assert (INP2 : In (pn, P, 128) LBall2) by exact (proj1 KP2 _ INP1 (fun X => X)).
  cbn [map blk_id fst] in ND1. inversion ND1 as [|hd tl NIn ND1']; subst. inversion ND1' as [|hd tl NIs ND1'']; subst. inversion ND1'' as [|hd tl NIm _]; subst.
  cbn [map fst] in NDL1. inversion NDL1 as [|hd tl NInL NDL1']; subst. inversion NDL1' as [|hd tl NIsL NDL1'']; subst. inversion NDL1'' as [|hd tl NImL _]; subst.
  assert (NEsn : psa <> pn) by (intros E; apply NIn; left; exact E).
  assert (NEmn : pm <> pn) by (intros E; apply NIn; right; left; exact E).
  assert (NEms : pm <> psa) by (intros E; apply NIs; left; exact E).
  pose proof (FRESH pm ltac:(left; cbn [map blk_id fst]; right; right; left; reflexivity)) as (NEmk & NEml & NEmb).
  pose proof (FRESH psa ltac:(left; cbn [map blk_id fst]; right; left; reflexivity)) as (NEsk & NEsl & NEsb).
  pose proof (FRESH pn ltac:(left; cbn [map blk_id fst]; left; reflexivity)) as (NEnk & NEnl & NEnb).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INS2 INP2 NEsn) as APSP.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INM2 INS2 NEms) as APMS.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INM2 INP2 NEmn) as APMP.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INK2 INS2 (fun E => NEsk (eq_sym E))) as APKS.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INK2 INP2 (fun E => NEnk (eq_sym E))) as APKP.
  pose proof RNGM as (M0 & _ & _ & M72 & MIMG). pose proof RNGS as (S0 & _ & _ & S32 & SIMG). pose proof RNGP as (P0 & _ & _ & P128 & PIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST2 INK2) as (LK0 & _ & _ & LK40 & LKIMG).
  unfold mutex_cells in MC. unfold ERR_ONCE_CELL, err_statics in HCE.
  assert (OCr : ro_cells usegs m2 3333796 [C4 (Z_to_bv 64 2)]) by exact (proj1 OC2).
  assert (KCr : ro_cells usegs m2 0x32dea8 [C4 (Z_to_bv 64 2)]) by exact (proj1 KC2).
  assert (TSDr : ro_cells usegs m2 (3344744 + -88) [C8 (Z_to_bv 64 3480784)]) by exact (proj1 TSD2).
  assert (SLOTr : ro_cells usegs m2 (3480784 + 8 * 2) [C8 (Z_to_bv 64 MK)]) by exact (proj1 SLOT3).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp - 32); (SA + 8, SA + 24); (P, P + 8); (3333708, 3333712)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. step. step. step. step.
  calle (eapply err_unshelve_proof with (lo := lo) (MK := MK) (SA := SA) (P := P)).
  1: lia.
  lazymatch goal with H : ?x = Z_to_bv 64 (bv_unsigned ne + sa_delta (Z_to_bv 64 0) vneg) |- _ =>
    assert (NEF : bv_unsigned x <= 1)
      by (rewrite H, NE1; unfold sa_delta; replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity); rewrite VN0; cbv iota;
          rewrite unsigned_lit by (clear; lia); clear; lia) end.
  unfold sa_hdr in *.
  step. step. cstep. do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk _ mf lo _ |- _ => rename H into ST3 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -32) _ |- _ => rename H into RES3 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -24) _ |- _ => rename H into FR3 end.
  release_frame RES3 ST3 (bv_unsigned sp + -24). release_frame FR3 ST3 (bv_unsigned sp).
  step. step.
  lazymatch goal with H : stk _ mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv _ mf |- _ => rename H into MIf end.
  lazymatch goal with H : rw_cells usegs mf LK _ |- _ => rename H into MCf end.
  lazymatch goal with H : rw_cells usegs mf SA _ |- _ => rename H into HDRf end.
  lazymatch goal with H : rw_cells usegs mf P _ |- _ => rename H into PBLKf end.
  lazymatch goal with H : rw_cells usegs mf MK _ |- _ => rename H into BLKMf end.
  chere. apply climpl_done.
  eexists. exists mf, LBall2.
  split; [unfold cret; do 14 eexists; reflexivity|].
  split; [clear - Hf FU1 FU2; lia|].
  split; [pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) as GR; clear - GR; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m2 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - constructor; [apply cwin_stack; lia|].
      constructor; [apply (cwin_block _ _ _ (psa, SA, 32)); [exact INS2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      constructor; [apply (cwin_block _ _ _ (pn, P, 128)); [exact INP2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      constructor; [apply cwin_bss; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRM0| exact FRM2| lia| | intros q _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    - intros a X. unfold ILS_W, SHV_W, IC_S, RATP. cbn [rin_ivs fst snd] in X |- *. lia.
    - constructor; [apply cseg_ok_stack; lia|].
      constructor. { apply (cseg_ok_block _ _ _ _ _ (psa, SA, 32)); [exact INS2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
                     intros b0 Hb0 _ E. apply NIs. right. change psa with (blk_id (psa, SA, 32)). rewrite <- E. apply in_map. exact Hb0. }
      constructor. { apply (cseg_ok_block _ _ _ _ _ (pn, P, 128)); [exact INP2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
                     intros b0 Hb0 _ E. apply NIn. right; right. change pn with (blk_id (pn, P, 128)). rewrite <- E. apply in_map. exact Hb0. }
      constructor; [| constructor]. apply cseg_ok_static; [lia| lia| intros a Ha; unfold ILS_W, IC_S; cbn [rin_ivs fst snd]; lia]. }
  unfold loadstr_res. exists pm, psa, pn, MK, SA, P, u'. do 3 eexists. exists pk, pl, pb, LK, lh, B.
  split. { split; [reflexivity|]. exists pb', B', nmb', g', bks'.
    split. { eapply (lh_rep_seg st2 DVERR m2 mf); [exact HP2| exact REP| exact MU2| exact WM2|].
      constructor; [left; cbn [fst snd]; intros a Ha Hc Hi; lia|].
      constructor. { right. exists (psa, SA, 32). split; [exact INS2|]. split; [| unfold blk_addr, blk_size; cbn [fst snd]; lia].
                     unfold blk_id; cbn [fst snd]. apply TK; [left; cbn [map blk_id fst]; do 4 right; left; reflexivity|].
                     unfold lh_T. cbn [repeat concat app map]. intros [E|[E|[]]]; [exact (NEsl E)| exact (NEsb E)]. }
      constructor. { right. exists (pn, P, 128). split; [exact INP2|]. split; [| unfold blk_addr, blk_size; cbn [fst snd]; lia].
                     unfold blk_id; cbn [fst snd]. apply TK; [left; cbn [map blk_id fst]; do 3 right; left; reflexivity|].
                     unfold lh_T. cbn [repeat concat app map]. intros [E|[E|[]]]; [exact (NEnl E)| exact (NEnb E)]. }
      constructor; [left; cbn [fst snd]; intros a Ha Hc Hi; lia| constructor]. }
    split; [exact IT|]. split; [exact NM|]. split; [exact GRL|]. split; [exact TK|]. split; [unfold mutex_cells; exact MCf| exact INK2]. }
  split. { intros q Hq. assert (Hq1 : In q (map blk_id ((pn, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall)) \/ In q (map fst ((pn, 128) :: (psa, 32) :: (pm, 72) :: L)))
             by (destruct Hq as [Hq|Hq]; [left| right]; cbn [map blk_id fst]; do 3 right; exact Hq).
           destruct (FRESH q Hq1) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. split; [exact N3|].
           destruct Hq as [Hq|Hq].
           - split; [intros ->; apply NIn; right; right; exact Hq|]. split; [intros ->; apply NIs; right; exact Hq| intros ->; exact (NIm Hq)].
           - split; [intros ->; apply NInL; right; right; exact Hq|]. split; [intros ->; apply NIsL; right; exact Hq| intros ->; exact (NImL Hq)]. }
  split; [exact INM2|]. split; [exact INS2|]. split; [exact INP2|]. split; [exact RNGM|]. split; [exact RNGS|]. split; [exact RNGP|].
  unfold RATP, IC_S, ERR_ONCE_CELL, err_statics. change (3333664 + 44) with 3333708.
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
End WithCeiling0.
