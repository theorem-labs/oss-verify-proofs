(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_calloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_errno. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_once Fz_T_local Fz_T_sa Fz_T_master Fz_T_master1 Fz_T_sa_new Fz_T_sa_set Fz_T_lock_new Fz_T_slx Fz_T_atomic Fz_I3_base Fz_I3_kit.
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

Definition FZ_ERR_SHELVE : Z := 0xe89a4.
Definition FZ_ERR_UNSHELVE : Z := 0xe8a54.
Definition SHV_STACK : Z := 48 + 8368.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHV_W : list (Z * Z) := [(0x32dea0, 0x32deac); (0x351c90, 0x351c9c); (0x3518a0, 0x3518a8); (RATP + -96, RATP + -80); (0x351ce0, 0x351ce8); (RATP + -150, RATP + -149)].

Definition shelve_res (res : Z) (oldcb w sh : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pm psa pl : bptr) (MK SA P : Z) (u' : byte) (ne vneg : word),
       v = Z_to_bv 64 1
    /\ LBall' = (pl, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall /\ L' = (pl, 128) :: (psa, 32) :: (pm, 72) :: L
    /\ rblock_range MK 72 /\ rblock_range SA 32 /\ rblock_range P 128
    /\ rw_cells usegs m' res [C8 z64]
    /\ rw_cells usegs m' 0x32dea0 [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' 0x32dea4 [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' 0x32dea8 [C4 (Z_to_bv 64 2)]
    /\ rw_cells usegs m' (RATP + -96) [C8 oldcb] /\ rw_cells usegs m' (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] /\ rw_cells usegs m' (RATP + -150) [C1 u']
    /\ rw_cells usegs m' 0x351c90 [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' 0x351c98 [C4 z64; C4 z64; C4 sh]
    /\ rw_cells usegs m' (0x351890 + 8 * 1) [C8 w] /\ rw_cells usegs m' (0x351890 + 8 * 2) [C8 (Z_to_bv 64 0xe3f98)]
    /\ rw_cells usegs m' (0x351cd0 + 8 * 2) [C8 (Z_to_bv 64 MK)]
    /\ rw_cells usegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
    /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 ne (Z_to_bv 64 P))
    /\ rw_cells usegs m' P [C8 vneg; CB 120 (zeros 120)]
    (* [comment removed for export] *)
    /\ bv_unsigned ne = 1 /\ bv_eqb vneg z64 = false.

Definition err_shelve_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd res : Z) (od old oldcb tsd w sh kold : word) (ib : byte) (u : byte),
  (3 <= f)%nat -> croom L 3 0 0 ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - SHV_STACK ->
  a0 = Z_to_bv 64 res -> bv_unsigned sp <= res -> res + 8 <= Bd -> res mod 8 = 0 -> rw_cells usegs m res [C8 old] ->
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells usegs m (IC_S + 96) [C8 od] ->
  rw_cells usegs m 0x32dea0 [C1 ib] -> rw_cells usegs m 0x32dea4 [C4 z64] -> rw_cells usegs m 0x32dea8 [C4 kold] ->
  rw_cells usegs m (RATP + -96) [C8 oldcb] -> rw_cells usegs m (RATP + -88) [C8 tsd] -> (tsd = z64 \/ tsd = Z_to_bv 64 0x351cd0) -> rw_cells usegs m (RATP + -150) [C1 u] ->
  rw_cells usegs m 0x351c90 [C4 (Z_to_bv 64 1)] -> rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh] ->
  rw_cells usegs m (0x351890 + 8 * 1) [C8 w] -> bv_unsigned w <> 0 -> rw_cells usegs m (0x351890 + 8 * 2) [C8 z64] -> rw_cells usegs m (0x351cd0 + 8 * 2) [C8 z64] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_ERR_SHELVE) fc None m (seg_rom usegs))
    (fun f' L' s' ms' => exists v m' LBall',
       cret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v m' ms'
       /\ (f - 3 <= f')%nat /\ cgrow L L' 3 0 0
       /\ cstate s' LBall' LB L' m' sp tp lo Bd
       /\ cframe (fun _ => False) SHV_W (res + 8) s LBall L m s' LBall' L' m'
       /\ shelve_res res oldcb w sh LBall L v LBall' L' m').

Theorem err_shelve_first_spec : T_set_local_ex_first_stmt -> err_shelve_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros SLX ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd res od old oldcb tsd w sh kold ib u
         Hf ROOM CST SLO -> RLO RHI RAL RES STOP ONCE OD IC OC KC CBC TC TV USED NK KL K1 WNZ K2 SLOT2.
  unfold T_set_local_ex_first_stmt in SLX.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  subst tp.
  unfold SHV_STACK, GLOBALS_TOP, FZ_ERR_SHELVE, RATP, IC_S in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  change (3333664 + 8) with 3333672 in STOP. change (3333664 + 32) with 0x32de40 in ONCE. change (3333664 + 96) with 3333760 in OD.
  assert (ETP : errno_addr (Z_to_bv 64 3344744) = 3344580) by (unfold errno_addr; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR.
  destruct ROOM as (RA & RB & RC).
  destruct (rheap_ssp _ _ _ HP) as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
  pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp); (res, res + 8); (3344580, 3344580 + 4); (0x32dea0, 0x32dea0 + 12); (0x351c90, 0x351c90 + 12);
                           (0x351890 + 8 * 2, 0x351890 + 8 * 2 + 8); (3344744 + -96, 3344744 + -80)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 48%nat ST. do 5 step. step. step. step.
  eapply evt_cut; [eapply errno_location_proof; rewrite unsigned_lit by lia; lia|]. intros ms' ->. cbv beta delta [mkR]. try th_ret_lit. try cret_lit.
  rewrite (unsigned_lit 3344744) by lia. change (3344744 + -164) with 3344580.
  step. th_if_lit. step. step. step. th_if_lit. step. do 2 step. step.
  calle (eapply init_crypto_base_spec with (lo := lo) (od := od)); try (unfold IC_BASE_STACK; lia).
  step. th_if_lit.
  (* [comment removed for export] *)
  do 2 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  destruct (rheap_ssp _ _ _ HP) as [GOTx GUx]. clear GOTx GUx.
  lazymatch goal with H : rw_cells usegs ma 0x31c468 _ |- _ => rename H into GOTa end.
  lazymatch goal with H : rw_cells usegs ma 3475880 _ |- _ => rename H into GUa end.
  assert (PROBE : ro_cells usegs ma (0x351890 + 8 * 1) [C8 w]) by (lazymatch goal with H : rw_cells usegs ma (3479696 + 8 * 1) _ |- _ => exact (proj1 H) end).
  assert (SLOTr : ro_cells usegs ma (0x351cd0 + 8 * 2) [C8 (Z_to_bv 64 0)]) by (lazymatch goal with H : rw_cells usegs ma (3480784 + 8 * 2) _ |- _ => exact (proj1 H) end).
  pose proof T_get_local_ex_first_proof as GLX. unfold T_get_local_ex_first_stmt, ssp_cells, got_ssp, ssp_guard in GLX.
  tcall (GLX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3 1 2 sh kold w tsd oldcb rr_guard ib).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear GLX PROBE SLOTr. cbv beta delta [mkR].
  pose proof (ro_cells_bound _ _ _ _ (proj1 RES)) as RESB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in RESB.
  (* [comment removed for export] *)
  step. ubs_if. step. step. ubs_if. cstep. do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mc end.
  lazymatch goal with H : stk _ mc _ _ |- _ => rename H into STc end.
  lazymatch goal with H : mem_inv _ mc |- _ => rename H into MIc end.
  lazymatch goal with H : rw_cells usegs mc 3344580 _ |- _ => rename H into ERRc end.
  lazymatch goal with H : rw_cells usegs mc res _ |- _ => rename H into RESc end.
  lazymatch goal with H : rw_cells usegs mc 3333796 _ |- _ => rename H into ONCEc end.
  lazymatch goal with H : rw_cells usegs mc 0x32dea8 _ |- _ => rename H into KEYc end.
  lazymatch goal with H : rw_cells usegs mc (3344744 + -88) _ |- _ => rename H into TSDc end.
  lazymatch goal with H : rw_cells usegs mc (3480784 + 8 * 2) _ |- _ => rename H into SLOTc end.
  lazymatch goal with H : rw_cells usegs mc (3344744 + -150) _ |- _ => rename H into USEDc end.
  assert (CSTc : cstate s LBall LB L mc (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg_e _ s LBall LB L m mc sp _ _ lo Bd (res + 8));
      [exact CST| exact MU| exact WM| exact MIc| | lia| lia| | unfold errno_addr; rewrite unsigned_lit by lia; exact ERRc
      | rewrite unsigned_lit by lia; exact STc| rewrite unsigned_lit by lia; lia].
    - repeat apply Forall_cons; try apply Forall_nil;
        first [left; apply cwin_stack; lia | left; unfold cwin; cbn [fst snd]; lia | right; split]. all: rewrite unsigned_lit by lia; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe (fun _ => False) SHV_W (res + 8) s LBall L m s LBall L mc).
  { eapply cframe_seg_e; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    unfold SHV_W, RATP. repeat apply Forall_cons; try apply Forall_nil;
      first [left; apply cseg_ok_stack; lia | right; unfold RMallocRep.RERRNO; cbn [fst snd]; lia
            | left; apply cseg_ok_static; [lia| lia| intros a Ha; cbn [rin_ivs fst snd]; lia]]. }
  destruct (wA_small 72 ltac:(unfold TIER_A_MAX; lia)) as (WA72 & WB72 & WC72).
  destruct (wA_small 32 ltac:(unfold TIER_A_MAX; lia)) as (WA32 & WB32 & WC32).
  destruct (wA_small 128 ltac:(unfold TIER_A_MAX; lia)) as (WA128 & WB128 & WC128).
  eapply climpl_seq.
  { eapply SLX with (lo := lo) (B := Bd) (T := 3480784) (k := 2);
      [lia| unfold croom; rewrite WA72, WB72, WC72, WA32, WB32, WC32, WA128, WB128, WC128; lia| exact CSTc
      | rewrite unsigned_lit by lia; unfold SLX_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity
      | exact ONCEc| exact KEYc| lia| rewrite unsigned_lit by lia; exact TSDc| exact SLOTc| lia| lia| lia| rewrite unsigned_lit by lia; exact USEDc]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pm & MK & psa & SA & pl & P & u' & -> & -> & -> & RNGM & RNGS & RNGP & SLOT1 & USED1 & BLKM & HDR & PBLK)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). repeat (rewrite unsigned_lit in USED1 by lia).
  rewrite WA72, WB72, WC72, WA32, WB32, WC32, WA128, WB128, WC128 in GR1. cbn [Z.add] in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 RESc ltac:(lia)) as RES1.
  cst_static CFR1 ONCEc ONCE1. cst_static CFR1 PC2 INIT1. cst_static CFR1 KEYc KEY1. cst_static CFR1 PC4 CB1. cst_static CFR1 TSDc TSD1.
  cst_static CFR1 PC6 NK1. cst_static CFR1 PC7 KL1. cst_static CFR1 K1 K11. cst_static CFR1 POST0 K21.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & ERR1 & MI1 & _) & _).
  rewrite ETP in ERR1. rewrite unsigned_lit in ST1 by lia.
  pose proof (munch_refl [(3344580, 3344580 + 4)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  pose proof (conj BLKM (conj HDR PBLK)) as BLK1. clear BLKM HDR PBLK.     (* [comment removed for export] *)
  (* [comment removed for export] *)
  cprefix. step. th_if_lit. cstep. step. step. do 5 step.
  lazymatch goal with H : stk _ _ lo _ |- _ => rename H into STe end.
  release_frame FR1 STe (bv_unsigned sp). step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk _ mf _ _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv _ mf |- _ => rename H into MIf end.
  lazymatch goal with H : rw_cells usegs mf 3344580 _ |- _ => rename H into ERRf end.
  chere. apply climpl_done.
  exists (Z_to_bv 64 1), mf, ((pl, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact GR1|].
  split. { eapply (cstate_seg_e _ _ _ _ _ m1 mf _ sp _ lo Bd (bv_unsigned sp));
      [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | unfold errno_addr; rewrite unsigned_lit by lia; exact ERRf| exact STf| exact SPB].
    - apply Forall_cons; [right; split; rewrite unsigned_lit by lia; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg_e; [eapply cframe_call; [exact FR0| exact FRM1| lia| | intros q0 _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    - intros a X. unfold SHV_W, RATP. cbn [rin_ivs fst snd] in X |- *. lia.
    - apply Forall_cons; [right; unfold RMallocRep.RERRNO; cbn [fst snd]; lia| apply Forall_nil]. }
  unfold shelve_res, RATP. exists pm, psa, pl, MK, SA, P, u'.
  destruct BLK1 as (BLKM & HDR & PBLK).
  lazymatch type of HDR with rw_cells _ _ _ (sa_hdr _ _ _ ?n _) => exists n; assert (NE1 : bv_unsigned n = 1) by (vm_compute; reflexivity) end.
  lazymatch type of PBLK with rw_cells _ _ _ (C8 ?v :: _) => exists v; assert (VN0 : bv_eqb v z64 = false) by (vm_compute; reflexivity) end.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNGM|]. split; [exact RNGS|]. split; [exact RNGP|].
  destruct RNGM as (_ & _ & _ & _ & IMM). destruct RNGS as (_ & _ & _ & _ & IMS). destruct RNGP as (_ & _ & _ & _ & IMP).
  repeat match goal with |- _ /\ _ => split end; try eassumption.
  - eapply rw_cells_transport; [exact BLKM| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat]; lia].
  - eapply rw_cells_transport; [exact HDR| exact MU1| exact WM1| unfold sa_hdr; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  - eapply rw_cells_transport; [exact PBLK| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat]; lia].
Qed.

(* [comment removed for export] *)
Definition err_unshelve_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (lo MK SA P : Z) (pad top ne oldv : word) (j1 j2 j3 : list byte),
  a0 = z64 -> tp = Z_to_bv 64 RATP ->
  ro_cells usegs m 0x32dea4 [C4 (Z_to_bv 64 2)] -> ro_cells usegs m 0x32dea8 [C4 (Z_to_bv 64 2)] ->
  ro_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] -> ro_cells usegs m (0x351cd0 + 8 * 2) [C8 (Z_to_bv 64 MK)] ->
  rw_cells usegs m MK [CB 24 j1; C8 (Z_to_bv 64 SA); CB 40 j2] ->
  rw_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P)) ->
  rw_cells usegs m P [C8 oldv; CB 120 j3] ->
  rblock_range MK 72 -> rblock_range SA 32 -> rblock_range P 128 -> (SA + 32 <= P \/ P + 128 <= SA) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (t1' a1' a2' a3' top' ne' : word) (m' : mem),
         ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (SA + 8, SA + 24); (P, P + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' ne' (Z_to_bv 64 P))
      /\ rw_cells usegs m' P [C8 z64; CB 120 j3]
      /\ ne' = Z_to_bv 64 (bv_unsigned ne + sa_delta z64 oldv))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_ERR_UNSHELVE) fc None m (seg_rom usegs)).

Theorem err_unshelve_proof : err_unshelve_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo MK SA P pad top ne oldv j1 j2 j3
         -> -> OC KC TSD SLOT BLKM HDR PBLK (M0 & M16 & _ & MC & MIMG) (S0 & S16 & _ & SC & SIMG) (P0 & P16 & _ & PCL & PIMG) APSP ST LO SLO MI.
  unfold FZ_ERR_UNSHELVE, RATP in *. unfold ceil_window in CEIL_RANGE__.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  change [CB 24 j1; C8 (Z_to_bv 64 SA); CB 40 j2] with ([CB 24 j1] ++ [C8 (Z_to_bv 64 SA)] ++ [CB 40 j2]) in BLKM.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in BLKM. destruct BLKM as [_ BLKM]. apply (proj1 (rw_cells_app usegs m _ _ _)) in BLKM. destruct BLKM as [MK24 _].
  assert (MK24r : ro_cells usegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)]) by exact (proj1 MK24). clear MK24.
  change [C8 oldv; CB 120 j3] with ([C8 oldv] ++ [CB 120 j3]) in PBLK.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in PBLK. destruct PBLK as [PV PJ]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PJ.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (SA + 8, SA + 24); (P, P + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold sa_hdr in HDR.
  step. carve_frame 16%nat ST. do 2 step. step. step. step. th_if_lit. step. do 2 step. do 2 step.
  lazymatch goal with H : stk _ _ lo _ |- _ => rename H into STe end.
  release_frame FR STe (bv_unsigned sp). step. step.
  pose proof T_set_local_ex_steady_proof as SLS. unfold T_set_local_ex_steady_stmt, sa_hdr in SLS.
  tcall (SLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0x351cd0 2 3 MK SA P pad top ne oldv).
  all: try first [eassumption | reflexivity | lia].
  clear SLS. cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m' end.
  lazymatch goal with H : rw_cells usegs m' P [C8 _] |- _ => rename H into PV' end.
  lazymatch goal with H : rw_cells usegs m' _ [CB 120 j3] |- _ => rename H into PJ' end.
  apply evt_done. do 6 eexists. exists m'. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - unfold sa_hdr. eassumption.
  - change [C8 (Z_to_bv 64 0); CB 120 j3] with ([C8 (Z_to_bv 64 0)] ++ [CB 120 j3]). apply rw_cells_app. split; [exact PV'|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact PJ'.
  - reflexivity.
Qed.
End WithCeiling0.
