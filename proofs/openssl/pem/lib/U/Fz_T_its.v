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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_lock_new Fz_T_sk Fz_T_tevent Fz_T_mtl.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Lemma t_nodup_ne : forall {A B : Type} (g : A -> B) (pre : list A) (b : A) (mid : list A) (b' : A) (post : list A),
  List.NoDup (map g (pre ++ b :: mid ++ b' :: post)) -> g b <> g b'.
Proof.
  intros A B g pre b mid b' post H. rewrite map_app in H. apply NoDup_app_remove_l in H. cbn [map] in H. inversion H as [|x l NI _].
  intros E. apply NI. rewrite E. rewrite map_app. apply in_or_app. right. left. reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation DTOR_KEY := (0x31d4d0)%Z (only parsing).
Notation TEV_ONCE := (0x32de90)%Z (only parsing).
Notation TEV_CMP := (0xe2d48)%Z (only parsing).
Notation TEV_COPY := (0xe2d74)%Z (only parsing).
Notation TEV_FREE := (0xe2d20)%Z (only parsing).

Definition FZ_ITS : Z := 0xe29b0.
Definition ITS_STACK : Z := 48 + MTL_STACK.

Definition its_first_res (index arg handfn tp : word) (T k : Z) (oldcb : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pn N ph H pg G psk SK plk LK pd D (u' : byte),
       v = Z_to_bv 64 1
    /\ LBall' = (pn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall
    /\ L' = (pn, 32) :: (pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: L
    /\ rblock_range N 32 /\ rblock_range H 8 /\ rblock_range G 16 /\ rblock_range SK 56 /\ rblock_range LK 40 /\ rblock_range D 32
    /\ rw_cells usegs m' (T + 8 * k) [C8 (Z_to_bv 64 H)] /\ rw_cells usegs m' (bv_unsigned tp + -150) [C1 u']
    /\ rw_cells usegs m' TEV_ONCE [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)]
    /\ rw_cells usegs m' (bv_unsigned tp + -96) [C8 oldcb]
    /\ rw_cells usegs m' H [C8 (Z_to_bv 64 N)]
    /\ rw_cells usegs m' N [C8 index; C8 arg; C8 handfn; C8 z64]
    /\ rw_cells usegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
    /\ rw_cells usegs m' SK (sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))
    /\ rw_cells usegs m' LK (mutex_cells z64 z64)
    /\ rw_cells usegs m' D [C8 (Z_to_bv 64 H); CB 24 (zeros 24)].

Definition T_its_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B T k : Z) (u : byte) (r0 g0 oldcb : word),
  (6 <= f)%nat ->
  croom L (wA 8 + wA 16 + wA 56 + wA 40 + wA 32 + wA 32) (wB 8 + wB 16 + wB 56 + wB 40 + wB 32 + wB 32) (wBig 8 + wBig 16 + wBig 56 + wBig 40 + wBig 32 + wBig 32) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - ITS_STACK ->
  rw_cells usegs m DTOR_KEY [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0xffffffff)] -> 0 <= k < 128 ->
  rw_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] ->
  rw_cells usegs m (T + 8 * k) [C8 z64] -> 0x351010 <= T + 8 * k -> T + 8 * k + 8 <= 0x3520d0 -> 0 <= T ->
  rw_cells usegs m (bv_unsigned tp + -150) [C1 u] ->
  rw_cells usegs m TEV_ONCE [C4 z64; C4 r0; C8 g0] ->
  rw_cells usegs m (bv_unsigned tp + -96) [C8 oldcb] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_ITS) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) (mtl_W tp T k) 6
                (wA 8 + wA 16 + wA 56 + wA 40 + wA 32 + wA 32) (wB 8 + wB 16 + wB 56 + wB 40 + wB 32 + wB 32) (wBig 8 + wBig 16 + wBig 56 + wBig 40 + wBig 32 + wBig 32)
                (its_first_res a0 a1 a2 tp T k oldcb LBall L)).

Theorem T_its_first_spec : crypto_zalloc_stmt -> crypto_calloc_stmt -> crypto_malloc_stmt -> T_its_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ CC CM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B T k u r0 g0 oldcb
         Hf ROOM CST SLO DK4 HK TSDP SLOT SL1 SL2 HT USED ONCE CBC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & TPE) & _ & _ & _ & GLO).
  assert (TPV : bv_unsigned tp = 3344744) by (rewrite TPE; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  unfold ITS_STACK, MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_ITS, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (w_bounds 8 ltac:(lia)) as W8. pose proof (w_bounds 16 ltac:(lia)) as W16. pose proof (w_bounds 56 ltac:(lia)) as W56.
  pose proof (w_bounds 40 ltac:(lia)) as W40. pose proof (w_bounds 32 ltac:(lia)) as W32.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 48%nat ST. do 6 step. step. do 3 step. do 3 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) (mtl_W tp T k) (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply (T_mtl_first_spec CZ CC) with (T := T) (k := k) (u := u) (r0 := r0) (g0 := g0) (oldcb := oldcb);
      [lia| eapply croom_weaken; [exact ROOM| lia..]| exact CSTc
      | rewrite unsigned_lit by lia; unfold MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia
      | reflexivity| reflexivity| exact DK4| exact HK| exact TSDP| exact SLOT| exact SL1| exact SL2| exact HT| exact USED| exact ONCE| exact CBC]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 &
    (ph & H & pg & G & psk & SK & plk & LK & pd & D & u' & -> & -> & -> & RNGH & RNGG & RNGS & RNGL & RNGD & SLOTr & USEDr & ONCEr & CBr & HBLK & GBLK & SKC & LKC & DBLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNGH as (H0 & H16 & _ & HC & HIMG).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  do 6 step. chere.
  assert (FRa : cframe (fun _ => False) (mtl_W tp T k) (bv_unsigned sp) st LBall L m st1
                       ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)
                       ((pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: L) m1).
  { eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ X; exact X]. }
  assert (ROOM6 : croom ((pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: L) (wA 32) (wB 32) (wBig 32)).
  { eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| lia..]. }
  eapply climpl_seq.
  { eapply CM with (n := 32); [lia| exact ROOM6| lia| exact CST1| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pn & N & jk & -> & -> & -> & RNGN & NBLK)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM2 as (CFR2 & _).
  unfold sk_cells, mutex_cells in *.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  assert (INH : In (ph, H, 8) ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (do 4 right; left; reflexivity).
  assert (ING : In (pg, G, 16) ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (do 3 right; left; reflexivity).
  assert (INS : In (psk, SK, 56) ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (do 2 right; left; reflexivity).
  assert (INL : In (plk, LK, 40) ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (right; left; reflexivity).
  assert (IND : In (pd, D, 32) ((pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, H, 8) CFR2 HBLK INH ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HBLK2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNGN as (N0 & N16 & _ & NC & _).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 NDL2].
  assert (INN2 : In (pn, N, 32) ((pn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)) by (left; reflexivity).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror INH) INN2 ltac:(eapply cstate_head_fresh; [exact CST2| exact INH])) as APHN.
  change (Z.to_nat 32) with 32%nat in NBLK.
  apply (rw_cells_split_CB usegs _ _ [] 32%nat _ _ [8; 8; 8; 8]%nat) in NBLK; [|reflexivity].
  cbn [mk_CB_cells app] in NBLK.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (N, N + 32); (H, H + 8)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  clear HIMG.
  (* [comment removed for export] *)
  cprefix. step. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  step. step. ubs_if. step. step. step. step. step. ubs_if. step. ths. ths. step. do 6 step.
  th_release FR2 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  pose proof RNGH as (_ & _ & _ & _ & HIMG). pose proof RNGN as (_ & _ & _ & _ & NIMG).
  (* [comment removed for export] *)
  assert (SLOT3 : rw_cells usegs m3 (T + 8 * k) [C8 (Z_to_bv 64 H)]).
  { cst_static CFR2 SLOTr X. eapply rw_cells_transport; [exact X| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (USED3 : rw_cells usegs m3 (bv_unsigned tp + -150) [C1 u']).
  { cst_static CFR2 USEDr X. eapply rw_cells_transport; [exact X| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (ONCE3 : rw_cells usegs m3 3333776 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)]).
  { cst_static CFR2 ONCEr X. eapply rw_cells_transport; [exact X| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (CB3 : rw_cells usegs m3 (bv_unsigned tp + -96) [C8 oldcb]).
  { cst_static CFR2 CBr X. eapply rw_cells_transport; [exact X| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (GBLK3 : rw_cells usegs m3 G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]).
  { pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pg, G, 16) CFR2 GBLK ING ltac:(intros X; exact X)
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as X.
    pose proof RNGG as (_ & _ & _ & GC & _).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror ING) INN2 ltac:(eapply cstate_head_fresh; [exact CST2| exact ING])) as AP1.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror ING) (or_intror INH)
                  (t_nodup_ne blk_id [(pn, N, 32); (pd, D, 32); (plk, LK, 40); (psk, SK, 56)] (pg, G, 16) [] (ph, H, 8) LBall ND2)) as AP2.
    clear HIMG NIMG APHN. eapply rw_cells_transport; [exact X| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (SKC3 : rw_cells usegs m3 SK [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 4); C8 (Z_to_bv 64 0);
                                       C8 (Z_to_bv 64 929096); C8 (Z_to_bv 64 929056); C8 (Z_to_bv 64 929140)]).
  { pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (psk, SK, 56) CFR2 SKC INS ltac:(intros X; exact X)
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as X.
    pose proof RNGS as (_ & _ & _ & SC & _).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror INS) INN2 ltac:(eapply cstate_head_fresh; [exact CST2| exact INS])) as AP1.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror INS) (or_intror INH)
                  (t_nodup_ne blk_id [(pn, N, 32); (pd, D, 32); (plk, LK, 40)] (psk, SK, 56) [(pg, G, 16)] (ph, H, 8) LBall ND2)) as AP2.
    clear HIMG NIMG APHN. eapply rw_cells_transport; [exact X| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (LKC3 : rw_cells usegs m3 LK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (plk, LK, 40) CFR2 LKC INL ltac:(intros X; exact X)
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as X.
    pose proof RNGL as (_ & _ & _ & KC & _).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror INL) INN2 ltac:(eapply cstate_head_fresh; [exact CST2| exact INL])) as AP1.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror INL) (or_intror INH)
                  (t_nodup_ne blk_id [(pn, N, 32); (pd, D, 32)] (plk, LK, 40) [(psk, SK, 56); (pg, G, 16)] (ph, H, 8) LBall ND2)) as AP2.
    clear HIMG NIMG APHN. eapply rw_cells_transport; [exact X| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (DBLK3 : rw_cells usegs m3 D [C8 (Z_to_bv 64 H); CB 24 (zeros 24)]).
  { pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pd, D, 32) CFR2 DBLK IND ltac:(intros X; exact X)
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as X.
    pose proof RNGD as (_ & _ & _ & DC & _).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror IND) INN2 ltac:(eapply cstate_head_fresh; [exact CST2| exact IND])) as AP1.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_intror IND) (or_intror INH)
                  (t_nodup_ne blk_id [(pn, N, 32)] (pd, D, 32) [(plk, LK, 40); (psk, SK, 56); (pg, G, 16)] (ph, H, 8) LBall ND2)) as AP2.
    clear HIMG NIMG APHN. eapply rw_cells_transport; [exact X| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  exists (Z_to_bv 64 1), m3, ((pn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)|].
  split. { eapply (cstate_seg _ _ _ _ _ m2 m3 _ sp tp lo B (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MI2| | lia| lia| | exact ST2| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pn, N, 32)); [exact INN2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (ph, H, 8)); [right; exact INH| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM2| lia| intros a X; destruct X| intros q0 _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    change ((pn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: LBall)
      with ([(pn, N, 32); (pd, D, 32); (plk, LK, 40); (psk, SK, 56); (pg, G, 16); (ph, H, 8)] ++ LBall) in ND2.
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply (cseg_ok_block _ _ _ _ _ (pn, N, 32)); [exact INN2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      apply (t_fresh_notin (fun _ => False)). apply (t_nodup_prefix blk_id _ _ _ ND2). left. reflexivity.
    - apply (cseg_ok_block _ _ _ _ _ (ph, H, 8)); [right; exact INH| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      apply (t_fresh_notin (fun _ => False)). apply (t_nodup_prefix blk_id _ _ _ ND2). do 5 right. left. reflexivity. }
  exists pn, N, ph, H, pg, G, psk, SK, plk, LK, pd, D, u'.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RNGN|]. split; [exact RNGH|]. split; [exact RNGG|]. split; [exact RNGS|]. split; [exact RNGL|]. split; [exact RNGD|].
  split; [exact SLOT3|]. split; [exact USED3|]. split; [exact ONCE3|]. split; [exact CB3|]. split; [exact HBLK2|]. split; [exact NBLK|].
  split; [exact GBLK3|]. split; [exact SKC3|]. split; [exact LKC3|]. exact DBLK3.
Qed.
End WithCeiling0.
