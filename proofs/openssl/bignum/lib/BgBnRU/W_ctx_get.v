(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Drv_facts.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_crypto BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import CtxKit.
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

Definition BN_CTX_GET : Z := 0x100e84.
Definition BN_CTX_GET_STACK : Z := 64 + 8400.

Definition get_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo CTX A D : Z) (b : bignum bptr) (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word) (used : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)] m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ rw_cells bgusegs m' A (bn_cells D (bn_zero_pure b))
    /\ rw_cells bgusegs m' CTX [C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C4 c6; C4 c7; C4 (Z_to_bv 64 (used + 1)); C4 c9; C4 c10; C4 c11; C8 c12].

Lemma get_tail : forall (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo CTX A D : Z) (b : bignum bptr)
    (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word) (used : Z),
  rw_cells bgusegs m A (bn_cells D b) -> 0 < A /\ A mod 8 = 0 -> 0 <= bn_flags b <= 1 ->
  rw_cells bgusegs m CTX [C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C4 c6; C4 c7; C4 (Z_to_bv 64 used); C4 c9; C4 c10; C4 c11; C8 c12] ->
  0 <= used < 2^31 - 1 ->
  rw_cells bgusegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bgusegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= A) -> (CTX + 72 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= CTX) ->
  (A + 24 <= CTX \/ CTX + 72 <= A) -> 0 <= lo ->
  evt bgusegs (get_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CTX A D b c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 used)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 A) x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x101054) fc None m (seg_rom bgusegs)).
Proof.
  intros until used. intros BN PAL FLR CX USED FR ST LO MI SEPA SEPC SEPAC LO0.
  pose proof PAL as [PA PM].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  step. step.
  eapply evt_cut.
  { eapply (BN_zero_ex_spec) with (lo := lo) (A := A) (D := D) (b := b); rewrite ?ESP; [exact BN| exact PAL| exact ST| lia| exact MI| lia| reflexivity]. }
  rewrite ?ESP. post_call bgusegs m.
  rewrite ESP in PC. unfold BnRep.bn_cells in POST.
  replace (bn_flags (bn_zero_pure b)) with (bn_flags b) in POST by reflexivity.
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (zx32_small (bn_flags b)) by lia.
  step. rewrite (sx32_small used) by lia.
  step.
  replace (Z.land (bv_unsigned (Z_to_bv 64 (bn_flags b))) 18446744073709551611) with (bn_flags b)
    by (assert (bn_flags b = 0 \/ bn_flags b = 1) as [E|E] by lia; rewrite E; reflexivity).
  step. step. step. step. step.
  do 8 step. step. release_frame FR PC (bv_unsigned sp). step.
  finish.
Qed.

Definition init_loop_post (sp gp tp s0 s1 s2 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo P : Z) (n : nat) : machine_state -> Prop :=
  fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (P + 24 * Z.of_nat n)) (Z_to_bv 64 0)
                  (Z_to_bv 64 0) (Z_to_bv 64 (-24)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x100f6c) fc None m' (seg_rom bgusegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + 24 * Z.of_nat n)] m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ rw_cells bgusegs m' P [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))].

Lemma get_init_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo P : Z) (junk : list byte),
  rw_cells bgusegs m P [CB (24 * S n) junk] ->
  stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv bgusegs m ->
  (P + 24 * Z.of_nat (S n) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= P) -> 0 < P -> P + 24 * Z.of_nat (S n) < 2^63 -> (n < 2^20)%nat ->
  evt bgusegs (init_loop_post sp gp tp s0 s1 s2 s7 s8 s9 s10 s11 F fc m lo P (S n))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 P) (Z_to_bv 64 0)
             (Z_to_bv 64 (Z.of_nat (S n))) (Z_to_bv 64 (-24)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x100f44) fc None m (seg_rom bgusegs)).
Proof.
  induction n as [|n IH]; intros until junk; intros BLK ST LO MI SEP P0 PHI NB.
  -
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + 24 * Z.of_nat 1)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    change (24 * 1)%nat with 24%nat in *. change (24 * Z.of_nat 1) with 24 in *. change (Z.of_nat 1) with 1.
    step. step.
    eapply evt_cut.
    { eapply (bn_init_spec) with (lo := lo) (A := P) (junk := junk); [exact BLK| exact ST| lia| exact MI| lia| reflexivity]. }
    post_call bgusegs m.
    step. if_true.
    chk ltac:(fun C => clear - C P0 PHI; lia).
    step. step.
    step. if_false.
    finish. eapply bk_rw_cells_recast; [exact POST| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
  -
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + 24 * Z.of_nat (S (S n)))]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    assert (SPLIT : rw_cells bgusegs m P ([CB 24 (firstn 24 junk)] ++ [CB (24 * S n) (skipn 24 junk)])).
    { pose proof BLK as [[[LJ _] _] _]. cbn in LJ.
      eapply bk_rw_cells_recast; [exact BLK| | |].
      - cbn. rewrite length_firstn, length_skipn. lia.
      - cbn. rewrite !app_nil_r. apply firstn_skipn.
      - cbn. lia. }
    apply bk_rw_cells_app in SPLIT. destruct SPLIT as [B1 B2]. cbn [cells_size csize Nat.add] in B2. change (Z.of_nat 24) with 24 in B2. clear BLK.
    step. step.
    eapply evt_cut.
    { eapply (bn_init_spec) with (lo := lo) (A := P) (junk := firstn 24 junk); [exact B1| exact ST| lia| exact MI| lia| reflexivity]. }
    post_call bgusegs m.
    step. if_true.
    chk ltac:(fun C => clear - C P0 PHI; lia).
    step. rewrite (swrap32_wrap64 (Z.of_nat (S (S n))) (-1)) by lia.
    replace (Z.of_nat (S (S n)) + -1) with (Z.of_nat (S n)) by lia.
    step.
    step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [|exfalso; lia]. clear KB.
    replace (P + 24 * Z.of_nat (S (S n))) with (P + 24 + 24 * Z.of_nat (S n)) by lia.
    unfold BnRep.bn_cells in POST.
    eapply evt_cut.
    { eapply (IH) with (lo := lo) (P := P + 24) (junk := skipn 24 junk); [exact B2| exact PC| lia| exact MI0| lia| lia| lia| lia]. }
    lazymatch goal with |- forall _, _ -> evt _ _ _ => idtac end.
    lazymatch goal with MUx : munch _ m ?mx |- _ => post_call bgusegs mx end.
    apply evt_done. unfold init_loop_post. do 16 eexists. eexists.
    split. { replace (P + 24 + 24 * Z.of_nat (S n)) with (P + 24 * Z.of_nat (S (S n))) by lia. reflexivity. }
    split; [exact MU|].
    split; [exact WM|]. split; [exact MI|]. split; [exact PC|].
    assert (JOIN : rw_cells bgusegs x31 P ([C8 (wz 0); C4 (wz (Z.of_nat (bn_top (bn_nil 0 : bignum bptr)))); C4 (wz (Z.of_nat (bn_dmax (bn_nil 0 : bignum bptr))));
                                         C4 (wz (Z.b2z (bn_neg (bn_nil 0 : bignum bptr)))); C4 (wz (bn_flags (bn_nil 0 : bignum bptr)))]
                                        ++ [CB (24 * S n) (repeat (Z_to_bv 8 0) (24 * S n))])).
    { apply bk_rw_cells_app. split; [exact POST| exact POST0]. }
    eapply bk_rw_cells_recast; [exact JOIN| | |].
    + cbn [cells_wf cell_wf]. rewrite repeat_length. tauto.
    + cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      replace (24 * S (S n))%nat with (24 + 24 * S n)%nat by lia. rewrite repeat_app. reflexivity.
    + cbn [cells_size csize app]. lia.
Qed.

Lemma nondecr_last_incr : forall (l : list nat) x y, nondecr (l ++ [x]) -> (x <= y)%nat -> nondecr (l ++ [y]).
Proof.
  induction l as [|z l IH]; intros x y H Hxy; cbn [app nondecr] in *; [tauto|].
  destruct H as [Hz H]. split; [|eapply IH; eassumption]. destruct l as [|w l]; cbn [app] in *; lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Lemma BN_CTX_get_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_CTX_GET_STACK -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_get (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun r bs' OW' PL' a0' => PL' = PL /\ (exists i, r = RPool i) /\ (exists a, ref_at bs' OW' PL r a /\ a0' = wz a)
                                     /\ (forall q A n, In (q, A, n) OW -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_GET) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> EC ->.
    unfold BN_CTX_GET_STACK, BN_CTX_GET, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof WFS as (EL & BOK & EONE & (CE1 & CE2 & CE3 & CE4 & CE5 & CE6 & CE7 & CE8)).
    destruct (lib_state_cx_open [] bs m OW PL EA LS) as (Hs & IX & CV & LSC).
    apply (cx_view_some _ _ _ _ _ _ _ _ EC) in CV. destruct CV as (BC & LHs & CX & STK & HItems & HLinks). change BN_CTX_SZ with 72 in BC.
    pose proof (RH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
    set (c := st_ctx bs) in *.
    unfold ctx_cells in CX. rewrite CE1, CE2 in CX. change (Z.of_nat 0) with 0 in CX. change (Z.b2z false) with 0 in CX.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold BN_CTX_get, bbind, bgetctx, bret, bunr, bmalloc, bsetctx, bget, bset, bgetst, bsetbns.
    cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
    rewrite CE1, CE2. cbn [Nat.eqb negb orb].
    set (psize := (BN_CTX_POOL_SIZE * length (gx_items c))%nat) in *.
    assert (P48 : (psize <= 48)%nat /\ (gx_used c <= psize)%nat) by (subst psize; unfold BN_CTX_POOL_SIZE in *; split; lia).
    destruct P48 as [P48 UP].
    unfold implM. iprefix.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (ac, ac + 72)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    assert (CA8 : ac mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
    carve_frame 64%nat ST. do 10 step.
    chk ltac:(fun C => rewrite ?land64_small in C by (clear - CA0 CAC; lia); clear - C CA0 CAC; lia).
    step. step. rewrite (land7_wrap _ CA8).
    chk ltac:(fun C => clear - C; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_false.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_true.
    step. unfold MallocRep.wz at 1. rewrite (zx32_small (Z.of_nat (gx_pused c))) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat psize)) by lia.
    step. rewrite (swrap32_wrap64 (Z.of_nat (gx_pused c)) 0) by lia. rewrite Z.add_0_r.
    step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    -
      replace (gx_pused c =? psize)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      cbn [tbind fst snd].
      set (i := gx_pused c) in *.
      assert (IU : i = gx_used c) by exact CE3.
      assert (ILT : (i < psize)%nat) by lia.
      pose proof (Nat.div_mod_eq i 16) as DM. pose proof (Nat.mod_upper_bound i 16 ltac:(lia)) as MB.
      assert (KLT : (i / 16 < length Hs)%nat).
      { rewrite LHs. apply div16_of_lt. subst psize. unfold BN_CTX_POOL_SIZE in ILT. lia. }
      destruct (nth_error Hs (i / 16)) as [Hk|] eqn:EHk; [|exfalso; apply nth_error_None in EHk; lia].
      pose proof (item_facts s OW LB m bs PL EA ac qc Hs _ _ HEAP PARTS EC LHs HItems EHk) as (HK0 & HKC & HKM & HKX & HKK & HKI). change BN_CTX_SZ with 72 in HKX.
      pose proof (item_align s OW LB m bs Hs _ _ HEAP LHs HItems EHk) as HK8.
      destruct (nth_error (gx_items c) (i / 16)) as [qk|] eqn:Eqk; [|exfalso; apply nth_error_None in Eqk; lia].
      pose proof (HItems _ _ Eqk) as HinK. rewrite (nth_error_nth _ _ _ EHk) in HinK. change ITEM_SZ with 400 in HinK.
      assert (HA : ref_at bs OW PL (RPool i) (Hk + 24 * Z.of_nat (i mod 16))).
      { replace (RPool i) with (RPool (BN_CTX_POOL_SIZE * (i / 16) + i mod 16)) by (unfold BN_CTX_POOL_SIZE; rewrite div16_mod_eq; reflexivity).
        eapply ref_at_item_slot; [exact Eqk| exact HinK| unfold BN_CTX_POOL_SIZE; lia]. }
      assert (NRO : RPool i <> ROne) by (unfold RPool, ROne, NFIX; lia).
      lazymatch goal with |- context [mkGx (gx_items c) ?cu (S i)] => set (cur := cu) in * end.
      assert (ECUR : cur = Some (i / 16)%nat).
      { subst cur. destruct (Nat.eqb_spec i 0) as [E0|E0]; [rewrite E0; reflexivity|].
        pose proof CE6 as EC6. fold c in EC6. rewrite <- IU in EC6. replace (i =? 0)%nat with false in EC6 by (symmetry; apply Nat.eqb_neq; exact E0).
        unfold BN_CTX_POOL_SIZE in EC6 |- *. destruct (Nat.eqb_spec (i mod 16) 0) as [EM|EM]; rewrite EC6; f_equal.
        - exact (proj1 (div16_pred_bd i E0 EM)).
        - exact (div16_pred_in i EM). }
      destruct (lib_state_open [] bs m OW PL EA (RPool i) _ LSC ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
      set (b := getbn (RPool i) bs) in *.
      assert (FLR : 0 <= bn_flags b <= 1) by (destruct OK4 as [E|E]; rewrite E; lia).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSC HA) as HV.
      lazymatch goal with |- evt _ ?Q _ => remember Q as QQ eqn:EQQ end.
      lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mx _) =>
        assert (CONT : forall (hk : Z) (x11 x12 : word) (mX : mem),
          hk = Hk ->
          rw_cells bgusegs mX ac
            [C8 (wz (hd 0 Hs)); C8 (wz hk); C8 (wz (last Hs 0)); C4 (wz (Z.of_nat i)); C4 (wz (Z.of_nat psize)); C8 (wz IX);
             C4 (wz (Z.of_nat (length (gx_frames c)))); C4 (wz (Z.of_nat (gx_ssize c))); C4 (wz (Z.of_nat (gx_used c)));
             C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)] ->
          rw_cells bgusegs mX (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
          stk bgusegs mX lo (bv_unsigned sp + -64) ->
          munch [(bv_unsigned sp + -64, bv_unsigned sp); (ac, ac + 72)]%Z m mX -> wmono bgusegs m mX -> mem_inv bgusegs mX ->
          rw_cells bgusegs mX 3346164 [C4 errv] ->
          evt bgusegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 ac)
                               (Z_to_bv 64 (Z.of_nat i)) x11 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x100ff8) fc None mX (seg_rom bgusegs))) end.
      { intros hk x11 x12 mX -> CXX FRX STX MUX WMX MIX ERRX.
        clear MU WM MI ERR ST FR CX.
        unfold MallocRep.wz in CXX.
        step.
        chk ltac:(fun C => rewrite ?land64_small in C by (clear - HK0 HKC; lia); clear - C HK0 HKC; lia).
        step. rewrite (land7_wrap _ HK8).
        chk ltac:(fun C => clear - C; lia).
        step. step.
        rewrite !(unsigned_lit (Z.of_nat i)) by lia.
        replace (Z.land (Z.of_nat i) 15) with (Z.of_nat (i mod 16)).
        2:{ change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. rewrite Nat2Z.inj_mod. reflexivity. }
        step. step. step.
        rewrite !(unsigned_lit (Z.of_nat (i mod 16))) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
        rewrite (unsigned_lit (Z.of_nat (i mod 16) * 2 ^ 3)) by lia.
        replace (Z.of_nat (i mod 16) * 2 ^ 5 + - (Z.of_nat (i mod 16) * 2 ^ 3)) with (24 * Z.of_nat (i mod 16)) by lia.
        step. rewrite (not64 Hk) by (clear - HK0 HKC; lia).
        step.
        chk ltac:(fun C => clear - C HK0 HKC MB; lia).
        step. step.
        unfold bn_cells in BN.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) => rename my into m2 end.
        lazymatch type of MUX with munch ?W0 _ _ =>
          apply (rw_cells_transport bgusegs W0 m m2 (Hk + 24 * Z.of_nat (i mod 16))) in BN; [| exact MUX| exact WMX| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
        eapply evt_cut.
        { eapply (get_tail) with (lo := lo) (CTX := ac) (A := Hk + 24 * Z.of_nat (i mod 16)) (D := D) (b := b) (used := Z.of_nat (gx_used c));
            [exact BN | split; [clear - HK0; lia| clear - HK8; Z.div_mod_to_equations; lia] | exact FLR | exact CXX | lia | exact FRX | exact STX | lia | exact MIX | lia | lia | lia | lia ]. }
        intros ms' PO. unfold get_tail_post in PO.
        destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & mF & -> & MUt & WMt & MIt & STt & BNt & CXt).
        subst QQ. apply evt_done. to_implM. cbn [embed interp]. apply implM_ret. apply evt_done.
        set (bz := bn_zero_pure b).
        set (c2 := mkGx (gx_items c) cur (S i) (gx_indexes c) (gx_frames c) (gx_ssize c) (S (gx_used c)) 0 false).
        lazymatch goal with |- context [(RPool i, ?stM)] => change stM with (set_ctx c2 (setbn (RPool i) bz bs)) end.
        set (WF := [(bv_unsigned sp - 80, bv_unsigned sp); (Hk + 24 * Z.of_nat (i mod 16), Hk + 24 * Z.of_nat (i mod 16) + 24); (ac, ac + 72)]%Z).
        assert (MUF : munch WF m mF).
        { eapply munch_trans; [eapply munch_weaken; [|exact MUX]| exact MUt].
          intros x Hx. subst WF. cbn [outside] in *. clear - Hx. intuition lia. }
        assert (WMF : wmono bgusegs m mF) by (eapply wmono_trans; eassumption).
        assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) WF).
        { subst WF. constructor; [left; cbn; lia|]. constructor; [right; left; exists (qk, Hk, 400); cbn; split; [exact HinK| lia]|].
          constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith| constructor]. }
        destruct (bn_arr_facts s OW LB m HEAP bs PL EA (bv_unsigned sp) B PARTS FROK (RPool i) D HV NRO ARR) as (U & LENW & D0 & DC & DI & DSEP).
        specialize (DSEP (RPool i) _ HA). fold b in U, LENW, DC, DI, DSEP.
        assert (DCX : ac + 72 <= D \/ D + 8 * Z.of_nat (bn_dmax b) <= ac).
        { pose proof ARR as ARR'. unfold bn_arr in ARR'. rewrite pl_of_pool in ARR'. destruct (bn_d b) as [pd|] eqn:Ed.
          - destruct ARR' as [Hin _]. assert (NE : qc <> pd) by (eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| eapply bn_in_m; [exact HV| exact Ed]]).
            destruct PLB as (_ & PC & _). rewrite EC in PC. exact (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP PC Hin NE).
          - destruct ARR' as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn. lia. }
        assert (LKF : links mF Hs).
        { eapply links_transport; [exact HLinks| exact MUF| exact WMF|]. intros j H Hj. subst WF. cbn [disjoint_from].
          pose proof (item_facts s OW LB m bs PL EA ac qc Hs _ _ HEAP PARTS EC LHs HItems Hj) as (F0 & FC & FM & FX & FK & FI). change BN_CTX_SZ with 72 in FX.
          destruct (Nat.eq_dec j (i / 16)) as [->|NEj].
          - rewrite EHk in Hj. injection Hj as <-. clear - F0 FC FX MB CEIL LO SPR. lia.
          - specialize (FK _ _ EHk ltac:(congruence)). clear - F0 FC FX FK MB CEIL LO SPR. lia. }
        assert (LSF : lib_state (set_ctx c2 (setbn (RPool i) bz bs)) mF OW PL EA).
        { unfold lib_state.
          assert (IDS1 : ids_ok (setbn (RPool i) bz bs) PL EA) by (apply ids_ok_setbn_same; [exact IDS| exact HV| reflexivity]).
          assert (OKz : bg_ok bz).
          { subst bz. unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OK1|]. split; [lia|]. split; [exact OK3| exact OK4]. }
          assert (LS1 : lib_state_hc true [] (setbn (RPool i) bz bs) mF OW PL EA).
          { eapply (lib_state_close [] bs mF OW PL EA (RPool i) (Hk + 24 * Z.of_nat (i mod 16)) bz); [| exact ND| exact HA| exact NRO| | exact OKz| exact IDS1].
            - eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP| exact LSH| exact MUF| exact WMF| exact FROK|]. subst WF.
              constructor; [apply w_stack; cbn; lia|].
              constructor; [eapply (w_struct OW LB bs PL EA (bv_unsigned sp) true [RPool i] _ (RPool i) (Hk + 24 * Z.of_nat (i mod 16)));
                              [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]|].
              constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]| constructor].
            - exists D. split; [exact BNt|]. change (bn_arr mF OW (pl_of PL (RPool i)) D b).
              eapply bn_arr_of_u64arr; [exact ARR|]. eapply u64arr_transport; [exact U| exact MUF| exact WMF|].
              subst WF. cbn [disjoint_from]. rewrite LENW. clear - DSEP DCX DC CEIL LO SPR. lia. }
          eapply (lib_state_cx_close [] (setbn (RPool i) bz bs) _ mF OW PL EA Hs IX); [exact LS1| exact ND| reflexivity| reflexivity| reflexivity| reflexivity| | |].
          - apply st_wf_set_ctx; [apply st_wf_setbn; [exact WFS| exact NRO| exact OKz]| reflexivity|].
            unfold ctx_wf, c2. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many].
            split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [fold psize; lia|]. split; [exact CE5|].
            split. { rewrite ECUR. cbn [Nat.eqb]. f_equal. rewrite <- IU. unfold BN_CTX_POOL_SIZE. rewrite Nat.sub_succ, Nat.sub_0_r. reflexivity. }
            split; [eapply nondecr_last_incr; [exact CE7| lia]| exact CE8].
          - apply ids_ok_set_ctx_same; [exact IDS1| reflexivity| reflexivity].
          - apply (cx_view_some _ _ _ _ _ _ _ _ EC). cbn [st_ctx set_ctx]. split; [exact BC|]. split; [exact LHs|]. split; [|split; [|split; [| exact LKF]]].
            + unfold ctx_cells, cur_addr, c2. cbn [gx_items gx_current gx_pused gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z].
              rewrite ECUR. cbn [gx_items]. rewrite (nth_error_nth _ _ _ EHk). unfold MallocRep.wz. rewrite !Nat2Z.inj_succ. unfold Z.succ. exact CXt.
            + apply (stack_rep_same mF OW IX c c2); [reflexivity| reflexivity| reflexivity|].
              eapply (stack_rep_keep s OW LB m mF bs PL EA ac qc IX); [exact HEAP| exact PARTS| exact EC| exact STK| exact MUF| exact WMF|]. subst WF.
              constructor; [left; cbn; lia|]. constructor; [|constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]].
              right; right. exists qk, Hk, 400. split; [apply in_or_app; left; exact HinK|]. cbn [fst snd]. split; [lia|]. split; [lia|].
              fold c. intros E. eapply (ids_item_idx_neq bs qk qk); [eapply ids_m_nodup; exact IDS| eapply nth_error_In; exact Eqk| symmetry; exact E| reflexivity].
            + apply item_blocks_set_ctx; [reflexivity| exact HItems]. }
        unfold bn_post. do 15 eexists. exists mF, OW, PL, errv. split; [reflexivity|]. cbn [fst snd].
        split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUF WMF HWL CEIL)|]. split; [exact LSF|].
        split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MUF WMF HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact STt|].
        split. { unfold LX_ERRNO, RATP. change (3346328 - 164) with 3346164.
                 eapply rw_cells_transport; [exact ERRX| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add].
                 clear - HK0 HKC HKM CAI GLO LO SPR MB. lia. }
        split; [exact MIt|].
        split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUF WMF HWL CEIL); unfold GLOBALS_TOP; lia|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [apply refs_stable_ow; [reflexivity| auto]|].
        split; [reflexivity|]. split; [eexists; reflexivity|]. split; [|intros q0 A0 n0 Hq0; exact Hq0].
        exists (Hk + 24 * Z.of_nat (i mod 16)). split; [|reflexivity].
        apply (proj1 (ref_at_same_items (setbn (RPool i) bz bs) c2 OW PL (RPool i) _ ltac:(reflexivity))).
        apply (proj2 (ref_at_setbn bs OW PL (RPool i) bz (RPool i) _)). exact HA. }

      step. if_cases KU; zify_cond KU; rewrite ?unsigned_lit in KU by lia.
      +
        assert (I0 : i = 0%nat) by lia.
        assert (EH : hd 0 Hs = Hk).
        { rewrite I0 in EHk. cbn in EHk. destruct Hs as [|h0 Hs']; [discriminate EHk|]. injection EHk as ->. reflexivity. }
        step. unfold MallocRep.wz at 1. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply evt_eq; [| eapply (CONT (hd 0 Hs) _ _ mx); [exact EH| exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR] ] end.
        first [reflexivity | rewrite I0; reflexivity].
      +
        pose proof CE6 as EC6. fold c in EC6. rewrite <- IU in EC6. replace (i =? 0)%nat with false in EC6 by (symmetry; apply Nat.eqb_neq; lia).
        unfold cur_addr in CX. rewrite EC6 in CX. unfold BN_CTX_POOL_SIZE in CX.
        step.
        rewrite (unsigned_lit (Z.of_nat i)) by lia.
        replace (Z.land (Z.of_nat i) 15) with (Z.of_nat (i mod 16)).
        2:{ change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. rewrite Nat2Z.inj_mod. reflexivity. }
        step. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
        *
          assert (EK : ((i - 1) / 16 = i / 16)%nat) by (apply div16_pred_in; lia).
          rewrite EK, (nth_error_nth _ _ _ EHk) in CX.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            eapply (CONT Hk _ _ mx); [reflexivity| exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR] end.
        *
          assert (EM : (i mod 16 = 0)%nat) by lia.
          destruct (div16_pred_bd i ltac:(lia) EM) as [EK0 KP1].
          assert (EK : ((i - 1) / 16 = i / 16 - 1)%nat) by lia.
          rewrite EK in CX.
          destruct (nth_error Hs (i / 16 - 1)) as [Hp|] eqn:EHp; [|exfalso; apply nth_error_None in EHp; lia].
          pose proof (item_facts s OW LB m bs PL EA ac qc Hs _ _ HEAP PARTS EC LHs HItems EHp) as (HP0 & HPC & HPM & HPX & _ & _). change BN_CTX_SZ with 72 in HPX.
          rewrite (nth_error_nth _ _ _ EHp) in CX.
          assert (LNK : rw_cells bgusegs m (Hp + 384) [C8 (wz (match (i / 16 - 1)%nat with O => 0 | S k' => nth k' Hs 0 end)); C8 (wz Hk)]).
          { replace Hk with (nth (S (i / 16 - 1)) Hs 0) by (replace (S (i / 16 - 1)) with (i / 16)%nat by lia; exact (nth_error_nth _ _ _ EHk)).
            exact (HLinks _ _ EHp). }
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            lazymatch type of MU with munch ?W0 _ _ =>
              apply (rw_cells_transport bgusegs W0 m mx (Hp + 384)) in LNK; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end end.
          unfold MallocRep.wz in LNK.
          pose proof (item_align s OW LB m bs Hs _ _ HEAP LHs HItems EHp) as HP8.
          unfold MallocRep.wz in CX.
          step.
          chk ltac:(fun C => rewrite ?land64_small in C by (clear - HP0 HPC; lia); clear - C HP0 HPC; lia).
          step. rewrite (land7_wrap _ HP8).
          chk ltac:(fun C => clear - C; lia).
          step. step. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            eapply evt_eq; [| eapply (CONT Hk _ _ mx); [reflexivity| exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR] ] end.
          first [reflexivity | rewrite ?EM; reflexivity].
    -
      replace (gx_pused c =? psize)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
      destruct (3 <=? length (gx_items c))%nat eqn:E3.
      { cbn [tbind fst snd]. ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
      apply Nat.leb_gt in E3. cbn [tbind fst snd].
      assert (IU : gx_pused c = gx_used c) by exact CE3.
      assert (IP : gx_pused c = psize) by lia.
      step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
      do 5 step.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ac, ac + 72)]).
      { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith| constructor]. }
      assert (HEAP1 : RHEAP s (OW ++ LB) m1) by (exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)).
      assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
      assert (LXP1 : lx_pres LB (bv_unsigned sp) (XW PL) m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
      assert (LSC1 : lib_state_hc true [] bs m1 OW PL EA).
      { eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP| exact LSC| exact MU| exact WM| exact FROK|].
        constructor; [apply w_stack; cbn; lia|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]| constructor]. }
      assert (STK1 : stack_rep m1 OW IX c).
      { eapply (stack_rep_keep s OW LB m m1 bs PL EA ac qc IX); [exact HEAP| exact PARTS| exact EC| exact STK| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]. }
      assert (PM1 : links m1 Hs).
      { eapply (links_keep s OW LB m m1 bs PL EA ac qc Hs); [exact HEAP| exact PARTS| exact EC| exact LHs| exact HItems| exact HLinks| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]. }
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
      ihere. to_implM. cbn [embed]. unfold POOL_ITEM_BYTES.
      eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 400);
        [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
        | exact (proj1 LSC1) | reflexivity | lia | reflexivity | ].
      intros pn st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & An & errv2
                      & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & (junkA & BLK)).
      replace (ret_pc (Z_to_bv 64 1052452)) with (Z_to_bv 64 1052452) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AGP.
      apply (rw_cells_agree _ _ _ _ _ AGP) in FR; [| intros x Hx; left; cbn in Hx; lia].
      apply (rw_cells_agree _ _ _ _ _ AGP) in CX; [| intros x Hx; right; right; exists (qc, ac, 72); split; [apply in_or_app; left; exact BC| cbn in Hx |- *; lia]].
      assert (LSC3 : lib_state_hc true [] bs m3 OW PL EA).
      { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ _ (bv_unsigned sp) B); [exact LSC1| exact FROK| | exact HP|]; [lia|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (STK3 : stack_rep m3 OW IX c).
      { eapply (stack_rep_heap_pres OW); [| exact STK1| exact HP]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (PM3 : links m3 Hs).
      { eapply (links_heap_pres bs OW); [exact LHs| exact HItems| | exact PM1| exact HP]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (ND3 : List.NoDup (map blk_id ((pn, An, 400) :: OW ++ LB))) by (eapply LH_nodup; exact HEAP3).
      assert (FRESH : ~ In pn (map blk_id (OW ++ LB))) by (cbn [map] in ND3; apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
      assert (FRESHA : ~ In pn (all_ids bs PL EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + 400 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (LH_disjoint _ _ _ (pn, An, 400) (q, A, n) HEAP3 ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ BC) as SEPc.
      set (OW1 := (pn, An, 400) :: OW).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSC3) as PARTS3.
      assert (LSC3' : lib_state_hc true [] bs m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LSC3|]; intros q A n _ Hq; right; exact Hq).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSC3') as PARTS1.
      assert (STK3' : stack_rep m3 OW1 IX c) by (eapply stack_rep_ow; [| exact STK3]; intros b0 Hb0; right; exact Hb0).
      assert (HItems1 : item_blocks bs OW1 Hs) by (eapply item_blocks_ow; [exact HItems| intros b0 Hb0; right; exact Hb0]).
      assert (LXP3 : lx_pres LB (bv_unsigned sp) (XW PL) m m3).
      { eapply lx_pres_trans; [exact LXP1|]. apply lx_pres_of_heap_pres.
        eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
      unfold LX_ERRNO, RATP in ERR3. change (3346328 - 164) with 3346164 in ERR3.

      assert (HR : forall j H, nth_error Hs j = Some H ->
                0 < H /\ H + 400 <= alloc_ceiling /\ (H + 400 <= 0x10000 \/ 0x353000 <= H) /\ (H + 400 <= ac \/ ac + 72 <= H) /\ (An + 400 <= H \/ H + 400 <= An)
                /\ (forall j' H', nth_error Hs j' = Some H' -> j' <> j -> H + 400 <= H' \/ H' + 400 <= H)).
      { intros j H Hj. pose proof (item_facts s OW LB m bs PL EA ac qc Hs _ _ HEAP PARTS EC LHs HItems Hj) as (F0 & FC & FM & FX & FK & FI). change BN_CTX_SZ with 72 in FX.
        split; [exact F0|]. split; [exact FC|]. split; [exact FM|]. split; [exact FX|]. split; [|exact FK].
        assert (Hj' : (j < length (gx_items c))%nat) by (rewrite <- LHs; apply nth_error_Some; congruence).
        destruct (nth_error (gx_items c) j) as [qj|] eqn:Eqj; [|apply nth_error_None in Eqj; lia].
        pose proof (HItems j qj Eqj) as Hin. rewrite (nth_error_nth _ _ _ Hj) in Hin. exact (NEWSEP _ _ _ Hin). }

      assert (SPLIT : rw_cells bgusegs m3 An ([CB 384 (firstn 384 junkA)] ++ [CB 16 (skipn 384 junkA)])).
      { pose proof BLK as [[[LJ _] _] _]. cbn in LJ.
        eapply bk_rw_cells_recast; [exact BLK| | |].
        - cbn. rewrite length_firstn, length_skipn. lia.
        - cbn. rewrite !app_nil_r. apply firstn_skipn.
        - cbn. lia. }
      apply bk_rw_cells_app in SPLIT. destruct SPLIT as [B1 B2]. cbn [cells_size csize Nat.add] in B2. change (Z.of_nat 384) with 384 in B2. clear BLK.
      cbn [tbind fst snd embed interp]. apply implM_ret.
      pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (ac, ac + 72); (An, An + 400)]%Z m3) as MU3.
      pose proof (wmono_refl bgusegs m3) as WM3.
      clear MU WM LSC LSC1 LSC3 HEAP1 AUX1 STK STK1 STK3 PM1 HLinks.
      unfold MallocRep.wz in *.
      assert (BA8 : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
      step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
      step. step. rewrite (land7_wrap _ BA8).
      chk ltac:(fun C => clear - C; lia).
      step. step. step. step.
      eapply evt_cut.
      { eapply (get_init_loop 15) with (lo := lo) (P := An) (junk := firstn 384 junkA); rewrite ?ESP;
          [exact B1 | exact ST3 | lia | exact MI3 | lia | lia | lia | lia]. }
      rewrite ?ESP. post_call bgusegs m3.
      rewrite ESP in PC. change (24 * Z.of_nat 16) with 384. change (24 * 16)%nat with 384%nat in POST.
      assert (SPLZ : rw_cells bgusegs x15 An (bn_cells 0 (bn_nil 0) ++ [CB 360 (repeat (Z_to_bv 8 0) 360)])).
      { eapply bk_rw_cells_recast; [exact POST| | |].
        - cbn [bn_cells app cells_wf cell_wf]. rewrite repeat_length. tauto.
        - vm_compute. reflexivity.
        - reflexivity. }
      apply bk_rw_cells_app in SPLZ. destruct SPLZ as [BN0 ZR]. cbn [bn_cells cells_size csize Nat.add] in ZR. change (Z.of_nat 24) with 24 in ZR.
      unfold bn_cells in BN0. clear POST.
      lazymatch goal with |- evt _ ?Q _ => remember Q as QQ eqn:EQQ end.

      assert (CONTB : forall (WX : list (Z * Z)) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y28 y29 y30 y31 : word) (mX : mem),
        sub_fp [(bv_unsigned sp - 80, bv_unsigned sp); (An, An + 24); (ac, ac + 72)]%Z WX ->
        Forall (w_lib bs OW1 PL lo (bv_unsigned sp)) WX ->
        Forall (w_okc OW1 LB bs PL EA (bv_unsigned sp) true []) WX ->
        Forall (fun iv : Z * Z => alloc_ceiling <= fst iv \/ (ac <= fst iv /\ snd iv <= ac + BN_CTX_SZ)
                                  \/ (exists q A n, In (q, A, n) (OW1 ++ LB) /\ A <= fst iv /\ snd iv <= A + n /\ Some q <> gx_indexes (st_ctx bs))) WX ->
        (forall k H, nth_error Hs k = Some H -> (S k < length Hs)%nat -> disjoint_from WX (H + 384) 16) ->
        munch WX m3 mX -> wmono bgusegs m3 mX -> mem_inv bgusegs mX ->
        rw_cells bgusegs mX ac
          [C8 (Z_to_bv 64 (hd 0 (Hs ++ [An]))); C8 (Z_to_bv 64 (cur_addr Hs c)); C8 (Z_to_bv 64 (last Hs 0)); C4 (Z_to_bv 64 (Z.of_nat (gx_pused c))); C4 (Z_to_bv 64 (Z.of_nat psize)); C8 (Z_to_bv 64 IX);
           C4 (Z_to_bv 64 (Z.of_nat (length (gx_frames c)))); C4 (Z_to_bv 64 (Z.of_nat (gx_ssize c))); C4 (Z_to_bv 64 (Z.of_nat (gx_used c)));
           C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
        rw_cells bgusegs mX (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk bgusegs mX lo (bv_unsigned sp + -64) ->
        rw_cells bgusegs mX 3346164 [C4 errv2] ->
        rw_cells bgusegs mX An [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (Z.of_nat (bn_top (bn_nil 0 : bignum bptr)))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax (bn_nil 0 : bignum bptr))));
                               C4 (Z_to_bv 64 (Z.b2z (bn_neg (bn_nil 0 : bignum bptr)))); C4 (Z_to_bv 64 (bn_flags (bn_nil 0 : bignum bptr)))] ->
        rw_cells bgusegs mX (An + 24) [CB 360 (repeat (Z_to_bv 8 0) 360)] ->
        rw_cells bgusegs mX (An + 384) [C8 (Z_to_bv 64 (last Hs 0)); C8 (Z_to_bv 64 0)] ->
        (forall k H, nth_error Hs k = Some H -> S k = length Hs ->
           rw_cells bgusegs mX (H + 384) [C8 (Z_to_bv 64 (match k with O => 0 | S k' => nth k' Hs 0 end)); C8 (Z_to_bv 64 An)]) ->
        evt bgusegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) y5 y6 y7 sp (Z_to_bv 64 ac)
                              y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 An) y19 y20 y21 y22 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                         F (Z_to_bv 64 0x101034) fc None mX (seg_rom bgusegs))).
      { intros WX y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y28 y29 y30 y31 mX SUB HWLX HWOK HWST HWLK MUX WMX MIX CXX FRX STX ERRX BNX ZRX LNX LTX.
        clear MU3 WM3 B2 BN0 ZR CX FR ERR3. try clear ST3. try clear PC. try clear MI3. try clear MI0.
        change (munch WX m3 mX) with (id (munch WX m3 mX)) in MUX.
        pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (An, An + 24); (ac, ac + 72)]%Z mX) as MUc. pose proof (wmono_refl bgusegs mX) as WMc.
        step. step.
        step. rewrite (sx32_small (Z.of_nat psize)) by lia.
        step. rewrite (sx32_small (Z.of_nat (gx_pused c))) by lia.
        step. step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        eapply evt_cut.
        { eapply (get_tail) with (lo := lo) (CTX := ac) (A := An) (D := 0) (b := bn_nil 0) (used := Z.of_nat (gx_used c));
            [exact BNX | split; [clear - BA0; lia| exact BA8] | cbn; lia | exact CXX | lia | exact FRX | exact STX | lia | eassumption | lia | lia | lia | lia ]. }
        intros ms' PO. unfold get_tail_post in PO.
        destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & mF & -> & MUt & WMt & MIt & STt & BNt & CXt).
        subst QQ. apply evt_done.
        set (c2 := mkGx (gx_items c ++ [pn]) (Some (length (gx_items c))) (S (gx_pused c)) (gx_indexes c) (gx_frames c) (gx_ssize c) (S (gx_used c)) 0%nat false).
        set (stF := mkST (st_bns bs ++ repeat (bn_nil 0) BN_CTX_POOL_SIZE) c2 (st_ri bs) (st_n0 bs) (st_rbits bs) (st_rshift bs)).
        lazymatch goal with |- context [(RPool (gx_pused c), ?stM)] =>
          assert (ESTF : stM = stF);
          [| rewrite ESTF] end.
        { subst stF c2. unfold set_ctx, setbn, set_bns, getbn. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used].
          f_equal.
          set (L := st_bns bs ++ repeat (bn_nil 0) BN_CTX_POOL_SIZE).
          assert (EN : nth (RPool (gx_pused c)) L (bn_nil 0) = bn_nil 0).
          { subst L. rewrite app_nth2 by (rewrite EL, IP; subst psize; unfold RPool; lia). apply nth_repeat. }
          transitivity (list_set L (RPool (gx_pused c)) (nth (RPool (gx_pused c)) L (bn_nil 0))); [| apply list_set_nth_id].
          f_equal. rewrite EN. reflexivity. }
        assert (MUcF : munch [(bv_unsigned sp - 80, bv_unsigned sp); (An, An + 24); (ac, ac + 72)]%Z mX mF).
        { eapply munch_trans; [exact MUc|]. first [exact MUt | eapply munch_weaken; [|exact MUt]; intros xx Hx; cbn [outside] in *; clear - Hx; intuition lia]. }
        assert (WMcF : wmono bgusegs mX mF) by (eapply wmono_trans; eassumption).
        assert (MUF : munch WX m3 mF).
        { unfold id in MUX. eapply munch_trans; [exact MUX|]. eapply munch_weaken; [exact SUB| exact MUcF]. }
        assert (WMF : wmono bgusegs m3 mF) by (eapply wmono_trans; eassumption).
        assert (HinN : In (pn, An, 400) OW1) by (left; reflexivity).
        assert (BC1 : In (qc, ac, 72) OW1) by (right; exact BC).
        assert (ND1 : List.NoDup (map blk_id OW1)) by (eapply (RH_nodup_l st1 OW1 LB m3); exact HEAP3).
        assert (LSF : lib_state stF mF OW1 PL EA).
        { unfold lib_state. eapply (lib_state_cx_close_newitem [] bs stF mF OW1 PL EA Hs IX pn An ac qc);
            [| exact ND1| exact EC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| | exact FRESHA| exact HinN| |].
          - eapply (lib_state_frame st1 LB (bv_unsigned sp) B); [exact HEAP3| exact LSC3'| exact MUF| exact WMF| exact FROK| exact HWOK].
          - unfold st_wf. subst stF c2. cbn [st_bns st_ctx gx_items]. split; [|split; [|split]].
            + rewrite !length_app, repeat_length, EL. cbn [length]. lia.
            + intros r Hr NE1. unfold getbn. cbn [st_bns]. rewrite length_app, repeat_length in Hr.
              destruct (Nat.lt_ge_cases r (length (st_bns bs))) as [LT|GE].
              * rewrite app_nth1 by exact LT. apply BOK; [exact LT| exact NE1].
              * rewrite app_nth2 by exact GE. rewrite nth_repeat. apply bg_ok_nil. left. reflexivity.
            + unfold getbn. cbn [st_bns]. rewrite app_nth1 by (rewrite EL; unfold ROne, NFIX; lia). exact EONE.
            + unfold ctx_wf. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many].
              split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
              split; [rewrite length_app; cbn [length]; subst psize; unfold BN_CTX_POOL_SIZE in *; lia|].
              split; [rewrite length_app; cbn [length]; lia|].
              split. { cbn [Nat.eqb]. f_equal. rewrite <- IU, IP. subst psize. unfold BN_CTX_POOL_SIZE. rewrite Nat.sub_succ, Nat.sub_0_r. symmetry. apply div16_mul. }
              split; [eapply nondecr_last_incr; [exact CE7| lia]| exact CE8].
          -
            assert (JOIN : rw_cells bgusegs mF An (bn_cells 0 (bn_zero_pure (bn_nil 0)) ++ [CB 360 (repeat (Z_to_bv 8 0) 360)])).
            { apply bk_rw_cells_app. split; [exact BNt|]. cbn [bn_cells cells_size csize Nat.add]. change (Z.of_nat 24) with 24.
              eapply rw_cells_transport; [exact ZRX| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SEPc BAC CEIL LO SPR. lia. }
            eapply bk_rw_cells_recast; [exact JOIN| cbn [cells_wf cell_wf]; rewrite repeat_length; tauto| vm_compute; reflexivity| reflexivity].
          - apply (cx_view_some _ _ _ _ _ _ _ _ EC). subst stF. cbn [st_ctx]. split; [exact BC1|].
            split; [subst c2; cbn [gx_items]; rewrite !length_app; cbn [length]; lia|].
            split; [|split; [|split]].
            + unfold ctx_cells, cur_addr. subst c2. cbn [gx_items gx_current gx_pused gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z].
              rewrite length_app. cbn [length]. rewrite <- LHs, nth_middle, last_last. unfold MallocRep.wz.
              rewrite !Nat2Z.inj_succ. unfold Z.succ.
              replace (Z.of_nat (BN_CTX_POOL_SIZE * (length Hs + 1))) with (Z.of_nat psize + 16) by (subst psize; rewrite LHs; unfold BN_CTX_POOL_SIZE; lia).
              exact CXt.
            + apply (stack_rep_same mF OW1 IX c c2); [reflexivity| reflexivity| reflexivity|].
              eapply (stack_rep_keep st1 OW1 LB m3 mF bs PL EA ac qc IX WX); [exact HEAP3| exact PARTS1| exact EC| exact STK3'| exact MUF| exact WMF| exact HWST].
            + intros k q Hk. subst c2. cbn [gx_items] in Hk.
              destruct (Nat.lt_ge_cases k (length (gx_items c))) as [LT|GE].
              * rewrite nth_error_app1 in Hk by exact LT. rewrite app_nth1 by (rewrite LHs; exact LT). right. exact (HItems k q Hk).
              * rewrite nth_error_app2 in Hk by exact GE.
                destruct (k - length (gx_items c))%nat as [|kk] eqn:EKK; [|destruct kk; discriminate Hk].
                cbn [nth_error] in Hk. injection Hk as <-. assert (k = length Hs) as -> by lia. rewrite nth_middle. exact HinN.
            + apply links_snoc.
              * intros k H Hk HSk. eapply rw_cells_transport; [exact (PM3 k H Hk)| exact MUF| exact WMF| cbn [cells_size csize Nat.add]; exact (HWLK k H Hk HSk)].
              * intros k H Hk HSk. destruct (HR k H Hk) as (F0 & FC & FM & FX & FN & _).
                eapply rw_cells_transport; [exact (LTX k H Hk HSk)| exact MUcF| exact WMcF|]. cbn [disjoint_from cells_size csize Nat.add]. clear - F0 FC FX FN CEIL LO SPR. lia.
              * eapply rw_cells_transport; [exact LNX| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SEPc BAC CEIL LO SPR. lia. }
        unfold bn_post. do 15 eexists. exists mF, OW1, PL, errv2. split; [reflexivity|]. cbn [fst snd].
        split; [exact (seg_heap st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ HEAP3 PARTS1 FROK MUF WMF HWLX CEIL)|]. split; [exact LSF|].
        split; [apply (seg_auxv st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ B HEAP3 PARTS1 FROK AUX3 MUF WMF HWLX SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact STt|].
        split. { unfold LX_ERRNO, RATP. change (3346328 - 164) with 3346164.
                 eapply rw_cells_transport; [exact ERRX| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add].
                 clear - BAI CAI GLO LO SPR. lia. }
        split; [exact MIt|].
        split. { eapply lx_pres_trans; [exact LXP3|]. apply (seg_lx_pres st1 bs OW1 LB PL EA _ _ m3 mF _ lo _ HEAP3 PARTS1 FROK MUF WMF HWLX CEIL); unfold GLOBALS_TOP; lia. }
        split; [exact FA|]. split; [exact SO|].
        split. { eapply (refs_stable_intro _ _ _ _ [pn]); [subst stF c2; reflexivity|]. intros q H0 _ Hq. right. exact Hq. }
        split; [reflexivity|]. split; [eexists; reflexivity|]. split; [|intros q0 A0 n0 Hq0; right; exact Hq0].
        exists An. split; [|reflexivity].
        apply ref_at_pool. exists pn, An. subst stF c2. cbn [st_ctx gx_items].
        split. { rewrite IP. subst psize. unfold BN_CTX_POOL_SIZE. rewrite div16_mul. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
        split; [exact HinN|]. rewrite IP. subst psize. unfold BN_CTX_POOL_SIZE. rewrite mod16_mul. lia. }

      step. step. step. step.
      step. if_cases KH; zify_cond KH.
      +
        assert (EHS : Hs = []).
        { destruct Hs as [|h0 Hs']; [reflexivity| exfalso]. destruct (HR 0%nat h0 eq_refl) as (F0 & FC & _). cbn [hd] in KH.
          change 18446744073709551615 with (Z.ones 64) in KH. rewrite Z.land_ones, Z.mod_small in KH by lia. lia. }
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (CONTB [(bv_unsigned sp + -80, bv_unsigned sp); (ac, ac + 72); (An, An + 400)]%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx);
            [ | | | | | exact MU3| exact WM3| first [exact MI0 | eassumption]| | exact FR| exact PC| exact ERR3| exact BN0| exact ZR| | ] end.
        * intros xx Hx. cbn [outside] in *. clear - Hx. intuition lia.
        * constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith|].
          constructor; [right; left; exists (pn, An, 400); cbn; auto with zarith| constructor].
        * constructor; [apply w_stack; cbn; lia|].
          constructor; [apply w_cx; [reflexivity| intros x' Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]|].
          constructor; [|constructor].
          eapply (w_foreign OW1 LB bs PL EA (bv_unsigned sp) true [] _ pn An 400); [left; reflexivity| exact FRESHA| cbn; lia| cbn; lia].
        * constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia|]. constructor; [|constructor].
          right; right. exists pn, An, 400. split; [left; reflexivity|]. cbn [fst snd]. split; [lia|]. split; [lia|].
          intros E. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply idx_in_m. symmetry. exact E.
        * intros k H Hk HSk. rewrite EHS in HSk. cbn in HSk. lia.
        * rewrite EHS in CX |- *. cbn [hd app last] in CX |- *. exact CX.
        * first [exact B2 | rewrite EHS in B2 |- *; cbn [last] in B2 |- *; exact B2].
        * intros k H Hk HSk. rewrite EHS in Hk. destruct k; discriminate Hk.
      +
        assert (NHS : Hs <> []) by (intros E; rewrite E in KH; cbn [hd] in KH; rewrite Z.land_0_l in KH; lia).
        destruct (nth_error Hs (length Hs - 1)) as [T|] eqn:ET; [|exfalso; apply nth_error_None in ET; destruct Hs; [congruence| cbn in ET; lia]].
        assert (ELT : last Hs 0 = T) by (rewrite last_nth by exact NHS; exact (nth_error_nth _ _ _ ET)).
        destruct (HR _ _ ET) as (T0 & TC & TM & TX & TN & TK).
        assert (Hj' : (length Hs - 1 < length (gx_items c))%nat) by (rewrite <- LHs; destruct Hs; [congruence| cbn; lia]).
        destruct (nth_error (gx_items c) (length Hs - 1)) as [qT|] eqn:EqT; [|apply nth_error_None in EqT; lia].
        pose proof (HItems1 _ _ EqT) as HinT. rewrite (nth_error_nth _ _ _ ET) in HinT. change ITEM_SZ with 400 in HinT.
        assert (LNKT : rw_cells bgusegs m3 (T + 384) [C8 (Z_to_bv 64 (match (length Hs - 1)%nat with O => 0 | S k' => nth k' Hs 0 end)); C8 (Z_to_bv 64 0)]).
        { pose proof (PM3 _ _ ET) as L. rewrite (nth_overflow Hs (n := S (length Hs - 1)) 0) in L by lia. exact L. }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          lazymatch type of MU3 with munch ?W0 _ _ =>
            apply (rw_cells_transport bgusegs W0 m3 mx (T + 384)) in LNKT; [| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; lia] end end.
        apply (munch_weaken _ [(bv_unsigned sp + -80, bv_unsigned sp); (ac, ac + 72); (An, An + 400); (T + 384, T + 400)]%Z) in MU3;
          [| intros xx Hx; cbn [outside] in *; tauto].
        rewrite ELT.
        pose proof (item_align s OW LB m bs Hs _ _ HEAP LHs HItems ET) as T8.
        chk ltac:(fun C => rewrite ?land64_small in C by (clear - T0 TC; lia); clear - C T0 TC; lia).
        step. rewrite (land7_wrap _ T8).
        chk ltac:(fun C => clear - C; lia).
        step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (CONTB [(bv_unsigned sp + -80, bv_unsigned sp); (ac, ac + 72); (An, An + 400); (T + 384, T + 400)]%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx);
            [ | | | | | exact MU3| exact WM3| first [exact MI0 | eassumption]| | exact FR| exact PC| exact ERR3| exact BN0| exact ZR| | ] end.
        * intros xx Hx. cbn [outside] in *. clear - Hx. intuition lia.
        * constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith|].
          constructor; [right; left; exists (pn, An, 400); cbn; auto with zarith|].
          constructor; [right; left; exists (qT, T, 400); cbn; split; [exact HinT| lia]| constructor].
        * constructor; [apply w_stack; cbn; lia|].
          constructor; [apply w_cx; [reflexivity| intros x' Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]|].
          constructor; [eapply (w_foreign OW1 LB bs PL EA (bv_unsigned sp) true [] _ pn An 400); [left; reflexivity| exact FRESHA| cbn; lia| cbn; lia]|].
          constructor; [|constructor].
          apply w_cx; [reflexivity|]. intros x' Hx. right; left. exists qT, T. cbn in Hx. split; [eapply nth_error_In; exact EqT|]. split; [exact HinT|]. lia.
        * constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia|].
          constructor. { right; right. exists pn, An, 400. split; [left; reflexivity|]. cbn [fst snd]. split; [lia|]. split; [lia|].
                         intros E. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply idx_in_m. symmetry. exact E. }
          constructor; [|constructor].
          right; right. exists qT, T, 400. split; [apply in_or_app; left; exact HinT|]. cbn [fst snd]. split; [lia|]. split; [lia|].
          fold c. intros E. eapply (ids_item_idx_neq bs qT qT); [eapply ids_m_nodup; exact IDS| eapply nth_error_In; exact EqT| symmetry; exact E| reflexivity].
        * intros k H Hk HSk. cbn [disjoint_from]. destruct (HR k H Hk) as (F0 & FC & FM & FX & FN & FK).
          specialize (FK _ _ ET ltac:(lia)). clear - F0 FC FX FN FK CEIL LO SPR. lia.
        * replace (hd 0 (Hs ++ [An])) with (hd 0 Hs) by (destruct Hs; [congruence| reflexivity]). first [exact CX | rewrite <- ELT; exact CX | rewrite ELT in CX |- *; exact CX].
        * first [exact B2 | rewrite <- ELT; exact B2 | rewrite ELT; exact B2].
        * intros k H Hk HSk. replace k with (length Hs - 1)%nat in * by lia. rewrite ET in Hk. injection Hk as EKT. rewrite <- ?EKT. first [exact LNKT | rewrite ?EKT; exact LNKT].
  Qed.
End Proofs.
End WithCeiling0.
