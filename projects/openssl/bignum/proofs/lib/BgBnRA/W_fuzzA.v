(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2 AsByte.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgPlace.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Stdio BgWords BgArith BgMont BgExp BgTree.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXA Require HxaEceIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require FuzzKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitA BnCallA W_expandA PlaceKitA FuzzKitA W_callsA W_cmpA W_bin2bnA W_newA W_freeA W_ctx_freeA ExpKitA AFrameKit AFrameEnv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import FuzzModelA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition FUZZER_TEST_ONE : Z := 0x1f304c.
Definition LX_FUZZ_ENTRY : Z := 0x1f2fe8.
Definition BN_MOD_EXP : Z := 0x2ae9cc.
Definition BN_MOD_EXP_SIMPLE : Z := 0x2b12c0.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Ltac fix_ret :=
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Local Notation ops := (tree_ops bptr).

Definition fuzz_suffixA (p1 p2 p3 p4 p5 pc : bptr) : BM (M := btree bptr) Z :=
  bbind ops (BN_free_gA ops RB1 p1) (fun _ =>
  bbind ops (BN_free_gA ops RB2 p2) (fun _ =>
  bbind ops (BN_free_gA ops RB3 p3) (fun _ =>
  bbind ops (BN_free_gA ops RB4 p4) (fun _ =>
  bbind ops (BN_free_gA ops RB5 p5) (fun _ =>
  bbind ops (BN_CTX_free_g ops pc) (fun _ =>
  bret ops 0)))))).

Definition fuzz_bodyA (p1 p2 p3 p4 p5 pc : bptr) (n1 n2 n3 : list Z) (s1 s3 : bool) : BM (M := btree bptr) Z :=
  bbind ops (BN_bin2bn ops n1 RB1) (fun _ =>
  bbind ops (BN_set_negative ops RB1 s1) (fun _ =>
  bbind ops (BN_bin2bn ops n2 RB2) (fun _ =>
  bbind ops (BN_bin2bn ops n3 RB3) (fun _ =>
  bbind ops (BN_set_negative ops RB3 s3) (fun _ =>
  bbind ops (bget ops RB3) (fun b3 =>
  bbind ops (if is_zero_pure b3 then bret ops tt
             else bbind ops (BN_mod_exp ops RB4 RB1 RB2 RB3) (fun _ =>
                  bbind ops (BN_mod_exp_simple ops RB5 RB1 RB2 RB3) (fun _ =>
                  bbind ops (bget ops RB4) (fun b4 =>
                  bbind ops (bget ops RB5) (fun b5 =>
                  if cmp_pure b4 b5 =? 0 then bret ops tt else bunr ops)))))
        (fun _ => fuzz_suffixA p1 p2 p3 p4 p5 pc))))))).

Definition fuzz_restA (p1 p2 p3 p4 p5 pc : bptr) (data : list Z) : BM (M := btree bptr) Z :=
  let '(n1, n2, n3, s1, s3) := bg_split data in fuzz_bodyA p1 p2 p3 p4 p5 pc n1 n2 n3 s1 s3.

Lemma fuzz_one_gA_eq : forall (d : list Z),
  fuzz_one_gA ops d =
  bbind ops (BN_new ops RB1) (fun p1 => bbind ops (BN_new ops RB2) (fun p2 => bbind ops (BN_new ops RB3) (fun p3 =>
  bbind ops (BN_new ops RB4) (fun p4 => bbind ops (BN_new ops RB5) (fun p5 => bbind ops (BN_CTX_new ops) (fun pc =>
  fuzz_restA p1 p2 p3 p4 p5 pc d)))))).
Proof. intros d. unfold fuzz_one_gA, fuzz_restA, fuzz_bodyA, fuzz_suffixA. destruct (bg_split d) as [[[[n1 n2] n3] s1] s3]. reflexivity. Qed.

Lemma bg_split_cons3 : forall k0 k1 k2 (buf : list Z), 0 <= k0 < 256 -> 0 <= k1 < 256 -> 0 <= k2 < 256 ->
  let len := zlength buf in
  let l1 := ((len * k0) / 255) mod 512 in
  let q2 := ((len - l1) * k1) / 255 in
  let l2 := q2 mod 512 in
  let l3 := (len - l1 - q2) mod 512 in
  bg_split (k0 :: k1 :: k2 :: buf)
  = (firstn (Z.to_nat l1) buf, firstn (Z.to_nat l2) (skipn (Z.to_nat l1) buf), firstn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf),
     Z.testbit k2 0, Z.testbit k2 2).
Proof.
  intros k0 k1 k2 buf R0 R1 R2. cbv zeta. unfold bg_split. cbn [length nth skipn Nat.ltb Nat.leb].
  rewrite (Z.mod_small k0 256 R0), (Z.mod_small k1 256 R1), (Z.mod_small k2 256 R2).
  replace (Z.of_nat (S (S (S (length buf)))) - 3) with (zlength buf) by (unfold zlength; lia).
  rewrite (Z.mul_comm k0 (zlength buf)).
  set (l1 := (zlength buf * k0 / 255) mod 512). rewrite (Z.mul_comm k1 (zlength buf - l1)).
  set (q2 := (zlength buf - l1) * k1 / 255).
  replace ((zlength buf - l1 - q2 mod 512) mod 512) with ((zlength buf - l1 - q2) mod 512) by (rewrite Zminus_mod_idemp_r; reflexivity).
  reflexivity.
Qed.

Lemma split_parts : forall (buf : list Z) l1 l2 l3, 0 <= l1 -> 0 <= l2 -> 0 <= l3 -> l1 + l2 + l3 <= zlength buf ->
  let n1 := firstn (Z.to_nat l1) buf in
  let n2 := firstn (Z.to_nat l2) (skipn (Z.to_nat l1) buf) in
  let n3 := firstn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf) in
  zlength n1 = l1 /\ zlength n2 = l2 /\ zlength n3 = l3 /\ exists rest, buf = n1 ++ n2 ++ n3 ++ rest.
Proof.
  intros buf l1 l2 l3 H1 H2 H3 HL. cbv zeta. unfold zlength in *.
  split; [rewrite firstn_length_le by lia; lia|].
  split; [rewrite firstn_length_le by (rewrite length_skipn; lia); lia|].
  split; [rewrite firstn_length_le by (rewrite length_skipn; lia); lia|].
  exists (skipn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf)).
  rewrite (firstn_skipn (Z.to_nat l3)).
  replace (skipn (Z.to_nat (l1 + l2)) buf) with (skipn (Z.to_nat l2) (skipn (Z.to_nat l1) buf)) by (rewrite skipn_skipn; f_equal; lia).
  rewrite (firstn_skipn (Z.to_nat l2)). rewrite (firstn_skipn (Z.to_nat l1)). reflexivity.
Qed.

Definition MAGIC255_BYTES : list byte := Eval vm_compute in (cells_bytes [C8 (Z_to_bv 64 9259542123273814145)]).
Lemma magic255_cellsA : forall mx, mem_inv bgasegs mx -> ro_cells bgasegs mx 0x103f8 [C8 (wz 9259542123273814145)].
Proof.
  intros mx MI. pose proof (ro_cells_image bgasegs mx 0x103f8 MAGIC255_BYTES MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.
  eapply ro_cells_recast; [exact H| cbn; tauto| vm_compute; reflexivity].
Qed.

Definition payload_okA (m : mem) (LB : list block) (D : Z) (d : list Z) : Prop :=
  bytes_at bgasegs m D (to_bytes d) /\ Forall byte_ok d
  /\ 0 < D /\ zlength d < 2^30
  /\ (d = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b).

Definition FUZZ_CALLEE_MAX : Z := 0x18000.
Definition FUZZ_STACK_A : Z := 112 + FUZZ_CALLEE_MAX.

Section Proofs.

  Variables (EXP_STACK EXP_COST SIMPLE_STACK SIMPLE_COST : Z) (EXP_DEPTH SIMPLE_DEPTH : nat).
  Hypothesis STK_EXP : 0 <= EXP_STACK <= FUZZ_CALLEE_MAX.
  Hypothesis STK_SIMPLE : 0 <= SIMPLE_STACK <= FUZZ_CALLEE_MAX.
  Hypothesis COST_EXP : 0 <= EXP_COST.
  Hypothesis COST_SIMPLE : 0 <= SIMPLE_COST.

  Hypothesis FR_NIL : @ar_FR AR = [].
  Hypothesis DEPTH_EXP : (EXP_DEPTH <= 4)%nat.
  Hypothesis DEPTH_SIMPLE : (SIMPLE_DEPTH <= 4)%nat.
  Hypothesis BN_mod_exp_walkA : exp_stmtA_f BN_MOD_EXP EXP_STACK EXP_COST EXP_DEPTH (BN_mod_exp ops) None.
  Hypothesis BN_mod_exp_simple_walkA : exp_stmtA BN_MOD_EXP_SIMPLE SIMPLE_STACK SIMPLE_COST SIMPLE_DEPTH (BN_mod_exp_simple ops) None.
  Hypothesis ERR_clear_error_cpsA_h : HxaEceIface.ERR_clear_error_cpsA_stmt HxaEceIface.ECE_STACK HxaEceIface.ECE_COST.

  Definition FUZZ_TOTAL : Z := 9 * MC + EXP_COST + SIMPLE_COST + HxaEceIface.ECE_COST.

  Section Env.

    Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
    Variables (m : mem) (Σ : rts RT) (OW LB : list block) (EA : BnRepDefs.err_addrs) (lo : Z).
    Notation SP := (bv_unsigned sp).
    Notation FB := (bv_unsigned sp + -112).

    Notation PREC := [C8 (Z_to_bv 64 SHB); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
    Notation CENV PL ls0 OW0 := (cenvA LB PL lo SP FB s0 ra None FUZZ_TOTAL Σ ls0 OW0 m PREC).
    Notation QPOST := (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st_init OW LB lo m pl_empty EA FUZZ_TOTAL
                                (fun (rc : Z) (_ : bstate bptr) (_ : list block) (_ : placement) (a0' : word) => rc = 0 /\ a0' = wz 0)).
    Hypothesis LOS : lo <= SP - FUZZ_STACK_A.

    Hypothesis CNT80 : cnt_bal st_init OW + Z.of_nat (length LB) + 80 <= LIVE_MAX.

    Lemma cnt_ok_d : forall (lsx : bstate bptr) OWx d, cnt_bal lsx OWx = cnt_bal st_init OW + d -> d <= 7 -> cnt_ok lsx OWx LB.
    Proof. intros lsx OWx d E Hd. unfold cnt_ok. rewrite E. clear - CNT80 Hd. lia. Qed.

    Lemma free_callA : forall (Q : Z * bstate bptr -> rts RT -> machine_state -> Prop) (K : BM (M := btree bptr) Z)
        (PL : placement) (ls0 : bstate bptr) (OW0 : list block) used Σx (lsx : bstate bptr) (mx : mem) (OWx : list block) (r : bnref) (a : Z) (q : bptr) (d : Z)
        (rax t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      hpl_only PL -> CENV PL ls0 OW0 used Σx lsx mx OWx -> lib_state lsx mx OWx PL EA -> pl_bn PL r = Some (PHeap a q 0) ->
      cnt_bal lsx OWx = cnt_bal st_init OW + d -> d <= 7 -> used <= FUZZ_TOTAL ->
      fp_stop FB (bv_unsigned x8) -> uk_ctx BN_FREE [bv_unsigned rax] ->
      (forall Σ' m' OW' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F' fc',
          let ls' := setbn r (bn_nil 0) lsx in
          CENV (pl_set PL r None) ls' OW' (used + 0) Σ' ls' m' OW' -> lib_state ls' m' OW' (pl_set PL r None) EA ->
          cnt_bal ls' OW' = cnt_bal st_init OW + (d - 1) ->
          implA (K ls') Σ' Q
            (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                F' (ret_pc rax) fc' None m' (seg_rom bgasegs))) ->
      implA (bbind ops (BN_free_gA ops r q) (fun _ => K) lsx) Σx Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 (wz a) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz BN_FREE) fc None mx (seg_rom bgasegs)).
    Proof.
      intros until fc. intros HPL ENV LS E CB Hd HU FPS CTX K1.
      pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP) as ESP.
      pose proof LOS as LOS'. unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX in LOS'.
      unfold bbind at 1. cbn [bind tree_ops]. unfold BN_free_gA.
      destruct (bn_flags (getbn r lsx) =? BN_FLG_MALLOCED) eqn:EF; [| cbn [bunr unreachable tree_ops tbind]; apply implA_unr].
      apply Z.eqb_eq in EF.
      assert (PRE1 : bn_preA Σx lsx mx OWx LB PL EA (Z_to_bv 64 FB) lo BN_FREE_STACK 0).
      { eapply cenv_preA; [exact ENV | exact LS | unfold BN_FREE_STACK, BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK; clear - LOS'; lia | clear - HU; lia]. }
      eapply implA_bind.
      { eapply (BN_free_walkA) with (r := r) (a := a) (q := q) (ras := []); [exact PRE1 | rewrite ESP; exact FPS | exact CTX | reflexivity | exact E | exact EF | reflexivity]. }
      cbv beta. intros [u ls'] Σ' ms' PO. unfold bn_postA_p in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & HEAP2 & LS2 & ST2 & MI2 & AXP2 & CRED2 & (-> & EBS & CB2)).
      cbn [fst snd] in *. subst ls'. rewrite ESP in *.
      eapply K1; [| exact LS2 | rewrite CB2, CB; clear; lia].
      eapply (cenv_rebaseA LB PL (pl_set PL r None)); [exact ENV | exact HEAP2 | exact ST2 | exact MI2 | exact AXP2 | exact CRED2 | apply hpl_only_set_none; exact HPL |].
      eapply (cnt_ok_d _ _ (d - 1)); [rewrite CB2, CB; clear; lia | clear - Hd; lia].
    Qed.

    Lemma fuzz_doneA : forall (PL : placement) (ls0 : bstate bptr) (OW0 : list block) used ΣE (lsE : bstate bptr) (mE : mem) (OWE : list block)
        (p1 p2 p3 p4 p5 pc : bptr) (a1 a2 a3 a4 a5 ac : Z)
        (x1 t0 t1 t2 a0 b1 b2 b3 b4 b5 b6 b7 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      hpl_only PL ->
      pl_bn PL RB1 = Some (PHeap a1 p1 0) -> pl_bn PL RB2 = Some (PHeap a2 p2 0) -> pl_bn PL RB3 = Some (PHeap a3 p3 0) ->
      pl_bn PL RB4 = Some (PHeap a4 p4 0) -> pl_bn PL RB5 = Some (PHeap a5 p5 0) -> pl_ctx PL = Some (ac, pc) ->
      CENV PL ls0 OW0 used ΣE lsE mE OWE -> lib_state lsE mE OWE PL EA ->
      cnt_bal lsE OWE = cnt_bal st_init OW + 6 -> used + HxaEceIface.ECE_COST <= FUZZ_TOTAL ->
      implA (fuzz_suffixA p1 p2 p3 p4 p5 pc lsE) ΣE QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 (wz a1) (wz a2) a0 b1 b2 b3 b4 b5 b6 b7
                 (wz a3) (wz a4) (wz a5) (wz ac) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f31f4) fc None mE (seg_rom bgasegs)).
    Proof.
      intros until fc. intros HPL E1 E2 E3 E4 E5 EC ENV LS CB HU.
      pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP) as ESP.
      pose proof LOS as LOS'. unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX in LOS'.
      pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
      assert (ECE0 : 0 <= HxaEceIface.ECE_COST) by (unfold HxaEceIface.ECE_COST; clear; lia).

      pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
      pose proof (pl_wf_stored PL RB1 _ PWF E1) as SR1. pose proof SR1 as (RN1 & _).
      assert (EO1 : pl_of PL RB1 = Some (PHeap a1 p1 0)) by (rewrite pl_of_stored by exact SR1; exact E1).
      destruct (proj1 PLB RB1 _ RN1 EO1) as (n1 & Hin1 & _ & Hn1). replace (a1 - 0) with a1 in Hin1 by (clear; lia). unfold BN_STRUCT_SZ in Hn1.
      pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin1) as (A10 & _ & _ & A1C & _).
      assert (EA1 : bv_unsigned (Z_to_bv 64 a1) = a1) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - A10 A1C Hn1 C1 C2 C3; lia).
      assert (A1LO : a1 <= lo) by (clear - A1C Hn1 CEIL; lia).
      assert (FPS : fp_stop FB (bv_unsigned (Z_to_bv 64 a1))) by (left; rewrite EA1; clear - A1LO LOFB; lia).
      clear PARTS WFS PWF IDS PLB ERRB SR1 RN1 EO1 Hin1.
      unfold fuzz_suffixA, MallocRep.wz.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (free_callA QPOST _ PL ls0 OW0 used ΣE lsE mE OWE RB1 a1 p1 6); [exact HPL | exact ENV | exact LS | exact E1 | exact CB | clear; lia | clear - HU ECE0; lia | exact FPS
        | rewrite unsigned_lit by (clear; lia); exact R_BN_free_1f3014 |].
      intros Σ1 m1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F1 fc1 ls1 ENV1 LS1 CB1. clear ENV LS CB HEAP.
      set (PL1 := pl_set PL RB1 None) in *. pose proof (hpl_only_set_none PL RB1 HPL) as HPL1. fold PL1 in HPL1. fix_ret.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (free_callA QPOST _ PL1 ls1 OW1 (used + 0) Σ1 ls1 m1 OW1 RB2 a2 p2 (6 - 1)); [exact HPL1 | exact ENV1 | exact LS1 | exact E2 | exact CB1 | clear; lia | clear - HU ECE0; lia | exact FPS
        | rewrite unsigned_lit by (clear; lia); exact R_BN_free_1f301c |].
      intros Σ2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ls2 ENV2 LS2 CB2. clear ENV1 LS1 CB1.
      set (PL2 := pl_set PL1 RB2 None) in *. pose proof (hpl_only_set_none PL1 RB2 HPL1) as HPL2. fold PL2 in HPL2. fix_ret.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (free_callA QPOST _ PL2 ls2 OW2 (used + 0 + 0) Σ2 ls2 m2 OW2 RB3 a3 p3 (6 - 1 - 1)); [exact HPL2 | exact ENV2 | exact LS2 | exact E3 | exact CB2 | clear; lia | clear - HU ECE0; lia | exact FPS
        | rewrite unsigned_lit by (clear; lia); exact R_BN_free_1f3024 |].
      intros Σ3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ls3 ENV3 LS3 CB3. clear ENV2 LS2 CB2.
      set (PL3 := pl_set PL2 RB3 None) in *. pose proof (hpl_only_set_none PL2 RB3 HPL2) as HPL3. fold PL3 in HPL3. fix_ret.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (free_callA QPOST _ PL3 ls3 OW3 (used + 0 + 0 + 0) Σ3 ls3 m3 OW3 RB4 a4 p4 (6 - 1 - 1 - 1)); [exact HPL3 | exact ENV3 | exact LS3 | exact E4 | exact CB3 | clear; lia | clear - HU ECE0; lia | exact FPS
        | rewrite unsigned_lit by (clear; lia); exact R_BN_free_1f302c |].
      intros Σ4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F4 fc4 ls4 ENV4 LS4 CB4. clear ENV3 LS3 CB3.
      set (PL4 := pl_set PL3 RB4 None) in *. pose proof (hpl_only_set_none PL3 RB4 HPL3) as HPL4. fold PL4 in HPL4. fix_ret.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (free_callA QPOST _ PL4 ls4 OW4 (used + 0 + 0 + 0 + 0) Σ4 ls4 m4 OW4 RB5 a5 p5 (6 - 1 - 1 - 1 - 1)); [exact HPL4 | exact ENV4 | exact LS4 | exact E5 | exact CB4 | clear; lia | clear - HU ECE0; lia | exact FPS
        | rewrite unsigned_lit by (clear; lia); exact R_BN_free_1f3034 |].
      intros Σ5 m5 OW5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F5 fc5 ls5 ENV5 LS5 CB5. clear ENV4 LS4 CB4.
      set (PL5 := pl_set PL4 RB5 None) in *. pose proof (hpl_only_set_none PL4 RB5 HPL4) as HPL5. fold PL5 in HPL5. fix_ret.

      set (U5 := used + 0 + 0 + 0 + 0 + 0) in *. assert (EU5 : U5 = used) by (unfold U5; clear; lia).
      apply implA_from_evt. step. step. apply evt_done.
      assert (PRE5 : bn_preA Σ5 ls5 m5 OW5 LB PL5 EA (Z_to_bv 64 FB) lo BN_CTX_FREE_STACK 0).
      { eapply cenv_preA; [exact ENV5 | exact LS5
          | unfold BN_CTX_FREE_STACK, BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK; clear - LOS'; lia | clear - HU ECE0 EU5; lia]. }
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implA_bind.
      { eapply (BN_CTX_free_walkA) with (ac := ac) (qc := pc) (ras := []);
          [exact PRE5 | rewrite ESP; exact FPS | rewrite unsigned_lit by (clear; lia); exact R_BN_CTX_free_1f303c | reflexivity | exact EC | reflexivity]. }
      cbv beta. intros [u ls6] Σ6 ms6 PO. unfold bn_postA_p in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & PL6' & -> & HEAP6 & LS6 & ST6 & MI6 & AXP6 & CRED6 & (-> & EBS6 & CB6)).
      cbn [fst snd] in *. rewrite ESP in *. fix_ret.
      set (PL6 := pl_set_ctx PL5 None) in *.
      assert (HPL6 : hpl_only PL6) by exact HPL5.
      assert (CBE : cnt_bal ls6 OW6 = cnt_bal st_init OW + 0) by (rewrite CB6, CB5; clear; lia).
      assert (ENV6 : CENV PL6 ls6 OW6 (U5 + 0) Σ6 ls6 m6 OW6).
      { eapply (cenv_rebaseA LB PL5 PL6); [exact ENV5 | exact HEAP6 | exact ST6 | exact MI6 | exact AXP6 | exact CRED6 | exact HPL6 |].
        eapply (cnt_ok_d _ _ 0); [exact CBE | clear; lia]. }
      clear ENV5 LS5 PRE5 ST6 MI6 AXP6 CRED6 CB5 CB6.

      unfold bret. cbn [ret tree_ops].
      pose proof ENV6 as (OK6 & _ & ST6 & MI6 & _).
      pose proof LS6 as (CS6 & EI6 & _).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS6) as PARTS6. pose proof PARTS6 as (_ & _ & _ & _ & (_ & _ & _ & EB4)).
      pose proof (AH_range _ _ _ _ _ _ _ HEAP6 EB4) as (E0 & _ & _ & ECc & EI').
      pose proof OK6 as (_ & _ & _ & _ & _ & _ & _ & _ & FROK6 & _).
      pose proof ERR_clear_error_cpsA_h as ECEH. unfold HxaEceIface.ERR_clear_error_cpsA_stmt in ECEH.
      apply implA_from_evt. step. apply evt_done.
      eapply implA_step.
      { eapply ECEH with (lo := lo) (OW := OW6) (LB := LB) (EA := EA);
          [exact HEAP6 | rewrite ESP; exact ST6 | exact CEIL | rewrite ESP; unfold HxaEceIface.ECE_STACK; clear - LOS'; lia | rewrite ESP; clear - SPT; lia | rewrite ESP; exact FB16 | exact MI6
          | reflexivity | reflexivity | left; rewrite EA1; exact A1LO | exact CS6 | exact EI6 | clear - HU EU5 ENV6 CRED0; destruct ENV6 as (_ & _ & _ & _ & _ & CR & _); lia]. }
      intros Σ7 ms7 PO. unfold HxaEceIface.ece_postA in PO.
      destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F7 & fc7 & m7 & -> & HEAP7 & MI7 & ST7 & AG7 & ES7 & CR7).
      rewrite ESP in *. fix_ret.
      assert (LS7 : lib_state ls6 m7 OW6 PL6 EA).
      { eapply (lib_state_err_clearedA Σ6 LB ls6 m6 m7 OW6 PL6 EA FB SP USTACK_TOP); [exact HEAP6 | exact LS6 | exact FROK6 | clear - FBSP; lia | clear; lia | exact AG7 | exact ES7]. }
      assert (ENV7 : CENV PL6 ls6 OW6 (U5 + 0 + HxaEceIface.ECE_COST) Σ7 ls6 m7 OW6).
      { eapply (cenv_rebaseA LB PL6 PL6); [exact ENV6 | exact HEAP7 | exact ST7 | exact MI7 | | exact CR7 | exact HPL6 | eapply (cnt_ok_d _ _ 0); [exact CBE | clear; lia]].
        eapply (ax_pres_of_icall Σ6 OW6 LB m6 m7 FB _ (BnRepDefs.ea_ES EA) 904 (BnRepDefs.ea_pe EA, BnRepDefs.ea_ES EA, 904) HEAP6 EB4);
          [cbn; clear; lia | cbn; clear; lia | clear - CEIL LOFB; lia | exact AG7]. }
      pose proof ENV7 as (_ & G1 & ST8 & G3 & G4 & G5 & _ & _ & FR8 & _ & _).
      clear ENV6 LS6 HEAP6 ST6 MI6 AG7.
      cbn [app] in FR8.
      pose proof (munch_refl [(FB, bv_unsigned sp)]%Z m7) as MUe. pose proof (wmono_refl bgasegs m7) as WMe.
      apply implA_ret_evt.
      step. do 13 step.
      release_frame FR8 ST8 (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_postA. do 17 eexists. exists m7, OW6, PL6. split; [reflexivity|]. cbn [fst snd].
      split; [exact G1|]. split; [exact LS7|]. split; [exact ST8|]. split; [exact G3|].
      split; [rewrite <- (xw_hpl_only pl_empty PL6 hpl_only_empty HPL6); exact G4|].
      split; [clear - G5 HU EU5; lia|].
      split; [unfold cnt_eq; rewrite CBE; clear; lia|].
      split; [apply refs_stable_noitems; reflexivity|]. split; reflexivity.
    Qed.

    Lemma bytes_clientA : forall PL (ls0 : bstate bptr) OW0 used Σx (lsx : bstate bptr) mx OWx A bs,
      hpl_only PL -> CENV PL ls0 OW0 used Σx lsx mx OWx -> bytes_at bgasegs m A bs ->
      (bs = [] \/ exists b, In b LB /\ blk_addr b <= A /\ A + Z.of_nat (length bs) <= blk_addr b + blk_size b) ->
      bytes_at bgasegs mx A bs.
    Proof.
      intros PL ls0 OW0 used Σx lsx mx OWx A bs HPL (OK & HEAP & _ & _ & AXP & _) BY [->|(b & Hb & Hb1 & Hb2)].
      - destruct BY as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
      - eapply bytes_at_agree; [exact AXP | exact BY |].
        intros a Ha.
        pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (B0 & _ & _ & BC & BI).
        pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
        split; [| right; right; exists b; split; [exact Hb| clear - Ha Hb1 Hb2; lia]].
        unfold XW. unfold hpl_only in HPL. rewrite HPL, app_nil_r.
        unfold LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold BnHeapA.ACEIL in *. clear - Ha Hb1 Hb2 B0 BC BI C1. lia.
    Qed.

    Lemma b2b_callA : forall (Q : Z * bstate bptr -> rts RT -> machine_state -> Prop) (K : BM (M := btree bptr) Z)
        (PL : placement) (ls0 : bstate bptr) (OW0 : list block) used Σx (lsx : bstate bptr) (mx : mem) (OWx : list block) (r : bnref) (a : Z) (q : bptr) (P : Z) (n : list Z)
        (rax t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      hpl_only PL -> CENV PL ls0 OW0 used Σx lsx mx OWx -> lib_state lsx mx OWx PL EA -> pl_bn PL r = Some (PHeap a q 0) ->
      bytes_at bgasegs m P (to_bytes n) -> Forall byte_ok n -> 0 < P -> Z.of_nat (length n) < 2^31 ->
      (n = [] \/ exists bk, In bk LB /\ blk_addr bk <= P /\ P + Z.of_nat (length n) <= blk_addr bk + blk_size bk) ->
      (n <> [] -> 1 < P) ->
      used + MC <= FUZZ_TOTAL -> fp_stop FB (bv_unsigned x8) -> uk_ctx BN_BIN2BN [bv_unsigned rax] ->
      (forall Σ' (ls' : bstate bptr) m' OW' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F' fc',
          CENV PL ls0 OW0 (used + MC) Σ' ls' m' OW' -> lib_state ls' m' OW' PL EA ->
          implA (K ls') Σ' Q
            (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 (wz a) y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                F' (ret_pc rax) fc' None m' (seg_rom bgasegs))) ->
      implA (bbind ops (BN_bin2bn ops n r) (fun _ => K) lsx) Σx Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 (wz P) (wz (Z.of_nat (length n))) (wz a) a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz BN_BIN2BN) fc None mx (seg_rom bgasegs)).
    Proof.
      intros until fc. intros HPL ENV LS E BY FR P0 LEN HBK HP1 HU FPS CTX K1.
      pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP) as ESP.
      pose proof LOS as LOS'. unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX in LOS'.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
      pose proof (pl_wf_stored PL r _ PWF E) as SR.
      assert (EO : pl_of PL r = Some (PHeap a q 0)) by (rewrite pl_of_stored by exact SR; exact E).
      assert (HA : ref_at lsx OWx PL r a) by (apply ref_at_fixed; [exact (proj1 SR)|]; exists (PHeap a q 0); split; [exact EO| reflexivity]).
      assert (PRE1 : bn_preA Σx lsx mx OWx LB PL EA (Z_to_bv 64 FB) lo BN_BIN2BN_STACK MC).
      { eapply cenv_preA; [exact ENV | exact LS
          | unfold BN_BIN2BN_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, CRYPTO_FREE_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK; clear - LOS'; lia | exact HU]. }
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implA_bind.
      { eapply (BN_bin2bn_walkA) with (r := r) (a := a) (SRC := P) (bs := n) (ras := []);
          [exact PRE1 | rewrite ESP; exact FPS | exact CTX | reflexivity | exact HA | exact (wref_heap PL r a q 0 EO)
          | eapply (bytes_clientA PL); [exact HPL | exact ENV | exact BY | unfold to_bytes; rewrite length_map; clear - HBK; destruct HBK as [->|HBK']; [left; reflexivity| right; exact HBK']]
          | exact FR | exact LEN | exact P0 | exact HBK | reflexivity | reflexivity | reflexivity]. }
      cbv beta. intros [u ls'] Σ' ms' PO.
      apply (bn_postA_cpost LB PL EA lo SP FB FUZZ_TOTAL Σ ls0 OW0) in PO; [| exact OK | exact HEAP].
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (-> & -> & _)).
      specialize (CP eq_refl).
      assert (EL : CENV PL ls0 OW0 (used + MC) Σ' ls' m2 OW2 /\ lib_state ls' m2 OW2 PL EA) by (eapply cenv_postA; [exact ENV | exact CP]).
      destruct EL as (ENV' & LS').
      cbn [fst snd] in *. eapply K1; [exact ENV'| exact LS'].
    Qed.

    Lemma fuzz_mainA : forall (PL : placement) (ls0 : bstate bptr) (OW0 : list block) used Σ6 (ls6 : bstate bptr) (m6 : mem) (OW6 : list block)
        (p1 p2 p3 p4 p5 pc : bptr) (a1 a2 a3 a4 a5 ac : Z) (P : Z) (n1 n2 n3 : list Z) (s1v s3v : Z)
        (x1 t0 t1 t2 a0 b1 b2 b3 b4 b5 b6 b7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      hpl_only PL ->
      pl_bn PL RB1 = Some (PHeap a1 p1 0) -> pl_bn PL RB2 = Some (PHeap a2 p2 0) -> pl_bn PL RB3 = Some (PHeap a3 p3 0) ->
      pl_bn PL RB4 = Some (PHeap a4 p4 0) -> pl_bn PL RB5 = Some (PHeap a5 p5 0) -> pl_ctx PL = Some (ac, pc) -> pl_fresh PL ->
      CENV PL ls0 OW0 used Σ6 ls6 m6 OW6 -> lib_state ls6 m6 OW6 PL EA ->
      cnt_bal ls0 OW0 = cnt_bal st_init OW + 6 -> used + 3 * MC + EXP_COST + SIMPLE_COST + HxaEceIface.ECE_COST <= FUZZ_TOTAL ->
      bytes_at bgasegs m P (to_bytes n1) -> bytes_at bgasegs m (P + zlength n1) (to_bytes n2) -> bytes_at bgasegs m (P + zlength n1 + zlength n2) (to_bytes n3) ->
      Forall byte_ok n1 -> Forall byte_ok n2 -> Forall byte_ok n3 ->
      0 < P -> P + zlength n1 + zlength n2 + zlength n3 < 2^63 -> zlength n1 < 2^31 -> zlength n2 < 2^31 -> zlength n3 < 2^31 ->
      (n1 = [] \/ exists b, In b LB /\ blk_addr b <= P /\ P + zlength n1 <= blk_addr b + blk_size b) ->
      (n2 = [] \/ exists b, In b LB /\ blk_addr b <= P + zlength n1 /\ P + zlength n1 + zlength n2 <= blk_addr b + blk_size b) ->
      (n3 = [] \/ exists b, In b LB /\ blk_addr b <= P + zlength n1 + zlength n2 /\ P + zlength n1 + zlength n2 + zlength n3 <= blk_addr b + blk_size b) ->
      ((n1 = [] /\ n2 = [] /\ n3 = []) \/ 1 < P) ->
      0 <= s1v < 2^64 -> 0 <= s3v < 2^64 ->
      implA (fuzz_bodyA p1 p2 p3 p4 p5 pc n1 n2 n3 (negb (s1v =? 0)) (negb (s3v =? 0)) ls6) Σ6 QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 (wz a1) (wz a2) a0 b1 b2 b3 b4 b5 b6 b7
                 (wz a3) (wz a4) (wz a5) (wz ac) (wz P) (wz s3v) (wz (zlength n3)) (wz (zlength n2)) (wz (zlength n1)) (wz s1v) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f3190) fc None m6 (seg_rom bgasegs)).
    Proof.
      intros until fc. intros HPL E1 E2 E3 E4 E5 EC FRESH ENV LS CB0 HU BY1 BY2 BY3 FR1 FR2 FR3 P0 PH L1 L2 L3 K1 K2 K3 HP1 S1R S3R.
      pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP) as ESP.
      pose proof LOS as LOS'. unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX in LOS'.
      pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
      assert (ECE0 : 0 <= HxaEceIface.ECE_COST) by (unfold HxaEceIface.ECE_COST; clear; lia).
      assert (MC0 : 0 <= MC) by (unfold MC; clear; lia).
      assert (LOFB16 : lo <= FB - 16) by (clear - LOS'; lia).
      assert (ZL1 : 0 <= zlength n1) by (unfold zlength; clear; lia). assert (ZL2 : 0 <= zlength n2) by (unfold zlength; clear; lia). assert (ZL3 : 0 <= zlength n3) by (unfold zlength; clear; lia).

      pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
      pose proof (pl_wf_stored PL RB1 _ PWF E1) as SR1. pose proof (pl_wf_stored PL RB2 _ PWF E2) as SR2. pose proof (pl_wf_stored PL RB3 _ PWF E3) as SR3.
      pose proof (pl_wf_stored PL RB4 _ PWF E4) as SR4. pose proof (pl_wf_stored PL RB5 _ PWF E5) as SR5.
      assert (EO1 : pl_of PL RB1 = Some (PHeap a1 p1 0)) by (rewrite pl_of_stored by exact SR1; exact E1).
      assert (EO2 : pl_of PL RB2 = Some (PHeap a2 p2 0)) by (rewrite pl_of_stored by exact SR2; exact E2).
      assert (EO3 : pl_of PL RB3 = Some (PHeap a3 p3 0)) by (rewrite pl_of_stored by exact SR3; exact E3).
      assert (EO4 : pl_of PL RB4 = Some (PHeap a4 p4 0)) by (rewrite pl_of_stored by exact SR4; exact E4).
      assert (EO5 : pl_of PL RB5 = Some (PHeap a5 p5 0)) by (rewrite pl_of_stored by exact SR5; exact E5).
      assert (HA1 : forall bs OWx, ref_at bs OWx PL RB1 a1) by (intros; apply ref_at_fixed; [exact (proj1 SR1)|]; exists (PHeap a1 p1 0); split; [exact EO1| reflexivity]).
      assert (HA2 : forall bs OWx, ref_at bs OWx PL RB2 a2) by (intros; apply ref_at_fixed; [exact (proj1 SR2)|]; exists (PHeap a2 p2 0); split; [exact EO2| reflexivity]).
      assert (HA3 : forall bs OWx, ref_at bs OWx PL RB3 a3) by (intros; apply ref_at_fixed; [exact (proj1 SR3)|]; exists (PHeap a3 p3 0); split; [exact EO3| reflexivity]).
      assert (HA4 : forall bs OWx, ref_at bs OWx PL RB4 a4) by (intros; apply ref_at_fixed; [exact (proj1 SR4)|]; exists (PHeap a4 p4 0); split; [exact EO4| reflexivity]).
      assert (HA5 : forall bs OWx, ref_at bs OWx PL RB5 a5) by (intros; apply ref_at_fixed; [exact (proj1 SR5)|]; exists (PHeap a5 p5 0); split; [exact EO5| reflexivity]).
      destruct (proj1 PLB RB1 _ (proj1 SR1) EO1) as (sz1 & Hin1 & _ & Hn1). replace (a1 - 0) with a1 in Hin1 by (clear; lia). unfold BN_STRUCT_SZ in Hn1.
      pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin1) as (A10 & _ & _ & A1C & _).
      assert (EA1 : bv_unsigned (Z_to_bv 64 a1) = a1) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - A10 A1C Hn1 C1 C2 C3; lia).
      assert (A1LO : a1 <= lo) by (clear - A1C Hn1 CEIL; lia).
      assert (FPS : fp_stop FB (bv_unsigned (Z_to_bv 64 a1))) by (left; rewrite EA1; clear - A1LO LOFB; lia).
      clear PARTS WFS IDS PLB ERRB Hin1 HEAP.
      pose proof (set_neg_callA LB PL EA lo SP FB s0 ra None FUZZ_TOTAL Σ ls0 OW0 m LOFB16) as SNC.
      pose proof (is_zero_callA LB PL EA lo SP FB s0 ra None FUZZ_TOTAL Σ ls0 OW0 m LOFB16) as IZC.
      unfold fuzz_bodyA, MallocRep.wz.

      apply implA_from_evt. do 3 step. step. apply evt_done.
      eapply (b2b_callA QPOST _ PL ls0 OW0 used Σ6 ls6 m6 OW6 RB1 a1 p1 P n1);
        [exact HPL | exact ENV | exact LS | exact E1 | exact BY1 | exact FR1 | exact P0 | exact L1 | exact K1
        | intros NE1; clear - HP1 NE1; destruct HP1 as [(HE & _)|HE]; [contradiction | exact HE] | clear - HU MC0 COST_EXP COST_SIMPLE ECE0; lia | exact FPS
        | rewrite unsigned_lit by (clear; lia); exact R_BN_bin2bn_1f2fb8 |].
      intros Σ7 ls7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F7 fc7 ENV7 LS7. clear ENV LS. fix_ret.

      unfold BN_set_negative at 1. unfold bbind at 1 2. unfold bget at 1. unfold bset at 1. cbn [bind ret tree_ops tbind fst snd].
      apply implA_from_evt.
      step. if_cases KE; zify_cond KE; [exfalso; apply KE; reflexivity|]. clear KE.
      do 3 step.
      eapply SNC; [exact ENV7 | exact LS7 | exact (HA1 ls7 OW7) | exact (wref_heap PL RB1 a1 p1 0 EO1) |].
      rewrite (unsigned_lit s1v) by (clear - S1R; lia).
      intros m8 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ls8 ENV8 LS8. clear ENV7 LS7.
      fix_ret.

      do 4 zstep. zstep. apply evt_done.
      eapply (b2b_callA QPOST _ PL ls0 OW0 (used + MC) Σ7 ls8 m8 OW7 RB2 a2 p2 (P + zlength n1) n2);
        [exact HPL | exact ENV8 | exact LS8 | exact E2 | exact BY2 | exact FR2 | clear - P0 ZL1; lia | exact L2 | exact K2
        | intros NE2; clear - HP1 NE2 ZL1; destruct HP1 as [(_ & HE & _)|HE]; [contradiction | lia] | clear - HU MC0 COST_EXP COST_SIMPLE ECE0; lia | exact FPS
        | rewrite unsigned_lit by (clear; lia); exact R_BN_bin2bn_1f2fdc |].
      intros Σ9 ls9 m9 OW9 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F9 fc9 ENV9 LS9. clear ENV8 LS8. fix_ret.

      apply implA_from_evt.
      zstep. if_cases KE; zify_cond KE; [exfalso; apply KE; reflexivity|]. clear KE.
      do 3 zstep. zstep. apply evt_done.
      eapply (b2b_callA QPOST _ PL ls0 OW0 (used + MC + MC) Σ9 ls9 m9 OW9 RB3 a3 p3 (P + zlength n1 + zlength n2) n3);
        [exact HPL | exact ENV9 | exact LS9 | exact E3 | exact BY3 | exact FR3 | clear - P0 ZL1 ZL2; lia | exact L3 | exact K3
        | intros NE3; clear - HP1 NE3 ZL1 ZL2; destruct HP1 as [(_ & _ & HE)|HE]; [contradiction | lia] | clear - HU MC0 COST_EXP COST_SIMPLE ECE0; lia | exact FPS
        | rewrite unsigned_lit by (clear; lia); exact R_BN_bin2bn_1f2ff0 |].
      intros Σ10 ls10 m10 OW10 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F10 fc10 ENV10 LS10. clear ENV9 LS9. fix_ret.

      unfold BN_set_negative at 1. unfold bbind at 1 2. unfold bget at 1. unfold bset at 1. cbn [bind ret tree_ops tbind fst snd].
      apply implA_from_evt.
      zstep. if_cases KE; zify_cond KE; [exfalso; apply KE; reflexivity|]. clear KE.
      do 3 zstep.
      eapply SNC; [exact ENV10 | exact LS10 | exact (HA3 ls10 OW10) | exact (wref_heap PL RB3 a3 p3 0 EO3) |].
      rewrite (unsigned_lit s3v) by (clear - S3R; lia).
      intros m11 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ls11 ENV11 LS11. clear ENV10 LS10.
      fix_ret.

      do 2 zstep.
      eapply IZC; [exact ENV11 | exact LS11 | exact (HA3 ls11 OW10) | exact (proj1 (proj2 SR3)) |].
      intros m12 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV12 LS12. clear ENV11 LS11.
      fix_ret.
      apply evt_done.
      unfold bbind at 1. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd]. fold ls11. unfold is_zero_pure.
      assert (CB12 : cnt_bal ls11 OW10 = cnt_bal st_init OW + 6).
      { destruct ENV12 as (_ & _ & _ & _ & _ & _ & CNT12 & _). unfold cnt_eq in CNT12. rewrite CNT12. exact CB0. }
      destruct (bn_top (getbn RB3 ls11) =? 0)%nat eqn:EZ; cbn [Z.b2z].
      {
        unfold bbind at 1. unfold bret at 1. cbn [bind ret tree_ops tbind fst snd].
        apply implA_from_evt.
        zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ; discriminate KZ|]. clear KZ.
        apply evt_done.
        eapply (fuzz_doneA PL ls0 OW0 (used + MC + MC + MC) Σ10 ls11 m12 OW10 p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac);
          [exact HPL | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact EC | exact ENV12 | exact LS12 | exact CB12 | clear - HU MC0 COST_EXP COST_SIMPLE ECE0; lia]. }

      apply implA_from_evt.
      zstep. if_cases KZ; zify_cond KZ; [|exfalso; apply KZ; reflexivity]. clear KZ.
      do 5 zstep. zstep. apply evt_done.
      assert (PRE12 : bn_preA Σ10 ls11 m12 OW10 LB PL EA (Z_to_bv 64 FB) lo EXP_STACK EXP_COST).
      { eapply cenv_preA; [exact ENV12 | exact LS12 | clear - STK_EXP LOS'; unfold FUZZ_CALLEE_MAX in STK_EXP; lia | clear - HU MC0 COST_EXP COST_SIMPLE ECE0; lia]. }
      assert (ROOM12 : fr_room EXP_DEPTH ls11 OW10 LB).
      { apply fr_room_intro; [exact FR_NIL | unfold FRAMES_MAX; clear - DEPTH_EXP; lia | rewrite CB12; clear - CNT80 DEPTH_EXP; lia]. }
      pose proof BN_mod_exp_walkA as EXPH. unfold exp_stmtA_f in EXPH.
      unfold bbind at 1 2. cbn [bind tree_ops]. apply implA_assoc.
      eapply implA_bind.
      { eapply EXPH with (rr := RB4) (ra_ := RB1) (rp := RB2) (rm := RB3) (arr := a4) (ara := a1) (arp := a2) (arm := a3) (ac := ac) (qc := pc) (ras := []);
          [exact PRE12 | exact ROOM12 | rewrite ESP; exact FPS | rewrite unsigned_lit by (clear; lia); exact R_BN_mod_exp_1f3098 | reflexivity | exact (HA4 _ _) | exact (HA1 _ _) | exact (HA2 _ _) | exact (HA3 _ _)
          | exact (hpl_heap PL RB4 a4 p4 0 EO4) | discriminate | discriminate | discriminate | exact EC | exact FRESH
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros w Hw; discriminate Hw]. }
      cbv beta. intros [u ls13] Σ13 ms13 PO.
      pose proof ENV12 as (_ & HEAP12 & _).
      apply (bn_postA_cpost LB PL EA lo SP FB FUZZ_TOTAL Σ ls0 OW0) in PO; [| exact OK | exact HEAP12].
      destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F13 & fc13 & m13 & OW13 & PL13 & -> & CP & (-> & ->)).
      specialize (CP eq_refl).
      assert (EL : CENV PL ls0 OW0 (used + MC + MC + MC + EXP_COST) Σ13 ls13 m13 OW13 /\ lib_state ls13 m13 OW13 PL EA) by (eapply cenv_postA; [exact ENV12 | exact CP]).
      destruct EL as (ENV13 & LS13). cbn [fst snd] in *. clear ENV12 LS12 PRE12 HEAP12 CP. fix_ret.

      apply implA_from_evt.
      zstep. if_cases KE; zify_cond KE; [exfalso; clear - KE; discriminate KE|]. clear KE.
      do 5 zstep. zstep. apply evt_done.
      assert (PRE13 : bn_preA Σ13 ls13 m13 OW13 LB PL EA (Z_to_bv 64 FB) lo SIMPLE_STACK SIMPLE_COST).
      { eapply cenv_preA; [exact ENV13 | exact LS13 | clear - STK_SIMPLE LOS'; unfold FUZZ_CALLEE_MAX in STK_SIMPLE; lia | clear - HU MC0 COST_EXP COST_SIMPLE ECE0; lia]. }
      assert (CB13 : cnt_bal ls13 OW13 = cnt_bal st_init OW + 6).
      { destruct ENV13 as (_ & _ & _ & _ & _ & _ & CNT13 & _). unfold cnt_eq in CNT13. rewrite CNT13. exact CB0. }
      assert (ROOM13 : fr_room SIMPLE_DEPTH ls13 OW13 LB).
      { apply fr_room_intro; [exact FR_NIL | unfold FRAMES_MAX; clear - DEPTH_SIMPLE; lia | rewrite CB13; clear - CNT80 DEPTH_SIMPLE; lia]. }
      pose proof BN_mod_exp_simple_walkA as SIMH. unfold exp_stmtA in SIMH.
      unfold bbind at 1 2. cbn [bind tree_ops]. apply implA_assoc.
      eapply implA_bind.
      { eapply SIMH with (rr := RB5) (ra_ := RB1) (rp := RB2) (rm := RB3) (arr := a5) (ara := a1) (arp := a2) (arm := a3) (ac := ac) (qc := pc) (ras := []);
          [exact PRE13 | exact ROOM13 | rewrite ESP; exact FPS | rewrite unsigned_lit by (clear; lia); exact R_BN_mod_exp_simple_1f30b4 | reflexivity | exact (HA5 _ _) | exact (HA1 _ _) | exact (HA2 _ _) | exact (HA3 _ _)
          | exact (hpl_heap PL RB5 a5 p5 0 EO5) | discriminate | discriminate | discriminate | exact EC
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros w Hw; discriminate Hw]. }
      cbv beta. intros [u' ls14] Σ14 ms14 PO.
      pose proof ENV13 as (_ & HEAP13 & _).
      apply (bn_postA_cpost LB PL EA lo SP FB FUZZ_TOTAL Σ ls0 OW0) in PO; [| exact OK | exact HEAP13].
      destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & F14 & fc14 & m14 & OW14 & PL14 & -> & CP & (-> & ->)).
      specialize (CP eq_refl).
      assert (EL : CENV PL ls0 OW0 (used + MC + MC + MC + EXP_COST + SIMPLE_COST) Σ14 ls14 m14 OW14 /\ lib_state ls14 m14 OW14 PL EA) by (eapply cenv_postA; [exact ENV13 | exact CP]).
      destruct EL as (ENV14 & LS14). cbn [fst snd] in *. clear ENV13 LS13 PRE13 HEAP13 CP. fix_ret.

      unfold bbind, bget. cbn [bind ret tree_ops tbind fst snd].
      apply implA_from_evt.
      zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ; discriminate KZ|]. clear KZ.
      do 2 zstep.
      assert (PRE14 : bn_preA Σ14 ls14 m14 OW14 LB PL EA (Z_to_bv 64 FB) lo BN_CMP_STACK 0).
      { eapply cenv_preA; [exact ENV14 | exact LS14 | unfold BN_CMP_STACK; clear - LOS'; lia | clear - HU MC0 COST_EXP COST_SIMPLE ECE0; lia]. }
      zstep.
      eapply evt_cut.
      { eapply BN_cmp_evtA with (r1 := RB4) (r2 := RB5) (a := a4) (b := a5);
          [exact PRE14 | reflexivity | exact (HA4 _ _) | exact (HA5 _ _) | exact (proj1 (proj2 SR4)) | exact (proj1 (proj2 SR5)) | reflexivity | reflexivity]. }
      intros ms15 PO.
      pose proof ENV14 as (_ & HEAP14 & _).
      apply (bn_postA_cpost LB PL EA lo SP FB FUZZ_TOTAL Σ ls0 OW0) in PO; [| exact OK | exact HEAP14].
      destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & F15 & fc15 & m15 & OW15 & PL15 & -> & CP15 & (-> & -> & CR & _ & ->)).
      specialize (CP15 eq_refl).
      assert (EL : CENV PL ls0 OW0 (used + MC + MC + MC + EXP_COST + SIMPLE_COST + 0) Σ14 ls14 m15 OW14 /\ lib_state ls14 m15 OW14 PL EA) by (eapply cenv_postA; [exact ENV14 | exact CP15]).
      destruct EL as (ENV15 & LS15). cbn [fst snd] in *. clear ENV14 LS14 PRE14 HEAP14 CP15. fix_ret.
      apply evt_done.
      assert (CB15 : cnt_bal ls14 OW14 = cnt_bal st_init OW + 6).
      { destruct ENV15 as (_ & _ & _ & _ & _ & _ & CNT15 & _). unfold cnt_eq in CNT15. rewrite CNT15. exact CB0. }
      destruct (cmp_pure (getbn RB4 ls14) (getbn RB5 ls14) =? 0) eqn:EC0.
      2:{
        unfold bunr. cbn [unreachable tree_ops tbind]. apply implA_unr. }
      apply Z.eqb_eq in EC0. rewrite EC0. unfold bret. cbn [ret tree_ops tbind fst snd].
      apply implA_from_evt.
      zstep. if_cases KZ; zify_cond KZ; [|exfalso; apply KZ; reflexivity]. clear KZ.
      apply evt_done.
      eapply (fuzz_doneA PL ls0 OW0 (used + MC + MC + MC + EXP_COST + SIMPLE_COST + 0) Σ14 ls14 m15 OW14 p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac);
        [exact HPL | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact EC | exact ENV15 | exact LS15 | exact CB15 | clear - HU MC0 COST_EXP COST_SIMPLE ECE0; lia].
    Qed.

    Lemma new_callA : forall (Q : Z * bstate bptr -> rts RT -> machine_state -> Prop) (K : bptr -> BM (M := btree bptr) Z)
        (PL : placement) (ls0 : bstate bptr) (OW0 : list block) used Σx (lsx : bstate bptr) (mx : mem) (OWx : list block) (r : bnref) (d : Z)
        (rax t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      hpl_only PL -> CENV PL ls0 OW0 used Σx lsx mx OWx -> lib_state lsx mx OWx PL EA -> stored_ref r -> pl_bn PL r = None ->
      cnt_bal lsx OWx = cnt_bal st_init OW + d -> length (blocks_of (setbn r (bn_nil BN_FLG_MALLOCED) lsx)) = length (blocks_of lsx) ->
      d + 1 <= 7 -> used + MC <= FUZZ_TOTAL ->
      fp_stop FB (bv_unsigned x8) -> uk_ctx BN_NEW [bv_unsigned rax] ->
      (forall (p : bptr) (a : Z) Σ' m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F' fc',
          let ls' := setbn r (bn_nil BN_FLG_MALLOCED) lsx in
          0 < a < 2^63 ->
          CENV (pl_set PL r (Some (PHeap a p 0))) ls' ((p, a, 24) :: OWx) (used + MC) Σ' ls' m' ((p, a, 24) :: OWx) ->
          lib_state ls' m' ((p, a, 24) :: OWx) (pl_set PL r (Some (PHeap a p 0))) EA ->
          cnt_bal ls' ((p, a, 24) :: OWx) = cnt_bal st_init OW + (d + 1) ->
          implA (K p ls') Σ' Q
            (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 (wz a) y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                F' (ret_pc rax) fc' None m' (seg_rom bgasegs))) ->
      implA (bbind ops (BN_new ops r) K lsx) Σx Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz BN_NEW) fc None mx (seg_rom bgasegs)).
    Proof.
      intros until fc. intros HPL ENV LS SR E CB EBL Hd HU FPS CTX K1.
      pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP) as ESP.
      pose proof LOS as LOS'. unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX in LOS'.
      assert (PRE1 : bn_preA Σx lsx mx OWx LB PL EA (Z_to_bv 64 FB) lo BN_NEW_STACK MC).
      { eapply cenv_preA; [exact ENV | exact LS | unfold BN_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LOS'; lia | exact HU]. }
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implA_bind.
      { eapply (BN_new_walkA) with (r := r) (ras := []); [exact PRE1 | rewrite ESP; exact FPS | exact CTX | reflexivity | exact SR | exact E]. }
      cbv beta. intros [p ls'] Σ' ms' PO. unfold bn_postA_p in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & HEAP2 & LS2 & ST2 & MI2 & AXP2 & CRED2
                      & (a & -> & -> & RA & -> & EBS)).
      cbn [fst snd] in *. subst ls'. rewrite ESP in *.
      assert (CB2 : cnt_bal (setbn r (bn_nil BN_FLG_MALLOCED) lsx) ((p, a, 24) :: OWx) = cnt_bal st_init OW + (d + 1)).
      { unfold cnt_bal in *. cbn [length]. rewrite EBL. clear - CB. lia. }
      eapply K1; [exact RA | | exact LS2 | exact CB2].
      eapply (cenv_rebaseA LB PL (pl_set PL r (Some (PHeap a p 0)))); [exact ENV | exact HEAP2 | exact ST2 | exact MI2 | exact AXP2 | exact CRED2 | apply hpl_only_set_heap; exact HPL |].
      eapply (cnt_ok_d _ _ (d + 1)); [exact CB2 | clear - Hd; lia].
    Qed.

    Lemma ctx_new_callA : forall (Q : Z * bstate bptr -> rts RT -> machine_state -> Prop) (K : bptr -> BM (M := btree bptr) Z)
        (PL : placement) (ls0 : bstate bptr) (OW0 : list block) used Σx (lsx : bstate bptr) (mx : mem) (OWx : list block) (d : Z)
        (rax t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      hpl_only PL -> CENV PL ls0 OW0 used Σx lsx mx OWx -> lib_state lsx mx OWx PL EA -> pl_ctx PL = None ->
      cnt_bal lsx OWx = cnt_bal st_init OW + d -> length (blocks_of (set_ctx gx_nil lsx)) = length (blocks_of lsx) ->
      d + 1 <= 7 -> used + MC <= FUZZ_TOTAL ->
      fp_stop FB (bv_unsigned x8) -> uk_ctx BN_CTX_NEW [bv_unsigned rax] ->
      (forall (p : bptr) (a : Z) Σ' m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F' fc',
          let ls' := set_ctx gx_nil lsx in
          0 < a < 2^63 ->
          CENV (pl_set_ctx PL (Some (a, p))) ls' ((p, a, 72) :: OWx) (used + MC) Σ' ls' m' ((p, a, 72) :: OWx) ->
          lib_state ls' m' ((p, a, 72) :: OWx) (pl_set_ctx PL (Some (a, p))) EA ->
          cnt_bal ls' ((p, a, 72) :: OWx) = cnt_bal st_init OW + (d + 1) ->
          implA (K p ls') Σ' Q
            (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 (wz a) y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                F' (ret_pc rax) fc' None m' (seg_rom bgasegs))) ->
      implA (bbind ops (BN_CTX_new ops) K lsx) Σx Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (wz BN_CTX_NEW) fc None mx (seg_rom bgasegs)).
    Proof.
      intros until fc. intros HPL ENV LS E CB EBL Hd HU FPS CTX K1.
      pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP) as ESP.
      pose proof LOS as LOS'. unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX in LOS'.
      assert (PRE1 : bn_preA Σx lsx mx OWx LB PL EA (Z_to_bv 64 FB) lo BN_CTX_NEW_STACK MC).
      { eapply cenv_preA; [exact ENV | exact LS | unfold BN_CTX_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LOS'; lia | exact HU]. }
      unfold bbind at 1. cbn [bind tree_ops].
      eapply implA_bind.
      { eapply (BN_CTX_new_walkA) with (ras := []); [exact PRE1 | rewrite ESP; exact FPS | exact CTX | reflexivity | exact E]. }
      cbv beta. intros [p ls'] Σ' ms' PO. unfold bn_postA_p in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & HEAP2 & LS2 & ST2 & MI2 & AXP2 & CRED2
                      & (a & -> & -> & RA & -> & EBS)).
      cbn [fst snd] in *. subst ls'. rewrite ESP in *.
      assert (CB2 : cnt_bal (set_ctx gx_nil lsx) ((p, a, 72) :: OWx) = cnt_bal st_init OW + (d + 1)).
      { unfold cnt_bal in *. cbn [length]. rewrite EBL. clear - CB. lia. }
      eapply K1; [exact RA | | exact LS2 | exact CB2].
      eapply (cenv_rebaseA LB PL (pl_set_ctx PL (Some (a, p)))); [exact ENV | exact HEAP2 | exact ST2 | exact MI2 | exact AXP2 | exact CRED2 | apply hpl_only_set_ctx; exact HPL |].
      eapply (cnt_ok_d _ _ (d + 1)); [exact CB2 | clear - Hd; lia].
    Qed.

    Lemma fuzz_splitA : forall (PL : placement) (ls0 : bstate bptr) (OW0 : list block) used Σ6 (ls6 : bstate bptr) (m6 : mem) (OW6 : list block)
        (p1 p2 p3 p4 p5 pc : bptr) (a1 a2 a3 a4 a5 ac : Z) (D : Z) (d : list Z)
        (x1 t0 t1 t2 a0 b1 b2 b3 b4 b5 b6 b7 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      hpl_only PL ->
      pl_bn PL RB1 = Some (PHeap a1 p1 0) -> pl_bn PL RB2 = Some (PHeap a2 p2 0) -> pl_bn PL RB3 = Some (PHeap a3 p3 0) ->
      pl_bn PL RB4 = Some (PHeap a4 p4 0) -> pl_bn PL RB5 = Some (PHeap a5 p5 0) -> pl_ctx PL = Some (ac, pc) -> pl_fresh PL ->
      CENV PL ls0 OW0 used Σ6 ls6 m6 OW6 -> lib_state ls6 m6 OW6 PL EA ->
      cnt_bal ls0 OW0 = cnt_bal st_init OW + 6 -> used + 3 * MC + EXP_COST + SIMPLE_COST + HxaEceIface.ECE_COST <= FUZZ_TOTAL ->
      payload_okA m LB D d -> D <= lo ->
      implA (fuzz_restA p1 p2 p3 p4 p5 pc d ls6) Σ6 QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 (wz a1) (wz a2) a0 b1 b2 b3 b4 b5 b6 b7
                 (wz a3) (wz a4) (wz a5) (wz ac) (wz D) (wz (zlength d)) x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f30e4) fc None m6 (seg_rom bgasegs)).
    Proof.
      intros until fc. intros HPL E1 E2 E3 E4 E5 EC FRESH ENV LS CB0 HU (PLB & PLF & PLD & PLN & PLK) DLO.
      pose proof ENV as (OK & HEAP & ST6 & MI6 & _ & _ & _ & _ & FR6 & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP) as ESP.
      pose proof LOS as LOS'. unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX in LOS'.
      pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3.
      assert (ZL0 : 0 <= zlength d) by (unfold zlength; clear; lia).
      pose proof (magic255_cellsA m6 MI6) as MAGIC. unfold MallocRep.wz in MAGIC.
      assert (PLB6 : bytes_at bgasegs m6 D (to_bytes d)).
      { eapply (bytes_clientA PL); [exact HPL | exact ENV | exact PLB |]. unfold to_bytes. rewrite length_map.
        destruct PLK as [->|PLK']; [left; reflexivity| right; unfold zlength in PLK'; exact PLK']. }
      assert (D47 : D + zlength d < 140737488355328).
      { destruct PLK as [->|(bb & Hbb & Hbb1 & Hbb2)].
        - unfold zlength; cbn [length]. unfold BnHeapA.ACEIL in *. unfold USTACK_TOP in SPT. clear - DLO LOFB FBSP SPT CL1 CL2 CL3. lia.
        - pose proof (AH_range_gen _ _ _ _ bb HEAP ltac:(apply in_or_app; right; exact Hbb)) as (_ & _ & _ & BC & _).
          unfold BnHeapA.ACEIL in *. clear - Hbb2 BC CL1 CL2 CL3. lia. }
      cbn [app] in FR6.
      unfold MallocRep.wz.
      apply implA_from_evt.
      step. step. if_cases K3; rewrite ?unsigned_lit in K3 by (clear - ZL0 PLN; lia); zify_cond K3.
      {
        assert (ES : bg_split d = ([], [], [], false, false)).
        { unfold bg_split. replace (2 <? length d)%nat with false by (symmetry; apply Nat.ltb_ge; unfold zlength in K3; clear - K3; lia). reflexivity. }
        do 5 step.
        apply evt_done. unfold fuzz_restA. rewrite ES.
        assert (BE0 : forall A, 0 <= A <= 2^64 -> bytes_at bgasegs m A (to_bytes [])).
        { intros A HA. split; [clear - HA; lia|]. split; [cbn [to_bytes map length]; clear - HA; lia|]. intros i Hi. cbn in Hi. clear - Hi. lia. }
        eapply (fuzz_mainA PL ls0 OW0 used Σ6 ls6 m6 OW6 p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac D [] [] [] 0 0);
          [exact HPL | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact EC | exact FRESH | exact ENV | exact LS | exact CB0 | exact HU
          | apply BE0; clear - PLD D47 ZL0; lia | apply BE0; unfold zlength; cbn [length]; clear - PLD D47 ZL0; lia | apply BE0; unfold zlength; cbn [length]; clear - PLD D47 ZL0; lia
          | constructor | constructor | constructor | exact PLD
          | unfold zlength; cbn [length]; clear - D47 ZL0; lia | reflexivity | reflexivity | reflexivity
          | left; reflexivity | left; reflexivity | left; reflexivity | left; repeat split; reflexivity | clear; lia | clear; lia]. }

      destruct d as [|k0 [|k1 [|k2 buf]]]; try (exfalso; unfold zlength in K3; cbn [length] in K3; clear - K3; lia).
      assert (R0 : 0 <= k0 < 256) by (inversion PLF; assumption).
      assert (R1 : 0 <= k1 < 256) by (inversion PLF as [|? ? _ H]; inversion H; assumption).
      assert (R2 : 0 <= k2 < 256) by (inversion PLF as [|? ? _ H]; inversion H as [|? ? _ H']; inversion H'; assumption).
      assert (ZLB : zlength (k0 :: k1 :: k2 :: buf) = zlength buf + 3) by (unfold zlength; cbn [length]; clear; lia).
      assert (ZB0 : 0 <= zlength buf) by (unfold zlength; clear; lia).
      assert (PLKs : exists b, In b LB /\ blk_addr b <= D /\ D + (zlength buf + 3) <= blk_addr b + blk_size b)
        by (destruct PLK as [E|H]; [discriminate E| rewrite ZLB in H; exact H]).
      destruct PLKs as (bb & Hbb & Hbb1 & Hbb2).
      assert (HDR : ro_cells bgasegs m6 D [C1 (Z_to_bv 8 k0); C1 (Z_to_bv 8 k1); C1 (Z_to_bv 8 k2)]).
      { change (to_bytes (k0 :: k1 :: k2 :: buf)) with ([Z_to_bv 8 k0; Z_to_bv 8 k1; Z_to_bv 8 k2] ++ to_bytes buf) in PLB6.
        apply bytes_at_app in PLB6. destruct PLB6 as [H3 _]. split; [cbn; auto| exact H3]. }
      assert (EB : forall k, 0 <= k < 256 -> bv_unsigned (Z_to_bv 8 k) = k) by (intros k Hk; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_small; lia).
      rewrite ZLB in PLN, D47.
      set (len := zlength buf) in *.
      assert (ACCD : acc bgasegs m6 D (len + 3)).
      { exact (AH_acc_in _ _ _ _ bb D (len + 3) HEAP ltac:(apply in_or_app; right; exact Hbb) Hbb1 Hbb2). }
      pose proof (munch_refl (@nil (Z * Z)) m6) as MU.
      rewrite ZLB.
      lazymatch goal with |- evt _ ?P _ => set (POST := P) end.

      assert (J3 : forall w10 w13 w14 : word, evt bgasegs POST
                (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 a1) (Z_to_bv 64 a2)
                         w10 (Z_to_bv 64 k0) (Z_to_bv 64 k1) w13 w14 b5 b6 b7 (Z_to_bv 64 a3) (Z_to_bv 64 a4) (Z_to_bv 64 a5) (Z_to_bv 64 ac)
                         (Z_to_bv 64 D) (Z_to_bv 64 (len + 3)) x24 x25 x26 x27 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1f3130) fc None m6 (seg_rom bgasegs))).
      { intros w10 w13 w14.
        set (l1 := ((len * k0) / 255) mod 512). set (q2 := ((len - l1) * k1) / 255). set (l2 := q2 mod 512). set (l3 := (len - l1 - q2) mod 512).
        assert (LEN30 : 0 <= len < 2^30) by (clear - ZB0 PLN; lia).
        assert (X40 : 0 <= len * k0 < 2^40) by (clear - LEN30 R0; change (2^40) with 1099511627776; change (2^30) with 1073741824 in LEN30; nia).
        pose proof (FuzzKit.div255_le len k0 ZB0 R0) as Q1R.
        assert (L1R : 0 <= l1 <= len) by (unfold l1; pose proof (Z.mod_pos_bound (len * k0 / 255) 512 ltac:(clear; lia)); pose proof (Z.mod_le (len * k0 / 255) 512 ltac:(clear - Q1R; lia) ltac:(clear; lia)); clear - H H0 Q1R; lia).
        assert (Y30 : 0 <= len - l1 < 2^30) by (clear - L1R LEN30; lia).
        pose proof (FuzzKit.div255_le (len - l1) k1 ltac:(clear - L1R; lia) R1) as Q2R. fold q2 in Q2R.
        assert (L2R : 0 <= l2 <= q2) by (unfold l2; pose proof (Z.mod_pos_bound q2 512 ltac:(clear; lia)); pose proof (Z.mod_le q2 512 ltac:(clear - Q2R; lia) ltac:(clear; lia)); clear - H H0; lia).
        assert (L3R : 0 <= l3 <= len - l1 - q2) by (unfold l3; pose proof (Z.mod_pos_bound (len - l1 - q2) 512 ltac:(clear; lia)); pose proof (Z.mod_le (len - l1 - q2) 512 ltac:(clear - Q2R; lia) ltac:(clear; lia)); clear - H H0; lia).
        destruct (FuzzKit.byte_bits k2 R2) as [TB0 TB2]. destruct (FuzzKit.byte_masks k2 R2) as [MK1 MK4].
        do 4 zstep. cbv beta. rewrite (EB k2 R2).
        do 4 zstep.
        setreg 26%Z (Z_to_bv 64 l1) ltac:(f_equal; symmetry; first [apply (FuzzKit.split_l1_m (len * k0) X40) | apply (FuzzKit.split_l1_m' (len * k0) X40)]).
        do 11 zstep.
        replace (len + - l1) with (len - l1) by (clear; lia).
        assert (YK : 0 <= (len - l1) * k1 < 2^64) by (clear - Y30 R1; change (2^64) with 18446744073709551616; change (2^30) with 1073741824 in Y30; nia).
        rewrite (FuzzKit.land_ones64_id ((len - l1) * k1) YK).
        rewrite (FuzzKit.split_q2_m' (len - l1) k1 Y30 R1). fold q2.
        replace (len - l1 + - q2) with (len - l1 - q2) by (clear; lia).
        rewrite (FuzzKit.land_ones64_id (len - l1 - q2)) by (clear - Q2R Y30; change (2^64) with 18446744073709551616; change (2^30) with 1073741824 in Y30; lia).
        rewrite (FuzzKit.land511_mod (len - l1 - q2)) by (clear - Q2R; lia). fold l3.
        rewrite (FuzzKit.land511_mod q2) by (clear - Q2R; lia). fold l2.

        pose proof (bg_split_cons3 k0 k1 k2 buf R0 R1 R2) as ES. cbv zeta in ES. fold len l1 q2 l2 l3 in ES.
        destruct (split_parts buf l1 l2 l3 ltac:(clear - L1R; lia) ltac:(clear - L2R; lia) ltac:(clear - L3R; lia) ltac:(fold len; clear - L1R L2R L3R; lia))
          as (ZN1 & ZN2 & ZN3 & rest & EBUF).
        set (n1 := firstn (Z.to_nat l1) buf) in *. set (n2 := firstn (Z.to_nat l2) (skipn (Z.to_nat l1) buf)) in *.
        set (n3 := firstn (Z.to_nat l3) (skipn (Z.to_nat (l1 + l2)) buf)) in *.
        assert (PLBs : bytes_at bgasegs m (D + 3) (to_bytes n1) /\ bytes_at bgasegs m (D + 3 + zlength n1) (to_bytes n2)
                       /\ bytes_at bgasegs m (D + 3 + zlength n1 + zlength n2) (to_bytes n3)).
        { change (to_bytes (k0 :: k1 :: k2 :: buf)) with ([Z_to_bv 8 k0; Z_to_bv 8 k1; Z_to_bv 8 k2] ++ to_bytes buf) in PLB.
          apply bytes_at_app in PLB. destruct PLB as [_ PLB]. cbn [length] in PLB. change (Z.of_nat 3) with 3 in PLB.
          rewrite EBUF in PLB. unfold to_bytes in PLB. rewrite !map_app in PLB.
          apply bytes_at_app in PLB. destruct PLB as [P1 PLB]. apply bytes_at_app in PLB. destruct PLB as [P2 PLB].
          apply bytes_at_app in PLB. destruct PLB as [P3 _]. rewrite !length_map in *. unfold zlength.
          split; [exact P1|]. split; [exact P2| exact P3]. }
        destruct PLBs as (P1 & P2 & P3).
        assert (PLFs : Forall byte_ok n1 /\ Forall byte_ok n2 /\ Forall byte_ok n3).
        { assert (FB0 : Forall byte_ok buf) by (inversion PLF as [|? ? _ H]; inversion H as [|? ? _ H']; inversion H'; assumption).
          rewrite EBUF in FB0. apply Forall_app in FB0. destruct FB0 as [F1 FB0]. apply Forall_app in FB0. destruct FB0 as [F2 FB0].
          apply Forall_app in FB0. destruct FB0 as [F3 _]. auto. }
        destruct PLFs as (F1 & F2 & F3).
        apply evt_done. unfold POST. unfold fuzz_restA. rewrite ES. fold n1 n2 n3.
        rewrite <- TB0, <- TB2. rewrite <- ZN1, <- ZN2, <- ZN3.
        eapply (fuzz_mainA PL ls0 OW0 used Σ6 ls6 m6 OW6 p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac (D + 3) n1 n2 n3 (Z.land k2 1) (Z.land k2 4));
          [exact HPL | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact EC | exact FRESH | exact ENV | exact LS | exact CB0 | exact HU
          | exact P1 | exact P2 | exact P3 | exact F1 | exact F2 | exact F3 | clear - PLD; lia
          | rewrite ZN1, ZN2, ZN3; clear - D47 L1R L2R L3R Q2R; lia | rewrite ZN1; clear - L1R LEN30; change (2^31) with 2147483648; change (2^30) with 1073741824 in LEN30; lia
          | rewrite ZN2; clear - L2R Q2R L1R LEN30; change (2^31) with 2147483648; change (2^30) with 1073741824 in LEN30; lia
          | rewrite ZN3; clear - L3R Q2R L1R LEN30; change (2^31) with 2147483648; change (2^30) with 1073741824 in LEN30; lia
          | right; exists bb; split; [exact Hbb|]; rewrite ZN1; clear - Hbb1 Hbb2 L1R L2R L3R Q2R; lia
          | right; exists bb; split; [exact Hbb|]; rewrite ZN1, ZN2; clear - Hbb1 Hbb2 L1R L2R L3R Q2R; lia
          | right; exists bb; split; [exact Hbb|]; rewrite ZN1, ZN2, ZN3; clear - Hbb1 Hbb2 L1R L2R L3R Q2R; lia
          | right; clear - PLD; lia
          | clear - MK1; change (2^64) with 18446744073709551616; lia | clear - MK4; change (2^64) with 18446744073709551616; lia]. }
      assert (D0 : 0 < D) by exact PLD.

      assert (J2 : forall w10 w12 w13 : word, evt bgasegs POST
                (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 a1) (Z_to_bv 64 a2)
                         w10 (Z_to_bv 64 k0) w12 w13 (Z_to_bv 64 SHB) b5 b6 b7 (Z_to_bv 64 a3) (Z_to_bv 64 a4) (Z_to_bv 64 a5) (Z_to_bv 64 ac)
                         (Z_to_bv 64 D) (Z_to_bv 64 (len + 3)) x24 x25 x26 x27 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1f3118) fc None m6 (seg_rom bgasegs))).
      { intros w10 w12 w13.
        do 3 step. shl1 sb3 OK3.
        step. rewrite (zxb_small k1) by (clear - R1; lia).
        destruct (sh_ok_cases sb3 (D + 2) OK3) as [-> | (kk & KK1 & KK2 & EK1 & EK2)].
        - step. rewrite sxb_z8. if_false. apply J3.
        - rewrite EK1. step. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by (clear - KK1; lia); [|exfalso; clear - KS KK1; lia]. clear KS.
          step. rewrite ?(unsigned_lit (D + 2)) by (clear - D0 D47 ZB0; lia). rewrite (land7_mod8 (D + 2)) by (clear - D0; lia).
          step. if_cases KB; zify_cond KB.
          + apply J3.
          + exfalso. rewrite ?signed_small in KB by (pose proof (Z.mod_pos_bound (D + 2) 8 ltac:(clear; lia)) as MB; clear - MB KK1; lia). clear - KB KK2. lia. }

      assert (J1 : forall w10 w11 : word, evt bgasegs POST
                (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 a1) (Z_to_bv 64 a2)
                         w10 w11 b2 b3 (Z_to_bv 64 SHB) b5 b6 b7 (Z_to_bv 64 a3) (Z_to_bv 64 a4) (Z_to_bv 64 a5) (Z_to_bv 64 ac)
                         (Z_to_bv 64 D) (Z_to_bv 64 (len + 3)) x24 x25 x26 x27 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1f3100) fc None m6 (seg_rom bgasegs))).
      { intros w10 w11.
        do 3 step. shl1 sb2 OK2.
        step. rewrite (zxb_small k0) by (clear - R0; lia).
        destruct (sh_ok_cases sb2 (D + 1) OK2) as [-> | (kk & KK1 & KK2 & EK1 & EK2)].
        - step. rewrite sxb_z8. if_false. apply J2.
        - rewrite EK1. step. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by (clear - KK1; lia); [|exfalso; clear - KS KK1; lia]. clear KS.
          step. rewrite ?(unsigned_lit (D + 1)) by (clear - D0 D47 ZB0; lia). rewrite (land7_mod8 (D + 1)) by (clear - D0; lia).
          step. if_cases KB; zify_cond KB.
          + apply J2.
          + exfalso. rewrite ?signed_small in KB by (pose proof (Z.mod_pos_bound (D + 1) 8 ltac:(clear; lia)) as MB; clear - MB KK1; lia). clear - KB KK2. lia. }

      do 3 step. shl1 sb1 OK1.
      destruct (sh_ok_cases sb1 D OK1) as [-> | (kk & KK1 & KK2 & EK1 & EK2)].
      - step. rewrite sxb_z8. if_false. apply J1.
      - rewrite EK1. step. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by (clear - KK1; lia); [|exfalso; clear - KS KK1; lia]. clear KS.
        step. rewrite ?(unsigned_lit D) by (clear - D0 D47 ZB0; lia). rewrite (land7_mod8 D) by (clear - D0; lia).
        step. if_cases KB; zify_cond KB.
        + apply J1.
        + exfalso. rewrite ?signed_small in KB by (pose proof (Z.mod_pos_bound D 8 ltac:(clear; lia)) as MB; clear - MB KK1; lia). clear - KB KK2. lia.
    Qed.

    Lemma fuzz_createA : forall (m0 : mem) (D : Z) (d : list Z)
        (x1 t0 t1 t2 x9 a0 b1 b2 b3 b4 b5 b6 b7 x18 x19 x20 x21 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      CENV pl_empty st_init OW 0 Σ st_init m0 OW -> lib_state st_init m0 OW pl_empty EA ->
      fp_stop FB (bv_unsigned s0) ->
      payload_okA m LB D d -> D <= lo ->
      implA (fuzz_one_gA ops d st_init) Σ QPOST
        (MS (mkR x1 (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0 x9 a0 b1 b2 b3 b4 b5 b6 b7
                 x18 x19 x20 x21 (wz D) (wz (zlength d)) x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f309c) fc None m0 (seg_rom bgasegs)).
    Proof.
      intros until fc. intros ENV0 LS0 S0STOP PLD DLO.
      pose proof ENV0 as (OK & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
      pose proof hpl_only_empty as HPL0.
      assert (SR1 : stored_ref RB1) by (unfold stored_ref; split; [unfold RB1, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (SR2 : stored_ref RB2) by (unfold stored_ref; split; [unfold RB2, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (SR3 : stored_ref RB3) by (unfold stored_ref; split; [unfold RB3, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (SR4 : stored_ref RB4) by (unfold stored_ref; split; [unfold RB4, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (SR5 : stored_ref RB5) by (unfold stored_ref; split; [unfold RB5, NFIX; lia| split; [discriminate| reflexivity]]).
      assert (ECE0 : 0 <= HxaEceIface.ECE_COST) by (unfold HxaEceIface.ECE_COST; clear; lia).
      assert (MC0 : 0 <= MC) by (unfold MC; clear; lia).
      assert (TOT : 9 * MC + EXP_COST + SIMPLE_COST + HxaEceIface.ECE_COST <= FUZZ_TOTAL) by (unfold FUZZ_TOTAL; clear; lia).
      rewrite fuzz_one_gA_eq. unfold MallocRep.wz.

      apply implA_from_evt. step. apply evt_done.
      eapply (new_callA QPOST _ pl_empty st_init OW 0 Σ st_init m0 OW RB1 0);
        [exact HPL0 | exact ENV0 | exact LS0 | exact SR1 | reflexivity | clear; lia | reflexivity | clear; lia
        | clear - TOT MC0 COST_EXP COST_SIMPLE ECE0; lia | exact S0STOP | rewrite unsigned_lit by (clear; lia); exact R_BN_new_1f2eb8 |].
      intros p1 a1 Σ1 m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F1 fc1 ls1 RA1 ENV1 LS1 CB1. clear ENV0 LS0.
      set (PL1 := pl_set pl_empty RB1 (Some (PHeap a1 p1 0))) in *.
      pose proof (hpl_only_set_heap pl_empty RB1 a1 p1 0 HPL0) as HPL1. fold PL1 in HPL1. fix_ret.

      assert (FPS : fp_stop FB (bv_unsigned (Z_to_bv 64 a1))).
      { pose proof ENV1 as (_ & HEAP1 & _).
        pose proof (AH_range _ _ _ _ p1 a1 24 HEAP1 ltac:(left; reflexivity)) as (A10 & _ & _ & A1C & _).
        left. rewrite unsigned_lit by (clear - RA1; lia). clear - A1C CEIL LOFB. lia. }

      apply implA_from_evt. step. step. apply evt_done.
      eapply (new_callA QPOST _ PL1 ls1 _ (0 + MC) Σ1 ls1 m1 _ RB2 (0 + 1));
        [exact HPL1 | exact ENV1 | exact LS1 | exact SR2 | reflexivity | exact CB1 | reflexivity | clear; lia
        | clear - TOT MC0 COST_EXP COST_SIMPLE ECE0; lia | exact FPS | rewrite unsigned_lit by (clear; lia); exact R_BN_new_1f2ec0 |].
      intros p2 a2 Σ2 m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ls2 RA2 ENV2 LS2 CB2. clear ENV1 LS1.
      set (PL2 := pl_set PL1 RB2 (Some (PHeap a2 p2 0))) in *.
      pose proof (hpl_only_set_heap PL1 RB2 a2 p2 0 HPL1) as HPL2. fold PL2 in HPL2. fix_ret.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (new_callA QPOST _ PL2 ls2 _ (0 + MC + MC) Σ2 ls2 m2 _ RB3 (0 + 1 + 1));
        [exact HPL2 | exact ENV2 | exact LS2 | exact SR3 | reflexivity | exact CB2 | reflexivity | clear; lia
        | clear - TOT MC0 COST_EXP COST_SIMPLE ECE0; lia | exact FPS | rewrite unsigned_lit by (clear; lia); exact R_BN_new_1f2ec8 |].
      intros p3 a3 Σ3 m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ls3 RA3 ENV3 LS3 CB3. clear ENV2 LS2.
      set (PL3 := pl_set PL2 RB3 (Some (PHeap a3 p3 0))) in *.
      pose proof (hpl_only_set_heap PL2 RB3 a3 p3 0 HPL2) as HPL3. fold PL3 in HPL3. fix_ret.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (new_callA QPOST _ PL3 ls3 _ (0 + MC + MC + MC) Σ3 ls3 m3 _ RB4 (0 + 1 + 1 + 1));
        [exact HPL3 | exact ENV3 | exact LS3 | exact SR4 | reflexivity | exact CB3 | reflexivity | clear; lia
        | clear - TOT MC0 COST_EXP COST_SIMPLE ECE0; lia | exact FPS | rewrite unsigned_lit by (clear; lia); exact R_BN_new_1f2ed0 |].
      intros p4 a4 Σ4 m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F4 fc4 ls4 RA4 ENV4 LS4 CB4. clear ENV3 LS3.
      set (PL4 := pl_set PL3 RB4 (Some (PHeap a4 p4 0))) in *.
      pose proof (hpl_only_set_heap PL3 RB4 a4 p4 0 HPL3) as HPL4. fold PL4 in HPL4. fix_ret.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (new_callA QPOST _ PL4 ls4 _ (0 + MC + MC + MC + MC) Σ4 ls4 m4 _ RB5 (0 + 1 + 1 + 1 + 1));
        [exact HPL4 | exact ENV4 | exact LS4 | exact SR5 | reflexivity | exact CB4 | reflexivity | clear; lia
        | clear - TOT MC0 COST_EXP COST_SIMPLE ECE0; lia | exact FPS | rewrite unsigned_lit by (clear; lia); exact R_BN_new_1f2ed8 |].
      intros p5 a5 Σ5 m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F5 fc5 ls5 RA5 ENV5 LS5 CB5. clear ENV4 LS4.
      set (PL5 := pl_set PL4 RB5 (Some (PHeap a5 p5 0))) in *.
      pose proof (hpl_only_set_heap PL4 RB5 a5 p5 0 HPL4) as HPL5. fold PL5 in HPL5. fix_ret.

      apply implA_from_evt. step. step. apply evt_done.
      eapply (ctx_new_callA QPOST _ PL5 ls5 _ (0 + MC + MC + MC + MC + MC) Σ5 ls5 m5 _ (0 + 1 + 1 + 1 + 1 + 1));
        [exact HPL5 | exact ENV5 | exact LS5 | reflexivity | exact CB5 | reflexivity | clear; lia
        | clear - TOT MC0 COST_EXP COST_SIMPLE ECE0; lia | exact FPS | rewrite unsigned_lit by (clear; lia); exact R_BN_CTX_new_1f2ee0 |].
      intros pc ac Σ6 m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? F6 fc6 ls6 RAC ENV6 LS6 CB6. clear ENV5 LS5.
      set (PL6 := pl_set_ctx PL5 (Some (ac, pc))) in *.
      pose proof (hpl_only_set_ctx PL5 (Some (ac, pc)) HPL5) as HPL6. fold PL6 in HPL6. fix_ret.

      apply implA_from_evt. step.
      step. if_cases KN1; unfold MallocRep.wz in KN1; rewrite ?unsigned_lit in KN1 by (clear - RA1; lia); zify_cond KN1. { exfalso. clear - KN1 RA1. lia. }
      step. if_cases KN2; unfold MallocRep.wz in KN2; rewrite ?unsigned_lit in KN2 by (clear - RA2; lia); zify_cond KN2. { exfalso. clear - KN2 RA2. lia. }
      step. if_cases KN3; unfold MallocRep.wz in KN3; rewrite ?unsigned_lit in KN3 by (clear - RA3; lia); zify_cond KN3. { exfalso. clear - KN3 RA3. lia. }
      step. if_cases KN4; unfold MallocRep.wz in KN4; rewrite ?unsigned_lit in KN4 by (clear - RA4; lia); zify_cond KN4. { exfalso. clear - KN4 RA4. lia. }
      step. if_cases KN5; unfold MallocRep.wz in KN5; rewrite ?unsigned_lit in KN5 by (clear - RA5; lia); zify_cond KN5. { exfalso. clear - KN5 RA5. lia. }
      step. if_cases KN6; unfold MallocRep.wz in KN6; rewrite ?unsigned_lit in KN6 by (clear - RAC; lia); zify_cond KN6. { exfalso. clear - KN6 RAC. lia. }
      apply evt_done.
      eapply (fuzz_splitA PL6 ls6 _ (0 + MC + MC + MC + MC + MC + MC) Σ6 ls6 m6 _ p1 p2 p3 p4 p5 pc a1 a2 a3 a4 a5 ac D d);
        [exact HPL6 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | unfold pl_fresh; repeat split; reflexivity | exact ENV6 | exact LS6
        | rewrite CB6; clear; lia | clear - TOT MC0 COST_EXP COST_SIMPLE ECE0; lia | exact PLD | exact DLO].
    Qed.
  End Env.

  Lemma fuzz_one_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (EA : BnRepDefs.err_addrs)
      (lo : Z) (D : Z) (d : list Z),
    bn_preA Σ st_init m OW LB pl_empty EA sp lo FUZZ_STACK_A FUZZ_TOTAL -> tp = wz TP_A ->
    cnt_bal st_init OW + Z.of_nat (length LB) + 80 <= LIVE_MAX ->
    (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
    payload_okA m LB D d -> D <= lo -> a0 = wz D -> a1 = wz (zlength d) ->
    implA (fuzz_one_gA ops d st_init) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st_init OW LB lo m pl_empty EA FUZZ_TOTAL
                (fun (rc : Z) (_ : bstate bptr) (_ : list block) (_ : placement) (a0' : word) => rc = 0 /\ a0' = wz 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ_ENTRY) fc None m (seg_rom bgasegs)).
  Proof.
    intros until d. intros PRE -> CNT80 S0NF PL DLO -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX in LO'.
    unfold LX_FUZZ_ENTRY, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    apply implA_from_evt.
    step.
    carve_frame 112%nat ST.
    step. do 13 step. do 6 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib st_init OW pl_empty lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp)]) by (constructor; [left; cbn; clear - LO'; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB st_init pl_empty EA (bv_unsigned sp) []) [(bv_unsigned sp + -112, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] st_init m m1 OW pl_empty EA _ HEAP LS MU WM FROK WOK) as LS1.
    assert (ENV : cenvA LB pl_empty lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra None FUZZ_TOTAL Σ st_init OW m
                    [C8 (Z_to_bv 64 SHB); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ st_init m1 OW).
    { unfold cenvA, cenv_ok.
      split. { split; [exact CEIL|]. split; [clear - LO'; lia|]. split; [clear; lia|]. split; [unfold USTACK_TOP; exact SPT|]. split; [exact SP16|].
               split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact CNT|]. split; [exact CRED|]. split; [exact FROK|]. split; [exact FAL| exact NOFR]. }
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
      split; [exact ST|]. split; [exact MI|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(clear - LO'; lia))|].
      split; [clear; lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
      split; [cbn [app]; exact FR|]. split; [cbn; clear; lia|]. exact I. }
    assert (LOS : lo <= bv_unsigned sp - FUZZ_STACK_A) by exact LO.
    assert (FPS0 : fp_stop (bv_unsigned sp + -112) (bv_unsigned s0)).
    { destruct S0NF as [H|[H|H]]; [left; clear - H LO'; lia | right; left; exact H | right; right; exact H]. }
    apply evt_done.
    eapply (fuzz_createA) with (lo := lo) (m0 := m1) (D := D) (d := d); [exact LOS | exact CNT80 | exact ENV | exact LS1 | exact FPS0 | exact PL | exact DLO].
  Qed.
End Proofs.

End WithRT.
