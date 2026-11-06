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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameEnv BnAKitAF BnCallAF PlaceMont PlaceKitA W_mont_ctxAF W_mont_freeAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).

Lemma st_mont_init_eq : forall (st : bstate bptr) m OW PL EA, lib_state st m OW PL EA -> pl_mont PL = None -> st_mont_init st = set_mont 0 0 st.
Proof.
  intros st m OW PL EA (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) EM.
  assert (G1 : getbn RMontRR st = bn_nil 0) by (apply M2; [unfold RMontRR, NFIX; lia | apply pl_of_mont_none; [exact EM | reflexivity]]).
  assert (G2 : getbn RMontN st = bn_nil 0) by (apply M2; [unfold RMontN, NFIX; lia | apply pl_of_mont_none; [exact EM | reflexivity]]).
  assert (G3 : getbn RMontNi st = bn_nil 0) by (apply M2; [unfold RMontNi, NFIX; lia | apply pl_of_mont_none; [exact EM | reflexivity]]).
  assert (S1 : setbn RMontRR (bn_nil 0) (set_mont 0 0 st) = set_mont 0 0 st)
    by (rewrite <- G1; change (getbn RMontRR st) with (getbn RMontRR (set_mont 0 0 st)); apply setbn_getbn_id).
  assert (S2 : setbn RMontN (bn_nil 0) (set_mont 0 0 st) = set_mont 0 0 st)
    by (rewrite <- G2; change (getbn RMontN st) with (getbn RMontN (set_mont 0 0 st)); apply setbn_getbn_id).
  assert (S3 : setbn RMontNi (bn_nil 0) (set_mont 0 0 st) = set_mont 0 0 st)
    by (rewrite <- G3; change (getbn RMontNi st) with (getbn RMontNi (set_mont 0 0 st)); apply setbn_getbn_id).
  unfold st_mont_init. rewrite S1, S2, S3. reflexivity.
Qed.

Lemma refs_stable_mont_in : forall (st : bstate bptr) OW (b : block), blk_size b = 96 -> refs_stable st (b :: OW) st OW.
Proof.
  intros st OW b Hb PLx i a H. apply ref_at_pool in H. apply ref_at_pool. destruct H as (q & Hh & Eq & Hin & Ea).
  exists q, Hh. split; [exact Eq|]. split; [| exact Ea].
  destruct Hin as [Hin|Hin]; [| exact Hin]. exfalso. rewrite Hin in Hb. cbn [blk_size snd] in Hb. unfold ITEM_SZ, POOL_ITEM_BYTES in Hb. lia.
Qed.
Lemma refs_stable_mont_out : forall (st : bstate bptr) OW (b : block), refs_stable st OW st (b :: OW).
Proof. intros st OW b PLx i a H. eapply ref_at_ow_mono; [| exact H]. intros x Hx. right. exact Hx. Qed.

Lemma fr_room_mont : forall {AR : ARun} d (st : bstate bptr) OW LB (b : block),
  fr_room d st OW LB -> cnt_bal st OW + Z.of_nat (length LB) + 66 + 2 * Z.of_nat d <= LIVE_MAX -> fr_room d st (b :: OW) LB.
Proof. intros AR d st OW LB b [H1 _] H2. split; [exact H1|]. rewrite cnt_bal_cons. lia. Qed.

Section Calls.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma mont_new_callA : forall {C : Type} (K : bptr -> BM (M := btree bptr) (ptr := bptr) C) (Q : C * bstate bptr -> rts RT -> machine_state -> Prop)
    (LB : list block) (PL0 : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (TOTAL : Z)
    (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem) (pre : list cell) (used used' : Z) (Σ : rts RT) (ls : bstate bptr) (m : mem) (OW : list block)
    (rax gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  cenvA LB PL0 lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  lib_state ls m OW PL0 EA -> pl_mont PL0 = None ->
  bv_unsigned x8 = SPv -> lo <= FB - BN_MONT_CTX_NEW_STACK -> used + MC <= used' -> used' <= TOTAL -> tp = wz TP_A ->
  cnt_bal ls0 OW0 + Z.of_nat (length LB) + 66 <= LIVE_MAX ->
  uk_ctx BN_MONT_CTX_NEW (bv_unsigned rax :: bv_unsigned raw :: ras) ->
  (forall (qm : bptr) (am : Z) Σ' m' (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) F' fc',
      0 < am < 2^63 ->
      cenvA LB (pl_set_mont PL0 (Some (am, qm))) lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 ((qm, am, 96) :: OW0) m0 pre used' Σ' (st_mont_init ls) m' ((qm, am, 96) :: OW) ->
      lib_state (st_mont_init ls) m' ((qm, am, 96) :: OW) (pl_set_mont PL0 (Some (am, qm))) EA ->
      implA (K qm (st_mont_init ls)) Σ' Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 (wz am) y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
            F' (ret_pc rax) fc' None m' (seg_rom bgasegs))) ->
  implA (bbind ops (BN_MONT_CTX_new ops) K ls) Σ Q
    (MS (mkR rax (Z_to_bv 64 FB) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (wz BN_MONT_CTX_NEW) fc None m (seg_rom bgasegs)).
Proof.
  intros until fc. intros ENV LS EM E8 HK HU HT -> CNT1 CTX K1.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRC & FSZ & UW).
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  assert (EF : bv_unsigned (Z_to_bv 64 FB) = FB) by (eapply ESPvA; [exact OK | exact HEAP]).
  unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply (BN_MONT_CTX_new_walkA) with (lo := lo) (ras := bv_unsigned raw :: ras) (LB := LB) (PL := PL0) (EA := EA);
      [ eapply cenv_preA; [exact ENV | exact LS | exact HK | clear - HU HT; lia]
      | rewrite E8, EF; eapply cenv_uwA; [reflexivity | exact ENV] | exact CTX | reflexivity | exact EM ]. }
  cbv beta. intros [p ls'] Σ' ms' PO. unfold bn_postA_p in PO. rewrite EF in PO. cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & PL' & -> & HEAP' & LS' & ST' & MI' & AXP' & CR' & (a & -> & -> & ARg & -> & ->)).
  assert (AG : agree_on (fun x => FB <= x < USTACK_TOP) m m').
  { eapply agree_on_mono; [exact AXP'|]. intros x Hx. cbv beta in Hx. split; [|left; lia].
    apply (xw_stack_out Σ OW LB m PL0 SPv USTACK_TOP x HEAP FROK). clear - Hx CEIL LOFB. lia. }
  eapply K1; [exact ARg | | exact LS'].
  unfold cenvA, cenv_ok.
  split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|].
           split; [unfold cnt_ok; rewrite cnt_bal_cons; clear - CNT1; lia|]. split; [exact CRED0|].
           split; [exact (frames_ok_set_mont _ _ _ _ _ FROK)|]. split; [exact (frames_al_set_mont _ _ FAL) | exact NOFR]. }
  split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
  split. { eapply ax_pres_trans; [exact AXP|]. eapply ax_pres_weaken; [exact AXP'| clear - FBSP; lia]. }
  split; [clear - CR CR' HU; lia|].
  split. { unfold cnt_eq in *. rewrite !cnt_bal_cons. rewrite (st_mont_init_eq ls m OW PL0 EA LS EM). change (cnt_bal (set_mont 0 0 ls) OW) with (cnt_bal ls OW). rewrite CNT. reflexivity. }
  split. { eapply refs_stable_trans; [apply refs_stable_mont_in; reflexivity|]. eapply refs_stable_trans; [exact RS|].
           rewrite (st_mont_init_eq ls m OW PL0 EA LS EM). intros PLx i x H. apply ref_at_set_mont. eapply ref_at_ow_mono; [| exact H]. intros b Hb. right. exact Hb. }
  split. { eapply rw_cells_agree; [exact AG | exact FRC |]. intros x Hx. rewrite cells_size_app in Hx. cbn [cells_size csize Nat.add] in Hx.
           unfold USTACK_TOP in *. clear - Hx FSZ FBSP SPT. lia. }
  split; [exact FSZ|].
  unfold uw_opt in *. apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AG|]. intros x Hx. cbv beta in *. clear - Hx FBSP. lia.
Qed.

Lemma mont_free_callA : forall {C : Type} (K : unit -> BM (M := btree bptr) (ptr := bptr) C) (Q : C * bstate bptr -> rts RT -> machine_state -> Prop)
    (LB : list block) (PL0 : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (TOTAL : Z)
    (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem) (pre : list cell) (used : Z) (Σ : rts RT) (ls : bstate bptr) (m : mem) (OW : list block)
    (am : Z) (qm : bptr)
    (rax gp tp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  cenvA LB (pl_set_mont PL0 (Some (am, qm))) lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 ((qm, am, 96) :: OW0) m0 pre used Σ ls m OW ->
  lib_state ls m OW (pl_set_mont PL0 (Some (am, qm))) EA -> pl_mont PL0 = None ->
  bv_unsigned x8 = SPv -> lo <= FB - BN_MONT_CTX_FREE_STACK -> used <= TOTAL -> tp = wz TP_A ->
  uk_ctx BN_MONT_CTX_FREE (bv_unsigned rax :: bv_unsigned raw :: ras) ->
  (forall Σ' ls' m' OW' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) F' fc',
      cenvA LB PL0 lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 pre used Σ' ls' m' OW' ->
      lib_state ls' m' OW' PL0 EA ->
      implA (K tt ls') Σ' Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
            F' (ret_pc rax) fc' None m' (seg_rom bgasegs))) ->
  implA (bbind ops (BN_MONT_CTX_free ops qm) K ls) Σ Q
    (MS (mkR rax (Z_to_bv 64 FB) gp tp t0 t1 t2 x8 x9 (wz am) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (wz BN_MONT_CTX_FREE) fc None m (seg_rom bgasegs)).
Proof.
  intros until fc. intros ENV LS EM E8 HK HU -> CTX K1.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRC & FSZ & UW).
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  assert (EF : bv_unsigned (Z_to_bv 64 FB) = FB) by (eapply ESPvA; [exact OK | exact HEAP]).
  unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply (BN_MONT_CTX_free_walkA) with (lo := lo) (ras := bv_unsigned raw :: ras) (LB := LB) (PL := pl_set_mont PL0 (Some (am, qm))) (EA := EA) (am := am) (qm := qm);
      [ eapply cenv_preA; [exact ENV | exact LS | exact HK | clear - HU; lia]
      | rewrite E8, EF; eapply cenv_uwA; [reflexivity | exact ENV] | exact CTX | reflexivity | reflexivity | reflexivity ]. }
  cbv beta. intros [v ls'] Σ' ms' PO. unfold bn_postA_p in PO. rewrite EF in PO. cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & PL' & -> & HEAP' & LS' & ST' & MI' & AXP' & CR' & (-> & CB1 & RS')).
  destruct v. rewrite (pl_set_mont_fresh PL0 _ EM) in LS'.
  assert (AG : agree_on (fun x => FB <= x < USTACK_TOP) m m').
  { eapply agree_on_mono; [exact AXP'|]. intros x Hx. cbv beta in Hx. split; [|left; lia].
    apply (xw_stack_out Σ OW LB m _ SPv USTACK_TOP x HEAP FROK). clear - Hx CEIL LOFB. lia. }
  eapply K1; [| exact LS'].
  unfold cenvA, cenv_ok.
  split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|].
           split; [unfold cnt_ok in *; rewrite cnt_bal_cons in CNT0; clear - CNT0; lia|]. split; [exact CRED0|].
           split; [exact FROK|]. split; [exact FAL | exact NOFR]. }
  split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
  split. { eapply ax_pres_trans; [exact AXP|]. eapply ax_pres_weaken; [exact AXP'| clear - FBSP; lia]. }
  split; [clear - CR CR'; lia|].
  split. { unfold cnt_eq in *. rewrite cnt_bal_cons in CNT. rewrite CB1, CNT. clear. lia. }
  split. { eapply refs_stable_trans; [apply (refs_stable_mont_out ls0 OW0 (qm, am, 96))|]. eapply refs_stable_trans; [exact RS | exact RS']. }
  split. { eapply rw_cells_agree; [exact AG | exact FRC |]. intros x Hx. rewrite cells_size_app in Hx. cbn [cells_size csize Nat.add] in Hx.
           unfold USTACK_TOP in *. clear - Hx FSZ FBSP SPT. lia. }
  split; [exact FSZ|].
  unfold uw_opt in *. apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AG|]. intros x Hx. cbv beta in *. clear - Hx FBSP. lia.
Qed.

End Calls.
