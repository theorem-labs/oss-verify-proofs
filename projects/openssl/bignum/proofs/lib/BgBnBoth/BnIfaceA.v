(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require BgInv.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition MC : Z := 0.

Lemma mcost_le_MC : forall n, 0 <= n <= BgInv.BG_BSZ -> 0 <= mcost n <= MC.
Proof. intros n Hn. unfold mcost, MC, BgInv.BG_BSZ in *. destruct (Z.leb_spec n 64512); lia. Qed.

Definition refs_stable (ls : lstate bptr) (OW : list block) (ls' : lstate bptr) (OW' : list block) (AD : bn_addrs) : Prop :=
  forall r a, ref_at ls OW AD r a -> ref_at ls' OW' AD r a.

Definition cnt_bal (ls : lstate bptr) (OW : list block) : Z := Z.of_nat (length OW) - Z.of_nat (length (blocks_of ls)).
Definition cnt_eq (ls : lstate bptr) (OW : list block) (ls' : lstate bptr) (OW' : list block) : Prop := cnt_bal ls' OW' = cnt_bal ls OW.
Definition cnt_ok (ls : lstate bptr) (OW LB : list block) : Prop := cnt_bal ls OW + Z.of_nat (length LB) + 25 <= LIVE_MAX.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition ax_client (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop := ~ rin_ivs X a /\ aclient_addr LB SP a.
Definition ax_pres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop := agree_on (ax_client LB SP X) m m'.

Definition bn_preA (Σ : rts RT) (ls : lstate bptr) (m : mem) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (sp : word) (lo : Z) (stack cost : Z) : Prop :=
  AHEAP Σ OW LB m /\ lib_state ls m OW AD EA
  /\ stk bgbsegs m lo (bv_unsigned sp) /\ ACEIL <= lo /\ lo <= bv_unsigned sp - stack
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
  /\ mem_inv bgbsegs m
  /\ cnt_ok ls OW LB /\ cost <= rt_credit RT Σ.

Definition bn_postA {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (lo : Z) (m : mem) (AD : bn_addrs) (EA : err_addrs) (cost : Z)
    (RES : A -> lstate bptr -> list block -> word -> Prop)
    (r : A * lstate bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bgbsegs)
    /\ AHEAP Σ' OW' LB m' /\ lib_state (snd r) m' OW' AD EA
    /\ stk bgbsegs m' lo (bv_unsigned sp) /\ mem_inv bgbsegs m'
    /\ ax_pres LB (bv_unsigned sp) LIBW_A m m'
    /\ rt_credit RT Σ - cost <= rt_credit RT Σ'
    /\ cnt_eq ls OW (snd r) OW'
    /\ refs_stable ls OW (snd r) OW' AD
    /\ RES (fst r) (snd r) OW' a0.

Definition w_lib (OW : list block) (lo sp : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= sp) \/ (exists b, In b OW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma seg_heap : forall Σ OW LB m m' W lo sp,
  AHEAP Σ OW LB m -> munch W m m' -> wmono bgbsegs m m' -> Forall (w_lib OW lo sp) W -> ACEIL <= lo -> sp <= USTACK_TOP ->
  AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' W lo sp HEAP MU WM HW CEIL SPT. eapply AH_frame; [exact HEAP| exact MU| exact WM|].
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|(b & Hb & H1 & H2)]; cbn [fst snd] in *.
  - left. cbn. lia.
  - right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn. auto.
Qed.

Lemma blk_not_static : forall Σ OW LB m b x, AHEAP Σ OW LB m -> In b OW -> blk_addr b <= x < blk_addr b + blk_size b -> client_static x -> False.
Proof.
  intros Σ OW LB m b x HEAP Hb Hx [(l & h & Hin & Hr) _].
  pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (B0 & _ & _ & _ & BI).
  unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Lemma stack_munch_agree : forall Σ OW LB m m1 W (L : list block) sp,
  AHEAP Σ OW LB m -> munch W m m1 -> Forall (fun iv => ACEIL <= fst iv /\ snd iv <= sp) W ->
  (forall b, In b L -> In b (OW ++ LB)) ->
  agree_on (aclient_addr L sp) m m1.
Proof.
  intros Σ OW LB m m1 W L sp HEAP MU HW HL. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a Ha. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1. clear MU.
  induction HW as [|[x y] W [H1 H2] HW IH]; [exact I|]. cbn [outside fst snd] in *. split; [|exact IH].
  intros Hx. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia | |].
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP (HL b Hb)) as (_ & _ & _ & BC & _). lia.
Qed.

Lemma agree_client_weaken : forall (L L2 : list block) sp sp' m m',
  agree_on (aclient_addr L sp') m m' -> sp' <= sp -> (forall b, In b L2 -> In b L) -> agree_on (aclient_addr L2 sp) m m'.
Proof.
  intros L L2 sp sp' m m' H HS HL. eapply agree_on_mono; [exact H|].
  intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; lia | right; left; exact Ha | right; right; exists b; split; [exact (HL b Hb) | exact Hr]].
Qed.

Lemma call_okA : forall Σ OW LB m lo sp',
  AHEAP Σ OW LB m -> stk bgbsegs m lo sp' -> ACEIL <= lo -> lo + RT_STACK <= sp' -> sp' + 16 <= USTACK_TOP -> sp' mod 16 = 0 ->
  call_ok RT Σ m (Z_to_bv 64 sp') lo.
Proof.
  intros Σ OW LB m lo sp' HEAP ST CEIL LO TOP M16. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK in *; lia).
  unfold call_ok. rewrite ESP. destruct HEAP as (_ & HS & _). rewrite HS. fold ACEIL.
  split; [exact ST|]. split; [exact CEIL|]. split; [exact LO|]. split; [exact TOP | exact M16].
Qed.

End WithRT.
