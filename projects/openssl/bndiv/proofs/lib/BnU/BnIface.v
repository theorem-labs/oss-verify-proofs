(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma implM_embed_lbind : forall {A B} (t : btree bptr A) (f : A -> btree bptr B) s Q ms,
  implM usegs (interp (lbind (embed t) (fun a => embed (f a)))) s Q ms -> implM usegs (interp (embed (tbind t f))) s Q ms.
Proof.
  intros A B t f. induction t as [a| |n k IH|p k IH]; intros s Q ms H; cbn [tbind embed lbind interp] in *; try exact H.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1). exact H1.
Qed.

Lemma implM_embed_bind : forall {A B} (t : btree bptr A) (f : A -> btree bptr B) s Q1 Q ms,
  implM usegs (interp (embed t)) s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implM usegs (interp (embed (f a))) s' Q ms') ->
  implM usegs (interp (embed (tbind t f))) s Q ms.
Proof. intros A B t f s Q1 Q ms H1 H2. apply implM_embed_lbind. eapply implM_interp_bind; eauto. Qed.

(* [comment removed for export] *)
Definition refs_stable (ls : lstate bptr) (OW : list block) (ls' : lstate bptr) (OW' : list block) (AD : bn_addrs) : Prop :=
  forall r a, ref_at ls OW AD r a -> ref_at ls' OW' AD r a.

Lemma refs_stable_refl : forall ls OW AD, refs_stable ls OW ls OW AD.
Proof. intros ls OW AD r a H. exact H. Qed.
Lemma refs_stable_trans : forall ls1 OW1 ls2 OW2 ls3 OW3 AD,
  refs_stable ls1 OW1 ls2 OW2 AD -> refs_stable ls2 OW2 ls3 OW3 AD -> refs_stable ls1 OW1 ls3 OW3 AD.
Proof. intros until AD. intros H1 H2 r a H. apply H2, H1, H. Qed.

(* [comment removed for export] *)
Definition bn_pre (s : PState) (ls : lstate bptr) (m : mem) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (sp : word) (lo B : Z) (errv : word) (stack : Z) : Prop :=
  RHEAP s (OW ++ LB) m /\ lib_state ls m OW AD EA
  /\ rauxv_ok m B /\ bv_unsigned sp <= B
  /\ stk usegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo /\ lo <= bv_unsigned sp - stack
  /\ rw_cells usegs m LX_ERRNO [C4 errv] /\ mem_inv usegs m.

Definition bn_post {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (ls : lstate bptr) (OW LB : list block) (lo B : Z) (m : mem) (AD : bn_addrs) (EA : err_addrs)
    (RES : A -> lstate bptr -> list block -> word -> Prop)
    (r : A * lstate bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' OW' (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ RHEAP s' (OW' ++ LB) m' /\ lib_state (snd r) m' OW' AD EA
    /\ rauxv_ok m' B /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ mem_inv usegs m'
    /\ lx_pres LB (bv_unsigned sp) LIBW_bn m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ refs_stable ls OW (snd r) OW' AD
    /\ RES (fst r) (snd r) OW' a0.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition w_lib (OW : list block) (lo sp : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= sp) \/ (exists b, In b OW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma seg_heap : forall s OW LB m m' W lo sp,
  RHEAP s (OW ++ LB) m -> munch W m m' -> wmono usegs m m' -> Forall (w_lib OW lo sp) W -> alloc_ceiling <= lo ->
  RHEAP s (OW ++ LB) m'.
Proof.
  intros s OW LB m m' W lo sp HEAP MU WM HW CEIL. eapply LH_frame; [exact HEAP| exact MU| exact WM|].
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|(b & Hb & H1 & H2)]; cbn [fst snd] in *.
  - left. cbn. lia.
  - right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn. auto.
Qed.

Lemma seg_auxv : forall s OW LB m m' W lo sp B,
  RHEAP s (OW ++ LB) m -> rauxv_ok m B -> munch W m m' -> wmono usegs m m' -> Forall (w_lib OW lo sp) W ->
  sp <= B -> GLOBALS_TOP <= lo -> rauxv_ok m' B.
Proof.
  intros s OW LB m m' W lo sp B HEAP AUX MU WM HW SPB GLO. eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
  pose proof AUX as (av & x3' & x4' & x5' & x16' & x6' & x11' & x12' & x23' & rnd & _ & _ & _ & HB & _).
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|(b & Hb & H1 & H2)]; cbn [fst snd] in *.
  - unfold RAUXV_CELL, GLOBALS_TOP in *. lia.
  - pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & BI).
    unfold RAUXV_CELL. lia.
Qed.

Lemma seg_lx_pres : forall s OW LB m m' W lo sp X,
  RHEAP s (OW ++ LB) m -> munch W m m' -> wmono usegs m m' -> Forall (w_lib OW lo sp) W -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  lo <= sp -> lx_pres LB sp X m m'.
Proof.
  intros s OW LB m m' W lo sp X HEAP MU WM HW CEIL GLO LOSP. eapply lx_pres_of_munch; [exact MU| exact WM|].
  intros a Ha [_ Hc]. pose proof (LH_nodup _ _ _ HEAP) as ND. clear MU.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
  intros Hx. destruct Hiv as [[H1 H2]|(b & Hb & H1 & H2)]; cbn [fst snd] in *.
  - destruct Hc as [Hc|[(b' & Hb' & Hr)|[Hc _]]]; [lia| | unfold GLOBALS_TOP in *; lia].
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb')) as (_ & _ & _ & BC & _). lia.
  - pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & BI).
    destruct Hc as [Hc|[(b' & Hb' & Hr)|[Hc _]]]; [lia| | lia].
    assert (NE : blk_id b <> blk_id b').
    { rewrite map_app in ND. intros E. eapply (nodup_app_disj _ _ (blk_id b) ND); [apply in_map; exact Hb| rewrite E; apply in_map; exact Hb']. }
    pose proof (LH_disjoint _ _ _ b b' HEAP ltac:(apply in_or_app; left; exact Hb) ltac:(apply in_or_app; right; exact Hb') NE). lia.
Qed.

End WithCeiling0.
