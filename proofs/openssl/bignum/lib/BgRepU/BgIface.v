(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma implM_embed_lbind : forall {A B} (t : btree bptr A) (f : A -> btree bptr B) s Q ms,
  implM bgusegs (interp (lbind (embed t) (fun a => embed (f a)))) s Q ms -> implM bgusegs (interp (embed (tbind t f))) s Q ms.
Proof.
  intros A B t f. induction t as [a| |n k IH|p k IH]; intros s Q ms H; cbn [tbind embed lbind interp] in *; try exact H.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1). exact H1.
Qed.

Lemma implM_embed_bind : forall {A B} (t : btree bptr A) (f : A -> btree bptr B) s Q1 Q ms,
  implM bgusegs (interp (embed t)) s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implM bgusegs (interp (embed (f a))) s' Q ms') ->
  implM bgusegs (interp (embed (tbind t f))) s Q ms.
Proof. intros A B t f s Q1 Q ms H1 H2. apply implM_embed_lbind. eapply implM_interp_bind; eauto. Qed.

Definition refs_stable (st : ST) (OW : list block) (st' : ST) (OW' : list block) : Prop :=
  forall PL i a, ref_at st OW PL (RPool i) a -> ref_at st' OW' PL (RPool i) a.

Lemma refs_stable_refl : forall st OW, refs_stable st OW st OW.
Proof. intros st OW PL i a H. exact H. Qed.
Lemma refs_stable_trans : forall st1 OW1 st2 OW2 st3 OW3,
  refs_stable st1 OW1 st2 OW2 -> refs_stable st2 OW2 st3 OW3 -> refs_stable st1 OW1 st3 OW3.
Proof. intros until OW3. intros H1 H2 PL i a H. apply H2, H1, H. Qed.

Lemma ref_at_stable : forall st OW st' OW' PL r a, refs_stable st OW st' OW' -> ref_at st OW PL r a -> ref_at st' OW' PL r a.
Proof.
  intros st OW st' OW' PL r a RS H. destruct (Nat.ltb_spec r NFIX) as [Hr|Hr].
  - eapply ref_at_fixed_indep; [exact Hr| exact H].
  - replace r with (RPool (r - NFIX)) in * by (unfold RPool; lia). apply RS. exact H.
Qed.

Lemma refs_stable_intro : forall st OW st' OW' extra,
  gx_items (st_ctx st') = gx_items (st_ctx st) ++ extra ->
  (forall q H, In q (gx_items (st_ctx st)) -> In (q, H, ITEM_SZ) OW -> In (q, H, ITEM_SZ) OW') ->
  refs_stable st OW st' OW'.
Proof.
  intros st OW st' OW' extra EI HOW PL i a H. apply ref_at_pool in H. apply ref_at_pool. destruct H as (q & H0 & Eq & Hin & Ea).
  exists q, H0. rewrite EI. split; [rewrite nth_error_app1; [exact Eq| apply nth_error_Some; congruence]|].
  split; [apply HOW; [eapply nth_error_In; exact Eq| exact Hin]| exact Ea].
Qed.

Lemma refs_stable_ow : forall st OW st' OW',
  gx_items (st_ctx st') = gx_items (st_ctx st) -> (forall q H, In q (gx_items (st_ctx st)) -> In (q, H, ITEM_SZ) OW -> In (q, H, ITEM_SZ) OW') ->
  refs_stable st OW st' OW'.
Proof. intros st OW st' OW' E HOW. eapply (refs_stable_intro _ _ _ _ []); [rewrite E, app_nil_r; reflexivity| exact HOW]. Qed.

Lemma refs_stable_setbn : forall st OW r b, refs_stable st OW (setbn r b st) OW.
Proof. intros st OW r b PL i a H. apply ref_at_setbn. exact H. Qed.

Definition bn_pre (s : PState) (st : ST) (m : mem) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
    (sp : word) (lo B : Z) (errv : word) (stack : Z) : Prop :=
  RHEAP s (OW ++ LB) m /\ lib_state st m OW PL EA /\ frames_ok PL (bv_unsigned sp) B
  /\ rauxv_ok m B /\ bv_unsigned sp <= B /\ B < 2^63
  /\ stk bgusegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo /\ lo <= bv_unsigned sp - stack
  /\ rw_cells bgusegs m LX_ERRNO [C4 errv] /\ mem_inv bgusegs m.

Definition bn_post {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (st : ST) (OW LB : list block) (lo B : Z) (m : mem) (PL : placement) (EA : BnRep.err_addrs)
    (RES : A -> ST -> list block -> placement -> word -> Prop)
    (r : A * ST) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' OW' PL' (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ RHEAP s' (OW' ++ LB) m' /\ lib_state (snd r) m' OW' PL' EA
    /\ rauxv_ok m' B /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ rw_cells bgusegs m' LX_ERRNO [C4 errv'] /\ mem_inv bgusegs m'
    /\ lx_pres LB (bv_unsigned sp) (XW PL) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ refs_stable st OW (snd r) OW'
    /\ RES (fst r) (snd r) OW' PL' a0.

Lemma frames_ok_call : forall PL sp sp' B lo, frames_ok PL sp B -> alloc_ceiling <= lo -> lo <= sp' -> sp' <= sp -> frames_ok PL sp' B.
Proof. intros PL sp sp' B lo H H1 H2 H3. eapply frames_ok_mono; [exact H| lia]. Qed.

Definition w_lib (st : ST) (OW : list block) (PL : placement) (lo sp : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= sp)
  \/ (exists b, In b OW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
  \/ (exists r a, ref_at st OW PL r a /\ r <> ROne /\ a <= fst iv /\ snd iv <= a + 24).

Lemma w_lib_struct_cases : forall st OW PL EA SPX BX r a, lib_parts st OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  (exists b, In b OW /\ blk_addr b <= a /\ a + 24 <= blk_addr b + blk_size b)
  \/ (In (a, a + BN_STRUCT_SZ) (pl_frames PL) /\ SPX <= a /\ a + 24 <= BX).
Proof.
  intros st OW PL EA SPX BX r a (WFS & PWF & IDS & PLB & ERRB) (PLF & CSP & BXB) HA NE.
  pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
  destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea'].
  - left. exists (q, a, n). split; [exact Hin|]. cbn. unfold BN_STRUCT_SZ in *. lia.
  - left. exists (qm, am, MONT_CTX_SZ). split; [exact Hin|]. cbn. unfold MONT_CTX_SZ in *. lia.
  - left. exists (q, H, ITEM_SZ). split; [exact Hin|]. cbn. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. nia.
  - right. split; [exact HF|]. destruct (PLF _ HF) as [X Y]. cbn [fst snd] in X, Y. unfold BN_STRUCT_SZ in *. lia.
  - exfalso. exact (NE Er).
Qed.

Lemma seg_heap : forall s st OW LB PL EA SPX BX m m' W lo sp,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> frames_ok PL SPX BX ->
  munch W m m' -> wmono bgusegs m m' -> Forall (w_lib st OW PL lo sp) W -> alloc_ceiling <= lo ->
  RHEAP s (OW ++ LB) m'.
Proof.
  intros s st OW LB PL EA SPX BX m m' W lo sp HEAP PARTS FROK MU WM HW CEIL. eapply LH_frame; [exact HEAP| exact MU| exact WM|].
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[(b & Hb & H1 & H2)|(r & a & HA & NE & H1 & H2)]]; cbn [fst snd] in *.
  - left. cbn. lia.
  - right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn. auto.
  - destruct (w_lib_struct_cases _ _ _ _ _ _ _ _ PARTS FROK HA NE) as [(b & Hb & B1 & B2)|(HF & F1 & F2)].
    + right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn. lia.
    + left. cbn. destruct FROK as (_ & CSP & _). lia.
Qed.

Lemma seg_auxv : forall s st OW LB PL EA SPX BX m m' W lo sp B,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> rauxv_ok m B ->
  munch W m m' -> wmono bgusegs m m' -> Forall (w_lib st OW PL lo sp) W ->
  sp <= B -> BX <= B -> GLOBALS_TOP <= lo -> rauxv_ok m' B.
Proof.
  intros s st OW LB PL EA SPX BX m m' W lo sp B HEAP PARTS FROK AUX MU WM HW SPB BXB GLO. eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
  pose proof AUX as (av & x3' & x4' & x5' & x16' & x6' & x11' & x12' & x23' & rnd & _ & _ & _ & HB & _).
  pose proof alloc_ceiling_range as CR.
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[(b & Hb & H1 & H2)|(r & a & HA & NE & H1 & H2)]]; cbn [fst snd] in *.
  - unfold RAUXV_CELL, GLOBALS_TOP in *. lia.
  - pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & BI). unfold RAUXV_CELL. lia.
  - destruct (w_lib_struct_cases _ _ _ _ _ _ _ _ PARTS FROK HA NE) as [(b & Hb & B1 & B2)|(HF & F1 & F2)].
    + pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & BI). unfold RAUXV_CELL. lia.
    + destruct FROK as (_ & CSP & _). unfold RAUXV_CELL. lia.
Qed.

Lemma seg_lx_pres : forall s st OW LB PL EA SPX BX m m' W lo sp,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> frames_ok PL SPX BX ->
  munch W m m' -> wmono bgusegs m m' -> Forall (w_lib st OW PL lo sp) W -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  lo <= sp -> lx_pres LB sp (XW PL) m m'.
Proof.
  intros s st OW LB PL EA SPX BX m m' W lo sp HEAP PARTS FROK MU WM HW CEIL GLO LOSP. eapply lx_pres_of_munch; [exact MU| exact WM|].
  intros a Ha [Hna Hc]. pose proof (LH_nodup _ _ _ HEAP) as ND. clear MU.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
  intros Hx. destruct Hiv as [[H1 H2]|[(b & Hb & H1 & H2)|(r & a' & HA & NE & H1 & H2)]]; cbn [fst snd] in *.
  - destruct Hc as [Hc|[(b' & Hb' & Hr)|[Hc _]]]; [lia| | unfold GLOBALS_TOP in *; lia].
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb')) as (_ & _ & _ & BC & _). lia.
  - pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & BI).
    destruct Hc as [Hc|[(b' & Hb' & Hr)|[Hc _]]]; [lia| | lia].
    assert (NEb : blk_id b <> blk_id b').
    { rewrite map_app in ND. intros E. eapply (nodup_app_disj _ _ (blk_id b) ND); [apply in_map; exact Hb| rewrite E; apply in_map; exact Hb']. }
    pose proof (LH_disjoint _ _ _ b b' HEAP ltac:(apply in_or_app; left; exact Hb) ltac:(apply in_or_app; right; exact Hb') NEb). lia.
  - destruct (w_lib_struct_cases _ _ _ _ _ _ _ _ PARTS FROK HA NE) as [(b & Hb & B1 & B2)|(HF & F1 & F2)].
    + pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & BI).
      destruct Hc as [Hc|[(b' & Hb' & Hr)|[Hc _]]]; [lia| | lia].
      assert (NEb : blk_id b <> blk_id b').
      { rewrite map_app in ND. intros E. eapply (nodup_app_disj _ _ (blk_id b) ND); [apply in_map; exact Hb| rewrite E; apply in_map; exact Hb']. }
      pose proof (LH_disjoint _ _ _ b b' HEAP ltac:(apply in_or_app; left; exact Hb) ltac:(apply in_or_app; right; exact Hb') NEb). lia.
    +
      apply Hna. unfold XW. apply rin_ivs_app. right. apply rin_ivs_In. exists (a', a' + BN_STRUCT_SZ). split; [exact HF|]. cbn. unfold BN_STRUCT_SZ. lia.
Qed.

End WithCeiling0.
