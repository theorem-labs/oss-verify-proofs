(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS Tac. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA ImplA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBgRepA Require ApBnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require BnIfaceA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBgRepA Require Import BgRepDefs BgRep BgLayer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation MC := BnIfaceA.MC.
Definition mcost_le_MC := BnIfaceA.mcost_le_MC.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition refs_stable (st : ST) (OW : list block) (st' : ST) (OW' : list block) : Prop :=
  forall PL i a, ref_at st OW PL (RPool i) a -> ref_at st' OW' PL (RPool i) a.

Lemma refs_stable_refl : forall st OW, refs_stable st OW st OW.
Proof. intros st OW PL i a H. exact H. Qed.
Lemma refs_stable_trans : forall st1 OW1 st2 OW2 st3 OW3,
  refs_stable st1 OW1 st2 OW2 -> refs_stable st2 OW2 st3 OW3 -> refs_stable st1 OW1 st3 OW3.
Proof. intros until OW3. intros H1 H2 PL i a H. apply H2, H1, H. Qed.

(* [comment removed for export] *)
Lemma ref_at_stable : forall st OW st' OW' PL r a, refs_stable st OW st' OW' -> ref_at st OW PL r a -> ref_at st' OW' PL r a.
Proof.
  intros st OW st' OW' PL r a RS H. destruct (Nat.ltb_spec r NFIX) as [Hr|Hr].
  - eapply ref_at_fixed_indep; [exact Hr| exact H].
  - replace r with (RPool (r - NFIX)) in * by (unfold RPool; lia). apply RS. exact H.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cnt_bal (st : ST) (OW : list block) : Z := Z.of_nat (length OW) - Z.of_nat (length (blocks_of st)).
Definition cnt_eq (st : ST) (OW : list block) (st' : ST) (OW' : list block) : Prop := cnt_bal st' OW' = cnt_bal st OW.
Definition cnt_ok (st : ST) (OW LB : list block) : Prop := True.   (* [comment removed for export] *)

Lemma cnt_eq_refl : forall st OW, cnt_eq st OW st OW.
Proof. intros. reflexivity. Qed.
Lemma cnt_eq_trans : forall st1 OW1 st2 OW2 st3 OW3, cnt_eq st1 OW1 st2 OW2 -> cnt_eq st2 OW2 st3 OW3 -> cnt_eq st1 OW1 st3 OW3.
Proof. unfold cnt_eq. intros. congruence. Qed.
Lemma cnt_ok_eq : forall st OW st' OW' LB, cnt_ok st OW LB -> cnt_eq st OW st' OW' -> cnt_ok st' OW' LB.
Proof. unfold cnt_ok, cnt_eq. intros. lia. Qed.

(* [comment removed for export] *)
Lemma cnt_bal_setbn : forall r b' (st : ST) OW OW', vref r st ->
  cnt_bal (setbn r b' st) OW' = cnt_bal st OW + (Z.of_nat (length OW') - Z.of_nat (length OW))
                                - (Z.of_nat (length (bn_blocks b')) - Z.of_nat (length (bn_blocks (getbn r st)))).
Proof.
  intros r b' st OW OW' HV. destruct (blocks_setbn r st HV) as (R & P1 & P2). unfold cnt_bal.
  rewrite (Permutation_length (P2 b')), (Permutation_length P1), !length_app. lia.
Qed.

(* [comment removed for export] *)

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma ax_pres_refl : forall LB SP X m, ax_pres LB SP X m m.
Proof. intros. apply agree_on_refl. Qed.
Lemma ax_pres_trans : forall LB SP X m1 m2 m3, ax_pres LB SP X m1 m2 -> ax_pres LB SP X m2 m3 -> ax_pres LB SP X m1 m3.
Proof. intros LB SP X m1 m2 m3. apply agree_on_trans. Qed.
Lemma ax_pres_weaken : forall LB SP SP' X m m', ax_pres LB SP X m m' -> SP <= SP' -> ax_pres LB SP' X m m'.
Proof.
  intros LB SP SP' X m m' H HS. eapply agree_on_mono; [exact H|]. intros a [H1 H2]. split; [exact H1|].
  destruct H2 as [H2|[H2|H2]]; [left; lia | right; left; exact H2 | right; right; exact H2].
Qed.

(* [comment removed for export] *)
Definition frames_al (PL : placement) : Prop := forall iv, In iv (pl_frames PL) -> fst iv mod 8 = 0.

(* [comment removed for export] *)
Definition not_one (r : bnref) : Prop := r <> ROne.

(* [comment removed for export] *)
Definition bn_preA (Σ : rts RT) (st : ST) (m : mem) (OW LB : list block) (PL : placement) (EA : ApBnRepA.err_addrs)
    (sp : word) (lo : Z) (stack cost : Z) : Prop :=
  AHEAP Σ OW LB m /\ lib_state st m OW PL EA /\ frames_ok PL (bv_unsigned sp) USTACK_TOP
  /\ stk ctasegs m lo (bv_unsigned sp) /\ ACEIL <= lo /\ lo <= bv_unsigned sp - stack
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
  /\ mem_inv ctasegs m
  /\ cnt_ok st OW LB /\ cost <= rt_credit RT Σ
  /\ frames_al PL /\ pl_frames PL = [].
   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bn_postA {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (st : ST) (OW LB : list block) (lo : Z) (m : mem) (PL : placement) (EA : ApBnRepA.err_addrs) (cost : Z)
    (RES : A -> ST -> list block -> placement -> word -> Prop)
    (r : A * ST) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' PL',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ AHEAP Σ' OW' LB m' /\ lib_state (snd r) m' OW' PL' EA
    /\ stk ctasegs m' lo (bv_unsigned sp) /\ mem_inv ctasegs m'
    /\ ax_pres LB (bv_unsigned sp) (XW PL) m m'
    /\ rt_credit RT Σ - cost <= rt_credit RT Σ'
    /\ cnt_eq st OW (snd r) OW'
    /\ refs_stable st OW (snd r) OW'
    /\ RES (fst r) (snd r) OW' PL' a0.
   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma frames_ok_call : forall PL sp sp' B lo, frames_ok PL sp B -> ACEIL <= lo -> lo <= sp' -> sp' <= sp -> frames_ok PL sp' B.
Proof. intros PL sp sp' B lo H H1 H2 H3. eapply frames_ok_mono; [exact H| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition w_lib (st : ST) (OW : list block) (PL : placement) (lo sp : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= sp)
  \/ (exists b, In b OW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
  \/ (exists r a, ref_at st OW PL r a /\ r <> ROne /\ a <= fst iv /\ snd iv <= a + 24).

(* [comment removed for export] *)
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

Lemma seg_heap : forall Σ st OW LB PL EA SPX m m' W lo sp,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX USTACK_TOP ->
  munch W m m' -> wmono ctasegs m m' -> Forall (w_lib st OW PL lo sp) W -> ACEIL <= lo -> sp <= USTACK_TOP ->
  AHEAP Σ OW LB m'.
Proof.
  intros Σ st OW LB PL EA SPX m m' W lo sp HEAP PARTS FROK MU WM HW CEIL SPT. eapply AH_frame; [exact HEAP| exact MU| exact WM|].
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[(b & Hb & H1 & H2)|(r & a & HA & NE & H1 & H2)]]; cbn [fst snd] in *.
  - left. cbn. lia.
  - right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn. auto.
  - destruct (w_lib_struct_cases _ _ _ _ _ _ _ _ PARTS FROK HA NE) as [(b & Hb & B1 & B2)|(HF & F1 & F2)].
    + right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn. lia.
    + left. cbn. destruct FROK as (_ & CSP & _). lia.
Qed.

Lemma seg_ax_pres : forall Σ st OW LB PL EA SPX m m' W lo sp X,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX USTACK_TOP ->
  munch W m m' -> Forall (w_lib st OW PL lo sp) W -> ACEIL <= lo -> lo <= sp ->
  (forall b x, In b OW -> blk_addr b <= x < blk_addr b + blk_size b -> client_static x -> rin_ivs X x) ->
  (forall x, rin_ivs (pl_frames PL) x -> rin_ivs X x) ->
  ax_pres LB sp X m m'.
Proof.
  intros Σ st OW LB PL EA SPX m m' W lo sp X HEAP PARTS FROK MU HW CEIL LOSP HCS HFR. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a [HX Hc]. pose proof (AH_nodup _ _ _ _ HEAP) as ND. clear MU.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
  assert (BLK : forall b, In b OW -> blk_addr b <= x -> y <= blk_addr b + blk_size b -> ~ (x <= a < y)).
  { intros b Hb H1 H2 Hx. pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & BI).
    destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _); lia| |].
    + apply HX. apply (HCS b a Hb); [lia | exact Hc].
    + assert (NE : blk_id b <> blk_id b').
      { rewrite map_app in ND. intros E. eapply (nodup_app_disj _ _ (blk_id b) ND); [apply in_map; exact Hb| rewrite E; apply in_map; exact Hb']. }
      pose proof (AH_disjoint_gen _ _ _ _ b b' HEAP ltac:(apply in_or_app; left; exact Hb) ltac:(apply in_or_app; right; exact Hb') NE). lia. }
  intros Hx. destruct Hiv as [[H1 H2]|[(b & Hb & H1 & H2)|(r & a' & HA & NE & H1 & H2)]]; cbn [fst snd] in *.
  - destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| |].
    + (* [comment removed for export] *)
      destruct Hc as [(l & h & Hin & Hr) _]. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _).
      unfold CLIENT_STATIC, SEGTOP_A in *. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
    + pose proof (AH_range_gen _ _ _ _ b' HEAP ltac:(apply in_or_app; right; exact Hb')) as (_ & _ & _ & BC & _). lia.
  - exact (BLK b Hb H1 H2 Hx).
  - destruct (w_lib_struct_cases _ _ _ _ _ _ _ _ PARTS FROK HA NE) as [(b & Hb & B1 & B2)|(HF & F1 & F2)].
    + apply (BLK b Hb); [lia| lia| exact Hx].
    + (* [comment removed for export] *)
      apply HX. apply HFR. apply rin_ivs_In. exists (a', a' + BN_STRUCT_SZ). split; [exact HF|]. cbn. unfold BN_STRUCT_SZ. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_not_static : forall Σ OW LB m b x, AHEAP Σ OW LB m -> In b OW -> blk_addr b <= x < blk_addr b + blk_size b -> client_static x -> False.
Proof.
  intros Σ OW LB m b x HEAP Hb Hx [(l & h & Hin & Hr) _].
  pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (B0 & _ & _ & _ & BI).
  unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Lemma seg_ax_pres' : forall Σ st OW LB PL EA SPX m m' W lo sp,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX USTACK_TOP ->
  munch W m m' -> Forall (w_lib st OW PL lo sp) W -> ACEIL <= lo -> lo <= sp -> ax_pres LB sp (XW PL) m m'.
Proof.
  intros Σ st OW LB PL EA SPX m m' W lo sp HEAP PARTS FROK MU HW CEIL LOSP. eapply seg_ax_pres; eauto.
  - intros b x Hb Hx Hc. exfalso. eapply blk_not_static; eauto.
  - intros x Hx. unfold XW. apply rin_ivs_app. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma seg_env : forall Σ st OW LB PL EA m m' W lo (sp : word) X0,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok PL (bv_unsigned sp) USTACK_TOP ->
  munch W m m' -> wmono ctasegs m m' -> Forall (w_lib st OW PL lo (bv_unsigned sp)) W -> ACEIL <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp <= USTACK_TOP ->
  ax_pres LB (bv_unsigned sp) (XW PL) X0 m ->
  AHEAP Σ OW LB m' /\ ax_pres LB (bv_unsigned sp) (XW PL) X0 m'.
Proof.
  intros Σ st OW LB PL EA m m' W lo sp X0 HEAP PARTS FROK MU WM HW CEIL LOSP SPT AX0.
  split; [eapply seg_heap; eauto|]. eapply ax_pres_trans; [exact AX0|]. eapply seg_ax_pres'; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma frames_al_empty : frames_al pl_empty.
Proof. intros iv Hiv. rewrite pl_frames_empty in Hiv. destruct Hiv. Qed.
Lemma frames_al_set_ctx : forall PL c, frames_al PL -> frames_al (pl_set_ctx PL c).
Proof. intros PL c H iv Hiv. apply H. exact Hiv. Qed.
Lemma frames_al_set_mont : forall PL mo, frames_al PL -> frames_al (pl_set_mont PL mo).
Proof. intros PL mo H iv Hiv. apply H. exact Hiv. Qed.

Lemma ref_at_siteA : forall Σ st OW LB PL EA SPX m r a,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX USTACK_TOP -> frames_al PL -> ref_at st OW PL r a -> r <> ROne ->
  a mod 8 = 0 /\ acc ctasegs m a 24 /\ (a + 24 <= SHLO \/ SHHI <= a) /\ a + 24 <= USTACK_TOP.
Proof.
  intros Σ st OW LB PL EA SPX m r a HEAP PARTS FROK FAL HA NE. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  assert (BLK : forall q A n off, In (q, A, n) OW -> a = A + off -> 0 <= off -> off mod 8 = 0 -> off + 24 <= n ->
                a mod 8 = 0 /\ acc ctasegs m a 24 /\ (a + 24 <= SHLO \/ SHHI <= a) /\ a + 24 <= USTACK_TOP).
  { intros q A n off Hin Ea Hoff Hm Hn. assert (INS : In (q, A, n) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
    pose proof (AH_okA _ _ _ _ _ _ _ HEAP Hin) as [A16 _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & BC & _).
    split; [subst a; clear - A16 Hm; Z.div_mod_to_equations; lia|].
    split; [eapply (AH_acc_in _ _ _ _ (q, A, n) a 24 HEAP INS); cbn [blk_addr blk_size fst snd]; lia|].
    pose proof (AH_offsh _ _ _ _ (q, A, n) HEAP INS) as O. cbn [blk_addr blk_size fst snd] in O. unfold STACK_WIN in C3. lia. }
  pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
  destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
  - eapply (BLK q a n 0); [exact Hin| lia| lia| reflexivity| unfold BN_STRUCT_SZ in Hn; lia].
  - eapply (BLK qm am MONT_CTX_SZ (24 * Z.of_nat (r - RMontRR))); [exact Hin| exact Ea| lia| replace (24 * Z.of_nat (r - RMontRR)) with (3 * Z.of_nat (r - RMontRR) * 8) by lia; apply Z_mod_mult| unfold MONT_CTX_SZ; lia].
  - eapply (BLK q H ITEM_SZ (24 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat)); [exact Hin| exact Ea| lia| replace (24 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat) with (3 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat * 8) by lia; apply Z_mod_mult|].
    unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. nia.
  - destruct FROK as (PLF & CSP & _). destruct (PLF _ HF) as [X Y]. cbn [fst snd] in X, Y. unfold BN_STRUCT_SZ in Y.
    split; [exact (FAL _ HF)|]. split; [|split; [|lia]].
    + destruct HEAP as (HART & HSP0 & _). apply (af_acc_stack RT AF Σ m a 24 HART); [| lia]. unfold BnHeapA.ACEIL in CSP. rewrite HSP0. lia.
    + right. unfold BnHeapA.ACEIL, SHHI in *. lia.
  - exfalso. exact (NE Er).
Qed.

(* [comment removed for export] *)
Lemma ref_at_inbA : forall Σ st OW LB PL EA m r a,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> pl_frames PL = [] -> ref_at st OW PL r a -> r <> ROne ->
  exists q A n, In (q, A, n) OW /\ A <= a /\ a + 24 <= A + n.
Proof.
  intros Σ st OW LB PL EA m r a HEAP PARTS NOFR HA NE. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
  destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
  - exists q, a, n. split; [exact Hin|]. unfold BN_STRUCT_SZ in Hn. lia.
  - exists qm, am, MONT_CTX_SZ. split; [exact Hin|]. unfold MONT_CTX_SZ in *. lia.
  - exists q, H, ITEM_SZ. split; [exact Hin|]. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. nia.
  - exfalso. rewrite NOFR in HF. exact HF.
  - exfalso. exact (NE Er).
Qed.

Lemma ref_at_al8A : forall Σ st OW LB PL EA m r a,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> pl_frames PL = [] -> ref_at st OW PL r a -> r <> ROne -> a mod 8 = 0.
Proof.
  intros Σ st OW LB PL EA m r a HEAP PARTS NOFR HA NE. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  assert (BLK : forall q A n off, In (q, A, n) OW -> a = A + off -> off mod 8 = 0 -> a mod 8 = 0).
  { intros q A n off Hin Ea Hm. pose proof (AH_okA _ _ _ _ _ _ _ HEAP Hin) as [A16 _]. subst a. clear - A16 Hm. Z.div_mod_to_equations. lia. }
  pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
  destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
  - eapply (BLK q a n 0); [exact Hin| lia| reflexivity].
  - eapply (BLK qm am MONT_CTX_SZ (24 * Z.of_nat (r - RMontRR))); [exact Hin| exact Ea| replace (24 * Z.of_nat (r - RMontRR)) with (3 * Z.of_nat (r - RMontRR) * 8) by lia; apply Z_mod_mult].
  - eapply (BLK q H ITEM_SZ (24 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat)); [exact Hin| exact Ea| replace (24 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat) with (3 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat * 8) by lia; apply Z_mod_mult].
  - exfalso. rewrite NOFR in HF. exact HF.
  - exfalso. exact (NE Er).
Qed.

(* [comment removed for export] *)
Lemma pl_frames_no_framebuf : forall PL r a d, pl_wf PL -> pl_frames PL = [] -> pl_bn PL r = Some (PFrameBuf a d) -> False.
Proof.
  intros PL r a d WF NOFR Eb. pose proof (proj1 WF r _ Eb) as (Hr & _).
  assert (HIn : In (a, a + BN_STRUCT_SZ) (pl_frames PL)).
  { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact Hr| left; reflexivity]. }
  rewrite NOFR in HIn. exact HIn.
Qed.

Lemma bn_arr_nofr : forall PL r m OW D b, pl_wf PL -> pl_frames PL = [] -> r <> ROne ->
  bn_arr m OW (pl_of PL r) D b -> ApBnRepA.bn_arr m OW D b.
Proof.
  intros PL r m OW D b WF NOFR NE ARR. unfold bn_arr in ARR. unfold ApBnRepA.bn_arr. destruct (bn_d b) as [p|]; [exact ARR|].
  destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try exact ARR.
  - exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
    exact (pl_frames_no_framebuf PL r x d WF NOFR Eb).
  - exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
    exact (proj2 (proj2 (proj2 (proj1 WF r _ Eb)))).
Qed.

Lemma bn_arr_of_nofr : forall PL r m OW D b, pl_wf PL -> pl_frames PL = [] -> r <> ROne ->
  ApBnRepA.bn_arr m OW D b -> bn_arr m OW (pl_of PL r) D b.
Proof.
  intros PL r m OW D b WF NOFR NE ARR. unfold ApBnRepA.bn_arr in ARR. unfold bn_arr. destruct (bn_d b) as [p|]; [exact ARR|].
  destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try exact ARR.
  - exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
    exact (pl_frames_no_framebuf PL r x d WF NOFR Eb).
  - exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
    exact (proj2 (proj2 (proj2 (proj1 WF r _ Eb)))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma call_okA : forall Σ OW LB m lo sp',
  AHEAP Σ OW LB m -> stk ctasegs m lo sp' -> ACEIL <= lo -> lo + RT_STACK <= sp' -> sp' + 16 <= USTACK_TOP -> sp' mod 16 = 0 ->
  call_ok RT Σ m (Z_to_bv 64 sp') lo.
Proof.
  intros Σ OW LB m lo sp' HEAP ST CEIL LO TOP M16. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK in *; lia).
  unfold call_ok. rewrite ESP. destruct HEAP as (_ & HS & _). rewrite HS. fold ACEIL.
  split; [exact ST|]. split; [exact CEIL|]. split; [exact LO|]. split; [exact TOP | exact M16].
Qed.

End WithRT.
