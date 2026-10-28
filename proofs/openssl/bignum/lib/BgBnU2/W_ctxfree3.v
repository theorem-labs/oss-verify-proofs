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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG BnBase BnModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnRep W_crypto W_small W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3 W_alloc3 W_ctx3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition pbn (m : mem) (L : list block) (a : Z) (b : bignum bptr) : Prop :=
  exists D, rw_cells bgusegs m a (bn_cells D b)
    /\ match bn_d b with
       | Some p => In (p, D, 8 * Z.of_nat (bn_dmax b)) L /\ u64arr bgusegs m D (wlimbs (bn_buf b))
       | None => D = 0
       end
    /\ Z.of_nat (bn_dmax b) <= 512 /\ bn_flags b = 0.

Fixpoint pbns (m : mem) (L : list block) (a : Z) (l : list (bignum bptr)) : Prop :=
  match l with [] => True | b :: l' => pbn m L a b /\ pbns m L (a + 24) l' end.

Fixpoint pitems (m : mem) (L : list block) (items : list bptr) (Hs : list Z) (vals : list (bignum bptr)) (prev : Z) : Prop :=
  match items, Hs with
  | [], [] => True
  | q :: items', H :: Hs' =>
      In (q, H, 400) L /\ (16 <= length vals)%nat /\ pbns m L H (firstn 16 vals)
      /\ rw_cells bgusegs m (H + 384) [C8 (wz prev); C8 (wz (hd 0 Hs'))]
      /\ pitems m L items' Hs' (skipn 16 vals) H
  | _, _ => False
  end.

Definition val_ids (vs : list (bignum bptr)) : list bptr :=
  flat_map (fun b => match bn_d b with Some p => [p] | None => [] end) vs.
Fixpoint item_ids (items : list bptr) (vals : list (bignum bptr)) : list bptr :=
  match items with
  | [] => []
  | q :: items' => val_ids (firstn 16 vals) ++ q :: item_ids items' (skipn 16 vals)
  end.
Definition opt_ids (o : option bptr) : list bptr := match o with Some p => [p] | None => [] end.
Definition ctx_free_ids (oi : option bptr) (items : list bptr) (vals : list (bignum bptr)) (qc : bptr) : list bptr :=
  opt_ids oi ++ item_ids items vals ++ [qc].

Fixpoint lfrees {X : Type} (ps : list bptr) (k : lprog X) : lprog X :=
  match ps with [] => k | p :: ps' => LFree p (lfrees ps' k) end.
Fixpoint lb_remove_list (ps : list bptr) (L : list block) : list block :=
  match ps with [] => L | p :: ps' => lb_remove_list ps' (lb_remove p L) end.

Lemma lfrees_app : forall {X} (l1 l2 : list bptr) (k : lprog X), lfrees (l1 ++ l2) k = lfrees l1 (lfrees l2 k).
Proof. intros X l1 l2 k. induction l1 as [|p l1 IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma lb_remove_list_app : forall l1 l2 L, lb_remove_list (l1 ++ l2) L = lb_remove_list l2 (lb_remove_list l1 L).
Proof. intros l1. induction l1 as [|p l1 IH]; intros l2 L; [reflexivity|]. cbn. apply IH. Qed.
Lemma lb_remove_list_incl : forall ps L b, In b (lb_remove_list ps L) -> In b L.
Proof. intros ps. induction ps as [|p ps IH]; intros L b Hb; [exact Hb|]. cbn in Hb. eapply lb_remove_incl. eapply IH. exact Hb. Qed.
Lemma lb_remove_list_In : forall ps L b, In b L -> ~ In (blk_id b) ps -> In b (lb_remove_list ps L).
Proof.
  intros ps. induction ps as [|p ps IH]; intros L b Hb Hn; [exact Hb|]. cbn. apply IH.
  - apply (proj2 (lb_remove_In p L b)). split; [exact Hb|]. intros E. apply Hn. left. symmetry. exact E.
  - intros Hi. apply Hn. right. exact Hi.
Qed.

Lemma val_ids_cons : forall b vs, val_ids (b :: vs) = opt_ids (bn_d b) ++ val_ids vs.
Proof. intros b vs. reflexivity. Qed.

Lemma NoDup_app_r : forall (l1 l2 : list bptr), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  intros l1 l2 H. induction l1 as [|x l1 IH]; [exact H|]. cbn in H. apply List.NoDup_cons_iff in H. apply IH. exact (proj2 H).
Qed.
Lemma NoDup_app_disj : forall (l1 l2 : list bptr) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros l1 l2 x H. induction l1 as [|y l1 IH]; intros H1 H2; [exact H1|]. cbn in H. apply List.NoDup_cons_iff in H. destruct H as [Hy H].
  destruct H1 as [<-|H1]; [apply Hy; apply in_app_iff; right; exact H2| exact (IH H H1 H2)].
Qed.

Lemma val_ids_In : forall vs b p, In b vs -> bn_d b = Some p -> In p (val_ids vs).
Proof.
  intros vs. induction vs as [|b0 vs IH]; intros b p Hb Ed; [exact Hb|]. rewrite val_ids_cons. apply in_or_app.
  destruct Hb as [<-|Hb]; [left; rewrite Ed; left; reflexivity| right; eapply IH; [exact Hb| exact Ed]].
Qed.

Lemma pbns_transport : forall l m m' L L' (P : Z -> Prop) a,
  pbns m L a l -> agree_on P m m' ->
  (forall b p D, In b l -> bn_d b = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax b)) L ->
                 In (p, D, 8 * Z.of_nat (bn_dmax b)) L' /\ forall x, D <= x < D + 8 * Z.of_nat (bn_dmax b) -> P x) ->
  (forall x, a <= x < a + 24 * Z.of_nat (length l) -> P x) ->
  pbns m' L' a l.
Proof.
  intros l. induction l as [|b l IH]; intros m m' L L' P a PB AG HL HC; [exact I|].
  cbn [pbns] in PB |- *. cbn [length] in HC. destruct PB as [(D & BN & ARR & DM & FL) PB]. split.
  - exists D. split; [| split; [| split; [exact DM| exact FL]]].
    + eapply rw_cells_agree; [exact AG| exact BN|]. intros x Hx. cbn in Hx. apply HC. lia.
    + destruct (bn_d b) as [p|] eqn:Ed; [| exact ARR]. destruct ARR as [IND U].
      destruct (HL b p D ltac:(left; reflexivity) Ed IND) as [IND' HP]. split; [exact IND'|].
      eapply u64arr_agree; [exact AG| exact U|]. intros x Hx. rewrite wlimbs_length in Hx. apply HP. unfold bn_dmax. lia.
  - eapply IH; [exact PB| exact AG| |].
    + intros b' p D' Hb' Ed IND. exact (HL b' p D' ltac:(right; exact Hb') Ed IND).
    + intros x Hx. apply HC. lia.
Qed.

Lemma item_ids_cons : forall q items vals, item_ids (q :: items) vals = val_ids (firstn 16 vals) ++ q :: item_ids items (skipn 16 vals).
Proof. intros. reflexivity. Qed.

Lemma pitems_transport : forall items m m' L L' (P : Z -> Prop) Hs vals prev,
  pitems m L items Hs vals prev -> agree_on P m m' ->
  (forall blk, In blk L -> In (blk_id blk) (item_ids items vals) ->
               In blk L' /\ forall x, blk_addr blk <= x < blk_addr blk + blk_size blk -> P x) ->
  pitems m' L' items Hs vals prev.
Proof.
  intros items. induction items as [|q items IH]; intros m m' L L' P Hs vals prev PI AG HL; destruct Hs as [|H Hs]; cbn [pitems] in PI |- *; try exact PI.
  destruct PI as (INQ & L16 & PB & LNK & PI). rewrite item_ids_cons in HL.
  destruct (HL _ INQ ltac:(cbn [blk_id fst snd]; apply in_or_app; right; left; reflexivity)) as [INQ' CL]. cbn [blk_addr blk_size fst snd] in CL.
  split; [exact INQ'|]. split; [exact L16|]. split; [| split].
  - eapply pbns_transport; [exact PB| exact AG| |].
    + intros b p D Hb Ed IND. destruct (HL _ IND) as [IND' HP]; [cbn [blk_id fst snd]; apply in_or_app; left; eapply val_ids_In; [exact Hb| exact Ed]|].
      cbn [blk_addr blk_size fst snd] in HP. split; [exact IND'| exact HP].
    + intros x Hx. rewrite length_firstn in Hx. apply CL. lia.
  - eapply rw_cells_agree; [exact AG| exact LNK|]. intros x Hx. cbn in Hx. apply CL. lia.
  - eapply IH; [exact PI| exact AG|]. intros blk Hb Hi. apply HL; [exact Hb|]. apply in_or_app. right. right. exact Hi.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition BN_CTX_FREE : Z := 0x100afc.

  Definition BN_CTX_FREE_STACK : Z := 64 + BN_CLEAR_FREE_STACK.
  Definition CTXF_STR : Z := 0x2bf0b.

  Definition vl_post (sp gp s0 s1 s2 s4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L' : list block) (aend : Z) (lo B : Z) (errv : word) (m : mem) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz aend) s4 (wz 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x100b88) fc None m' (seg_rom bgusegs)
      /\ mem_inv bgusegs m' /\ stk bgusegs m' lo (bv_unsigned sp)
      /\ rw_cells bgusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
      /\ rheap_pres L' (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ RHEAP s' L' m' /\ crypto_statics m'.

  Lemma vals_loop : forall {X : Type} (vs : list (bignum bptr))
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp gp s0 s1 s2 s4 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (q : bptr) (H a lo B : Z) (errv : word) (EX : list bptr)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    pbns m L a vs ->
    (1 <= length vs <= 16)%nat -> a = H + 24 * (16 - Z.of_nat (length vs)) ->
    RHEAP s L m -> In (q, H, 400) L ->
    List.NoDup (val_ids vs ++ EX) -> In q EX ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_CLEAR_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> crypto_statics m ->
    s4 = wz (-24) ->
    (forall s' ms', vl_post sp gp s0 s1 s2 s4 s6 s7 s8 s9 s10 s11 F fc s (lb_remove_list (val_ids vs) L) (a + 24 * Z.of_nat (length vs)) lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (lfrees (val_ids vs) k)) s Q
      (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz a) s4 (wz (Z.of_nat (length vs))) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x100b68) fc None m (seg_rom bgusegs)).
  Proof.
    intros X vs. induction vs as [|b vs IH]; intros until Q; intros PB LEN Ea HEAP INQ ND INEX AUX SPB ST CEIL GLO LO ERR MI CS -> K; [cbn in LEN; lia|].
    cbn [length] in LEN, Ea, K |- *. cbn [pbns] in PB. destruct PB as [(D & BN & ARR & DM & FL0) PB].
    unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP INQ) as (QA0 & QA16 & _ & QAC & QAI). cbn [blk_addr blk_size fst snd] in QA0, QA16, QAC, QAI.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_cells in BN.

    assert (TAIL : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (s' : PState),
      let L1 := lb_remove_list (opt_ids (bn_d b)) L in
      mem_inv bgusegs m' -> stk bgusegs m' lo (bv_unsigned sp) -> rw_cells bgusegs m' 3346164 [C4 errv] -> rauxv_ok m' B ->
      rheap_pres L1 (bv_unsigned sp) m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> RHEAP s' L1 m' -> crypto_statics m' ->
      pbns m' L1 (a + 24) vs ->
      impl bgusegs (at_node bgusegs) (interp (lfrees (val_ids vs) k) s') (epost (fun p : X * PState => Q p.1 p.2))
        (MS (mkR ra' sp gp (Z_to_bv 64 RATP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 a) (Z_to_bv 64 (-24))
                 (Z_to_bv 64 (Z.of_nat (S (length vs)))) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x100b78) fc None m' (seg_rom bgusegs))).
    { intros until s'. intros L1 MI' ST' ERR' AUX' HP' FA' SO' HEAP' CS' PB'.
      iprefix. step. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; rewrite ?unsigned_lit_wrap in KC; lia|]. clear KC.
      step.
      rewrite (unsigned_lit (Z.of_nat (S (length vs)))) by lia. rewrite bk_swrap32_small by lia.
      replace (Z.of_nat (S (length vs)) + -1) with (Z.of_nat (length vs)) by lia.
      step. replace (a + 24) with (H + 24 * (16 - Z.of_nat (length vs))) in PB' |- * by lia.
      step. if_cases KB; zify_cond KB.
      -
        rewrite ?unsigned_lit in KB by lia.
        ihere.
        lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
          lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp gp s0 s1 s2 (Z_to_bv 64 (-24)) s6 s7 s8 s9 s10 s11 F fc m' s' L1 q H _ lo B errv EX);
          [ exact PB' | lia | reflexivity | exact HEAP' | | | exact INEX | exact AUX' | exact SPB | exact ST' | exact CEIL | unfold GLOBALS_TOP; lia | lia
          | unfold LX_ERRNO, RATP; exact ERR' | exact MI' | exact CS' | reflexivity | ].
        + unfold L1. apply lb_remove_list_In; [exact INQ|]. cbn [blk_id fst snd]. intros Hi.
          rewrite val_ids_cons in ND. eapply (NoDup_app_disj _ _ q ND); [apply in_or_app; left; exact Hi| exact INEX].
        + rewrite val_ids_cons, <- app_assoc in ND. exact (NoDup_app_r _ _ ND).
        + intros s'' ms'' PO. apply K. unfold vl_post in PO |- *.
          destruct PO as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & m'' & -> & MI'' & ST'' & ERR'' & AUX'' & HP'' & FA'' & SO'' & HEAP'' & CS'').
          do 16 eexists. exists m''. split; [replace (a + 24 * Z.of_nat (S (length vs))) with (H + 24 * (16 - Z.of_nat (length vs)) + 24 * Z.of_nat (length vs)) by lia; reflexivity|].
          split; [exact MI''|]. split; [exact ST''|]. split; [exact ERR''|]. split; [exact AUX''|].
          split. { rewrite val_ids_cons, lb_remove_list_app. fold L1. eapply rheap_pres_trans; [| exact HP''].
                   eapply rheap_pres_weaken; [exact HP'| lia| intros bb Hbb; eapply lb_remove_list_incl; exact Hbb]. }
          split; [rewrite FA''; exact FA'|]. split; [rewrite SO''; exact SO'|]. split; [| exact CS''].
          rewrite val_ids_cons, lb_remove_list_app. exact HEAP''.
      -
        rewrite ?unsigned_lit in KB by lia. assert (vs = []) as -> by (destruct vs; [reflexivity| cbn [length] in KB; lia]).
        cbn [val_ids flat_map lfrees lb_remove_list app length Z.of_nat] in K |- *.
        ihere.
        lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
          lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
        change (Z.of_nat 0) with 0 in *. change (Z.of_nat 1) with 1 in *.
        replace (H + 24 * (16 - 0)) with (a + 24 * 1) by lia.
        apply K. unfold vl_post, MallocRep.wz. do 16 eexists. exists m'. split; [reflexivity|].
        split; [exact MI'|]. split; [exact ST'|]. split; [unfold LX_ERRNO, RATP; exact ERR'|]. split; [exact AUX'|].
        split. { rewrite app_nil_r. exact HP'. }
        split; [exact FA'|]. split; [exact SO'|]. split; [rewrite app_nil_r; exact HEAP'| exact CS']. }
    rewrite val_ids_cons in K, ND |- *.
    unfold implM. iprefix.
    step.
    destruct (bn_d b) as [pd|] eqn:Ed; try rewrite Ed in ARR; try rewrite Ed in TAIL; try rewrite Ed in ND; try rewrite Ed in K; cbn [opt_ids app lfrees lb_remove_list] in TAIL, K, ND |- *.
    -
      destruct ARR as [IND U0].
      pose proof (LH_block_range _ _ _ _ HEAP IND) as (PD0 & _ & _ & PDC & _). cbn [blk_addr blk_size fst snd] in PD0, PDC.
      assert (NEq : q <> pd).
      { intros E. apply List.NoDup_cons_iff in ND. apply (proj1 ND). apply in_or_app. right. rewrite <- E. exact INEX. }
      unfold MallocRep.wz. step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
      step. step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
      eapply (BN_clear_free_walk_d HF) with (A := a) (D := D) (b := b) (pd := pd) (L := L) (B := B) (lo := lo) (errv := errv);
        [ exact HEAP | exact IND
        | intros x Hx; right; right; exists (q, H, 400); split; [apply (proj2 (lb_remove_In _ _ _)); split; [exact INQ| cbn [blk_id fst snd]; exact NEq]| cbn [blk_addr blk_size fst snd]; lia]
        | exact AUX | exact SPB | exact ST | exact CEIL | unfold GLOBALS_TOP; lia | unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
        | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS | unfold bn_cells; exact BN | exact U0
        | rewrite FL0; lia | rewrite FL0; reflexivity | rewrite FL0; reflexivity | rewrite FL0; reflexivity | lia
        | left; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia | lia | lia | lia | reflexivity | ].
      intros st1 ms1 PO BNa. unfold cfree_post in PO.
      destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                      & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
      replace (ret_pc (Z_to_bv 64 1051512)) with (Z_to_bv 64 1051512) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (CS4 : crypto_statics m4).
      { eapply crypto_statics_agree; [exact (agree_of_heap_pres _ _ _ _ HP4)| intros x Hx; apply libw_client; exact Hx| exact CS]. }
      unfold MallocRep.wz in TAIL. apply TAIL with (s' := st1);
        [ exact MI4 | exact ST4 | unfold LX_ERRNO, RATP in ERR4; exact ERR4 | exact AUX4 | exact HP4 | exact FA4 | exact SO4 | exact HEAP4 | exact CS4 | ].
      eapply pbns_transport; [exact PB| exact (agree_of_heap_pres _ _ _ _ HP4)| |].
      + intros b' p' D' Hb' Ed' IND'.
        assert (IND2 : In (p', D', 8 * Z.of_nat (bn_dmax b')) (lb_remove pd L)).
        { apply (proj2 (lb_remove_In _ _ _)). split; [exact IND'|]. cbn [blk_id fst snd]. intros E.
          apply List.NoDup_cons_iff in ND. apply (proj1 ND). apply in_or_app. left. rewrite <- E. eapply val_ids_In; [exact Hb'| exact Ed']. }
        split; [exact IND2|]. intros x Hx. right. right. exists (p', D', 8 * Z.of_nat (bn_dmax b')). split; [exact IND2|]. cbn [blk_addr blk_size fst snd]. lia.
      + intros x Hx. right. right. exists (q, H, 400). split; [apply (proj2 (lb_remove_In _ _ _)); split; [exact INQ| cbn [blk_id fst snd]; exact NEq]|].
        cbn [blk_addr blk_size fst snd]. lia.
    -
      subst D. unfold MallocRep.wz. step. if_cases KA; zify_cond KA; [| exfalso; rewrite ?unsigned_lit in KA by lia; lia]. clear KA.
      ihere. unfold MallocRep.wz in TAIL. apply TAIL with (s' := s);
        [ exact MI | exact ST | exact ERR | exact AUX | intros x Hx Hc; split; [reflexivity| auto] | reflexivity | reflexivity | exact HEAP | exact CS | exact PB ].
  Qed.

  Definition ctxf_cells (hd0 cu : word) (tl pu ps de ss us es tm fl lc : word) : list cell :=
    [C8 hd0; C8 cu; C8 tl; C4 pu; C4 ps; C8 (wz 0); C4 de; C4 ss; C4 us; C4 es; C4 tm; C4 fl; C8 lc].

  Definition il_post (sp gp s0 s1 s2 s4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L' : list block) (qc : bptr) (A : Z) (tl pu ps de ss us es tm fl lc : word) (lo B : Z) (errv : word) (m : mem) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3 s5 m',
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x100bb8) fc None m' (seg_rom bgusegs)
      /\ mem_inv bgusegs m' /\ stk bgusegs m' lo (bv_unsigned sp)
      /\ rw_cells bgusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
      /\ rheap_pres (lb_remove qc L') (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ RHEAP s' L' m' /\ crypto_statics m'
      /\ rw_cells bgusegs m' A (ctxf_cells (wz 0) (wz 0) tl pu ps de ss us es tm fl lc).

  Lemma items_loop : forall {X : Type} (items : list bptr) (Hs : list Z) (vals : list (bignum bptr)) (prev : Z)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp gp s0 s5 s6 s7 s8 s9 s10 s11 : word) (cu tl pu ps de ss us es tm fl lc : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (qc : bptr) (A lo B : Z) (errv : word) (EX : list bptr)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    pitems m L items Hs vals prev -> items <> [] ->
    RHEAP s L m -> In (qc, A, 72) L ->
    List.NoDup (item_ids items vals ++ EX) -> In qc EX ->
    rw_cells bgusegs m A (ctxf_cells (wz (hd 0 Hs)) cu tl pu ps de ss us es tm fl lc) ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_CLEAR_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> crypto_statics m ->
    (forall s' ms', il_post sp gp s0 (wz A) (wz CTXF_STR) (wz (-24)) s6 s7 s8 s9 s10 s11 F fc s (lb_remove_list (item_ids items vals) L) qc A tl pu ps de ss us es tm fl lc lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (lfrees (item_ids items vals) k)) s Q
      (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz CTXF_STR) (wz (hd 0 Hs)) (wz (-24)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x100b5c) fc None m (seg_rom bgusegs)).
  Proof.
    intros X items. induction items as [|q items IH]; intros until Q; intros PI NE HEAP INQC ND INEX CX AUX SPB ST CEIL GLO LO ERR MI CS K; [exfalso; apply NE; reflexivity|].
    destruct Hs as [|H Hs]; cbn [pitems] in PI; [contradiction|]. cbn [hd] in CX |- *.
    destruct PI as (INQ & L16 & PB & LNK & PI). rewrite item_ids_cons in ND, K |- *.
    unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, GLOBALS_TOP, CTXF_STR, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP INQ) as (QA0 & QA16 & _ & QAC & QAI). cbn [blk_addr blk_size fst snd] in QA0, QA16, QAC, QAI.
    pose proof (LH_block_range _ _ _ _ HEAP INQC) as (CA0 & CA16 & _ & CAC & CAI). cbn [blk_addr blk_size fst snd] in CA0, CA16, CAC, CAI.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (LF : length (firstn 16 vals) = 16%nat) by (rewrite length_firstn; lia).
    assert (NDX : forall x, In x (val_ids (firstn 16 vals)) -> In x (q :: item_ids items (skipn 16 vals) ++ EX) -> False).
    { intros x H1 H2. eapply (NoDup_app_disj _ _ x); [rewrite <- app_assoc in ND; exact ND| exact H1| exact H2]. }

    rewrite lfrees_app.
    assert (HA8 : H mod 8 = 0) by lia.
    unfold implM. iprefix. step. ub_chk. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
    replace (Z_to_bv 64 16) with (Z_to_bv 64 (Z.of_nat (length (firstn 16 vals)))) by (f_equal; lia).
    eapply (vals_loop (firstn 16 vals)) with (a := H) (q := q) (H := H) (L := L) (B := B) (lo := lo) (errv := errv) (EX := q :: item_ids items (skipn 16 vals) ++ EX);
      [ exact PB | rewrite LF; lia | lia | exact HEAP | exact INQ | rewrite <- app_assoc in ND; exact ND | left; reflexivity
      | exact AUX | exact SPB | exact ST | exact CEIL | unfold GLOBALS_TOP; lia | unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
      | unfold LX_ERRNO, RATP; exact ERR | exact MI | exact CS | reflexivity | ].
    intros st1 ms1 PO. unfold vl_post in PO.
    destruct PO as (ra1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & -> & MI1 & ST1 & ERR1 & AUX1 & HP1 & FA1 & SO1 & HEAP1 & CS1).
    set (L1 := lb_remove_list (val_ids (firstn 16 vals)) L) in *.

    assert (KEEP1 : forall blk, In blk L -> In (blk_id blk) (q :: item_ids items (skipn 16 vals) ++ EX) -> In blk L1).
    { intros blk Hb Hi. unfold L1. apply lb_remove_list_In; [exact Hb|]. intros Hv. exact (NDX _ Hv Hi). }
    assert (INQC1 : In (qc, A, 72) L1) by (apply KEEP1; [exact INQC| right; apply in_or_app; right; exact INEX]).
    assert (INQ1 : In (q, H, 400) L1) by (apply KEEP1; [exact INQ| left; reflexivity]).
    assert (CLc : forall LL x, In (qc, A, 72) LL -> A <= x < A + 72 -> rclient_addr LL (bv_unsigned sp) x).
    { intros LL x Hin Hx. right. right. exists (qc, A, 72). split; [exact Hin|]. cbn [blk_addr blk_size fst snd]. lia. }
    assert (CLq : forall LL x, In (q, H, 400) LL -> H <= x < H + 400 -> rclient_addr LL (bv_unsigned sp) x).
    { intros LL x Hin Hx. right. right. exists (q, H, 400). split; [exact Hin|]. cbn [blk_addr blk_size fst snd]. lia. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP1)) in CX; [| intros x Hx; cbn in Hx; apply CLc; [exact INQC1| lia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP1)) in LNK; [| intros x Hx; cbn in Hx; apply CLq; [exact INQ1| lia]].
    assert (PI1 : pitems m1 L1 items Hs (skipn 16 vals) H).
    { eapply pitems_transport; [exact PI| exact (agree_of_heap_pres _ _ _ _ HP1)|]. intros blk Hb Hi.
      assert (Hb1 : In blk L1) by (apply KEEP1; [exact Hb| right; apply in_or_app; left; exact Hi]).
      split; [exact Hb1|]. intros x Hx. right. right. exists blk. split; [exact Hb1| exact Hx]. }
    clear PB HEAP AUX MI CS ERR ST PI.
    unfold LX_ERRNO, RATP in ERR1. change (3346328 - 164) with 3346164 in ERR1.
    unfold ctxf_cells, MallocRep.wz in CX.
    pose proof (munch_refl [(A + 8, A + 16)]%Z m1) as MU1. pose proof (wmono_refl bgusegs m1) as WM1.

    unfold MallocRep.wz. unfold implM. iprefix. cbn [lfrees].
    step. ub_chk. step. ub_chk. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1' end.
    assert (ND1 : List.NoDup (map blk_id L1)) by (eapply LH_nodup; exact HEAP1).

    assert (OUTc : forall LL W x, (forall blk, In blk LL -> In blk L1 /\ blk_id blk <> qc) -> (forall y, ~ (A <= y < A + 72) \/ bv_unsigned sp <= y -> outside W y) ->
                   0 <= x < 2^64 -> rclient_addr LL (bv_unsigned sp) x -> outside W x).
    { intros LL W x HLL HW Hx Hc. apply HW. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [right; lia| left; lia|].
      destruct (HLL _ Hb') as [Hb1 Hne].
      pose proof (LH_disjoint _ _ _ (qc, A, 72) b' HEAP1 INQC1 Hb1 ltac:(intros E; apply Hne; symmetry; exact E)) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ. left. lia. }
    assert (HEAP1' : RHEAP st1 L1 m1').
    { eapply LH_frame; [exact HEAP1| exact MU1| exact WM1|]. constructor; [| constructor].
      eapply (W_ok_block _ (qc, A, 72)); [exact INQC1| cbn; lia| cbn; lia]. }
    assert (AUX1' : rauxv_ok m1' B).
    { eapply rauxv_ok_frame; [exact AUX1| exact MU1| exact WM1|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1' : crypto_statics m1').
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU1 WM1)| | exact CS1].
      intros x Hx. cbn. split; [|exact I]. revert Hx. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (PI1' : pitems m1' L1 items Hs (skipn 16 vals) H).
    { eapply pitems_transport; [exact PI1| apply (agree_on_of_munch _ _ _ MU1 WM1)|]. intros blk Hb Hi. split; [exact Hb|].
      intros x Hx. assert (Hne : blk_id blk <> qc).
      { intros E. eapply (NoDup_app_disj _ _ qc ND); [| exact INEX]. apply in_or_app. right. right. rewrite <- E. exact Hi. }
      pose proof (LH_disjoint _ _ _ (qc, A, 72) blk HEAP1 INQC1 Hb ltac:(intros E; apply Hne; symmetry; exact E)) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ. cbn. split; [lia| exact I]. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
    eapply (CRYPTO_free_walk HF) with (p := q) (A := H) (n := 400) (L := L1) (B := B) (lo := lo) (errv := errv);
      [ exact HEAP1' | exact INQ1 | exact AUX1' | exact SPB | assumption | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; assumption | assumption | reflexivity | exact CS1' | reflexivity | ].
    intros st2 ms2 PO. unfold cfree_post in PO.
    destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m2
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & FA2 & SO2 & HEAP2).
    set (L2 := lb_remove q L1) in *.
    replace (ret_pc (Z_to_bv 64 1051564)) with (Z_to_bv 64 1051564) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (KEEP2 : forall blk, In blk L1 -> blk_id blk <> q -> In blk L2).
    { intros blk Hb Hne. unfold L2. apply (proj2 (lb_remove_In _ _ _)). split; [exact Hb| exact Hne]. }
    assert (NEqc : qc <> q).
    { intros E. eapply (NoDup_app_disj _ _ qc ND); [| exact INEX]. apply in_or_app. right. left. symmetry. exact E. }
    assert (INQC2 : In (qc, A, 72) L2) by (apply KEEP2; [exact INQC1| cbn [blk_id fst snd]; exact NEqc]).
    lazymatch goal with CXH : rw_cells bgusegs m1' A _ |- _ =>
      apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP2)) in CXH; [rename CXH into CX2| intros x Hx; cbn in Hx; apply CLc; [exact INQC2| lia]] end.
    assert (PI2 : pitems m2 L2 items Hs (skipn 16 vals) H).
    { eapply pitems_transport; [exact PI1'| exact (agree_of_heap_pres _ _ _ _ HP2)|]. intros blk Hb Hi.
      assert (Hb2 : In blk L2).
      { apply KEEP2; [exact Hb|]. intros E. pose proof ND as NDc. rewrite <- app_assoc in NDc. apply NoDup_app_r in NDc. cbn in NDc.
        apply List.NoDup_cons_iff in NDc. apply (proj1 NDc). apply in_or_app. left. rewrite <- E. exact Hi. }
      split; [exact Hb2|]. intros x Hx. right. right. exists blk. split; [exact Hb2| exact Hx]. }
    assert (CS2 : crypto_statics m2).
    { eapply crypto_statics_agree; [exact (agree_of_heap_pres _ _ _ _ HP2)| intros x Hx; apply libw_client; exact Hx| exact CS1']. }

    assert (HP02 : rheap_pres (lb_remove qc L2) (bv_unsigned sp) m m2).
    { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP1| lia| intros bb Hbb; eapply lb_remove_incl; eapply lb_remove_incl; exact Hbb]|].
      eapply rheap_pres_trans; [| eapply rheap_pres_weaken; [exact HP2| lia| intros bb Hbb; eapply lb_remove_incl; exact Hbb]].
      eapply heap_pres_of_munch; [exact MU1| exact WM1|]. intros x Hx Hc. eapply (OUTc (lb_remove qc L2)); [| | exact Hx| exact Hc].
      - intros blk Hb. pose proof (proj1 (lb_remove_In _ _ _) Hb) as [Hb' Hne]. split; [eapply lb_remove_incl; exact Hb'| exact Hne].
      - intros y Hy. cbn. split; [lia| exact I]. }
    clear HEAP1 HEAP1' AUX1 AUX1' CS1 CS1' PI1 PI1' MU1 WM1 HP1 HP2 KEEP1 INQ1 INQC1.
    unfold LX_ERRNO, RATP in ERR2. change (3346328 - 164) with 3346164 in ERR2. unfold MallocRep.wz.
    pose proof (munch_refl [(A, A + 8)]%Z m2) as MU2. pose proof (wmono_refl bgusegs m2) as WM2.

    unfold implM. iprefix.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2' end.
    assert (HEAP2' : RHEAP st2 L2 m2').
    { eapply LH_frame; [exact HEAP2| exact MU2| exact WM2|]. constructor; [| constructor].
      eapply (W_ok_block _ (qc, A, 72)); [exact INQC2| cbn; lia| cbn; lia]. }
    assert (AUX2' : rauxv_ok m2' B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS2' : crypto_statics m2').
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU2 WM2)| | exact CS2].
      intros x Hx. cbn. split; [|exact I]. revert Hx. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ND2 : List.NoDup (map blk_id L2)) by (eapply LH_nodup; exact HEAP2).
    assert (PI2' : pitems m2' L2 items Hs (skipn 16 vals) H).
    { eapply pitems_transport; [exact PI2| apply (agree_on_of_munch _ _ _ MU2 WM2)|]. intros blk Hb Hi. split; [exact Hb|].
      intros x Hx. assert (Hne : blk_id blk <> qc).
      { intros E. eapply (NoDup_app_disj _ _ qc ND); [| exact INEX]. apply in_or_app. right. right. rewrite <- E. exact Hi. }
      pose proof (LH_disjoint _ _ _ (qc, A, 72) blk HEAP2 INQC2 Hb ltac:(intros E; apply Hne; symmetry; exact E)) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ. cbn. split; [lia| exact I]. }
    assert (HP02' : rheap_pres (lb_remove qc L2) (bv_unsigned sp) m m2').
    { eapply rheap_pres_trans; [exact HP02|]. eapply heap_pres_of_munch; [exact MU2| exact WM2|].
      intros x Hx Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia| exact I]| split; [lia| exact I]|].
      pose proof (proj1 (lb_remove_In _ _ _) Hb') as [Hb2 Hne].
      pose proof (LH_disjoint _ _ _ (qc, A, 72) b' HEAP2 INQC2 Hb2 ltac:(intros E; apply Hne; symmetry; exact E)) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ. split; [lia| exact I]. }
    step. if_cases KB; zify_cond KB.
    -
      destruct items as [|q' items']; [| ].
      { destruct Hs; cbn [pitems] in PI2'; [| contradiction]. exfalso. apply KB. reflexivity. }
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
      eapply (IH Hs (skipn 16 vals) H) with (qc := qc) (L := L2) (B := B) (lo := lo) (errv := errv) (EX := EX);
        [ exact PI2' | intros E; discriminate E | exact HEAP2' | exact INQC2
        | pose proof ND as NDc; rewrite <- app_assoc in NDc; apply NoDup_app_r in NDc; cbn in NDc; apply List.NoDup_cons_iff in NDc; exact (proj2 NDc)
        | exact INEX | unfold ctxf_cells, MallocRep.wz; eassumption | exact AUX2' | exact SPB | assumption | exact CEIL | unfold GLOBALS_TOP; lia
        | unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
        | unfold LX_ERRNO, RATP; assumption | assumption | exact CS2' | ].
      intros st3 ms3 PO. apply K. unfold il_post in PO |- *.
      destruct PO as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & FA3 & SO3 & HEAP3 & CS3 & CX3).
      do 18 eexists. exists m3. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
      rewrite lb_remove_list_app. cbn [lb_remove_list]. fold L1. fold L2.
      split. { eapply rheap_pres_trans; [| exact HP3].
               eapply rheap_pres_weaken; [exact HP02'| lia|]. intros bb Hbb. pose proof (proj1 (lb_remove_In _ _ _) Hbb) as [Hb3 Hne].
               apply (proj2 (lb_remove_In _ _ _)). split; [eapply lb_remove_list_incl; exact Hb3| exact Hne]. }
      split; [rewrite FA3, FA2; exact FA1|]. split; [rewrite SO3, SO2; exact SO1|]. split; [exact HEAP3| split; [exact CS3| exact CX3]].
    -
      destruct items as [|q' items'].
      2: { destruct Hs as [|H' Hs']; cbn [pitems] in PI2'; [contradiction|]. destruct PI2' as (INQ' & _). exfalso.
           pose proof (LH_block_range _ _ _ _ HEAP2 INQ') as (Q0 & _ & _ & QC' & _). cbn [blk_addr blk_size fst snd hd] in Q0, QC', KB.
           change 18446744073709551615 with (Z.ones 64) in KB. rewrite Z.land_ones in KB by lia. rewrite Z.mod_small in KB by lia. lia. }
      destruct Hs; cbn [pitems] in PI2'; [| contradiction]. cbn [hd item_ids lfrees lb_remove_list] in K |- *.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
      apply K. unfold il_post. rewrite lb_remove_list_app. cbn [lb_remove_list]. fold L1. fold L2.
      do 18 eexists. exists m2'. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [unfold LX_ERRNO, RATP; assumption|]. split; [exact AUX2'|].
      split; [exact HP02'|]. split; [rewrite FA2; exact FA1|]. split; [rewrite SO2; exact SO1|]. split; [exact HEAP2'|]. split; [exact CS2'|].
      unfold ctxf_cells, MallocRep.wz. assumption.
  Qed.

  Definition ctx0_cells (hd0 cu : word) (tl pu ps : word) (ix : word) (de ss us es tm fl lc : word) : list cell :=
    [C8 hd0; C8 cu; C8 tl; C4 pu; C4 ps; C8 ix; C4 de; C4 ss; C4 us; C4 es; C4 tm; C4 fl; C8 lc].

  Lemma BN_CTX_free_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (qc : bptr) (oi : option bptr)
      (items : list bptr) (Hs : list Z) (vals : list (bignum bptr)) (prev : Z)
      (A IX : Z) (cu tl pu ps de ss us es tm fl lc : word) (lo B : Z) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    let ids := ctx_free_ids oi items vals qc in
    RHEAP s L m -> In (qc, A, 72) L ->
    rw_cells bgusegs m A (ctx0_cells (wz (hd 0 Hs)) cu tl pu ps (wz IX) de ss us es tm fl lc) ->
    match oi with Some qi => In (qi, IX, 128) L | None => IX = 0 end ->
    pitems m L items Hs vals prev ->
    List.NoDup ids ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_CTX_FREE_STACK ->
    rw_cells bgusegs m LX_ERRNO [C4 errv] -> mem_inv bgusegs m -> tp = wz RATP -> crypto_statics m ->
    a0 = wz A ->
    (forall s' ms', gfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove_list ids L) lo B errv m s' ms' ->
                    implM bgusegs (interp k) s' Q ms') ->
    implM bgusegs (interp (lfrees ids k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Q. intros ids HEAP INQC CX IDX PI ND AUX SPB ST CEIL GLO LO ERR MI -> CS -> K.
    unfold BN_CTX_FREE_STACK, BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, BN_CTX_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP INQC) as (CA0 & CA16 & _ & CAC & CAI). cbn [blk_addr blk_size fst snd] in CA0, CA16, CAC, CAI.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (CLc : forall LL SP x, In (qc, A, 72) LL -> A <= x < A + 72 -> rclient_addr LL SP x).
    { intros LL SP x Hin Hx. right. right. exists (qc, A, 72). split; [exact Hin|]. cbn [blk_addr blk_size fst snd]. lia. }
    unfold ids, ctx_free_ids in ND, K |- *. rewrite !lfrees_app. rewrite !lb_remove_list_app in K.
    assert (NIQC : ~ In qc (item_ids items vals)).
    { intros Hi. apply NoDup_app_r in ND. eapply (NoDup_app_disj _ _ qc ND); [exact Hi| left; reflexivity]. }
    unfold ctx0_cells in CX.
    unfold implM. iprefix.
    assert (CA8 : A mod 8 = 0) by lia.
    carve_frame 64%nat ST. do 9 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step. ub_chk. step. do 3 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros x Hx. cbn. split; [|exact I]. revert Hx. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (PI1 : pitems m1 L items Hs vals prev).
    { eapply pitems_transport; [exact PI| apply (agree_on_of_munch _ _ _ MU WM)|]. intros blk Hb Hi. split; [exact Hb|].
      intros x Hx. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & Bc & _). cbn. split; [lia| exact I]. }
    assert (CLI : forall LL x, (forall b, In b LL -> In b L) -> 0 <= x < 2^64 -> rclient_addr LL (bv_unsigned sp) x -> outside [(bv_unsigned sp - 64, bv_unsigned sp)] x).
    { intros LL x HLL Hx Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP (HLL _ Hb')) as (_ & _ & _ & B3' & _). lia. }
    clear PI AUX CS.

    assert (EXIT : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2 x3 x4 x5 fp : word) (m' : mem) (s' : PState) (L' : list block),
      mem_inv bgusegs m' -> stk bgusegs m' lo (bv_unsigned sp - 64) -> rw_cells bgusegs m' 3346164 [C4 errv] -> rauxv_ok m' B ->
      rheap_pres (lb_remove qc L') (bv_unsigned sp - 64) m1 m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> RHEAP s' L' m' -> crypto_statics m' ->
      In (qc, A, 72) L' -> (forall b, In b L' -> In b L) ->
      lb_remove qc L' = lb_remove_list [qc] (lb_remove_list (item_ids items vals) (lb_remove_list (opt_ids oi) L)) ->
      impl bgusegs (at_node bgusegs) (interp (LFree qc k) s') (epost (fun p : X * PState => Q p.1 p.2))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0' t1' t2' fp (Z_to_bv 64 A)
                 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x100bb8) fc None m' (seg_rom bgusegs))).
    { intros until L'. intros MI' ST' ERR' AUX' HP' FA' SO' HEAP' CS' INQC' INCL EL.
      assert (FR' : rw_cells bgusegs m' (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_agree; [exact (agree_of_heap_pres _ _ _ _ HP')| exact FR|]. intros x Hx. cbn in Hx. left. lia. }
      pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m') as MU'. pose proof (wmono_refl bgusegs m') as WM'.
      iprefix. do 4 step.
      do 7 step. release_frame FR' ST' (bv_unsigned sp). step. step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
      assert (CLI' : forall x, 0 <= x < 2^64 -> rclient_addr L' (bv_unsigned sp) x -> outside [(bv_unsigned sp - 64, bv_unsigned sp)] x).
      { intros x Hx Hc. apply (CLI L'); [exact INCL| exact Hx| exact Hc]. }
      eapply (CRYPTO_free_walk HF) with (p := qc) (A := A) (n := 72) (L := L') (B := B) (lo := lo) (errv := errv);
        [ eapply LH_frame; [exact HEAP'| exact MU'| exact WM'|]; constructor; [apply W_ok_stack; cbn; lia| constructor]
        | exact INQC'
        | eapply rauxv_ok_frame; [exact AUX'| exact MU'| exact WM'|]; constructor; [| constructor]; cbn; unfold RAUXV_CELL; lia
        | exact SPB | assumption | exact CEIL | unfold GLOBALS_TOP; lia | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia
        | unfold LX_ERRNO, RATP; assumption | assumption | reflexivity
        | eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU' WM')| | exact CS'];
          intros x Hx; cbn; split; [|exact Logic.I]; revert Hx; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia
        | reflexivity | ].
      intros st4 ms4 PO. apply K. unfold cfree_post in PO. unfold gfree_post.
      destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m7
                      & -> & MI7 & ST7 & ERR7 & AUX7 & HP7 & FA7 & SO7 & HEAP7).
      rewrite <- EL.
      do 15 eexists. exists m7. split; [reflexivity|].
      split; [exact MI7|]. split; [exact ST7|]. split; [exact ERR7|]. split; [exact AUX7|].
      split. { eapply rheap_pres_trans; [| exact HP7].
               eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM|]; intros x Hx Hc; apply (CLI (lb_remove qc L')); [| exact Hx| exact Hc];
                                          intros b Hb; apply INCL; eapply lb_remove_incl; exact Hb |].
               eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP'| lia| auto]|].
               eapply heap_pres_of_munch; [exact MU'| exact WM'|]. intros x Hx Hc. apply (CLI (lb_remove qc L')); [| exact Hx| exact Hc].
               intros b Hb; apply INCL; eapply lb_remove_incl; exact Hb. }
      split; [rewrite FA7; exact FA'|]. split; [rewrite SO7; exact SO'|]. exact HEAP7. }

    assert (REST : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' fp : word) (m' : mem) (s' : PState),
      let L0 := lb_remove_list (opt_ids oi) L in
      mem_inv bgusegs m' -> stk bgusegs m' lo (bv_unsigned sp - 64) -> rw_cells bgusegs m' 3346164 [C4 errv] -> rauxv_ok m' B ->
      rheap_pres L0 (bv_unsigned sp - 64) m1 m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> RHEAP s' L0 m' -> crypto_statics m' ->
      impl bgusegs (at_node bgusegs) (interp (lfrees (item_ids items vals) (lfrees [qc] k)) s') (epost (fun p : X * PState => Q p.1 p.2))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0' t1' t2' fp (Z_to_bv 64 A)
                 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x100b44) fc None m' (seg_rom bgusegs))).
    { intros until s'. intros L0 MI' ST' ERR' AUX' HP' FA' SO' HEAP' CS'.
      assert (INCL0 : forall b, In b L0 -> In b L) by (intros b Hb; eapply lb_remove_list_incl; exact Hb).
      assert (KEEP0 : forall blk, In blk L -> In (blk_id blk) (item_ids items vals ++ [qc]) -> In blk L0).
      { intros blk Hb Hi. apply lb_remove_list_In; [exact Hb|]. intros Ho. eapply (NoDup_app_disj _ _ (blk_id blk) ND); [exact Ho| exact Hi]. }
      assert (INQC0 : In (qc, A, 72) L0) by (apply KEEP0; [exact INQC| apply in_or_app; right; left; reflexivity]).
      assert (CX0 : rw_cells bgusegs m' A [C8 (Z_to_bv 64 (hd 0 Hs)); C8 cu; C8 tl; C4 pu; C4 ps; C8 (Z_to_bv 64 IX); C4 de; C4 ss; C4 us; C4 es; C4 tm; C4 fl; C8 lc]).
      { eapply rw_cells_agree; [exact (agree_of_heap_pres _ _ _ _ HP')| exact CX|]. intros x Hx. cbn in Hx. apply CLc; [exact INQC0| lia]. }
      assert (PI0 : pitems m' L0 items Hs vals prev).
      { eapply pitems_transport; [exact PI1| exact (agree_of_heap_pres _ _ _ _ HP')|]. intros blk Hb Hi.
        assert (Hb0 : In blk L0) by (apply KEEP0; [exact Hb| apply in_or_app; left; exact Hi]).
        split; [exact Hb0|]. intros x Hx. right. right. exists blk. split; [exact Hb0| exact Hx]. }
      pose proof (munch_refl [(A + 32, A + 40)]%Z m') as MU'. pose proof (wmono_refl bgusegs m') as WM'.
      iprefix. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m'' end.
      assert (HEAP'' : RHEAP s' L0 m'').
      { eapply LH_frame; [exact HEAP'| exact MU'| exact WM'|]. constructor; [| constructor].
        eapply (W_ok_block _ (qc, A, 72)); [exact INQC0| cbn; lia| cbn; lia]. }
      assert (AUX'' : rauxv_ok m'' B).
      { eapply rauxv_ok_frame; [exact AUX'| exact MU'| exact WM'|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
      assert (CS'' : crypto_statics m'').
      { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU' WM')| | exact CS'].
        intros x Hx. cbn. split; [|exact Logic.I]. revert Hx. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
      assert (PI'' : pitems m'' L0 items Hs vals prev).
      { eapply pitems_transport; [exact PI0| apply (agree_on_of_munch _ _ _ MU' WM')|]. intros blk Hb Hi. split; [exact Hb|].
        intros x Hx. assert (Hne : blk_id blk <> qc) by (intros E; apply NIQC; rewrite <- E; exact Hi).
        pose proof (LH_disjoint _ _ _ (qc, A, 72) blk HEAP' INQC0 Hb ltac:(intros E; apply Hne; symmetry; exact E)) as DJ.
        cbn [blk_addr blk_size blk_id fst snd] in DJ. cbn. split; [lia| exact Logic.I]. }
      assert (HP'' : rheap_pres (lb_remove qc L0) (bv_unsigned sp - 64) m1 m'').
      { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP'| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
        eapply heap_pres_of_munch; [exact MU'| exact WM'|].
        intros x Hx Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia| exact Logic.I]| split; [lia| exact Logic.I]|].
        pose proof (proj1 (lb_remove_In _ _ _) Hb') as [Hb2 Hne].
        pose proof (LH_disjoint _ _ _ (qc, A, 72) b' HEAP' INQC0 Hb2 ltac:(intros E; apply Hne; symmetry; exact E)) as DJ.
        cbn [blk_addr blk_size blk_id fst snd] in DJ. split; [lia| exact Logic.I]. }
      clear HEAP' AUX' CS' PI0 PI1 CX HP' MU' WM'.
      step. if_cases KB; zify_cond KB.
      -
        destruct items as [|q' items'].
        2: { destruct Hs as [|H' Hs']; cbn [pitems] in PI''; [contradiction|]. destruct PI'' as (INQ' & _). exfalso.
             pose proof (LH_block_range _ _ _ _ HEAP'' INQ') as (Q0 & _ & _ & QC' & _). cbn [blk_addr blk_size fst snd hd] in Q0, QC', KB.
             change 18446744073709551615 with (Z.ones 64) in KB. rewrite Z.land_ones in KB by lia. rewrite Z.mod_small in KB by lia. lia. }
        cbn [item_ids lfrees lb_remove_list] in EXIT |- *. ihere.
        eapply EXIT; [assumption | assumption | assumption | exact AUX'' | exact HP'' | exact FA' | exact SO' | exact HEAP'' | exact CS'' | exact INQC0 | exact INCL0 | reflexivity].
      -
        destruct items as [|q' items']; [destruct Hs; cbn [pitems] in PI''; [| contradiction]; exfalso; apply KB; reflexivity|].
        do 3 step.
        ihere.
        lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
          lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
        eapply (items_loop (q' :: items') Hs vals prev) with (qc := qc) (L := L0) (B := B) (lo := lo) (errv := errv) (EX := [qc]);
          [ exact PI'' | intros E; discriminate E | exact HEAP'' | exact INQC0 | apply NoDup_app_r in ND; exact ND | left; reflexivity
          | unfold ctxf_cells, MallocRep.wz; eassumption | exact AUX'' | rewrite ESP; lia | rewrite ESP; assumption | exact CEIL | unfold GLOBALS_TOP; lia
          | rewrite ESP; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; lia
          | unfold LX_ERRNO, RATP; assumption | assumption | exact CS'' | ].
        intros st3 ms3 PO. unfold il_post, CTXF_STR, MallocRep.wz in PO. rewrite ?ESP in PO.
        destruct PO as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & FA3 & SO3 & HEAP3 & CS3 & CX3).
        replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by lia.
        eapply EXIT; [exact MI3 | exact ST3 | unfold LX_ERRNO, RATP in ERR3; exact ERR3 | exact AUX3 | | rewrite FA3; exact FA' | rewrite SO3; exact SO' | exact HEAP3 | exact CS3 | | | reflexivity].
        + eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP''| lia|]| exact HP3].
          intros b Hb. pose proof (proj1 (lb_remove_In _ _ _) Hb) as [Hb3 Hne]. apply (proj2 (lb_remove_In _ _ _)). split; [eapply lb_remove_list_incl; exact Hb3| exact Hne].
        + apply lb_remove_list_In; [exact INQC0| exact NIQC].
        + intros b Hb. apply INCL0. eapply lb_remove_list_incl. exact Hb. }

    ihere.
    destruct oi as [qi|]; cbn [opt_ids lfrees lb_remove_list] in REST |- *.
    - lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st QQ ms) end end.
      pose proof (LH_block_range _ _ _ _ HEAP IDX) as (I0 & _ & _ & IC & _). cbn [blk_addr blk_size fst snd] in I0, IC.
      eapply (CRYPTO_free_walk HF) with (p := qi) (A := IX) (n := 128) (L := L) (B := B) (lo := lo) (errv := errv);
        [ exact HEAP1 | exact IDX | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1 | reflexivity | ].
      intros st2 ms2 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
      destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m2
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & FA2 & SO2 & HEAP2).
      replace (ret_pc (Z_to_bv 64 1051460)) with (Z_to_bv 64 1051460) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by lia.
      replace (Z_to_bv 64 (bv_unsigned sp - 64)) with (Z_to_bv 64 (bv_unsigned sp + -64)) by (f_equal; lia).
      eapply REST; [exact MI2 | exact ST2 | unfold LX_ERRNO, RATP in ERR2; exact ERR2 | exact AUX2 | exact HP2 | exact FA2 | exact SO2 | exact HEAP2 |].
      eapply crypto_statics_agree; [exact (agree_of_heap_pres _ _ _ _ HP2)| intros x Hx; apply libw_client; exact Hx| exact CS1].
    - subst IX.
      eapply impl_evt.
      { eapply (CRYPTO_free_null_spec _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo);
          [ rewrite ESP; exact ST | unfold GLOBALS_TOP; lia | rewrite ESP; lia | exact MI | exact CS1 | reflexivity ]. }
      cbv beta. intros ms2 (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite ESP in MU2, ST2. rewrite (ret_pc_even 1051460) by lia.
      replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by lia.
      replace (Z_to_bv 64 (bv_unsigned sp - 64)) with (Z_to_bv 64 (bv_unsigned sp + -64)) by (f_equal; lia).
      assert (CLI2 : forall x, 0 <= x < 2^64 -> rclient_addr L (bv_unsigned sp - 64) x -> outside [(bv_unsigned sp - 64 - 16, bv_unsigned sp - 64)] x).
      { intros x Hx Hc. cbn. split; [|exact Logic.I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
        pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
      eapply REST; [exact MI2 | exact ST2 | | | | reflexivity | reflexivity | | ].
      + eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia].
      + eapply rauxv_ok_frame; [exact AUX1| exact MU2| exact WM2|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia.
      + eapply heap_pres_of_munch; [exact MU2| exact WM2| exact CLI2].
      + eapply LH_frame; [exact HEAP1| exact MU2| exact WM2|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU2 WM2)| | exact CS1].
        intros x Hx. cbn. split; [|exact Logic.I]. revert Hx. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia.
  Qed.

End Proofs.
End WithCeiling0.
