(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac al8chk A := step; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 7 with (Z.ones 3) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].

(* [comment removed for export] *)
Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))      (* [comment removed for export] *)
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Definition PREFIX_CREATE : Z := 0x13f3d0.
  Definition PREFIX_CREATE_STACK : Z := 32 + CRYPTO_ZALLOC_STACK.

  (* [comment removed for export] *)
  Lemma zero16_cells : forall m A,
    rw_cells ctusegs m A [CB 16%nat (repeat (Z_to_bv 8 0) 16%nat)] -> rw_cells ctusegs m A [C8 (wz 0); C8 (wz 0)].
  Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; auto| unfold MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma prefix_ctx_cells_fold : forall m A,
    rw_cells ctusegs m A [C8 (wz 0); C8 (wz 4294967296)] -> rw_cells ctusegs m A (prefix_ctx_cells 0 0 1).
  Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; auto| unfold prefix_ctx_cells, MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

  (* [comment removed for export] *)
  Definition oalloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L : list block) (pb : bptr) (n lo B : Z) (m : mem) (rv : Z) (init : Z -> mem -> Prop)
      (p : bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' A (errv' : word),
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
      /\ rheap_pres (lb_remove pb L) (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ rblock_range A n /\ RHEAP s' ((p, A, n) :: L) m' /\ init A m'.

  (* [comment removed for export] *)
  Lemma prefix_create_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pb : bptr) (bio meth init ptr next prev nw : Z)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - PREFIX_CREATE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pb, bio, BIO_SIZE) L -> rw_cells ctusegs m bio (bio_cells meth init ptr next prev nw) ->
    a0 = wz bio ->
    k None = LUnr ->
    (forall p s' ms',
       oalloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pb 16 lo B m 1
                   (fun A m' => rw_cells ctusegs m' A (prefix_ctx_cells 0 0 1) /\ rw_cells ctusegs m' bio (bio_cells meth 1 A next prev nw)) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc 16 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PREFIX_CREATE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HBIN HB -> KN K.
    unfold PREFIX_CREATE_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, PREFIX_CREATE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4). unfold BIO_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    assert (SEP : bio + 128 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bio) by lia.
    unfold bio_cells, MallocRep.wz in HB.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 6 step. do 6 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_zalloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 16);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    replace (ret_pc (Z_to_bv 64 1307648)) with (Z_to_bv 64 1307648) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HB; [| intros a Ha; right; right; exists (pb, bio, 128); split; [exact HBIN| cbn; cbn in Ha; lia]].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    apply zero16_cells in BLK.
    assert (ND : List.NoDup (map blk_id ((p, A, 16) :: L))) by (eapply LH_nodup; exact HEAP3).
    pose proof (LH_disjoint _ _ _ (p, A, 16) (pb, bio, 128) HEAP3 ltac:(left; reflexivity) ltac:(right; exact HBIN)) as DJB. cbn [blk_addr blk_size blk_id fst snd] in DJB.
    assert (NEB : p <> pb).
    { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map_iff. exists (pb, bio, 128). split; [reflexivity| exact HBIN]. }
    specialize (DJB NEB).
    assert (SEPA : A + 16 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) by lia.
    assert (SEPAB : A + 16 <= bio \/ bio + 128 <= A) by lia.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := oalloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pb 16 lo B m 1
                   (fun A m' => rw_cells ctusegs m' A (prefix_ctx_cells 0 0 1) /\ rw_cells ctusegs m' bio (bio_cells meth 1 A next prev nw)) p st1);
      [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 16); (bio, bio + 128)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pb L) (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 16); (bio, bio + 128)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]];
        [split; [lia| split; [lia| split; [lia| exact I]]] | split; [lia| split; [lia| split; [lia|exact I]]] |].
      apply lb_remove_In in Hb0. destruct Hb0 as [Hb' Hnp].
      pose proof (LH_disjoint _ _ _ (p, A, 16) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      pose proof (LH_disjoint _ _ _ (pb, bio, 128) b' HEAP ltac:(exact HBIN) ltac:(exact Hb')) as DJB2.
      cbn [blk_addr blk_size blk_id fst snd] in DJ, DJB2.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). specialize (DJB2 ltac:(intros E; apply Hnp; symmetry; exact E)). split; [lia| split; [lia| split; [lia| exact I]]]. }
    unfold MallocRep.wz.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step. al8chk BA16. do 2 step. step. step. step. step.
    carve_frame 16%nat ST3. do 4 step. step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ. step. al8chk BB1. do 5 step.
    do 3 step. do 4 step. step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ. step. al8chk BB1. do 5 step.
    step. step. do 4 step. release_frame FR0 ST3 (bv_unsigned sp + -32). step. release_frame FR ST3 (bv_unsigned sp). step.
    apply evt_done. unfold oalloc_post, MallocRep.wz.
    do 14 eexists. exists m2, A, errv2. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [unfold LX_ERRNO, RATP; exact ERR3|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
             pose proof AUX3 as (av & x3' & x4' & x5' & x16' & x6' & x11' & x12' & x23' & rnd & _ & _ & _ & HB' & _).
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (p, A, 16)); [left; reflexivity| cbn; lia| cbn; lia]|].
             constructor; [eapply (W_ok_block _ (pb, bio, 128)); [right; exact HBIN| cbn; lia| cbn; lia]| constructor]. }
    split; [apply prefix_ctx_cells_fold; exact BLK|].
    unfold bio_cells, MallocRep.wz. exact HB.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HF : rfree_stmt.

  Definition PREFIX_DESTROY : Z := 0x13f45c.
  Definition PREFIX_DESTROY_STACK : Z := 32 + CRYPTO_FREE_STACK.

  Definition free2_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L' : list block) (lo B : Z) (errv : word) (m : mem) (rv : Z) (fin : mem -> Prop)
      (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
      /\ rheap_pres L' (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ RHEAP s' L' m' /\ fin m'.

  Lemma prefix_destroy_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pb ppre pctx : bptr) (bio meth init nxt prev nw ctxA preA npre indent linestart : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - PREFIX_DESTROY_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pb, bio, BIO_SIZE) L -> In (ppre, preA, npre) L -> In (pctx, ctxA, PREFIX_CTX_SIZE) L -> pb <> pctx -> pb <> ppre -> ppre <> pctx ->
    rw_cells ctusegs m bio (bio_cells meth init ctxA nxt prev nw) ->
    rw_cells ctusegs m ctxA (prefix_ctx_cells preA indent linestart) ->
    a0 = wz bio ->
    (forall s' ms', free2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pctx (lb_remove ppre L)) lo B errv m 1
                      (fun m' => rw_cells ctusegs m' bio (bio_cells meth init ctxA nxt prev nw)) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree ppre (LFree pctx k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PREFIX_DESTROY) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HBIN HPIN HCIN NBC NBP NPC HB HC -> K.
    unfold PREFIX_DESTROY_STACK, CRYPTO_FREE_STACK, RFREE_STACK, PREFIX_DESTROY, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    pose proof (LH_block_range _ _ _ _ HEAP HCIN) as (BC0 & BC1 & BC2 & BC3 & BC4).
    unfold BIO_SIZE, PREFIX_CTX_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    assert (SEPB : bio + 128 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bio) by lia.
    assert (SEPC : ctxA + 16 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= ctxA) by lia.
    unfold bio_cells, MallocRep.wz in HB. unfold prefix_ctx_cells, MallocRep.wz in HC.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 6 step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 5 step. step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ. step. al8chk BB1. do 4 step. release_frame FR0 ST (bv_unsigned sp + -32).
    step. step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ. step. step. al8chk BC1. do 6 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := preA) (n := npre);
      [exact HEAP1 | exact HPIN | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | ].
    intros st1 ms1 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & HEAP3).
    replace (ret_pc (Z_to_bv 64 1307808)) with (Z_to_bv 64 1307808) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HB;
      [| intros a Ha; right; right; exists (pb, bio, 128); split; [apply lb_remove_In; split; [exact HBIN| cbn; congruence]| cbn; cbn in Ha; lia]].
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (HCIN3 : In (pctx, ctxA, 16) (lb_remove ppre L)) by (apply lb_remove_In; split; [exact HCIN| cbn; congruence]).
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    unfold implM. iprefix. do 4 step.
    assert (ND : List.NoDup (map blk_id L)) by (eapply LH_nodup; exact HEAP).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := ctxA) (n := 16);
      [exact HEAP3 | exact HCIN3 | exact AUX3 | rewrite ESP; lia | rewrite ESP; exact ST3 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR3 | exact MI3 | reflexivity
      | exact CS3 | reflexivity | ].
    intros st2 ms2 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    replace (ret_pc (Z_to_bv 64 1307824)) with (Z_to_bv 64 1307824) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in HB;
      [| intros a Ha; right; right; exists (pb, bio, 128); split; [apply lb_remove_In; split; [apply lb_remove_In; split; [exact HBIN| cbn; congruence]| cbn; congruence]| cbn; cbn in Ha; lia]].
    eapply implM_evt with (P := free2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pctx (lb_remove ppre L)) lo B errv m 1
                   (fun m' => rw_cells ctusegs m' bio (bio_cells meth init ctxA nxt prev nw)) st2); [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m4) as MU4. pose proof (wmono_refl ctusegs m4) as WM4.
    unfold LX_ERRNO, RATP in ERR4. change (3355176 - 164) with 3355012 in ERR4.
    assert (CLI4 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pctx (lb_remove ppre L)) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      apply lb_remove_incl in Hb'. apply lb_remove_incl in Hb'. pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    unfold MallocRep.wz. step. do 5 step. release_frame FR ST4 (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    apply evt_done. unfold free2_post, MallocRep.wz.
    do 14 eexists. exists m9. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [unfold LX_ERRNO, RATP; exact ERR4|].
    split. { eapply rauxv_ok_frame; [exact AUX4| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP4| lia| auto]|].
             eapply heap_pres_of_munch; [exact MU4| exact WM4| apply CLI4]. }
    split; [congruence|]. split; [congruence|].
    split. { eapply LH_frame; [exact HEAP4| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    unfold bio_cells, MallocRep.wz. exact HB.
  Qed.
End Proofs.
End WithCeiling0.
