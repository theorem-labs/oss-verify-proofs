(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnHeap BnRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition CRYPTO_MALLOC_STACK : Z := 48 + RMALLOC_STACK.

(* [comment removed for export] *)
Definition calloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (L : list block) (n lo B : Z) (m : mem) (init : Z -> mem -> Prop)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' A (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres L (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range A n /\ RHEAP s' ((p, A, n) :: L) m' /\ init A m'.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Lemma CRYPTO_malloc_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (n lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_MALLOC_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> a0 = wz n -> 0 < n < 2^32 ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L n lo B m
                   (fun A m' => exists junk, rw_cells ctusegs m' A [CB (Z.to_nat n) junk]) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_MALLOC) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS -> Hn KN K.
    unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK, CRYPTO_MALLOC, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct CS as (CS1 & CS2 & CS3 & CS4 & CS5 & CS6).
    unfold CR_GOT_MALLOC, CR_MALLOC_IMPL, CR_NO_CUSTOMIZE, CRYPTO_MALLOC, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 13 step.
    step. step. if_true.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. step. if_true.
    step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply implM_interp_malloc.
    { eapply (malloc_callZ HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL| unfold RMALLOC_STACK; lia| exact ERR| exact MI| lia| lia]. }
    cbv beta. intros r st1 ms1 PO.
    destruct r as [p|]; [| rewrite KN; apply implM_interp_unr].
    unfold malloc_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & (A & junkA & -> & BR & HEAP3 & BLK)).
    replace (ret_pc (Z_to_bv 64 957208)) with (Z_to_bv 64 957208) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L n lo B m
                   (fun A m' => exists junk, rw_cells ctusegs m' A [CB (Z.to_nat n) junk]) p st1); [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    step. if_cases KA; zify_cond KA; [| exfalso; rewrite ?unsigned_lit in KA by lia; lia]. clear KA.
    do 6 step. release_frame FR ST3 (bv_unsigned sp). step.
    apply evt_done. unfold calloc_post, MallocRep.wz, RATP.
    do 14 eexists. exists m3, A, errv2. split; [reflexivity|].
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    repeat (split; [first [assumption | congruence]|]).
    exists junkA. exact BLK.
  Qed.

  (* [comment removed for export] *)
  Definition CRYPTO_ZALLOC : Z := 0xe9b6c.
  Definition CRYPTO_ZALLOC_STACK : Z := 32 + CRYPTO_MALLOC_STACK.

  Lemma CRYPTO_zalloc_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (n lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_ZALLOC_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> a0 = wz n -> 0 < n < 2^32 ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L n lo B m
                   (fun A m' => rw_cells ctusegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_ZALLOC) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS -> Hn KN K.
    unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, CRYPTO_ZALLOC, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 6 step. step.
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
    eapply (CRYPTO_malloc_walk) with (B := B) (lo := lo) (errv := errv) (n := n);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & (junkA & BLK)).
    replace (ret_pc (Z_to_bv 64 957320)) with (Z_to_bv 64 957320) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L n lo B m
                   (fun A m' => rw_cells ctusegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]) p st1); [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + n)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    assert (ND : List.NoDup (map blk_id ((p, A, n) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + n)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (p, A, n) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). split; [lia| split; [lia| exact I]]. }
    unfold MallocRep.wz.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    do 6 step. release_frame FR ST3 (bv_unsigned sp). step. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (memset_callZ ra sp) with (D := A) (C := 0) (N := n) (junk := junkA); [exact BLK| exact MI3| lia| lia| lia| lia]. }
    post_call ctusegs m3.
    apply evt_done. unfold calloc_post, MallocRep.wz.
    do 14 eexists. exists x13, A, errv2. split; [reflexivity|].
    split; [exact MI0|]. split; [exact ST3|]. split; [unfold LX_ERRNO, RATP; exact ERR3|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
             pose proof AUX3 as (av & x3' & x4' & x5' & x16' & x6' & x11' & x12' & x23' & rnd & _ & _ & _ & HB & _).
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (p, A, n)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    change (0 mod 256) with 0 in POST. exact POST.
  Qed.

  (* [comment removed for export] *)
  Definition CRYPTO_CALLOC : Z := 0xe7ab8.
  Definition CRYPTO_CALLOC_STACK : Z := 32 + CRYPTO_ZALLOC_STACK.

  Lemma CRYPTO_calloc_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (num size lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_CALLOC_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> a0 = wz num -> a1 = wz size -> 0 < num -> 0 < size -> num * size < 2^32 ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L (num * size) lo B m
                   (fun A m' => rw_cells ctusegs m' A [CB (Z.to_nat (num * size)) (repeat (Z_to_bv 8 0) (Z.to_nat (num * size)))]) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc (num * size) k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_CALLOC) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS -> -> Hnum Hsize Hn KN K.
    unfold CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, CRYPTO_CALLOC, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    assert (Hsz : num < 2^32 /\ size < 2^32) by nia.
    carve_frame 32%nat ST. do 6 step. step. step. step.
    rewrite (unsigned_lit num), (unsigned_lit size) by lia.
    replace (Z.shiftr (num * size) 64) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    step. if_true.
    step. rewrite (unsigned_lit num), (unsigned_lit size) by lia.
    do 7 step. release_frame FR ST (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_zalloc_walk) with (B := B) (lo := lo) (errv := errv) (n := num * size);
      [exact HEAP1 | exact AUX1 | lia | exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | nia | exact KN | ].
    intros p st1 ms1 PO. apply K. unfold calloc_post in *.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    do 14 eexists. exists m3, A, errv2. split; [reflexivity|].
    repeat (split; [assumption|]).
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]| exact HP]. }
    repeat (split; [assumption|]). exact BLK.
  Qed.
  (* [comment removed for export] *)
  Definition CRYPTO_MALLOC_ARRAY : Z := 0xe7a24.
  Definition CRYPTO_MALLOC_ARRAY_STACK : Z := 32 + CRYPTO_MALLOC_STACK.

  Lemma CRYPTO_malloc_array_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (num size lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_MALLOC_ARRAY_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> a0 = wz num -> a1 = wz size -> 0 < num -> 0 < size -> num * size < 2^32 ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L (num * size) lo B m
                   (fun A m' => exists junk, rw_cells ctusegs m' A [CB (Z.to_nat (num * size)) junk]) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc (num * size) k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_MALLOC_ARRAY) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS -> -> Hnum Hsize Hn KN K.
    unfold CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, CRYPTO_MALLOC_ARRAY, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    assert (Hsz : num < 2^32 /\ size < 2^32) by nia.
    carve_frame 32%nat ST. do 6 step. step. step. step.
    rewrite (unsigned_lit num), (unsigned_lit size) by lia.
    replace (Z.shiftr (num * size) 64) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    step. if_true.
    step. rewrite (unsigned_lit num), (unsigned_lit size) by lia.
    do 7 step. release_frame FR ST (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_malloc_walk) with (B := B) (lo := lo) (errv := errv) (n := num * size);
      [exact HEAP1 | exact AUX1 | lia | exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | nia | exact KN | ].
    intros p st1 ms1 PO. apply K. unfold calloc_post in *.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    do 14 eexists. exists m3, A, errv2. split; [reflexivity|].
    repeat (split; [assumption|]).
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]| exact HP]. }
    repeat (split; [assumption|]). exact BLK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HF : rfree_stmt.

  Definition CRYPTO_FREE_STACK : Z := 16 + RFREE_STACK.

  Definition cfree_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
      (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
      /\ rheap_pres (lb_remove p L) (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ RHEAP s' (lb_remove p L) m'.

  Lemma CRYPTO_free_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (p : bptr) (A n lo B : Z) (errv : word)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (p, A, n) L -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> a0 = wz A ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L p lo B errv m s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree p k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP IN AUX SPB ST CEIL GLO LO ERR MI -> CS -> K.
    unfold CRYPTO_FREE_STACK, RFREE_STACK, CRYPTO_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct CS as (CS1 & CS2 & CS3 & CS4 & CS5 & CS6).
    unfold CR_GOT_FREE, CR_FREE_IMPL, CRYPTO_FREE, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    carve_frame 16%nat ST. do 8 step. step. if_true.
    do 3 step. release_frame FR ST (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove p L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      assert (Hb2 : In b' L) by (eapply lb_remove_incl; exact Hb').
      pose proof (LH_block_range _ _ _ _ HEAP Hb2) as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    eapply implM_interp_free.
    { eapply HF with (B := B) (lo := lo) (A := A) (n := n) (errv := errv);
        [exact HEAP1| exact IN| exact AUX1| exact SPB| exact ST| exact CEIL| unfold RFREE_STACK; lia| rewrite EA; exact ERR| exact MI
        | reflexivity| reflexivity]. }
    cbv beta. intros [] st1 ms1 PO. apply K. unfold rfree_post in PO. unfold cfree_post.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    rewrite EA in ERR4.
    do 15 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [unfold LX_ERRNO, RATP; exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]| exact HP4]. }
    repeat (split; [assumption|]). exact HEAP4.
  Qed.

  (* [comment removed for export] *)
  Lemma CRYPTO_free_null_spec : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk ctusegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv ctusegs m ->
    crypto_statics m -> a0 = wz 0 ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom ctusegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
                 /\ stk ctusegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until lo. intros ST GLO LO MI CS ->.
    unfold CRYPTO_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct CS as (CS1 & CS2 & CS3 & CS4 & CS5 & CS6).
    unfold CR_GOT_FREE, CR_FREE_IMPL, CR_GOT_MALLOC, CR_MALLOC_IMPL, CR_MEMSET_FUNC, CR_NO_CUSTOMIZE, CRYPTO_FREE, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    carve_frame 16%nat ST. do 8 step. step. if_true.
    do 3 step. release_frame FR ST (bv_unsigned sp). step. step.
    eapply evt_cut; [eapply rfree_null_spec; reflexivity|]. intros ms' ->.
    apply evt_done. do 15 eexists. eexists. split; [reflexivity|]. auto.
  Qed.

  (* [comment removed for export] *)
  Definition OPENSSL_CLEANSE : Z := 0xea1b0.

  Lemma OPENSSL_cleanse_spec : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo D N : Z) (junk : list byte),
    stk ctusegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv ctusegs m ->
    crypto_statics m -> rw_cells ctusegs m D [CB (Z.to_nat N) junk] -> 0 <= N < 2^63 ->
    (D + N <= lo \/ bv_unsigned sp <= D) -> (D + N <= 0x2c2000 \/ GLOBALS_TOP <= D) ->
    a0 = wz D -> a1 = wz N ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom ctusegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (D, D + N)] m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
                 /\ stk ctusegs m' lo (bv_unsigned sp)
                 /\ rw_cells ctusegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz OPENSSL_CLEANSE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until junk. intros ST GLO LO MI CS BLK HN SEP SEPI -> ->.
    unfold OPENSSL_CLEANSE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Z2Nat.id in BB by lia.
    destruct CS as (CS1 & CS2 & CS3 & CS4 & CS5 & CS6).
    unfold CR_GOT_FREE, CR_FREE_IMPL, CR_GOT_MALLOC, CR_MALLOC_IMPL, CR_MEMSET_FUNC, CR_NO_CUSTOMIZE, MEMSET, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (D, D + N)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    carve_frame 16%nat ST. do 8 step.
    do 3 step. release_frame FR ST (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    eapply evt_cut.
    { eapply (memset_callZ ra sp) with (D := D) (C := 0) (N := N) (junk := junk); [exact BLK| exact MI| lia| lia| lia| lia]. }
    post_call ctusegs m1.
    apply evt_done. do 14 eexists. eexists. split; [reflexivity|].
    change (0 mod 256) with 0 in POST. auto 8.
  Qed.

  (* [comment removed for export] *)
  Definition CRYPTO_CLEAR_FREE : Z := 0xe9f9c.
  Definition CRYPTO_CLEAR_FREE_STACK : Z := 48 + RFREE_STACK.

  Lemma CRYPTO_clear_free_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (p : bptr) (A n num lo B : Z) (errv : word)
      (junk : list byte) (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (p, A, n) L -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_CLEAR_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> rw_cells ctusegs m A [CB (Z.to_nat num) junk] -> 0 <= num <= n ->
    a0 = wz A -> a1 = wz num ->
    (forall s' ms', cfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L p lo B errv m s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree p k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_CLEAR_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP IN AUX SPB ST CEIL GLO LO ERR MI -> CS BLK Hnum -> -> K.
    unfold CRYPTO_CLEAR_FREE_STACK, RFREE_STACK, CRYPTO_CLEAR_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP IN) as (BA0 & BA16 & _ & BAC & BAI). cbn [blk_addr blk_size fst snd] in *.
    pose proof CS as (CS1 & CS2 & CS3 & CS4 & CS5 & CS6).
    unfold CR_GOT_FREE, CR_FREE_IMPL, CR_GOT_MALLOC, CR_MALLOC_IMPL, CR_MEMSET_FUNC, CR_NO_CUSTOMIZE, CRYPTO_FREE, CRYPTO_MALLOC, MEMSET, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + num)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    assert (ND : List.NoDup (map blk_id L)) by (eapply LH_nodup; exact HEAP).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove p L) (bv_unsigned sp) a ->
                  outside [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + num)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      apply lb_remove_In in Hb'. destruct Hb' as [Hb2 NE].
      pose proof (LH_block_range _ _ _ _ HEAP Hb2) as (_ & _ & _ & B3' & _).
      pose proof (LH_disjoint _ _ _ (p, A, n) b' HEAP IN Hb2 ltac:(cbn [blk_id fst snd]; congruence)) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ. split; [lia| split; [lia| exact I]]. }
    (* [comment removed for export] *)
    Ltac cf_tail spw HF K HEAP IN AUX MU WM SPB CEIL EA ERR CLI FRn STn MIn :=
      do 4 step; step; if_true;
      do 7 step; release_frame FRn STn (bv_unsigned spw); step; step;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        let HEAP1 := fresh "HEAP1" in let AUX1 := fresh "AUX1" in
        assert (HEAP1 : RHEAP _ _ mx) by
          (eapply LH_frame; [exact HEAP| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; lia|];
           constructor; [eapply (W_ok_block _ _); [exact IN| cbn; lia| cbn; lia]| constructor]);
        assert (AUX1 : rauxv_ok mx _) by
          (eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
           let HB := fresh "HB" in pose proof AUX as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & HB & _);
           constructor; [cbn; unfold RAUXV_CELL; lia|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]);
        ihere;
        lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
          lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end;
        eapply implM_interp_free;
        [ eapply HF with (errv := _);
            [exact HEAP1| exact IN| exact AUX1| exact SPB| exact STn| exact CEIL| unfold RFREE_STACK; lia| rewrite EA; exact ERR| exact MIn
            | reflexivity| reflexivity]
        | cbv beta; intros [] ?st1 ?ms1 PO; apply K; unfold rfree_post in PO; unfold cfree_post;
          destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                          & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4);
          rewrite EA in ERR4;
          do 15 eexists; exists m4; split; [reflexivity|];
          split; [exact MI4|]; split; [exact ST4|]; split; [unfold LX_ERRNO, RATP; exact ERR4|]; split; [exact AUX4|];
          split; [eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]| exact HP4]|];
          repeat (split; [assumption|]); exact HEAP4 ]
      end.
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 7 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    do 3 step.
    step. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *)
      cf_tail sp HF K HEAP IN AUX MU WM SPB CEIL EA ERR CLI FR ST MI. }
    step. step.
    (* [comment removed for export] *)
    rewrite ?unsigned_lit in KB by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (CSm1 : crypto_statics m1).
    { unfold crypto_statics, CR_GOT_FREE, CR_FREE_IMPL, CR_GOT_MALLOC, CR_MALLOC_IMPL, CR_MEMSET_FUNC, CR_NO_CUSTOMIZE, CRYPTO_FREE, CRYPTO_MALLOC, MEMSET, MallocRep.wz. auto 8. }
    eapply evt_cut.
    { eapply (OPENSSL_cleanse_spec) with (D := A) (N := num) (junk := junk) (lo := lo);
        rewrite ?ESP; [exact ST| unfold GLOBALS_TOP; lia| lia| exact MI| exact CSm1| exact BLK| lia| lia| unfold GLOBALS_TOP; lia| reflexivity| reflexivity]. }
    rewrite ?ESP. post_call ctusegs m1. unfold MallocRep.wz.
    cf_tail sp HF K HEAP IN AUX MU WM SPB CEIL EA ERR CLI FR PC MI0.
  Qed.
End Proofs.
End WithCeiling0.
