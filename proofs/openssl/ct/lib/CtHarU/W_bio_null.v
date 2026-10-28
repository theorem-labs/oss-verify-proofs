(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac W_prefix_create W_bio_push W_locks W_ex_data W_bio_new W_bio_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac ub1c :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ub_kind pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => first [ (zstep; udecide) | uchk ]
      end
  end.
Local Ltac step := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition bio_null_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L : list block) (lo B : Z) (m : mem) (pb : bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' A (errv' : word),
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
      /\ rheap_pres L (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ rblock_range A BIO_SIZE
      /\ RHEAP s' ((pb, A, BIO_SIZE) :: L) m'
      /\ rw_cells ctusegs m' A (bio_null_cells NULL_METHOD 0 0).

  (* [comment removed for export] *)
  Lemma BIO_new_null_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word) (E : ap_env)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BIO_NEW_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    ap_statics_fixed m E -> exlock_free m E -> In (p_xl E, e_xl E, MUTEX_SIZE) L ->
    ro_cells ctusegs m (NULL_METHOD + 72) [C8 (wz 0)] ->
    a0 = wz NULL_METHOD ->
    k None = LUnr ->
    (forall pb s' ms',
       bio_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m pb s' ms' ->
       implM ctusegs (interp (k (Some pb))) s' Q ms') ->
    implM ctusegs (interp (LMalloc 128 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BIO_NEW) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> SF HXL HXLIN HMC -> K1N K.
    unfold BIO_NEW_STACK, PREFIX_CREATE_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, BIO_NEW, GLOBALS_TOP, MUTEX_SIZE, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof SF as SF0. destruct SF0 as (CS & _).
    pose proof (LH_block_range _ _ _ _ HEAP HXLIN) as (BX0 & BX1 & BX2 & BX3 & BX4). cbn [blk_addr blk_size fst snd] in *.
    assert (SEPX : e_xl E + 40 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= e_xl E) by lia.
    unfold NULL_METHOD in HMC. change (2978032 + 72) with 2978104 in HMC.
    assert (SEPMC : 2978104 + 8 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= 2978104) by lia.
    unfold exlock_free in HXL. unfold mutex_free_cells, zeros4, MallocRep.wz in HXL. cbn [repeat] in HXL.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 6 step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 step. do 6 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (AG1 : agree_on (lib_addr []) m m1).
    { eapply lib_agree_of_munch; [exact MU| exact WM|]. intros a Ha. cbn. lia. }
    assert (CS1 : crypto_statics m1) by (eapply (ApRep.crypto_statics_agree []); [exact CS| exact AG1]).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_zalloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 128);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact K1N | ].
    intros pb st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & A & errv2
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA & SO & BR & HEAP2 & BLK).
    replace (ret_pc (Z_to_bv 64 1098012)) with (Z_to_bv 64 1098012) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HXL;
      [| intros a Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXLIN| cbn; cbn in Ha; lia]].
    apply (ro_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HMC;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    assert (AG2 : agree_on (lib_addr []) m m2) by (eapply agree_on_trans; [exact AG1| eapply lib_agree_of_heap_pres; exact HP]).
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    apply zero128_cells in BLK. unfold bio_zero_cells, MallocRep.wz in BLK.
    assert (ND : List.NoDup (map blk_id ((pb, A, 128) :: L))) by (eapply LH_nodup; exact HEAP2).
    pose proof (LH_disjoint _ _ _ (pb, A, 128) (p_xl E, e_xl E, 40) HEAP2 ltac:(left; reflexivity) ltac:(right; exact HXLIN)) as DJX. cbn [blk_addr blk_size blk_id fst snd] in DJX.
    assert (NEX : pb <> p_xl E).
    { intros EQ. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite EQ. apply in_map_iff. exists (p_xl E, e_xl E, 40). split; [reflexivity| exact HXLIN]. }
    specialize (DJX NEX).
    assert (SEPA : A + 128 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) by lia.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m2).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    clear MU WM AG1 CS1 HEAP1 AUX1.
    pose proof (munch_refl [(bv_unsigned sp - 352, bv_unsigned sp); (A, A + 128)]%Z m2) as MU2. pose proof (wmono_refl ctusegs m2) as WM2.
    unfold LX_ERRNO, RATP in ERR2. change (3355176 - 164) with 3355012 in ERR2.
    unfold MallocRep.wz. unfold implM. iprefix.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    do 4 step. step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (AG3 : agree_on (lib_addr []) m m3).
    { eapply agree_on_trans; [exact AG2| eapply lib_agree_of_munch; [exact MU2| exact WM2|]]. intros a Ha. cbn. lia. }
    assert (SF3 : ap_statics_fixed m3 E) by (eapply (ap_statics_fixed_agree []); [exact SF| exact AG3]).
    (* [comment removed for export] *)
    lazymatch type of BLK with rw_cells _ _ _ ?cs =>
      lazymatch eval cbv in (firstn 18%nat cs) with ?cs1 =>
      lazymatch eval cbv in (skipn 18%nat cs) with ?cs2 =>
        change cs with (cs1 ++ cs2) in BLK end end end.
    apply rw_cells_app in BLK. destruct BLK as [HB1 HAD]. cbn [cells_size csize Nat.add] in HAD. replace (Z.of_nat 112) with 112 in HAD by reflexivity.
    eapply evt_cut.
    { eapply CRYPTO_new_ex_data_spec with (lo := lo) (E := E) (ad := A + 112) (c0 := 0) (k0 := 0);
        [rewrite ESP; exact ST2| exact MI2| unfold GLOBALS_TOP; lia| rewrite ESP; unfold NEW_EX_DATA_STACK; lia| reflexivity| exact SF3| exact HXL
        | unfold obj_range, MUTEX_SIZE, GLOBALS_TOP; lia| lia| unfold MallocRep.wz; exact HAD| unfold obj_range, GLOBALS_TOP; lia| clear - BA16; Z.div_mod_to_equations; lia| unfold MUTEX_SIZE; lia
        | reflexivity| reflexivity]. }
    clear HAD HXL SF3. post_call_esp ESP m3. rewrite ?ESP in *.
    match goal with H : stk ctusegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST3 end.
    match goal with H : rw_cells ctusegs _ (A + 112) _ |- _ => rename H into HAD end.
    match goal with H : exlock_free _ E |- _ => rename H into HXL end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    (* [comment removed for export] *)
    unfold MallocRep.wz in HAD.
    pose proof (proj2 (rw_cells_app m4 A _ _) (conj HB1 HAD)) as HB. clear HB1 HAD. cbn [app] in HB.
    assert (AG4 : agree_on (lib_addr []) m m4).
    { eapply agree_on_trans; [exact AG2| eapply lib_agree_of_munch; [exact MU2| exact WM2|]]. intros a Ha. cbn. lia. }
    clear AG3.
    step. if_false. (* [comment removed for export] *)
    unfold NULL_METHOD. step. (* [comment removed for export] *)
    step. if_true. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : stk ctusegs m5 lo _ |- _ => rename H into ST5 end.
    assert (HEAP5 : RHEAP st1 ((pb, A, 128) :: L) m5).
    { eapply LH_frame; [exact HEAP2| exact MU2| exact WM2|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (pb, A, 128)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX5 : rauxv_ok m5 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    do 5 step. step. release_frame FR ST5 (bv_unsigned sp). step.
    apply evt_done. apply K. unfold bio_null_post, MallocRep.wz.
    assert (CLI2 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 352, bv_unsigned sp); (A, A + 128)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (pb, A, 128) b' HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (pb <> blk_id b') as NE.
      { intros EQ. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite EQ. apply in_map. exact Hb'. }
      specialize (DJ NE). split; [lia| split; [lia| exact I]]. }
    do 14 eexists. exists m5, A. eexists. split; [reflexivity|].
    split; [assumption|]. split; [exact ST5|]. split; [unfold LX_ERRNO, RATP; eassumption|]. split; [exact AUX5|].
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU2| exact WM2| apply CLI2]. }
    split; [congruence|]. split; [congruence|]. split; [exact BR|].
    split; [exact HEAP5|]. unfold bio_null_cells, bio_cells, MallocRep.wz. exact HB.
  Qed.
  (* [comment removed for export] *)
  Lemma BIO_free_null_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word) (E : ap_env)
      (pb : bptr) (A nxt prev nw : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BIO_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    ap_statics_fixed m E -> exlock_free m E -> In (p_xl E, e_xl E, MUTEX_SIZE) L ->
    ro_cells ctusegs m (NULL_METHOD + 80) [C8 (wz 0)] ->
    In (pb, A, BIO_SIZE) L -> p_xl E <> pb ->
    rw_cells ctusegs m A (bio_cells NULL_METHOD 1 0 nxt prev nw) ->
    a0 = wz A ->
    bv_unsigned sp mod 16 = 0 ->
    (forall s' ms', free2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pb L) lo B errv m 1 (fun _ => True) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree pb k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BIO_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> SF HXL HXLIN HMD HBIN NXB HB -> SP16 K.
    unfold BIO_FREE_STACK, PREFIX_DESTROY_STACK, CRYPTO_FREE_STACK, RFREE_STACK, BIO_FREE, GLOBALS_TOP, MUTEX_SIZE, BIO_SIZE, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof SF as SF0. destruct SF0 as (CS & _).
    pose proof (LH_block_range _ _ _ _ HEAP HXLIN) as (BX0 & BX1 & BX2 & BX3 & BX4).
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    cbn [blk_addr blk_size fst snd] in *.
    assert (ND : List.NoDup (map blk_id L)) by (eapply LH_nodup; exact HEAP).
    pose proof (LH_disjoint _ _ _ (pb, A, 128) (p_xl E, e_xl E, 40) HEAP HBIN HXLIN ltac:(cbn; congruence)) as DJX.
    cbn [blk_addr blk_size blk_id fst snd] in DJX.
    assert (SEPX : e_xl E + 40 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= e_xl E) by lia.
    assert (SEPB : A + 128 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= A) by lia.
    unfold NULL_METHOD in HMD. change (2978032 + 80) with 2978112 in HMD.
    assert (SEPMD : 2978112 + 8 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= 2978112) by lia.
    unfold exlock_free in HXL. unfold mutex_free_cells, zeros4, MallocRep.wz in HXL. cbn [repeat] in HXL.
    unfold bio_cells, MallocRep.wz in HB.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    assert (AMO : amo_aligned AW (Z_to_bv 64 (A + 88)) = true) by (apply amo_aligned_w_intro; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + 128)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 4 step. step. step.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 6 step.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch type of HB with context [C4 (Z_to_bv 64 (bv_unsigned ?XX))] => change (bv_unsigned XX) with 0%Z in HB end.
    rewrite (sx32_small 1) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. if_false. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. rewrite (sx32_small 0) by lia. (* [comment removed for export] *)
    step. if_false. (* [comment removed for export] *)
    step. step. if_false. (* [comment removed for export] *)
    step. step. if_true. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. if_false. unfold NULL_METHOD. step. (* [comment removed for export] *)
    step. if_true. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end.
    match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
    assert (HEAP3 : RHEAP s L m3).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (pb, A, 128)); [exact HBIN| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (AG3 : agree_on (lib_addr []) m m3).
    { eapply lib_agree_of_munch; [exact MU| exact WM|]. intros a Ha. cbn. lia. }
    assert (SF3 : ap_statics_fixed m3 E) by (eapply (ap_statics_fixed_agree []); [exact SF| exact AG3]).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pb L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + 128)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      apply lb_remove_In in Hb0. destruct Hb0 as [Hb' Hnp].
      pose proof (LH_disjoint _ _ _ (pb, A, 128) b' HEAP HBIN Hb' ltac:(cbn; congruence)) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). split; [lia| split; [lia| exact I]]. }
    assert (HP0 : rheap_pres (lb_remove pb L) (bv_unsigned sp) m m3) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    clear MU WM AG3.
    (* [comment removed for export] *)
    lazymatch type of HB with rw_cells _ _ _ ?cs =>
      lazymatch eval cbv in (firstn 18%nat cs) with ?cs1 =>
      lazymatch eval cbv in (skipn 18%nat cs) with ?cs2 =>
        change cs with (cs1 ++ cs2) in HB end end end.
    apply rw_cells_app in HB. destruct HB as [HB1 HAD]. cbn [cells_size csize Nat.add] in HAD. replace (Z.of_nat 112) with 112 in HAD by reflexivity.
    pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp); (A + 112, A + 128)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    do 3 step. step. (* [comment removed for export] *)
    eapply evt_cut.
    { eapply CRYPTO_free_ex_data_spec with (lo := lo) (E := E) (ad := A + 112);
        [rewrite ESP; exact ST3| exact MI3| unfold GLOBALS_TOP; lia| rewrite ESP; unfold FREE_EX_DATA_STACK; lia| reflexivity| exact SF3| exact HXL
        | unfold obj_range, MUTEX_SIZE, GLOBALS_TOP; lia| lia| exact HAD| unfold obj_range, GLOBALS_TOP; lia| clear - BB1; Z.div_mod_to_equations; lia| unfold MUTEX_SIZE; lia
        | reflexivity| reflexivity]. }
    clear HAD HXL SF3. post_call_esp ESP m3. rewrite ?ESP in *.
    match goal with H : stk ctusegs _ lo (bv_unsigned sp + -64) |- _ => rename H into ST4 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (AG4 : agree_on (lib_addr []) m m4).
    { eapply agree_on_trans; [eapply lib_agree_of_heap_pres; exact HP0| eapply lib_agree_of_munch; [exact MU3| exact WM3|]]. intros a Ha. cbn. lia. }
    assert (HEAP4 : RHEAP s L m4).
    { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (pb, A, 128)); [exact HBIN| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (CS4 : crypto_statics m4) by (eapply (ApRep.crypto_statics_agree []); [exact CS| exact AG4]).
    do 4 step. step. (* [comment removed for export] *)
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := 128);
      [exact HEAP4 | exact HBIN | exact AUX4 | rewrite ESP; lia | rewrite ESP; exact ST4 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; eassumption | eassumption | reflexivity
      | exact CS4 | reflexivity | ].
    intros st5 ms5 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
    replace (ret_pc (Z_to_bv 64 1098556)) with (Z_to_bv 64 1098556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR0; [| intros a Ha; left; cbn in Ha; lia].
    eapply implM_evt with (P := free2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pb L) lo B errv m 1 (fun _ => True) st5);
      [| intros ms' PO'; apply K; exact PO'].
    unfold LX_ERRNO, RATP in ERR5. change (3355176 - 164) with 3355012 in ERR5.
    unfold MallocRep.wz.
    step. step. (* [comment removed for export] *)
    do 4 step. step. release_frame FR0 ST5 (bv_unsigned sp + -32). step.
    (* [comment removed for export] *)
    do 2 step. step. release_frame FR ST5 (bv_unsigned sp). step.
    apply evt_done. unfold free2_post, MallocRep.wz.
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pb L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 448, bv_unsigned sp); (A + 112, A + 128)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      apply lb_remove_In in Hb0. destruct Hb0 as [Hb1 Hnp].
      pose proof (LH_disjoint _ _ _ (pb, A, 128) b' HEAP HBIN Hb1 ltac:(cbn; congruence)) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb1) as (_ & _ & _ & B3' & _). split; [lia| split; [lia| exact I]]. }
    do 14 eexists. exists m5. split; [reflexivity|].
    split; [exact MI5|]. split; [exact ST5|]. split; [unfold LX_ERRNO, RATP; exact ERR5|]. split; [exact AUX5|].
    split. { eapply rheap_pres_trans; [exact HP0|].
             eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]|].
             eapply rheap_pres_weaken; [exact HP5| lia| auto]. }
    split; [congruence|]. split; [congruence|]. split; [exact HEAP5| exact I].
  Qed.
End Proofs.
End WithCeiling0.
