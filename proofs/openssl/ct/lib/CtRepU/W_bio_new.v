(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac W_prefix_create W_bio_push W_locks W_ex_data.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

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
Local Ltac al8chk A := step; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 7 with (Z.ones 3) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lib_static_range : forall a, lib_addr [] a -> 2891776 <= a < 3493888.
Proof.
  intros a [H|(b & Hb & _)]; [| destruct Hb].
  unfold HxpInit.LIBW_HX in H. cbn [rin_ivs fst snd] in H. lia.
Qed.

(* [comment removed for export] *)
Lemma lib_agree_of_munch : forall W m m', munch W m m' -> wmono ctusegs m m' ->
  (forall a, 2891776 <= a < 3493888 -> outside W a) -> agree_on (lib_addr []) m m'.
Proof.
  intros W m m' MU WM HW. eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|].
  intros a Ha. apply HW. apply lib_static_range. exact Ha.
Qed.
Lemma lib_agree_of_heap_pres : forall L SP m m', rheap_pres L SP m m' -> agree_on (lib_addr []) m m'.
Proof.
  intros L SP m m' HP. eapply agree_on_mono; [apply (agree_of_heap_pres _ _ _ _ HP)|].
  intros a Ha. eapply lib_addr_rclient; [| exact Ha]. intros b Hb. destruct Hb.
Qed.

(* [comment removed for export] *)
Definition bio_zero_cells : list cell :=
  [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Lemma zero128_cells : forall m A,
  rw_cells ctusegs m A [CB 128%nat (repeat (Z_to_bv 8 0) 128%nat)] -> rw_cells ctusegs m A bio_zero_cells.
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; tauto| unfold bio_zero_cells, MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Definition BIO_NEW : Z := 0x10c210.
  Definition BIO_NEW_EX : Z := 0x10c0e4.
  (* [comment removed for export] *)
  Definition BIO_NEW_STACK : Z := 48 + PREFIX_CREATE_STACK.

  Definition bio_new_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L : list block) (lo B : Z) (m : mem) (meth : Z)
      (pb pc : bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' A C (errv' : word),
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
      /\ rheap_pres L (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ rblock_range A BIO_SIZE /\ rblock_range C PREFIX_CTX_SIZE
      /\ RHEAP s' ((pc, C, PREFIX_CTX_SIZE) :: (pb, A, BIO_SIZE) :: L) m'
      /\ rw_cells ctusegs m' A (bio_cells meth 1 C 0 0 0) /\ rw_cells ctusegs m' C (prefix_ctx_cells 0 0 1).

  (* [comment removed for export] *)
  Lemma BIO_new_prefix_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word) (E : ap_env)
      (k1 : option bptr -> lprog X) (k2 : bptr -> option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BIO_NEW_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    ap_statics_fixed m E -> exlock_free m E -> In (p_xl E, e_xl E, MUTEX_SIZE) L ->
    ro_cells ctusegs m (AP_PREFIX_METH + 72) [C8 (wz PREFIX_CREATE)] ->
    a0 = wz AP_PREFIX_METH ->
    k1 None = LUnr -> (forall pb, k1 (Some pb) = LMalloc 16 (k2 pb)) -> (forall pb, k2 pb None = LUnr) ->
    (forall pb pc s' ms',
       bio_new_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m AP_PREFIX_METH pb pc s' ms' ->
       implM ctusegs (interp (k2 pb (Some pc))) s' Q ms') ->
    implM ctusegs (interp (LMalloc 128 k1)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BIO_NEW) fc None m (seg_rom ctusegs)).
  Proof using HM.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> SF HXL HXLIN HMC -> K1N K1S K2N K.
    unfold BIO_NEW_STACK, PREFIX_CREATE_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, BIO_NEW, GLOBALS_TOP, MUTEX_SIZE, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof SF as SF0. destruct SF0 as (CS & _).
    pose proof (LH_block_range _ _ _ _ HEAP HXLIN) as (BX0 & BX1 & BX2 & BX3 & BX4). cbn [blk_addr blk_size fst snd] in *.
    assert (SEPX : e_xl E + 40 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= e_xl E) by lia.
    unfold AP_PREFIX_METH in HMC. change (2963608 + 72) with 2963680 in HMC.
    assert (SEPMC : 2963680 + 8 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= 2963680) by lia.
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
    rewrite (K1S pb).
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
    step. step. al8chk BA16. step. (* [comment removed for export] *)
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
    unfold AP_PREFIX_METH. step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
    assert (MA8 : 2963608 mod 8 = 0) by reflexivity. step. al8chk MA8. clear MA8.
    step. (* [comment removed for export] *)
    step. if_false. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 PREFIX_CREATE)) with (Z_to_bv 64 PREFIX_CREATE) by (symmetry; apply ret_pc_even; [unfold PREFIX_CREATE; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (HEAP4 : RHEAP st1 ((pb, A, 128) :: L) m4).
    { eapply LH_frame; [exact HEAP2| exact MU2| exact WM2|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (pb, A, 128)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (CS4 : crypto_statics m4) by (eapply (ApRep.crypto_statics_agree []); [exact CS| exact AG4]).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (prefix_create_walk HM) with (B := B) (lo := lo) (pb := pb) (bio := A) (meth := AP_PREFIX_METH) (init := 0) (ptr := 0) (next := 0) (prev := 0) (nw := 0);
      [exact HEAP4 | exact AUX4 | rewrite ESP; lia | rewrite ESP; exact ST3 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold PREFIX_CREATE_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
      | unfold LX_ERRNO, RATP; eassumption | eassumption | reflexivity | exact CS4 | left; reflexivity
      | unfold bio_cells, AP_PREFIX_METH, MallocRep.wz; exact HB | reflexivity | apply K2N | ].
    intros pc st2 ms2 PO. unfold oalloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m5 & C & errv3
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & BRC & HEAP5 & HC5 & HB5).
    replace (ret_pc (Z_to_bv 64 1098108)) with (Z_to_bv 64 1098108) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (ro_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in HMC;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    eapply implM_evt with (P := bio_new_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m AP_PREFIX_METH pb pc st2);
      [| intros ms' PO'; apply K; exact PO'].
    unfold LX_ERRNO, RATP in ERR5. change (3355176 - 164) with 3355012 in ERR5.
    unfold MallocRep.wz.
    step. if_false. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. if_true. (* [comment removed for export] *)
    step. do 6 step. release_frame FR ST5 (bv_unsigned sp). step.
    apply evt_done. unfold bio_new_post, MallocRep.wz.
    assert (CLI2 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 352, bv_unsigned sp); (A, A + 128)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (pb, A, 128) b' HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (pb <> blk_id b') as NE.
      { intros EQ. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite EQ. apply in_map. exact Hb'. }
      specialize (DJ NE). split; [lia| split; [lia| exact I]]. }
    do 14 eexists. exists m5, A, C, errv3. split; [reflexivity|].
    split; [exact MI5|]. split; [exact ST5|]. split; [unfold LX_ERRNO, RATP; exact ERR5|]. split; [exact AUX5|].
    split. { eapply rheap_pres_trans; [exact HP0|].
             eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU2| exact WM2| apply CLI2]|].
             eapply rheap_pres_weaken; [exact HP5| lia|].
             intros b Hb. apply lb_remove_In. split; [right; exact Hb|].
             intros EQ. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite <- EQ. apply in_map. exact Hb. }
    split; [congruence|]. split; [congruence|]. split; [exact BR|]. split; [exact BRC|].
    split; [exact HEAP5|]. split; [exact HB5| exact HC5].
  Qed.
End Proofs.
End WithCeiling0.
