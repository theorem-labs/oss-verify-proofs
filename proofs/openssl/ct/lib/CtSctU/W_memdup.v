(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Definition CRYPTO_MEMDUP : Z := 0xeafc8.
  Definition CRYPTO_MEMDUP_STACK : Z := 32 + CRYPTO_MALLOC_STACK.

  Lemma CRYPTO_memdup_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pp : bptr) (P PA psz n : Z) (src : list byte)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_MEMDUP_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pp, PA, psz) L -> PA <= P -> P + n <= PA + psz -> bytes_at ctusegs m P src -> length src = Z.to_nat n ->
    a0 = wz P -> a1 = wz n -> 0 < n < 2^31 - 1 ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L n lo B m
                   (fun C m' => rw_cells ctusegs m' C [CB (Z.to_nat n) src] /\ bytes_at ctusegs m' P src) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_MEMDUP) fc None m (seg_rom ctusegs)).
  Proof using HM.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HPIN PA1 PA2 SRC SLEN -> -> Hn KN K.
    unfold CRYPTO_MEMDUP_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, CRYPTO_MEMDUP, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HPIN) as (BP0 & BP1 & BP2 & BP3 & BP4). cbn [blk_addr blk_size fst snd] in *.
    assert (SEPP : P + n <= bv_unsigned sp - 32 \/ bv_unsigned sp <= P) by lia.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite SLEN, Z2Nat.id in SB by lia.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 6 step.
    step. if_cases K0; zify_cond K0; [exfalso; try rewrite <- unsigned_lit_land, ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. step. step.
    step. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; lia|]. clear K1.
    step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := n);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & C & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & (junkC & BLK)).
    replace (ret_pc (Z_to_bv 64 962568)) with (Z_to_bv 64 962568) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (bytes_at_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in SRC;
      [| intros a Ha; right; right; exists (pp, PA, psz); split; [exact HPIN| cbn; rewrite SLEN, Z2Nat.id in Ha by lia; lia]].
    pose proof BR as (BC0 & BC16 & _ & BCC & BCI).
    assert (ND : List.NoDup (map blk_id ((p, C, n) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (NEP : p <> pp).
    { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map_iff. exists (pp, PA, psz). split; [reflexivity| exact HPIN]. }
    pose proof (LH_disjoint _ _ _ (p, C, n) (pp, PA, psz) HEAP3 ltac:(left; reflexivity) ltac:(right; exact HPIN) NEP) as DJP.
    cbn [blk_addr blk_size blk_id fst snd] in DJP.
    assert (SEPC : C + n <= bv_unsigned sp - 32 \/ bv_unsigned sp <= C) by lia.
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L n lo B m
                   (fun C m' => rw_cells ctusegs m' C [CB (Z.to_nat n) src] /\ bytes_at ctusegs m' P src) p st1);
      [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (C, C + n)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp); (C, C + n)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]];
        [ clear - Ha Hc CEIL GLO LO SPR BCC BCI; split; [lia| split; [lia| exact I]] | clear - Ha Hc CEIL GLO LO SPR BCC BCI; split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (p, C, n) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). clear - Ha Hr DJ B3' CEIL LO SPR. split; [lia| split; [lia| exact I]]. }
    unfold MallocRep.wz.
    (* [comment removed for export] *)
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step. do 4 step. step. release_frame FR ST3 (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    eapply evt_mono; [eapply memcpy_spec with (src := src) (junk := junkC);
        [ rewrite unsigned_lit by lia; exact SRC | rewrite unsigned_lit by lia; exact SLEN
        | rewrite !unsigned_lit by lia; exact BLK | rewrite !unsigned_lit by lia; lia | assumption ]|].
    unfold memcpy_post. intros ms' PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU5 & WM5 & MI2 & DST2 & SRC2).
    unfold calloc_post, MallocRep.wz.
    do 14 eexists. exists m2, C, errv2. split; [reflexivity|].
    split; [exact MI2|].
    split. { eapply stk_transport; [exact ST3| exact MU5| exact WM5|]. intros x Hx. left. cbn. split; [lia| exact I]. }
    split. { unfold LX_ERRNO, RATP. eapply rw_cells_transport; [exact ERR3| exact MU5| exact WM5|]. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU5| exact WM5|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU5| exact WM5|].
             intros a Ha Hc. destruct (CLI3 a Ha Hc) as (_ & O2 & _). cbn. split; [exact O2| exact I]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU5| exact WM5|].
             constructor; [eapply (W_ok_block _ (p, C, n)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    split; [exact DST2| exact SRC2].
  Qed.
End Proofs.
End WithCeiling0.
