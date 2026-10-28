(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApWalkTac W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_memdup.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  (* [comment removed for export] *)
  Definition set_sig_cells (adr : bptr -> Z) (x : sctr bptr) (et C n : Z) : list cell :=
    [C4 (wz (u32 (sc_version x))); C4 (wz 0);
     C8 (wz (optr adr (sc_blob x))); C8 (wz (sc_bloblen x));
     C8 (wz (optr adr (osz32 (sc_logid x)))); C8 (wz (logid_len (sc_logid x)));
     C8 (wz (sc_ts x));
     C8 (wz (optr adr (sc_ext x))); C8 (wz (sc_extlen x));
     C1 (Z_to_bv 8 (sc_hash x)); C1 (Z_to_bv 8 (sc_sigalg x)); CB 6%nat (repeat (Z_to_bv 8 0) 6%nat);
     C8 (wz C); C8 (wz n);
     C4 (wz (u32 et)); C4 (wz 0); C4 (wz 0); C4 (wz 0)].

  Definition SCT_SET1_SIGNATURE : Z := 0x19d5e4.
  Definition SCT_SET1_SIGNATURE_STACK : Z := 48 + CRYPTO_MEMDUP_STACK.

  (* [comment removed for export] *)
  Lemma SCT_set1_signature_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (adr : bptr -> Z) (x : sctr bptr) (et vs : Z) (pp : bptr) (P PA psz n : Z) (src : list byte)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SCT_SET1_SIGNATURE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (sc_blk x, adr (sc_blk x), SCT_SIZE) L -> rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x et vs) -> sc_sig x = None ->
    In (pp, PA, psz) L -> pp <> sc_blk x -> PA <= P -> P + n <= PA + psz -> bytes_at ctusegs m P src -> length src = Z.to_nat n ->
    a0 = wz (adr (sc_blk x)) -> a1 = wz P -> a2 = wz n -> 0 < n < 2^31 - 1 ->
    k None = LUnr ->
    (forall p s' ms',
       oalloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L (sc_blk x) n lo B m 1
                   (fun C m' => rw_cells ctusegs m' C [CB (Z.to_nat n) src] /\ bytes_at ctusegs m' P src
                                /\ rw_cells ctusegs m' (adr (sc_blk x)) (set_sig_cells adr x et C n)) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz SCT_SET1_SIGNATURE) fc None m (seg_rom ctusegs)).
  Proof using HM.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HXIN HX HSIG HPIN NPX PA1 PA2 SRC SLEN -> -> -> Hn KN K.
    unfold SCT_SET1_SIGNATURE_STACK, CRYPTO_MEMDUP_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, SCT_SET1_SIGNATURE, SCT_SIZE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HXIN) as (BX0 & BX1 & BX2 & BX3 & BX4).
    pose proof (LH_block_range _ _ _ _ HEAP HPIN) as (BP0 & BP1 & BP2 & BP3 & BP4). cbn [blk_addr blk_size fst snd] in *.
    pose proof (LH_disjoint _ _ _ (pp, PA, psz) (sc_blk x, adr (sc_blk x), 104) HEAP HPIN HXIN NPX) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
    assert (SEPX : adr (sc_blk x) + 104 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= adr (sc_blk x)) by lia.
    assert (SEPP : P + n <= bv_unsigned sp - 64 \/ bv_unsigned sp <= P) by lia.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite SLEN, Z2Nat.id in SB by lia.
    unfold sct_cells, sc_siglen in HX. rewrite HSIG in HX. cbn [optr] in HX. unfold MallocRep.wz in HX.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 8 step. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. uchk. step. step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [| split; [|exact I]]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (CRYPTO_free_null_spec _) with (lo := lo); [rewrite ESP; exact ST| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact MI| exact CS1| reflexivity]|].
    post_call_esp ESP m1. name_mem m2. rename POST into ST2, MI0 into MI2.
    (* [comment removed for export] *)
    step. step. step.
    (* [comment removed for export] *)
    step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. clear KB.
    step. step. step. step. step.
    step. name_mem m3.
    assert (HEAP3 : RHEAP s L m3).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (sc_blk x, adr (sc_blk x), 104)); [exact HXIN| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [| split; [|exact I]]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove (sc_blk x) L) (bv_unsigned sp) a ->
                  outside [(bv_unsigned sp - 64, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      apply lb_remove_In in Hb0. destruct Hb0 as [Hb' Hnp].
      pose proof (LH_disjoint _ _ _ (sc_blk x, adr (sc_blk x), 104) b' HEAP ltac:(exact HXIN) ltac:(exact Hb')) as DJB.
      cbn [blk_addr blk_size blk_id fst snd] in DJB.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      specialize (DJB ltac:(intros E; apply Hnp; symmetry; exact E)). split; [lia| split; [lia| exact I]]. }
    assert (HP0 : rheap_pres (lb_remove (sc_blk x) L) (bv_unsigned sp) m m3) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_memdup_walk HM) with (B := B) (lo := lo) (errv := errv) (n := n) (pp := pp) (PA := PA) (psz := psz) (src := src);
      [exact HEAP3 | exact AUX3 | rewrite ESP; lia | rewrite ESP; exact ST2 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_MEMDUP_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI2 | reflexivity
      | exact CS3 | exact HPIN | exact PA1 | exact PA2 | exact SRC | exact SLEN | reflexivity | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m4 & C & errv2
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP & FA & SO & BR & HEAP4 & (BLK & SRC4)).
    replace (ret_pc (Z_to_bv 64 1693280)) with (Z_to_bv 64 1693280) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HX;
      [| intros a Ha; right; right; exists (sc_blk x, adr (sc_blk x), 104); split; [exact HXIN| cbn; cbn in Ha; lia]].
    pose proof BR as (BC0 & BC16 & _ & BCC & BCI).
    assert (ND : List.NoDup (map blk_id ((p, C, n) :: L))) by (eapply LH_nodup; exact HEAP4).
    assert (NEX : p <> sc_blk x).
    { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map_iff.
      exists (sc_blk x, adr (sc_blk x), 104). split; [reflexivity| exact HXIN]. }
    pose proof (LH_disjoint _ _ _ (p, C, n) (sc_blk x, adr (sc_blk x), 104) HEAP4 ltac:(left; reflexivity) ltac:(right; exact HXIN) NEX) as DJC.
    cbn [blk_addr blk_size blk_id fst snd] in DJC.
    assert (SEPC : C + n <= bv_unsigned sp - 48 \/ bv_unsigned sp <= C) by lia.
    unfold LX_ERRNO, RATP in ERR4. change (3355176 - 164) with 3355012 in ERR4.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104)]%Z m4) as MU4. pose proof (wmono_refl ctusegs m4) as WM4.
    assert (CLI4 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove (sc_blk x) L) (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 48, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104)] a).
    { intros a Ha Hc. destruct (CLI a Ha Hc) as (O1 & O2 & _). cbn. cbn in O1. split; [lia| split; [exact O2| exact I]]. }
    eapply implM_evt with (P := oalloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L (sc_blk x) n lo B m 1
                   (fun C m' => rw_cells ctusegs m' C [CB (Z.to_nat n) src] /\ bytes_at ctusegs m' P src
                                /\ rw_cells ctusegs m' (adr (sc_blk x)) (set_sig_cells adr x et C n)) p st1);
      [| intros ms' PO'; apply K; exact PO'].
    unfold MallocRep.wz.
    (* [comment removed for export] *)
    step.
    step. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; lia|]. clear KC.
    step. step. step.
    do 6 step. release_frame FR ST4 (bv_unsigned sp). step. step.
    name_mem m5. apply evt_done. unfold oalloc_post, MallocRep.wz.
    do 14 eexists. exists m5, C, errv2. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [unfold LX_ERRNO, RATP; exact ERR4|].
    split. { eapply rauxv_ok_frame; [exact AUX4| exact MU4| exact WM4|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             eapply heap_pres_of_munch; [exact MU4| exact WM4| apply CLI4]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP4| exact MU4| exact WM4|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (sc_blk x, adr (sc_blk x), 104)); [right; exact HXIN| cbn; lia| cbn; lia]| constructor]. }
    split; [exact BLK|]. split; [exact SRC4|]. unfold set_sig_cells, MallocRep.wz. exact HX.
  Qed.

  (* [comment removed for export] *)
  Lemma SCT_set1_signature_zero_spec : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (adr : bptr -> Z) (x : sctr bptr) (et vs : Z),
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv ctusegs m ->
    crypto_statics m ->
    rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x et vs) -> sc_sig x = None -> rblock_range (adr (sc_blk x)) SCT_SIZE ->
    a0 = wz (adr (sc_blk x)) -> a2 = wz 0 ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom ctusegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + SCT_SIZE)] m m' /\ wmono ctusegs m m'
                 /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
                 /\ rw_cells ctusegs m' (adr (sc_blk x)) (set_sig_cells adr x et 0 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz SCT_SET1_SIGNATURE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until vs. intros ST CEIL GLO LO MI CS HX HSIG BXC -> ->.
    unfold SCT_SET1_SIGNATURE, SCT_SIZE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    destruct BXC as (BX0 & BX1 & BX2 & BX3 & BX4).
    assert (SEPX : adr (sc_blk x) + 104 <= bv_unsigned sp - 64) by lia.
    unfold sct_cells, sc_siglen in HX. rewrite HSIG in HX. cbn [optr] in HX. unfold MallocRep.wz in HX.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 8 step. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. uchk. step. step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [| split; [|exact I]]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    eapply evt_cut; [eapply (CRYPTO_free_null_spec _) with (lo := lo); [rewrite ESP; exact ST| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact MI| exact CS1| reflexivity]|].
    post_call_esp ESP m1. name_mem m2. rename POST into ST2, MI0 into MI2.
    (* [comment removed for export] *)
    step. step. step. step. name_mem m3.
    assert (JOIN : forall (t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
      evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom ctusegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104)] m m' /\ wmono ctusegs m m'
                 /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
                 /\ rw_cells ctusegs m' (adr (sc_blk x)) (set_sig_cells adr x et 0 0))
        (MS (mkR (Z_to_bv 64 1693232) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0_ t1_ t2_ sp (Z_to_bv 64 0) a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_
                 (Z_to_bv 64 (adr (sc_blk x))) a1 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
            F (Z_to_bv 64 0x19d674) fc None m3 (seg_rom ctusegs))).
    { intros. step. do 6 step. release_frame FR ST2 (bv_unsigned sp). step. step.
      name_mem m5. apply evt_done. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. unfold set_sig_cells, MallocRep.wz. exact HX. }
    step. if_cases KA; [apply JOIN|].
    step. if_cases KB; zify_cond KB; [| exfalso; rewrite ?unsigned_lit in KB by lia; lia]. apply JOIN.
  Qed.
End Proofs.
End WithCeiling0.
