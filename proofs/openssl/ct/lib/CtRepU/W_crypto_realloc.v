(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition CRYPTO_REALLOC_NN_STACK : Z := 48 + RREALLOC_STACK.

(* [comment removed for export] *)
Definition crealloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (L : list block) (p : bptr) (n lo B : Z) (m : mem) (CP : Z -> mem -> Prop)
    (q : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A' : Z) (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p L) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range A' n /\ RHEAP s' ((q, A', n) :: lb_remove p L) m'
    /\ CP A' m'.

(* [comment removed for export] *)
Lemma crealloc_prefix : forall (P : machine_state -> Prop)
    (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv ctusegs m ->
  realloc_statics m -> 0 < A < 2^64 -> 0 < n < 2^64 ->
  (forall m1 junk,
      munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
      stk ctusegs m1 lo (bv_unsigned sp - 48) ->
      rw_cells ctusegs m1 (bv_unsigned sp - 48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt ctusegs P
        (MS (mkR (wz 0xe9dc8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 sp a3 (wz A) (wz n) (wz CRYPTO_REALLOC) a3 (wz CRYPTO_REALLOC) a5 a6 a7
                 a2 (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz RREALLOC_SYM) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P
    (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_REALLOC) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST GLO LO MI RS HA Hn K.
  unfold CRYPTO_REALLOC, RREALLOC_SYM, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct RS as [RS1 RS2]. unfold CR_GOT_MALLOC, CR_REALLOC_IMPL, CRYPTO_REALLOC, MallocRep.wz in RS1, RS2.
  change (3270968 + 8) with 3270976 in RS1.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 48%nat ST. do 7 step. do 3 step. do 3 step. step. step.
  step. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. try clear K0.
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. try clear K2.
  step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => eapply (K m1 j); [exact MU|exact WM|exact MI|exact ST|exact FR] end.
Qed.

(* [comment removed for export] *)
Lemma crealloc_suffix : forall (P : machine_state -> Prop)
    (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x9 x18 x19 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (A' lo : Z) (junk : list byte),
  stk ctusegs m1 lo (bv_unsigned sp - 48) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv ctusegs m1 ->
  rw_cells ctusegs m1 (bv_unsigned sp - 48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> 0 < A' < 2^64 ->
  (forall m2, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1 m2 -> wmono ctusegs m1 m2 -> mem_inv ctusegs m2 -> stk ctusegs m2 lo (bv_unsigned sp) ->
      P (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m2 (seg_rom ctusegs))) ->
  evt ctusegs P
    (MS (mkR (wz 0xe9dc8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 sp x9 (wz A') a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (wz 0xe9dc8)) fc None m1 (seg_rom ctusegs)).
Proof.
  intros until junk. intros ST GLO LO MI FR HA K.
  unfold GLOBALS_TOP, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  replace (ret_pc (Z_to_bv 64 0xe9dc8)) with (Z_to_bv 64 0xe9dc8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in ST, FR by lia.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl ctusegs m1) as WM.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. try clear K0.
  do 7 step. release_frame FR ST (bv_unsigned sp). step.
  apply evt_done. lazymatch goal with |- P (MS _ _ _ _ _ ?mx _) => eapply (K mx); [exact MU|exact WM|eassumption|exact ST] end.
Qed.

(* [comment removed for export] *)
Ltac klia := try match goal with K : forall q s' ms', _ -> implM _ _ _ _ _ |- _ => clear K end; lia.

Section Proofs.
  Hypothesis HR : rrealloc_stmt.
  Hypothesis HRS : rrealloc_shrink_stmt.

  (* [comment removed for export] *)
  Lemma CRYPTO_realloc_grow_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old : list byte)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (p, A, n0) L -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC_NN_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> rw_cells ctusegs m A [CB (Z.to_nat n0) old] -> mem_inv ctusegs m -> tp = wz RATP ->
    realloc_statics m -> a0 = wz A -> a1 = wz n -> 0 < n < 2^32 ->
    k None = LUnr ->
    (forall q s' ms',
       crealloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L p n lo B m
                     (fun A' m' => exists junk, rw_cells ctusegs m' A' [CB (Z.to_nat n0) old; CB (Z.to_nat (n - n0)) junk] /\ n0 < n) q s' ms' ->
       implM ctusegs (interp (k (Some q))) s' Q ms') ->
    implM ctusegs (interp (LRealloc p n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_REALLOC) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP HIN AUX SPB ST CEIL GLO LO ERR HB MI -> RS -> -> Hn KN K.
    unfold CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP HIN) as (BA0 & BA16 & BN0 & BAC & _). cbn [blk_addr blk_size fst snd] in BA0, BN0, BAC. pose proof alloc_ceiling_range as ACR.
    unfold implM. iprefix.
    eapply crealloc_prefix; [exact ST|exact GLO|klia|exact MI|exact RS|klia|klia|].
    intros m1 junk MU WM MI1 ST1 FR.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)]%Z a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in ERR; [| intros a Ha; cbn in Ha |- *; unfold LX_ERRNO, RATP in Ha; split; [lia|exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG) in HB; [| intros a Ha; cbn in Ha |- *; split; [lia|exact I]].
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply implM_interp_realloc.
    { eapply HR with (B := B) (lo := lo) (p := p) (A := A) (n0 := n0) (n := n) (old := old);
        [ eapply LH_frame; [exact HEAP| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; klia| constructor]
        | exact HIN
        | eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; klia| constructor]
        | rewrite ESP; klia | rewrite ESP; exact ST1 | exact CEIL | rewrite ESP; unfold RREALLOC_STACK; klia
        | first [ replace (errno_addr (wz RATP)) with LX_ERRNO by (unfold errno_addr, LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia)
                | replace (bv_unsigned (wz RATP) + -164) with LX_ERRNO by (unfold LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia) ]; exact ERR
        | exact HB | exact MI1 | reflexivity | reflexivity | reflexivity | lia ]. }
    cbv beta. intros r st1 ms1 PO.
    destruct r as [q|]; [| rewrite KN; apply implM_interp_unr].
    unfold rrealloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & (A' & junkA & -> & BR & HEAP3 & BLK & GROW)).
    pose proof BR as (BA0' & _ & _ & BAC' & _).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    unfold implM. iprefix.
    eapply crealloc_suffix; [replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact ST3|exact GLO|lia|exact MI3
      |replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact FR|lia|].
    intros m4 MU4 WM4 MI4 ST4.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?E) ?ms =>
      lazymatch E with (fun p0 => ?Q0 (fst p0) (snd p0)) => change (implM segs c stt Q0 ms) end end.
    apply K. unfold crealloc_post.
    assert (CLI2 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove p L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)]%Z a).
    { intros a Ha Hc. apply CLI; [exact Ha|]. destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc| right; left; exact Hc| right; right].
      unfold in_block in Hc |- *. destruct Hc as (b' & Hb' & Hr). exists b'. split; [eapply lb_remove_incl; exact Hb'| exact Hr]. }
    clear K. pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
    do 14 eexists. exists m4, A', errv2. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
    split. { apply (rw_cells_agree _ _ _ _ _ AG4).
             - first [ replace (errno_addr (wz RATP)) with LX_ERRNO in ERR3 by (unfold errno_addr, LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia)
                     | replace (bv_unsigned (wz RATP) + -164) with LX_ERRNO in ERR3 by (unfold LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia) ]. exact ERR3.
             - intros a Ha; cbn in Ha |- *. unfold LX_ERRNO, RATP in Ha. split; [lia|exact I]. }
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| exact CLI2]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| auto]|]. eapply heap_pres_of_munch; [exact MU4| exact WM4| exact CLI2]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    exists junkA. split; [|exact GROW]. apply (rw_cells_agree _ _ _ _ _ AG4); [exact BLK|]. intros a Ha; cbn in Ha |- *; split; [lia|exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma CRYPTO_realloc_shrink_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old : list byte)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (p, A, n0) L -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC_NN_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> rw_cells ctusegs m A [CB (Z.to_nat n0) old] -> mem_inv ctusegs m -> tp = wz RATP ->
    realloc_statics m -> a0 = wz A -> a1 = wz n -> 0 < n < n0 -> n0 < 2^32 ->
    k None = LUnr ->
    (forall q s' ms',
       crealloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L p n lo B m
                     (fun A' m' => rw_cells ctusegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat n) old)]) q s' ms' ->
       implM ctusegs (interp (k (Some q))) s' Q ms') ->
    implM ctusegs (interp (LReallocS p n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_REALLOC) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP HIN AUX SPB ST CEIL GLO LO ERR HB MI -> RS -> -> Hn Hn0 KN K.
    unfold CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (LH_block_range _ _ _ _ HEAP HIN) as (BA0 & BA16 & BN0 & BAC & _). cbn [blk_addr blk_size fst snd] in BA0, BN0, BAC. pose proof alloc_ceiling_range as ACR.
    unfold implM. iprefix.
    eapply crealloc_prefix; [exact ST|exact GLO|klia|exact MI|exact RS|klia|klia|].
    intros m1 junk MU WM MI1 ST1 FR.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)]%Z a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in ERR; [| intros a Ha; cbn in Ha |- *; unfold LX_ERRNO, RATP in Ha; split; [lia|exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG) in HB; [| intros a Ha; cbn in Ha |- *; split; [lia|exact I]].
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply implM_interp_reallocS.
    { eapply HRS with (B := B) (lo := lo) (p := p) (A := A) (n0 := n0) (n := n) (old := old);
        [ eapply LH_frame; [exact HEAP| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; klia| constructor]
        | exact HIN
        | eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; klia| constructor]
        | rewrite ESP; klia | rewrite ESP; exact ST1 | exact CEIL | rewrite ESP; unfold RREALLOC_STACK; klia
        | first [ replace (errno_addr (wz RATP)) with LX_ERRNO by (unfold errno_addr, LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia)
                | replace (bv_unsigned (wz RATP) + -164) with LX_ERRNO by (unfold LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia) ]; exact ERR
        | exact HB | exact MI1 | reflexivity | reflexivity | reflexivity | lia ]. }
    cbv beta. intros r st1 ms1 PO.
    destruct r as [q|]; [| rewrite KN; apply implM_interp_unr].
    unfold rrealloc_shrink_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & (A' & -> & BR & HEAP3 & BLK & SHR)).
    pose proof BR as (BA0' & _ & _ & BAC' & _).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    unfold implM. iprefix.
    eapply crealloc_suffix; [replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact ST3|exact GLO|lia|exact MI3
      |replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact FR|lia|].
    intros m4 MU4 WM4 MI4 ST4.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?E) ?ms =>
      lazymatch E with (fun p0 => ?Q0 (fst p0) (snd p0)) => change (implM segs c stt Q0 ms) end end.
    apply K. unfold crealloc_post.
    assert (CLI2 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove p L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)]%Z a).
    { intros a Ha Hc. apply CLI; [exact Ha|]. destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc| right; left; exact Hc| right; right].
      unfold in_block in Hc |- *. destruct Hc as (b' & Hb' & Hr). exists b'. split; [eapply lb_remove_incl; exact Hb'| exact Hr]. }
    clear K. pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
    do 14 eexists. exists m4, A', errv2. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
    split. { apply (rw_cells_agree _ _ _ _ _ AG4).
             - first [ replace (errno_addr (wz RATP)) with LX_ERRNO in ERR3 by (unfold errno_addr, LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia)
                     | replace (bv_unsigned (wz RATP) + -164) with LX_ERRNO in ERR3 by (unfold LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia) ]. exact ERR3.
             - intros a Ha; cbn in Ha |- *. unfold LX_ERRNO, RATP in Ha. split; [lia|exact I]. }
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| exact CLI2]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| auto]|]. eapply heap_pres_of_munch; [exact MU4| exact WM4| exact CLI2]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    apply (rw_cells_agree _ _ _ _ _ AG4); [exact BLK|]. intros a Ha; cbn in Ha |- *; split; [lia|exact I].
  Qed.
End Proofs.
End WithCeiling0.
