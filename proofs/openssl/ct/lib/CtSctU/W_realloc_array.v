(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac W_crypto_realloc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition CRYPTO_REALLOC_ARRAY : Z := 0xe7c08.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HR : rrealloc_stmt.
  Hypothesis HRS : rrealloc_shrink_stmt.

  Lemma CRYPTO_realloc_array_grow_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (p : bptr) (A n0 num size lo B : Z) (errv : word) (old : list byte)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> In (p, A, n0) L -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC_NN_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> rw_cells ctusegs m A [CB (Z.to_nat n0) old] -> mem_inv ctusegs m -> tp = wz RATP ->
    realloc_statics m -> a0 = wz A -> a1 = wz num -> a2 = wz size -> 0 < num -> 0 < size -> num * size < 2^32 ->
    k None = LUnr ->
    (forall q s' ms',
       crealloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L p (num * size) lo B m
                     (fun A' m' => exists junk, rw_cells ctusegs m' A' [CB (Z.to_nat n0) old; CB (Z.to_nat (num * size - n0)) junk] /\ n0 < num * size) q s' ms' ->
       implM ctusegs (interp (k (Some q))) s' Q ms') ->
    implM ctusegs (interp (LRealloc p (num * size) k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_REALLOC_ARRAY) fc None m (seg_rom ctusegs)).
  Proof using HR.
    intros until Q. intros HEAP HIN AUX SPB ST CEIL GLO LO ERR HB MI -> RS -> -> -> Hnum Hsize Hn KN K.
    unfold CRYPTO_REALLOC_ARRAY, MallocRep.wz. unfold CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK in LO. unfold GLOBALS_TOP in GLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (LH_block_range _ _ _ _ HEAP HIN) as (BA0 & BA16 & BN0 & BAC & BAI). cbn [blk_addr blk_size fst snd] in BA0, BN0, BAC, BAI.
    assert (Hsz : num < 2^32 /\ size < 2^32) by nia.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (proj1 (rw_cells_bound _ _ _ _ HB)) as HB0.
    assert (SEPA : A + n0 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) by lia.
    cbn [cells_size csize Nat.add] in HB.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 5 step. step. step. step. step.
    step. if_cases K0; zify_cond K0.
    2: { exfalso. apply K0. rewrite Z.shiftr_div_pow2, Z.div_small by nia. reflexivity. }
    clear K0.
    (* [comment removed for export] *)
    step. setreg 11%Z (Z_to_bv 64 (num * size)) ltac:(rewrite (unsigned_lit num), (unsigned_lit size) by lia; reflexivity).
    step. step. do 4 step. release_frame FR ST (bv_unsigned sp). step. step.
    name_mem m1.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)]%Z a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p0 => ?Q0 (fst p0) (snd p0)) => change (implM segs c st Q0 ms) end end.
    eapply (CRYPTO_realloc_grow_walk HR) with (B := B) (lo := lo) (errv := errv) (A := A) (n0 := n0) (old := old) (L := L);
      [ eapply LH_frame; [exact HEAP| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; lia| constructor]
      | exact HIN
      | eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]
      | exact SPB | exact ST | exact CEIL | unfold GLOBALS_TOP; lia | unfold CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK; lia
      | unfold LX_ERRNO, RATP; exact ERR | cbn [cells_size csize Nat.add]; exact HB | exact MI | reflexivity
      | eapply (realloc_statics_agree []); [exact RS| eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]];
        intros a Ha; cbn; split; [| exact I]; destruct Ha as [Ha|(b' & Hb' & Hr)]; [| destruct Hb'];
        unfold LIBW_HX, rin_ivs in Ha; cbn [fst snd] in Ha; lia
      | reflexivity | reflexivity | nia | exact KN | ].
    intros q s' ms' PO. apply K. unfold crealloc_post in *.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A' & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & CP).
    do 14 eexists. exists m3, A', errv2. split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
    split. { eapply rheap_pres_trans; [| exact HP]. eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; exact Hb]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|]. split; [exact HEAP3|]. exact CP.
  Qed.
End Proofs.
End WithCeiling0.
