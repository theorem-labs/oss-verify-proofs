(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface RF_realloc_I_spec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac W_crypto_realloc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac klia := try match goal with K : forall s' ms', _ -> implM _ _ _ _ _ |- _ => clear K end; lia.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition creallocI_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (L : list block) (p : bptr) (A n0 n lo B : Z) (old : list byte) (m : mem)
    (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p L) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s /\ s' = s
    /\ RHEAP s' ((p, A, n) :: lb_remove p L) m'
    /\ rw_cells ctusegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat n) old)].

(* [comment removed for export] *)
Lemma CRYPTO_realloc_inplace_walk : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old : list byte)
    (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
  RHEAP s L m -> In (p, A, n0) L -> rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC_NN_STACK ->
  rw_cells ctusegs m LX_ERRNO [C4 errv] -> rw_cells ctusegs m A [CB (Z.to_nat n0) old] -> mem_inv ctusegs m -> tp = wz RATP ->
  realloc_statics m -> a0 = wz A -> a1 = wz n -> 0 < n <= n0 -> n0 < 2^32 ->
  k None = LUnr ->
  (forall s' ms',
     creallocI_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L p A n0 n lo B old m s' ms' ->
     implM ctusegs (interp (k (Some p))) s' Q ms') ->
  implM ctusegs (interp (LReallocI p n k)) s Q
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
  eapply implM_interp_reallocI.
  { eapply rrealloc_inplace_spec with (B := B) (lo := lo) (p := p) (A := A) (n0 := n0) (n := n) (old := old);
      [ eapply LH_frame; [exact HEAP| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; klia| constructor]
      | exact HIN
      | eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; klia| constructor]
      | rewrite ESP; klia | rewrite ESP; exact ST1 | exact CEIL | rewrite ESP; unfold RREALLOC_STACK; klia
      | first [ replace (errno_addr (wz RATP)) with LX_ERRNO by (unfold errno_addr, LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia)
              | replace (bv_unsigned (wz RATP) + -164) with LX_ERRNO by (unfold LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia) ]; exact ERR
      | exact HB | exact MI1 | reflexivity | reflexivity | reflexivity | lia ]. }
  cbv beta. intros r st1 ms1 PO.
  unfold rrealloc_inplace_post in PO. rewrite ?ESP in PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv2
                  & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & -> & ES & -> & HEAP3 & BLK). subst st1.
  apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
  unfold implM. iprefix.
  eapply crealloc_suffix; [replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact ST3|exact GLO|lia|exact MI3
    |replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; unfold MallocRep.wz; exact FR|lia|].
  intros m4 MU4 WM4 MI4 ST4.
  lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?E) ?ms =>
    lazymatch E with (fun p0 => ?Q0 (fst p0) (snd p0)) => change (implM segs c stt Q0 ms) end end.
  apply K. unfold creallocI_post.
  assert (CLI2 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove p L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)]%Z a).
  { intros a Ha Hc. apply CLI; [exact Ha|]. destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc| right; left; exact Hc| right; right].
    unfold in_block in Hc |- *. destruct Hc as (b' & Hb' & Hr). exists b'. split; [eapply lb_remove_incl; exact Hb'| exact Hr]. }
  clear K. pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
  do 14 eexists. exists m4, errv2. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
  split. { apply (rw_cells_agree _ _ _ _ _ AG4).
           - first [ replace (errno_addr (wz RATP)) with LX_ERRNO in ERR3 by (unfold errno_addr, LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia)
                   | replace (bv_unsigned (wz RATP) + -164) with LX_ERRNO in ERR3 by (unfold LX_ERRNO, RATP, MallocRep.wz; rewrite unsigned_lit by lia; lia) ]. exact ERR3.
           - intros a Ha; cbn in Ha |- *. unfold LX_ERRNO, RATP in Ha. split; [lia|exact I]. }
  split. { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| exact CLI2]|].
           eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| auto]|]. eapply heap_pres_of_munch; [exact MU4| exact WM4| exact CLI2]. }
  split; [exact FA|]. split; [exact SO|]. split; [reflexivity|].
  split. { eapply LH_frame; [exact HEAP3| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
  apply (rw_cells_agree _ _ _ _ _ AG4); [exact BLK|]. intros a Ha; cbn in Ha |- *; split; [lia|exact I].
Qed.

End WithCeiling0.
