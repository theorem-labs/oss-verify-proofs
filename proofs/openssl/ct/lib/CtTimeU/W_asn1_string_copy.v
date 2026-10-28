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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac W_crypto_realloc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 W_crypto_realloc3.
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

Ltac klia := try match goal with K : forall s' ms', _ -> implM _ _ _ _ _ |- _ => clear K end; lia.
Ltac nchk := let C := fresh "C" in if_cases C; [exfalso; zify_cond C; rewrite ?land64, ?Z.mod_small in C by klia; klia | clear C].
Ltac achk H := let C := fresh "C" in if_cases C;
  [exfalso; zify_cond C; change 7 with (Z.ones 3) in C; rewrite Z.land_ones in C by lia; change (2^3) with 8 in C; apply C; clear - H; Z.div_mod_to_equations; lia
  | clear C].

(* [comment removed for export] *)
Definition ASN1_STRING_COPY_STACK : Z := 32 + 48 + CRYPTO_REALLOC_NN_STACK.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ascopy_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (L : list block) (lo B : Z) (m : mem) (G D : Z) (dp : bptr) (n ty : Z) (src : list byte)
    (s' : PState) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_but (lb_remove dp L) (bv_unsigned sp) (G, G + 24) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s /\ s' = s
    /\ RHEAP s' ((dp, D, n) :: lb_remove dp L) m'
    /\ rw_cells ctusegs m' G (asn1_string_cells n ty D 0)
    /\ rw_cells ctusegs m' D [CB (Z.to_nat n) src].

Lemma ASN1_STRING_copy_walk : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
    (G D STR GS : Z) (gb dp : bptr) (dl ty0 n0 n ty : Z) (old src : list byte)
    (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
  RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_COPY_STACK ->
  rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP -> realloc_statics m ->
  In (gb, G, 24) L -> In (dp, D, n0) L -> gb <> dp ->
  rw_cells ctusegs m G (asn1_string_cells dl ty0 D 0) -> 0 < dl < 2^31 -> dl <> n ->
  rw_cells ctusegs m D [CB (Z.to_nat n0) old] -> 0 < n <= n0 -> n0 < 2^31 ->
  ro_cells ctusegs m STR (asn1_string_cells n ty GS 0) -> bv_unsigned sp <= STR -> STR + 24 <= 2^63 -> STR mod 8 = 0 -> 0 <= ty < 2^31 ->
  bytes_at ctusegs m GS src -> length src = Z.to_nat n -> bv_unsigned sp <= GS -> GS + n <= 2^63 ->
  a0 = wz G -> a1 = wz STR ->
  k None = LUnr ->
  (forall s' ms', ascopy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m G D dp n ty src s' ms' ->
                implM ctusegs (interp (k (Some dp))) s' Q ms') ->
  implM ctusegs (interp (LReallocI dp n k)) s Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_COPY) fc None m (seg_rom ctusegs)).
Proof.
  intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> RS HGIN HDIN NE HG HDL HDN HD Hn Hn0 HS SLO SHI SAL TY SRC SLEN GLO2 GHI -> -> KN K.
  unfold ASN1_STRING_COPY_STACK, CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK, ASN1_STRING_COPY, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
  unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
  pose proof (LH_block_range _ _ _ _ HEAP HGIN) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB1, BB2, BB3, BB4.
  pose proof (LH_block_range _ _ _ _ HEAP HDIN) as (BD0 & BD1 & BD2 & BD3 & BD4). cbn [blk_addr blk_size fst snd] in BD0, BD1, BD2, BD3, BD4.
  pose proof (LH_disjoint _ _ _ (gb, G, 24) (dp, D, n0) HEAP HGIN HDIN NE) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
  assert (SEPG : G + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= G) by klia.
  assert (SEPS : STR + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp - 80 + 80 <= STR) by klia.
  unfold asn1_string_cells, MallocRep.wz in HG, HS.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  unfold implM. iprefix.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 6 step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by klia; klia|]. try clear K0.
  step. step. step. step. achk SAL.
  step. rewrite (sx32_small n) by klia.
  step. brF ltsz.
  step. nchk. step. step. achk BB1.
  step. rewrite (sx32_small ty) by klia. step. step. step. step. step.
  (* [comment removed for export] *)
  carve_frame 48%nat ST. do 7 step. step. step. step. brT ltsz.
  do 3 step. step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by klia; klia|]. try clear K1.
  step. nchk. step. step. achk BB1.
  (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2; [| exfalso; apply K2; reflexivity]. try clear K2.
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by klia; klia|]. try clear K3.
  step. rewrite (sx32_small dl) by klia.
  step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by klia; klia|]. try clear K4.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by klia; klia|]. try clear K5.
  step.
  (* [comment removed for export] *)
  do 4 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : RHEAP s L m1).
  { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; klia|].
    constructor; [eapply (W_ok_block _ (gb, G, 24)); [exact HGIN| cbn; klia| cbn; klia]| constructor]. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; klia|]. constructor; [cbn; unfold RAUXV_CELL; klia| constructor]. }
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
  assert (RS1 : realloc_statics m1).
  { destruct RS as [RSa RSb]. unfold realloc_statics, CR_GOT_MALLOC, CR_REALLOC_IMPL in *.
    split; (eapply ro_cells_agree; [exact AG1| eassumption| intros a Ha; cbn; cbn in Ha; split; [klia| split; [klia| exact I]]]). }
  clear RS AG1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; klia).
  assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove dp L) (bv_unsigned sp) a -> ~ (G <= a < G + 24) ->
                outside [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24)] a).
  { intros a Ha Hc NX. cbn. split; [| split; [klia| exact I]]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [klia| klia|].
    apply lb_remove_incl in Hb'. pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). klia. }
  ihere.
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
  eapply CRYPTO_realloc_inplace_walk with (B := B) (lo := lo) (errv := errv) (A := D) (n0 := n0) (old := old);
    [ exact HEAP1 | exact HDIN | exact AUX1 | rewrite ESP; klia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; klia
    | rewrite ESP; unfold CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK; klia
    | unfold LX_ERRNO, RATP; exact ERR | exact HD | exact MI | reflexivity | exact RS1 | reflexivity | reflexivity | klia | klia | exact KN | ].
  intros st1 ms1 PO. unfold creallocI_post in PO. rewrite ?ESP in PO.
  destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2
                  & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA & SO & ES & HEAP2 & HD2). subst st1.
  replace (ret_pc (Z_to_bv 64 1040288)) with (Z_to_bv 64 1040288) by (symmetry; apply ret_pc_even; [klia| reflexivity]).
  pose proof (agree_of_heap_pres _ _ _ _ HP) as AG2.
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; klia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR0; [| intros a Ha; left; cbn in Ha; klia].
  apply (ro_cells_agree _ _ _ _ _ AG2) in HS; [| intros a Ha; left; cbn in Ha; klia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HG;
    [| intros a Ha; right; right; exists (gb, G, 24); split; [apply lb_remove_In; split; [exact HGIN| cbn; congruence]| cbn; cbn in Ha; klia]].
  assert (SRC2 : bytes_at ctusegs m2 GS src).
  { eapply bytes_at_agree; [exact AG2| exact SRC|]. rewrite SLEN. intros a Ha. left. klia. }
  clear AG2 HEAP1 AUX1 RS1 MI ST.
  unfold LX_ERRNO, RATP in ERR2. change (3355176 - 164) with 3355012 in ERR2.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24); (D, D + n)]%Z m2) as MU2. pose proof (wmono_refl ctusegs m2) as WM2.
  eapply implM_evt with (P := ascopy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m G D dp n ty src s);
    [| intros ms' PO'; apply K; exact PO'].
  clear K.
  (* [comment removed for export] *)
  unfold MallocRep.wz.
  step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by klia; klia|]. try clear K6.
  step. step.
  step. if_cases K7; zify_cond K7; [exfalso; rewrite ?unsigned_lit in K7 by klia; klia|]. try clear K7.
  step. step. if_cases K8; zify_cond K8; [exfalso; rewrite ?unsigned_lit in K8 by klia; klia|]. try clear K8.
  do 3 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  eapply evt_cut.
  { eapply memcpy_spec with (src := src) (junk := firstn (Z.to_nat n) old); rewrite ?unsigned_lit by klia;
      [exact SRC2| rewrite SLEN; reflexivity| exact HD2| klia| assumption]. }
  intros ms' PO; unfold memcpy_post in PO; rewrite ?unsigned_lit in PO by klia; revert ms' PO. post_call ctusegs m3.
  match goal with H : rw_cells ctusegs _ D [CB _ src] |- _ => rename H into HD4 end.
  (* [comment removed for export] *)
  step. step. step. step. step.
  do 5 step. step. release_frame FR0 ST2 (bv_unsigned sp + -32). step.
  (* [comment removed for export] *)
  step. if_cases K9; zify_cond K9; [exfalso; rewrite ?unsigned_lit in K9 by klia; klia|]. try clear K9.
  do 7 step. step. step.
  do 4 step. step.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -32) |- _ => release_frame FR H (bv_unsigned sp) end. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  apply evt_done. unfold ascopy_post, MallocRep.wz.
  assert (HEAP5 : RHEAP s ((dp, D, n) :: lb_remove dp L) m5).
  { eapply LH_frame; [exact HEAP2| exact MU2| exact WM2|].
    constructor; [apply W_ok_stack; cbn; klia|].
    constructor; [eapply (W_ok_block _ (gb, G, 24)); [right; apply lb_remove_In; split; [exact HGIN| cbn; congruence]| cbn; klia| cbn; klia]|].
    constructor; [eapply (W_ok_block _ (dp, D, n)); [left; reflexivity| cbn; klia| cbn; klia]| constructor]. }
  do 14 eexists. exists m5. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [unfold LX_ERRNO, RATP; change (3355176 - 164) with 3355012; eassumption|].
  split. { eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2|].
           constructor; [cbn; unfold RAUXV_CELL; klia|]. constructor; [cbn; unfold RAUXV_CELL; klia|]. constructor; [cbn; unfold RAUXV_CELL; klia| constructor]. }
  split. { intros a Ha Hc NX. cbn [fst snd] in NX.
           assert (E1 : m1 (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m1 (wa a) <> None)).
           { split; [| intros Hv; apply WM; exact Hv]. apply MU. unfold wa. rewrite unsigned_lit by klia. exact (CLI a Ha Hc NX). }
           assert (E2 : m2 (wa a) = m1 (wa a) /\ (wview ctusegs m1 (wa a) <> None -> wview ctusegs m2 (wa a) <> None)).
           { apply (HP a Ha). destruct Hc as [Hc|Hc]; [left; klia| right; exact Hc]. }
           assert (E3 : m5 (wa a) = m2 (wa a) /\ (wview ctusegs m2 (wa a) <> None -> wview ctusegs m5 (wa a) <> None)).
           { split; [| intros Hv; apply WM2; exact Hv]. apply MU2. unfold wa. rewrite unsigned_lit by klia.
             pose proof (CLI a Ha Hc NX) as [O1 [O2 _]]. cbn. split; [exact O1|]. split; [exact O2|]. split; [| exact I].
             apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [klia| klia|].
             apply lb_remove_In in Hb'. destruct Hb' as [Hb' Hne].
             pose proof (LH_disjoint _ _ _ (dp, D, n0) b' HEAP HDIN Hb' ltac:(cbn; intros E; apply Hne; symmetry; exact E)) as DJ'.
             cbn [blk_addr blk_size blk_id fst snd] in DJ'. klia. }
           destruct E1 as [E1 V1], E2 as [E2 V2], E3 as [E3 V3]. split; [congruence| auto]. }
  split; [exact FA|]. split; [exact SO|]. split; [reflexivity|]. split; [exact HEAP5|].
  split; [unfold asn1_string_cells, MallocRep.wz; assumption|].
  exact HD4.
Qed.

End WithCeiling0.
