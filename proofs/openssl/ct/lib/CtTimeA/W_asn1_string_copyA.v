(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog BnBase BnModel BnTree ApBase ApLogic ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA W_crypto_reallocA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface W_akit W_prefix_create W_strdup W_asn1_stringA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import W_crypto_reallocIA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
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

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.

(* [comment removed for export] *)
Local Notation E_copy_sint := (E_ASN1_STRING_copy_22265c : uk_call 0x2242a0 0x224340 0x2243f8).                (* [comment removed for export] *)
Local Notation E_sint_realloc := (E_ossl_asn1_string_set_internal_222850 : uk_call 0x2243f8 0x224524 0x1fd224). (* [comment removed for export] *)

Definition ASN1_STRING_COPY_A : Z := 0x2242a0.
Definition SINT_A : Z := 0x2243f8.                         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SINT_COPY_STACK_A : Z := 80 + CRYPTO_REALLOC2_STACK.
Definition ASN1_STRING_COPY_STACK_A : Z := 48 + SINT_COPY_STACK_A.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis REA : realloc_contract_gen RT.

(* [comment removed for export] *)
Definition ascopy_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (G : Z) (dp : bptr) (n ty lo : Z) (src : list byte) (m : mem)
    (p' : bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' D',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_but LB (lb_remove dp OW) (bv_unsigned sp) G ASN1_STRING_SIZE m m'
    /\ rt_credit RT Σ - mcost n <= rt_credit RT Σ'
    /\ ablock_range D' n /\ AHEAP Σ' ((p', D', n) :: lb_remove dp OW) LB m'
    /\ rw_cells ctasegs m' G (asn1_string_cells n ty D' 0)
    /\ rw_cells ctasegs m' D' [CB (Z.to_nat n) src].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sint_copy_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (gb dp : bptr) (bsrc : block) (G dl ty0 D0 n0 GS n : Z) (src : list byte)
    (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SINT_COPY_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> realloc_statics m -> bv_unsigned ra mod 2 = 0 ->
  In (gb, G, ASN1_STRING_SIZE) OW -> rw_cells ctasegs m G (asn1_string_cells dl ty0 D0 0) -> 0 < dl < 2^31 -> dl <> n ->
  In (dp, D0, n0) OW -> gb <> dp ->
  In bsrc (OW ++ LB) -> blk_id bsrc <> gb -> blk_id bsrc <> dp -> blk_addr bsrc <= GS -> GS + n <= blk_addr bsrc + blk_size bsrc ->
  bytes_at ctasegs m GS src -> Z.of_nat (length src) = n ->
  a0 = wz G -> a1 = wz GS -> a2 = wz n -> 0 < n <= 0x8000000 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SINT_A (bv_unsigned ra :: ras) ->
  (forall p' Σ' ms', ~ In p' (map blk_id (OW ++ LB)) ->
     ascopy_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB G dp n ty0 lo src m p' Σ' ms' ->
     implAp (k (Some p')) Σ' Q ms') ->
  implAp (AReallocI dp n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SINT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI TP RS RAEV HBIN HB HDL DLN HDIN NE INS NSG NSD S1 S2 SRC SLEN -> -> -> Hn CRED UW CTX K.
  pose proof LO as LO'. unfold SINT_COPY_STACK_A, CRYPTO_REALLOC2_STACK, RT_STACK, SINT_A, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (gb, G, ASN1_STRING_SIZE) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  assert (HDIN' : In (dp, D0, n0) (OW ++ LB)) by (apply in_or_app; left; exact HDIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HDIN') as (BD0 & _ & _ & BD3 & BD4).
  pose proof (AH_range_gen _ _ _ _ bsrc HEAP INS) as (BS0 & _ & _ & BS3 & BS4).
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB. pose proof (AH_okA _ _ _ _ _ _ _ HEAP HDIN) as [ALD N0P].
  unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4, BD0, BD3, BD4.
  assert (EA : bv_unsigned (Z_to_bv 64 G) = G) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 D0) = D0) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  pose proof (AH_disjoint_gen _ _ _ _ bsrc (gb, G, 24) HEAP INS HBIN' NSG) as DJP. cbn [blk_addr blk_size blk_id fst snd] in DJP.
  ablock HEAP HBIN' ACCB OFFB.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold asn1_string_cells, MallocRep.wz in HB.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. do 11 step.      (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2; [clear K2| exfalso; rewrite ab_signed_small in K2 by lia; lia].
  step. step. step.
  step. if_cases K3; zify_cond K3; [exfalso; clear - K3 Hn; lia| clear K3].
  (* [comment removed for export] *)
  step. zstep. step. step. if_true.
  step. if_cases K4; zify_cond K4; [exfalso; clear - K4 Hn; lia| clear K4].
  (* [comment removed for export] *)
  step. rewrite (sx32_small dl) by lia.
  step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; clear - K5 DLN HDL Hn; lia| clear K5].
  step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; clear - K6 HDL; lia| clear K6].
  step.
  do 4 step. step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (AGL1 : agree_on (lib_addr OW) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn. split; [| exact I].
    destruct Ha as [Ha|(b & Hb & Hr)]; [revert Ha; unfold LIBW_S; cbn [rin_ivs fst snd]; unfold BnHeapA.ACEIL in *; lia|].
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & BC & _). unfold BnHeapA.ACEIL in *. lia. }
  assert (RS1 : realloc_statics m1) by (exact (realloc_statics_agree OW m m1 RS AGL1)).
  apply evt_done.
  eapply (CRYPTO_reallocI_walkAp REA) with (lo := lo) (n := n) (n0 := n0) (p := dp) (OW := OW) (LB := LB);
    [exact HEAP1| exact HDIN| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_REALLOC2_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; lia| rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| assumption| exact TP
    | rewrite unsigned_lit by (clear; lia); reflexivity
    | exact RS1| reflexivity| reflexivity| lia| exact CRED
    | rewrite ESP; uw_call_mu_tac m 80 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_sint_realloc CTX)|].
  intros p' Σ' ms' Hp PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & C & -> & MI2 & ST2 & AG2 & CR2 & BR2 & HEAP2 & ACC2 & (jk & BLK) & OLD2).
  clear OLD2.
  unfold MallocRep.wz in *. rewrite ESP in ST2, AG2.
  rewrite (ret_pc_even 0x224524) by (lia || reflexivity).
  pose proof BR2 as (C0 & C16 & _ & CCE & CIMG).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; alia).
  set (OW2 := lb_remove dp OW) in *.
  assert (HBIN2o : In (gb, G, 24) OW2) by (subst OW2; apply lb_remove_In_map; [exact HBIN| cbn; exact NE]).
  assert (HBIN2 : In (gb, G, 24) (((p', C, n) :: OW2) ++ LB)) by (right; apply in_or_app; left; exact HBIN2o).
  assert (INS2' : In bsrc (OW2 ++ LB)).
  { subst OW2. apply in_app_iff in INS. apply in_or_app. destruct INS as [Hb|Hb]; [left; apply lb_remove_In_map; [exact Hb| exact NSD]| right; exact Hb]. }
  assert (INS2 : In bsrc (((p', C, n) :: OW2) ++ LB)) by (right; exact INS2').
  assert (SUB2 : forall b, In b (OW2 ++ LB) -> In b (OW ++ LB)) by (subst OW2; intros b Hb; exact (lb_remove_app_incl1 _ _ _ _ Hb)).
  pose proof (AH_offsh _ _ _ _ (p', C, n) HEAP2 (or_introl eq_refl)) as OSHC. cbn [blk_addr blk_size fst snd] in OSHC.
  pose proof (AH_disjoint_gen _ _ _ _ (p', C, n) (gb, G, 24) HEAP2 (or_introl eq_refl) HBIN2
                ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map_iff; exists (gb, G, 24); split; [reflexivity| exact HBIN'])) as DJB.
  cbn [blk_addr blk_size blk_id fst snd] in DJB.
  pose proof (AH_disjoint_gen _ _ _ _ (p', C, n) bsrc HEAP2 (or_introl eq_refl) INS2
                ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map; exact INS)) as DJS.
  cbn [blk_addr blk_size blk_id fst snd] in DJS.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; alia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HB; [| intros a Ha; right; right; exists (gb, G, 24); split; [apply in_or_app; left; exact HBIN2o| cbn; cbn in Ha; alia]].
  apply (bytes_at_agree _ _ _ _ _ AG2) in SRC; [| intros a Ha; right; right; exists bsrc; split; [exact INS2'| lia]].
  ablock HEAP2 HBIN2 ACCB2 OFFB2.
  destruct (AH_shb _ _ _ _ HEAP2) as [SHB1' SHB2'].
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
  assert (OFF2 : offshW [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24)]%Z) by (cbn [offshW]; alia).
  rename MU1 into MU0. clear HEAP1 RS1 ACCB SHB1 SHB2 OFF.
  lazymatch type of SRC with ?T => change (frozen T) in SRC end.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC; [exfalso; rewrite ?EC in KC; lia|]. clear KC.
  step. step.
  step. if_cases KS; zify_cond KS; [exfalso; rewrite ?unsigned_lit in KS by alia; clear - KS S1 S2 BS0 Hn; alia|]. clear KS.
  (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD; [exfalso; rewrite ?EC in KD; lia|]. clear KD.
  step. step. step.
  name_mem m3.
  match goal with H : munch _ m2 m3 |- _ => rename H into MU3 end. match goal with H : wmono ctasegs m2 m3 |- _ => rename H into WM3 end.
  match goal with H : stk ctasegs m3 _ _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctasegs m3 |- _ => rename H into MI3 end.
  assert (HEAP3 : AHEAP Σ' ((p', C, n) :: OW2) LB m3).
  { eapply AH_frame; [exact HEAP2| exact MU3| exact WM3|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (gb, G, 24); split; [exact HBIN2| cbn; lia]| constructor]. }
  unfold frozen in SRC. apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU3)) in SRC; [| intros a Ha; cbn [outside]; clear - Ha S1 S2 SLEN DJP BS3 CEIL LO'; alia].
  rewrite ?ESP in ST3.
  apply evt_done. eapply implAp_step_same.
  { eapply asan_memcpy_cpsA with (d := C) (s := GS) (bs := src) (bd := (p', C, n)) (bsrc := bsrc) (lo := lo) (OW := (p', C, n) :: OW2) (LB := LB); try reflexivity;
      rewrite ?ESP, ?SLEN; cbn [blk_addr blk_size fst snd];
      [exact HEAP3| exact ST3| exact CEIL| unfold RT_STACK; lia| unfold USTACK_TOP; lia| uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI3
      | left; reflexivity| lia| exact INS2| exact S1| exact S2| exact SRC| clear - DJS S1 S2; lia| lia| reflexivity]. }
  intros msM PO.
  destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & BYM & WRM).
  unfold MallocRep.wz in *. rewrite ?ESP in STM, AGM. rewrite (ret_pc_even 0x224578) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AGM) in FR; [| intros a Ha; cbn in Ha; split; [left; alia| clear - Ha CCE CEIL LO' SLEN; alia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HB; [| intros a Ha; cbn in Ha; split; [right; right; exists (gb, G, 24); split; [exact HBIN2| cbn; lia]| clear - Ha DJB Hn SLEN; lia]].
  ablock HEAPM HBIN2 ACCBM OFFBM.
  destruct (AH_shb _ _ _ _ HEAPM) as [SHB1M SHB2M].
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24)]%Z mM) as MUM. pose proof (wmono_refl ctasegs mM) as WMM'.
  clear ACCB2 SHB1' SHB2'. try clear MU2. try clear WM2.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. zstep. step. step. step.
  do 9 step. release_frame FR STM (bv_unsigned sp). step. step.      (* [comment removed for export] *)
  name_mem m9.
  apply evt_done. apply (K p' Σ' _ Hp).
  unfold ascopy_postA, MallocRep.wz.
  do 16 eexists. exists m9, C. split; [reflexivity|].
  assert (MU9 : munch [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24)]%Z mM m9) by assumption.
  split; [assumption|]. split; [assumption|].
  assert (HEAP9 : AHEAP Σ' ((p', C, n) :: OW2) LB m9).
  { eapply AH_frame; [exact HEAPM| exact MU9| apply wmono_refl || assumption|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (gb, G, 24); split; [exact HBIN2| cbn; lia]| constructor]. }
  split.
  { (* [comment removed for export] *)
    unfold apres_but.
    assert (FRM : forall a, aclient_addr (OW2 ++ LB) (bv_unsigned sp) a /\ ~ (G <= a < G + 24) -> outside [(bv_unsigned sp - 80, bv_unsigned sp); (G, G + 24)]%Z a).
    { intros a [Ha Hnb]. cbn [outside]. split; [| split; [clear - Hnb; lia| exact I]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (SUB2 b Hb)) as (_ & _ & _ & BC & _). clear - Hr BC CEIL LO'. alia. }
    assert (FRM0 : forall a, aclient_addr (OW2 ++ LB) (bv_unsigned sp) a /\ ~ (G <= a < G + 24) -> outside [(bv_unsigned sp - 80, bv_unsigned sp)]%Z a).
    { intros a Ha. pose proof (FRM a Ha) as O. cbn [outside] in O |- *. clear - O. tauto. }
    assert (NEWB : forall a, aclient_addr (OW2 ++ LB) (bv_unsigned sp) a -> ~ (C <= a < C + n)).
    { intros a Ha HAr. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
      - clear - Ha HAr CCE CEIL LO'. alia.
      - eapply (blk_not_static _ ((p', C, n) :: OW2) LB m2 (p', C, n) a HEAP2 (or_introl eq_refl)); [cbn; clear - HAr; lia | exact Ha].
      - assert (NEb : blk_id b <> p') by (intros E; apply Hp; rewrite <- E; apply in_map; exact (SUB2 b Hb)).
        pose proof (AH_disjoint_gen _ _ _ _ b (p', C, n) HEAP2 (or_intror Hb) (or_introl eq_refl) NEb) as DJ. cbn in DJ. clear - DJ Hr HAr. lia. }
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU0)| exact FRM0]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG2| intros a [[Ha|[Ha|Ha]] _]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU3)| exact FRM]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGM| intros a [Ha Hnb]; split; [| rewrite SLEN; exact (NEWB a Ha)];
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; apply in_block_mono with (L1 := OW2 ++ LB); [intros b Hb; right; exact Hb| exact Ha]]]|].
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU9)| exact FRM]. }
  split; [exact CR2|]. split; [exact BR2|]. split; [exact HEAP9|].
  split.
  { unfold asn1_string_cells, MallocRep.wz. match goal with H : rw_cells ctasegs m9 G _ |- _ => exact H end. }
  pose proof (rw_cells_of_bytes _ C src BYM WRM) as HC. rewrite <- SLEN, Nat2Z.id.
  first [ exact HC
        | eapply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU9)); [exact HC|];
          intros a Ha; cbn [outside cells_size csize] in Ha |- *; clear - Ha DJB DJS S1 S2 SLEN CCE CEIL LO' Hn; alia ].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASN1_STRING_copy_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (gb dp : bptr) (bstr bsrc : block) (G dl ty0 D0 n0 STR n ty GS : Z) (src : list byte)
    (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_COPY_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> realloc_statics m -> bv_unsigned ra mod 2 = 0 ->
  In (gb, G, ASN1_STRING_SIZE) OW -> rw_cells ctasegs m G (asn1_string_cells dl ty0 D0 0) -> 0 < dl < 2^31 -> dl <> n ->
  In (dp, D0, n0) OW -> gb <> dp ->
  In bstr (OW ++ LB) -> blk_id bstr <> gb -> blk_id bstr <> dp -> blk_addr bstr <= STR -> STR + ASN1_STRING_SIZE <= blk_addr bstr + blk_size bstr ->
  rw_cells ctasegs m STR (asn1_string_cells n ty GS 0) -> STR mod 8 = 0 -> 0 <= ty < 2^31 ->
  In bsrc (OW ++ LB) -> blk_id bsrc <> gb -> blk_id bsrc <> dp -> blk_addr bsrc <= GS -> GS + n <= blk_addr bsrc + blk_size bsrc ->
  bytes_at ctasegs m GS src -> Z.of_nat (length src) = n ->
  a0 = wz G -> a1 = wz STR -> 0 < n <= 0x8000000 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_STRING_COPY_A (bv_unsigned ra :: ras) ->
  (forall p' Σ' ms', ~ In p' (map blk_id (OW ++ LB)) ->
     ascopy_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB G dp n ty lo src m p' Σ' ms' ->
     implAp (k (Some p')) Σ' Q ms') ->
  implAp (AReallocI dp n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_COPY_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI TP RS RAEV HBIN HB HDL DLN HDIN NE INT NTG NTD T1 T2 HS STAL TY INS NSG NSD S1 S2 SRC SLEN -> -> Hn CRED UW CTX K.
  pose proof LO as LO'. unfold ASN1_STRING_COPY_STACK_A, SINT_COPY_STACK_A, CRYPTO_REALLOC2_STACK, RT_STACK, ASN1_STRING_COPY_A, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (gb, G, ASN1_STRING_SIZE) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4).
  pose proof (AH_range_gen _ _ _ _ bstr HEAP INT) as (BT0 & _ & _ & BT3 & BT4).
  pose proof (AH_range_gen _ _ _ _ bsrc HEAP INS) as (BS0 & _ & _ & BS3 & BS4).
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  assert (EA : bv_unsigned (Z_to_bv 64 G) = G) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 STR) = STR) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  pose proof (AH_disjoint_gen _ _ _ _ bstr (gb, G, 24) HEAP INT HBIN' NTG) as DJT. cbn [blk_addr blk_size blk_id fst snd] in DJT.
  ablock HEAP HBIN' ACCB OFFB. ablock HEAP INT ACCT OFFT.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold asn1_string_cells, MallocRep.wz in HB, HS.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (G, G + 24)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 48, bv_unsigned sp); (G, G + 24)]%Z) by (cbn [offshW]; alia).
  assert (SEPG : G + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= G) by (clear - BB3 CEIL LO'; alia).
  assert (SEPT : STR + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= STR) by (clear - BT3 T1 T2 CEIL LO'; alia).
  lazymatch type of SRC with ?T => change (frozen T) in SRC end.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 48%nat ST. do 7 step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?ET in K0; clear - K0 BT0 T1 CEIL; alia|]. clear K0.
  step. step.
  step. rewrite (sx32_small n) by lia.
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?ab_signed_small in K1 by lia; clear - K1 Hn; lia|]. clear K1.
  (* [comment removed for export] *)
  step. step. step. ab_shload 4.
  step. rewrite (sx32_small ty) by lia. step. brc.
  step.
  (* [comment removed for export] *)
  step. step. step. step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  match goal with H : stk ctasegs m1 _ _ |- _ => rename H into ST1 end. match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (gb, G, 24); split; [exact HBIN'| cbn; lia]| constructor]. }
  assert (RS1 : realloc_statics m1).
  { unfold realloc_statics in *. eapply ro_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact RS|].
    intros a Ha. cbn [outside]. cbn in Ha. unfold CR_REALLOC_IMPL in Ha. clear - Ha BB4 CEIL LO' C1. alia. }
  unfold frozen in SRC. apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU1)) in SRC;
    [| intros a Ha; cbn [outside]; pose proof (AH_disjoint_gen _ _ _ _ bsrc (gb, G, 24) HEAP INS HBIN' NSG) as DJS; cbn in DJS; clear - Ha DJS S1 S2 SLEN BS3 CEIL LO'; alia].
  try (apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU1)) in HS; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; clear - Ha DJT T1 T2 SEPT; lia]).
  rewrite ?ESP in ST1.
  apply evt_done.
  eapply (sint_copy_walkA) with (lo := lo) (gb := gb) (dp := dp) (bsrc := bsrc) (G := G) (dl := dl) (D0 := D0) (n0 := n0) (GS := GS) (n := n) (src := src) (OW := OW) (LB := LB)
      (ras := bv_unsigned ra :: ras);
    [exact HEAP1| rewrite ESP; exact ST1| exact CEIL| rewrite ESP; unfold SINT_COPY_STACK_A, CRYPTO_REALLOC2_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; lia| rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI1| exact TP| exact RS1
    | rewrite unsigned_lit by (clear; lia); reflexivity
    | exact HBIN| unfold asn1_string_cells, MallocRep.wz; exact HB| exact HDL| exact DLN| exact HDIN| exact NE
    | exact INS| exact NSG| exact NSD| exact S1| exact S2| exact SRC| exact SLEN| reflexivity| reflexivity| reflexivity| exact Hn| exact CRED
    | rewrite ESP; uw_call_mu_tac m 48 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_copy_sint CTX)|].
  intros p' Σ' ms' Hp PO.
  destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & F' & fc' & m2 & D' & -> & MI2 & ST2 & AP2 & CR2 & BR2 & HEAP2 & HG2 & HD2).
  unfold MallocRep.wz in *. rewrite ?ESP in ST2, AP2. unfold ASN1_STRING_SIZE in AP2.
  rewrite (ret_pc_even 0x224340) by (clear; lia).
  set (OW2 := lb_remove dp OW) in *.
  assert (HBIN2o : In (gb, G, 24) OW2) by (subst OW2; apply lb_remove_In_map; [exact HBIN| cbn; exact NE]).
  assert (HBIN2 : In (gb, G, 24) (((p', D', n) :: OW2) ++ LB)) by (right; apply in_or_app; left; exact HBIN2o).
  assert (INT2' : In bstr (OW2 ++ LB)).
  { subst OW2. apply in_app_iff in INT. apply in_or_app. destruct INT as [Hb|Hb]; [left; apply lb_remove_In_map; [exact Hb| exact NTD]| right; exact Hb]. }
  assert (INT2 : In bstr (((p', D', n) :: OW2) ++ LB)) by (right; exact INT2').
  assert (SUB2 : forall b, In b (OW2 ++ LB) -> In b (OW ++ LB)) by (subst OW2; intros b Hb; exact (lb_remove_app_incl1 _ _ _ _ Hb)).
  pose proof BR2 as (D0' & D16 & _ & DCE & DIMG).
  pose proof (AH_disjoint_gen _ _ _ _ (p', D', n) (gb, G, 24) HEAP2 (or_introl eq_refl) HBIN2
                ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map_iff; exists (gb, G, 24); split; [reflexivity| exact HBIN'])) as DJB.
  cbn [blk_addr blk_size blk_id fst snd] in DJB.
  pose proof (AH_disjoint_gen _ _ _ _ (p', D', n) bstr HEAP2 (or_introl eq_refl) INT2
                ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map; exact INT)) as DJTN.
  cbn [blk_addr blk_size blk_id fst snd] in DJTN.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AP2) in FR; [| intros a Ha; cbn in Ha; split; [left; alia| clear - Ha SEPG; lia]].
  apply (rw_cells_agree _ _ _ _ _ AP2) in HS; [| intros a Ha; cbn in Ha; split; [right; right; exists bstr; split; [exact INT2'| lia]| clear - Ha DJT T1 T2; lia]].
  unfold asn1_string_cells, MallocRep.wz in HG2.
  ablock HEAP2 HBIN2 ACCB2 OFFB2. ablock HEAP2 INT2 ACCT2 OFFT2.
  destruct (AH_shb _ _ _ _ HEAP2) as [SHB1' SHB2'].
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (G, G + 24)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
  clear ACCB ACCT SHB1 SHB2 HEAP1 RS1 MI1 ST1.
  lazymatch type of HD2 with ?T => change (frozen T) in HD2 end.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by (clear; lia); clear - K2; lia|]. clear K2.
  step. step. step. zstep. step.
  step. zstep. zstep. step.
  step. step.
  do 5 step. release_frame FR ST2 (bv_unsigned sp). step. step.
  name_mem m9.
  apply evt_done. apply (K p' Σ' _ Hp).
  unfold ascopy_postA, MallocRep.wz.
  do 16 eexists. exists m9, D'. split; [reflexivity|].
  assert (MU9 : munch [(bv_unsigned sp - 48, bv_unsigned sp); (G, G + 24)]%Z m2 m9) by assumption.
  split; [assumption|]. split; [assumption|].
  assert (HEAP9 : AHEAP Σ' ((p', D', n) :: OW2) LB m9).
  { eapply AH_frame; [exact HEAP2| exact MU9| apply wmono_refl || assumption|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (gb, G, 24); split; [exact HBIN2| cbn; lia]| constructor]. }
  split.
  { (* [comment removed for export] *)
    unfold apres_but in AP2 |- *.
    assert (FRM : forall a, aclient_addr (OW2 ++ LB) (bv_unsigned sp) a /\ ~ (G <= a < G + 24) -> outside [(bv_unsigned sp - 48, bv_unsigned sp); (G, G + 24)]%Z a).
    { intros a [Ha Hnb]. cbn [outside]. split; [| split; [clear - Hnb; lia| exact I]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (SUB2 b Hb)) as (_ & _ & _ & BC & _). clear - Hr BC CEIL LO'. alia. }
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact FRM]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AP2| intros a [Ha Hnb]; split; [| exact Hnb];
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]]|].
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU9)| exact FRM]. }
  split; [exact CR2|]. split; [exact BR2|]. split; [exact HEAP9|].
  split.
  { unfold asn1_string_cells, MallocRep.wz. match goal with H : rw_cells ctasegs m9 G _ |- _ => exact H end. }
  unfold frozen in HD2.
  eapply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU9)); [exact HD2|].
  intros a Ha. cbn [outside cells_size csize] in Ha |- *. rewrite ?Nat.add_0_r, ?Z2Nat.id in Ha by (clear - Hn; lia). clear - Ha DJB DCE CEIL LO' Hn. alia.
Qed.

End WithRT.
