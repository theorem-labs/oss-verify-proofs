(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_defs Atp_h_defs Atp_h_push Atp_h_find Atp_h_split Atp_h_splitinto El_empl El_defs El_hdr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma map_pview_nil : forall D r, map (pview D) (poffs r) = [] <-> r = [].
Proof.
  intros D r. split; [| intros ->; reflexivity]. intros E. destruct r as [|z l]; [reflexivity| exfalso].
  rewrite poffs_eq in E. apply (f_equal (@length _)) in E. rewrite length_map in E. pose proof (poffs_of_nonnil 0 (z :: l)).
  destruct (poffs_of 0 (z :: l)); [congruence| discriminate].
Qed.

Lemma vec_post_of_empl : forall (sp0 : Z) (gp s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (s st s' : PState) (LB : list block) (lo B D : Z) (d : list Z) (init : bool) (m m2 : mem) (els : list (Z * Z)) (P : nat) (v' : vec) (ms' : machine_state)
    (j0 j48 jel jpa j416 j441 : list byte) (sel : Z),
  empl_post sp0 gp (Z_to_bv 64 (el_action d)) s9 s10 s11 F fc st LB lo B els P m2 v' s' ms' ->
  P = el_P d -> els ++ repeat (0, 0) (P - length els) = el_els D d ->
  ps_fa st = ps_fa s -> ps_so st = ps_so s ->
  lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m m2 -> sj_statics m2 init -> payload_ok m2 LB D d ->
  alloc_ceiling <= sp0 -> GLOBALS_TOP <= sp0 -> (forall a, in_block LB a -> a < alloc_ceiling) ->
  rw_cells usegs m2 sp0 [CB 8 j0] -> rw_cells usegs m2 (sp0 + 48) [CB 248 j48] -> rw_cells usegs m2 (sp0 + 296) [CB 16 jel] -> rw_cells usegs m2 (sp0 + 312) [CB 80 jpa] ->
  rw_cells usegs m2 (sp0 + 416) [CB 4 j416; C4 (Z_to_bv 64 sel)] -> 0 <= sel < 8 -> (el_fd_ok d = true -> sel = el_sel d) ->
  rw_cells usegs m2 (sp0 + 424) [C8 (Z_to_bv 64 (if el_fd_ok d then D + zlength d else 0)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j441] ->
  rw_cells usegs m2 (sp0 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  vec_post sp0 gp s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra F fc s LB lo B D d init m v' s' ms'.
Proof.
  intros until sel; intros PO -> EELS FA SO PRES2 SJS2 PL2 CEIL GLO BLB J0 J48 JEL JPA XSEL SELB SELD XFD SAVE.
  unfold GLOBALS_TOP in GLO. try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  destruct PO as (x1 & t0 & t1 & t2 & y0 & y1 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & y2 & y3 & y4 & y5 & y7 & y8 & t3 & t4 & t5 & t6 & m3 & errv3 & A3 & cap3 & b3 & jr3
                  & c48 & c56 & c64 & c72 & c80 & -> & -> & CAP3 & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & HEAP3 & VR3 & SCR3 & PRES3).
  pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
  assert (FRCL3 : forall a, sp0 <= a < sp0 + 528 -> ~ (sp0 + 8 <= a < sp0 + 48) -> ~ (sp0 + 392 <= a < sp0 + 416) -> lx_client LB sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] a).
  { intros a Ha N1 N2. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
  apply (rw_cells_agree _ _ _ _ _ AG3) in J0; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in J48; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in JEL; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in JPA; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in XSEL; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in XFD; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
  unfold vec_post. do 23 eexists. exists m3, errv3, A3, cap3, b3, jr3. do 12 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [reflexivity|]. split; [exact CAP3|].
  split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|]. split; [congruence|]. split; [congruence|].
  split; [exact HEAP3|].
  split; [rewrite <- EELS; exact VR3|].
  split. { eapply lx_pres_trans; [exact PRES2|]. eapply (lx_pres_sub LB (sp0 + 528) _ _ _ _ _ _ PRES3); [lia| intros b0 Hb0; exact Hb0|].
           intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB a IB); lia| lia]. }
  split. { eapply sj_statics_agree; [exact AG3| | exact SJS2]. intros a Ha. apply sjs_addr_client; [exact Ha|].
           unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. clear - Ha GLO. lia. }
  split. { eapply payload_ok_agree; [exact AG3| exact PL2|]. intros b a Hb Ha.
           assert (AC : a < alloc_ceiling) by (apply BLB; exists b; split; [exact Hb| exact Ha]).
           split; [cbn [rin_ivs fst snd]; clear - AC CEIL; lia| right; left; exists b; split; [exact Hb| exact Ha]]. }
  split; [exact J0|]. split; [exact SCR3|]. split; [exact J48|]. split; [exact JEL|]. split; [exact JPA|]. split; [exact XSEL|]. split; [exact SELB|]. split; [exact SELD|].
  split; [exact XFD| exact SAVE].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma splitinto_nil_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B RV FD : Z) (errv : word)
      (v0 v8 v16 : list byte),
    RHEAP s LB0 m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (64 + 80 + 128 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    q <= RV -> RV + 24 <= FD -> FD + 16 <= B -> q mod 16 = 0 ->
    rw_cells usegs m RV [CB 8 v0; CB 8 v8; CB 8 v16] ->
    rw_cells usegs m FD [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    implM usegs (vpushes lops 0 vec0) s
          (splitinto_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B RV FD 0 [] m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 RV) (Z_to_bv 64 FD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_SPLITINTO) fc None m (seg_rom usegs)).
  Proof.
    intros until v16; intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QRV RVFD FDB Q16 XRV XFD.
    unfold RMALLOC_STACK, GLOBALS_TOP, ATP_SPLITINTO in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = ltac:(let v := eval vm_compute in LX_ERRNO in exact v)) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b0 & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (munch_refl [(q - 80, q); (RV, RV + 24); (FD, FD + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB0 q [(RV, RV + 24); (FD, FD + 16)] a -> outside [(q - 80, q); (RV, RV + 24); (FD, FD + 16)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| split; [clear -HX; lia| exact I]]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    unfold implM. iprefix.
    step. carve_frame 64%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. step.
    if_lia. step. step. step. hstep. hstep. hstep. step.
    if_cases K; zify_cond K; [clear K| exfalso; lia].
    step. step. step. step. step. release_frame FR ST q. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    ihere. to_implM. rewrite vpushes_O. apply implM_ret.
    apply evt_done. unfold splitinto_post. do 15 eexists. exists m1, errv, 0, 0, (@None bptr), (@nil byte).
    split; [cbv delta [mkR]; reflexivity|].
    split; [reflexivity|]. split; [tauto|]. split; [unfold zlength; cbn [poffs length Z.of_nat]; lia|].
    split; [assumption|]. split; [assumption|]. split; [exact ERR|].
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
             constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [reflexivity|]. split; [reflexivity|].
    split. { cbn [vblocks app]. eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    split. { unfold vrep, vblk. cbn [map poffs zlength length Z.of_nat]. split; [reflexivity|]. split; [lia|]. split; [| split; reflexivity].
             lazymatch goal with H : rw_cells usegs m1 RV _ |- _ => exact H end. }
    split. { replace (0 + zlength (@nil Z)) with 0 by (unfold zlength; cbn; lia). lazymatch goal with H : rw_cells usegs m1 FD _ |- _ => exact H end. }
    eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
  Qed.
  Lemma splitinto_view_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B RV FD D : Z) (d : list Z) (errv : word)
      (v0 v8 v16 : list byte),
    RHEAP s LB0 m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (64 + 80 + 128 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    q <= RV -> RV + 24 <= FD -> FD + 16 <= B -> q mod 16 = 0 ->
    payload_ok m LB0 D d \/ (D = 0 /\ d = []) ->
    rw_cells usegs m RV [CB 8 v0; CB 8 v8; CB 8 v16] ->
    rw_cells usegs m FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (zlength d))] ->
    implM usegs (vpushes lops (length (atp_parts d)) vec0) s
          (splitinto_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B RV FD D d m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 RV) (Z_to_bv 64 FD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_SPLITINTO) fc None m (seg_rom usegs)).
  Proof.
    intros until v16; intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QRV RVFD FDB Q16 [PL|[-> ->]] XRV XFD.
    - exact (splitinto_spec HM HF ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 q lo B RV FD D d errv v0 v8 v16
               HEAP AUX QB B63 ST CEIL GLO LO ERR MI QRV RVFD FDB Q16 PL XRV XFD).
    - change (length (atp_parts [])) with 0%nat. change (zlength (@nil Z)) with 0 in XFD.
      exact (splitinto_nil_spec ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 q lo B RV FD errv v0 v8 v16
               HEAP AUX QB B63 ST CEIL GLO LO ERR MI QRV RVFD FDB Q16 XRV XFD).
  Qed.


  Lemma lftoi_vec_cps : forall {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (s : PState) (LB : list block) (D : Z) (d : list Z) (init : bool) (lo B : Z) (errv canary : word),
    RHEAP s LB m -> lx_statics m -> sj_statics m init -> stderr_wfile m -> ssp_cells m canary ->
    rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^62 ->
    stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
    mem_inv usegs m ->
    bv_unsigned sp mod 16 = 0 ->
    payload_ok m LB D d ->
    frm0 fc ->
    a0 = wz D -> a1 = wz (zlength d) ->
    (forall v s' ms', vec_post (bv_unsigned sp - 528) gp s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra F fc s LB lo B D d init m v s' ms' -> implM usegs (k v) s' Q ms') ->
    implM usegs (mbind (vpushes lops (el_P d) vec0) k) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ) fc None m (seg_rom usegs)).
  Proof.
    intros until canary.
    intros HEAP LXS SJS SEW SSP AUX SPB B63 ST CEIL GLO LO ERR TP MI AL16 PL FRM -> -> HK.
    unfold LX_FUZZ, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *. unfold MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. replace (errno_addr (Z_to_bv 64 RATP)) with 980196 in ERR by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof PL as (PB & PRNG & D0 & DN & DLEN & PIN).
    assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity. pose proof DLEN as DLEN'. change (2^26) with 67108864 in DLEN'.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (bv_unsigned sp) [LXW_SJ; LXW_UNW] a -> outside [(bv_unsigned sp - 528, bv_unsigned sp)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    unfold implM. iprefix.

    eapply evt_cut; [eapply hdr_spec; [exact HEAP| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| exact MI| exact PL]|].
    cbv beta. intros ms1 PO. unfold hdr_post in PO. cbv zeta in PO.
    destruct PO as (t0' & t1' & t2' & xs0 & a0' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & j0 & c8 & c16 & c24 & c32 & c40 & j48 & jel & jpa & jv & j416 & jfd8 & j441 & sel
                    & -> & MU & WM & MI1 & ST1 & J0 & SCR & J48 & JEL & JPA & JV & XSEL & SELB & SELD & XFD & XPAD & SAVE).
    clear t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI.
    set (usp := bv_unsigned sp) in *.
    remember (usp + -528) as sp0 eqn:Esp0.
    replace (usp - 528) with sp0 in MU, CLI by lia.
    assert (SPQ : sp0 + 528 = usp) by lia.
    apply (rw_cells_split_CB usegs _ _ [] 24 jv [] [8; 8; 8]%nat) in JV; [| reflexivity]. cbn [mk_CB_cells app] in JV.
    hstep. hstep. hstep. hstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.

    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in ERR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
    assert (HEAP1 : RHEAP s LB mc).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok mc B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB usp [LXW_SJ; LXW_UNW] m mc) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
    assert (SJS1 : sj_statics mc init).
    { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
      cbn [outside]; split; [lia| exact I]. }
    assert (PL1 : payload_ok mc LB D d).
    { eapply payload_ok_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| exact PL|]. intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
      pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & _ & BS). unfold LXW_SJ, LXW_UNW, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha BS. lia. }
    rewrite <- SPQ in PRES1. clear MU WM HEAP AUX SJS PL PB.
    assert (VW : (payload_ok mc LB (if el_fd_ok d then D + 10 else 0) (el_rem d) \/ ((if el_fd_ok d then D + 10 else 0) = 0 /\ el_rem d = []))
                 /\ (if el_fd_ok d then zlength d - 10 else 0) = zlength (el_rem d)).
    { destruct (el_fd_ok d) eqn:FD.
      - pose proof (el_rem_fd d FD) as [_ EL]. split; [left; apply payload_ok_rem; [exact PL1| exact FD]| lia].
      - pose proof (el_rem_nofd d FD) as (ER & _ & _). rewrite ER. split; [right; split; reflexivity| reflexivity]. }
    destruct VW as [VPL VLEN]. rewrite VLEN in XFD.
    set (D' := if el_fd_ok d then D + 10 else 0) in *.
    assert (AL0 : sp0 mod 16 = 0) by (subst sp0; clear - AL16; replace (usp + -528) with (usp + (-33) * 16) by lia; rewrite Z.mod_add by lia; exact AL16).
    ihere. to_implM. unfold el_P, el_parts.
    replace (Nat.max (length (atp_parts (el_rem d))) 2) with (length (atp_parts (el_rem d)) + (Nat.max (length (atp_parts (el_rem d))) 2 - length (atp_parts (el_rem d))))%nat by lia.
    apply implM_vpushes_split. eapply implM_bind.
    { eapply splitinto_view_spec with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| (clear - B63; lia)| exact ST1| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| exact ERR| exact MI1
        | lia| lia| lia| exact AL0| exact VPL| exact JV| exact XFD]. }
    cbv beta. intros v1 st1 ms1 PO. unfold splitinto_post in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & A2 & cap2 & blk2 & jr2
                    & -> & -> & BNIL & Ecap2 & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & HEAP2 & VR2 & XFD2 & PRES2).
    replace (ret_pc (Z_to_bv 64 246052)) with (Z_to_bv 64 246052) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
    assert (FRCL : forall a, sp0 <= a < sp0 + 528 -> ~ (sp0 + 392 <= a < sp0 + 416) -> ~ (sp0 + 424 <= a < sp0 + 440) ->
                     lx_client LB sp0 [(sp0 + 392, sp0 + 392 + 24); (sp0 + 424, sp0 + 424 + 16)] a).
    { intros a Ha N1 N2. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in J0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in SCR; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in J48; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in JEL; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in JPA; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in XSEL; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in XPAD; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    assert (SJS2 : sj_statics m2 init).
    { eapply sj_statics_agree; [exact AG2| | exact SJS1]. intros a Ha. apply sjs_addr_client; [exact Ha|].
      unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. clear - Ha GLO LO SPQ. lia. }
    assert (BLB2 : forall a, in_block LB a -> a < alloc_ceiling) by exact BLB.
    assert (PRES2' : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply (lx_pres_sub LB (sp0 + 528) _ _ _ _ _ _ PRES2); [lia| intros b0 Hb0; exact Hb0|].
      intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB2 a IB); lia| lia]. }
    assert (PL2 : payload_ok m2 LB D d).
    { eapply payload_ok_agree; [exact AG2| exact PL1|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP1 Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. split; [cbn [rin_ivs fst snd]; clear - Ha BC CEIL LO SPQ; lia| right; left; exists b; split; [exact Hb| exact Ha]]. }
    clear AG2 PRES2 PRES1 HEAP1 AUX1 SJS1 PL1 VPL JV XFD.
    assert (XFD3 : rw_cells usegs m2 (sp0 + 424) [C8 (Z_to_bv 64 (if el_fd_ok d then D + zlength d else 0)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j441]).
    { replace (if el_fd_ok d then D + zlength d else 0) with (D' + zlength (el_rem d)).
      - eapply (rw_cells_join _ _ _ _ _ XFD2 XPAD). cbn [cells_size csize Nat.add]. lia.
      - subst D'. destruct (el_fd_ok d) eqn:FD; [pose proof (el_rem_fd d FD) as [_ EL]; lia| pose proof (el_rem_nofd d FD) as (ER & _ & _); rewrite ER; reflexivity]. }
    clear XFD2 XPAD.
    assert (ELS' : map (pview D') (poffs (el_rem d)) = map (pview (D + 10)) (poffs (el_rem d))).
    { subst D'. destruct (el_fd_ok d) eqn:FD; [reflexivity| pose proof (el_rem_nofd d FD) as (ER & _ & _); rewrite ER; reflexivity]. }
    pose proof (atp_P_bound (el_rem d)) as PBD. unfold atp_P in PBD. rewrite <- (poffs_length (el_rem d)) in *.
    assert (ELEN : length (map (pview D') (poffs (el_rem d))) = length (poffs (el_rem d))) by apply length_map.
    rewrite <- ELEN. replace (zlength (poffs (el_rem d))) with (zlength (map (pview D') (poffs (el_rem d)))) in * by (unfold zlength; rewrite ELEN; reflexivity).
    assert (RLEN : zlength (el_rem d) <= zlength d) by (subst D'; destruct (el_fd_ok d) eqn:FD; [pose proof (el_rem_fd d FD) as [_ EL]; lia| pose proof (el_rem_nofd d FD) as (ER & _ & _); rewrite ER; unfold zlength at 1; cbn; lia]).
    eapply (empl_cps HM HF) with (B := B) (lo := lo);
      [exact HEAP2| exact AUX2| lia| (clear - B63; lia)| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK; lia| eassumption| assumption| exact AL0
      | exact VR2| exact Ecap2| unfold zlength in *; rewrite ELEN; clear - PBD DLEN' ZD RLEN; lia| | exact SCR|].
    { rewrite <- BNIL. split; [intros ->; reflexivity| intros E; apply map_pview_nil in E; exact E]. }
    cbv beta. intros v2 st2 ms2 PO.
    apply HK. replace (usp - 528) with sp0 by lia. eapply vec_post_of_empl; [exact PO| unfold el_P, el_parts; rewrite <- poffs_length, <- ELEN; reflexivity
      | unfold el_els, el_P, el_parts; rewrite <- ELS', <- poffs_length, <- ELEN; reflexivity
      | exact FA2| exact SO2| exact PRES2'| exact SJS2| exact PL2| lia| unfold GLOBALS_TOP; lia| exact BLB2
      | exact J0| exact J48| exact JEL| exact JPA| exact XSEL| exact SELB| exact SELD| exact XFD3| exact SAVE].
  Qed.
End Proofs.
End WithCeiling0.
