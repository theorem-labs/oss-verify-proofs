(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module RF_ntf_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_C.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame psegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write psegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write psegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv psegs mX |- _ =>
      apply (mem_inv_store psegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a3 a4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x157c4) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

(* [comment removed for export] *)
Lemma rntf_deqself : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some g ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x157bc) fc None m (seg_rom psegs)).
Proof using .
  intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold alloc_ceiling, RCTX in *.
  st1.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok psegs _ _ (actives st) sc (Z_to_bv 64 (342928 + sc * 8 + 80)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
  clear ACTS.
  rraw_store_finish (342928 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
  assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
  { unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
  rewrite EQ.
  apply evt_done. unfold rat9c_post. nexists 3%nat. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + apply rfree_fp_ctx. unfold RCTX. lia. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

(* [comment removed for export] *)
Lemma rntf_deq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g nx pv : aptr) (sc lo : Z),
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  (active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
  a2 = pw st (active st sc) ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15738) fc None m (seg_rom psegs)).
Proof using .
  intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold alloc_ceiling, RCTX in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (342928, 342928 + 928)]%Z m) as MU.
  (* [comment removed for export] *)
  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. clear CH.
  (* [comment removed for export] *)
  rmeta_open (conc st pv) MUp WMp.
  rmeta_chunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
  set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
  (* [comment removed for export] *)
  rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. clear CH.
  (* [comment removed for export] *)
  rmeta_open (conc st nx) MUn WMn.
  rmeta_chunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
  set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
  replace (wa (342928 + 80 + 8 * sc)) with (Z_to_bv 64 (342928 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
  assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
  assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
  st1. clear RDA.
  assert (EQmid : deq_mid (LActive sc) g st =
                  if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
  { unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
    rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (HA : optr_eqb (active st sc) (Some g) = false).
    { destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
      unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
    rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
    apply evt_done. unfold rat9c_post. nexists 3%nat. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
  - (* [comment removed for export] *)
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
    rewrite HA, optr_eqb_refl in EQmid.
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. clear CH. st1.
    pose proof MR2 as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok psegs _ _ (actives st2) sc (Z_to_bv 64 (342928 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
    clear ACTS.
    rraw_store_finish (342928 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
    rewrite <- EQmid in MR3. subst a2.
    apply evt_done. unfold rat9c_post. nexists 3%nat. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.

(* [comment removed for export] *)
Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof using .
  intros Hn. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.

Lemma act_mask_le4 f y z : 0 <= f < 2^32 -> 1 <= y <= 2^32 -> z mod 2^32 = (y - 1) mod 2^32 ->
  le4 (Z_to_bv 64 (Z.land (sxv f) (bv_unsigned (Z_to_bv 64 z)))) = le4 (wz (Z.land f (y - 1))).
Proof using .
  intros Hf Hy Hz. apply le4_congr.
  pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
  assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
  assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
  { split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
  rewrite unsigned_lit, wz_unsigned by lia.
  rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15828) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

(* [comment removed for export] *)
Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
  let st1 := upd_meta g clr_links stm in
  rmrep stm m -> mem_inv psegs m -> meta_slot stm g -> 0 <= sc < 48 ->
  (if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
  (an = true -> forall a, active st1 sc = Some a ->
     meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
     /\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x157c4) fc None m (seg_rom psegs)).
Proof using .
  intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
  pose proof (rmeta_slot_bounds stm m g MR MSL) as GB.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold alloc_ceiling, RCTX in *.
  pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.
  (* [comment removed for export] *)
  rmeta_open (conc stm g) MUg WMg.
  rmeta_chunk MR MSL CH.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st1 mX)
      by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tclose]);
    clear MUg WMg CH
  end.
  assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono psegs m m' ->
                 rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
  { intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
    cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
  assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
  assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
    cbn [pd_st].
    apply evt_done. unfold rat00_post. nexists 9%nat. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
  - (* [comment removed for export] *)
    destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
    cbn [pd_st].
    (* [comment removed for export] *)
    pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
    assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
    replace (wa (342928 + 80 + 8 * sc)) with (Z_to_bv 64 (342928 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.
    (* [comment removed for export] *)
    st1. destruct (active st1 sc) as [a|] eqn:HA1.
    + (nelim (HACT eq_refl a eq_refl) 9%nat; intros MSa NEa AV0 FRR ba gh Hmem Hgh AI).
      pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. rewrite !Hconc in AB.
      munch_grow MU (conc stm a, conc stm a + 40).
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
      (* [comment removed for export] *)
      rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
      st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.
      (* [comment removed for export] *)
      st1.
      (* [comment removed for export] *)
      destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
      rewrite Hconc in RD8.
      st1.
      pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
      assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
      { rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
      (* [comment removed for export] *)
      st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
      set (y := 2 ^ (g_active_idx gh + 1)).
      st1. st1. rewrite negw_word.
      (* [comment removed for export] *)
      clear CHa. rmeta_open (conc stm a) MUa WMa.
      rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
      pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
      st1. rewrite sx32_wz_sxv by lia.
      st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
      (* [comment removed for export] *)
      assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
      { apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
      amo_step AMO. rewrite ?sx32_wz_sxv by lia.
      st1. if_false.
      amo_step AMO.
      st1. if_false.
      st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
      (* [comment removed for export] *)
      st1. st1. st1.
      (* [comment removed for export] *)
      set (f := m_freed (get_meta_rec st1 a)) in *.
      assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
      { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ACT : act_of st1 a = y - 1).
      { unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
      assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
      assert (Y1 : 1 <= y <= 2^32).
      { unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
      pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
      pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
      pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
      end.
      { unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
        eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | cbn; tclose].
        unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
        fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
        rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
      clear MUa WMa CHa.
      apply evt_done. unfold rat00_post. nexists 9%nat. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
               cbn [ivs_covered]. repeat split; intros x Hx.
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSa | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
      split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR2.
    + (* [comment removed for export] *)
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
      apply evt_done. unfold rat00_post. nexists 9%nat. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR1.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame psegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write psegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write psegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv psegs mX |- _ =>
      apply (mem_inv_store psegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
End RF_ntf_E.

(* [comment removed for export] *)
Module RF_ntf_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A RF_ntf_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Lemma testbit_false_ge a n : 0 <= a < 2^n -> 0 <= n -> forall k, n <= k -> Z.testbit a k = false.
Proof.
  intros Ha Hn k Hk. destruct (Z.eq_dec a 0) as [->|NE]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_lxor_ones64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  Z.lor (Z.lxor a 18446744073709551615) (Z.lxor b 18446744073709551615) = Z.lxor (Z.land a b) 18446744073709551615.
Proof using .
  intros Ha Hb. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !Z.lxor_spec, Z.land_spec.
  destruct (Z.lt_ge_cases n 64) as [L|G].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (testbit_false_ge a 64), (testbit_false_ge b 64) by lia. reflexivity.
Qed.

Lemma usage_sub_word u w : 0 <= u < 2^64 -> 0 <= w < 2^64 ->
  Z_to_bv 64 (u + Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor w 18446744073709551615))) 18446744073709551584)
  = wz (u - (Z.land w 31 + 1)).
Proof using .
  intros Hu Hw.
  assert (HX : 0 <= Z.lxor w 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
  rewrite unsigned_lit by lia.
  change 18446744073709551584 with (Z.lxor 31 18446744073709551615).
  rewrite lor_lxor_ones64 by lia.
  assert (HL : 0 <= Z.land w 31 < 32).
  { split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite zb_lxor_ones by lia. unfold wz.
  rewrite <- (Z_to_bv_mod64 (u + _)), <- (Z_to_bv_mod64 (u - _)). f_equal.
  replace (u + (18446744073709551615 - Z.land w 31)) with ((u - (Z.land w 31 + 1)) + 1 * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rfg_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc W : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a3 a4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz W) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1585c) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

(* [comment removed for export] *)
Lemma rntf_fg : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv psegs m -> meta_slot st g ->
  mw_ok mr ->
  (m_sizeclass mr < 48 -> 0 <= usage st (m_sizeclass mr) < 2^64) ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rfg_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (fg_usage_st st g) g (m_sizeclass mr) (meta_word mr) fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15828) fc None m (seg_rom psegs)).
Proof using .
  intros until lo. intros mr MR MI MSL MW UR FR FRL ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (meta_word_range mr MW) as MWR.
  pose proof MW as (LI & FB & SCR & ML).
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold alloc_ceiling, RCTX in *.
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
    replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
      with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rmeta_chunk MR MSL CH. fold mr in CH.
  st1. st1. st1. rewrite MW2. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    clear CH.
    unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply rpres_except_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR].
  - unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
    specialize (UR ltac:(lia)).
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (342928, 342928 + 928)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    pose proof (rmrep_usage_read st m (m_sizeclass mr) (wa (RCTX + 464 + 8 * m_sizeclass mr)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    st1. rewrite ?(unsigned_lit (m_sizeclass mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    st1.
    replace (wa (342928 + 464 + 8 * m_sizeclass mr)) with (Z_to_bv 64 (342928 + m_sizeclass mr * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    (* [comment removed for export] *)
    st1. st1. st1.
    rewrite (usage_sub_word (usage st (m_sizeclass mr)) (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
    (* [comment removed for export] *)
    pose proof MR as (_ & (_ & _ & USG & _) & _).
    pose proof (u64arr_store_ok psegs _ _ (usages st) (m_sizeclass mr) (Z_to_bv 64 (342928 + m_sizeclass mr * 8 + 464)) USG
                  ltac:(rewrite usages_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_usage st mX (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    clear USG.
    rraw_store_finish (342928 + 464 + 8 * m_sizeclass mr) (le8 (wz (usage st (m_sizeclass mr) - (m_last_idx mr + 1)))) FR ST MU WM SOK.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (CH' : rw_cells psegs mX (conc st g) (meta_cells st mr)) end.
    { pose proof (rmrep_meta_chunk _ _ _ MR2 (meta_slot_set_usage _ _ _ _ MSL)) as X.
      rewrite conc_set_usage, rec_set_usage in X. fold mr in X.
      replace (meta_cells (set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st) mr) with (meta_cells st mr) in X; [exact X|].
      unfold meta_cells, pw. rewrite !oconc_set_usage. reflexivity. }
    clear CH. unfold meta_cells in CH'.
    st1. clear CH'.
    apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.


End CeilWrap.
End RF_ntf_D.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf_H.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_A.
Module RF_ntf_F.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf_H.F_ntf_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_free_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A RF_ntf_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma rntf_seq : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc ns lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> mw_ok mr ->
  sc = m_sizeclass mr -> m_mem mr = Some p -> 0 <= ns < 256 ->
  fm_facts st g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (Z_to_bv 64 ns) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x158bc) fc None m (seg_rom psegs)).
Proof using .
  intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof FR as [[[LJ _] _] _]. cbn in LJ.
  unfold alloc_ceiling, RCTX, rntf_frame in *.
  (* [comment removed for export] *)
  st1. rewrite ?(unsigned_lit sc) by lia. st1.
  (* [comment removed for export] *)
  pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _).
  pose proof (rw_cells_store_ok_at psegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (342928 + 912)) C6 eq_refl eq_refl
                ltac:(unfold wa; f_equal; lia)) as SOK.
  clear C6.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_seq st mX ns MR NS) as MR1; unfold RCTX in MR1 end.
  rraw_store_finish (342928 + 912) [b8 ns] FR ST MU WM SOK.
  set (st1 := upd_ctx (set_seq ns) st) in MR1.
  (* [comment removed for export] *)
  st1.
  assert (JOIN : forall m2 (a1' : word),
    rmrep (seq_st ns sc st) m2 -> mem_inv psegs m2 ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (342928, 342928 + 928)] m0 m2 -> wmono psegs m0 m2 ->
    stk psegs m2 lo (bv_unsigned sp + -96) -> rw_cells psegs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 ssp_guard_val; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
    evt psegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
                 (fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 342928) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x158d4) fc None m2 (seg_rom psegs))).
  { intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
    assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); exact MSL).
    rmeta_chunk MR2 MS2 CH.
    assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
    assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
    assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
    rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.
    (* [comment removed for export] *)
    st1. st1. st1. st1. clear CH.
    rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
    replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
    replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
    eapply evt_mono.
    { eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
        first [exact MR2 | exact MI2 | exact MS2 | exact S1 | exact FR2 | exact ST2 | unfold alloc_ceiling; heap_lia_pruned | heap_lia_pruned | idtac].
      unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; exact FMF. }
    intros ms' PO. unfold rntf_ret_post in PO |- *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR').
    do 14 eexists. split; [reflexivity|].
    split.
    { eapply rpres_except_trans.
      - apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [exact MU2|exact WM2|].
        cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; unfold RCTX; lia].
      - eapply rpres_except_mono; [exact PE|]. intros a Ha.
        eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try exact Ha; try heap_lia_pruned;
          unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
    split; [eapply wmono_trans; [exact WM2|exact WM']|]. split; [exact MI'|]. split; [exact ST'|exact MR']. }
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K).
    eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. exact MR1.
  - assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
    (* [comment removed for export] *)
    st1.
    pose proof MR1 as (_ & (_ & _ & _ & US & _) & _).
    pose proof (u8arr_store_ok psegs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 (342928 + (sc + -7) + 848)) US
                  ltac:(rewrite unmap_seqs_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    clear US.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish (342928 + 848 + (sc - 7)) [b8 ns] FR ST MU WM SOK.
    eapply JOIN; try eassumption.
    unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
    match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [exact MR2|] end.
    unfold upd_ctx. cbn. reflexivity.
Qed.

Lemma zeros32_cells : cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] = zeros 32.
Proof using . vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rntf_top : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> mw_ok mr ->
  sc = m_sizeclass mr -> m_mem mr = Some p -> m_maplen mr <> 0 ->
  0 <= c_seq (ctx st) < 256 ->
  fm_facts st g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
  munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (fm_st (record_seq sc (step_seq st)) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1585c) fc None m (seg_rom psegs)).
Proof using .
  intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  pose proof FR as [[[LJ _] _] _]. cbn in LJ.
  unfold alloc_ceiling, RCTX, rntf_frame in *.
  (* [comment removed for export] *)
  st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.
  (* [comment removed for export] *)
  pose proof (rmrep_seq_read st m (wa (RCTX + 912)) MR eq_refl) as RDS. unfold RCTX, wa in RDS.
  st1. clear RDS. st1.
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  - (* [comment removed for export] *)
    st1.
    replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
    2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
      first [exact MR | exact MI | exact MSL | exact MW | exact HSC | exact Hmem | exact FMF | exact S1 | exact ER | exact ES | exact EG | exact MU | exact WM | exact FR | exact ST | unfold alloc_ceiling; lia].
  - (* [comment removed for export] *)
    pose proof MR as (_ & (_ & _ & _ & US & _) & _).
    pose proof (rw_cells_of_u8arr psegs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. unfold RCTX in UB.
    replace (342928 + 848) with 343776 in UB by reflexivity.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(342928 + 848, 342928 + 880)]%Z mX) as MUz; pose proof (wmono_refl psegs mX) as WMz end.
    st1. st1. st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (UA' : u8arr psegs mX (RCTX + 848) (zeros 32))
        by (apply (u8arr_of_rw_cells psegs mX _ 32); unfold RCTX; eapply rw_cells_congr; [| | | exact UB]; [exact zeros32_cells| reflexivity| cbn; tclose]) end.
    clear UB.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
    { eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - left. unfold stz. rewrite unmap_seqs_empty. exact UA'.
      - right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
        unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }
    (* [comment removed for export] *)
    st1. st1.
    replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
    2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by reflexivity.
    replace (conc st p) with (conc stz p) by reflexivity.
    change (get_meta_rec st g) with (get_meta_rec stz g).
    eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
      first [exact MRz | assumption | exact MSL | exact MW | exact HSC | exact Hmem | exact S1 | exact ER | exact ES | exact EG | exact FR | exact ST | unfold alloc_ceiling; lia
            | apply fm_facts_ctx; [reflexivity| exact FMF] ].
Qed.


End CeilWrap.
End RF_ntf_F.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Module RF_ntf_G.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A RF_ntf_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x15888) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15600) fc None m' (seg_rom psegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells psegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

(* [comment removed for export] *)
Lemma rntf_nest_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g p base1 g1 : aptr) (ghp gh1 : ghdr) (ar1 : area) (b3 lo8 hi8 off16 lo : Z),
  let mr := get_meta_rec st g in
  let mr1 := get_meta_rec st g1 in
  let idx1 := Z.land b3 31 in
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> mw_ok mr -> m_maplen mr = 0 -> m_mem mr = Some p ->
  (s_groups st) !! p = Some ghp ->
  (forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
  bytes_at psegs m (conc st p - 4) [b8 0; b8 b3; b8 lo8; b8 hi8] ->
  0 <= b3 < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> off16 = lo8 + 256 * hi8 ->
  base1 = aadd p (- (UNIT * off16) - UNIT) ->
  (s_groups st) !! base1 = Some gh1 -> g_meta gh1 = Some g1 -> meta_slot st g1 -> m_mem mr1 = Some base1 ->
  0 <= m_avail mr1 < 2^32 -> 0 <= m_freed mr1 < 2^32 -> 0 <= m_last_idx mr1 < 32 -> 0 <= m_freeable mr1 < 2 ->
  0 <= m_sizeclass mr1 < 64 -> 0 <= m_maplen mr1 < 2^40 ->
  (s_areas st) !! (area_of g1) = Some ar1 -> a_check ar1 = c_secret (ctx st) -> 0 <= c_secret (ctx st) < 2^64 ->
  idx1 <= m_last_idx mr1 -> Z.testbit (m_avail mr1) idx1 = false -> Z.testbit (m_freed mr1) idx1 = false ->
  (m_sizeclass mr1 < 48 -> size_class (m_sizeclass mr1) * idx1 <= off16 < size_class (m_sizeclass mr1) * (idx1 + 1)) ->
  (48 <= m_sizeclass mr1 -> m_sizeclass mr1 = 63) ->
  (m_maplen mr1 <> 0 -> off16 <= m_maplen mr1 * 256 - 1) ->
  rw_cells psegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rnest_call_post sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (grp_del st g p) g p (conc st g1) idx1 fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1585c) fc None m (seg_rom psegs)).
Proof using .
  intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
         AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
  pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).
  (* [comment removed for export] *)
  destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
  assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
  { rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
  rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
  pose proof MS1 as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
  destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
  assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  assert (Hao : area_of g1 = a).
  { rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
  assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
  { rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
  assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
  unfold alloc_ceiling, RCTX, AREA_HDR, META_SIZE, NSLOTS in *.
  assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.
  (* [comment removed for export] *)
  change (frozen (conc st p mod 16 = 0)) in P16m.
  change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
  clear HGm AAL RBAL RgBAL SpA BbA.
  destruct GB as (GB0 & GB1 & GB2 & _). destruct G1B as (G1B0 & G1B1 & G1B2 & _).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  (* [comment removed for export] *)
  st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
    pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
    pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
    pose proof (rmrep_ctx_secret_read_area st mX (area_of g1) ar1 MR Har1) as RC;
    pose proof (bytes_at_read psegs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
    pose proof (bytes_at_read psegs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
    pose proof (bytes_at_read psegs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
  end.
  rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
  unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
  (* [comment removed for export] *)
  assert (WS : wz (bv_unsigned malloc_secret_val) = malloc_secret_val) by (unfold wz; apply Z_to_bv_bv_unsigned).
  rewrite <- WS in RA, RC.
  pose proof (bv_unsigned_in_range _ (@malloc_secret_val AGRD)) as SRV. change (bv_modulus 64) with (2^64) in SRV.
  rewrite Hao, (conc_region' st a rg Hrg) in RA. unfold RCTX in RC.
  change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
  change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
  change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
  replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
  replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
  replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
  rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
            (m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
            (m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) (bv_unsigned malloc_secret_val)).
    all: lazymatch goal with
         | |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
         | |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
         | |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
         | |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
         | |- ov_read_bytes _ _ (wa 342928) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
         | |- rw_cells _ _ (conc _ _) _ => exact MM
         | |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
         | |- _ => idtac
         end.
    all: first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
               | heap_lia_pruned | unfold wz; rewrite ?unsigned_lit by lia; heap_lia_pruned | unfold UNIT in *; heap_lia_pruned
               | lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }   (* [comment removed for export] *)
  intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
  replace (ret_pc (Z_to_bv 64 0x15874)) with (Z_to_bv 64 0x15874) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* [comment removed for export] *)
  st1.
  unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
  st1.
  (* [comment removed for export] *)
  clear CH MM RG RA RC R4 R2.
  pose proof MR as (_ & _ & _ & _ & GR0 & _). destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rw_cells_store_ok_at psegs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
  clear RWp.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) MR Hp UNK (length_le8 _)) as MR2
  end.
  rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
  apply (rmrep_grp_del_eq st _ g p) in MR2.
  (* [comment removed for export] *)
  st1. st1.
  apply evt_done. unfold rnest_call_post. do 14 eexists.
  split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
           cbv delta [mkR]. unfold RCTX. reflexivity. }
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + eapply rfree_fp_group; [exact Hp | lia]. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rntf_nest_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) (st0 st : mstate) (g : aptr) (lo : Z),
  rmrep st m -> mem_inv psegs m -> meta_slot st g -> fm_facts st g ->
  conc st g = conc st0 g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  rw_cells psegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk psegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt psegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a0 a1)
      (MS (mkR (Z_to_bv 64 0x15888) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st0 g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15888) fc None m (seg_rom psegs)).
Proof using .
  intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold alloc_ceiling in *.
  st1. st1. st1.
  rewrite <- Hcg.
  eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
    first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | unfold alloc_ceiling; lia].
Qed.


End CeilWrap.
End RF_ntf_G.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_malloc_enframe MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_C.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf_H.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf_H.F_ntf_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_ntf_H F_ntf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_C.
Import RF_ntf_D.
Import RF_ntf_E.
Import RF_ntf_F.
Import RF_ntf_G.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RF_ntf_H.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
    (st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp) /\ rmrep st' m'
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
    /\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_entry st lo (sp : word) m m1 :
  munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono psegs m m1 -> lo <= bv_unsigned sp - 96 ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof.
  intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.

Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
  oracle_ok o m st -> rmrep st mw -> alloc_ceiling <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof using .
  intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
  rewrite (OK rid r q h Hr Hk Hq M8 Hc).
  pose proof MR as (WF & _). (nelimp WF 5%nat; intros Hres WR DJ WA WG).
  (nelim (WR rid r Hr) 5%nat; intros RB0 RBAL RL0 RBC RF). (nelimp (rreserved_disjoint _ _ RF) 4%nat; intros D1 D2 D3 D4).
  unfold alloc_ceiling in *.
  symmetry. apply (PE (r_base r + q)); [lia|].
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - (nelim A 5%nat; intros rid' r' Hr' Hk' Hin).
    destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
    pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
  - (nelim A 4%nat; intros b gh Hb Hin).
    (nelim (rgroup_conc st b gh WF Hb) 9%nat; intros rb Hrb Cb Krb Sb0 Sb1 SbA RbB0 _).
    (nelim (WR (fst b) rb Hrb) 3%nat; intros _ RbAL _).
    assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
    Z.div_mod_to_equations. lia.
  - (nelim A 7%nat; intros rid' r' v Hr' Hk' Hin HC).
    destruct (N.eq_dec rid' rid) as [->|NE].
    + rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof using .
  intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

Lemma rfree_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof using . intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

(* [comment removed for export] *)
Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> alloc_ceiling <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof using .
  intros MR LO LS H. pose proof MR as (WF & _). (nelimp WF 5%nat; intros _ WR _ _ _).
  unfold alloc_ceiling in *.
  destruct H as [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - (nelim A 5%nat; intros rid r Hr _ Hin). (nelim (WR rid r Hr) 5%nat; intros _ _ _ RC _). unfold alloc_ceiling in RC. lia.
  - (nelim A 4%nat; intros b gh Hb Hin). (nelim (rgroup_conc st b gh WF Hb) 9%nat; intros rb Hrb Cb _ _ Sb1 _ _ RC). unfold alloc_ceiling in RC. lia.
  - (nelim A 7%nat; intros rid r v Hr _ Hin _). (nelim (WR rid r Hr) 5%nat; intros _ _ _ RC _). unfold alloc_ceiling in RC. lia.
Qed.

(* [comment removed for export] *)
Lemma rknown_byte st m (q : aptr) r v :
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v ->
  bytes_at psegs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof using .
  intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
  (nelimp MR 6%nat; intros _ _ _ _ _ SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

(* [comment removed for export] *)
Lemma rimplT_queue {R} o h g st0 (k : mstate -> Malloc.M R) bail s Q ms :
  (m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
  rimplT o (queue h g st0 k bail) s Q ms.
Proof using .
  intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
  assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
  assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
  specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.

Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof using . reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
  rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
  (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
  (exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
  oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
  rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof using LO.
  intros RP PE FP KI ZI FR RES OOK MRX ER ES.
  (nelim RP 20%nat; intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' -> PE' WM' MI' ST' MR').
  unfold rntf_q. nexists 16%nat. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
  split. { eapply rpres_except_trans; [exact PE|]. eapply rpres_except_mono; [exact PE'|]. exact FP. }
  split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
  eapply oracle_ok_frame; [| exact ER | exact ES]. eapply roracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> Malloc.M R) (bail : Malloc.M R)
    (s : PState) (Q : R -> PState -> machine_state -> Prop)
    (ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
  KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
  rmrep st m -> mem_inv psegs m -> oracle_ok o m st ->
  stk psegs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
  (forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
  rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15600) fc None m (seg_rom psegs)).
Proof using LO.
  induction fuel as [|f IH]; intros until Zs; intros KI LP ZI MR MI OOK ST DEPTH KH.
  { cbn [nontrivial_free]. apply rimplT_undef. }
  rewrite ntf_unfold. cbv zeta.
  pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
  pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
  pose proof (go_slot _ _ _ GO) as MSL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
  set (ms0 := MS _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (ENTRY : entry_hyps st g i ->
    evt psegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
  { intros EH. subst ms0. eapply rntf_entry; eauto. }
  (* [comment removed for export] *)
  assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
                       (G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
                       (G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
                             m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
             entry_hyps st g i).
  { intros. constructor; auto.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - pose proof (go_sc _ _ _ GO). lia.
    - intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
    - intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
    - split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
  destruct (ntf_cond st g i) eqn:HC.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
      rfg_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
              (m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
      (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
      wmono psegs m m2 -> oracle_ok o m2 stX ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
    { intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
      pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
      unfold rfg_post in FGP. (nelim FGP 10%nat; intros y3 y4 m3 -> PE3 WM3 MI3 ST3 FR3 MR3).
      set (stU := fg_usage_st stX g) in *.
      assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
      assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
      rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
      rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).
      (* [comment removed for export] *)
      assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
      { (nelim (data_of_fields _ _ g DATX) 5%nat; intros _ EA EF EL _).
        unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
        unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
        pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
        apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
          try heap_lia_pruned; try exact HALL.
        - exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
        - destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tclose.
        - destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tclose. }
      assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
      assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; exact LPX).
      assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact GNX)).
      rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
          [ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
          | pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact Hj) ltac:(rewrite RU; apply ALLFREE; [exact Hj| exact NE])) as FC;
            rewrite RU in FC; exact FC ])).
      fold stG in GD. (nelim GD 3%nat; intros KIG NGM NSL).
      assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; exact MR3).
      assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; exact FRX).
      assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).
      (* [comment removed for export] *)
      pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
      pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
      replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
      change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
      destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
      - (* [comment removed for export] *)
        assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
        rewrite free_meta_eq.
        eapply rimplT_evt.
        { eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
            first [exact MRG | exact MI3 | exact MSG | exact MWU | exact MEMU | exact MLNZ | exact FR3 | exact ST3 | exact LO | exact LOLE | reflexivity
                  | apply munch_refl | apply wmono_refl | idtac].
          - pose proof (ki_cx _ _ _ KIG) as (SQ & _). exact SQ.
          - intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [exact GNU| exact Hhd]. }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try exact RP.
        + destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
            (eapply rpres_except_mono; [exact PE3| exact FPX]).
        + intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | exact Ha].
          unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
        + eexists. apply KINV_fm; [apply KINV_seq; exact KIG| | | |].
          * unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [exact MSG|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros [b Hb]. apply NGM. exists b. unfold hosts in *.
            replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [exact Hb|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [exact GNU|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
        + apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + (* [comment removed for export] *)
          pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
          (nelimp (seq_shape stG (m_sizeclass (get_meta_rec stG g))) 8%nat; intros SR1 SR2 SR3 SR4 SR5 SR6 SR7 SR8).
          set (stS := record_seq _ (step_seq stG)) in *.
          assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; exact GNU).
          unfold fm_st. apply frame_queue.
          * apply frame_put_meta; [apply frame_seq; exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
          * apply links_put_meta0; [exact (ki_links _ _ _ KIS)| exact GNS].
          * cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
            intros hd Hhd. (nelim (kinv_free_head stS LB _ hd KIS Hhd) 3%nat; intros _ NX' _).
            rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| exact NX'].
          * right; exact (hosts_is_gm _ _ _ HOSTS).
        + (* [comment removed for export] *)
          (nelimp (seq_shape stG (m_sizeclass (get_meta_rec stG g))) 4%nat; intros SR1 SR2 SR3 _).
          (nelimp (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) 4%nat; intros FS1 FS2 FS3 _).
          (nelim (go_region _ _ _ GOX) 7%nat; intros r Hr Kr _ _ _ TOP). rewrite <- RU in TOP.
          change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
          pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
          unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [exact SND| split]]]].
          * unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
          * exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
          * intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
            apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
            apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; exact MLNZ | exact ALLFREE | exact Hb' | exact E].
        + eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [exact OOK2 | exact MRW | exact LO | exact PE3].
        + exact MRG.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
        + (nelimp (seq_shape stG (m_sizeclass (get_meta_rec stG g))) 3%nat; intros _ SR2 _).
          (nelimp (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) 3%nat; intros _ FS2 _). rewrite FS2, SR2. reflexivity.
      - (* [comment removed for export] *)
        assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).
        (* [comment removed for export] *)
        pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
        (nelim (NEST MLZ) 18%nat; intros g1 i1 b1 SL1 HB1 FB1 PSS I1 NF1 LT1 v3 lo8 hi8 K3 V31 K2 K1 OFF).
        clear NEST.
        pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
        (nelim (go_region _ _ _ GOX) 7%nat; intros r Hr Kr SP0 SP16 SPAN _).
        (nelim (go_region _ _ _ GO1) 7%nat; intros r1 Hr1 _ SB0 SB16 SPAN1 _).
        rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
        assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
        assert (B1LT : snd b1 + 16 <= snd p).
        { rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
          pose proof (go_stride _ _ _ GO1) as [S16 _].
          assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
        assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
        assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; exact HB1).
        assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [exact NEb1| exact HB1U]).
        (* [comment removed for export] *)
        pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
        assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
        { split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
          rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
          unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
          rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
          assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
          unfold UNIT, IB in *. lia. }
        destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].
        (* [comment removed for export] *)
        unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
        apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
        assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
        { intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
          unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
        rewrite !ESH.
        rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; exact K4).
        rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; exact K3).
        rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; exact K2).
        rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; exact K1).
        cbn [Z.eqb negb].
        set (off16 := lo8 + 256 * hi8).
        assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
        { unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
        rewrite EB. unfold get_group.
        replace (s_groups stG !! b1) with (s_groups stX !! b1).
        2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
        destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
        apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
        apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
        (* [comment removed for export] *)
        assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
        change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
        rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
        destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
        apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
        apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
        (* [comment removed for export] *)
        assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
        assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
        assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
                   bytes_at psegs m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
        { intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; exact Hr) Kr ltac:(cbn; lia)
                   ltac:(cbn; unfold get_shadow; rewrite ESU; exact Hc)) as [B V].
          cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; exact Hr). cbn [snd] in B.
          rewrite (conc_region' stU p r) by (rewrite ERU; exact Hr). split; [| exact V].
          replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. exact B. }
        destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
        destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
        assert (HDR : bytes_at psegs m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
        { change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
          apply bytes_at_app. split; [exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; exact Y3|].
          apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; exact Y2|].
          cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. exact Y1. }
        (* [comment removed for export] *)
        destruct HOSTSX as [aig Hghp].
        eapply rimplT_evt.
        { eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
          all: first [exact MR3 | exact MI3 | exact MWU | exact MLZ | exact MEMU | exact HDR | exact FR3 | exact ST3 | exact LO | exact LOLE
                     | exact R3 | exact R2 | exact R1 | exact AR1 | exact G15 | apply rntf_frame_size | idtac].
          all: try reflexivity.
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
          all: rewrite ?EU1.
          all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
               try exact G12; try exact G13; try exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
          all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); heap_lia_pruned).
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
          all: try (unfold stU; rewrite fg_usage_groups; first [exact Hghp | exact Hgh1]).
          all: try (symmetry; exact EB).
          all: match goal with
               | |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
               | |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
                                   apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
               | |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
                                   fold off16 in G17; unfold UNIT in G17;
                                   replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
                                   rewrite Z.div_mul in G17 by lia; lia
               | |- ?G => idtac "NCGOAL" G; fail
               end. }
        intros ms3 NC. unfold rnest_call_post in NC.
        (nelim NC 21%nat; intros z0 z1 z2 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m4 -> PE4 WM4 MI4 ST4 FR4 MR4).
        fold stG in MR4.
        (* [comment removed for export] *)
        pose proof (bv_unsigned_in_range _ sp) as SPR'.
        assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (unfold alloc_ceiling in LO; rewrite unsigned_lit; lia).
        rewrite V31. replace (conc stU g1) with (conc stG g1) by reflexivity.
        eapply (IH R _ bail s Q (Z_to_bv 64 0x15888) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
        + exact KIG.
        + constructor.
          * exact HB1G.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact I1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact NF1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
            apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
            pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
            pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
        + unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + exact MR4.
        + exact MI4.
        + apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [exact OOK2 | exact MRW | exact LO |].
          eapply rpres_except_trans; [exact PE3|]. eapply rpres_except_mono; [exact PE4|].
          intros a Ha. eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha].
        + rewrite SPU. exact ST4.
        + rewrite SPU. lia.
        + (* [comment removed for export] *)
          intros st3 mi ms5 NQ. rewrite free_meta_eq.
          unfold rntf_q in NQ. rewrite SPU in NQ.
          (nelim NQ 26%nat; intros u0 u1 u2 ra0' ra1' u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 m5 -> MI5 ST5 MR5 PE5 [c3 KI3] ZI3 FR35 RES5 OOK5).
          replace (ret_pc (Z_to_bv 64 0x15888)) with (Z_to_bv 64 0x15888) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
          assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
          { apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
          assert (NGM3 : ~ is_gm st3 g).
          { intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). exact Hb. }
          eapply rimplT_evt.
          { eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
              first [exact MR5 | exact MI5 | exact LO | exact LOLE | reflexivity | idtac].
            - unfold meta_slot. rewrite (nf_areas _ _ FR35). exact MSG.
            - intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; exact GNU| exact Hhd].
            - unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
            - eapply rpres_except_rw_cells; [exact PE5 | exact FR4 |].
              intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
            - exact ST5. }
          intros ms6 RP. apply KH.
          pose proof (frame_trans _ _ _ FRG FR35) as FR03.
          (nelimp (fm_shape st3 g) 6%nat; intros FS1 FS2 FS3 FS4 FS5 FS6).
          eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try exact RP.
          * destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE3| exact FPX]|]);
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha]]|]);
              (eapply rpres_except_mono; [exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [exact FRG| lia| exact Ha]]).
          * intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [exact FR03| lia| exact Ha].
          * exists c3. apply KINV_fm; [exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); exact MSG| exact NGM3| rewrite RG3; exact GNU|].
            intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). exact Hs.
          * apply ZINV_fm. exact ZI3.
          * unfold fm_st. apply frame_queue.
            -- apply frame_put_meta; [exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
            -- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; exact GNU].
            -- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
               intros hd Hhd. (nelim (kinv_free_head st3 LB _ hd KI3 Hhd) 3%nat; intros _ NX' _).
               rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; exact GNU| exact NX'].
            -- right; exact (hosts_is_gm _ _ _ HOSTS).
          * destruct mi as [[bb len]|]; [| exact RES5].
            destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
            unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
            split; [exact A1|]. split; [exact LEN|]. split; [exact SND|]. split; [exists rr; rewrite FS1; auto|].
            intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
          * exact OOK5.
          * exact MR5.
          * exact FS1.
          * exact FS2. }
    (* [comment removed for export] *)
    assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
      s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
      (m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
      rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono psegs m m4 -> mem_inv psegs m4 ->
      stk psegs m4 lo (bv_unsigned sp + -96) -> rw_cells psegs m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
      ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
               F (Z_to_bv 64 0x15828) fc None m4 (seg_rom psegs) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
    { intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
      assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
      eapply rimplT_evt.
      { eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
          first [exact MR4 | exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | exact USX | exact FR4 | apply rntf_frame_size | exact ST4 | exact LO | exact LOLE]. }
      intros ms5 FGP.
      eapply (FG2 stX m4 junk); [exact KIX | exact ZIX | exact LPX | exact FRX | exact GNX | right; exact PE4 | exact FGP | | exact WM4 | | exact DATX | exists m4; exact MR4].
      - intros a Ha. eapply (rfree_fp_same st stX); eauto.
      - apply (oracle_ok_frame o m4 st stX); [| exact ERX | exact ESX].
        eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [exact OOK | exact MR | exact LO | exact PE4]. }
    destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
    + (* [comment removed for export] *)
      apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
      set (sc := m_sizeclass (get_meta_rec st g)) in *.
      set (an := optr_eqb (active st sc) (Some g)).
      set (stm := deq_mid (LActive sc) g st).
      set (st1 := dequeue (LActive sc) g st).
      assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
      pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
      pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
      assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
      assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; exact ZI).
      assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [exact SBL1| exact LP]).
      assert (FR1' : ntf_frame st st1).
      { unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
      (nelim (kinv_next _ _ _ _ _ KI NX) 8%nat; intros MSnx Pnx Nnx pv PV MSpv Npv NEpv).
      pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
      (nelim DS 4%nat; intros DSdata GN1 GP1 _).
      (* [comment removed for export] *)
      assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono psegs m m2 ->
        rat9c_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
                   (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (match an, active st1 sc with
                 | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
                 | _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
                 end) s Q ms2).
      { intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
        unfold rat9c_post in AP. (nelim AP 10%nat; intros y3 y4 m3 -> PE3 WM3 MI3 ST3 FR3 MR3).
        assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
        { destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE3]| eapply rpres_except_trans; [exact PE0| exact PE3]]. }
        (* [comment removed for export] *)
        assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
        { (nelimp (rmeta_slot_bounds st m g MR MSL) 3%nat; intros B0 B1 _). unfold alloc_ceiling in B1.
          rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
          - destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
            pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. (nelimp (rmeta_slot_bounds st m h MR MSh) 3%nat; intros C0 C1 _). unfold alloc_ceiling in C1.
            unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). exact E.
          - unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
        assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
          evt psegs (rat00_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x157c4) fc None m3 (seg_rom psegs))).
        { intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
          eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
            first [exact MR3 | exact MI3 | exact HA3 | exact FR3 | apply rntf_frame_size | exact ST3 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBLm| exact MSL].
          - pose proof (go_sc _ _ _ GO). subst sc. lia.
          - rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
            (nelim (kinv_active _ _ _ _ _ KI1 A1) 5%nat; intros _ MSa Na GMa _).
            destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
            destruct Hba as [ai Hgh]. (nelimp (ki_grps _ _ _ KI1 ba _ Hgh) 3%nat; intros g' Eg' AI). cbn in Eg', AI. inversion Eg'; subst g'.
            split; [exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
            exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
        assert (AVK : forall a, an = true -> active st1 sc = Some a ->
                 rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x157c4) fc None m3 (seg_rom psegs))).
        { intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
          change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
          set (stA := act_st st1 a (act_of st1 a)).
          (nelim (kinv_active _ _ _ _ _ KI1 A1) 5%nat; intros _ MSa Na GMa _).
          assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
          eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; exact AV0|].
          intros ms4 AQ. unfold rat00_post in AQ. (nelim AQ 16%nat; intros z0 w1 w2 w3 w4 w5 w6 w7 m4 -> PE4 WM4 MI4 ST4 FR4 MR4).
          assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX stA m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4.
          - unfold stA. apply KINV_act; [exact KI1| exact GMa| exact AV0| apply act_of_nonneg].
          - unfold stA. apply ZINV_act. exact ZI1.
          - unfold stA, act_st. apply LPRE_upd_other; [exact NEa| exact LP1].
          - unfold stA. apply frame_act; [exact FR1'| eapply (LG_frame st st1 a FR1'); left; exact Na].
          - unfold stA. rewrite act_st_rec_other by congruence. exact GN1.
          - unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
          - unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
          - unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
          - unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
          - unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
            change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
            apply (ki_usage _ _ _ KI1). (nelim (data_of_fields _ _ g (DSdata g)) 7%nat; intros _ _ _ _ _ -> _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        assert (NOACT : (an = false \/ active st1 sc = None) ->
                 rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x157c4) fc None m3 (seg_rom psegs))).
        { intros NA.
          eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
          intros ms4 AQ. unfold rat00_post in AQ. (nelim AQ 16%nat; intros z0 w1 w2 w3 w4 w5 w6 w7 m4 -> PE4 WM4 MI4 ST4 FR4 MR4).
          assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
          rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX st1 m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4; try exact KI1; try exact ZI1; try exact LP1; try exact FR1'; try exact GN1.
          - apply DSdata.
          - apply (sbl_regions _ _ SBL1).
          - apply (sbl_shadow _ _ SBL1).
          - apply (sbl_groups _ _ SBL1).
          - intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). (nelim (data_of_fields _ _ g (DSdata g)) 7%nat; intros _ _ _ _ _ -> _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| exact SC48b]|].
      intros ms1 nelH_; (nelim nelH_ 9%nat; intros m1 junk CASES MU WM MI1 ST1 FR1 MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; (nelim D 3%nat; intros D1 D2 D3); congruence).
      * (* [comment removed for export] *)
        (nelim D 16%nat; intros _ NXg _ x0 x1 x2 y3 y4 y5 y6 y7 x3 x4 x5 x6 ->).
        assert (Enx : nx = g) by congruence.
        eapply rimplT_evt.
        { eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - rewrite NX, Enx. reflexivity. }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
      * (* [comment removed for export] *)
        (nelim D 17%nat; intros _ _ nx' NX' NE x0 x1 x2 y4 y5 y6 y7 x3 x4 x5 x6 ->).
        assert (Enx : nx' = nx) by congruence. subst nx'.
        eapply rimplT_evt.
        { eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact NX | exact PV | exact NE | exact MSnx | exact MSpv | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | reflexivity | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - apply NEpv. exact NE.
          - destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
            exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
    + (* [comment removed for export] *)
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 nelH_; (nelim nelH_ 9%nat; intros m1 junk CASES MU WM MI1 ST1 FR1 MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; (nelim D 3%nat; intros D1 D2 D3); try (nelim D3 3%nat; intros nx0 D3 _); congruence).
      (nelim D 17%nat; intros _ _ x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 ->).
      eapply (FGX st m1 junk); [exact KI | exact ZI | exact LP | apply frame_refl | exact NX | reflexivity | reflexivity | reflexivity | reflexivity
                               | | eapply rpres_except_entry; eauto | exact WM | exact MI1 | exact ST1 | exact FR1 | exact MR1 | reflexivity].
      intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
  - destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
    + (* [comment removed for export] *)
      apply Z.eqb_eq in HM.
      apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.
      (* [comment removed for export] *)
      assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono psegs m m1 ->
        stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
        (active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
        forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
                      x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (k (aor_st stq g i) None) s Q ms2).
      { intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
        assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
        assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); exact ZI).
        assert (KIq : KINV stq LB c).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [exact KI|].
          apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
        assert (FRq : ntf_frame st stq).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
          apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
          cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
        unfold rqpath_post in QP. cbv beta in QP.
        (nelim QP 12%nat; intros qa0 qa2 qa3 qa5 m2 -> PE2 WM2 MI2 ST2 FR2 MR2).
        pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
        rewrite <- (conc_sbl st stq g SBL).
        eapply rimplT_evt.
        { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
            first [exact MR2 | exact MI2 | reflexivity | exact FR2 | exact ST2 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBL| exact MSL].
          - pose proof (go_li _ _ _ GO). lia.
          - (nelim (data_of_fields st stq g (sbl_data _ _ SBL g)) 4%nat; intros _ _ -> _). exact (go_freed _ _ _ GO). }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try exact RP.
        * eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [exact FRq| lia| exact Ha].
        * exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
        * apply ZINV_aor. exact ZIq.
        * apply frame_aor; [exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
        * exact eq_refl.
        * apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
          eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO|].
          eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * exact MR2.
        * reflexivity.
        * reflexivity. }
      destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
      * (* [comment removed for export] *)
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
        { destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia | exact HAct]|].
        intros ms1 nelH_; (nelim nelH_ 9%nat; intros m1 junk CASES MU WM MI1 ST1 FR1 MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; (nelim D 3%nat; intros D1 D2 _); congruence).
        (nelim D 15%nat; intros _ _ x0 x1 x2 y3 y5 y6 y7 s2x x3 x4 x5 x6 ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - right. exists g. split; [exact HAct| exact MSL].
          - intros NE. exfalso. exact (NE HAct).
          - intros hd Hhd NE. exfalso. apply NE. congruence. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| exact QP].
      * (* [comment removed for export] *)
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
        { intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
        apply rimplT_queue. intros GN GPV.
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia]|].
        intros ms1 nelH_; (nelim nelH_ 9%nat; intros m1 junk CASES MU WM MI1 ST1 FR1 MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; (nelim D 3%nat; intros D1 D2 D3); try destruct D3 as [D3 _]; congruence).
        (nelim D 15%nat; intros _ _ x0 x1 x2 y3 y5 y6 y7 s2x x3 x4 x5 x6 ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
            exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
          - intros _. split; assumption.
          - intros hd Hhd NE. (nelim (kinv_active _ _ _ _ _ KI Hhd) 9%nat; intros _ Shd Nhd _ _ pv Ppv Spv Npv).
            split; [exact Shd|]. exists pv. split; [exact Ppv|]. split; [| exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros _; split; assumption| exact QP].
    + (* [comment removed for export] *)
      apply Z.eqb_neq in HM.
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 nelH_; (nelim nelH_ 9%nat; intros m1 junk CASES MU WM MI1 ST1 FR1 MR1).
      destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; (nelim D 3%nat; intros D1 D2 _); congruence).
      (nelim D 17%nat; intros _ _ x0 x1 x2 y0 y2 y3 y5 y6 y7 s2x x3 x4 x5 x6 ->).
      eapply rimplT_evt.
      { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
          first [exact MR1 | exact MI1 | exact MSL | reflexivity | exact FR1 | exact ST1 | exact LO | exact LOLE | idtac].
        - pose proof (go_li _ _ _ GO). lia.
        - exact (go_freed _ _ _ GO). }
      intros ms2 RP. apply KH.
      eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try exact RP.
      * eapply rpres_except_entry; eauto.
      * auto.
      * exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
      * apply ZINV_aor. exact ZI.
      * apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
      * exact eq_refl.
      * eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO| eapply rpres_except_entry; eauto].
      * exact MR1.
      * reflexivity.
      * reflexivity.
Qed.
End NTF.


End CeilWrap.
