(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocU Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zpp.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu Zpo Zpr Zpn Zpq Zpz Zpy.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpg Zph SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Zp8.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Zwn Zpw Z6n Z44.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Z5l Z4d Z4j Z51 Z53 Z4p.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition lftoi_rest (d : list Z) (v : @vec bptr) (psb ptp pim pix poc pia : bptr) : M PState Z :=
  mbind mcho (fun ok =>
  mbind (if ok =? 0 then mret tt else atp_walk lops (ptr_segs (atp_ptr d))) (fun _ =>
  mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
  mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ =>
  mbind (vfree lops v) (fun _ => mret 0))))))))).

Lemma atp_els_second : forall D d, exists e0 P1 rest,
  atp_els D d = e0 :: (P1, zlength (atp_ptr d)) :: rest
  /\ (atp_ptr d = [] /\ P1 = 0 \/ exists off, atp_ptr d = firstn (length (atp_ptr d)) (skipn off d) /\ P1 = D + Z.of_nat off /\ (off + length (atp_ptr d) <= length d)%nat).
Proof.
  intros D d. unfold atp_els, atp_P, atp_ptr.
  pose proof (poffs_length d) as PL. pose proof (poffs_parts d) as PP. pose proof (poffs_bound d) as PB.
  assert (D0 : 0 <= zlength d) by (unfold zlength; lia).
  destruct (poffs d) as [|[o0 n0] [|[o1 n1] tl]] eqn:EP.
  - cbn in PP. rewrite <- PP. cbn. do 3 eexists. split; [reflexivity|]. left. split; reflexivity.
  - cbn in PP. rewrite <- PP. cbn -[skipn firstn Z.add Z.of_nat]. do 3 eexists. split; [reflexivity|]. left. split; reflexivity.
  - rewrite <- PP. cbn [map nth fst snd length Nat.max Nat.sub app].
    pose proof (PB (o1, n1) ltac:(right; left; reflexivity)) as B1. cbn in B1.
    assert (LN1 : length (firstn n1 (skipn o1 d)) = n1) by (rewrite firstn_length, length_skipn; lia).
    assert (ZL : zlength (firstn n1 (skipn o1 d)) = Z.of_nat n1) by (unfold zlength; rewrite LN1; reflexivity).
    rewrite ZL, LN1. do 3 eexists. split; [reflexivity|]. right. exists o1. split; [reflexivity|]. split; [reflexivity| lia].
Qed.

Lemma rw_cells_take2 : forall m A c1 c2 rest, rw_cells usegs m A (c1 :: c2 :: rest) -> rw_cells usegs m A [c1; c2].
Proof. intros m A c1 c2 rest H. exact (proj1 (rw_cells_split_at1 m A _ 2%nat H)). Qed.

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis ROOT : forall E, aenv_ok E -> atp_elem_stmt E TAPE_MAX_DEPTH.

  Lemma lftoi_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (m0 : mem) (s00 : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word)
      (bv : bptr) (A cap : Z) (jr : list byte) (psb ptp pim pix poc pia : bptr) (s1' : PState) (ms1 : machine_state),
    RHEAP s00 LB m0 -> lx_statics m0 -> stderr_wfile m0 -> ssp_cells m0 canary ->
    bv_unsigned sp <= B -> B < 2^63 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    tp = wz RATP -> bv_unsigned sp mod 16 = 0 -> cap < 2^26 ->
    gate_post (bv_unsigned sp - 272) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F s00 LB lo B D d m0 bv A cap jr psb ptp pim pix poc pia s1' ms1 ->
    implM usegs (lftoi_rest d (cap, Z.of_nat (atp_P d), Some bv) psb ptp pim pix poc pia) s1'
          (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0) ms1.
  Proof.
    intros until ms1. intros HEAP00 LXS0 SEW0 SSP0 SPB B63 CEIL GLO LO TP AL16 CAPB GP.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *. unfold Zf2.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
    remember (bv_unsigned sp) as usp eqn:Eusp.
    remember (usp - 272) as sp0 eqn:Esp0.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    subst tp.
    unfold gate_post in GP.
    destruct GP as (x1 & t0 & t1 & t2 & xs0 & xs1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & xs2 & xs3 & t3 & t4 & t5 & t6 & F1 & fc1 & m1 & errv1
                    & IMPL & IDX & OC & IA & TAPE & SBUF & r & jg & jl & jo & jn & j105 & j121 & j161 & jr20 & j225
                    & vptr & nsi & nxt & capv & md & bufv & lenv & docv & b48 & b49 & p12 & p28 & p50
                    & -> & FRM1 & MI1 & ST1 & ERR1 & AUX1 & FA1 & SO1 & HEAP1 & PRES1 & SJS1 & PL1 & VR1 & RES & OKR & BRTP & BRSB
                    & PA0 & PIMPL & PA16 & DOCC & P48 & THIS & EVP & GSO & LEAF & OUT & NODEC & XFD & SAVE).
    assert (LO0 : 0 <= lo) by (destruct ST1 as [? _]; assumption).
    assert (ELX : LX_ERRNO = 606604) by reflexivity. rewrite ELX in ERR1.
    pose proof PL1 as (PB1 & PRNG & D0 & DN & DLEN & PIN).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. lia. }
    remember (doc_cap d) as capd eqn:Ecapd. assert (CAPD : 32 <= capd) by (subst capd; unfold doc_cap; lia).
    pose proof BRTP as (TP0 & TP16 & _ & TPC & TPS). pose proof BRSB as (SB0 & _ & _ & SBC & SBS). unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in TPC, SBC.
    pose proof (roundup64_ge (capd + 3)) as RC2. pose proof (roundup64_ge (5 * (capd / 3) + 64)) as RC3. assert (D3 : 0 <= capd / 3) by (apply Z.div_pos; lia).
    pose proof (LH_block_range _ _ _ _ HEAP1 ltac:(do 3 right; left; reflexivity)) as (IM0 & _ & _ & IMC & IMS).
    pose proof (LH_block_range _ _ _ _ HEAP1 ltac:(do 6 right; left; reflexivity)) as (A0 & A16 & _ & AC & AS).
    cbn [blk_addr blk_size fst snd] in IM0, IMC, IMS, A0, A16, AC, AS. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in IMC, AC.
    destruct VR1 as (ELS & SZ & SV & BLK).
    pose proof (atp_els_length D d) as ELEN.
    unfold lftoi_rest.

    assert (K2C8 : forall (m2 : mem) (st2 : PState) (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 errv2 : word) (jg2 jl2 jo2 jn2 : list byte),
      RHEAP st2 ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 capd + 9)) :: (pim, IMPL, 96)
                 :: (ptp, TAPE, 8 * roundup64 (capd + 3)) :: (psb, SBUF, roundup64 (5 * (capd / 3) + 64)) :: (bv, A, 16 * cap) :: LB) m2 ->
      rauxv_ok m2 B -> mem_inv usegs m2 -> stk usegs m2 lo sp0 -> rw_cells usegs m2 606604 [C4 errv2] -> ps_fa st2 = ps_fa s00 -> ps_so st2 = ps_so s00 ->
      lx_pres LB (sp0 + 272) [LXW_SJ] m0 m2 -> sj_statics m2 true -> payload_ok m2 LB D d ->
      rw_cells usegs m2 (sp0 + 184) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * Z.of_nat (atp_P d))); C8 (Z_to_bv 64 (A + 16 * cap))] ->
      vblk m2 A cap (Z.of_nat (atp_P d)) (Some bv) (atp_els D d) jr ->
      rw_cells usegs m2 (sp0 + 104) [C1 (Z_to_bv 8 0); CB 7 j105] -> rw_cells usegs m2 (sp0 + 112) [C8 (Z_to_bv 64 IMPL)] ->
      rw_cells usegs m2 (sp0 + 120) [C1 (Z_to_bv 8 0); CB 3 j121; C4 (Z_to_bv 64 12)] ->
      rw_cells usegs m2 (sp0 + 128) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 (Z_to_bv 64 capd)] ->
      rw_cells usegs m2 (sp0 + 152) (p48_cells (Z_to_bv 8 0) j161 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
      rw_cells usegs m2 IMPL (impl_cells16 vptr nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
      rw_cells usegs m2 sp0 [CB 24 jg2] -> rw_cells usegs m2 (sp0 + 24) [CB 16 jl2] -> rw_cells usegs m2 (sp0 + 40) [CB 24 jo2] -> rw_cells usegs m2 (sp0 + 64) [CB 16 jn2] ->
      rw_cells usegs m2 (sp0 + 80) (res_cells (sp0 + 128) r jr20) ->
      rw_cells usegs m2 (sp0 + 208) [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j225] ->
      rw_cells usegs m2 (sp0 + 232) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM usegs (mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
                   mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => mbind (vfree lops (cap, Z.of_nat (atp_P d), Some bv)) (fun _ => mret 0)))))))) st2
        (rfuzz_one_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0)
        (MS (mkR y1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F1 (Z_to_bv 64 0x273c4) fc1 None m2 (seg_rom usegs))).
    { intros m2 st2 y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 errv2 jg2 jl2 jo2 jn2
             HEAP2 AUX2 MI2 ST2 ERR2 FA2 SO2 PRES2 SJS2 PL2 SV2 BLK2 PA0' PIMPL' PA16' DOCC' P48' THIS' GSO' LEAF' OUT' NODE' RES' XFD' SAVE'.
      assert (BLB2 : forall a, in_block LB a -> a < alloc_ceiling) by exact BLB.
      assert (LXS2 : lx_statics m2).
      { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES2)| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
        pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
        unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
      pose proof LXS2 as (_ & _ & _ & _ & VTD2). unfold Zf2.wz in VTD2.
      rewrite EVP in THIS'.
      pose proof (rw_cells_forget _ _ _ _ RES') as [jres RESJ]. clear RES'.
      replace (cells_size (res_cells (sp0 + 128) r jr20)) with 24%nat in RESJ by (unfold res_cells; destruct (bv_eqb r (Z_to_bv 64 0)); reflexivity).
      readdr PIMPL' (sp0 + 104 + 8). readdr DOCC' (sp0 + 104 + 24). readdr P48' (sp0 + 104 + 48).
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      step. step.
      ihere. to_implM.
      eapply (pdtor_cps HF) with (B := B) (lo := lo) (ocp := None) (PARSER := sp0 + 104) (IMPL := IMPL) (IDX := IDX) (OC := OC) (IA := IA) (TAPE := TAPE) (SBUF := SBUF)
                                  (psb := psb) (ptp := ptp) (pim := pim) (pix := pix) (poc := poc) (pia := pia);
        [exact HEAP2| exact AUX2| lia| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI2| lia| lia| lia
        | exact VTD2| exact PIMPL'| exact DOCC'| exact P48'| exact THIS'|].
      intros st3 ms3 PO. unfold hpost in PO.
      destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3
                      & -> & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & RR).
      unfold pdtor_R in RR. destruct RR as (HEAP3 & PRES23 & PIMPL3 & DOCC3 & P483). unfold p48_cells in P483.
      replace (ret_pc (Z_to_bv 64 0x273cc)) with (Z_to_bv 64 0x273cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR3.

      pose proof (agree_of_lx_pres _ _ _ _ _ PRES23) as AG23.
      assert (FRCL : forall a, sp0 <= a < sp0 + 272 -> ~ (sp0 + 112 <= a < sp0 + 120) -> ~ (sp0 + 128 <= a < sp0 + 144) -> ~ (sp0 + 168 <= a < sp0 + 176) ->
                lx_client ((bv, A, 16 * cap) :: LB) sp0 (pdtor_X (sp0 + 104)) a).
      { intros a Ha N1 N2 N3. split; [| left; lia]. unfold pdtor_X. cbn [rin_ivs fst snd]. clear - Ha N1 N2 N3. lia. }
      apply (rw_cells_agree _ _ _ _ _ AG23) in SV2; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in GSO'; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in LEAF'; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in OUT'; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in NODE'; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in RESJ; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in PA0'; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in PA16'; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in XFD'; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG23) in SAVE'; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG23) in BLK2;
        [| intros a _ Ha; split; [unfold pdtor_X; cbn [rin_ivs fst snd]; clear - Ha AC CEIL LO Esp0; lia| right; left; exists (bv, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]]
         | exact ELS| lia].
      assert (PL3 : payload_ok m3 LB D d).
      { eapply payload_ok_agree; [exact AG23| exact PL2|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. split; [unfold pdtor_X; cbn [rin_ivs fst snd]; clear - Ha BC CEIL LO Esp0; lia| right; left; exists b; split; [right; exact Hb| exact Ha]]. }
      assert (SJS3 : sj_statics m3 true).
      { eapply sj_statics_agree; [exact AG23| | exact SJS2]. intros a Ha. apply sjs_addr_client; [exact Ha|]. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. unfold pdtor_X. cbn [rin_ivs fst snd]. clear - Ha GLO LO Esp0. lia. }
      assert (PRES3 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m3).
      { eapply lx_pres_trans; [exact PRES2|]. eapply (lx_pres_sub LB (sp0 + 272) _ _ _ _ _ _ PRES23); [lia| intros b0 Hb0; right; exact Hb0|].
        intros a Ha NX. unfold pdtor_X in Ha. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB a IB); lia| lia]. }
      clear AG23 PRES23 HEAP2 AUX2 PRES2 SJS2 PL2 MU WM FRCL.
      pose proof (munch_refl [(sp0, sp0 + 272)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      assert (ND : List.NoDup (map blk_id ((bv, A, 16 * cap) :: LB))) by (eapply LH_nodup; exact HEAP3).
      pose proof (atp_P_ge2 d) as PGE2'. pose proof (atp_P_bound d) as PBD'.
      destruct (rw_cells_forget _ _ _ _ PA0') as [jh PA0'']. cbn [cells_size csize Nat.add] in PA0''. clear PA0'.
      unfold implM. iprefix.

      step. hstep. step. step.

      step. step. if_lia. zstep. rewrite (Z5l.land7_mod8 (sp0 + 184)) by lia. step. if_false.
      step. step. if_lia. step. step. if_lia. step.

      eapply (vdtor_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (atp_P d)); [lia| lia| lia|].
      step. zstep. replace (A + 16 * cap + - A) with (16 * cap) by lia. hstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      assert (HEAP4 : RHEAP st3 ((bv, A, 16 * cap) :: LB) m4).
      { eapply LH_frame; [exact HEAP3| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX4 : rauxv_ok m4 B).
      { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES4 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m4).
      { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      assert (SJS4 : sj_statics m4 true).
      { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS3]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
      assert (PL4 : payload_ok m4 LB D d).
      { eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact PL3|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
      clear MU WM.
      ihere. to_implM. cbn [vfree]. eapply implM_bind.
      { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := A) (n := 16 * cap);
          [exact HEAP4| left; reflexivity| exact AUX4| lia| eassumption| exact CEIL'| unfold RFREE_STACK; lia| eassumption| assumption| lia]. }
      cbv beta. intros [] st5 ms5 PO. unfold free_postZ in PO.
      destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5
                      & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
      rewrite (lb_remove_hd _ _ _ _ ND) in HP5, HEAP5.
      replace (ret_pc (Z_to_bv 64 0x273dc)) with (Z_to_bv 64 0x273dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP5) as AG5.
      assert (FRH : forall a, sp0 <= a < sp0 + 272 -> rclient_addr LB sp0 a) by (intros a Ha; left; lia).
      lazymatch goal with H : rw_cells usegs m4 (sp0 + 184) _ |- _ => apply (rw_cells_agree _ _ _ _ _ AG5) in H; [rename H into SV5| intros a Ha; cbn in Ha; apply FRH; lia] end.
      lazymatch goal with H : rw_cells usegs m4 (sp0 + 104) _ |- _ => apply (rw_cells_agree _ _ _ _ _ AG5) in H; [rename H into PA0'| intros a Ha; cbn in Ha; apply FRH; lia] end.
      apply (rw_cells_agree _ _ _ _ _ AG5) in GSO'; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in LEAF'; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in OUT'; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in NODE'; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in RESJ; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in PIMPL3; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in PA16'; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in DOCC3; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in P483; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in XFD'; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in SAVE'; [| intros a Ha; cbn in Ha; apply FRH; lia].
      pose proof (statics_heap _ _ _ _ HP5 ltac:(unfold GLOBALS_TOP; lia)) as (_ & SJSf & _). pose proof (SJSf _ SJS4) as SJS5. clear SJSf.
      assert (PL5 : payload_ok m5 LB D d).
      { eapply payload_ok_agree; [exact AG5| exact PL4|]. intros b a Hb Ha. right; right. exists b. split; [exact Hb| exact Ha]. }
      assert (PRES5 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m5).
      { eapply lx_pres_trans; [exact PRES4|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP5| lia| intros b Hb; exact Hb]. }
      clear AG5 HP5 HEAP4 AUX4 PRES4 SJS4 PL4 HEAP3 AUX3 PRES3 SJS3 PL3.

      readdr PIMPL3 (sp0 + 112). readdr DOCC3 (sp0 + 128). readdr P483 (sp0 + 152).
      pose proof (rw_cells_join _ _ _ _ _ GSO' LEAF' ltac:(cbn [cells_size csize Nat.add]; lia)) as J0a.
      pose proof (rw_cells_join _ _ _ _ _ J0a OUT' ltac:(cbn [app cells_size csize Nat.add]; lia)) as J0b.
      pose proof (rw_cells_join _ _ _ _ _ J0b NODE' ltac:(cbn [app cells_size csize Nat.add]; lia)) as J0c.
      pose proof (rw_cells_join _ _ _ _ _ J0c RESJ ltac:(cbn [app cells_size csize Nat.add]; lia)) as J1.
      pose proof (rw_cells_join _ _ _ _ _ J1 PA0' ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2.
      pose proof (rw_cells_join _ _ _ _ _ J2 PIMPL3 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J3.
      pose proof (rw_cells_join _ _ _ _ _ J3 PA16' ltac:(cbn [app cells_size csize Nat.add]; lia)) as J4.
      pose proof (rw_cells_join _ _ _ _ _ J4 DOCC3 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J5.
      pose proof (rw_cells_join _ _ _ _ _ J5 P483 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J6.
      pose proof (rw_cells_join _ _ _ _ _ J6 SV5 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J7.
      pose proof (rw_cells_join _ _ _ _ _ J7 XFD' ltac:(cbn [app cells_size csize Nat.add]; lia)) as J8.
      pose proof (rw_cells_join _ _ _ _ _ J8 SAVE' ltac:(cbn [app cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR.
      clear J0a J0b J0c J1 J2 J3 J4 J5 J6 J7 J8 GSO' LEAF' OUT' NODE' RESJ PA0' PIMPL3 PA16' DOCC3 P483 SV5 XFD' SAVE'.
      pose proof (munch_refl [(sp0, sp0 + 272)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
      apply implM_ret.

      step. do 5 step. step. release_frame FR ST5 (sp0 + 272). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (sp0 + 272) [LXW_SJ] a -> outside [(sp0, sp0 + 272)] a).
      { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      assert (PRESF : lx_pres LB (sp0 + 272) [LXW_SJ] m0 mF).
      { eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
      pose proof (agree_of_lx_pres _ _ _ _ _ PRESF) as AGF.
      rewrite Esp0. replace (usp - 272 + 272) with usp by lia. rewrite <- ESP. rewrite Esp0 in PRESF. replace (usp - 272 + 272) with usp in PRESF by lia.
      apply evt_done. unfold rfuzz_one_post, lx_post_env, lx_env. cbn [app]. rewrite <- Eusp. do 15 eexists. exists F1, fc1, mF.
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { split; [| split; [exact FRM1| split; [exact PRESF| split; congruence]]].
        exists errv3.
        split. { eapply LH_frame; [exact HEAP5| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        split. { eapply lx_statics_agree; [exact AGF| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
                 pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
                 unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
        split. { exists true. eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS5]. intros a Ha.
                 unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
        split. { eapply stderr_wfile_agree; [exact AGF| | exact SEW0]. intros a Ha. apply stderr_addr_client; [exact Ha|].
                 unfold stderr_addr in Ha. unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
        split. { pose proof (ssp_canary_0 _ _ _ _ HEAP00 SSP0) as EC. rewrite EC. eapply RHEAP_ssp.
                 eapply LH_frame; [exact HEAP5| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        split. { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        split; [lia|]. split; [exact B63|]. split; [rewrite Esp0 in ST5; replace (usp - 272 + 272) with usp in ST5 by lia; exact ST5|]. split; [exact CEIL'|]. split; [unfold GLOBALS_TOP; lia|].
        split. { unfold errno_addr, RATP. rewrite unsigned_lit by lia. rewrite ELX in ERR5. exact ERR5. }
        split; [reflexivity| assumption]. }
      split. { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS5]. intros a Ha.
               unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
      split; [reflexivity|]. split; [reflexivity|].
      eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact PL5|]. intros b a Hb Ha.
      pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }

    pose proof (atp_P_ge2 d) as PGE2. pose proof (atp_P_bound d) as PBD.
    destruct (bv_eqb r (Z_to_bv 64 0)) eqn:ER.
    -
      assert (R0 : r = Z_to_bv 64 0) by (unfold bv_eqb in ER; apply Z.eqb_eq in ER; apply bv_eq; rewrite ER; reflexivity).
      pose proof RES as RESC. unfold res_cells in RESC. rewrite ER in RESC.

      destruct OKR as [K|(E0 & tws & sbs & BT & BS & WF & RNG & LT & LS)].
      { exfalso. unfold bv_eqb in ER. apply Z.eqb_eq in ER. rewrite unsigned_lit in ER by lia. clear - K ER. lia. }
      pose proof (tape_wf_root _ _ _ _ _ WF) as [ELR NR].

      destruct (atp_els_second D d) as (e0 & P1 & rest1 & EE1 & HP1).
      pose proof BLK as BLK'. unfold vblk in BLK'. destruct BLK' as (BE & BJ & BR & C1). rewrite EE1 in BE.
      destruct (rw_cells_split_at1 _ _ _ 2%nat BE) as [_ BE1]. cbn [velts fst snd firstn skipn cells_size csize Nat.add] in BE1.
      pose proof (rw_cells_take2 _ _ _ _ _ BE1) as STR1. clear BE1.
      destruct e0 as [e0a e0b]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in STR1. readdr STR1 (A + 16).
      lazymatch type of STR1 with rw_cells _ _ (A + 16) _ => idtac end.
      pose proof (atp_ptr_len d) as P1L. assert (ZP : zlength (atp_ptr d) = Z.of_nat (length (atp_ptr d))) by reflexivity.
      assert (LBM : length (map (Z_to_bv 8) (atp_ptr d)) = length (atp_ptr d)) by apply length_map.
      set (LBall := (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 capd + 9)) :: (pim, IMPL, 96)
                     :: (ptp, TAPE, 8 * roundup64 (capd + 3)) :: (psb, SBUF, roundup64 (5 * (capd / 3) + 64)) :: (bv, A, 16 * cap) :: LB) in *.
      assert (PTRF : bytes_at usegs m1 P1 (map (Z_to_bv 8) (atp_ptr d)) /\ (atp_ptr d = [] \/ in_blocks LBall P1 (zlength (atp_ptr d))) /\ 0 <= P1 /\ P1 + zlength (atp_ptr d) < 2^63).
      { destruct HP1 as [[L1 ->]|(off & EQ & EP1 & BO)].
        - rewrite L1. cbn [map zlength length Z.of_nat]. split; [apply bytes_at_nil; lia|]. split; [left; reflexivity|]. unfold zlength. cbn [length Z.of_nat]. lia.
        - destruct PIN as [E0d|(b0 & Hb & Hb1 & Hb2)].
          + assert (PN : atp_ptr d = []) by (rewrite EQ, E0d, skipn_nil, firstn_nil; reflexivity).
            assert (O0 : off = 0%nat) by (rewrite E0d in BO; cbn in BO; lia). subst off.
            rewrite PN. cbn [map]. split; [apply bytes_at_nil; lia|]. split; [left; reflexivity|]. unfold zlength. cbn [length Z.of_nat]. lia.
          + split.
            { rewrite EQ at 1. fold (to_bytes (firstn (length (atp_ptr d)) (skipn off d))). rewrite to_bytes_firstn, to_bytes_skipn. subst P1.
              apply bytes_at_firstn. apply bytes_at_skipn; [exact PB1| pose proof (to_bytes_length d); lia]. }
            split; [| unfold zlength in *; lia]. right. exists b0. split; [subst LBall; do 7 right; exact Hb|]. unfold zlength in *. lia. }
      destruct PTRF as (PTRB & PTRIN & PTR0 & PTRH).
      assert (P1F : Forall (fun c => 0 <= c < 256) (atp_ptr d)).
      { destruct HP1 as [[L1 _]|(off & EQ & _)]; [rewrite L1; constructor|]. rewrite EQ. apply Forall_firstn', Forall_skipn'. exact PRNG. }
      set (E := mkAE LBall lo B (sp0 + 128) TAPE SBUF tws sbs P1 (atp_ptr d)).
      assert (OKE : aenv_ok E).
      { subst E. constructor; cbn [ae_LB ae_lo ae_B ae_DOC ae_TAPE ae_SBUF ae_tws ae_sbs ae_PTR ae_p1].
        - exact WF. - exact RNG. - exact P1F. - change (2^26) with 67108864; unfold zlength in *; lia.
        - exists (ptp, TAPE, 8 * roundup64 (capd + 3)). split; [subst LBall; do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        - exists (psb, SBUF, roundup64 (5 * (capd / 3) + 64)). split; [subst LBall; do 5 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        - exact PTRIN. - split; [exact PTR0| exact PTRH]. - split; [exact CEIL'| unfold GLOBALS_TOP; lia]. - exact B63. - lia.
        - split; [clear - AL16 Esp0; subst sp0; lia| clear - TP16; lia]. }
      pose proof (ROOT E OKE) as RT. unfold atp_elem_stmt in RT.
      pose proof (rw_cells_take2 _ _ _ _ _ RESC) as RES2. pose proof (rw_cells_take2 _ _ _ _ _ DOCC) as DOC2.
      assert (AI1 : AINV E m1) by (subst E; split; [exact BT| split; [exact BS| split; [exact PTRB| exact DOC2]]]).

      apply (rw_cells_split_CB usegs _ _ [] 16 jn [] [8;8]%nat) in NODEC; [|reflexivity]. cbn [mk_CB_cells app] in NODEC.
      pose proof (munch_refl [(sp0 + 64, sp0 + 80)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      hide THIS. hide P48. hide BT. hide BS. hide PTRB.
      unfold implM. iprefix.

      step. step. step. if_false. step. if_false.
      ihere. to_implM. apply implM_atp_gate_ok.
      unfold implM. iprefix.

      step. step. step. hide RES. hstep. hstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG12.
      unhide THIS. unhide P48. unhide RES. unhide BT. unhide BS. unhide PTRB.
      apply (rw_cells_agree _ _ _ _ _ AG12) in THIS; [| intros a Ha; unfold impl_cells16 in Ha; cbn in Ha; cbn [outside]; clear - Ha IMC CEIL LO Esp0; lia].
      apply (rw_cells_agree _ _ _ _ _ AG12) in RES; [| intros a Ha; unfold res_cells in Ha; rewrite ER in Ha; cbn in Ha; cbn [outside]; clear - Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG12) in P48; [| intros a Ha; unfold p48_cells in Ha; cbn in Ha; cbn [outside]; clear - Ha; lia].
      assert (AI2 : AINV E m2).
      { eapply AINV_agree; [exact AI1| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OKE].
        - intros a (b & Hb & Hr). subst E. cbn [ae_LB] in Hb. pose proof (LH_block_range _ _ _ _ HEAP1 Hb) as (_ & _ & _ & BC & _).
          unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. lia.
        - intros a Ha. subst E. cbn [ae_DOC] in Ha. cbn [outside]. lia. }
      assert (HEAP2 : RHEAP s1' LBall m2).
      { eapply LH_frame; [exact HEAP1| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX2 : rauxv_ok m2 B).
      { eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES12 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m2).
      { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      assert (SJS2 : sj_statics m2 true).
      { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS1]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
      assert (PL2 : payload_ok m2 LB D d).
      { eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact PL1|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
      apply (vblk_agree _ _ _ _ _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO Esp0; lia| exact ELS| lia].
      clear MU WM.
      subst E. cbn [ae_LB ae_lo ae_B ae_DOC ae_TAPE ae_SBUF ae_tws ae_sbs ae_PTR ae_p1] in RT, AI2.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.

      step. if_lia.
      zstep. step. if_lia.
      zstep. zstep. rewrite (Z5l.land7_mod8 (A + 16)) by lia. step. if_false.
      step. step. step. step. step.
      lazymatch goal with H : rw_cells usegs m2 (sp0 + 64) _ |- _ => rename H into NODE2 end.
      lazymatch goal with H : stk usegs m2 _ _ |- _ => rename H into ST2 end.
      lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
      lazymatch goal with H : rw_cells usegs m2 606604 _ |- _ => rename H into ERR2 end.
      ihere. to_implM. eapply implM_bind.
      { eapply (RT (atp_ptr d) 1 (Z.of_nat (length tws) - 1) sp0 (sp0 + 40) (sp0 + 64) P1) with (jo := jo);
          [exact AI2| exists []; split; [reflexivity| unfold zlength; cbn [ae_PTR ae_p1 length Z.of_nat]; lia]| exact ELR| lia| lia| exact NODE2| lia| lia| lia| exact OUT| lia| lia| lia
          | exact HEAP2| exact AUX2| lia| exact ST2| unfold elem_need, ATP_LEAFX, RMALLOC_STACK; change (Z.of_nat TAPE_MAX_DEPTH) with 1024; lia
          | clear - AL16 Esp0; subst sp0; lia| rewrite ELX; exact ERR2| exact MI2]. }
      cbv beta. intros [] st7 ms7 PO. unfold hpost in PO.
      destruct PO as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m7 & -> & MI7 & ST7 & [errv7 ERR7] & AUX7 & FA7 & SO7 & RR).
      unfold lvl_R in RR. destruct RR as (HEAP7 & PRES27 & OUTR). cbn [ae_LB ae_lo ae_B] in HEAP7, PRES27.
      replace (ret_pc (Z_to_bv 64 0x2738c)) with (Z_to_bv 64 0x2738c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR7.

      pose proof (agree_of_lx_pres _ _ _ _ _ PRES27) as AG27.
      assert (FRCL : forall a, sp0 <= a < sp0 + 272 -> ~ (sp0 + 40 <= a < sp0 + 64) -> lx_client LBall sp0 [(sp0 + 40, sp0 + 40 + 24)] a).
      { intros a Ha N1. split; [cbn [rin_ivs fst snd]; clear - Ha N1; lia| left; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AG27) in RES; [| intros a Ha; unfold res_cells in Ha; rewrite ER in Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in PA0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in PIMPL; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in PA16; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in DOCC; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in P48; [| intros a Ha; unfold p48_cells in Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in SV; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in XFD; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in GSO; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in LEAF; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in NODE2; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG27) in THIS;
        [| intros a Ha; split; [cbn [rin_ivs fst snd]; clear - Ha IMC CEIL LO Esp0; unfold impl_cells16 in Ha; cbn in Ha; lia| right; left; exists (pim, IMPL, 96); split; [subst LBall; do 3 right; left; reflexivity| unfold impl_cells16 in Ha; cbn in Ha; cbn [blk_addr blk_size fst snd]; lia]]].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG27) in BLK;
        [| intros a _ Ha; split; [cbn [rin_ivs fst snd]; clear - Ha AC CEIL LO Esp0; lia| right; left; exists (bv, A, 16 * cap); split; [subst LBall; do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]]
         | exact ELS| lia].
      assert (SJS7 : sj_statics m7 true).
      { eapply sj_statics_agree; [exact AG27| | exact SJS2]. intros a Ha. apply sjs_addr_client; [exact Ha|]. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. clear - Ha GLO LO Esp0. lia. }
      assert (PL7 : payload_ok m7 LB D d).
      { eapply payload_ok_agree; [exact AG27| exact PL2|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. split; [cbn [rin_ivs fst snd]; clear - Ha BC CEIL LO Esp0; lia| right; left; exists b; split; [subst LBall; do 7 right; exact Hb| exact Ha]]. }
      assert (PRES7 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m7).
      { eapply lx_pres_trans; [exact PRES12|]. eapply (lx_pres_sub LB (sp0 + 272) _ _ _ _ _ _ PRES27); [lia| intros b0 Hb0; subst LBall; do 7 right; exact Hb0|].
        intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB a IB); lia| lia]. }
      assert (AI7 : AINV (mkAE LBall lo B (sp0 + 128) TAPE SBUF tws sbs P1 (atp_ptr d)) m7).
      { eapply AINV_agree; [exact AI2| exact AG27| | | exact OKE]; cbn [ae_LB ae_DOC].
        - intros a Ha. split; [| right; left; exact Ha]. destruct Ha as (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP2 Hb) as (_ & _ & _ & BC & _).
          unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. cbn [rin_ivs fst snd]. clear - Hr BC CEIL LO Esp0. lia.
        - intros a Ha. split; [cbn [rin_ivs fst snd]; clear - Ha; lia| left; lia]. }
      clear AG27 MU WM.
      destruct OUTR as (r0 & jx & code & jn4 & OUTC & CR & OIMP). cbn [ae_DOC ae_tws ae_sbs] in OIMP.
      pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl usegs m7) as WM.
      unfold implM. iprefix.

      astep. step. step. if_lia. step. if_cases KC; zify_cond KC.
      +
        destruct (rw_cells_forget _ _ _ _ OUTC) as [jo7 OUT7]. cbn [cells_size csize Nat.add] in OUT7.
        destruct (rw_cells_forget _ _ _ _ NODE2) as [jn7 NODE7]. cbn [cells_size csize Nat.add] in NODE7.
        ihere. to_implM. subst LBall. eapply K2C8; try eassumption; congruence.
      +
        destruct (OIMP ltac:(clear - KC CR; lia)) as (ER0 & J0 & dd & jj & ELJ). subst r0.
        apply (rw_cells_split_CB usegs _ _ [] 16 jl [] [8;8]%nat) in LEAF; [|reflexivity]. cbn [mk_CB_cells app] in LEAF.
        apply (rw_cells_split_CB usegs _ _ [] 24 jg [] [8;8;4;4]%nat) in GSO; [|reflexivity]. cbn [mk_CB_cells app] in GSO.
        clear MU WM. pose proof (munch_refl [(sp0 + 24, sp0 + 40)]%Z m7) as MU. pose proof (wmono_refl usegs m7) as WM.
        hide RES. hide P48. hide THIS.

        step. step. hstep. hstep. step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
        lazymatch goal with H : rw_cells usegs m8 (sp0 + 24) _ |- _ => rename H into LEAF8 end.
        lazymatch goal with H : stk usegs m8 _ _ |- _ => rename H into ST8 end.
        lazymatch goal with H : mem_inv usegs m8 |- _ => rename H into MI8 end.
        assert (AI8 : AINV (mkAE LBall lo B (sp0 + 128) TAPE SBUF tws sbs P1 (atp_ptr d)) m8).
        { eapply AINV_agree; [exact AI7| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OKE]; cbn [ae_LB ae_DOC].
          - intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP2 Hb) as (_ & _ & _ & BC & _).
            unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. lia.
          - intros a Ha. cbn [outside]. lia. }
        assert (HEAP8 : RHEAP st7 LBall m8).
        { eapply LH_frame; [exact HEAP7| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        eapply evt_cut.
        { try replace (Z_to_bv 64 (sp0 + 0)) with (Z_to_bv 64 sp0) by (f_equal; lia).
          eapply (getstr_spec _ OKE) with (s := st7) (dd := dd) (jj := jj); cbn [ae_LB ae_lo ae_B ae_DOC ae_TAPE ae_SBUF ae_tws ae_sbs ae_PTR ae_p1];
            [exact AI8| exact HEAP8| exact ELJ| exact J0| exact LEAF8| exact GSO| lia| lia| exact ST8| lia| exact MI8]. }
        cbv beta. intros ms' PO. unfold getstr_post in PO.
        destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m9 & gw0 & gw8 & gcode
                        & -> & MU9 & WM9 & MI9 & ST9 & GSO9 & GCR).
        replace (ret_pc (Z_to_bv 64 0x273b8)) with (Z_to_bv 64 0x273b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        hide MU. hide WM. transport_after_call usegs m8 m9 MU9 WM9. unhide MU. unhide WM.

        assert (MU9' : munch [(sp0 - 48, sp0 + 40)]%Z m7 m9).
        { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU9]]; unfold sub_fp; cbn [outside]; intros x Hx; lia. }
        pose proof (wmono_trans usegs _ _ _ WM WM9) as WM9'.
        assert (HEAP9 : RHEAP st7 LBall m9).
        { eapply LH_frame; [exact HEAP7| exact MU9'| exact WM9'|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        assert (AUX9 : rauxv_ok m9 B).
        { eapply rauxv_ok_frame; [exact AUX7| exact MU9'| exact WM9'|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        assert (PRES9 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m9).
        { eapply lx_pres_trans; [exact PRES7|]. eapply lx_pres_of_munch; [exact MU9'| exact WM9'|].
          intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
        assert (SJS9 : sj_statics m9 true).
        { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU9' WM9')| | exact SJS7]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
        assert (PL9 : payload_ok m9 LB D d).
        { eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU9' WM9')| exact PL7|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
          unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
        pose proof (agree_on_of_munch _ _ _ MU9' WM9') as AG9.
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG9) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO Esp0; lia| exact ELS| lia].
        unhide RES. unhide P48. unhide THIS.
        apply (rw_cells_agree _ _ _ _ _ AG9) in RES; [| intros a Ha; unfold res_cells in Ha; rewrite ER in Ha; cbn in Ha; cbn [outside]; clear - Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG9) in P48; [| intros a Ha; unfold p48_cells in Ha; cbn in Ha; cbn [outside]; clear - Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG9) in THIS; [| intros a Ha; unfold impl_cells16 in Ha; cbn in Ha; cbn [outside]; clear - Ha IMC CEIL LO Esp0; lia].

        clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m9) as MU. pose proof (wmono_refl usegs m9) as WM.
        astep. step. step. if_lia.
        destruct (rw_cells_forget _ _ _ _ GSO9) as [jg9 GSO9']. cbn [cells_size csize Nat.add] in GSO9'.
        lazymatch goal with H : rw_cells usegs m9 (sp0 + 24) _ |- _ => destruct (rw_cells_forget _ _ _ _ H) as [jl9 LEAF9]; cbn [cells_size csize Nat.add] in LEAF9 end.
        lazymatch goal with H : rw_cells usegs m9 (sp0 + 40) _ |- _ => destruct (rw_cells_forget _ _ _ _ H) as [jo9 OUT9]; cbn [cells_size csize Nat.add] in OUT9 end.
        lazymatch goal with H : rw_cells usegs m9 (sp0 + 64) _ |- _ => destruct (rw_cells_forget _ _ _ _ H) as [jn9 NODE9]; cbn [cells_size csize Nat.add] in NODE9 end.
        ihere. to_implM. subst LBall. eapply K2C8; try eassumption; congruence.
    -
      pose proof RES as RESC. unfold res_cells in RESC. rewrite ER in RESC.
      assert (RNZ : 1 <= bv_unsigned r < 64).
      { destruct OKR as [K|(E0 & _)]; [exact K|]. exfalso. unfold Zf2.wz in E0. subst r. unfold bv_eqb in ER. rewrite Z.eqb_refl in ER. discriminate. }
      pose proof (bv_unsigned_in_range 64 r) as RR64. unfold bv_modulus in RR64. cbn in RR64.
      pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      unfold implM. iprefix. step. rewrite <- (Z_to_bv_bv_unsigned r). rewrite sx32_small by lia.
      step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K RNZ; lia| clear K].
      step. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K RNZ; lia].
      ihere. to_implM. apply implM_atp_gate_fail. try rewrite (Z_to_bv_bv_unsigned r).
      eapply K2C8; try eassumption.
  Qed.
End Proofs.
End WithCeiling0.
