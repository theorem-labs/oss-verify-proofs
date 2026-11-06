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
From Stdlib Require Permutation.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pwlopts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_cases.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Module CJ_pv_pro.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pwlopts_A.CJ_band3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_cases OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma words_of_bytes : forall (k : nat) (bs : list byte), length bs = (8 * k)%nat ->
  exists ws : list word, length ws = k /\ cells_bytes (map C8 ws) = bs.
Proof.
  induction k as [|k IH]; intros bs L.
  - exists []. destruct bs; [split; reflexivity| cbn in L; lia].
  - (nelim (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) 3%nat; intros ws LW EB).
    exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [cbn; lia|].
    cbn [map cells_bytes cbytes]. rewrite EB. rewrite le8_of_bytes8 by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.

Lemma cells_wf_mapC8 : forall ws : list word, cells_wf (map C8 ws).
Proof. induction ws; cbn; [exact I| split; [reflexivity| assumption]]. Qed.

Lemma locals_of_CB : forall m A junk, rw_cells bsegs m A [CB 72 junk] ->
  exists loc : list word, rw_cells bsegs m A (map C8 loc) /\ length loc = 9%nat.
Proof.
  intros m A junk H. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [L _].
  (nelim (words_of_bytes 9 junk ltac:(lia)) 3%nat; intros ws LW EB). exists ws. split; [| exact LW].
  eapply rw_cells_recast; [exact H| apply cells_wf_mapC8| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact EB].
Qed.

(* [comment removed for export] *)
Lemma pv_le4_wz_small : forall ty, 0 <= ty < 256 -> le4 (wz ty) = [wb ty; wb 0; wb 0; wb 0].
Proof.
  intros ty H. unfold le4, wz, wb. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  replace (Z.shiftr ty 8) with 0 by (rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_small by lia; reflexivity).
  reflexivity.
Qed.

Definition pv_nodeB (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z) : list cell :=
  [C8 (wz nx); C8 pv; C8 (wz ch); C1 (wb ty); C1 (wb 0); C1 (wb 0); C1 (wb 0); C4 p1; C8 (wz vs); C4 vi; C4 p2; C8 vd; C8 (wz ky)].

Lemma pv_nodeB_of_node : forall m p nx pv ch ty p1 vs vi p2 vd ky, 0 <= ty < 256 ->
  rw_cells bsegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> rw_cells bsegs m p (pv_nodeB nx pv ch ty p1 vs vi p2 vd ky).
Proof.
  intros until ky. intros TY H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I|].
  unfold pv_nodeB, node_cells. cbn [cells_bytes cbytes app]. rewrite (pv_le4_wz_small ty TY). reflexivity.
Qed.

Section PRO.
  Variables (AI : art_iface) (TI : trs_iface).
  Let CASEH (E : Z) : Prop := forall Q, q_ai Q = AI -> q_ti Q = TI -> pvl Q ->
                                (forall d, (d < q_n Q)%nat -> print_value_at AI TI d) -> pv_case_at E Q.
  Hypothesis CASE_F : CASEH PV_FALSE_ENTRY.
  Hypothesis CASE_T : CASEH PV_TRUE_ENTRY.
  Hypothesis CASE_N : CASEH PV_NULL_ENTRY.
  Hypothesis CASE_NUM : CASEH PV_NUM_ENTRY.
  Hypothesis CASE_STR : CASEH PV_STR_ENTRY.
  Hypothesis CASE_ARR : CASEH PV_ARR_ENTRY.
  Hypothesis CASE_OBJ : CASEH PV_OBJ_ENTRY.

  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.

  Theorem pv_entry : forall n, (forall d, (d < n)%nat -> print_value_at AI TI d) -> print_value_at AI TI n.
  Proof.
    intros n REC. unfold print_value_at. intros until errv.
    intros HL HP PS PD PN DEPN CHn PNZ BLR PL PB8 AL S47 TOP BOT PB80 HB16 HB8 ST CEIL LO ERR MI TP FRM SSZ TV NPM LFR CC CHOK CHL CHB RA1 RAH RA2 BBA A0 A1.
    subst a0 a1. unfold wz, PVALUE_ENTRY.
    (* [comment removed for export] *)
    (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APV_STACK in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (bv_unsigned_in_range 64 ra) as RAR. change (bv_modulus 64) with (2^64) in RAR.
    pose proof (bv_unsigned_in_range 64 s0) as S0R. change (bv_modulus 64) with (2^64) in S0R.
    pose proof (ASTACK_TOP_le sp0) as TOPR. unfold AIMG_HI in RAH.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CHn PNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bcc Bn Ed ND TY PT SV SK CHC CHN' EB).
    assert (N1 : (1 <= n)%nat) by lia.
    assert (PIN : In (p, 64) LB). { eapply Permutation_in; [exact HP|]. right. apply BLR. rewrite EB. left. reflexivity. }
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL PIN) 4%nat; intros P1 P2 _ P4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in P1. bandM. sepM. try rewrite alloc_ceiling_eq in P4.
    pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SB. pose proof (art_uar_cells AI _ _ _ _ _ _ _ _ _ HL) as UAR.
    unfold pb_struct, wz in PS. unfold AERRNO, ATP in ERR. destruct PD as [ARR LEN].
    pose proof ND as NDc. unfold node_cells, wz in ND.
    (* [comment removed for export] *)
    eapply lscps_step_evt.
    pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    shbase_split SB. destruct UAR as [UAR1 UAR2].
    zstep. carve_frame 192%nat ST. zstep. fix_lit_store. sepM. do 15 zstep.
    zstep. zstep.
    rewrite land_align32 by lia.
    set (SA := (bv_unsigned sp + -192) / 32 * 32) in *.
    assert (GSA : bv_unsigned sp - 208 <= SA <= bv_unsigned sp - 192 /\ SA mod 32 = 0) by (subst SA; Z.div_mod_to_equations; lia).
    clearbody SA. destruct GSA as [GSA1 GSA2].
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with context [CB 64 ?j] => set (j64 := j) in FR; clearbody j64 end.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?cs) => change (c1 :: c2 :: cs) with ([c1; c2] ++ cs) in FR end.
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FR. destruct FR as [FRLO SAVW].
    cbn [cells_size Cells.csize Nat.add] in SAVW. change (Z.of_nat 72) with 72 in SAVW.
    replace (bv_unsigned sp + -192 + 72) with (bv_unsigned sp + -120) in SAVW by lia.
    eapply stk_release in FRLO; [| exact ST| lia]. cbn [cells_size Cells.csize Nat.add] in FRLO. change (Z.of_nat 72) with 72 in FRLO.
    replace (bv_unsigned sp + -192 + 72) with (bv_unsigned sp + -120) in FRLO by lia. clear ST.
    destruct (stk_split bsegs m1 lo SA (bv_unsigned sp + -120) FRLO ltac:(lia)) as [ST STP0]. clear FRLO.
    destruct (stk_split bsegs m1 SA (SA + 72) (bv_unsigned sp + -120) STP0 ltac:(lia)) as [STL PAD]. clear STP0.
    (nelim (stk_carve bsegs m1 SA (SA + 72) 72 STL ltac:(lia)) 3%nat; intros _ lj LOCJ). clear STL.
    change (Z.of_nat 72) with 72 in LOCJ. replace (SA + 72 - 72) with SA in LOCJ by lia.
    (nelim (locals_of_CB _ _ _ LOCJ) 3%nat; intros loc0 LOC LL). clear LOCJ lj.
    (nelim (loc9 loc0 LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 EL). subst loc0. cbn [map] in LOC.
    (* [comment removed for export] *)
    do 8 zstep. zstep. zstep. if_false. zstep. zstep.
    (* [comment removed for export] *)
    assert (HLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (HL1 : ART AI sp0 SPB LB LF TRS BB m1 mo g).
    { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. constructor; [| constructor]. right; left. cbn. lia. }
    assert (PVA1 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m1).
    { eapply (pv_agree_stack AI); [exact HL| exact HLR| exact MU| exact WM| lia| lia| lia| lia]. }
    assert (CC1 : chain_cells m1 CH).
    { eapply (chain_cells_munch _ m m1 (bv_unsigned sp + 16) CH (ASTACK_TOP sp0)); [exact CC| exact CHOK| exact MU| lia| lia|].
      intros lo' hi' [E|[]]. injection E as E1 E2. subst lo' hi'. left. lia. }
    assert (SSZ1 : sh_zero m1 alloc_ceiling (2^47)).
    { eapply sh_zero_stack_munch; [exact SSZ| exact MU|]. constructor; [cbn [fst]; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| constructor]. }
    assert (HB16_1 : bv_unsigned sp + 16 <= PB -> pb_below m1 PB).
    { intros H16. eapply pb_below_munch; [exact (HB16 H16)| exact MU| cbn; lia]. }
    assert (HB8_1 : PB = bv_unsigned sp + 8 -> exists w : word, bytes_at bsegs m1 (bv_unsigned sp) (le8 w)).
    { intros H8. destruct (HB8 H8) as [w BW]. exists w. eapply bytes_at_transport; [exact BW| exact MU| rewrite length_le8; cbn; lia]. }
    assert (CHn1 : cj_chain CJ_PRINTABLE m1 n p B).
    { eapply cj_chain_frame; [exact CHn| exact MU| exact WM|]. intros A k Hin. cbn.
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia. }
    clear MU WM HL.
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (art_stkmalloc1 AI) with (lo := lo); rewrite ?unsigned_lit by lia;
        first [exact HL1 | exact ST | exact MI | exact ERR | exact TP | eapply lf_room_alloc; [exact LFR| lia] | unfold ASTKMALLOC_STACK; lia | lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 36%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 Fr fjunk fl -> MI2 ST2 ERR2 PR2 -> -> -> FAL FLO FHI FNEW FBLK HL2 FBODY FLP SHC)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x83fc4)) with (Z_to_bv 64 0x83fc4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold AERRNO, ATP in ERR2.
    change (fsz 1) with 128 in *. change (Z.to_nat (128 - 8)) with 120%nat in FBODY. clear FLP.
    change (shcells (repeat 0 (Z.to_nat (128 / 8)))) with (shcells [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]) in SHC. cbn [shcells map] in SHC.
    rewrite <- SH_shiftr in SHC. pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    try rewrite alloc_ceiling_eq in FHI. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (* [comment removed for export] *)
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in LOC; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in SAVW; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_stk _ _ _ _ _ _ _ _ PR2) in PAD; [| lia| lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in PS; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    assert (ARR2 : u8arr bsegs m2 buf bs).
    { destruct ARR as [BA WA]. split.
      - eapply cj_pres_bytes_at; [exact PR2| exact BA|]. do 3 right; left. exists buf, len. split; [eapply perm_in_head; exact HP| rewrite LEN; lia].
      - eapply cj_pres_wr_at; [exact PR2| exact WA|]. do 3 right; left. exists buf, len. split; [eapply perm_in_head; exact HP| rewrite LEN; lia]. }
    assert (PVA2 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m2).
    { eapply pv_agree_trans; [exact PVA1|]. eapply pv_agree_of_cj_pres; [exact PR2| lia| exact HLR]. }
    assert (CC2 : chain_cells m2 CH).
    { eapply (chain_cells_cj_pres sp0 _ _ SA m1 m2 (bv_unsigned sp + 16)); [exact CC1| exact CHOK| exact PR2| lia| lia| lia]. }
    assert (SSZ2 : sh_zero m2 alloc_ceiling (2^47)) by (eapply sh_zero_stack_cj_pres; [exact PR2| exact SSZ1]).
    assert (HB16_2 : bv_unsigned sp + 16 <= PB -> pb_below m2 PB).
    { intros H16. (nelim (HB16_1 H16) 4%nat; intros u1 u2 BY Hu). exists u1, u2. split; [| exact Hu].
      eapply cj_pres_bytes_at; [exact PR2| exact BY|]. left. rewrite length_app, !length_le8. cbn. lia. }
    assert (HB8_2 : PB = bv_unsigned sp + 8 -> exists w : word, bytes_at bsegs m2 (bv_unsigned sp) (le8 w)).
    { intros H8. destruct (HB8_1 H8) as [w BW]. exists w. eapply cj_pres_bytes_at; [exact PR2| exact BW|]. left. rewrite length_le8. cbn. lia. }
    assert (CHn2 : cj_chain CJ_PRINTABLE m2 n p B).
    { eapply cj_chain_pres; [exact CHn1| exact PR2| intros b Hb; apply HLR, BLR, Hb]. }
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in ND; [| do 3 right; left; exists p, 64; split; [exact PIN| cbn; lia]].
    clear PR2 HL1 PVA1 CC1 SSZ1 HB16_1 HB8_1 CHn1 MI ST ERR ARR.
    pose proof (FBLK p 64 PIN) as FDP. pose proof (FBLK buf len (perm_in_head _ _ _ HP)) as FDB.
    (* [comment removed for export] *)
    pose_blk_band HL2 PIN. pose proof (perm_in_head _ _ _ HP) as BIN. pose_blk_band HL2 BIN.
    pose proof (art_frame_sclr AI _ _ _ _ _ _ _ _ _ Fr 1 Fr 128 HL2 ltac:(left; reflexivity) ltac:(lia) ltac:(change (fsz 1) with 128; lia)) as FSC.
    unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in FSC.
    eapply lscps_step_evt. cbv beta delta [mkR]. unfold wz.
    zstep. zstep. zstep. if_cases Kf; zify_cond Kf; [| exfalso; lia].
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs m2 Fr [] 120 fjunk [] [24; 96]%nat) in FBODY; [| reflexivity].
    cbn [mk_CB_cells app] in FBODY.
    pose proof (munch_refl [(SA, SA + 72); (Fr, Fr + 24); (Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    zstep. do 9 zstep.
    zstep. sepM. fix_lit_store. zstep. fix_lit_store. zstep. fix_lit_store.
    zstep. zstep.
    sepM. do 4 sbstep. zstep. do 12 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LB ((Fr, 1) :: LF) TRS BB m3 mo g).
    { eapply (art_frame AI); [exact HL2| exact MU| exact WM|]. constructor; [| constructor; [| constructor; [| constructor]]].
      - right; left. cbn. try rewrite alloc_ceiling_eq. lia.
      - do 8 right. left. exists Fr, 1. cbn. split; [left; reflexivity|]. change (fsz 1) with 128. lia.
      - do 9 right. exists Fr, 1. cbn. split; [left; reflexivity|]. rewrite <- SH_shiftr. change (fsz 1) with 128. lia. }
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL3 ltac:(exact PIN)) as SOP.
    (* [comment removed for export] *)
    zstep. if_cases Kp; zify_cond Kp; [exfalso; lia|]. clear Kp.
    zstep. replace (Z.land p 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
    zstep. if_false.
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m3 p 64 (p + 24) 4 SOP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK4. sepM. asan_chk CK4.
    apply (pv_nodeB_of_node _ _ _ _ _ _ _ _ _ _ _ _ TY) in ND. unfold pv_nodeB, wz, wb in ND.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    set (Q := mkPVI AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LR B LF np BB CH n p PB len dep fw lo SA Fr).
    assert (PVLQ : pvl Q).
    { unfold pvl; cbn. try rewrite alloc_ceiling_eq. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, INT_MAX.
      repeat match goal with |- _ /\ _ => split end; first [assumption | exact PL | lia | idtac]. }
    all: try exact CHOK. all: try exact CHL. all: try exact CHB. all: try exact LFR. all: try exact FNEW. all: try exact CHn.
    assert (OWN3 : Forall (pv_own_iv Q) [(SA, SA + 72); (Fr, Fr + 24); (Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)]).
    { constructor; [| constructor; [| constructor; [| constructor]]]; unfold pv_own_iv; cbn; lia. }
    assert (CTX3 : PVX Q dep m3 mo g LB TRS BB np errv buf len off bs [w0; w1; w2; w3; w4; w5; w6; w7; Z_to_bv 64 Fr]
                       (firstn 96 (skipn 24 fjunk)) SHP_IDLE F fc).
    { split.
      - split; [exact HL3|]. split; [exact HP|]. split; [exact PS|].
        split; [first [exact ARR2 | eapply u8arr_transport; [exact ARR2| exact MU| exact WM| rewrite LEN; cbn; rewrite ?SHFR; lia]]|].
        split; [exact LEN|]. split; [exact PN|]. split; [exact ERR2|]. split; [exact MI2|].
        split; [eapply (pvm_agree_store Q PVLQ); [exact HL2| exact HLR| exact MU| exact WM| exact OWN3| exact PVA2]|].
        split. { eapply cj_chain_frame; [exact CHn2| exact MU| exact WM|]. intros A k Hin. cbn.
                 pose proof (HLR _ (BLR _ Hin)) as INA. pose_blk_band HL2 INA. pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2).   (* [comment removed for export] *)
                 pose proof (FBLK A k INA). sepM. lia. }
        split; [eapply (pvm_chain_cells_store Q PVLQ); [exact CC2| exact MU| exact OWN3]|].
        split; [eapply (pvm_sh_zero_store Q PVLQ); [exact SSZ2| exact MU| exact OWN3]|].
        destruct (pvm_below_store Q PVLQ _ _ _ HB16_2 HB8_2 MU OWN3) as [HB16_3 HB8_3].
        split; [exact HB16_3|]. split; [exact HB8_3|]. split; [apply gmono_refl|]. split; [exact TV|]. cbn. lia.
      - split; [exact SAVW|]. split; [exact LOC|]. split; [reflexivity|]. split; [exact PAD|]. split; [exact ST2|].
        destruct (rw_cells_app_split m3 Fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 81242); C8 (Z_to_bv 64 540488)] [CB 96 (firstn 96 (skipn 24 fjunk))] FBODY) as [HDR BODY].
        split; [exact HDR|]. split; [exact BODY|]. split; [exact SHC|]. split; [reflexivity|]. split; [exact FRM| apply FAG18_refl]. }
    clear MU WM.
    assert (RECQ : forall d, (d < q_n Q)%nat -> print_value_at AI TI d) by exact REC.
    destruct PT as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; rewrite <- E in *; zstep; if_false.
    sepM. all: zstep; zstep; zstep; zstep; step; zstep; step; apply evt_done; cbv beta.
    - eapply (CASE_F Q eq_refl eq_refl PVLQ RECQ). exact CTX3.
    - eapply (CASE_T Q eq_refl eq_refl PVLQ RECQ). exact CTX3.
    - eapply (CASE_N Q eq_refl eq_refl PVLQ RECQ). exact CTX3.
    - eapply (CASE_NUM Q eq_refl eq_refl PVLQ RECQ). exact CTX3.
    - eapply (CASE_STR Q eq_refl eq_refl PVLQ RECQ). exact CTX3.
    - eapply (CASE_ARR Q eq_refl eq_refl PVLQ RECQ). exact CTX3.
    - eapply (CASE_OBJ Q eq_refl eq_refl PVLQ RECQ). exact CTX3.
  Qed.
End PRO.


End CeilWrap.
End CJ_pv_pro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls.
Import CJ_pv_pro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma node_shb0 : forall (AI : art_iface) sp0 SPB LB LF TRS BB m mo g p off,
  ART AI sp0 SPB LB LF TRS BB m mo g -> In (p, 64) LB -> 0 <= off -> off + 8 <= 64 -> off mod 8 = 0 -> shb m (p + off) 0.
Proof.
  intros AI sp0 SPB LB LF TRS BB m mo g p off HL HIN H0 H1 H2.
  pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) as (_ & AL & _).
  pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) as SO.
  destruct (shadow_ok_shchk m p 64 (p + off) 8 SO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (v & SHB & [->|[C1 C2]]); [exact SHB|].
  exfalso. Z.div_mod_to_equations. lia.
Qed.

Section PVSTR.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Hypothesis PSTR : pstr_stmt AI TI.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.

  Theorem pv_str_case : pv_case_at PV_STR_ENTRY Q.
  Proof.
    unfold pv_case_at. intros until x31. intros [CTX FRX]. lits. unfold CASE_ST, PVPOST, PV_STR_ENTRY, ASHBASE, SHR.
    pose proof CTX as (HL & HP & PBS1 & ARR & LEN & PN & ERR & MI & PVA & CHN & CC & SSZ & HB16 & HB8 & GM & TV & L0 & HB & HNP).
    (* [comment removed for export] *)
    destruct (cj_chain_cons_inv _ _ _ _ _ CHN0 PNZ) as (d0 & nx & pv & ch & ty & p1 & vs & vi & p2 & vd & ky & Bv & Bk & Bcc & Bn & Ed & ND0 & TY & PT & SV & SK & CHC & CHN' & EB).
    assert (PINB : In (p, 64) B) by (rewrite EB; left; reflexivity).
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (PIN : In (p, 64) LB1) by (apply HLR, BLR, PINB).
    pose proof (pvm_node Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND0 (node_cells_size _ _ _ _ _ _ _ _ _ _) PINB) as ND.
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL PIN) as (P1 & P2 & _ & P4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in P1. try rewrite alloc_ceiling_eq in P4.
    unfold node_cells, wz in ND.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof (node_shb0 AI _ _ _ _ _ _ _ _ _ p 32 HL PIN ltac:(lia) ltac:(lia) ltac:(reflexivity)) as Z32. asan_chk Z32. clear Z32.
    zstep. zstep. zstep.
    change (Z_to_bv 64 551116) with (wz APSTR_ENTRY). apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_pstr Q PVL PSTR) with (Bv := Bv); [split; [exact CTX| exact FRX]| exact SV| | rewrite unsigned_lit by lia; lia].
      intros b Hb. rewrite EB. right. apply in_or_app. left. exact Hb. }
    cbv beta. intros ms2 mo2 g2 PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Fx' & fcx' & m2 & LB2 & TRS2 & B2 & np2 & errv2 & -> & OUT).
    replace (ret_pc (Z_to_bv 64 0x84708)) with (Z_to_bv 64 0x84708) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct OUT as [[-> EX] | (-> & buf' & len' & off' & bs' & [CTX2 FRX2] & NUL)].
    - pose proof EX as ((_ & _) & _ & _ & MI2 & _).
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done. cbv beta.
      eapply (pv_epi' Q PVL FLAGLOW). exact EX.
    - pose proof CTX2 as (HL2 & HP2 & PBS2 & ARR2 & LEN2 & PN2 & ERR2 & MI2 & PVA2 & CHN2 & CC2 & SSZ2 & _ & _ & GM2 & TV2 & L02 & HB2 & HNP2).
      eapply lscps_step_evt. cbv beta delta [mkR]. zstep. apply evt_done. cbv beta.
      eapply (pv_epi' Q PVL FLAGLOW).
      split; [exact FRX2|]. split; [exact HL2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact PVA2|]. split; [exact CHN2|].
      split; [exact CC2|]. split; [exact GM2|]. split; [exact TV2|].
      exists buf', len', off'. right. split; [reflexivity|]. split; [| split; [exact L02| split; [exact HB2| exact HNP2]]].
      exists bs'. split; [exact HP2|]. split; [exact PBS2|]. split; [split; [exact ARR2| exact LEN2]|]. split; [exact PN2| exact NUL].
  Qed.
End PVSTR.


End CeilWrap.
