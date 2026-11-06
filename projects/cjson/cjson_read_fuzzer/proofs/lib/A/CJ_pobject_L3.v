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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstring_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pstring_C.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstring_B.CJ_pstring_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstring_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
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
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

Section PSTR.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z).
  Hypothesis HPU : Permutation ((U, 64) :: LR) LB.
  Hypothesis HDn : In (D, n) LR /\ D <= CA /\ CA + blen <= D + n.
  Hypothesis LEN : Z.of_nat (length bs) = blen.
  Hypothesis BLEN : blen < 2^31.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PARSE_STRING_STACK.
  Hypothesis PLF : In (P - 32, 1) LF.
  Hypothesis PFR : AIMG_HI <= P - 32 /\ P - 32 + 128 <= alloc_ceiling /\ (P - 32) mod 128 = 0.
  Hypothesis UBND : sclr U 64.                  (* [comment removed for export] *)
  Hypothesis PBND : sclr (P - 32) 128.          (* [comment removed for export] *)
  Hypothesis SPF : 0 <= bv_unsigned sp /\ bv_unsigned sp <= SPB /\ SPB < 2^62 /\ bv_unsigned sp + 16 < ASTACK_TOP sp0 /\ sp0 <= 2^47
                   /\ ASTACK_BOTTOM sp0 <= lo /\ bv_unsigned sp mod 16 = 0.
  Hypothesis OFF : 0 <= off < blen.
  Hypothesis TP : tp = wz ATP.
  Hypothesis URNG : ablock_range U 64.
  Hypothesis DRNG : ablock_range D n.
  Hypothesis UD : U + 64 <= D \/ D + n <= U.
  (* [comment removed for export] *)
  Hypothesis PU : U + 64 + 16 <= P - 32 \/ P - 32 + 128 <= U - 16.
  Hypothesis PD : D + n + 16 <= P - 32 \/ P - 32 + 128 <= D - 16.
  Hypothesis BPRE : pstr_cost_pre (blen - off) <= B.
  Hypothesis STM : STAT TI PSTR_TR_MALLOC.
  Hypothesis STF : STAT TI PSTR_TR_FREE.

  Notation SP := (bv_unsigned sp).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation POST := (parse_string_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LR LF np B U P CA blen off depth bs D n lo m g
                      nx pv ch ty p1 vs vi p2 vd ky).
  (* [comment removed for export] *)
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition CST (pc : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 (Z_to_bv 64 (P + 16)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
            (S4 P) (S5 P) (Z_to_bv 64 2147450880) x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mm (seg_rom asegs).

  (* [comment removed for export] *)
  Definition MID (m1 : word -> option byte) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 : Z) (errv1 : word) : Prop :=
    ART AI sp0 SPB LB1 LF TRS1 B1 m1 mo1 g1 /\ bytes_at asegs m1 CA bs /\ rw_cells asegs m1 AERRNO [C4 errv1]
    /\ mem_inv asegs m1 /\ stk asegs m1 lo (SP + -144) /\ ppres sp0 LR LF SP P m m1 /\ gmono g g1 /\ TINV TI np TRS1 /\ pbuf_sh m1 P.

  (* [comment removed for export] *)
  Ltac steq := unfold CST, LST, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length]; first [lia | split; [lia| exact I]].
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold AMALLOC_STACK, PARSE_STRING_STACK; lia | sclr_tac2 ].
  (* [comment removed for export] *)
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; repeat f_equal; lia] end end.
  Ltac lits := (nelimp URNG 4%nat; intros U1 U2 U3 U4); (nelimp DRNG 4%nat; intros D1 D2 D3 D4); (nelimp PFR 3%nat; intros PF1 PF2 PF3); pose proof PBND as PBND'; pose proof UBND as UBND';
               (nelimp SPF 7%nat; intros SP1 SP2 SP3 SP4 SP5 SP6 SP7); pose proof CEIL as CEIL'; pose proof LO as LO';
               try rewrite alloc_ceiling_eq in U4, D4, PF2, CEIL'; unfold sclr, PARSE_STRING_STACK, AMALLOC_STACK, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *;
               pose proof (bv_unsigned_in_range 64 sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.

  (* [comment removed for export] *)
  Lemma fail0_tail : forall (i off1 : Z) m1 mo1 g1 LB1 TRS1 B1 errv1 (junk : list byte)
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 g1 LB1 TRS1 B1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells asegs m1 (SP + -144) (CB 40 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells asegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    off <= i <= blen -> B - pstr_fail_cost (blen - off) <= B1 ->
    LSCPS asegs POST (CST 0x860d0 x1 x5 x6 x7 (Z_to_bv 64 (CA + i)) x10 (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                          x18 x19 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HP1 FR PB ND Hi HB. lits. bandM. sepM.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells in PB. unfold CST, S4, S5. unfold AERRNO, ATP in ERR.
    pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND. unfold wz in PB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    eapply lscps_step_evt. cbv beta delta [mkR].
    pose proof (munch_refl [(P + 16, P + 24)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    pose proof (sh_zero_shb m1 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.       (* [comment removed for export] *)
    zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    do 13 zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    apply evt_done. apply lscps_done. unfold parse_string_post.
    nexists 15%nat. exists m2, 0, i, LB1, [], TRS1, B1, errv1.
    split; [reflexivity|]. split; [unfold wz; rewrite (zxb_zb 0) by lia; reflexivity|].
    split.
    { (* [comment removed for export] *) split; [eapply (art_pbuf_store AI); [exact HL| exact PLF| exact MU| exact WM| lia| lia]|].
      split; [exact HP1|]. split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|].
      split; [exact ST|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
      split; [eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]|].
      repeat split; try assumption; alia. }
    split. { eapply ppres_trans; [exact PR|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    split; [exact GM|].
    split. { unfold pbuf_at. eqcells PB. }
    split; [lia|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [eqcells ND| exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma pres_frame : forall LBx m1 m2 cs, cj_pres sp0 LBx LF (SP + -144) m1 m2 ->
    rw_cells asegs m1 (SP + -144) cs -> Z.of_nat (cells_size cs) = 144 -> rw_cells asegs m2 (SP + -144) cs.
  Proof. intros LBx m1 m2 cs PR2 FR Hsz. lits. bandM. sepM. eapply cj_pres_rw_cells; [exact PR2| exact FR|]. left. rewrite Hsz. pose proof (ASTACK_TOP_le sp0). lia. Qed.

  Lemma pres_pbuf : forall LBx m1 m2 c l o d, cj_pres sp0 LBx LF (SP + -144) m1 m2 ->
    pbuf_at m1 P c l o d -> pbuf_at m2 P c l o d.
  Proof.
    intros LBx m1 m2 c l o d PR2 PB. unfold pbuf_at in *. eapply cj_pres_rw_cells; [exact PR2| exact PB|].
    do 4 right. left. exists (P - 32), 1. split; [exact PLF|]. rewrite pbuf_cells_size. change (fsz 1) with 128. lia.
  Qed.

  Lemma pres_node : forall LBx m1 m2 cs, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> In (U, 64) LBx ->
    rw_cells asegs m1 U cs -> Z.of_nat (cells_size cs) = 64 -> rw_cells asegs m2 U cs.
  Proof. intros LBx m1 m2 cs PR2 HIn ND Hsz. eapply cj_pres_rw_cells; [exact PR2| exact ND|]. do 3 right. left. exists U, 64. rewrite Hsz. split; [exact HIn| lia]. Qed.

  Lemma pres_text : forall LBx m1 m2, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> In (D, n) LBx ->
    bytes_at asegs m1 CA bs -> bytes_at asegs m2 CA bs.
  Proof. intros LBx m1 m2 PR2 HIn BY. eapply cj_pres_bytes_at; [exact PR2| exact BY|]. do 3 right. left. exists D, n. rewrite LEN. split; [exact HIn| lia]. Qed.

  Lemma pres_pbuf_sh : forall LBx m1 m2, cj_pres sp0 LBx LF (SP + -144) m1 m2 -> (forall b, In b LR -> In b LBx) ->
    pbuf_sh m1 P -> pbuf_sh m2 P.
  Proof.
    intros LBx m1 m2 PR2 INL PSH. lits. bandM. sepM.
    apply (ppres_pbuf_sh sp0 LR LF SP P m1 m2); [| exact PSH| exact PLF| alia| alia| alia (* [comment removed for export] *)].
    eapply ppres_of_cj_pres; [exact PR2| lia| exact INL].
  Qed.

  (* [comment removed for export] *)
  Lemma dealloc_tail : forall (S k i off1 : Z) m1 mo1 g1 LB2 TRS1 B1 errv1 (junk : list byte)
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 g1 LB2 TRS1 B1 errv1 -> Permutation ((U, 64) :: (S, k) :: LR) LB2 ->
    rw_cells asegs m1 (SP + -144) (CB 24 junk :: C8 (Z_to_bv 64 U) :: C8 (Z_to_bv 64 P) :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells asegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    off <= i <= blen -> B - pstr_fail_cost (blen - off) <= B1 - cost_free ->
    LSCPS asegs POST (CST 0x860b0 x1 x5 x6 x7 (Z_to_bv 64 (CA + i)) (Z_to_bv 64 S) (Z_to_bv 64 P) x12 x13 x14 x15 x16 x17
                          x18 x19 x23 x24 x25 x26 x27 x28 x29 x30 x31 m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HP2 FR PB ND Hi HB. lits. bandM. sepM.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof PB as PB0. unfold pbuf_at, pbuf_cells in PB. unfold CST, S4, S5. unfold AERRNO, ATP in ERR.
    unfold wz in PB.
    assert (HP2' : Permutation ((S, k) :: (U, 64) :: LR) LB2) by (eapply Permutation_trans; [apply perm_swap| exact HP2]).
    (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ HB0 _).
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 40) PSH ltac:(lia)) as Z40. asan_chk Z40. clear Z40.
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { sepM. eapply (art_free_ok AI) with (lo := lo) (A := S) (n := k) (tl := []); rewrite ?unsigned_lit by lia;
        first [ exact HL | eapply perm_in_head; exact HP2' | exact ST | unfold AERRNO, ATP; exact ERR | exact MI | exact TP | reflexivity | alia
              | clear -HB BPRE OFF; unfold pstr_cost_pre, pstr_fail_cost, cost_free in *; lia
              | split; [lia| unfold PC0_FREE; lia]
              | apply uwt_hook_nonfp; lia
              | eapply (tinv_room TI); [exact TV| exact STF] ]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 HL2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x860cc)) with (Z_to_bv 64 0x860cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (perm_cb_remove _ _ _ _ HP2' (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HP1.
    assert (INL : forall b, In b LR -> In b (cb_remove S LB2)) by (intros b Hb; eapply Permutation_in; [exact HP1| right; exact Hb]).
    apply (pres_frame _ _ _ _ PR2) in FR; [| reflexivity].
    apply (pres_pbuf _ _ _ _ _ _ _ PR2) in PB0.
    apply (pres_node _ _ _ _ PR2 ltac:(eapply perm_in_head; exact HP1)) in ND; [| reflexivity].
    apply (pres_text _ _ _ PR2 ltac:(apply INL; apply (proj1 HDn))) in BY.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. apply evt_done.
    apply (rw_cells_merge asegs m2 _ [] [CB 24 junk; C8 (Z_to_bv 64 U); C8 (Z_to_bv 64 P)]) in FR.
    cbn [cells_size Cells.csize cells_bytes cbytes Nat.add app] in FR.
    eapply (fail0_tail i off1 m2 mo2 g2 (cb_remove S LB2) TRS2 (B1 - cost_free) errv1).
    - split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [eapply ppres_trans; [exact PR| eapply ppres_of_cj_pres; [exact PR2| lia| exact INL]]|].
      split; [eapply gmono_trans; [exact GM| exact GM2]|].
      split; [eapply (tinv_put TI); [exact TV| exact STF| rewrite unsigned_lit in TP2 by lia; exact TP2]|].
      eapply pres_pbuf_sh; [exact PR2| exact INL| exact PSH].
    - exact HP1.
    - exact FR.
    - exact PB0.
    - exact ND.
    - exact Hi.
    - exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma ok_tail : forall (S e oc off1 : Z) (buf junk : list byte) m1 mo1 g1 LB2 TRS1 B1 errv1
      x1 x5 x6 x7 x9 x12 x14 x15 x16 x17 x18 x24 x25 x26 x27 x28 x29 x30 x31,
    MID m1 mo1 g1 LB2 TRS1 B1 errv1 -> Permutation ((U, 64) :: (S, Z.of_nat (length buf)) :: LR) LB2 ->
    rw_cells asegs m1 (SP + -144) (CB 24 junk :: C8 (Z_to_bv 64 U) :: C8 (Z_to_bv 64 P) :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth ->
    rw_cells asegs m1 U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    u8arr asegs m1 S buf -> 0 <= oc < Z.of_nat (length buf) ->
    ablock_range S (Z.of_nat (length buf)) -> (U + 64 <= S \/ S + Z.of_nat (length buf) <= U) ->
    (D + n <= S \/ S + Z.of_nat (length buf) <= D) -> (S + Z.of_nat (length buf) + 16 <= P - 32 \/ P - 32 + 128 <= S - 16) ->
    off <= e < blen -> 1 <= Z.of_nat (length buf) <= e - off + 1 -> B1 = B - cost_malloc (Z.of_nat (length buf)) ->
    LSCPS asegs POST (CST 0x8604c x1 x5 x6 x7 x9 (Z_to_bv 64 S) (Z_to_bv 64 P) x12 (Z_to_bv 64 U) x14 x15 x16 x17
                          x18 (Z_to_bv 64 (S + oc)) (Z_to_bv 64 (CA + e)) x24 x25 x26 x27 x28 x29 x30 x31 m1) mo1 g1.
  Proof.
    intros until x31. intros (HL & BY & ERR & MI & ST & PR & GM & TV & PSH) HP2 FR PB ND BUF Hoc SRNG SU SD SPfr He Hk HB1.
    (nelim SRNG 4%nat; intros SR1 SR2 SR3 SR4). lits. bandM. sepM. try rewrite alloc_ceiling_eq in SR4.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB. unfold CST, S4, S5. unfold AERRNO, ATP in ERR.
    pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (HP2' : Permutation ((S, Z.of_nat (length buf)) :: (U, 64) :: LR) LB2) by (eapply Permutation_trans; [apply perm_swap| exact HP2]).
    assert (INS : In (S, Z.of_nat (length buf)) LB2) by (eapply perm_in_head; exact HP2').
    assert (INU : In (U, 64) LB2) by (eapply perm_in_head; exact HP2).
    assert (INLR : forall b, In b LR -> In b LB2) by (intros b Hb; eapply Permutation_in; [exact HP2| right; right; exact Hb]).
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INS) as SOS.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INU) as SOU.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(S + oc, S + oc + 1)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. pose proof (shadow_ok_shchk1 m1 S _ (S + oc) SOS ltac:(lia)) as CK. sepM. asan_chk CK.
    pose proof (u8arr_store_ok asegs _ _ _ oc (Z_to_bv 64 (S + oc)) BUF ltac:(lia) eq_refl) as SOK.
    zstep. rewrite le1_lit.
    pose proof (u8arr_write asegs _ _ _ oc (Z_to_bv 8 0) BUF ltac:(lia)) as BUF'. clear BUF. sepM. store_done. rename BUF' into BUF.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LB2 LF TRS1 B1 m2 mo1 g1) by (eapply (art_block_store AI); [exact HL| exact INS| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store AI); [exact HL| exact HP2'| intros b Hb; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
    sepM. assert (SOU2 : shadow_ok m2 U 64) by (eapply shadow_ok_high_store; [exact SOU| exact MU| lia| alia| lia| alia]).
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    clear MU WM SOS SOU.
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 40)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m2 U 64 (U + 24) 4 SOU2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK4. sepM. asan_chk CK4.
    zstep. zstep. fix_lit_store.
    zstep. zstep. zstep.
    pose proof (shadow_ok_shchk m2 U 64 (U + 32) 8 SOU2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK8. sepM. asan_chk CK8.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LB2 LF TRS1 B1 m3 mo1 g1) by (eapply (art_block_store AI); [exact HL2| exact INU| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres sp0 LR LF SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store AI); [exact HL2| exact HP2| intros b Hb; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    clear MU WM HL2 PR2 SOU2 PSH2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    pose proof (sh_zero_shb m3 P (P + 56) P PSH3 ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. zstep. zstep. zstep.
    pose proof (sh_zero_shb m3 P (P + 56) (P + 16) PSH3 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HL4 : ART AI sp0 SPB LB2 LF TRS1 B1 m4 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL3| exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR4 : ppres sp0 LR LF SP P m m4).
    { eapply ppres_trans; [exact PR3|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    assert (PSH4 : pbuf_sh m4 P) by (eapply pbuf_sh_high_store; [exact PSH3| exact MU| alia| alia| alia]).
    clear MU WM HL3 PR3 PSH3.
    do 13 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. apply lscps_done. unfold parse_string_post.
    nexists 15%nat. exists m4, 1, (e + 1), LB2, [(S, Z.of_nat (length buf))], TRS1, B1, errv1.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { split; [exact HL4|].
      split; [exact HP2|]. split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
      split; [exact PSH4|]. repeat split; try assumption; alia. }
    split; [exact PR4|]. split; [exact GM|].
    split. { unfold pbuf_at. eqcells PB. }
    split; [lia|]. right. split; [reflexivity|]. exists S, (Z.of_nat (length buf)). split; [reflexivity|]. split; [lia|].
    split; [eqcells ND|].
    split.
    { destruct (split_first_nul (upd buf (Z.to_nat oc) (Z_to_bv 8 0)) (Z.to_nat oc)) as (str & tail & E & NI). (* [comment removed for export] *)
      { apply nth_error_upd_same. lia. }
      eapply cj_str_intro; [lia| | exact NI|].
      - rewrite <- E. exact (proj1 BUF).
      - apply (f_equal (@length byte)) in E. rewrite upd_length, length_app in E. cbn [length] in E. lia. }
    split; [lia| exact HB1].
  Qed.

  (* [comment removed for export] *)
  Section Loop1.
    Variables (t3 t4 t5 t6 : word) (m1 : word -> option byte).

    Definition L1 (pc : Z) (x5 x6 x7 x13 x18 x23 x25 : word) : machine_state :=
      MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 (CA + off + 1)) (Z_to_bv 64 U) (Z_to_bv 64 P)
              (Z_to_bv 64 (CA + off)) x13 (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 92) (Z_to_bv 64 34)
              x18 s3 (S4 P) (S5 P) (Z_to_bv 64 2147450880) x23 s8 x25 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs).

    Definition Q1 : machine_state -> Prop := fun ms' =>
      (exists (q sk : Z) (x6 x7 : word),
          ms' = L1 0x85a6c (Z_to_bv 64 (Z.shiftr (CA + off + q) 3 + 2147450880)) x6 x7 (Z_to_bv 64 sk)
                   (Z_to_bv 64 (CA + off + q)) (Z_to_bv 64 (CA + off + q)) (Z_to_bv 64 q)
          /\ ps_scan bs blen (Z.to_nat blen) (off + 1) 0 = Some (off + q, sk) /\ 1 <= q /\ off + q < blen /\ 0 <= sk <= q)
      \/ (exists x5 x6 x7 x13 x18 x23 x25, ms' = L1 0x860d0 x5 x6 x7 x13 x18 x23 x25).

    Lemma loop1 : bytes_at asegs m1 CA bs -> mem_inv asegs m1 -> text_sh m1 CA blen ->
      forall (cnt : nat) (q sk : Z) (x5 x6 x7 x18 : word),
      Z.of_nat cnt = blen - (off + q) -> 1 <= q -> off + q < blen -> 0 <= sk <= q - 1 ->
      (forall r, ps_scan bs blen (Z.to_nat (blen - (off + q))) (off + q) sk = Some r ->
                 ps_scan bs blen (Z.to_nat blen) (off + 1) 0 = Some r) ->
      evt asegs Q1 (L1 0x85a18 x5 x6 x7 (Z_to_bv 64 sk) x18 (Z_to_bv 64 (CA + off + q)) (Z_to_bv 64 q)).
    Proof.
      intros BY1 MI1 TS1. induction cnt as [cnt IH] using lt_wf_ind.
      intros q sk x5 x6 x7 x18 Hcnt Hq Hoq Hsk K. lits. bandM. sepM. pose proof (bytes_at_bound _ _ _ _ BY1) as BYB. unfold L1, S4, S5.
      (nelim (text_read m1 CA bs (off + q) (Z_to_bv 64 (CA + off + q)) BY1 ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros b Hb RD Hat).
      pose proof (byte_range b) as Rb.
      assert (STEP : ps_scan bs blen (Z.to_nat (blen - (off + q))) (off + q) sk =
                     (if at_ bs (off + q) =? 34 then Some (off + q, sk)
                      else if at_ bs (off + q) =? 92 then (if blen <=? off + q + 1 then None else ps_scan bs blen (Z.to_nat (blen - (off + q + 1))) (off + q + 2) (sk + 1))
                      else ps_scan bs blen (Z.to_nat (blen - (off + q + 1))) (off + q + 1) sk)).
      { replace (Z.to_nat (blen - (off + q))) with (S (Z.to_nat (blen - (off + q + 1)))) by lia. apply ps_scan_step. lia. }
      rewrite Hat in STEP.
      zstep. zstep. zstep. pose proof (TS1 (CA + off + q) ltac:(lia)) as CK. sepM. asan_chk CK.
      zstep. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        zstep. if_cases Kq; zify_cond Kq.
        + (* [comment removed for export] *)
          apply evt_done. left. exists q, sk. eexists. eexists. split; [reflexivity|]. split; [| lia].
          apply K. rewrite STEP. rewrite (proj2 (Z.eqb_eq _ _) Kq). reflexivity.
        + zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
          { apply evt_done. right. nexists 7%nat. reflexivity. }
          replace (CA + off + (q + 1)) with (CA + off + (q + 1)) by lia.
          eapply (IH (cnt - 1)%nat ltac:(lia) (q + 1) sk); [lia| lia| lia| lia|].
          intros r Hr. apply K. rewrite STEP. rewrite (proj2 (Z.eqb_neq _ _) Kq), (proj2 (Z.eqb_neq _ _) Kbs).
          replace (off + (q + 1)) with (off + q + 1) in Hr by lia. exact Hr.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
        { apply evt_done. right. nexists 7%nat. reflexivity. }
        zstep. zstep. zstep. zstep. zstep. if_cases Ke2; zify_cond Ke2.
        + replace (CA + off + (q + 1 + 1)) with (CA + off + (q + 2)) by lia. replace (q + 1 + 1) with (q + 2) by lia.
          eapply (IH (cnt - 2)%nat ltac:(lia) (q + 2) (sk + 1)); [lia| lia| lia| lia|].
          intros r Hr. apply K. rewrite STEP, Kbs. change (92 =? 34) with false. change (92 =? 92) with true. cbv iota.
          replace (blen <=? off + q + 1) with false by (symmetry; apply Z.leb_gt; lia).
          eapply ps_scan_fuel; [| ]. { replace (off + q + 2) with (off + (q + 2)) by lia. exact Hr. } lia.
        + zstep. apply evt_done. right. nexists 7%nat. reflexivity.
    Qed.
  End Loop1.

  (* [comment removed for export] *)
  Lemma art_loop_fp : forall S na LB2 TRS1 B1 m3 mm mo1 g1,
    ART AI sp0 SPB LB2 LF TRS1 B1 m3 mo1 g1 -> In (S, na) LB2 ->
    munch [(S, S + na); (lo, SP + -144)] m3 mm -> wmono asegs m3 mm -> ART AI sp0 SPB LB2 LF TRS1 B1 mm mo1 g1.
  Proof.
    intros S na LB2 TRS1 B1 m3 mm mo1 g1 HL HIn MU WM. lits. bandM. eapply (art_frame AI); [exact HL| exact MU| exact WM|].
    constructor; [| constructor; [| constructor]].
    - do 7 right. left. exists S, na. cbn. split; [exact HIn| lia].
    - right; left. cbn. lia.
  Qed.

  Lemma ppres_loop_fp : forall S na R LB2 TRS1 B1 m3 mm mo1 g1,
    ART AI sp0 SPB LB2 LF TRS1 B1 m3 mo1 g1 -> Permutation ((S, na) :: R) LB2 -> (forall b, In b LR -> In b R) ->
    munch [(S, S + na); (lo, SP + -144)] m3 mm -> wmono asegs m3 mm -> ppres sp0 LR LF SP P m3 mm.
  Proof.
    intros S na R LB2 TRS1 B1 m3 mm mo1 g1 HL HP HLR MU WM a Ha nelH_; (nelim nelH_ 3%nat; intros Hc _ _). lits. bandM. sepM.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
    try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn.
    destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' (HLR _ Hin)) as [_ Dj].
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact (HLR _ Hin)])) 4%nat; intros Q1' _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia.
    - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 8%nat; intros Hk GAL HF1 HF2 _ _ _ HD).
      try rewrite alloc_ceiling_eq in HF2. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HF1. bandM. sepM.
      assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      destruct Hr as [Hr|Hr].
      + destruct (HD S na (perm_in_head _ _ _ HP)) as [Dd|Dd]; lia.
      + (* [comment removed for export] *)
        pose proof (frame_sh_in_band Fr k a Hk GAL ltac:(lia) HF2 Hr) as AB.
        pose proof (band_addr_not_block AI _ _ _ _ _ _ _ _ _ S na a HL (perm_in_head _ _ _ HP) AB) as NB. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in AB. bandM. sepM. clear - AB NB CEIL'. lia.
    - pose proof (stack_sh_in_band _ _ Hsh) as AB.
      pose proof (band_addr_not_block AI _ _ _ _ _ _ _ _ _ S na a HL (perm_in_head _ _ _ HP) AB) as NB. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in AB. bandM. sepM. clear - AB NB CEIL'. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem parse_string_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mo : Model) (TRS : list (list Z)) (errv : word),
    ART AI sp0 SPB LB LF TRS B m mo g -> TINV TI np TRS ->
    bytes_at asegs m CA bs -> rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m ->
    stk asegs m lo SP -> pbuf_sh m P ->
    rw_cells asegs m U (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> pbuf_at m P CA blen off depth ->
    a0 = wz U -> a1 = wz P ->
    LSCPS asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (wz PARSE_STRING) fc None m (seg_rom asegs)) mo g.
  Proof.
    intros until errv. intros HL TV BY ERR MI ST PSH ND PB A0 A1. lits. bandM. sepM.
    unfold wz in A0, A1. subst a0 a1. unfold PARSE_STRING, wz.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold AERRNO, ATP in ERR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SB.
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ (proj1 HDn)) ltac:(lia) ltac:(lia)) as TS.
    eapply lscps_step_evt.
    pose proof (munch_refl [(SP + -144, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SB as SB0. shbase_split SB0.
    zstep. carve_frame 144%nat ST. sepM. do 13 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HL1 : ART AI sp0 SPB LB LF TRS B m1 mo g) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (PR1 : ppres sp0 LR LF SP P m m1) by (eapply (ppres_frame_store AI); [exact HL| exact INLR| exact MU| exact WM| alia| lia| exact SP5]).
    assert (PSH1 : pbuf_sh m1 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    assert (TS1 : text_sh m1 CA blen) by (eapply text_sh_high_store; [exact TS| exact MU| alia| lia| alia]).
    clear MU WM HL PSH TS.
    Ltac mid HLx BYx ERRx MIx STx PRx TVx PSHx :=
      split; [exact HLx|]; split; [exact BYx|]; split; [unfold AERRNO, ATP; exact ERRx|]; split; [exact MIx|];
      split; [exact STx|]; split; [exact PRx|]; split; [apply gmono_refl|]; split; [exact TVx| exact PSHx].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) P PSH1 ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH1 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    pose proof (TS1 (CA + off) ltac:(lia)) as CK. sepM. asan_chk CK.
    (nelim (text_read m1 CA bs off (Z_to_bv 64 (CA + off)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b0 Hb0 RD0 Hat0).
    pose proof (byte_range b0) as Rb0.
    zstep. zstep. zstep. zstep. if_cases K34; zify_cond K34.
    { replace (CA + off + 1) with (CA + (off + 1)) by lia. apply evt_done.
      eapply (fail0_tail (off + 1) off m1 mo g LB TRS B errv); [mid HL1 BY ERR MI ST PR1 TV PSH1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia
        | clear -BPRE OFF; unfold pstr_cost_pre, pstr_fail_cost, cost_free in *; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 8) PSH1 ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { replace (CA + off + 1) with (CA + (off + 1)) by lia. apply evt_done.
      eapply (fail0_tail (off + 1) off m1 mo g LB TRS B errv); [mid HL1 BY ERR MI ST PR1 TV PSH1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia
        | clear -BPRE OFF; unfold pstr_cost_pre, pstr_fail_cost, cost_free in *; lia]. }
    do 6 zstep.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (loop1 t3 t4 t5 t6 m1 BY MI TS1 (Z.to_nat (blen - (off + 1))) 1 0); [lia| lia| lia| lia|].
      intros r Hr. eapply ps_scan_fuel; [exact Hr| lia]. }
    intros ms' [(q & sk & x6 & x7 & -> & SCAN & Hq & Hoq & Hsk) | (x5 & x6' & x7' & x13 & x18 & x23 & x25 & ->)]; unfold L1.
    2:{ replace (CA + off + 1) with (CA + (off + 1)) by lia. apply evt_done.
        eapply (fail0_tail (off + 1) off m1 mo g LB TRS B errv); [mid HL1 BY ERR MI ST PR1 TV PSH1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| lia
          | clear -BPRE OFF; unfold pstr_cost_pre, pstr_fail_cost, cost_free in *; lia]. }
    (* [comment removed for export] *)
    (nelimp (ps_scan_npairs _ _ _ _ _ _ _ SCAN) 3%nat; intros SKE _ AT34).
    pose proof (npairs_window bs blen (Z.to_nat blen) (off + 1) (off + 1) (off + q) ltac:(lia)) as [Wa Wb].
    rewrite (npairs_le bs blen _ (off + 1) (off + 1)) in Wa, Wb by lia. pose proof (bflag_range bs (off + 1)) as BF.
    unfold S4, S5. cbv beta delta [mkR].
    pose proof (TS1 (CA + off + q) ltac:(lia)) as CKq. sepM. asan_chk CKq.
    (nelim (text_read m1 CA bs (off + q) (Z_to_bv 64 (CA + off + q)) BY ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) 4%nat; intros bq Hbq RDq Hatq).
    zstep. zstep. zstep. if_cases Kq34; zify_cond Kq34; [exfalso; lia|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(SP + -120, SP + -104)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1a end.
    assert (HL1a : ART AI sp0 SPB LB LF TRS B m1a mo g) by (eapply (art_frame_store AI); [exact HL1| exact MU| exact WM| alia| alia]).
    assert (PR1a : ppres sp0 LR LF SP P m m1a).
    { eapply ppres_trans; [exact PR1|]. eapply (ppres_frame_store AI); [exact HL1| exact INLR| exact MU| exact WM| alia| lia| exact SP5]. }
    assert (PSH1a : pbuf_sh m1a P) by (eapply pbuf_sh_high_store; [exact PSH1| exact MU| alia| alia| alia]).
    assert (TS1a : text_sh m1a CA blen) by (eapply text_sh_high_store; [exact TS1| exact MU| alia| lia| alia]).
    clear MU WM HL1 PR1 PSH1 TS1.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m1a P (P + 56) (P + 32) PSH1a ltac:(lia)) as Z32. asan_chk Z32. clear Z32.
    zstep. zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 AMALLOC)) with (wz AMALLOC) by (unfold wz, AMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL1a) 4%nat; intros _ _ HB0 _).
    eapply lscps_bind.
    { sepM. eapply (art_malloc_ok AI) with (lo := lo) (n := off + q - off - sk + 1) (tl := []); rewrite ?unsigned_lit by lia;
        first [ exact HL1a | exact ST | unfold AERRNO, ATP; exact ERR | exact MI | exact TP | unfold wz; f_equal; lia | alia
              | clear -BPRE OFF Hq Hoq Hsk SKE Wa Wb BF; unfold pstr_cost_pre, pstr_fail_cost, cost_free in *;
                pose proof (RT_cost.cost_malloc_lin (off + q - off - sk + 1) ltac:(lia)); lia
              | split; [lia| unfold PC0_MALLOC; lia]
              | apply uwt_hook_nonfp; lia
              | eapply (tinv_room TI); [exact TV| exact STM] ]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 26%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 RES)
.
    rewrite ?unsigned_lit in ST2, PR2, TP2 by lia.
    replace (ret_pc (Z_to_bv 64 0x85ab0)) with (Z_to_bv 64 0x85ab0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    apply (pres_frame _ _ _ _ PR2) in FR; [| reflexivity].
    assert (PB1 : pbuf_at m2 P CA blen off depth) by (eapply (pres_pbuf _ _ _ _ _ _ _ PR2); unfold pbuf_at; eqcells PB).
    apply (pres_node _ _ _ _ PR2 ltac:(eapply perm_in_head; exact HPU)) in ND; [| reflexivity].
    apply (pres_text _ _ _ PR2 ltac:(apply INLR; apply (proj1 HDn))) in BY.
    assert (TV2 : TINV TI np TRS2) by (eapply (tinv_put_or TI); [exact TV| exact STM| exact TP2]).
    assert (PR3 : ppres sp0 LR LF SP P m m2) by (eapply ppres_trans; [exact PR1a| eapply ppres_of_cj_pres; [exact PR2| lia| exact INLR]]).
    assert (PSH2 : pbuf_sh m2 P) by (eapply pres_pbuf_sh; [exact PR2| exact INLR| exact PSH1a]).
    clear PR1a PR2 MI ST HL1a ERR TS1a PSH1a PB. unfold pbuf_at, pbuf_cells, wz in PB1. unfold AERRNO, ATP in ERR2.
    destruct RES as [[-> HL2] | (A & jk & -> & ARNG & ANEW & AFR & HL2 & BLK & FILL)].
    - (* [comment removed for export] *)
      eapply lscps_step_evt. cbv beta delta [mkR].
      unfold wz. zstep. if_true. zstep. replace (CA + off + 1) with (CA + (off + 1)) by lia. apply evt_done.
      apply (rw_cells_merge asegs m2 _ [] [CB 24 _; C8 (Z_to_bv 64 U); C8 (Z_to_bv 64 P)]) in FR.
      cbn [cells_size Cells.csize cells_bytes cbytes Nat.add app] in FR.
      eapply (fail0_tail (off + 1) off m2 mo2 g2 LB TRS2 (B - cost_malloc (off + q - off - sk + 1)) errv2);
        [| exact HPU| exact FR| unfold pbuf_at; eqcells PB1| eqcells ND| lia
         | clear -BPRE OFF Hq Hoq Hsk SKE Wa Wb BF; unfold pstr_cost_pre, pstr_fail_cost, cost_free in *;
           pose proof (RT_cost.cost_malloc_lin (off + q - off - sk + 1) ltac:(lia)); lia].
      split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [exact PR3|]. split; [eapply gmono_trans; [apply gmono_refl| exact GM2]|]. split; [exact TV2| exact PSH2].
    - (* [comment removed for export] *)
      (nelimp ARNG 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
      set (na := off + q - off - sk + 1) in *.
      assert (HP2 : Permutation ((U, 64) :: (A, na) :: LR) ((A, na) :: LB)).
      { eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. exact HPU. }
      assert (INU2 : In (U, 64) ((A, na) :: LB)) by (right; eapply perm_in_head; exact HPU).
      assert (IND2 : In (D, n) ((A, na) :: LB)) by (right; apply INLR; apply (proj1 HDn)).
      assert (AU : U + 64 <= A \/ A + na <= U).
      { destruct (art_blocks_disjoint AI _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 INU2 ltac:(left; reflexivity)) as [?|?]; [| lia| lia].
        intros ->. apply ANEW. apply (in_map fst) with (x := (A, 64)). eapply perm_in_head; exact HPU. }
      assert (AD : D + n <= A \/ A + na <= D).
      { destruct (art_blocks_disjoint AI _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 IND2 ltac:(left; reflexivity)) as [?|?]; [| lia| lia].
        intros ->. apply ANEW. apply (in_map fst) with (x := (A, n)). apply INLR, (proj1 HDn). }
      assert (APF : A + na + 16 <= P - 32 \/ P - 32 + 128 <= A - 16).
      { (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL2 PLF) 8%nat; intros _ _ _ _ _ _ _ HD').
        destruct (HD' A na ltac:(left; reflexivity)); [left| right]; change (fsz 1) with 128 in *; lia. }
      assert (LJ : length jk = Z.to_nat na) by (destruct BLK as [[Hwf _] _]; cbn in Hwf; lia).
      pose proof (u8arr_of_rw_cells asegs m2 A _ jk BLK) as BUF.
      eapply lscps_step_evt. cbv beta delta [mkR].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      zstep. zstep. zstep. zstep. zstep. rewrite (bv_lts_small q 2) by lia. if_cases Kq; zify_cond Kq.
      + (* [comment removed for export] *)
        apply evt_done.
        eapply lscps_eq; [| eapply (ok_tail A (off + q) 0 off jk _ m2 mo2 g2 ((A, na) :: LB) TRS2 (B - cost_malloc na) errv2)].
        { steq. }
        * split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
          split; [exact PR3|]. split; [eapply gmono_trans; [apply gmono_refl| exact GM2]|]. split; [exact TV2| exact PSH2].
        * replace (Z.of_nat (length jk)) with na by lia. exact HP2.
        * exact FR.
        * unfold pbuf_at; eqcells PB1.
        * eqcells ND.
        * exact BUF.
        * lia.
        * replace (Z.of_nat (length jk)) with na by lia. exact ARNG.
        * lia.
        * lia.
        * lia.
        * subst na; lia.
        * subst na; lia.
        * replace (Z.of_nat (length jk)) with na by lia; reflexivity.
      + (* [comment removed for export] *)
        pose proof (munch_refl [(SP + -136, SP + -120)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        do 13 zstep. zstep. sepM. fix_lit_store. zstep. zstep. fix_lit_store.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        assert (HL3 : ART AI sp0 SPB ((A, na) :: LB) LF TRS2 (B - cost_malloc na) m3 mo2 g2)
          by (eapply (art_frame_store AI); [exact HL2| exact MU| exact WM| alia| alia]).
        assert (PR4 : ppres sp0 LR LF SP P m m3).
        { eapply ppres_trans; [exact PR3|]. eapply (ppres_frame_store AI); [exact HL2| | exact MU| exact WM| alia| lia| exact SP5].
          intros b Hb. right. apply INLR. exact Hb. }
        assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
        pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL3) as SB3.
        pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL3 IND2 ltac:(lia) ltac:(lia)) as TS3.
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL3 ltac:(left; reflexivity)) as SO3.
        clear MU WM HL2 PR3 PSH2.
        zstep. zstep.
        (* [comment removed for export] *)
        lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: C8 ?v1 :: C8 ?v2 :: _) =>
          replace v1 with (Z_to_bv 64 0xdc00) in FR by (apply bv_eq; vm_compute; reflexivity);
          replace v2 with (Z_to_bv 64 0xd800) in FR by (apply bv_eq; vm_compute; reflexivity);
          remember j as j0 eqn:Ej0 in FR; clear Ej0 end.
        assert (CTX : ps_ctx sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m3 CA blen off (off + q) sk A P U lo bs j0).
        { split; [exact LEN|]. split; [exact BY|]. split; [exact FR|]. split; [exact SCAN|]. split; [lia|]. split; [exact BLEN|].
          split; [lia|]. split; [alia|]. split; [alia|]. unfold nalloc. split; [alia|]. split; [lia|]. split; [alia|]. split; [lia|]. split; [lia|].
          split; [alia|]. split; [alia|]. split; [alia|]. split; [alia|]. split; [exact SB3|]. split; [exact TS3|]. split; [exact SO3|]. sclr_tac2 (* [comment removed for export] *). }
        eapply evt_cut.
        { eapply evt_eq.
          2:{ pose proof (dec_loop sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc m3 CA blen off (off + q) sk A P U lo bs j0 CTX (Z.to_nat (off + q - (off + 1)))) as DL.
              unfold LOOPK in DL. eapply (DL (off + 1) 0 m3 jk); [lia| lia| eapply dinv0; exact CTX| lia|].
              split; [exact BUF|]. split; [unfold nalloc; exact LJ|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI2| exact ST2]. }
          steq. }
        intros ms' KP.
        (nelim KP 20%nat; intros mm buf y5 y6 y7 y12 y13 y14 y15 y16 y17 y25 y28 i oc LMm Hi Hoc ROOM [-> | ->]);
          unfold LST; (nelimp LMm 6%nat; intros BUFm BLm MUm WMm MIm STm); unfold W2, nalloc in MUm, BLm, ROOM.
        * (* [comment removed for export] *)
          apply evt_done.
          pose proof FR as FRm. eapply rw_cells_transport in FRm; [| exact MUm| exact WMm| dj].
          apply (rw_cells_merge asegs mm (SP + -144) [] [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800)]) in FRm.
          cbn [app cells_size cells_bytes Cells.csize cbytes Nat.add] in FRm.
          pose proof PB1 as PBm. eapply rw_cells_transport in PBm; [| exact MUm| exact WMm| dj].
          pose proof ND as NDm. eapply rw_cells_transport in NDm; [| exact MUm| exact WMm| dj].
          pose proof ERR2 as ERRm. eapply rw_cells_transport in ERRm; [| exact MUm| exact WMm| dj].
          pose proof BY as BYm. sepM. eapply bytes_at_transport in BYm; [| exact MUm| rewrite LEN; dj].
          unfold S4, S5.
          eapply (ok_tail A (off + q) oc off buf _ mm mo2 g2 ((A, na) :: LB) TRS2 (B - cost_malloc na) errv2).
          -- split. { eapply (art_loop_fp A na); [exact HL3| left; reflexivity| exact MUm| exact WMm]. }
             split; [exact BYm|]. split; [exact ERRm|]. split; [exact MIm|]. split; [exact STm|].
             split. { eapply ppres_trans; [exact PR4|]. eapply (ppres_loop_fp A na); [exact HL3| apply perm_skip; exact HPU| intros b Hb; right; exact Hb| exact MUm| exact WMm]. }
             split; [eapply gmono_trans; [apply gmono_refl| exact GM2]|]. split; [exact TV2|].
             sepM. eapply pbuf_sh_munch; [exact PSH3| exact MUm| alia| alia| pbuf_dj (* [comment removed for export] *)].
          -- replace (Z.of_nat (length buf)) with na by lia. exact HP2.
          -- exact FRm.
          -- unfold pbuf_at; eqcells PBm.
          -- eqcells NDm.
          -- exact BUFm.
          -- lia.
          -- replace (Z.of_nat (length buf)) with na by lia. exact ARNG.
          -- lia.
          -- lia.
          -- lia.
          -- subst na; lia.
          -- subst na; lia.
          -- replace (Z.of_nat (length buf)) with na by lia; reflexivity.
        * (* [comment removed for export] *)
          apply evt_done.
          pose proof FR as FRm. eapply rw_cells_transport in FRm; [| exact MUm| exact WMm| dj].
          apply (rw_cells_merge asegs mm (SP + -144) [] [CB 8 j0; C8 (Z_to_bv 64 0xdc00); C8 (Z_to_bv 64 0xd800)]) in FRm.
          cbn [app cells_size cells_bytes Cells.csize cbytes Nat.add] in FRm.
          pose proof PB1 as PBm. eapply rw_cells_transport in PBm; [| exact MUm| exact WMm| dj].
          pose proof ND as NDm. eapply rw_cells_transport in NDm; [| exact MUm| exact WMm| dj].
          pose proof ERR2 as ERRm. eapply rw_cells_transport in ERRm; [| exact MUm| exact WMm| dj].
          pose proof BY as BYm. eapply bytes_at_transport in BYm; [| exact MUm| rewrite LEN; dj].
          unfold S4, S5.
          eapply (dealloc_tail A na i off mm mo2 g2 ((A, na) :: LB) TRS2 (B - cost_malloc na) errv2).
          -- split. { eapply (art_loop_fp A na); [exact HL3| left; reflexivity| exact MUm| exact WMm]. }
             split; [exact BYm|]. split; [exact ERRm|]. split; [exact MIm|]. split; [exact STm|].
             split. { eapply ppres_trans; [exact PR4|]. eapply (ppres_loop_fp A na); [exact HL3| apply perm_skip; exact HPU| intros b Hb; right; exact Hb| exact MUm| exact WMm]. }
             split; [eapply gmono_trans; [apply gmono_refl| exact GM2]|]. split; [exact TV2|].
             sepM. eapply pbuf_sh_munch; [exact PSH3| exact MUm| alia| alia| pbuf_dj (* [comment removed for export] *)].
          -- exact HP2.
          -- exact FRm.
          -- unfold pbuf_at; eqcells PBm.
          -- eqcells NDm.
          -- lia.
          -- clear -BPRE OFF Hq Hoq Hsk SKE Wa Wb BF; subst na; unfold pstr_cost_pre, pstr_fail_cost, cost_free in *;
             pose proof (RT_cost.cost_malloc_lin (off + q - off - sk + 1) ltac:(lia)); lia.
  Qed.
End PSTR.

Theorem parse_string_spec : forall AI TI, parse_string_stmt AI TI.
Proof.
  intros AI TI. unfold parse_string_stmt. intros until ky.
  intros (HL & HPU & HD & DCA & CAD & BY & LEN & BLEN & ERR & MI & ST & CEIL & TV & PLF & PSH & SP1 & SP2 & SP3 & SP4 & SP5 & SP6 & SP7) ND PB OFF LO TP A0 A1 STM STF BPRE.
  assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
  assert (IND : In (D, n) LB) by (eapply Permutation_in; [exact HPU| right; exact HD]).
  assert (UD : U <> D).
  { intros ->. pose proof (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL)) as NDP.
    apply (NoDup_map_fst_perm _ _ (Permutation_sym HPU)) in NDP. rewrite NoDup_ListNoDup in NDP. cbn in NDP.
    inversion NDP; subst. apply H1. apply (in_map fst) in HD. exact HD. }
  (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL PLF) 8%nat; intros _ FAL FLO FHI _ _ _ FD). change (fsz 1) with 128 in *.
  pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ U 64 U 64 HL INU ltac:(lia) ltac:(lia)) as UBND.   (* [comment removed for export] *)
  pose proof (art_frame_sclr AI _ _ _ _ _ _ _ _ _ (P - 32) 1 (P - 32) 128 HL PLF ltac:(lia) ltac:(change (fsz 1) with 128; lia)) as PBND.   (* [comment removed for export] *)
  eapply parse_string_main; try eassumption.
  - split; [exact HD| split; [exact DCA| exact CAD]].
  - split; [exact FLO|]. split; [exact FHI| exact FAL].
  - repeat split; assumption.
  - eapply (art_block_range AI); [exact HL| exact INU].
  - eapply (art_block_range AI); [exact HL| exact IND].
  - destruct (art_blocks_disjoint AI _ _ _ _ _ _ _ _ _ _ _ _ _ HL INU IND UD); lia.
  - destruct (FD U 64 INU); lia.
  - destruct (FD D n IND); lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
End CJ_pstring_C.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pobject_L1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
Module CJ_pobject_L2.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas CJ_pstring_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pobject_L1.CJ_pobject_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pobject_L1.CJ_pobject_ws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pobject_L1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

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
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section POL.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (POBJ_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis DEL : cjson_delete_stmt AI TI.
  Hypothesis SDEL : Forall (STAT TI) S_DELETE.
  Hypothesis SCONST : Forall (STAT TI) S_PARSE_CONST.
  Hypothesis SPV : forall b, STAT TI (tr_pv_pobj b).
  Hypothesis LFR : lf_room 2 LF (1000 - depth).
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at AI TI nf.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B [] U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDO AI TI sp m g sp0 SPB LR LF np P CA bs lo).
  Notation SAVED := (SAVEDO ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation OFR := (OFRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P).
  Notation dch := (dch depth).
  Notation OLOOPc := (OLOOP AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LR LF np B U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation WSM := (ws_mem P CA blen bs).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & HDn & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold POBJ_STACK, PARSE_STACK in LO.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac steq := unfold CSTO, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  (* [comment removed for export] *)
  Ltac blia := unfold pv_cost_pre, PV_FRATE, PV_RATE, cost_free in *; rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.

  Notation FAILO7 := (fail_o7 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation FAILO4 := (fail_o4 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation FAILO := (fail_o AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation RET0O := (ret0_o AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC).
  Notation OBJCLOSE := (obj_close AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC).
  Notation PRES_FRAME := (pres_frame sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_PBUF := (pres_pbuf sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_TEXT := (pres_text sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_PSH := (pres_pbuf_sh sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).

  Notation KEY_DONE := (key_done AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL SCONST SPV LFR nfuel FUEL PVREC).

  (* [comment removed for export] *)
  Lemma after_key : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o1 hd A : Z) (pvA : word) (X : list cblock) (r off2 : Z) (X2 : list cblock)
           m1 mo1 g1 LBX TRS1 (B2 B3 : Z) errv1 Fx fcx (j0 : list byte)
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o1 -> depth <= 999 ->
      MID m1 mo1 g1 LBX TRS1 B3 errv1 -> Permutation ((A, 64) :: X2 ++ (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells asegs m1 (SP + -144) (OFR j0) ->
      pbuf_at m1 P CA blen off2 (depth + 1) -> o1 <= off2 <= blen ->
      rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o + 1 - off) + 192 <= B2 -> Z.of_nat (length X) + 1 <= o + 1 - off ->
      ( (r = 0 /\ X2 = [] /\ rw_cells asegs m1 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0)
          /\ B2 - pstr_fail_cost (blen - o1) <= B3)
        \/ (r = 1 /\ exists (KS k : Z), X2 = [(KS, k)] /\ KS <> 0
              /\ rw_cells asegs m1 A (node_cells 0 pvA 0 16 (wz 0) KS (wz 0) (wz 0) (wz 0) 0)
              /\ cj_str m1 KS [(KS, k)] /\ 1 <= k <= off2 - o1 /\ B3 = B2 - cost_malloc k) ) ->
      LSCPS asegs POST (CST 0x86568 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                             (Z_to_bv 64 (P + 8)) (Z_to_bv 64 32) (Z_to_bv 64 A) (Z_to_bv 64 P) (SHR P) (Z_to_bv 64 hd)
                             (SHR (P + 16)) (SHR (P + 24)) (SHR (P + 8)) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho1 Hd MIDm HPX HNZ ANZ SEG FR PB Ho2 ND FA FRM HB HX RES. lits. bandM. sepM. unfold CSTO, SHR.
    (nelimp MIDm 9%nat; intros HL BY ERR MI ST PR GM TV PSH).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; left; exact Hb]).
    assert (INA : In (A, 64) LBX) by (eapply perm_in_head; exact HPX).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INA) 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
    pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL PLF) as BHA. destruct (BHA A 64 INA) as [_ APd].
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ (proj1 HDn)) ltac:(lia) ltac:(lia)) as TS.
    pose proof (OFRAME_fold ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P m1 j0 FR) as FR40.
    eapply lscps_step_evt. cbv beta delta [mkR].
    destruct RES as [(-> & -> & NDA & HB3) | (-> & KS & k & -> & KNZ & NDA & SK & Hk & HB3)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CH : cj_chain CJ_ANY m1 (S dch) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply FAILO7; [exact MIDm| | exact CH| unfold CJ_pvalue_lemmas.dch; lia| exact FR40| exact PB| exact ND| exact FA| exact FRM
        | clear -HB HX HB3 Ho Ho1 Ho2 BPRE OFF; unfold pstr_fail_cost in *; blia].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR).
    - (* [comment removed for export] *)
      clear FR40.
      pose proof (rw_cells_bound asegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; left; reflexivity]).
      pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold AERRNO, ATP in ERR. unfold OFRAME, SAVEDO, SHR in FR.
      pose proof (RT_cost.cost_malloc_lin k ltac:(lia)) as CMK.
      assert (HB3' : B - PV_RATE * (off2 - off) <= B3) by (clear -HB HB3 Hk CMK Ho1 Ho2; unfold PV_RATE in *; lia).
      zstep. if_false.
      pose proof (sh_zero_shb m1 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
      zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
      pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      pose proof (sh_zero_shb m1 P (P + 56) (P + 8) PSH ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
      zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
      + (* [comment removed for export] *)
        apply evt_done.
        eapply (KEY_DONE c IHc o off2 hd A KS k pvA X m1 mo1 g1 LBX TRS1 B3 errv1);
          [exact Hc| exact Ho| lia| exact Hd| exact MIDm| exact HPX| exact HNZ| exact ANZ| exact SEG| exact SK| eqcells NDA
          | unfold OFRAME, SAVEDO, SHR; exact FR| exact PB'| eqcells ND| exact FA| exact FRM| exact HB3'| lia].
      + pose proof (fin_off0 P blen off2 bs LEN ltac:(lia)) as FO.
        eapply evt_cut.
        { eapply (ws3 sp gp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC m1 TS PSH (Z.to_nat (blen - off2)) off2 (depth + 1) m1);
            [lia| lia| exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
        intros ms' nelH_; (nelim nelH_ 12%nat; intros x10' x11' x14' x15' x16' m2 -> PB2 BY2 MI2 MU2 WM2). unfold CSTO, SHR. rewrite <- FO in PB2.
        trc FR MU2 WM2. trc ND MU2 WM2. trc NDA MU2 WM2. trc ERR MU2 WM2. trc ST MU2 WM2.
        assert (HL2 : ART AI sp0 SPB LBX LF TRS1 B3 m2 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL| exact PLF| exact MU2| exact WM2| lia| lia]).
        assert (PR2 : ppres sp0 LR LF SP P m m2).
        { eapply ppres_trans; [exact PR|]. eapply ppres_pbuf_store; [exact MU2| exact WM2| lia| lia]. }
        assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU2| alia| alia| alia]).
        assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
        { intros A' k' Hin. cbn. split; [|exact I]. destruct (BHA A' k' Hin). lia. }
        assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
        { eapply cj_lseg_frame; [exact SEG| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
        assert (SK2 : cj_str m2 KS [(KS, k)]).
        { eapply cj_str_frame; [exact SK| exact MU2| exact WM2|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
        pose proof (skipws_off_range bs off2 ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
        apply evt_done.
        eapply (KEY_DONE c IHc o (skipws_off bs off2) hd A KS k pvA X m2 mo1 g1 LBX TRS1 B3 errv1);
          [exact Hc| exact Ho| lia| exact Hd| | exact HPX| exact HNZ| exact ANZ| exact SEG2| exact SK2| eqcells NDA
          | unfold OFRAME, SAVEDO, SHR; exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM| clear -HB3' OR; unfold PV_RATE in *; lia| lia].
        split; [exact HL2|]. split; [exact BY2|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI2|]. split; [exact ST|].
        split; [exact PR2|]. split; [exact GM|]. split; [exact TV| exact PSH2].
  Qed.

  (* [comment removed for export] *)
  Lemma sconst_stats : STAT TI [PC0_MALLOC; 0x86478] /\ STAT TI PSTR_TR_MALLOC /\ STAT TI PSTR_TR_FREE.
  Proof.
    pose proof SCONST as SC. unfold S_PARSE_CONST in SC.
    apply Forall_cons_iff in SC. destruct SC as [S1 SC]. apply Forall_cons_iff in SC. destruct SC as [S2 SC]. apply Forall_cons_iff in SC. destruct SC as [S3 _].
    split; [exact S1|]. split; [exact S2| exact S3].
  Qed.

  (* [comment removed for export] *)
  Lemma do_key : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o hd A : Z) (pvA : word) (X : list cblock) m2 mo2 g2 LBX2 TRS2 B2 errv2 Fx fcx (j0 : list byte)
           x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x22 x23 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MID m2 mo2 g2 LBX2 TRS2 B2 errv2 -> Permutation ((A, 64) :: (U, 64) :: X ++ LR) LBX2 ->
      hd <> 0 ->
      cj_lseg CJ_PRINTABLE m2 dch hd A X ->
      rw_cells asegs m2 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) ->
      rw_cells asegs m2 (SP + -144) (OFR j0) ->
      pbuf_at m2 P CA blen o (depth + 1) ->
      rw_cells asegs m2 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o + 1 - off) + 192 <= B2 -> Z.of_nat (length X) + 1 <= o + 1 - off ->
      LSCPS asegs POST (CST 0x864c8 x1 x5 x6 x7 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 (P + 24)) x10 (Z_to_bv 64 P) x12 x13 (Z_to_bv 64 hd) x15 x16 x17
                             (Z_to_bv 64 (P + 8)) (Z_to_bv 64 32) (Z_to_bv 64 A) (Z_to_bv 64 P) x22 x23
                             (SHR (P + 16)) (SHR (P + 24)) (SHR (P + 8)) x28 x29 x30 x31 Fx fcx m2) mo2 g2.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Hd MIDm HPX HNZ SEG NDA FR PB ND FA FRM HB HX. lits. bandM. sepM. unfold CSTO, SHR.
    (nelimp MIDm 9%nat; intros HL BY ERR MI ST PR GM TV PSH).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound asegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; left; exact Hb]).
    assert (INA : In (A, 64) LBX2) by (eapply perm_in_head; exact HPX).
    assert (INU : In (U, 64) LBX2) by (eapply Permutation_in; [exact HPX| right; left; reflexivity]).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INA) 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
    pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL PLF) as BHA. destruct (BHA A 64 INA) as [_ APd].
    assert (BLK : forall A' k, In (A', k) LBX2 -> disjoint_from [(P + 16, P + 24)] A' k).
    { intros A' k Hin. cbn. split; [|exact I]. destruct (BHA A' k Hin). lia. }
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ (proj1 HDn)) ltac:(lia) ltac:(lia)) as TS.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold AERRNO, ATP in ERR. unfold OFRAME, SAVEDO, SHR in FR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (sh_zero_shb m2 P (P + 56) (P + 8) PSH ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { apply evt_done.
      assert (CH : cj_chain CJ_ANY m2 (S dch) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [lia| eqcells NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply FAILO4; [exact MIDm| | exact CH| unfold CJ_pvalue_lemmas.dch; lia| | exact PB'| eqcells ND| exact FA| exact FRM
        | clear -HB HX Ho BPRE OFF; blia].
      - eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR).
      - apply (OFRAME_fold ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P m2 j0). unfold OFRAME, SAVEDO, SHR. exact FR. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    pose proof (sh_zero_shb m2 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    assert (TS3 : text_sh m3 CA blen) by (eapply text_sh_high_store; [exact TS| exact MU| alia| lia| alia]).
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    (* [comment removed for export] *)
    pose proof (fin_off0 P blen (o + 1) bs LEN ltac:(lia)) as FO.
    eapply evt_cut.
    { eapply (ws2 sp gp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC m3 TS3 PSH3 (Z.to_nat (blen - (o + 1))) (o + 1) (depth + 1) m3);
        [lia| lia| unfold pbuf_cells, wz; lazymatch goal with H : rw_cells asegs m3 P _ |- _ => exact H end| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
    intros ms' nelH_; (nelim nelH_ 12%nat; intros x10' x12' x13' x15' x16' m4 -> PB4 BY4 MI4 MU4 WM4). unfold CSTO, SHR. rewrite <- FO in PB4.
    clear BY MI PB.
    pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
    trc FR MU4 WM4. trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4. trc ST MU4 WM4.
    assert (HL4 : ART AI sp0 SPB LBX2 LF TRS2 B2 m4 mo2 g2) by (eapply (art_pbuf_store AI); [exact HL| exact PLF| exact MU24| exact WM24| lia| lia]).
    assert (PR4 : ppres sp0 LR LF SP P m m4).
    { eapply ppres_trans; [exact PR|]. eapply ppres_pbuf_store; [exact MU24| exact WM24| lia| lia]. }
    assert (PSH4 : pbuf_sh m4 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU24| alia| alia| alia]).
    assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU24| exact WM24|]. intros A' k Hin. apply BLK. apply INX. exact Hin. }
    clear MU WM MU4 WM4 MU24 WM24 PR SEG m3 TS3 PSH3 TS.
    pose proof (skipws_off_range bs (o + 1) ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
    set (o1 := skipws_off bs (o + 1)) in *.
    (* [comment removed for export] *)
    zstep. zstep.
    assert (PI : parse_inv AI TI m4 mo2 g2 sp0 SPB LBX2 [] ((U, 64) :: X ++ LR) LF TRS2 np B2 A P CA blen bs D n lo (SP + -144) errv2).
    { split; [exact HL4|]. split; [exact HPX|]. split; [right; apply in_or_app; right; exact (proj1 HDn)|].
      split; [lia|]. split; [lia|]. split; [exact BY4|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI4|]. split; [exact ST|]. split; [alia|]. split; [exact TV|]. split; [exact PLF|].
      split; [exact PSH4|]. repeat split; try assumption; alia. }
    (nelimp sconst_stats 3%nat; intros _ STM STF).
    change (Z_to_bv 64 547128) with (wz PARSE_STRING).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { pose proof (parse_string_spec AI TI) as PS. unfold parse_string_stmt in PS.
      eapply PS with (U := A) (P := P) (off := o1) (depth := depth + 1) (nx := 0) (ch := 0) (ty := 0) (vs := 0) (ky := 0); clear PS; rewrite ?unsigned_lit by lia;
        first [ exact PI | unfold pbuf_at; exact PB4 | eqcells NDA | exact TP | reflexivity | exact STM | exact STF
              | clear -HB BPRE OFF OR Ho; unfold pstr_cost_pre, pstr_fail_cost in *; blia
              | alia ]. }
    cbv beta. intros ms5 mo5 g5 PO'.
    (nelim PO' 31%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' m5 r off2 LB5 X2 TRS5 B5 errv5 -> -> PI5 PR5 GM5 PB5 Ho2 RES)
.
    rewrite ?unsigned_lit in PI5, PR5 by lia.
    replace (ret_pc (Z_to_bv 64 0x86568)) with (Z_to_bv 64 0x86568) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI5 16%nat; intros HL5 HP5 _ _ _ BY5 _ _ ERR5 MI5 ST5 _ TV5 _ PSH5 _).
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR5) in FR; [| lia| cbn; lia| alia| alia].
    apply (ppres_rw_cells_block _ _ _ _ _ _ _ _ _ U 64 PR5) in ND; [| left; reflexivity| lia| cbn; lia| unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| lia].
    apply (ppres_cj_lseg _ _ _ _ _ _ _ _ _ _ _ _ PR5) in SEG4; [| intros b Hb; right; apply in_or_app; left; exact Hb| intros A' n' Hin; apply BHA; apply INX; exact Hin].
    assert (PR6 : ppres sp0 LR LF SP P m m5).
    { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b Hb; right; apply in_or_app; right; exact Hb| intros f Hf; exact Hf]. }
    unfold wz. eapply (after_key c IHc o o1 hd A pvA X r off2 X2 m5 mo5 g5 LB5 TRS5 B2 B5 errv5);
      [exact Hc| lia| lia| exact Hd| | exact HP5| exact HNZ| lia| exact SEG4| unfold OFRAME, SAVEDO, SHR; exact FR| exact PB5| exact Ho2| eqcells ND| exact FA| exact FRM
      | exact HB| exact HX| ].
    - split; [exact HL5|]. split; [exact BY5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PR6|].
      split; [eapply gmono_trans; [exact GM| exact GM5]|]. split; [exact TV5| exact PSH5].
    - destruct RES as [(-> & -> & NDR & HBF)|(-> & KS & k & -> & KNZ & NDR & SK & Hk & HBk)].
      + left. split; [reflexivity|]. split; [reflexivity|]. split; [exact NDR| exact HBF].
      + right. split; [reflexivity|]. exists KS, k. split; [reflexivity|]. split; [exact KNZ|]. split; [exact NDR|]. split; [exact SK|]. split; [exact Hk| exact HBk].
  Qed.

End POL.


End CeilWrap.
End CJ_pobject_L2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas.
Import CJ_pstring_C.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pobject_L1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pobject_L1.CJ_pobject_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pobject_L1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pobject_L1.CJ_pobject_ws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pobject_L1.
Import CJ_pobject_L2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section POL.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (POBJ_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis DEL : cjson_delete_stmt AI TI.
  Hypothesis SDEL : Forall (STAT TI) S_DELETE.
  Hypothesis SCONST : Forall (STAT TI) S_PARSE_CONST.
  Hypothesis SPV : forall b, STAT TI (tr_pv_pobj b).
  Hypothesis LFR : lf_room 2 LF (1000 - depth).
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at AI TI nf.
  Hypothesis MEMSET : asan_memset_spec.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B [] U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDO AI TI sp m g sp0 SPB LR LF np P CA bs lo).
  Notation SAVED := (SAVEDO ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation OFR := (OFRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P).
  Notation dch := (dch depth).
  Notation OLOOPc := (OLOOP AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LR LF np B U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation WSM := (ws_mem P CA blen bs).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & HDn & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold POBJ_STACK, PARSE_STACK in LO.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac steq := unfold CSTO, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  (* [comment removed for export] *)
  Ltac blia := unfold pv_cost_pre, PV_FRATE, PV_RATE, cost_free in *; rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.

  Notation FAILO7 := (fail_o7 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation FAILO4 := (fail_o4 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation FAILO := (fail_o AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL).
  Notation RET0O := (ret0_o AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC).
  Notation OBJCLOSE := (obj_close AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC).
  Notation PRES_FRAME := (pres_frame sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_PBUF := (pres_pbuf sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_TEXT := (pres_text sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation PRES_PSH := (pres_pbuf_sh sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).

  Notation DO_KEY := (do_key AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B U P CA blen off depth bs D n lo
                        nx pv ty p1 vi p2 vd ky PVC BPRE DEL SDEL SCONST SPV LFR nfuel FUEL PVREC).

  (* [comment removed for export] *)
  Lemma ppres_memset_fp : forall A R LB2 TRS1 B1 m3 mm mo1 g1,
    ART AI sp0 SPB LB2 LF TRS1 B1 m3 mo1 g1 -> Permutation ((A, 64) :: R) LB2 -> (forall b, In b LR -> In b R) ->
    munch [(A, A + 64); (SP + -144 - AINTRIN_STACK, SP + -144)] m3 mm -> wmono asegs m3 mm -> ppres sp0 LR LF SP P m3 mm.
  Proof.
    intros A R LB2 TRS1 B1 m3 mm mo1 g1 HL HP HLR MU WM a Ha nelH_; (nelim nelH_ 3%nat; intros Hc _ _). lits. bandM. sepM. unfold AINTRIN_STACK in MU.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
    try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn.
    destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' (HLR _ Hin)) as [_ Dj].
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact (HLR _ Hin)])) 4%nat; intros Q1' _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia.
    - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 8%nat; intros Hk _ HF1 HF2 _ _ _ HD).
      try rewrite alloc_ceiling_eq in HF2. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HF1. bandM. sepM.
      assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      destruct Hr as [Hr|Hr].
      + destruct (HD A 64 (perm_in_head _ _ _ HP)) as [Dd|Dd]; lia.
      + (* [comment removed for export] *)
        (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 3%nat; intros _ GAL _).
        pose proof (frame_sh_in_band Fr k a Hk GAL ltac:(lia) HF2 Hr) as AB.
        pose proof (band_addr_not_block AI _ _ _ _ _ _ _ _ _ A 64 a HL (perm_in_head _ _ _ HP) AB) as NB. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in AB. bandM. sepM.
        pose proof alloc_ceiling_range as ACR. assert (LOC : alloc_ceiling <= SP + -144 - 2304) by lia. clear - AB NB ACR LOC. lia.
    - pose proof (stack_sh_in_band _ _ Hsh) as AB.
      pose proof (band_addr_not_block AI _ _ _ _ _ _ _ _ _ A 64 a HL (perm_in_head _ _ _ HP) AB) as NB. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in AB. bandM. sepM.
      pose proof alloc_ceiling_range as ACR. assert (LOC : alloc_ceiling <= SP + -144 - 2304) by lia. clear - AB NB ACR LOC. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_body_o : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') -> OLOOPc c.
  Proof.
    intros c IHc. unfold OLOOP. intros until x31. intros Hc Ho Hd MIDm HPX OI FR PB ND FA FRM HB HX. lits. bandM. sepM. unfold CSTO, SHR.
    (nelimp MIDm 9%nat; intros HL BY ERR MI ST PR GM TV PSH).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    (nelimp (sconst_stats TI SCONST) 3%nat; intros STO _ _).
    assert (B0 : 448 + 256 <= B1) by (clear -HB BPRE OFF Ho; blia).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold AERRNO, ATP in ERR. unfold OFRAME, SAVEDO, SHR in FR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 32) PSH ltac:(lia)) as Z32. asan_chk Z32. clear Z32.
    zstep. zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 AMALLOC)) with (wz AMALLOC) by (unfold wz, AMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (art_malloc_ok AI) with (lo := lo) (n := 64) (tl := []); rewrite ?unsigned_lit by lia;
        first [ exact HL | exact ST | unfold AERRNO, ATP; exact ERR | exact MI | exact TP | reflexivity | alia
              | rewrite cost_malloc_64; lia
              | split; [lia| unfold PC0_MALLOC; lia]
              | apply uwt_hook_nonfp; lia
              | eapply (tinv_room TI); [exact TV| exact STO] ]. }
    cbv beta. intros ms2 mo2 g2 PO'.
    (nelim PO' 26%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 RES)
.
    rewrite ?unsigned_lit in ST2, PR2, TP2 by lia. rewrite cost_malloc_64 in RES.
    replace (ret_pc (Z_to_bv 64 0x86478)) with (Z_to_bv 64 0x86478) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (PRES_FRAME _ _ _ _ PR2) in FR; [| reflexivity].
    apply (PRES_PBUF _ _ _ _ _ _ _ PR2) in PB'. clear PB.
    apply (pres_block sp sp0 LF _ _ _ U _ PR2 INU) in ND; [| reflexivity].
    apply (PRES_TEXT _ _ _ PR2 (INLR _ (proj1 HDn))) in BY.
    assert (TV2 : TINV TI np TRS2) by (eapply (tinv_put_or TI); [exact TV| exact STO| exact TP2]).
    assert (PR3 : ppres sp0 LR LF SP P m m2) by (eapply pres_ppres; [exact PR2| exact INLR| exact PR]).
    assert (PSH2 : pbuf_sh m2 P) by (eapply PRES_PSH; [exact PR2| exact INLR| exact PSH]).
    apply (obj_inv_magree _ m1 m2) in OI; [| eapply magree_blocks_of_cj_pres; [exact PR2| exact INX]].
    assert (GM3 : gmono g g2) by (eapply gmono_trans; [exact GM| exact GM2]).
    clear PR PR2 MI ST HL ERR PSH TV GM. unfold AERRNO, ATP in ERR2.
    destruct RES as [[-> HL2] | (A & jk & -> & ARNG & ANEW & AFR & HL2 & BLK & FILL)].
    - (* [comment removed for export] *)
      eapply lscps_step_evt. cbv beta delta [mkR].
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (obj_inv_chain _ _ _ _ _ OI)) 3%nat; intros HR1 _ HR2).
      unfold wz. zstep. if_true. zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct OI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        apply evt_done. eapply (RET0O _ o (depth + 1) m2 mo2 g2 LBX TRS2 (B1 - 448) errv2); [| exact HPX| | exact PB'| eqcells ND| exact FA| exact FRM| clear -HB BPRE OFF Ho; blia].
        * split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
          split; [exact PR3|]. split; [exact GM3|]. split; [exact TV2| exact PSH2].
        * apply (OFRAME_fold ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P m2 j0). unfold OFRAME, SAVEDO, SHR. exact FR.
      + (* [comment removed for export] *)
        apply evt_done. eapply (FAILO _ o (depth + 1) head X (S dch) m2 mo2 g2 LBX TRS2 (B1 - 448) errv2);
          [| exact HPX| eapply cj_chain_any; eapply obj_inv_chain; exact OI| unfold CJ_pvalue_lemmas.dch; lia| | exact PB'| eqcells ND| exact FA| exact FRM
          | clear -HB HX BPRE OFF Ho; blia].
        * split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
          split; [exact PR3|]. split; [exact GM3|]. split; [exact TV2| exact PSH2].
        * apply (OFRAME_fold ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P m2 j0). unfold OFRAME, SAVEDO, SHR. exact FR.
    - (* [comment removed for export] *)
      (nelimp ARNG 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
      assert (HPA : Permutation ((A, 64) :: (U, 64) :: X ++ LR) ((A, 64) :: LBX)) by (apply perm_skip; exact HPX).
      assert (APART : forall A' n', In (A', n') ((U, 64) :: X ++ LR) -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
      { intros A' n' Hin. eapply (lheap_perm_apart AI); [exact HL2| exact HPA| exact Hin]. }
      destruct (APART U 64 ltac:(left; reflexivity)) as [_ AU]. destruct (APART D n ltac:(right; apply in_or_app; right; exact (proj1 HDn))) as [_ AD].
      assert (APF : A + 64 + 16 <= P - 32 \/ P - 32 + 128 <= A - 16).
      { (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL2 PLF) 8%nat; intros _ _ _ _ _ _ _ FD').
        destruct (FD' A 64 ltac:(left; reflexivity)); [left| right]; change (fsz 1) with 128 in *; lia. }
      eapply lscps_step_evt. cbv beta delta [mkR].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
        sepM. eapply MSX with (lo := lo) (d := A) (c := 0) (n := 64) (junk := jk); clear MSX; rewrite ?unsigned_lit by lia;
          first [ lazymatch goal with |- icpt_cells _ => eapply art_icpt_cells; exact HL2 end | exact MI2 | exact ST2 | exact BLK | reflexivity
                | lazymatch goal with |- app_range _ _ => app_rng0 end
                | apply wr_range_ok_high; lia
                | intros _; eapply art_block_shadow_ok; [exact HL2| left; reflexivity]
                | unfold AINTRIN_STACK; alia
                | lia ]. }
      cbv beta. intros ms' PO.
      (nelim PO 21%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m3 -> MU3 WM3 MI3 ZB ST3).
      rewrite ?unsigned_lit in MU3, ST3 by lia. unfold AINTRIN_STACK in MU3.
      replace (ret_pc (Z_to_bv 64 0x8648c)) with (Z_to_bv 64 0x8648c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (zero_node_cells' _ _ ZB) as NDA. clear ZB. unfold node_cells, wz in NDA.
      trc FR MU3 WM3. trc ND MU3 WM3. trc ERR2 MU3 WM3. trc BY MU3 WM3.
      assert (PB3 : pbuf_at m3 P CA blen o (depth + 1)).
      { unfold pbuf_at in *. eapply rw_cells_transport; [exact PB'| exact MU3| exact WM3| rewrite pbuf_cells_size; dj]. }
      unfold pbuf_at, pbuf_cells, wz in PB3.
      apply (obj_inv_magree _ m2 m3) in OI.
      2:{ eapply magree_blocks_of_munch; [exact MU3| exact WM3|]. intros A' n' Hin. cbn. destruct (APART A' n' ltac:(right; apply in_or_app; left; exact Hin)).
          (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 ltac:(right; apply INX; exact Hin)) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4.
          split; [lia| split; [lia| exact I]]. }
      assert (HL3 : ART AI sp0 SPB ((A, 64) :: LBX) LF TRS2 (B1 - 448) m3 mo2 g2).
      { eapply (art_frame AI); [exact HL2| exact MU3| exact WM3|].
        constructor; [| constructor; [| constructor]].
        - do 7 right. left. exists A, 64. cbn. split; [left; reflexivity| lia].
        - right; left. cbn. alia. }
      assert (PR4 : ppres sp0 LR LF SP P m m3).
      { eapply ppres_trans; [exact PR3|]. eapply ppres_memset_fp; [exact HL2| apply Permutation_refl| intros b Hb; apply INLR; exact Hb| unfold AINTRIN_STACK; exact MU3| exact WM3]. }
      assert (PSH3 : pbuf_sh m3 P).
      { eapply pbuf_sh_munch; [exact PSH2| exact MU3| lia| lia| pbuf_dj (* [comment removed for export] *)]. }
      clear MU3 WM3 MI2 ST2 PR3 PSH2 BLK FILL.
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (obj_inv_chain _ _ _ _ _ OI)) 3%nat; intros HR1 _ HR2).
      zstep. zstep. zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct OI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX, HPA.
        apply evt_done. eapply (DO_KEY c IHc o A A (wz 0) [] m3 mo2 g2 ((A, 64) :: LBX) TRS2 (B1 - 448) errv2);
          [exact Hc| exact Ho| exact Hd| | exact HPA| lia| apply cj_lseg_nil| eqcells NDA| unfold OFRAME, SAVEDO, SHR; exact FR| unfold pbuf_at; eqcells PB3| eqcells ND| exact FA| exact FRM
          | clear -HB; unfold PV_RATE in *; lia| cbn; lia].
        split; [exact HL3|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact PR4|]. split; [exact GM3|]. split; [exact TV2| exact PSH3].
      + (* [comment removed for export] *)
        destruct OI as [[E _]|(NZ & NZc & B1' & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & NDC & TYC & SVC & SKC & CHC)]; [exfalso; exact (Kh E)|].
        assert (HPcur : Permutation ((cur, 64) :: (A, 64) :: (B1' ++ Bv ++ Bk ++ Bc) ++ (U, 64) :: LR) ((A, 64) :: LBX)).
        { eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply Permutation_trans; [apply perm_pick_mid| exact HPX]. }
        assert (INC : In (cur, 64) ((A, 64) :: LBX)) by (eapply perm_in_head; exact HPcur).
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL3 INC) 4%nat; intros C1 C2 C3 C4). try rewrite alloc_ceiling_eq in C4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM.
        assert (CPART : forall A' n', In (A', n') ((A, 64) :: (B1' ++ Bv ++ Bk ++ Bc) ++ (U, 64) :: LR) -> A' <> cur /\ (A' + n' <= cur \/ cur + 64 <= A')).
        { intros A' n' Hin. eapply (lheap_perm_apart AI); [exact HL3| exact HPcur| exact Hin]. }
        destruct (CPART A 64 ltac:(left; reflexivity)) as [_ CA'].
        destruct (CPART U 64 ltac:(right; apply in_or_app; right; left; reflexivity)) as [_ CU].
        destruct (CPART D n ltac:(right; apply in_or_app; right; right; exact (proj1 HDn))) as [_ CD].
        pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL3 PLF) as BHA. destruct (BHA cur 64 INC) as [_ CPd]. destruct (BHA A 64 ltac:(left; reflexivity)) as [_ APd].
        pose proof (rw_cells_bound asegs _ _ _ NDC) as NCB. rewrite node_cells_size in NCB. unfold node_cells, wz in NDC.
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL3 INC) as SOC.
        (* [comment removed for export] *)
        pose proof (munch_refl [(cur, cur + 8)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        zstep. zstep.
        pose proof (shadow_ok_shchk m3 cur 64 cur 8 SOC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CKc. asan_chk CKc.
        sepM. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        assert (HL4 : ART AI sp0 SPB ((A, 64) :: LBX) LF TRS2 (B1 - 448) m4 mo2 g2) by (eapply (art_block_store AI); [exact HL3| exact INC| exact MU| exact WM| lia| lia]).
        assert (PR5 : ppres sp0 LR LF SP P m m4).
        { eapply ppres_trans; [exact PR4|]. eapply (ppres_block_store AI); [exact HL3| exact HPcur| intros b Hb; right; apply in_or_app; right; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
        assert (PSH4 : pbuf_sh m4 P) by (eapply pbuf_sh_high_store; [exact PSH3| exact MU| alia| alia| alia]).
        assert (DJ : forall A' n', In (A', n') (B1' ++ Bv ++ Bk ++ Bc) -> disjoint_from [(cur, cur + 8)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I]. destruct (CPART A' n' ltac:(right; apply in_or_app; left; exact Hin)). lia. }
        assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch head cur B1').
        { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC4 : cj_str m4 vsc Bv).
        { eapply cj_str_frame; [exact SVC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (SKC4 : cj_str m4 kyc Bk).
        { eapply cj_str_frame; [exact SKC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC4 : cj_chain CJ_PRINTABLE m4 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL4 ltac:(left; reflexivity)) as SOA.
        clear MU WM HL3 PR4 PSH3 SEG SVC SKC CHC DJ SOC.
        (* [comment removed for export] *)
        pose proof (munch_refl [(A + 8, A + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        zstep. zstep. zstep.
        pose proof (shadow_ok_shchk m4 A 64 (A + 8) 8 SOA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CKa. asan_chk CKa.
        sepM. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        assert (HL5 : ART AI sp0 SPB ((A, 64) :: LBX) LF TRS2 (B1 - 448) m5 mo2 g2) by (eapply (art_block_store AI); [exact HL4| left; reflexivity| exact MU| exact WM| lia| lia]).
        assert (PR6 : ppres sp0 LR LF SP P m m5).
        { eapply ppres_trans; [exact PR5|]. eapply (ppres_block_store AI); [exact HL4| apply Permutation_refl| exact INLR| alia| lia| exact MU| exact WM| lia| lia]. }
        sepM. assert (PSH5 : pbuf_sh m5 P) by (eapply pbuf_sh_high_store; [exact PSH4| exact MU| alia| alia| alia]).
        assert (DJ : forall A' n', In (A', n') (B1' ++ Bv ++ Bk ++ Bc) -> disjoint_from [(A + 8, A + 16)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I].
          destruct (APART A' n') as [_ ?]; [| lia]. right. apply in_or_app. left. apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]. }
        assert (SEG5 : cj_lseg CJ_PRINTABLE m5 dch head cur B1').
        { eapply cj_lseg_frame; [exact SEG4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC5 : cj_str m5 vsc Bv).
        { eapply cj_str_frame; [exact SVC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (SKC5 : cj_str m5 kyc Bk).
        { eapply cj_str_frame; [exact SKC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC5 : cj_chain CJ_PRINTABLE m5 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL4 PR5 PSH4 SEG4 SVC4 SKC4 CHC4 DJ.
        zstep. apply evt_done.
        eapply (DO_KEY c IHc o head A (Z_to_bv 64 cur) (B1' ++ (cur, 64) :: Bv ++ Bk ++ Bc) m5 mo2 g2 ((A, 64) :: LBX) TRS2 (B1 - 448) errv2);
          [exact Hc| exact Ho| exact Hd| | exact HPA| exact NZ| | eqcells NDA| unfold OFRAME, SAVEDO, SHR; exact FR| unfold pbuf_at; eqcells PB3| eqcells ND| exact FA| exact FRM
          | clear -HB; unfold PV_RATE in *; lia| clear -HX; lia].
        * split; [exact HL5|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI3|]. split; [exact ST3|].
          split; [exact PR6|]. split; [exact GM3|]. split; [exact TV2| exact PSH5].
        * eapply cj_lseg_snoc; [exact SEG5| exact NZc| eqcells NDC| apply CJ_PRINTABLE_range; exact TYC| exact TYC| exact SVC5| exact SKC5| exact CHC5].
  Qed.

  Theorem oloop : forall c, OLOOPc c.
  Proof. induction c as [c IH] using lt_wf_ind. apply loop_body_o. exact IH. Qed.
End POL.


End CeilWrap.
