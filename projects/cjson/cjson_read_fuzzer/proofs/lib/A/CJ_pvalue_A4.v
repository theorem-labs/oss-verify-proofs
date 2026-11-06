(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Module CJ_band4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Ltac sh_dj_at X Y :=
  let PB1 := fresh "SB1" in let PB2 := fresh "SB2" in let PM := fresh "SM" in
  pose proof (SH_in_band X ltac:(lia) ltac:(lia)) as (PB1 & _);
  pose proof (SH_in_band Y ltac:(lia) ltac:(lia)) as (_ & PB2);
  pose proof (SH_mono X Y ltac:(lia)) as PM;
  unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in PB1, PB2;
  cbn [disjoint_from fst snd];
  repeat lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split
  | |- _ + _ <= ?u \/ ?v <= _ =>
      first [ let SC := fresh "SC" in assert (SC : sclr u (v - u)) by sclr_tac2;
              unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in SC; lia
            | unfold SH, SHADOW_OFFSET in *; Z.div_mod_to_equations; lia ]
  end.
Ltac sh_dj := lazymatch goal with |- Frame.disjoint_from _ (SH ?X) (SH ?Y + 1 - SH ?X) => sh_dj_at X Y end.
End CJ_band4.

(* [comment removed for export] *)
From Stdlib Require NArith.
From Stdlib Require Bool.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pvalue_A3.
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
Import CJ_band4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_band3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_A1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma pv_trace_push : forall f r s CH b, pv_trace 0x834b8 ((f, r, s) :: CH) b = pv_trace r CH (S b).
Proof.
  intros. unfold pv_trace. cbn [repeat map fr_ra fst snd]. rewrite repeat_cons, <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma chain_cells_consf : forall m f (s0w raw : word) CH,
  rw_cells asegs m (f + -16) [C8 s0w; C8 raw] -> chain_cells m CH -> chain_cells m ((f, bv_unsigned raw, bv_unsigned s0w) :: CH).
Proof.
  intros m f s0w raw CH H CC. pose proof (chain_cells_frame1 m f s0w raw H) as [H1 _]. split; [exact H1| exact CC].
Qed.

Section PVA3.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z) (CH : list (Z * Z * Z)).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (PARSE_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis CHOK : chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0).
  Hypothesis CHL : chain_link (bv_unsigned s0) (bv_unsigned sp) CH.
  Hypothesis RA1 : 4096 <= bv_unsigned ra.
  Hypothesis RA2 : ~ is_pc0 (bv_unsigned ra).
  Hypothesis FLA : flag_apart_stmt AI.
  Hypothesis STPV : forall b, STAT TI (pv_trace (bv_unsigned ra) CH b).
  Hypothesis STPO : forall b, STAT TI (tr_pv_pobj b).
  Hypothesis STC : Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE).
  Hypothesis LFR : lf_room 2 LF (1001 - depth).
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation VSTx := (VST sp gp tp).
  Notation MID := (MIDV AI TI sp m g sp0 SPB LR LF np CH P CA bs lo).
  Notation VFRx := (VFR ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P).
  Notation VGEOMx := (VGEOM sp LB LF P).
  Notation VRESx := (VRES LR B U blen off depth nx pv ty p1 vi p2 vd ky).
  Notation DCH := (dch depth).
  Notation CS08x := (CS08 P).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK, SKIPWS_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac steq := unfold VST, SHV, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac blia := unfold pv_cost_pre, pstr_cost_pre, pstr_fail_cost, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  Hypothesis DEL : cjson_delete_stmt AI TI.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at AI TI nf.

  Notation ALOOPc := (ALOOP AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation ARR_FAIL_C8 := (arr_fail_c8 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA STC nfuel DEL).
  Notation VFR_MUNCH := (VFR_munch ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC nfuel).
  Notation AFTER_CALL := (after_call AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA STC nfuel FUEL DEL).

  (* [comment removed for export] *)
  Lemma our_chain : forall SA Fr mm,
    VGEOMx SA Fr -> rw_cells asegs mm (SP + -104) (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> chain_cells mm CH ->
    chain_cells mm ((SP, bv_unsigned ra, bv_unsigned s0) :: CH)
    /\ chain_ok (SA + 16) ((SP, bv_unsigned ra, bv_unsigned s0) :: CH) (ASTACK_TOP sp0)
    /\ chain_link SP SA ((SP, bv_unsigned ra, bv_unsigned s0) :: CH).
  Proof.
    intros SA Fr mm (GSA & GAL & _) SAVW CC. lits. bandM. sepM. unfold SAVEDV in SAVW.
    lazymatch type of SAVW with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
      pose proof (proj2 (proj1 (rw_cells_split_app mm (SP + -104) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] rest) SAVW)) as S2 end.
    cbn [cells_size Cells.csize Nat.add app] in S2. replace (SP + -104 + Z.of_nat 88) with (SP + -16) in S2 by lia.
    split; [apply chain_cells_consf; [exact S2| exact CC]|].
    split.
    - cbn. split; [lia|]. split; [clear -SP6; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [exact RA2|]. split; [lia|].
      split; [exact CHL|]. eapply chain_ok_mono; [exact CHOK| lia].
    - cbn. split; [reflexivity| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pv_addr_not_newblock : forall LBX LFX m1 mo1 g1 TRS1 B1 A R a,
    ART AI sp0 SPB LBX LFX TRS1 B1 m1 mo1 g1 -> Permutation ((A, 64) :: R) LBX -> (forall b, In b LR -> In b R) -> (forall f, In f LF -> In f LFX) ->
    0 <= a < 2^64 -> pv_addr sp0 LR LF SP P a -> ~ (A <= a < A + 64).
  Proof.
    intros LBX LFX m1 mo1 g1 TRS1 B1 A R a HL HP INLR INLF Ha (Hc & He & Hp) Hin. lits. bandM. sepM.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
    try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
    pose_perm_blk_band HL HP. bandM. sepM.   (* [comment removed for export] *)
    destruct Hc as [Hs|[Hi|[(A' & n' & HinA & Hr)|[(G & k & HinG & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' (INLR _ HinA)) as [_ Dj]. lia.
    - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL (INLF _ HinG)) 8%nat; intros Hk GAL' GLO GHI _ _ _ FD).
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in GLO. bandM. sepM. try rewrite alloc_ceiling_eq in GHI.
      assert (Hfs : fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      destruct Hr as [Hb|Hshg].
      + destruct (FD A 64 (perm_in_head _ _ _ HP)); lia.
      + pose proof (SH_bounds G ltac:((lia_on Hshg PF1 U1 D1 R1 GAL' GLO GHI))). pose proof (SH_bounds (G + fsz k) ltac:((lia_on Hshg PF1 U1 D1 R1 GAL' GLO GHI))) as M1.
        rewrite (SH_aligned_add G (fsz k)) in M1 by first [mod8 | (Z.div_mod_to_equations; lia)]. lia.
    - pose proof (stack_sh_in_band _ _ Hsh) as AB. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in AB. lia.   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma do_call : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (SA Fr o hd A : Z) (pvA : word) (X : list cblock) m2 mo2 g2 LBX2 TRS2 B2 errv2 Fx fcx shb h jae jn lj
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      VGEOMx SA Fr -> MID SA Fr m2 mo2 g2 LBX2 TRS2 B2 errv2 -> Permutation ((A, 64) :: (U, 64) :: X ++ LR) LBX2 ->
      hd <> 0 -> cj_lseg CJ_PRINTABLE m2 DCH hd A X ->
      rw_cells asegs m2 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) ->
      VFRx SA Fr m2 shb h jae jn CS08x lj ->
      pbuf_at m2 P CA blen o (depth + 1) ->
      rw_cells asegs m2 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o - off) - 448 <= B2 -> Z.of_nat (length X) <= o - off ->
      LSCPS asegs POST (VSTx SA Fr 0x8348c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 hd) (Z_to_bv 64 A) (Z_to_bv 64 P)
                          (Z_to_bv 64 (P + 24)) (SHV (P + 24)) x24 x28 x29 x30 x31 Fx fcx m2) mo2 g2.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Hd GE MD HPX HNZ SEG NDA VF PB ND FA FRM HB HXl. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound asegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    assert (INLR : forall b, In b LR -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; left; exact Hb]).
    assert (INU : In (U, 64) LBX2) by (eapply Permutation_in; [exact HPX| right; left; reflexivity]).
    assert (INA : In (A, 64) LBX2) by (eapply perm_in_head; exact HPX).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INA) 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ HD) DCA CAD) as TSH.
    pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL ltac:(right; exact PLF)) as BHA. destruct (BHA A 64 INA) as [_ APd].
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    (nelimp VF 10%nat; intros _ L32 _ _ _ L0 S0 L16 _ _). unfold LOCSV, SHV in L16. unfold CS08, SHV in L0.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep. sepM. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LBX2 ((Fr, 2) :: LF) TRS2 B2 m3 mo2 g2) by (eapply (art_pbuf_store AI); [exact HL| right; exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres sp0 LR LF SP P m m3) by (eapply ppres_trans; [exact PR| eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]]).
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    assert (CC3 : chain_cells m3 CH).
    { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    assert (VF3 : VFRx SA Fr m3 shb h jae jn CS08x lj).
    { eapply VFR_MUNCH; [exact GE| exact VF| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right. repeat split; alia. }
    assert (SEG3 : cj_lseg CJ_PRINTABLE m3 DCH hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' k Hin. cbn. split; [|exact I]. destruct (BHA A' k (INX _ Hin)). lia. }
    assert (TSH3 : text_sh m3 CA blen) by (eapply (art_text_sh AI); [exact HL3| exact (INLR _ HD)| exact DCA| exact CAD]).
    clear MU WM HL PR PSH CC VF SEG.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply evt_cut.
    { eapply skipws_spec with (P := P) (content := CA) (len := blen) (offset := o + 1) (depth := depth + 1) (bs := bs) (lo := lo); rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- pbuf_at _ _ _ _ _ _ => unfold pbuf_at, pbuf_cells, wz; eqcells PB end
              | reflexivity | exact BY | exact LEN | exact PSH3 | exact TSH3 | exact ST
              | eapply (art_shbase AI); exact HL3
              | assumption
              | (cut_on [PF1 Hd DCA LO D1 GSA Ho OFF CAD D4 PF2 PF3 SMf BMf0] alia)
              | clear -PF3; Z.div_mod_to_equations; lia ]. }
    intros ms' PO. (nelim PO 18%nat; intros t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' m4 -> MU4 WM4 MI4 ST4 PB4 BY4).
    rewrite ?unsigned_lit in MU4, ST4 by lia.
    replace (ret_pc (Z_to_bv 64 0x834ac)) with (Z_to_bv 64 0x834ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4.
    assert (HL4 : ART AI sp0 SPB LBX2 ((Fr, 2) :: LF) TRS2 B2 m4 mo2 g2).
    { eapply (art_frame AI); [exact HL3| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]].
      - do 8 right. left. exists (P - 32), 1. cbn. split; [right; exact PLF|]. change (fsz 1) with 128. lia.
      - right; left. cbn. alia. }
    assert (PR4 : ppres sp0 LR LF SP P m m4).
    { eapply ppres_trans; [exact PR3|]. eapply ppres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hp. cbn.
      pose proof (pv_addr_below AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC LBX2 ((Fr, 2) :: LF) m3 mo2 g2 TRS2 B2 a HL3 INLR
                    ltac:(intros f Hf; right; exact Hf) Ha Hp) as BLW.
      (nelim Hp 3%nat; intros _ _ HnP). try rewrite alloc_ceiling_eq in BLW. clear -BLW HnP CEIL LO GSA DEP. lia. }
    assert (PSH4 : pbuf_sh m4 P).
    { eapply pbuf_sh_munch; [exact PSH3| exact MU4| lia| lia|]. sepM. sepM. pbuf_dj (* [comment removed for export] *). }
    assert (CC4 : chain_cells m4 CH).
    { eapply chain_cells_munch; [exact CC3| exact CHOK| exact MU4| lia| lia|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; left; lia. }
    assert (VF4 : VFRx SA Fr m4 shb h jae jn CS08x lj).
    { eapply VFR_MUNCH; [exact GE| exact VF3| exact MU4| exact WM4|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; [right; repeat split; (cut_on [PF1 PF2 Ho Hd DCA CAD CEIL LO OFF U1 D1 GSA FLO SMf2 NAB BMf0] alia)| left; alia]. }
    assert (SEG4 : cj_lseg CJ_PRINTABLE m4 DCH hd A X).
    { eapply cj_lseg_frame; [exact SEG3| exact MU4| exact WM4|]. intros A' k Hin. cbn. destruct (BHA A' k (INX _ Hin)) as [R1 R2].
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL3 (INX _ Hin)) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4.
      split; [(lia_on R2)|]. split; [lia| exact I]. }
    assert (O2 : o + 1 <= skipws_off bs (o + 1) <= blen).
    { destruct (Z.eq_dec (o + 1) blen) as [E|NE].
      - rewrite skipws_off_noop by lia. lia.
      - pose proof (skipws_off_range bs (o + 1)) as OR. rewrite LEN in OR. (lia_on Ho Hd CEIL LO PF1 OFF U1 D1 GSA GAL FLO NAB NE OR). }
    (nelimp VF4 10%nat; intros _ _ _ _ _ _ _ _ _ SAVW4).
    (nelim (our_chain SA Fr m4 GE SAVW4 CC4) 3%nat; intros CCF COK CLK).
    clear MU4 WM4 HL3 PR3 PSH3 CC3 VF3 SEG3 PB BY MI ST.
    set (o2 := skipws_off bs (o + 1)) in *.
    assert (PI4 : parse_inv AI TI m4 mo2 g2 sp0 SPB LBX2 [] ((U, 64) :: X ++ LR) ((Fr, 2) :: LF) TRS2 np B2 A P CA blen bs D n lo SA errv2).
    { split; [exact HL4|]. split; [exact HPX|]. split; [right; apply in_or_app; right; exact HD|]. split; [lia|]. split; [lia|]. split; [exact BY4|].
      split; [exact LEN|]. split; [exact BLEN|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI4|]. split; [exact ST4|]. split; [alia|].
      split; [exact TV|]. split; [right; exact PLF|]. split; [exact PSH4|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. clear -GAL. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. change (Z_to_bv 64 535724) with (wz PARSE_VALUE).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { pose proof (PVREC (Z.to_nat (blen - (o + 1))) ltac:(lia)) as PVS. unfold parse_value_at in PVS.
      sepM. eapply PVS with (U := A) (P := P) (off := o2) (depth := depth + 1) (nx := 0) (pv := pvA) (ty := 0) (p1 := wz 0) (vi := wz 0) (p2 := wz 0) (vd := wz 0) (ky := 0)
                      (LR := (U, 64) :: X ++ LR) (CH := (SP, bv_unsigned ra, bv_unsigned s0) :: CH) (lo := lo) (D := D) (n := n) (bs := bs);
        clear PVS; rewrite ?unsigned_lit by (lia_on Hd CEIL LO SP4 SP5 TOPR GSA);
        first [ exact PI4 | eqcells NDA | exact PB4 | exact FRM | exact TP | exact CCF | exact COK | exact CLK | exact STPO | exact STC
              | lazymatch goal with |- _ = _ => reflexivity end
              | apply not_pc0_high; lia
              | intros bb; rewrite pv_trace_push; exact (STPV (S bb))
              | replace (1001 - (depth + 1)) with (1001 - depth - 1) by lia; apply lf_room_push; [exact LFR| lia]
              | clear -HB BPRE Ho O2 OFF; blia
              | (cut_on [Hd DEP LO GSA GAL] alia)
              | lia ]. }
    cbv beta. intros ms5 mo5 g5 PO'.
    (nelim PO' 36%nat; intros u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F5 fc5 m5 r off5 depth5 LB5 X5 TRS5 B5 errv5 -> -> FA5 FRM5 PI5 PR5 GM5 CC5 PB5 RES)
.
    rewrite ?unsigned_lit in PI5, PR5 by lia.
    replace (ret_pc (Z_to_bv 64 0x834b8)) with (Z_to_bv 64 0x834b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI5 16%nat; intros HL5 HP5 _ _ _ BY5 _ _ ERR5 MI5 ST5 _ TV5 _ PSH5 _). cbn [app] in HP5.
    pose proof (VFR_ppres ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC SA Fr m4 m5 shb h jae jn CS08x lj _ GE VF4 PR5 ltac:(lia)) as VF5.
    assert (BPV : forall A' n' a, In (A', n') ((U, 64) :: X ++ LR) -> A' <= a < A' + n' -> pv_addr sp0 ((U, 64) :: X ++ LR) ((Fr, 2) :: LF) SA P a).
    { intros A' n' a Hin Ha'. assert (Hin2 : In (A', n') LBX2) by (eapply Permutation_in; [exact HPX| right; exact Hin]).
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL4 Hin2) 4%nat; intros R1 _ _ R4). destruct (BHA A' n' Hin2) as [_ R5].
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      split; [do 2 right; left; exists A', n'; split; [exact Hin| lia]|]. unfold AERRNO, ATP. split; lia. }
    assert (ND5 : rw_cells asegs m5 U [C8 (Z_to_bv 64 nx); C8 pv; C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 ty); C4 p1; C8 (Z_to_bv 64 0); C4 vi; C4 p2; C8 vd; C8 (Z_to_bv 64 ky)]).
    { eapply rw_cells_magree; [exact PR5| exact ND|]. cbn [cells_size Cells.csize Nat.add]. intros a Ha. eapply (BPV U 64); [left; reflexivity| lia]. }
    assert (SEG5 : cj_lseg CJ_PRINTABLE m5 DCH hd A X).
    { eapply cj_lseg_magree; [exact SEG4| exact PR5|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Ha'). eapply (BPV A' n'); [right; apply in_or_app; left; exact Hin| lia]. }
    assert (PR6 : ppres sp0 LR LF SP P m m5).
    { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b' Hb'; right; apply in_or_app; right; exact Hb'| intros f Hf; right; exact Hf]. }
    assert (MD5 : MID SA Fr m5 mo5 g5 LB5 TRS5 B5 errv5).
    { split; [exact HL5|]. split; [exact BY5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PR6|].
      split; [eapply gmono_trans; [exact GM| exact GM5]|]. split; [exact TV5|]. split; [exact PSH5| exact (proj2 CC5)]. }
    eapply (AFTER_CALL c IHc SA Fr o o2 hd A pvA X r off5 depth5 X5 m5 mo5 g5 LB5 TRS5 B5 errv5 F5 fc5 shb h jae jn lj);
      [exact Hc| lia| lia| exact Hd| exact GE| exact MD5| exact HP5| exact HNZ| lia| exact SEG5| exact VF5| exact PB5| unfold node_cells, wz; exact ND5
      | eapply Fagree_trans; [exact FA| exact FA5]| exact FRM5| exact HXl|].
    destruct RES as [(-> & -> & NDA5 & HB5) | (-> & -> & Ho5 & HB5 & HX5 & REST)].
    - left. split; [reflexivity|]. split; [reflexivity|]. split; [exact NDA5| clear -HB HB5; lia].
    - right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Ho5|]. split; [clear -HB HB5 Ho5 O2; unfold PV_RATE in *; lia|]. split; [exact HX5| exact REST].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_top : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') -> ALOOPc c.
  Proof.
    intros c IHc. unfold ALOOP. intros until x31. intros Hc Ho Hd GE MD HPX AINV VF PB ND FA FRM HB HX. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    clear U2 U3 D2 PF3 RAR S0R FAL FNEW FBLK BLEN.
    assert (D4' : D + n <= alloc_ceiling) by (clear -D4 D3; lia). clear D4.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    assert (ST0 : STAT TI (PC0_MALLOC :: 0x8343c :: chain_trace 2 ((SP, bv_unsigned ra, bv_unsigned s0) :: CH))).
    { rewrite hook_trace_fp. pose proof (STPV 0%nat) as S0'. unfold pv_trace in S0'. cbn [repeat app] in S0'. exact S0'. }
    assert (B0 : 448 + 256 <= B1) by (clear -HB BPRE OFF Ho; blia).
    (nelimp VF 10%nat; intros _ L32 _ _ _ L0 S0 L16 _ SAVW). unfold LOCSV, SHV in L16. unfold CS08, SHV in L0.
    (nelim (our_chain SA Fr m1 GE SAVW CC) 3%nat; intros CCF COK CLK).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. pose proof (sh_zero_shb m1 P (P + 56) (P + 32) PSH ltac:(lia)) as Z32. asan_chk Z32. clear Z32.
    zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 AMALLOC)) with (wz AMALLOC) by (unfold wz, AMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { sepM. eapply (art_malloc_ok AI) with (lo := lo) (n := 64) (tl := chain_trace 2 ((SP, bv_unsigned ra, bv_unsigned s0) :: CH)); rewrite ?unsigned_lit by (lia_on Hd CEIL LO SP4 SP5 TOPR GSA);
        first [ exact HL | exact ST | unfold AERRNO, ATP; exact ERR | exact MI | exact TP | reflexivity | (cut_on [Hd CEIL LO SP2 GSA BOT SP4 GAL] (cut_on [Hd CEIL LO SP2 GSA BOT SP4 GAL] alia))
              | rewrite cost_malloc_64; lia
              | split; [lia| unfold PC0_MALLOC; lia]
              | eapply uwt_of_chain; [left; reflexivity| exact CCF| exact COK| lia| lia| cbn; split; [reflexivity| lia]]
              | eapply (tinv_room TI); [exact TV| exact ST0]
              | clear -SP6 GAL GSA; Z.div_mod_to_equations; lia ]. }
    cbv beta. intros ms2 mo2 g2 PO'.
    (nelim PO' 26%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 RES)
.
    rewrite ?unsigned_lit in ST2, PR2, TP2 by lia. rewrite cost_malloc_64 in RES. clear GAL SP6 CCF COK CLK.
    replace (ret_pc (Z_to_bv 64 0x8343c)) with (Z_to_bv 64 0x8343c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (VFR_cj_pres ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC SA Fr m1 m2 shb h jae jn CS08x lj _ GE VF PR2) as VF2.
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in ND; [| do 3 right; left; exists U, 64; cbn [cells_size Cells.csize Nat.add]; split; [exact INU| lia]].
    unfold pbuf_at in PB'. apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in PB'; [| do 4 right; left; exists (P - 32), 1; split; [right; exact PLF| rewrite pbuf_cells_size; change (fsz 1) with 128; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ _ _ PR2) in BY; [| do 3 right; left; exists D, n; rewrite LEN; split; [exact (INLR _ HD)| lia]].
    assert (TV2 : TINV TI np TRS2) by (eapply (tinv_put_or TI); [exact TV| exact ST0| exact TP2]). clear ST0.
    assert (INL : forall b, In b LR -> In b ((U, 64) :: LR)) by (intros b Hb; right; exact Hb).
    assert (PR3 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|].
      eapply ppres_weaken; [eapply ppres_of_cj_pres; [exact PR2| apply Z.le_refl| intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]]| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf]. }
    assert (PSH2 : pbuf_sh m2 P).
    { apply (ppres_pbuf_sh sp0 LR ((Fr, 2) :: LF) SA P m1 m2); [| exact PSH| right; exact PLF| alia| alia| alia (* [comment removed for export] *)].
      eapply ppres_of_cj_pres; [exact PR2| lia| intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]]. }
    apply (arr_inv_magree depth nfuel m1 m2) in AINV; [| eapply magree_blocks_of_cj_pres; [exact PR2| exact INX]].
    assert (CC2 : chain_cells m2 CH) by (eapply chain_cells_cj_pres; [exact CC| exact CHOK| exact PR2| lia| lia| lia]).
    assert (GM3 : gmono g g2) by (eapply gmono_trans; [exact GM| exact GM2]).
    clear PR PR2 MI ST HL ERR PSH TV GM CC VF PB. unfold AERRNO, ATP in ERR2.
    destruct RES as [[-> HL2] | (A & jk & -> & ARNG & ANEW & AFR & HL2 & BLK & FILL)].
    - (* [comment removed for export] *)
      eapply lscps_step_evt. cbv beta delta [mkR]. unfold wz. zstep. if_true. apply evt_done.
      eapply (ARR_FAIL_C8 SA Fr head X (S DCH) m2 mo2 g2 LBX TRS2 (B1 - 448) errv2 Fx fcx shb h jae jn CS08x lj o (depth + 1));
        [exact GE| | exact HPX| exact (cj_chain_any _ _ _ _ _ (arr_inv_chain depth _ _ _ _ AINV))| unfold dch; lia| exact VF2| unfold pbuf_at; exact PB'| eqcells ND| exact FA| exact FRM
        | clear -HB HX BPRE OFF Ho; blia].
      split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [exact PR3|]. split; [exact GM3|]. split; [exact TV2|]. split; [exact PSH2| exact CC2].
    - (* [comment removed for export] *)
      (nelimp ARNG 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM. change (Z.max 64 1) with 64 in A4. clear A3.
      assert (HPA : Permutation ((A, 64) :: (U, 64) :: X ++ LR) ((A, 64) :: LBX)) by (apply perm_skip; exact HPX).
      assert (APART : forall A' n', In (A', n') ((U, 64) :: X ++ LR) -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
      { intros A' n' Hin. eapply (lheap_perm_apart AI); [exact HL2| exact HPA| exact Hin]. }
      destruct (APART U 64 ltac:(left; reflexivity)) as [_ AU]. destruct (APART D n ltac:(right; apply in_or_app; right; exact HD)) as [_ AD].
      pose proof (AFR Fr 2 ltac:(left; reflexivity)) as AFr. change (fsz 2) with 256 in AFr.
      assert (APF : A + 64 + 16 <= P - 32 \/ P - 32 + 128 <= A - 16).
      { (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL2 ltac:(right; exact PLF)) 8%nat; intros _ _ _ _ _ _ _ FD').
        destruct (FD' A 64 ltac:(left; reflexivity)); [left| right]; change (fsz 1) with 128 in *; lia. }
      eapply lscps_step_evt. cbv beta delta [mkR]. unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
        sepM. eapply MSX with (lo := lo) (d := A) (c := 0) (n := 64) (junk := jk); clear MSX; rewrite ?unsigned_lit by (lia_on Hd CEIL LO SP4 SP5 TOPR GSA);
          first [ eapply art_icpt_cells; exact HL2 | exact MI2 | exact ST2 | exact BLK | reflexivity
                | app_rng0
                | apply wr_range_ok_high; lia
                | intros _; eapply art_block_shadow_ok; [exact HL2| left; reflexivity]
                | unfold AINTRIN_STACK; (cut_on [CEIL Hd LO GSA A4] (cut_on [CEIL Hd LO GSA A4] alia))
                | lia ]. }
      cbv beta. intros ms' PO.
      (nelim PO 21%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m3 -> MU3 WM3 MI3 ZB ST3).
      rewrite ?unsigned_lit in MU3, ST3 by lia. unfold AINTRIN_STACK in MU3.
      replace (ret_pc (Z_to_bv 64 0x83450)) with (Z_to_bv 64 0x83450) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (zero_node_cells' _ _ ZB) as NDA. clear ZB. unfold node_cells, wz in NDA.
      trc ND MU3 WM3. trc ERR2 MU3 WM3. trc BY MU3 WM3.
      assert (PB3 : pbuf_at m3 P CA blen o (depth + 1)) by (unfold pbuf_at in *; eapply rw_cells_transport; [exact PB'| exact MU3| exact WM3| rewrite pbuf_cells_size; dj]).
      unfold pbuf_at, pbuf_cells, wz in PB3.
      apply (arr_inv_magree depth nfuel m2 m3) in AINV.
      2:{ eapply magree_blocks_of_munch; [exact MU3| exact WM3|]. intros A' n' Hin. cbn. destruct (APART A' n' ltac:(right; apply in_or_app; left; exact Hin)).
          (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 ltac:(right; apply INX; exact Hin)) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4.
          split; [lia| split; [lia| exact I]]. }
      assert (HL3 : ART AI sp0 SPB ((A, 64) :: LBX) ((Fr, 2) :: LF) TRS2 (B1 - 448) m3 mo2 g2).
      { eapply (art_frame AI); [exact HL2| exact MU3| exact WM3|]. constructor; [| constructor; [| constructor]].
        - do 7 right. left. exists A, 64. cbn. split; [left; reflexivity| lia].
        - right; left. cbn. alia. }
      assert (PR4 : ppres sp0 LR LF SP P m m3).
      { eapply ppres_trans; [exact PR3|]. eapply ppres_of_munch; [exact MU3| exact WM3|]. intros a Ha Hp. cbn.
        pose proof (pv_addr_not_newblock ((A, 64) :: LBX) ((Fr, 2) :: LF) m2 mo2 g2 TRS2 (B1 - 448) A ((U, 64) :: X ++ LR) a HL2 HPA
                      ltac:(intros b Hb; right; apply in_or_app; right; exact Hb) ltac:(intros f Hf; right; exact Hf) Ha Hp) as NB.
        pose proof (pv_addr_below AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC ((A, 64) :: LBX) ((Fr, 2) :: LF) m2 mo2 g2 TRS2 (B1 - 448) a HL2
                      ltac:(intros b Hb; right; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]) ltac:(intros f Hf; right; exact Hf) Ha Hp) as BLW.
        try rewrite alloc_ceiling_eq in BLW. clear -NB BLW CEIL LO GSA DEP. lia. }
      assert (PSH3 : pbuf_sh m3 P).
      { eapply pbuf_sh_munch; [exact PSH2| exact MU3| lia| lia|]. sepM. pbuf_dj (* [comment removed for export] *). }
      assert (CC3 : chain_cells m3 CH).
      { eapply chain_cells_munch; [exact CC2| exact CHOK| exact MU3| lia| lia|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; left; lia. }
      assert (VF3 : VFRx SA Fr m3 shb h jae jn CS08x lj).
      { eapply VFR_MUNCH; [exact GE| exact VF2| exact MU3| exact WM3|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; [right; repeat split; (cut_on [A1 A4 AFr] (cut_on [A1 A4 AFr] alia))| left; alia]. }
      clear MU3 WM3 MI2 ST2 PR3 PSH2 BLK FILL CC2 VF2.
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (arr_inv_chain depth _ _ _ _ AINV)) 3%nat; intros HR1 _ HR2).
      zstep. zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct AINV as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX, HPA, HX.
        zstep. apply evt_done.
        eapply (do_call c IHc SA Fr o A A (wz 0) [] m3 mo2 g2 ((A, 64) :: LBX) TRS2 (B1 - 448) errv2 Fx fcx shb h jae jn lj);
          [exact Hc| exact Ho| exact Hd| exact GE| | exact HPA| lia| apply cj_lseg_nil| eqcells NDA| exact VF3| unfold pbuf_at; eqcells PB3| eqcells ND| exact FA| exact FRM
          | clear -HB; unfold PV_RATE in *; lia| cbn; lia].
        split; [exact HL3|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact PR4|]. split; [exact GM3|]. split; [exact TV2|]. split; [exact PSH3| exact CC3].
      + (* [comment removed for export] *)
        destruct AINV as [[E _]|(NZ & NZc & B1' & Bv & Bc & chc & tyc & vsc & pvc & p1c & vic & p2c & vdc & -> & SEG & NDC & TYC & SVC & CHC)]; [exfalso; exact (Kh E)|].
        assert (HPcur : Permutation ((cur, 64) :: (A, 64) :: (B1' ++ Bv ++ Bc) ++ (U, 64) :: LR) ((A, 64) :: LBX)).
        { eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply Permutation_trans; [apply perm_pick_mid| exact HPX]. }
        assert (INC : In (cur, 64) ((A, 64) :: LBX)) by (eapply perm_in_head; exact HPcur).
        pose_blk_band HL3 INC. pose_head_blk_band A. bandM. sepM.   (* [comment removed for export] *)
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL3 INC) 4%nat; intros C1 C2 C3 C4). try rewrite alloc_ceiling_eq in C4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. change (Z.max 64 1) with 64 in C4. clear C3.
        assert (CPART : forall A' n', In (A', n') ((A, 64) :: (B1' ++ Bv ++ Bc) ++ (U, 64) :: LR) -> A' <> cur /\ (A' + n' <= cur \/ cur + 64 <= A')).
        { intros A' n' Hin. eapply (lheap_perm_apart AI); [exact HL3| exact HPcur| exact Hin]. }
        destruct (CPART A 64 ltac:(left; reflexivity)) as [_ CA']. destruct (CPART U 64 ltac:(right; apply in_or_app; right; left; reflexivity)) as [_ CU].
        destruct (CPART D n ltac:(right; apply in_or_app; right; right; exact HD)) as [_ CD].
        pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL3 ltac:(right; exact PLF)) as BHA. destruct (BHA cur 64 INC) as [_ CPd]. destruct (BHA A 64 ltac:(left; reflexivity)) as [_ APd].
        (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL3 ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD3).
        pose proof (FD3 cur 64 INC) as CFr. change (fsz 2) with 256 in CFr.
        pose proof (rw_cells_bound asegs _ _ _ NDC) as NCB. rewrite node_cells_size in NCB. unfold node_cells, wz in NDC.
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL3 INC) as SOC.
        pose proof (shadow_ok_sh_zero m3 cur 64 cur (cur + 64) SOC ltac:(lia) ltac:(clear -C2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (cur + 64 - cur) with 64 by lia; reflexivity)) as SZC.
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL3 ltac:(left; reflexivity)) as SOA3.
        pose proof (shadow_ok_sh_zero m3 A 64 A (A + 64) SOA3 ltac:(lia) ltac:(clear -A2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (A + 64 - A) with 64 by lia; reflexivity)) as SZA3.
        clear C2 A2 SOC SOA3.
        (* [comment removed for export] *)
        pose proof (munch_refl [(cur, cur + 8)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        zstep. zstep. pose proof (sh_zero_shb m3 cur (cur + 64) cur SZC ltac:(lia)) as CKc. asan_chk CKc. clear CKc.
        sepM. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        assert (HL4 : ART AI sp0 SPB ((A, 64) :: LBX) ((Fr, 2) :: LF) TRS2 (B1 - 448) m4 mo2 g2) by (eapply (art_block_store AI); [exact HL3| exact INC| exact MU| exact WM| lia| lia]).
        assert (PR5 : ppres sp0 LR LF SP P m m4).
        { eapply ppres_trans; [exact PR4|]. eapply (ppres_weaken sp0 LR LR ((Fr, 2) :: LF) LF SA SP P); [| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf].
          eapply (ppres_block_store AI); [exact HL3| exact HPcur| intros b Hb; right; apply in_or_app; right; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
        assert (PSH4 : pbuf_sh m4 P) by (eapply pbuf_sh_high_store; [exact PSH3| exact MU| alia| alia| alia]).
        assert (DJ : forall A' n', In (A', n') (B1' ++ Bv ++ Bc) -> disjoint_from [(cur, cur + 8)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I]. destruct (CPART A' n' ltac:(right; apply in_or_app; left; exact Hin)). lia. }
        assert (SEG4 : cj_lseg CJ_PRINTABLE m4 DCH head cur B1') by (eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]; intros A' n' Hin; apply DJ; apply in_or_app; left; exact Hin).
        assert (SVC4 : cj_str m4 vsc Bv) by (eapply cj_str_frame; [exact SVC| exact MU| exact WM|]; intros A' n' Hin; apply DJ; apply in_or_app; right; apply in_or_app; left; exact Hin).
        assert (CHC4 : cj_chain CJ_PRINTABLE m4 DCH chc Bc) by (eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]; intros A' n' Hin; apply DJ; apply in_or_app; right; apply in_or_app; right; exact Hin).
        assert (CC4 : chain_cells m4 CH) by (eapply chain_cells_munch; [exact CC3| exact CHOK| exact MU| lia| lia|]; intros lo' hi' [E|[]]; inversion E; subst; left; lia).
        assert (VF4 : VFRx SA Fr m4 shb h jae jn CS08x lj) by (eapply VFR_MUNCH; [exact GE| exact VF3| exact MU| exact WM|]; intros lo' hi' [E|[]]; inversion E; subst; right; repeat split; alia).
        assert (SZA : sh_zero m4 A (A + 64)).
        { pose proof (SH_bounds A ltac:(lia)). pose proof (SH_bounds (A + 64 - 1) ltac:(lia)).
          eapply sh_zero_munch; [exact SZA3| exact MU| lia| lia|]. sepM. sh_dj (* [comment removed for export] *). }
        clear MU WM HL3 PR4 PSH3 SEG SVC CHC DJ SZC CC3 VF3 SZA3.
        (* [comment removed for export] *)
        pose proof (munch_refl [(A + 8, A + 16)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        zstep. zstep. zstep. pose proof (sh_zero_shb m4 A (A + 64) (A + 8) SZA ltac:(lia)) as CKa. asan_chk CKa. clear CKa.
        sepM. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        assert (HL5 : ART AI sp0 SPB ((A, 64) :: LBX) ((Fr, 2) :: LF) TRS2 (B1 - 448) m5 mo2 g2) by (eapply (art_block_store AI); [exact HL4| left; reflexivity| exact MU| exact WM| lia| lia]).
        assert (PR6 : ppres sp0 LR LF SP P m m5).
        { eapply ppres_trans; [exact PR5|]. eapply (ppres_weaken sp0 LR LR ((Fr, 2) :: LF) LF SA SP P); [| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf].
          eapply (ppres_block_store AI); [exact HL4| apply Permutation_refl| exact INLR| (cut_on [Hd CEIL LO GSA BR] alia)| lia| exact MU| exact WM| lia| lia]. }
        assert (PSH5 : pbuf_sh m5 P) by (eapply pbuf_sh_high_store; [exact PSH4| exact MU| alia| alia| alia]).
        assert (DJ : forall A' n', In (A', n') (B1' ++ Bv ++ Bc) -> disjoint_from [(A + 8, A + 16)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I].
          destruct (APART A' n' ltac:(right; apply in_or_app; left; apply in_app_or in Hin; apply in_or_app; destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin])). (lia_on A1 Kz H0). }
        assert (SEG5 : cj_lseg CJ_PRINTABLE m5 DCH head cur B1') by (eapply cj_lseg_frame; [exact SEG4| exact MU| exact WM|]; intros A' n' Hin; apply DJ; apply in_or_app; left; exact Hin).
        assert (SVC5 : cj_str m5 vsc Bv) by (eapply cj_str_frame; [exact SVC4| exact MU| exact WM|]; intros A' n' Hin; apply DJ; apply in_or_app; right; apply in_or_app; left; exact Hin).
        assert (CHC5 : cj_chain CJ_PRINTABLE m5 DCH chc Bc) by (eapply cj_chain_frame; [exact CHC4| exact MU| exact WM|]; intros A' n' Hin; apply DJ; apply in_or_app; right; apply in_or_app; right; exact Hin).
        assert (CC5 : chain_cells m5 CH) by (eapply chain_cells_munch; [exact CC4| exact CHOK| exact MU| lia| lia|]; intros lo' hi' [E|[]]; inversion E; subst; left; lia).
        assert (VF5 : VFRx SA Fr m5 shb h jae jn CS08x lj) by (eapply VFR_MUNCH; [exact GE| exact VF4| exact MU| exact WM|]; intros lo' hi' [E|[]]; inversion E; subst; right; repeat split; alia).
        clear MU WM HL4 PR5 PSH4 SEG4 SVC4 CHC4 DJ SZA CC4 VF4.
        zstep. zstep. apply evt_done.
        eapply (do_call c IHc SA Fr o head A (Z_to_bv 64 cur) (B1' ++ (cur, 64) :: Bv ++ Bc) m5 mo2 g2 ((A, 64) :: LBX) TRS2 (B1 - 448) errv2 Fx fcx shb h jae jn lj);
          [exact Hc| exact Ho| exact Hd| exact GE| | exact HPA| exact NZ| | eqcells NDA| exact VF5| unfold pbuf_at; eqcells PB3| eqcells ND| exact FA| exact FRM
          | clear -HB; unfold PV_RATE in *; lia| exact HX].
        * split; [exact HL5|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI3|]. split; [exact ST3|].
          split; [exact PR6|]. split; [exact GM3|]. split; [exact TV2|]. split; [exact PSH5| exact CC5].
        * replace (B1' ++ (cur, 64) :: Bv ++ Bc) with (B1' ++ (cur, 64) :: Bv ++ [] ++ Bc) by reflexivity.
          eapply cj_lseg_snoc; [exact SEG5| exact NZc| eqcells NDC| apply CJ_PRINTABLE_range; exact TYC| exact TYC| exact SVC5| apply cj_str_null| exact CHC5].
  Qed.

  Theorem aloop : forall c, ALOOPc c.
  Proof. induction c as [c IH] using lt_wf_ind. apply loop_top. exact IH. Qed.
End PVA3.


End CeilWrap.
End CJ_pvalue_A3.

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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_A2.CJ_pvalue_A1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_A2.
Import CJ_pvalue_A3.
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

Section PVA4.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z) (CH : list (Z * Z * Z)).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (PARSE_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis CHOK : chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0).
  Hypothesis CHL : chain_link (bv_unsigned s0) (bv_unsigned sp) CH.
  Hypothesis RA1 : 4096 <= bv_unsigned ra.
  Hypothesis RA2 : ~ is_pc0 (bv_unsigned ra).
  Hypothesis FLA : flag_apart_stmt AI.
  Hypothesis STPV : forall b, STAT TI (pv_trace (bv_unsigned ra) CH b).
  Hypothesis STPO : forall b, STAT TI (tr_pv_pobj b).
  Hypothesis STC : Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE).
  Hypothesis LFR : lf_room 2 LF (1001 - depth).
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation VSTx := (VST sp gp tp).
  Notation MID := (MIDV AI TI sp m g sp0 SPB LR LF np CH P CA bs lo).
  Notation VFRx := (VFR ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P).
  Notation VGEOMx := (VGEOM sp LB LF P).
  Notation VRESx := (VRES LR B U blen off depth nx pv ty p1 vi p2 vd ky).
  Notation MAGIC_EXIT := (magic_exit AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA).
  Notation DCH := (dch depth).
  Notation CS08x := (CS08 P).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK, SKIPWS_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac steq := unfold VST, SHV, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac blia := unfold pv_cost_pre, pstr_cost_pre, pstr_fail_cost, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  Hypothesis DEL : cjson_delete_stmt AI TI.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at AI TI nf.

  Notation ALOOPx := (aloop AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK CHL RA1 RA2 FLA STPV STPO STC LFR nfuel FUEL DEL MEMSET PVREC).
  Notation ARR_SUCCESS := (arr_success AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA nfuel FUEL).
  Notation VFR_MUNCH := (VFR_munch ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC nfuel).

  (* [comment removed for export] *)
  Lemma arr_tail : forall (SA Fr o2 : Z) m1 mo1 g1 TRS1 errv1 Fx fcx shb h jae jn (j08 : list byte) lj
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    VFRx SA Fr m1 shb h jae jn [CB 16 j08] lj ->
    pbuf_at m1 P CA blen o2 (depth + 1) -> off + 1 <= o2 <= blen -> depth <= 999 ->
    rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x83014 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (SHV (P + 16)) (Z_to_bv 64 U) (Z_to_bv 64 P)
                        (Z_to_bv 64 (P + 24)) (SHV (P + 24)) x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD VF PB Ho2 Hd ND FA FRM. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ HD) DCA CAD) as TSH.
    (nelimp VF 10%nat; intros _ L32 _ _ _ L0 S0 L16 _ _). unfold LOCSV, SHV in L16.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. pose proof (sh_zero_shb m1 P (P + 56) (P + 8) PSH ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *)
      pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      pose proof (munch_refl [(P + 16, P + 24)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (HL2 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m2 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL| right; exact PLF| exact MU| exact WM| lia| lia]).
      assert (PR2 : ppres sp0 LR LF SP P m m2) by (eapply ppres_trans; [exact PR| eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]]).
      assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
      assert (CC2 : chain_cells m2 CH).
      { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
      assert (VF2 : VFRx SA Fr m2 shb h jae jn [CB 16 j08] lj).
      { eapply VFR_MUNCH; [exact GE| exact VF| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right. repeat split; alia. }
      (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m2 shb h jae jn [CB 16 j08] lj VF2 ltac:(lia)) 3%nat; intros locs FRL SZL).
      (nelim VF2 10%nat; intros SHC2 _ HDR2 _ _ _ _ _ _ SAVW2).
      try change (sxb (zb 0)) with (Z_to_bv 64 0). try change (uxb (zb 0)) with (Z_to_bv 64 0).
      apply evt_done. eapply lscps_eq; [| eapply (MAGIC_EXIT 0x833e0 SA Fr 0 m2 mo1 g1 LB TRS1 B errv1 Fx fcx shb h locs (o2 - 1) (depth + 1));
        [cbn; tauto| exact GE| | exact SHC2| exact L32| exact HDR2| exact FRL| lia| exact SAVW2| exact FA| exact FRM| unfold pbuf_at, pbuf_cells, wz; eqcells PB|]].
      - steq.
      - split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
        split; [exact PR2|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH2| exact CC2].
      - exists []. split; [exact HPU|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [eqcells ND| clear -BPRE OFF; blia]. }
    (* [comment removed for export] *)
    zstep. pose proof (sh_zero_shb m1 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    destruct (nth_error bs (Z.to_nat o2)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read asegs _ CA bs o2 b _ BY Hn ltac:(lia) eq_refl) as RD. pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. zstep.
    pose proof (TSH (CA + o2) ltac:(lia)) as CK. sepM. asan_chk CK.
    zstep. zstep. zstep. if_cases K93; zify_cond K93.
    - (* [comment removed for export] *)
      pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      pose proof (munch_refl [(SA, SA + 16); (P + 16, P + 24)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (HL2 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m2 mo1 g1).
      { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. constructor; [| constructor; [| constructor]].
        - right; left. cbn. alia.
        - do 8 right. left. exists (P - 32), 1. cbn. split; [right; exact PLF|]. change (fsz 1) with 128. lia. }
      assert (PR2 : ppres sp0 LR LF SP P m m2).
      { eapply ppres_trans; [exact PR|]. eapply ppres_of_munch; [exact MU| exact WM|]. intros a Ha Hp. cbn.
        pose proof (pv_addr_below AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC LB ((Fr, 2) :: LF) m1 mo1 g1 TRS1 B a HL INLR
                      ltac:(intros f Hf; right; exact Hf) Ha Hp) as BLW.
        (nelim Hp 3%nat; intros _ _ HnP). try rewrite alloc_ceiling_eq in BLW. clear -BLW HnP CEIL LO GSA DEP. lia. }
      assert (PSH2 : pbuf_sh m2 P).
      { eapply pbuf_sh_munch; [exact PSH| exact MU| lia| lia|]. sepM. pbuf_dj (* [comment removed for export] *). }
      assert (CC2 : chain_cells m2 CH).
      { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; left; lia. }
      (nelimp VF 10%nat; intros SHC _ HDR AE NC _ _ _ STP SAVW).
      assert (VF2 : VFRx SA Fr m2 shb h jae jn CS08x lj).
      { split. { unfold SHCW in *. eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. rewrite cells_size_mapC1, L32, SH_shiftr.
                 pose proof (SH_bounds Fr ltac:(lia)). pose proof (SH_bounds (Fr + 255) ltac:(lia)) as SB2. rewrite (SH_aligned_add Fr 255) in SB2 by first [mod8 | (Z.div_mod_to_equations; lia)]. cbn. lia. }
        split; [exact L32|].
        split. { eapply rw_cells_transport; [exact HDR| exact MU| exact WM|]. cbn. lia. }
        split. { eapply rw_cells_transport; [exact AE| exact MU| exact WM|]. cbn. lia. }
        split. { eapply rw_cells_transport; [exact NC| exact MU| exact WM|]. cbn. lia. }
        split. { unfold CS08, SHV. lazymatch goal with |- rw_cells _ _ _ ?cs => idtac end.
                 match goal with H : rw_cells asegs m2 SA ?cs |- _ => eqcells H end. }
        split; [reflexivity|].
        split. { unfold LOCSV, SHV. match goal with H : rw_cells asegs m2 (SA + 16) ?cs |- _ => exact H end. }
        split. { eapply stk_transport_disjoint; [exact STP| exact MU| exact WM|]. cbn. lia. }
        eapply rw_cells_transport; [exact SAVW| exact MU| exact WM|]. cbn. lia. }
      apply evt_done.
      eapply lscps_eq; [| eapply (ALOOPx (Z.to_nat (blen - (o2 - 1))) SA Fr (o2 - 1) 0 0 [] m2 mo1 g1 LB TRS1 B errv1 Fx fcx shb h jae jn lj);
        [lia| lia| exact Hd| exact GE| | exact HPU| left; split; reflexivity| exact VF2| | eqcells ND| exact FA| exact FRM
        | clear -BPRE OFF Ho2; unfold PV_RATE in *; lia| cbn; lia]].
      + steq.
      + split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
        split; [exact PR2|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH2| exact CC2].
      + unfold pbuf_at, pbuf_cells, wz. match goal with H : rw_cells asegs m2 P ?cs |- _ => eqcells H end.
    - (* [comment removed for export] *)
      pose proof (sh_zero_shb m1 P (P + 56) (P + 24) PSH ltac:(lia)) as Z24. asan_chk Z24. clear Z24.
      pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (HL2 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m2 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL| right; exact PLF| exact MU| exact WM| lia| lia]).
      assert (PR2 : ppres sp0 LR LF SP P m m2) by (eapply ppres_trans; [exact PR| eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]]).
      assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
      assert (CC2 : chain_cells m2 CH).
      { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
      assert (VF2 : VFRx SA Fr m2 shb h jae jn [CB 16 j08] lj).
      { eapply VFR_MUNCH; [exact GE| exact VF| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right. repeat split; alia. }
      clear MU WM.
      (* [comment removed for export] *)
      pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL2 INU) as SOU.
      pose proof (shadow_ok_sh_zero m2 U 64 U (U + 64) SOU ltac:(lia) ltac:(clear -U2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (U + 64 - U) with 64 by lia; reflexivity)) as SZU.
      zstep. zstep. zstep. pose proof (sh_zero_shb m2 U (U + 64) (U + 24) SZU ltac:(lia)) as CK4. asan_chk CK4. clear CK4.
      apply evt_done.
      eapply lscps_eq; [| eapply (ARR_SUCCESS SA Fr o2 0 [] m2 mo1 g1 LB TRS1 B errv1 Fx fcx shb h jae jn [CB 16 j08] lj);
        [exact GE| | exact HPU| apply cj_chain_nil| exact Hd| exact VF2| unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| lia| exact FA| exact FRM
        | clear -BPRE OFF Ho2 Kend; blia| cbn; lia]].
      + steq.
      + split; [exact HL2|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
        split; [exact PR2|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH2| exact CC2].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_entry : forall (SA Fr : Z) m1 mo1 g1 TRS1 errv1 Fx fcx shb h jae jn (j08 : list byte) lj (b : byte)
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LB TRS1 B errv1 ->
    VFRx SA Fr m1 shb h jae jn [CB 16 j08] lj ->
    pbuf_at m1 P CA blen off depth -> rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off < blen -> nth_error bs (Z.to_nat off) = Some b -> bv_unsigned b = 91 ->
    Fagree F Fx -> frm0 fcx ->
    LSCPS asegs POST (VSTx SA Fr 0x82fb4 x1 x5 x6 x7 (Z_to_bv 64 (CA + off)) (SHV (CA + off)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 CA) (Z_to_bv 64 U) (Z_to_bv 64 P)
                        x22 x23 (Z_to_bv 64 off) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD VF PB ND Ho Hn Hb91 FA FRM. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INLR : forall b', In b' LR -> In b' LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ HD) DCA CAD) as TSH.
    pose proof (byte_range b) as Rb.
    (nelimp VF 10%nat; intros _ L32 _ _ _ L0 S0 L16 _ _). unfold LOCSV, SHV in L16.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m1 P (P + 56) (P + 24) PSH ltac:(lia)) as Z24. asan_chk Z24.
    zstep. zstep. zstep. if_cases Kd; zify_cond Kd.
    { (* [comment removed for export] *)
      (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m1 shb h jae jn [CB 16 j08] lj VF ltac:(lia)) 3%nat; intros locs FRL SZL).
      (nelimp VF 10%nat; intros SHC _ HDR _ _ _ _ _ _ SAVW).
      zstep. apply evt_done.
      eapply (MAGIC_EXIT 0x83568 SA Fr 0 m1 mo1 g1 LB TRS1 B errv1 Fx fcx shb h locs off depth);
        [cbn; tauto| exact GE| exact MD| exact SHC| exact L32| exact HDR| exact FRL| lia| exact SAVW| exact FA| exact FRM| exact PB'|].
      exists []. split; [exact HPU|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [eqcells ND| clear -BPRE OFF; blia]. }
    (* [comment removed for export] *)
    asan_chk Z24. clear Z24.
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m2 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL| right; exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2) by (eapply ppres_trans; [exact PR| eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]]).
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    assert (CC2 : chain_cells m2 CH).
    { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    assert (VF2 : VFRx SA Fr m2 shb h jae jn [CB 16 j08] lj).
    { eapply VFR_MUNCH; [exact GE| exact VF| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right. repeat split; alia. }
    assert (TSH2 : text_sh m2 CA blen) by (eapply (art_text_sh AI); [exact HL2| exact (INLR _ HD)| exact DCA| exact CAD]).
    clear MU WM HL PR PSH CC VF.
    (* [comment removed for export] *)
    pose proof (TSH2 (CA + off) ltac:(lia)) as CK. sepM. asan_chk CK.
    pose proof (u8ro_read asegs _ CA bs off b _ BY Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. zstep. if_cases K91; zify_cond K91; [exfalso; lia|].
    zstep. pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m3 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL2| right; exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres sp0 LR LF SP P m m3) by (eapply ppres_trans; [exact PR2| eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]]).
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    assert (CC3 : chain_cells m3 CH).
    { eapply chain_cells_munch; [exact CC2| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    assert (VF3 : VFRx SA Fr m3 shb h jae jn [CB 16 j08] lj).
    { eapply VFR_MUNCH; [exact GE| exact VF2| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right. repeat split; alia. }
    assert (TSH3 : text_sh m3 CA blen) by (eapply (art_text_sh AI); [exact HL3| exact (INLR _ HD)| exact DCA| exact CAD]).
    clear MU WM HL2 PR2 PSH2 CC2 VF2.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply evt_cut.
    { eapply skipws_spec with (P := P) (content := CA) (len := blen) (offset := off + 1) (depth := depth + 1) (bs := bs) (lo := lo); rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- pbuf_at _ _ _ _ _ _ => unfold pbuf_at, pbuf_cells, wz; eqcells PB end
              | reflexivity | exact BY | exact LEN | exact PSH3 | exact TSH3 | exact ST
              | eapply (art_shbase AI); exact HL3
              | assumption
              | alia
              | clear -PF3; Z.div_mod_to_equations; lia ]. }
    intros ms' PO. (nelim PO 18%nat; intros t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' m4 -> MU4 WM4 MI4 ST4 PB4 BY4).
    rewrite ?unsigned_lit in MU4, ST4 by lia.
    replace (ret_pc (Z_to_bv 64 0x83014)) with (Z_to_bv 64 0x83014) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc ND MU4 WM4. trc ERR MU4 WM4.
    assert (HL4 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS1 B m4 mo1 g1).
    { eapply (art_frame AI); [exact HL3| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]].
      - do 8 right. left. exists (P - 32), 1. cbn. split; [right; exact PLF|]. change (fsz 1) with 128. lia.
      - right; left. cbn. alia. }
    assert (PR4 : ppres sp0 LR LF SP P m m4).
    { eapply ppres_trans; [exact PR3|]. eapply ppres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hp. cbn.
      pose proof (pv_addr_below AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC LB ((Fr, 2) :: LF) m3 mo1 g1 TRS1 B a HL3 INLR
                    ltac:(intros f Hf; right; exact Hf) Ha Hp) as BLW.
      (nelim Hp 3%nat; intros _ _ HnP). try rewrite alloc_ceiling_eq in BLW. clear -BLW HnP CEIL LO GSA DEP. lia. }
    assert (PSH4 : pbuf_sh m4 P).
    { eapply pbuf_sh_munch; [exact PSH3| exact MU4| lia| lia|]. sepM. pbuf_dj (* [comment removed for export] *). }
    assert (CC4 : chain_cells m4 CH).
    { eapply chain_cells_munch; [exact CC3| exact CHOK| exact MU4| lia| lia|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; left; lia. }
    assert (VF4 : VFRx SA Fr m4 shb h jae jn [CB 16 j08] lj).
    { eapply VFR_MUNCH; [exact GE| exact VF3| exact MU4| exact WM4|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; [right; repeat split; alia| left; alia]. }
    assert (O2 : off + 1 <= skipws_off bs (off + 1) <= blen).
    { destruct (Z.eq_dec (off + 1) blen) as [E|NE].
      - rewrite skipws_off_noop by lia. lia.
      - pose proof (skipws_off_range bs (off + 1)) as OR. rewrite LEN in OR. lia. }
    apply evt_done.
    eapply lscps_eq; [| eapply (arr_tail SA Fr (skipws_off bs (off + 1)) m4 mo1 g1 TRS1 errv1 Fx fcx shb h jae jn j08 lj);
      [exact GE| | exact VF4| exact PB4| exact O2| lia| eqcells ND| exact FA| exact FRM]].
    - steq.
    - split; [exact HL4|]. split; [exact BY4|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI4|]. split; [exact ST4|].
      split; [exact PR4|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH4| exact CC4].
  Qed.
End PVA4.


End CeilWrap.
